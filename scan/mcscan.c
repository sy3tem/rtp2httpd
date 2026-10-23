// mcscan - multicast IPTV channel scanner (companion tool for rtp2httpd)
//
// Probes IPv4 multicast groups, detects live RTP/MPEG-TS streams and writes an
// M3U playlist. rtp2httpd can consume it with
//   external-m3u = file:///etc/rtp2httpd/playlist.m3u
//   external-m3u-update-interval = 300
// so the channel list refreshes without restarting the service.
//
// Why this shape:
//   * an ISP's multicast block is unknown, so the tool sweeps a CIDR list;
//   * each membership costs one socket slot (igmp_max_memberships), so a batch
//     of groups shares one socket and IP_PKTINFO tells us which group the
//     datagram was sent to;
//   * batches are short-lived, which keeps kernel state small during a sweep.
//
// SPDX-License-Identifier: GPL-2.0

#define _GNU_SOURCE
#include <arpa/inet.h>
#include <errno.h>
#include <net/if.h>
#include <netinet/in.h>
#include <poll.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <time.h>
#include <unistd.h>

#define MAX_PORTS   8
#define MAX_RANGES  16
#define MAX_SEGS    (MAX_PORTS * MAX_RANGES)

typedef struct {
	uint16_t port;
	uint32_t base;
	uint32_t count;
	uint64_t start;   /* flat index of this segment */
} seg_t;

typedef struct {
	uint32_t addr;
	uint16_t port;
	uint64_t bytes;
	int rtp;
} hit_t;

static seg_t g_segs[MAX_SEGS];
static int g_nsegs;
static uint64_t g_total;
static uint64_t g_cursor;
static pthread_mutex_t g_cursor_lock = PTHREAD_MUTEX_INITIALIZER;

static hit_t *g_hits;
static size_t g_nhits, g_chits;
static pthread_mutex_t g_hit_lock = PTHREAD_MUTEX_INITIALIZER;

static int g_ifindex;
static int g_timeout_ms = 250;
static int g_threads = 8;
static int g_memberships = 200;
static int g_min_bytes = 1200;
static const char *g_mapfile;

static void die(const char *m)
{
	fprintf(stderr, "mcscan: %s\n", m);
	exit(1);
}

static uint64_t now_ms(void)
{
	struct timespec ts;
	clock_gettime(CLOCK_MONOTONIC, &ts);
	return (uint64_t)ts.tv_sec * 1000u + (uint64_t)ts.tv_nsec / 1000000u;
}

static int parse_cidr(const char *s, uint32_t *base, uint32_t *count)
{
	char buf[64];
	char *slash;
	struct in_addr a;
	int bits;

	snprintf(buf, sizeof(buf), "%s", s);
	slash = strchr(buf, '/');
	bits = 32;
	if (slash) {
		*slash = '\0';
		bits = atoi(slash + 1);
	}
	if (inet_pton(AF_INET, buf, &a) != 1 || bits < 0 || bits > 32)
		return -1;

	uint32_t mask = bits == 0 ? 0 : 0xffffffffu << (32 - bits);
	*base = ntohl(a.s_addr) & mask;
	*count = bits == 32 ? 1u : (1u << (32 - bits));
	return 0;
}

static void build_segments(uint16_t *ports, int nports, uint32_t *bases,
			   uint32_t *counts, int nranges)
{
	uint64_t idx = 0;

	for (int p = 0; p < nports; p++) {
		for (int r = 0; r < nranges && g_nsegs < MAX_SEGS; r++) {
			g_segs[g_nsegs].port = ports[p];
			g_segs[g_nsegs].base = bases[r];
			g_segs[g_nsegs].count = counts[r];
			g_segs[g_nsegs].start = idx;
			idx += counts[r];
			g_nsegs++;
		}
	}
	g_total = idx;
}

static int flat_to_addr(uint64_t idx, uint32_t *addr, uint16_t *port)
{
	for (int i = 0; i < g_nsegs; i++) {
		if (idx >= g_segs[i].start &&
		    idx < g_segs[i].start + g_segs[i].count) {
			*addr = g_segs[i].base + (uint32_t)(idx - g_segs[i].start);
			*port = g_segs[i].port;
			return 0;
		}
	}
	return -1;
}

/* take a batch that never crosses a segment boundary */
static int take_batch(uint64_t *out_start, uint64_t *out_end)
{
	pthread_mutex_lock(&g_cursor_lock);
	if (g_cursor >= g_total) {
		pthread_mutex_unlock(&g_cursor_lock);
		return 0;
	}
	uint64_t start = g_cursor;
	uint64_t end = start + (uint64_t)g_memberships;

	for (int i = 0; i < g_nsegs; i++) {
		uint64_t seg_end = g_segs[i].start + g_segs[i].count;
		if (start >= g_segs[i].start && start < seg_end) {
			if (end > seg_end)
				end = seg_end;
			break;
		}
	}
	if (end <= start)
		end = start + 1;
	g_cursor = end;
	pthread_mutex_unlock(&g_cursor_lock);
	*out_start = start;
	*out_end = end;
	return 1;
}

static void add_hit(uint32_t addr, uint16_t port, uint64_t bytes, int rtp)
{
	pthread_mutex_lock(&g_hit_lock);
	for (size_t i = 0; i < g_nhits; i++) {
		if (g_hits[i].addr == addr && g_hits[i].port == port) {
			if (bytes > g_hits[i].bytes)
				g_hits[i].bytes = bytes;
			pthread_mutex_unlock(&g_hit_lock);
			return;
		}
	}
	if (g_nhits == g_chits) {
		size_t cap = g_chits ? g_chits * 2 : 64;
		hit_t *v = realloc(g_hits, cap * sizeof(*v));
		if (!v) {
			pthread_mutex_unlock(&g_hit_lock);
			return;
		}
		g_hits = v;
		g_chits = cap;
	}
	g_hits[g_nhits].addr = addr;
	g_hits[g_nhits].port = port;
	g_hits[g_nhits].bytes = bytes;
	g_hits[g_nhits].rtp = rtp;
	g_nhits++;
	pthread_mutex_unlock(&g_hit_lock);
}

static int looks_like_stream(const uint8_t *b, size_t n, int *rtp)
{
	if (n >= 12 && (b[0] & 0xc0) == 0x80 && (b[1] & 0x7f) == 33) {
		*rtp = 1;
		return 1;
	}
	if (n >= 189 && b[0] == 0x47 && b[188] == 0x47) {
		*rtp = 0;
		return 1;
	}
	return 0;
}

static int open_socket(uint16_t port)
{
	int fd = socket(AF_INET, SOCK_DGRAM | SOCK_NONBLOCK, 0);
	int one = 1;
	struct sockaddr_in sa;

	if (fd < 0)
		return -1;
	setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));
#ifdef SO_REUSEPORT
	setsockopt(fd, SOL_SOCKET, SO_REUSEPORT, &one, sizeof(one));
#endif
	setsockopt(fd, SOL_SOCKET, SO_RCVBUF, &(int){4 * 1024 * 1024}, sizeof(int));
	setsockopt(fd, IPPROTO_IP, IP_PKTINFO, &one, sizeof(one));
#ifdef IP_MULTICAST_ALL
	setsockopt(fd, IPPROTO_IP, IP_MULTICAST_ALL, &(int){0}, sizeof(int));
#endif

	memset(&sa, 0, sizeof(sa));
	sa.sin_family = AF_INET;
	sa.sin_port = htons(port);
	sa.sin_addr.s_addr = htonl(INADDR_ANY);
	if (bind(fd, (struct sockaddr *)&sa, sizeof(sa)) < 0) {
		close(fd);
		return -1;
	}
	return fd;
}

static int join_group(int fd, uint32_t addr_host)
{
	struct ip_mreqn mreq;

	memset(&mreq, 0, sizeof(mreq));
	mreq.imr_multiaddr.s_addr = htonl(addr_host);
	mreq.imr_address.s_addr = htonl(INADDR_ANY);
	mreq.imr_ifindex = g_ifindex;
	return setsockopt(fd, IPPROTO_IP, IP_ADD_MEMBERSHIP, &mreq, sizeof(mreq));
}

static void collect(int fd, uint64_t deadline)
{
	uint8_t buf[2048];
	char cbuf[256];
	uint32_t group_bytes = 0;
	uint32_t last_group = 0;
	uint16_t last_port = 0;
	int last_rtp = 0;

	while (now_ms() <= deadline) {
		struct pollfd p = { .fd = fd, .events = POLLIN };
		struct iovec iov = { .iov_base = buf, .iov_len = sizeof(buf) };
		int left = (int)(deadline - now_ms());
		int prc;

		if (left < 0)
			left = 0;
		prc = poll(&p, 1, left);
		if (prc <= 0)
			break;
		struct sockaddr_in from;
		struct msghdr msg;
		uint32_t dest = 0;
		ssize_t n;
		int rtp = 0;

		memset(&msg, 0, sizeof(msg));
		msg.msg_name = &from;
		msg.msg_namelen = sizeof(from);
		msg.msg_iov = &iov;
		msg.msg_iovlen = 1;
		msg.msg_control = cbuf;
		msg.msg_controllen = sizeof(cbuf);

		n = recvmsg(fd, &msg, 0);
		if (n <= 0)
			break;

		for (struct cmsghdr *c = CMSG_FIRSTHDR(&msg); c; c = CMSG_NXTHDR(&msg, c)) {
			if (c->cmsg_level == IPPROTO_IP && c->cmsg_type == IP_PKTINFO) {
				struct in_pktinfo *pi = (struct in_pktinfo *)CMSG_DATA(c);
				dest = ntohl(pi->ipi_addr.s_addr);
			}
		}
		if (!dest || !looks_like_stream(buf, (size_t)n, &rtp))
			continue;

		if (dest != last_group && last_group) {
			if ((int)group_bytes >= g_min_bytes)
				add_hit(last_group, last_port, group_bytes, last_rtp);
			group_bytes = 0;
		}
		last_group = dest;
		last_rtp = rtp;
		last_port = ntohs(from.sin_port);
		group_bytes += (uint32_t)n;
	}

	if (last_group && (int)group_bytes >= g_min_bytes)
		add_hit(last_group, last_port, group_bytes, last_rtp);
}

static void *worker(void *arg)
{
	(void)arg;

	for (;;) {
		uint64_t start, end;
		uint32_t addr;
		uint16_t port;
		int fd;

		if (!take_batch(&start, &end))
			break;
		if (flat_to_addr(start, &addr, &port) < 0)
			continue;

		fd = open_socket(port);
		if (fd < 0)
			continue;

		for (uint64_t i = start; i < end; i++) {
			uint32_t a;
			uint16_t p;

			if (flat_to_addr(i, &a, &p) < 0 || p != port)
				break;
			join_group(fd, a);
		}

		collect(fd, now_ms() + (uint64_t)g_timeout_ms);
		close(fd);
	}
	return NULL;
}

static void write_m3u(const char *out)
{
	char tmp[512];
	char name[160];
	FILE *f;

	snprintf(tmp, sizeof(tmp), "%s.tmp", out);
	f = fopen(tmp, "w");
	if (!f) {
		perror("mcscan: open output");
		return;
	}
	fprintf(f, "#EXTM3U\n");
	for (size_t i = 0; i < g_nhits; i++) {
		hit_t *h = &g_hits[i];
		snprintf(name, sizeof(name), "%u.%u.%u.%u:%u",
			 (h->addr >> 24) & 0xff, (h->addr >> 16) & 0xff,
			 (h->addr >> 8) & 0xff, h->addr & 0xff, h->port);
		if (g_mapfile) {
			FILE *m = fopen(g_mapfile, "r");
			if (m) {
				char line[256];
				while (fgets(line, sizeof(line), m)) {
					char *eq = strchr(line, '=');
					char *nl;
					if (!eq)
						continue;
					*eq = '\0';
					nl = strchr(eq + 1, '\n');
					if (nl)
						*nl = '\0';
					if (!strcmp(line, name)) {
						snprintf(name, sizeof(name), "%s", eq + 1);
						break;
					}
				}
				fclose(m);
			}
		}
		fprintf(f, "#EXTINF:-1 group-title=\"Auto\",%s\n", name);
		fprintf(f, "rtp://%u.%u.%u.%u:%u\n",
			(h->addr >> 24) & 0xff, (h->addr >> 16) & 0xff,
			(h->addr >> 8) & 0xff, h->addr & 0xff, h->port);
	}
	fclose(f);
	rename(tmp, out);
}

static void usage(void)
{
	fprintf(stderr,
		"usage: mcscan --iface IF --range CIDR[,CIDR] [options]\n"
		"  --ports 5140,5000     UDP ports to probe (default 5140)\n"
		"  --timeout 250         ms to wait per batch\n"
		"  --threads 8           parallel batches\n"
		"  --memberships 200     groups joined per socket\n"
		"  --min-bytes 1200      payload bytes required to accept a group\n"
		"  --map ip=name.txt     optional address -> channel name map\n"
		"  --out playlist.m3u    output playlist\n");
}

int main(int argc, char **argv)
{
	const char *iface = NULL, *out = NULL;
	char ports_arg[128] = "5140";
	char ranges_arg[1024] = "";
	uint16_t ports[MAX_PORTS];
	uint32_t bases[MAX_RANGES], counts[MAX_RANGES];
	int nports = 0, nranges = 0;
	uint64_t t0;
	pthread_t th[64];

	for (int i = 1; i < argc; i++) {
		if (!strcmp(argv[i], "--iface") && i + 1 < argc)
			iface = argv[++i];
		else if (!strcmp(argv[i], "--range") && i + 1 < argc)
			snprintf(ranges_arg, sizeof(ranges_arg), "%s", argv[++i]);
		else if (!strcmp(argv[i], "--ports") && i + 1 < argc)
			snprintf(ports_arg, sizeof(ports_arg), "%s", argv[++i]);
		else if (!strcmp(argv[i], "--timeout") && i + 1 < argc)
			g_timeout_ms = atoi(argv[++i]);
		else if (!strcmp(argv[i], "--threads") && i + 1 < argc)
			g_threads = atoi(argv[++i]);
		else if (!strcmp(argv[i], "--memberships") && i + 1 < argc)
			g_memberships = atoi(argv[++i]);
		else if (!strcmp(argv[i], "--min-bytes") && i + 1 < argc)
			g_min_bytes = atoi(argv[++i]);
		else if (!strcmp(argv[i], "--map") && i + 1 < argc)
			g_mapfile = argv[++i];
		else if (!strcmp(argv[i], "--out") && i + 1 < argc)
			out = argv[++i];
		else if (!strcmp(argv[i], "-h") || !strcmp(argv[i], "--help")) {
			usage();
			return 0;
		}
	}

	if (!iface || !ranges_arg[0] || !out) {
		usage();
		return 2;
	}

	g_ifindex = if_nametoindex(iface);
	if (!g_ifindex)
		die("unknown interface");

	for (char *tok = strtok(ports_arg, ","); tok && nports < MAX_PORTS;
	     tok = strtok(NULL, ","))
		ports[nports++] = (uint16_t)atoi(tok);

	for (char *tok = strtok(ranges_arg, ","); tok && nranges < MAX_RANGES;
	     tok = strtok(NULL, ",")) {
		if (parse_cidr(tok, &bases[nranges], &counts[nranges]) < 0)
			die("bad --range");
		nranges++;
	}

	build_segments(ports, nports, bases, counts, nranges);

	fprintf(stderr,
		"mcscan: iface=%s(idx %d) groups=%llu ports=%d timeout=%dms "
		"threads=%d memberships=%d\n",
		iface, g_ifindex, (unsigned long long)g_total, nports,
		g_timeout_ms, g_threads, g_memberships);

	if (g_threads > 64)
		g_threads = 64;
	if (g_memberships > 1024)
		g_memberships = 1024;

	t0 = now_ms();
	for (int i = 0; i < g_threads; i++)
		pthread_create(&th[i], NULL, worker, NULL);
	for (int i = 0; i < g_threads; i++)
		pthread_join(th[i], NULL);

	fprintf(stderr, "mcscan: %zu live group(s) in %.1f s\n",
		g_nhits, (now_ms() - t0) / 1000.0);

	write_m3u(out);
	return 0;
}
