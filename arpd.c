/*
 * arpd.c
 *
 * Copyright (c) 2001, 2002 Dug Song <dugsong@monkey.org>
 * Copyright (c) 2002 Niels Provos <provos@citi.umich.edu>
 *
 * $Id: arpd.c,v 1.16 2003/02/09 04:20:40 provos Exp $
 */

#include <sys/param.h>
#include <sys/types.h>
#include <sys/ioctl.h>
#include <sys/stat.h>

#include <pcap.h>

#include <err.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <syslog.h>
#include <unistd.h>

/* XXX - libevent */
#undef timeout_pending
#undef timeout_initialized

#include <event.h>
#include <dnet.h>

#define ARPD_MAX_ACTIVE		600
#define ARPD_MAX_INACTIVE	300

#define PIDFILE			"/var/run/farpd.pid"

struct arp_req {
	struct addr		pa;
	int			cnt;
	int			negative;

	struct event		active;
	struct event		inactive;
	struct event		discover;

	struct addr		ha;
};

int
compare(struct arp_req *a, struct arp_req *b)
{
	return (addr_cmp(&a->pa, &b->pa));
}

static pcap_t			*arpd_pcap;
static arp_t			*arpd_arp;
static eth_t			*arpd_eth;
static struct intf_entry	 arpd_ifent;
static int			 arpd_sig;

static void
usage(void)
{
	fprintf(stderr, "Usage: arpd [-d] [-i interface] [net]\n");
	exit(1);
}

/*
 * Expands several command line arguments into a complete pcap filter string.
 * Deals with normal CIDR notation and IP-IP ranges.
 */

static char *
arpd_expandips(int naddresses, char **addresses)
{
	static char filter[1024];
	char line[1024], *p;
	struct addr dst;

	if (naddresses == 0)
		return (NULL);

	filter[0] = '\0';

	while (naddresses--) {
		/* Get current address */
		p = *addresses++;

		if (filter[0] != '\0') {
			if (strlcat(filter, " or ", sizeof(filter)) >= sizeof(filter))
				errx(1, "%s: too many address for filter", 
				    __func__);
		}

		if (addr_pton(p, &dst) != -1) {

			snprintf(line, sizeof(line), "dst %s%s",
			    dst.addr_bits != 32 ? "net ": "", p);
		} else {
			char *first, *second;
			struct addr astart, aend;
			struct in_addr in;
			ip_addr_t istart, iend;

			second = p;

			first = strsep(&second, "-");
			if (second == NULL)
				errx(1, "%s: Invalid network range: %s",
				    __func__, p);

			line[0] = '\0';
			if (addr_pton(first, &astart) == -1 ||
			    addr_pton(second, &aend) == -1)
				errx(1, "%s: bad addresses %s-%s", __func__,
				    first, second);
#ifdef HAVE_BROKEN_DNET
			if (addr_cmp(&astart, &aend) <= 0)
#else
			if (addr_cmp(&astart, &aend) >= 0)
#endif
			    errx(1, "%s: inverted range %s-%s", __func__,
				first, second);

			/* Completely, IPv4 specific */
			istart = ntohl(astart.addr_ip);
			iend = ntohl(aend.addr_ip);
			while (istart <= iend) {
				char single[32];
				int count = 0, done = 0;
				ip_addr_t tmp;

				do {
					ip_addr_t bit = 1 << count;
					ip_addr_t mask;

					mask = ~(~0 << count);
					tmp = istart | mask;

					if (istart & bit)
						done = 1;

					if (iend < tmp) {
						count--;
						mask = ~(~0 << count);
						tmp = istart | mask;
						break;
					} else if (done)
						break;
					
					count++;
				} while (count < IP_ADDR_BITS);

				if (line[0] != '\0')
					strlcat(line, " or ", sizeof(line));
				in.s_addr = htonl(istart);
				snprintf(single, sizeof(single),
				    "dst net %s/%d",
				    inet_ntoa(in), 32 - count);

				strlcat(line, single, sizeof(line));

				istart = tmp + 1;
			}
		}
		
		if (strlcat(filter, line, sizeof(filter)) >= sizeof(filter))
			errx(1, "%s: too many address for filter", 
			    __func__);
	}

	return (filter);
}

static void
arpd_init(char *dev, int naddresses, char **addresses)
{
	struct bpf_program fcode;
	char filter[1024], ebuf[PCAP_ERRBUF_SIZE], *dst;
	intf_t *intf;
	
	dst = arpd_expandips(naddresses, addresses);

	if ((arpd_arp = arp_open()) == NULL)
		err(1, "arp_open");

	if ((intf = intf_open()) == NULL)
		err(1, "intf_open");

	if (dev == NULL) {
		if ((dev = pcap_lookupdev(ebuf)) == NULL)
			errx(1, "pcap_lookupdev: %s", ebuf);
	}
	arpd_ifent.intf_len = sizeof(arpd_ifent);
	strncpy(arpd_ifent.intf_name, dev, sizeof(arpd_ifent.intf_name) - 1);
	arpd_ifent.intf_name[sizeof(arpd_ifent.intf_name) - 1] = '\0';
	
	if (intf_get(intf, &arpd_ifent) < 0)
		err(1, "intf_get");

	if (arpd_ifent.intf_addr.addr_type != ADDR_TYPE_IP ||
	    arpd_ifent.intf_link_addr.addr_type != ADDR_TYPE_ETH)
		errx(1, "bad interface configuration: not IP or Ethernet");
	arpd_ifent.intf_addr.addr_bits = IP_ADDR_BITS;
	
	snprintf(filter, sizeof(filter), "arp %s%s%s and not ether src %s",
	    dst ? "and (" : "", dst ? dst : "", dst ? ")" : "",
	    addr_ntoa(&arpd_ifent.intf_link_addr));
	
	if ((arpd_pcap = pcap_open_live(dev, 128, 0, 500, ebuf)) == NULL)
		errx(1, "pcap_open_live: %s", ebuf);
	
	if (pcap_compile(arpd_pcap, &fcode, filter, 1, 0) < 0 ||
	    pcap_setfilter(arpd_pcap, &fcode) < 0)
		errx(1, "bad pcap filter: %s", pcap_geterr(arpd_pcap));
#if defined(BSD) && defined(BIOCIMMEDIATE)
	{
		int on = 1;
		if (ioctl(pcap_fileno(arpd_pcap), BIOCIMMEDIATE, &on) < 0)
			err(1, "BIOCIMMEDIATE");
	}
#endif
	if ((arpd_eth = eth_open(dev)) == NULL)
		errx(1, "eth_open");

#ifndef LOG_PERROR
#define LOG_PERROR	0
#endif
	openlog("arpd", LOG_PERROR|LOG_PID|LOG_CONS, LOG_DAEMON);
	syslog(LOG_INFO, "listening on %s: %s", dev, filter);
}

static void
arpd_exit(int status)
{
	eth_close(arpd_eth);
	pcap_close(arpd_pcap);
	arp_close(arpd_arp);
	closelog();
	unlink(PIDFILE);

	exit(status);
}

static void
arpd_send(eth_t *eth, int op,
    struct addr *sha, struct addr *spa,
    struct addr *tha, struct addr *tpa)
{
	u_char pkt[ETH_HDR_LEN + ARP_HDR_LEN + ARP_ETHIP_LEN];

	eth_pack_hdr(pkt, tha->addr_eth, sha->addr_eth, ETH_TYPE_ARP);
	arp_pack_hdr_ethip(pkt + ETH_HDR_LEN, op, sha->addr_eth,
	    spa->addr_ip, tha->addr_eth, tpa->addr_ip);
	
	if (op == ARP_OP_REQUEST) {
		syslog(LOG_DEBUG, "%s: who-has %s tell %s", __func__,
		    addr_ntoa(tpa), addr_ntoa(spa));
	} else if (op == ARP_OP_REPLY) {
		syslog(LOG_INFO, "arp reply %s is-at %s",
		    addr_ntoa(spa), addr_ntoa(sha));
	}
	if (eth_send(eth, pkt, sizeof(pkt)) != sizeof(pkt))
		syslog(LOG_ERR, "couldn't send packet: %m");
}

static int
arpd_lookup(struct addr *addr)
{
	struct arp_entry arpent;
	int error;

	if (addr_cmp(addr, &arpd_ifent.intf_addr) == 0) {
		syslog(LOG_DEBUG, "%s: %s at %s", __func__,
		    addr_ntoa(addr), addr_ntoa(&arpd_ifent.intf_link_addr));
		return (0);
	}
	memcpy(&arpent.arp_pa, addr, sizeof(*addr));
	
	error = arp_get(arpd_arp, &arpent);
	
	if (error == -1) {
		syslog(LOG_DEBUG, "%s: no entry for %s", __func__,
		    addr_ntoa(addr));
	} else {
		syslog(LOG_DEBUG, "%s: %s at %s", __func__,
		    addr_ntoa(addr), addr_ntoa(&arpent.arp_ha));
	}
	return (error);
}

static void
arpd_free(struct arp_req *req)
{
	timeout_del(&req->active);
	timeout_del(&req->inactive);
	timeout_del(&req->discover);
	free(req);
}

static void
arpd_timeout(int fd, short event, void *arg)
{
	struct arp_req *req = arg;
	
	syslog(LOG_DEBUG, "%s: expiring %s", __func__, addr_ntoa(&req->pa));
	arpd_free(req);
}

static void
arpd_discover(struct arp_req *req, struct addr *ha)
{
	struct timeval tv = {0, 500000};

	if (ha != NULL)
		memcpy(&req->ha, ha, sizeof(*ha));

	if (req->cnt < 2) {
		arpd_send(arpd_eth, ARP_OP_REQUEST,
		    &arpd_ifent.intf_link_addr,
		    &arpd_ifent.intf_addr, &req->ha, &req->pa);
		timeout_add(&req->discover, &tv);
	}
	req->cnt++;
}

static void
arpd_discovercb(int fd, short event, void *arg)
{
	struct arp_req *req = arg;

	arpd_discover(req, NULL);
}

static void
arpd_recv_cb(u_char *u, const struct pcap_pkthdr *pkthdr, const u_char *pkt)
{
	struct arp_hdr *arp;
	struct arp_ethip *ethip;
	struct arp_req *req, tmp;
	struct arp_entry src;
	struct timeval tv;

	if (pkthdr->caplen < ETH_HDR_LEN + ARP_HDR_LEN + ARP_ETHIP_LEN)
		return;

	arp = (struct arp_hdr *)(pkt + ETH_HDR_LEN);	/* XXX */
	ethip = (struct arp_ethip *)(arp + 1);
	
	addr_pack(&src.arp_ha, ADDR_TYPE_ETH, ETH_ADDR_BITS,
	    ETH_ADDR_BROADCAST, ETH_ADDR_LEN);
	addr_pack(&src.arp_pa, ADDR_TYPE_IP, IP_ADDR_BITS,
	    ethip->ar_spa, IP_ADDR_LEN);
	    
	switch (ntohs(arp->ar_op)) {
		
	case ARP_OP_REQUEST:
		addr_pack(&tmp.pa, ADDR_TYPE_IP, IP_ADDR_BITS,
		    &ethip->ar_tpa, IP_ADDR_LEN);

			arpd_send(arpd_eth, ARP_OP_REPLY,
			    &arpd_ifent.intf_link_addr, &tmp.pa,
			    &src.arp_ha, &src.arp_pa);
		break;
		
	case ARP_OP_REPLY:
		addr_pack(&tmp.pa, ADDR_TYPE_IP, IP_ADDR_BITS,
		    &ethip->ar_spa, IP_ADDR_LEN);
		break;
	}
}

static void
arpd_recv(int fd, short type, void *ev)
{
	event_add((struct event *)ev, NULL);
	
	if (pcap_dispatch(arpd_pcap, -1, arpd_recv_cb, NULL) < 0)
		syslog(LOG_ERR, "pcap_dispatch: %s", pcap_geterr(arpd_pcap));
}
 
void
terminate_handler(int sig)
{
	arpd_sig = sig;
}

int
arpd_signal(void)
{
	syslog(LOG_INFO, "exiting on signal %d", arpd_sig);
	arpd_exit(0);
	/* NOTREACHED */
	return (-1);
}

int
main(int argc, char *argv[])
{
	struct event recv_ev;
	char *dev;
	int c, debug;
	FILE *fp;

	dev = NULL;
	debug = 0;
	
	while ((c = getopt(argc, argv, "di:h?")) != -1) {
		switch (c) {
		case 'd':
			debug = 1;
			break;
		case 'i':
			dev = optarg;
			break;
		default:
			usage();
			break;
		}
	}
	argc -= optind;
	argv += optind;

	if (argc == 0)
		arpd_init(dev, 0, NULL);
	else
		arpd_init(dev, argc, argv);
	
	if ((fp = fopen(PIDFILE, "w")) == NULL)
		err(1, "fopen");
	
	if (!debug) {
		setlogmask(LOG_UPTO(LOG_INFO));
		
		if (daemon(1, 0) < 0) {
			unlink(PIDFILE);
			err(1, "daemon");
		}
	}
	fprintf(fp, "%d\n", getpid());
	fclose(fp);
	
	chmod(PIDFILE, 0644);

	event_init();
	
	event_set(&recv_ev, pcap_fileno(arpd_pcap), EV_READ,
	    arpd_recv, &recv_ev);
	event_add(&recv_ev, NULL);
	
	/* Setup signal handler */
	if (signal(SIGINT, terminate_handler) == SIG_ERR) {
		perror("signal");
		return (-1);
	}
	if (signal(SIGTERM, terminate_handler) == SIG_ERR) {
		perror("signal");
		return (-1);
	}
	
	event_dispatch();

	return (0);
}
