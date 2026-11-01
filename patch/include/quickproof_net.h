/* SPDX-License-Identifier: GPL-2.0 */
/*
 * quickproof_net.h: the socket buffer as cookie.c sees it.  QUICKPROOF S16 SHIM (not upstream code).
 *
 * cookie.c reads skb->data/len (the handshake message), skb->protocol, the IPv4 or IPv6 source address and the
 * UDP source port.  In the kernel ip_hdr/ipv6_hdr/udp_hdr point into the packet headroom; here the three headers
 * are fields of the buffer (only the fields cookie.c reads).  Addresses and port are bytes in network order.
 */
#ifndef QUICKPROOF_NET_H
#define QUICKPROOF_NET_H

#include "quickproof_kernel.h"

#define ETH_P_IP 0x0800
#define ETH_P_IPV6 0x86DD

struct in_addr { u8 s_addr[4]; };
struct in6_addr { u8 s6_addr[16]; };
struct iphdr { struct in_addr saddr; };
struct ipv6hdr { struct in6_addr saddr; };
struct udphdr { u8 source[2]; };

struct net_device { int unused; };
struct net { int unused; };

struct sk_buff {
	u8 *data;               /* the received message */
	unsigned int len;       /* its length */
	__be16 protocol;        /* htons(ETH_P_IP), htons(ETH_P_IPV6) or anything else */
	struct iphdr ip4;
	struct ipv6hdr ip6;
	struct udphdr udp;
};

#define ip_hdr(skb) (&(skb)->ip4)
#define ipv6_hdr(skb) (&(skb)->ip6)
#define udp_hdr(skb) (&(skb)->udp)
#define dev_net(dev) ((struct net *)0)

#endif /* QUICKPROOF_NET_H */
