/* SPDX-License-Identifier: GPL-2.0 */
/*
 * QUICKPROOF S17 SHIM for drivers/net/wireguard/ratelimiter.h: the rate limiter's decision is an input chosen by the
 * harness (wg_shim_ratelimit_allow, patch/wg_shim.c); the token-bucket implementation is not covered.
 */
#ifndef _WG_RATELIMITER_H
#define _WG_RATELIMITER_H
#include "quickproof_net.h"
bool wg_ratelimiter_allow(struct sk_buff *skb, struct net *net);
#endif
