/* SPDX-License-Identifier: GPL-2.0 */
/*
 * QUICKPROOF S13 SHIM for drivers/net/wireguard/device.h: struct wg_device reduced to what the handshake and the
 * cookie code touch (the static identity, the two lookup tables, the cookie checker).
 */
#ifndef _WG_DEVICE_H
#define _WG_DEVICE_H

#include "noise.h"
#include "cookie.h"
#include "peerlookup.h"

struct wg_device {
	struct net_device *dev;
	struct noise_static_identity static_identity;
	struct cookie_checker cookie_checker;
	struct pubkey_hashtable *peer_hashtable;
	struct index_hashtable *index_hashtable;
};

#endif /* _WG_DEVICE_H */
