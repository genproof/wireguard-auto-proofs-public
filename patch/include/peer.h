/* SPDX-License-Identifier: GPL-2.0 */
/*
 * QUICKPROOF S12 SHIM for drivers/net/wireguard/peer.h: struct wg_peer reduced to what the handshake and the cookie
 * code touch.  The field names and types are upstream's; queues, timers, endpoint, NAPI, statistics and list
 * heads are omitted, and pubkey_next links the peer into the device's public-key table (shim peerlookup.h).
 * Peers belong to the harness: wg_peer_put only counts (the release function of upstream frees the peer after an
 * RCU grace period; here reaching 0 is recorded in wg_shim_peer_released and nothing is freed).
 */
#ifndef _WG_PEER_H
#define _WG_PEER_H

#include "device.h"
#include "noise.h"
#include "cookie.h"

struct wg_peer {
	struct wg_device *device;
	bool is_dead;
	struct noise_keypairs keypairs;
	struct noise_handshake handshake;
	atomic64_t last_sent_handshake;
	struct cookie latest_cookie;
	struct kref refcount;
	u64 internal_id;
	struct wg_peer *pubkey_next;
};

static inline struct wg_peer *wg_peer_get(struct wg_peer *peer)
{
	kref_get(&peer->refcount);
	return peer;
}
struct wg_peer *wg_peer_get_maybe_zero(struct wg_peer *peer);
void wg_peer_put(struct wg_peer *peer);

#endif /* _WG_PEER_H */
