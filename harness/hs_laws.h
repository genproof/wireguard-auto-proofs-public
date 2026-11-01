// hs_laws.h: helpers shared by the handshake laws (hs_*): two devices with a peer for each other, set up as the
// kernel sets them up, and any clocks. No models, no algorithms.
#include "quickproof.h"
#include "noise.h"
#include "peer.h"
#include "device.h"
extern u64 wg_shim_boottime_ns;                       // the shim's clocks (patch/wg_shim.c): the laws set them
extern s64 wg_shim_real_sec;
extern long wg_shim_real_nsec;
extern unsigned long wg_shim_allocs;                  // the shim's count of successful kzalloc calls
static u64 any_u64(void) {                            // any 64-bit value
	u64 high = nondet_u32();
	return high << 32 | nondet_u32();
}
static int bytes_eq(const u8 *a, const u8 *b, size_t n) {   // a[0..n-1] == b[0..n-1]
	for (size_t i = 0; i < n; i++)
		if (a[i] != b[i])
			return 0;
	return 1;
}
static void any_clocks(void) {                        // any boot clock below 2^62 ns, any real-time clock
	wg_shim_boottime_ns = any_u64() >> 2;
	wg_shim_real_sec = (s64) any_u64();
	wg_shim_real_nsec = (long) (nondet_u32() % 1000000000u);
}
static void new_device(struct wg_device *wg, struct index_hashtable *indices, struct pubkey_hashtable *keys,
		       const u8 private_key[32]) {    // device.c (kzalloc'd), its private key set as netlink.c sets it
	wg->index_hashtable = indices;
	wg->peer_hashtable = keys;
	indices->head = NULL;
	keys->head = NULL;
	for (size_t i = 0; i < 32; i++)
		wg->static_identity.static_public[i] = 0;
	wg_noise_set_static_identity_private_key(&wg->static_identity, private_key);
}
static void new_peer(struct wg_peer *peer, struct wg_device *wg, const u8 public_key[32], const u8 psk[32]) {
	peer->device = wg;                            // peer.c, wg_peer_create: one reference, no keypairs, a new
	peer->is_dead = false;                        // handshake, listed in the device's public-key table
	peer->keypairs.current_keypair = NULL;
	peer->keypairs.previous_keypair = NULL;
	peer->keypairs.next_keypair = NULL;
	peer->refcount.refcount = 1;
	wg_noise_handshake_init(&peer->handshake, &wg->static_identity, public_key, psk, peer);
	peer->pubkey_next = wg->peer_hashtable->head;
	wg->peer_hashtable->head = peer;
}
struct pair {                                         // devices A and B, each with a peer for the other
	struct wg_device a, b;
	struct index_hashtable a_indices, b_indices;
	struct pubkey_hashtable a_keys, b_keys;
	struct wg_peer a_peer, b_peer;                // a_peer: A's peer for B; b_peer: B's peer for A
};
static void new_pair(struct pair *p) {                // any private keys, any preshared key (the same on both sides)
	u8 a_private[32], b_private[32], psk[32];
	nondet_bytes(a_private, 32);
	nondet_bytes(b_private, 32);
	nondet_bytes(psk, 32);
	wg_noise_init();
	new_device(&p->a, &p->a_indices, &p->a_keys, a_private);
	new_device(&p->b, &p->b_indices, &p->b_keys, b_private);
	new_peer(&p->a_peer, &p->a, p->b.static_identity.static_public, psk);
	new_peer(&p->b_peer, &p->b, p->a.static_identity.static_public, psk);
}
