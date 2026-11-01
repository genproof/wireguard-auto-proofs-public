// Law hs_matching_keys: For devices A and B with any private keys and any preshared key, any clocks (boot clock below
// 2^62 ns) and any randomness, if A's wg_noise_handshake_create_initiation, B's consume_initiation, B's
// create_response, A's consume_response, and wg_noise_handshake_begin_session on both sides all succeed, then the
// sending key of A's new current keypair is the receiving key of B's new next keypair and vice versa, and A's keypair
// is the initiator's and B's is not.
#include "hs_laws.h"

int main(void) {
	// Choose the inputs: the devices and their keys, any clocks
	struct pair p;
	new_pair(&p);
	any_clocks();
	// The handshake
	struct message_handshake_initiation initiation;
	struct message_handshake_response response;
	if (!wg_noise_handshake_create_initiation(&initiation, &p.a_peer.handshake))
		return 0;
	if (wg_noise_handshake_consume_initiation(&initiation, &p.b) == NULL)
		return 0;
	if (!wg_noise_handshake_create_response(&response, &p.b_peer.handshake))
		return 0;
	if (wg_noise_handshake_consume_response(&response, &p.a) == NULL)
		return 0;
	if (!wg_noise_handshake_begin_session(&p.a_peer.handshake, &p.a_peer.keypairs))
		return 0;
	if (!wg_noise_handshake_begin_session(&p.b_peer.handshake, &p.b_peer.keypairs))
		return 0;
	// Check. WireGuard paper, 5.4.5: "(T_i^send = T_r^recv, T_i^recv = T_r^send) := Kdf2(C_i = C_r, ε)"; noise.c,
	// add_new_keypair: the initiator's new keypair becomes current, the responder's becomes next.
	struct noise_keypair *a = p.a_peer.keypairs.current_keypair, *b = p.b_peer.keypairs.next_keypair;
	gp_assert(a != NULL && b != NULL);
	gp_assert(bytes_eq(a->sending.key, b->receiving.key, NOISE_SYMMETRIC_KEY_LEN) != 0);
	gp_assert(bytes_eq(a->receiving.key, b->sending.key, NOISE_SYMMETRIC_KEY_LEN) != 0);
	gp_assert(a->i_am_the_initiator != 0 && b->i_am_the_initiator == 0);
	return 0;
}
