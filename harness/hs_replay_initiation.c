// Law hs_replay_initiation: For devices A and B with any private keys and any preshared key, any clocks (boot clock
// below 2^62 ns) and any randomness, once B's wg_noise_handshake_consume_initiation has accepted A's initiation, the
// same 148 bytes given to it again are rejected (it returns NULL), whatever the clocks read then (boot clock below
// 2^62 ns) and whether or not B has in between answered with wg_noise_handshake_create_response and begun its
// session with wg_noise_handshake_begin_session.
#include "hs_laws.h"

int main(void) {
	// Choose the inputs: the devices and their keys, any clocks
	struct pair p;
	new_pair(&p);
	any_clocks();
	// A's initiation, accepted by B
	struct message_handshake_initiation message;
	struct message_handshake_response response;
	if (!wg_noise_handshake_create_initiation(&message, &p.a_peer.handshake))
		return 0;
	if (wg_noise_handshake_consume_initiation(&message, &p.b) == NULL)
		return 0;
	// B answers and begins its session, or not
	if ((nondet_u8() & 1) && wg_noise_handshake_create_response(&response, &p.b_peer.handshake) && (nondet_u8() & 1))
		(void) wg_noise_handshake_begin_session(&p.b_peer.handshake, &p.b_peer.keypairs);
	// The same message again, at any clocks. WireGuard paper, 5.1: "The responder keeps track of the greatest
	// timestamp received per peer and discards packets containing timestamps less than or equal to it."
	any_clocks();
	struct wg_peer *again = wg_noise_handshake_consume_initiation(&message, &p.b);
	// Check
	gp_assert(again == NULL);
	return 0;
}
