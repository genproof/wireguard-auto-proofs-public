// Law hs_response_state: For devices A and B with any private keys and any preshared key, any clocks (boot clock
// below 2^62 ns) and any randomness, after A's wg_noise_handshake_create_initiation for B, B's consume_initiation of
// it and B's create_response, with the state field of A's handshake then set to any 32-bit value other than
// HANDSHAKE_CREATED_INITIATION, A's wg_noise_handshake_consume_response of B's response returns NULL: a response is
// taken only by a handshake that is waiting for one.
#include "hs_laws.h"

int main(void) {
	// Choose the inputs: the devices and their keys, any clocks
	struct pair p;
	new_pair(&p);
	any_clocks();
	// A's initiation and B's response
	struct message_handshake_initiation initiation;
	struct message_handshake_response response;
	if (!wg_noise_handshake_create_initiation(&initiation, &p.a_peer.handshake))
		return 0;
	if (wg_noise_handshake_consume_initiation(&initiation, &p.b) == NULL)
		return 0;
	if (!wg_noise_handshake_create_response(&response, &p.b_peer.handshake))
		return 0;
	// A's handshake in any other state
	p.a_peer.handshake.state = (enum noise_handshake_state) nondet_u32();
	if (p.a_peer.handshake.state == HANDSHAKE_CREATED_INITIATION)
		return 0;
	// Consume. WireGuard paper, 5.4.2: I_i "is used to tie subsequent replies to the session begun by this
	// message"; Noise, 5.3: a HandshakeState processes its "message_patterns: A sequence of message patterns" in
	// order, the responder's message after the initiator's.
	struct wg_peer *found = wg_noise_handshake_consume_response(&response, &p.a);
	// Check
	gp_assert(found == NULL);
	return 0;
}
