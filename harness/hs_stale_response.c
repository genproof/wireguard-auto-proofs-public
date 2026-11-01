// Law hs_stale_response: For devices A and B with any private keys and any preshared key, any clocks (boot clock
// below 2^62 ns) and any randomness: after A's initiation for B, B's consume of it and B's response, then a second
// initiation of A for B that succeeds, wg_noise_handshake_consume_response on A of B's response to the first
// initiation returns NULL. ASSUMPTION: the second initiation drew a sender index other than the first's (the index is
// a random 32-bit value, the same with probability 2^-32; then the law claims nothing). Nothing is assumed about the
// ephemeral keys: with a new index the old response no longer names A's handshake.
#include "hs_laws.h"

int main(void) {
	// Choose the inputs: the devices and their keys, any clocks
	struct pair p;
	new_pair(&p);
	any_clocks();
	// The first handshake attempt: A's initiation, B's response
	struct message_handshake_initiation first, second;
	struct message_handshake_response response;
	if (!wg_noise_handshake_create_initiation(&first, &p.a_peer.handshake))
		return 0;
	if (wg_noise_handshake_consume_initiation(&first, &p.b) == NULL)
		return 0;
	if (!wg_noise_handshake_create_response(&response, &p.b_peer.handshake))
		return 0;
	// A starts again before the response arrives, at any later clocks
	any_clocks();
	if (!wg_noise_handshake_create_initiation(&second, &p.a_peer.handshake))
		return 0;
	gp_assume(second.sender_index != first.sender_index);
	// The old response arrives. WireGuard paper, 5.4.2: I_i "is generated randomly when this message is sent, and is
	// used to tie subsequent replies to the session begun by this message".
	struct wg_peer *found = wg_noise_handshake_consume_response(&response, &p.a);
	// Check
	gp_assert(found == NULL);
	return 0;
}
