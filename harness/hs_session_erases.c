// Law hs_session_erases: For devices A and B with any private keys and any preshared key, any clocks (boot clock
// below 2^62 ns) and any randomness, after A's wg_noise_handshake_create_initiation, B's consume_initiation, B's
// create_response and A's consume_response have all succeeded, each side's wg_noise_handshake_begin_session that
// returns true leaves that side's handshake in state HANDSHAKE_ZEROED with its ephemeral private key, the other
// side's ephemeral public key and its chaining key all zero. (The kernel also zeroes the hash, which the paper does
// not require; this law does not state it.)
#include "hs_laws.h"

static int zero(const u8 *bytes, size_t n) {          // bytes[0..n-1] are all 0
	for (size_t i = 0; i < n; i++)
		if (bytes[i] != 0)
			return 0;
	return 1;
}
static int erased(const struct noise_handshake *h) {
	return h->state == HANDSHAKE_ZEROED && zero(h->ephemeral_private, NOISE_PUBLIC_KEY_LEN) &&
	       zero(h->remote_ephemeral, NOISE_PUBLIC_KEY_LEN) && zero(h->chaining_key, NOISE_HASH_LEN);
}

int main(void) {
	// Choose the inputs: the devices and their keys, any clocks
	struct pair p;
	new_pair(&p);
	any_clocks();
	// The handshake
	struct message_handshake_initiation initiation;
	struct message_handshake_response response;
	if (!wg_noise_handshake_create_initiation(&initiation, &p.a_peer.handshake) ||
	    wg_noise_handshake_consume_initiation(&initiation, &p.b) == NULL ||
	    !wg_noise_handshake_create_response(&response, &p.b_peer.handshake) ||
	    wg_noise_handshake_consume_response(&response, &p.a) == NULL)
		return 0;
	// Both sessions. WireGuard paper, 5.4.5: "E_i^priv = E_i^pub = E_r^priv = E_r^pub = C_i = C_r := ε", "most
	// prior states of the handshake are zeroed from memory ..., but the value H_i = H_r is not necessarily zeroed".
	bool a_began = wg_noise_handshake_begin_session(&p.a_peer.handshake, &p.a_peer.keypairs);
	bool b_began = wg_noise_handshake_begin_session(&p.b_peer.handshake, &p.b_peer.keypairs);
	// Check
	if (a_began)
		gp_assert(erased(&p.a_peer.handshake) != 0);
	if (b_began)
		gp_assert(erased(&p.b_peer.handshake) != 0);
	return 0;
}
