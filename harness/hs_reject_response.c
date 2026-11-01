// Law hs_reject_response: For devices A and B with any private keys and any preshared key, any clocks (boot clock
// below 2^62 ns) and any randomness, after A's wg_noise_handshake_create_initiation for B, with A's handshake state
// field then set to any 32-bit value or left as it is, a wg_noise_handshake_consume_response on A of any 92 bytes
// that fails (returns NULL) leaves every field of A's handshake with B, its keypair slots and its reference count as
// they were. Besides any bytes, the message may carry A's sender index, or be B's genuine response to the initiation,
// so that runs reach every check.
#include "hs_unchanged.h"

int main(void) {
	// Choose the inputs: the devices and their keys, any clocks, A's initiation
	struct pair p;
	new_pair(&p);
	any_clocks();
	struct message_handshake_initiation initiation;
	bool initiated = wg_noise_handshake_create_initiation(&initiation, &p.a_peer.handshake);
	// Any message: any bytes, or with A's index, or B's response
	struct message_handshake_response message;
	message.header.type = nondet_u32();
	message.sender_index = nondet_u32();
	message.receiver_index = nondet_u32();
	nondet_bytes(message.unencrypted_ephemeral, sizeof message.unencrypted_ephemeral);
	nondet_bytes(message.encrypted_nothing, sizeof message.encrypted_nothing);
	nondet_bytes(message.macs.mac1, sizeof message.macs.mac1);
	nondet_bytes(message.macs.mac2, sizeof message.macs.mac2);
	if (initiated && (nondet_u8() & 1))
		message.receiver_index = initiation.sender_index;
	if (initiated && (nondet_u8() & 1) && wg_noise_handshake_consume_initiation(&initiation, &p.b) != NULL)
		(void) wg_noise_handshake_create_response(&message, &p.b_peer.handshake);
	// A's handshake state: any, or as the initiation left it
	if (nondet_u8() & 1)
		p.a_peer.handshake.state = (enum noise_handshake_state) nondet_u32();
	struct wg_peer before;
	copy_peer(&before, &p.a_peer);
	// Consume. WireGuard paper, 5.1: "Several classes of attacks are avoided by not allowing unauthenticated packets
	// to influence any state"; Noise, 5.3, ReadMessage: "aborting if any DecryptAndHash() call returns an error".
	struct wg_peer *found = wg_noise_handshake_consume_response(&message, &p.a);
	// Check
	if (found == NULL)
		gp_assert(same_peer(&p.a_peer, &before) != 0);
	return 0;
}
