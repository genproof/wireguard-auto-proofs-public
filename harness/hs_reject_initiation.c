// Law hs_reject_initiation: For devices A and B with any private keys and any preshared key, B's handshake with A in
// any state (its state field any 32-bit value; its ephemeral keys, hash, chaining key, remote index and latest
// timestamp any bytes; its last consumption time any value below 2^62 ns), any clocks (boot clock below 2^62 ns) and
// any 148 bytes as an initiation message, a wg_noise_handshake_consume_initiation on B that fails (returns NULL)
// leaves every field of B's handshake with A, its keypair slots and its reference count as they were. Besides any
// bytes, the message may be A's genuine initiation (made with any randomness), so that runs reach every check.
#include "hs_unchanged.h"

int main(void) {
	// Choose the inputs: the devices and their keys, any clocks
	struct pair p;
	new_pair(&p);
	any_clocks();
	// Any message: any bytes, or A's own initiation
	struct message_handshake_initiation message;
	message.header.type = nondet_u32();
	message.sender_index = nondet_u32();
	nondet_bytes(message.unencrypted_ephemeral, sizeof message.unencrypted_ephemeral);
	nondet_bytes(message.encrypted_static, sizeof message.encrypted_static);
	nondet_bytes(message.encrypted_timestamp, sizeof message.encrypted_timestamp);
	nondet_bytes(message.macs.mac1, sizeof message.macs.mac1);
	nondet_bytes(message.macs.mac2, sizeof message.macs.mac2);
	if (nondet_u8() & 1)
		(void) wg_noise_handshake_create_initiation(&message, &p.a_peer.handshake);
	// Any state of B's handshake with A
	struct noise_handshake *h = &p.b_peer.handshake;
	h->state = (enum noise_handshake_state) nondet_u32();
	h->remote_index = nondet_u32();
	h->last_initiation_consumption = any_u64() >> 2;
	nondet_bytes(h->ephemeral_private, 32);
	nondet_bytes(h->remote_ephemeral, 32);
	nondet_bytes(h->hash, 32);
	nondet_bytes(h->chaining_key, 32);
	nondet_bytes(h->latest_timestamp, 12);
	struct wg_peer before;
	copy_peer(&before, &p.b_peer);
	// Consume. WireGuard paper, 5.1: "Several classes of attacks are avoided by not allowing unauthenticated packets
	// to influence any state", and "The responder keeps track of the greatest timestamp received per peer and
	// discards packets containing timestamps less than or equal to it."
	struct wg_peer *found = wg_noise_handshake_consume_initiation(&message, &p.b);
	// Check
	if (found == NULL)
		gp_assert(same_peer(&p.b_peer, &before) != 0);
	return 0;
}
