// Law hs_begin_session_state: For devices A and B with any private keys and any preshared key, and any sequence of
// any number of calls of wg_noise_handshake_begin_session on A's handshake with B, before each of which the handshake's
// state field is set to any 32-bit value and its ephemeral keys, hash, chaining key, remote index and latest timestamp
// to any bytes: every call made while the state is neither HANDSHAKE_CREATED_RESPONSE nor HANDSHAKE_CONSUMED_RESPONSE
// returns false, allocates nothing and leaves A's three keypair slots as they were. (The other calls may create
// keypairs, so the slots hold any keypairs that such calls left; the shim's allocator may fail at any call.)
#include "hs_laws.h"

int main(void) {
	// Choose the inputs: the devices and their keys
	struct pair p;
	new_pair(&p);
	struct noise_handshake *h = &p.a_peer.handshake;
	struct noise_keypairs *slots = &p.a_peer.keypairs;
	do {
		// Any session state of the handshake
		h->state = (enum noise_handshake_state) nondet_u32();
		h->remote_index = nondet_u32();
		nondet_bytes(h->ephemeral_private, 32);
		nondet_bytes(h->remote_ephemeral, 32);
		nondet_bytes(h->hash, 32);
		nondet_bytes(h->chaining_key, 32);
		nondet_bytes(h->latest_timestamp, 12);
		int completed = h->state == HANDSHAKE_CREATED_RESPONSE || h->state == HANDSHAKE_CONSUMED_RESPONSE;
		struct noise_keypair *current = slots->current_keypair;
		struct noise_keypair *previous = slots->previous_keypair;
		struct noise_keypair *next = slots->next_keypair;
		unsigned long allocations = wg_shim_allocs;
		// Begin a session. WireGuard paper, 5.4.5: "After the above two messages have been exchanged, keys are
		// calculated by the initiator and responder for sending and receiving transport data messages"; Noise,
		// 5.3, ReadMessage/WriteMessage: "If there are no more message patterns returns two new CipherState
		// objects by calling Split()".
		bool began = wg_noise_handshake_begin_session(h, slots);
		// Check
		if (completed == 0) {
			gp_assert(began == 0 && wg_shim_allocs == allocations);
			gp_assert(slots->current_keypair == current && slots->previous_keypair == previous);
			gp_assert(slots->next_keypair == next);
		}
	} while (nondet_u8() != 0);
	return 0;
}
