// Law rp_duplicate: For a new key's replay window (zero, as keypair_create makes it), after any sequence of any number
// of any nonces given to counter_validate, a nonce that it accepts is rejected when it is given again, after any
// further sequence of any number of any nonces.
#include "wg_laws.h"

int main(void) {
	// Choose the inputs: any nonces, then the nonce n
	struct noise_replay_counter window;
	new_counter(&window);
	while (nondet_u8() != 0)
		(void) wg_counter_validate(&window, any_u64());
	u64 n = any_u64();
	bool first = wg_counter_validate(&window, n);
	if (first == 0)
		return 0;
	// Any nonces after it, n among them or not
	while (nondet_u8() != 0)
		(void) wg_counter_validate(&window, any_u64());
	// Check. RFC 6479, section 2: the bit of each sequence number "indicates whether or not a packet with that
	// sequence number has been received and authenticated, so that the replay packet can be detected and
	// rejected"; receive.c: "This is RFC6479"; selftest/counter.c, tests 3, 7, 10, 13, 16, 23, 28, 32.
	bool again = wg_counter_validate(&window, n);
	gp_assert(again == 0);
	return 0;
}
