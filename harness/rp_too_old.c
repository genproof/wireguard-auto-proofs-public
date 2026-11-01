// Law rp_too_old: For a new key's replay window (zero, as keypair_create makes it), after any sequence of any number
// of any nonces given to counter_validate, any nonce more than COUNTER_WINDOW_SIZE (8128) below the largest nonce
// accepted so far is rejected.
#include "wg_laws.h"

int main(void) {
	// Choose the inputs: any nonces; remember the largest one accepted
	struct noise_replay_counter window;
	new_counter(&window);
	u64 newest = 0;
	while (nondet_u8() != 0) {
		u64 nonce = any_u64();
		bool accepted = wg_counter_validate(&window, nonce);
		if (accepted && nonce > newest)
			newest = nonce;
	}
	// Any nonce n with newest - n > COUNTER_WINDOW_SIZE
	if (newest <= COUNTER_WINDOW_SIZE)
		return 0;
	u64 n = newest - COUNTER_WINDOW_SIZE - 1 - upto(newest - COUNTER_WINDOW_SIZE - 1);
	// Check. RFC 6479, section 2: "If S<WB, the packet is dropped."; receive.c: "This is RFC6479", with the window
	// [newest - COUNTER_WINDOW_SIZE, newest] (selftest/counter.c, tests 15, 19-21, 24, 34).
	bool accepted = wg_counter_validate(&window, n);
	gp_assert(accepted == 0);
	return 0;
}
