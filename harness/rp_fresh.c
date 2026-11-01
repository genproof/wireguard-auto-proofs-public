// Law rp_fresh: For a new key's replay window (zero, as keypair_create makes it), any nonce n and any sequence of any
// number of other nonces given to counter_validate first, n is accepted when it is below REJECT_AFTER_MESSAGES
// (2^64 - 8130) and at most COUNTER_WINDOW_SIZE (8128) below the largest nonce accepted before it (or when none was
// accepted).
#include "wg_laws.h"

int main(void) {
	// Choose the inputs: the nonce n, then any other nonces in any order; remember the largest one accepted
	struct noise_replay_counter window;
	new_counter(&window);
	u64 n = any_u64();
	u64 newest = 0;
	int accepted_any = 0;
	while (nondet_u8() != 0) {
		u64 other = any_u64();
		if (other != n) {
			bool accepted = wg_counter_validate(&window, other);
			if (accepted && (accepted_any == 0 || other > newest))
				newest = other;
			if (accepted)
				accepted_any = 1;
		}
	}
	// Check. RFC 6479, section 2: "If S is inside window (S<=WT and S>=WB), then the receiver checks the
	// corresponding bit ... to see if this S has already been seen"; receive.c: "This is RFC6479"; the window is
	// the newest nonce and the COUNTER_WINDOW_SIZE below it (selftest/counter.c, tests 1, 2, 4-6, 8, 9, 11, 12,
	// 14, 17, 18, 22, 26, 29, 33).
	if (n < REJECT_AFTER && (accepted_any == 0 || n + COUNTER_WINDOW_SIZE >= newest)) {
		bool accepted = wg_counter_validate(&window, n);
		gp_assert(accepted != 0);
	}
	return 0;
}
