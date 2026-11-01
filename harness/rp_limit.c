// Law rp_limit: For a new key's replay window (zero, as keypair_create makes it), after any sequence of any number of
// any nonces given to counter_validate, every nonce at or above REJECT_AFTER_MESSAGES (2^64 - 8130) is rejected.
#include "wg_laws.h"

int main(void) {
	// Choose the inputs: any nonces, then any nonce from REJECT_AFTER_MESSAGES to 2^64 - 1
	struct noise_replay_counter window;
	new_counter(&window);
	while (nondet_u8() != 0)
		(void) wg_counter_validate(&window, any_u64());
	u64 n = REJECT_AFTER + upto(U64_MAX - REJECT_AFTER);
	// Check. WireGuard paper, 6.2: "After Reject-After-Messages transport data messages ... WireGuard will refuse
	// to send or receive any more transport data messages using the current secure session"; the paper's table
	// gives 2^64 - 2^13 - 1, the kernel's messages.h "REJECT_AFTER_MESSAGES = U64_MAX - COUNTER_WINDOW_SIZE - 1"
	// (63 more); selftest/counter.c, tests 25, 27, 30, 31.
	bool accepted = wg_counter_validate(&window, n);
	gp_assert(accepted == 0);
	return 0;
}
