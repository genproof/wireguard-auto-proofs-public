// Law rp_any_order: For a new key's replay window (zero, as keypair_create makes it), any start s with
// s + COUNTER_WINDOW_SIZE below REJECT_AFTER_MESSAGES (2^64 - 8130), and any sequence of any number of nonces below s
// given to counter_validate first, any distinct nonces from s to s + COUNTER_WINDOW_SIZE (8128), given in any order,
// are all accepted.
#include "wg_laws.h"

int main(void) {
	// Choose the inputs: the start s, then any nonces below it
	struct noise_replay_counter window;
	new_counter(&window);
	u64 start = upto(REJECT_AFTER - 1 - COUNTER_WINDOW_SIZE);
	while (start > 0 && nondet_u8() != 0)
		(void) wg_counter_validate(&window, upto(start - 1));
	// Then any nonces of the window [s, s + COUNTER_WINDOW_SIZE] in any order, each the first time it comes
	u8 seen[COUNTER_WINDOW_SIZE + 1];
	for (size_t i = 0; i <= COUNTER_WINDOW_SIZE; i++)
		seen[i] = 0;
	while (nondet_u8() != 0) {
		size_t offset = upto(COUNTER_WINDOW_SIZE);
		if (seen[offset] == 0) {
			seen[offset] = 1;
			// Check. WireGuard paper, 5.4.6: "messages can sometimes arrive out of order. For that reason we use
			// a sliding window"; selftest/counter.c checks the window's COUNTER_WINDOW_SIZE + 1 nonces in
			// ascending and descending order ("for (i = COUNTER_WINDOW_SIZE + 1; i-- > 0;) T(i, true);").
			bool accepted = wg_counter_validate(&window, start + offset);
			gp_assert(accepted != 0);
		}
	}
	return 0;
}
