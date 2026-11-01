// SPDX-License-Identifier: GPL-2.0
/*
 * counter_validate.c: the data-path replay window of drivers/net/wireguard/receive.c, extracted.
 *
 * QUICKPROOF S19 (DEVIATIONS.md): the function between the markers is upstream's text, byte for byte
 * (receive.c at the pinned commit, the lines before `#include "selftest/counter.c"`); patch/wgpatch.py checks
 * that it still equals the text of receive.c at the pin, then applies the goto rewrite (P10) in the patched
 * tree.  The rest of receive.c (packet handling) is not compiled.  wg_counter_validate is a non-static wrapper
 * so that a harness can call the static function (S19).  Copyright (C) 2015-2019 Jason A. Donenfeld
 * <Jason@zx2c4.com>.  All Rights Reserved.
 */
#include "quickproof_kernel.h"
#include "noise.h"
#include "messages.h"

bool wg_counter_validate(struct noise_replay_counter *counter, u64 their_counter);

/* ---- BEGIN UPSTREAM receive.c ---- */
/* This is RFC6479, a replay detection bitmap algorithm that avoids bitshifts */
static bool counter_validate(struct noise_replay_counter *counter, u64 their_counter)
{
	unsigned long index, index_current, top, i;
	bool ret = false;

	spin_lock_bh(&counter->lock);

	if (unlikely(counter->counter >= REJECT_AFTER_MESSAGES + 1 ||
		     their_counter >= REJECT_AFTER_MESSAGES))
		goto out;

	++their_counter;

	if (unlikely((COUNTER_WINDOW_SIZE + their_counter) <
		     counter->counter))
		goto out;

	index = their_counter >> ilog2(BITS_PER_LONG);

	if (likely(their_counter > counter->counter)) {
		index_current = counter->counter >> ilog2(BITS_PER_LONG);
		top = min_t(unsigned long, index - index_current,
			    COUNTER_BITS_TOTAL / BITS_PER_LONG);
		for (i = 1; i <= top; ++i)
			counter->backtrack[(i + index_current) &
				((COUNTER_BITS_TOTAL / BITS_PER_LONG) - 1)] = 0;
		WRITE_ONCE(counter->counter, their_counter);
	}

	index &= (COUNTER_BITS_TOTAL / BITS_PER_LONG) - 1;
	ret = !test_and_set_bit(their_counter & (BITS_PER_LONG - 1),
				&counter->backtrack[index]);

out:
	spin_unlock_bh(&counter->lock);
	return ret;
}
/* ---- END UPSTREAM receive.c ---- */

bool wg_counter_validate(struct noise_replay_counter *counter, u64 their_counter)
{
	return counter_validate(counter, their_counter);
}
