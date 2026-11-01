// SPDX-License-Identifier: GPL-2.0
// Law `transport_send_nonce`: the per-keypair sending nonce is monotonic and never repeats, sending is
// refused at REJECT_AFTER_MESSAGES, and a key's nonce never wraps.
//
// !!! MODEL ONLY -- NOT backed by extracted upstream code (DEVIATIONS.md L16). !!!
// drivers/net/wireguard/send.c is NOT part of the code under test (receive.c is; the handshake laws never needed
// send.c), so wg_packet_send_staged_packets' nonce draw cannot be called.  This
// harness writes that draw out as send.c has it at the pin (send.c:363-364, 379-382, 391-392):
//     if (!READ_ONCE(keypair->sending.is_valid)) goto out_nokey;          -- no nonce on an invalid key
//     nonce = atomic64_inc_return(&keypair->sending_counter) - 1;
//     if (nonce >= REJECT_AFTER_MESSAGES) goto out_invalid;               -- out_invalid: is_valid = false
// with the shim's atomic64_inc_return (quickproof_kref.h, which wraps like the kernel's atomic64) and the kernel's
// REJECT_AFTER_MESSAGES as compiled (messages.h; DEVIATIONS.md C04), so the law is READY to be pointed at the real
// draw once send.c is added (the send path also pulls in skb allocation, padding to MESSAGE_PADDING_MULTIPLE, and
// the per-peer tx queue).
//
// A sending keypair in ANY state a valid key can be in -- counter = any value in [0, REJECT_AFTER_MESSAGES], as
// after that many messages (0, near REJECT_AFTER_MESSAGES, around 2^63, anywhere) -- then a sequence of ANY length
// of draws as above.
// Shadow model: shadow (u64) tracks the counter; nonce_model = shadow (the pre-increment value), shadow += 1;
// R = REJECT_AFTER_MESSAGES = 2^64 - 1 - 8128 - 1, computed here (as counter.c does).
// CHECKs after every draw:
//   - the drawn nonce == nonce_model  => strictly monotonic, increments by exactly 1, never repeats;
//   - the kernel's refusal test (nonce >= REJECT_AFTER_MESSAGES as compiled) == (nonce >= R)  => sending refused
//     exactly at the limit;
// and at the end: the counter == shadow <= R + 1 (at most one refused draw per key: the counter never wraps, so a
// nonce is never issued twice over the key's life).  (The kernel never draws on an invalid key, and the law models
// that rule: for the bare counter, "once refused, every later draw is refused" would be false for an unbounded
// number of draws, since the u64 nonce wraps to 0 after 8130 refused draws from R.)
#include "transport.h"

#define S64_TOP 0x7fffffffffffffffULL        // the largest s64: the shim's `++` must not step past it (L16)

int main(void)
{
	struct noise_keypair kp;             // only sending.is_valid and sending_counter are used
	u64 shadow, start;
	size_t steps, i;

	// Start values: any counter of a valid key, [0, R].  ASSUMPTION (DEVIATIONS.md L16, of the class of L02): the
	// run ends before the counter would step from 2^63 - 1 to 2^63 (a key never sends 2^63 messages:
	// it expires after REJECT_AFTER_TIME, 180 s); nonces >= 2^63 are still drawn, from starts in [2^63, R].  (The shim's increment
	// wraps like the kernel's atomic64 (quickproof_kref.h), so this guard is not needed for definedness; it is part
	// of the law as stated.)
	switch (nondet_u8() % 5) {
	case 0: start = 0; break;                                                // a fresh key
	case 1: start = M_R - (u64)(nondet_u32() % 8); break;                   // just below / at the limit
	case 2: start = (1ULL << 63) + draw_u64() % (M_R - (1ULL << 63) + 1); break;  // upper half, up to the limit
	case 3: start = S64_TOP - (u64)(nondet_u32() % 8); break;               // just below the s64 boundary
	default: start = draw_u64() % (M_R + 1); break;                         // anywhere a valid key can be
	}
	kp.sending.is_valid = true;
	atomic64_set(&kp.sending_counter, (s64)start);
	shadow = start;

	steps = draw_steps();
	for (i = 0; i < steps; i++) {
		u64 v, nonce, nonce_model;

		if (!READ_ONCE(kp.sending.is_valid))              // send.c:363: no nonce on an invalid key
			break;
		if (shadow == S64_TOP)                            // L16: the shim's s64 `++` would overflow
			break;
		v = (u64)atomic64_inc_return(&kp.sending_counter);  // send.c:379-380, the draw
		nonce = v - 1;
		nonce_model = shadow;
		shadow += 1;

		CHECK(nonce == nonce_model);                     // monotonic, +1 each draw, never repeats
		CHECK((nonce >= REJECT_AFTER_MESSAGES) == (nonce >= M_R));  // refused exactly at the limit
		if (nonce >= REJECT_AFTER_MESSAGES)              // send.c:381-382, 391-392
			WRITE_ONCE(kp.sending.is_valid, false);
	}
	CHECK((u64)kp.sending_counter.counter == shadow);
	CHECK(shadow <= M_R + 1);                                // at most one refused draw: the nonce never wraps
	return 0;
}
