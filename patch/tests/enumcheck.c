// SPDX-License-Identifier: GPL-2.0
// patch/tests/enumcheck.c (DEVIATIONS.md C04): CompCert types enumeration constants as int and truncates the
// ones above INT_MAX (a warning), where gcc gives them a wider type.  This program prints every use of such a
// constant in the code under test, as that code writes it (same operand types); enumcheck.sh runs it compiled by
// gcc and under CompCert's interpreter and compares the output.
#include "quickproof_kernel.h"
#include "messages.h"
#include <crypto/blake2s.h>
#include <stdio.h>

int main(void)
{
	u32 h[8], t0 = 0x12345678u, t1 = 0x9abcdef0u, f0 = 0xffffffffu, f1 = 0;
	size_t keylen = 32, outlen = 16;
	u64 counter = 0xfffffffffffff000ULL, their = 0xffffffffffffe03dULL;
	/* __blake2s_init */
	h[0] = BLAKE2S_IV0 ^ (0x01010000 | keylen << 8 | outlen);
	h[1] = BLAKE2S_IV1; h[2] = BLAKE2S_IV2; h[3] = BLAKE2S_IV3;
	h[4] = BLAKE2S_IV4; h[5] = BLAKE2S_IV5; h[6] = BLAKE2S_IV6; h[7] = BLAKE2S_IV7;
	for (int i = 0; i < 8; i++)
		printf("h[%d] = %08x\n", i, h[i]);
	/* blake2s_compress_generic */
	printf("v12..15 = %08x %08x %08x %08x\n", (u32)(BLAKE2S_IV4 ^ t0), (u32)(BLAKE2S_IV5 ^ t1), (u32)(BLAKE2S_IV6 ^ f0),
	       (u32)(BLAKE2S_IV7 ^ f1));
	/* counter_validate (receive.c) */
	printf("counter >= REJECT + 1: %d\n", counter >= REJECT_AFTER_MESSAGES + 1);
	printf("their >= REJECT: %d, %d\n", their >= REJECT_AFTER_MESSAGES, (their + 1) >= REJECT_AFTER_MESSAGES);
	printf("REJECT as u64: %016llx\n", (unsigned long long)(u64)REJECT_AFTER_MESSAGES);
	printf("REJECT + 1 as u64: %016llx\n", (unsigned long long)(u64)(REJECT_AFTER_MESSAGES + 1));
	printf("WINDOW + their < counter: %d\n", (COUNTER_WINDOW_SIZE + their) < counter);
	/* noise.h: wg_noise_reset_last_sent_handshake */
	printf("rekey: %llu\n", (unsigned long long)((u64)(REKEY_TIMEOUT + 1) * NSEC_PER_SEC));
	return 0;
}
