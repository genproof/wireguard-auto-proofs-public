/* SPDX-License-Identifier: GPL-2.0-or-later */
/*
 * QUICKPROOF S09 SHIM for include/crypto/utils.h: the same interface in plain C, byte by byte.
 *
 * Upstream's crypto_xor_cpy/__crypto_xor work in words chosen by pointer alignment (casts of pointers to
 * integers, word loads through u64 pointers), which have no meaning in CompCert's memory model; the kernel's
 * crypto_memneq is an optimisation barrier around the same OR of differences.  Both are replaced by the
 * obvious loops, with the upstream results (crypto_memneq: 0 when equal, 1 otherwise).  memzero_explicit is
 * memset (quickproof_kernel.h).
 */
#ifndef _CRYPTO_UTILS_H
#define _CRYPTO_UTILS_H

#include "../quickproof_kernel.h"

unsigned long __crypto_memneq(const void *a, const void *b, size_t size);
void __crypto_xor(u8 *dst, const u8 *src1, const u8 *src2, unsigned int size);

static inline int crypto_memneq(const void *a, const void *b, size_t size)
{
	return __crypto_memneq(a, b, size) != 0UL ? 1 : 0;
}

static inline void crypto_xor_cpy(u8 *dst, const u8 *src1, const u8 *src2, unsigned int size)
{
	__crypto_xor(dst, src1, src2, size);
}

static inline void crypto_xor(u8 *dst, const u8 *src, unsigned int size)
{
	__crypto_xor(dst, dst, src, size);
}

#endif /* _CRYPTO_UTILS_H */
