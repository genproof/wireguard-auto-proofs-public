/* SPDX-License-Identifier: GPL-2.0 */
/*
 * quickproof_kref.h: QUICKPROOF S04: the kernel's reference counts, exactly.  Included by linux/kref.h
 * (that is, by every unit that uses kref: noise.c and cookie.c through noise.h, the shim, the harnesses), after
 * quickproof_kernel.h, whose plain-counter kref and atomic64_inc_return it REPLACES here.  (quickproof_kernel.h keeps
 * that text, unused, so that the units that never use kref - the crypto primitives - are translated to exactly the
 * same Clight as before: clightgen numbers anonymous composites by the count of declarations before them.)
 *
 * atomic64_inc_return: the kernel's atomics wrap (two's complement); so does this (the sum in u64, the conversion
 * to s64 wraps in gcc and CompCert; no signed overflow).
 *
 * kref = the kernel's refcount_t (include/linux/refcount.h, include/linux/kref.h, lib/refcount.c at the pinned
 * commit), single-threaded: the count is the bits of the kernel's atomic_t (an int), read unsigned; it SATURATES
 * like refcount_t: a get that finds INT_MAX or a negative count, a put that finds 0 or a negative count, and a
 * kref_get of 0 set the count to REFCOUNT_SATURATED = INT_MIN / 2 and record a warning of the kernel's type in
 * wg_shim_refcount_warn[] (the kernel's refcount_warn_saturate WARN_ONCEs); a saturated count stays saturated and
 * its object is never released (the kernel's "saturated; leaking memory").  Exact for one thread: the kernel's
 * racy window (the count briefly INT_MIN before the store of REFCOUNT_SATURATED) closes before the next statement.
 * The operations are functions of patch/wg_shim.c; patch/tests/refcount_check.sh compiles the kernel's own text of
 * __refcount_add_not_zero, __refcount_add, __refcount_sub_and_test and refcount_warn_saturate (taken from the
 * pinned commit) and compares them with these on every edge value and on random operation sequences.
 */
#ifndef QUICKPROOF_KREF_H
#define QUICKPROOF_KREF_H

#include "quickproof_kernel.h"

#undef atomic64_inc_return
#define atomic64_inc_return(v) ((v)->counter = (s64)((u64)(v)->counter + 1))

#define REFCOUNT_SATURATED 0xc0000000u
enum refcount_saturation_type { REFCOUNT_ADD_NOT_ZERO_OVF, REFCOUNT_ADD_OVF, REFCOUNT_ADD_UAF, REFCOUNT_SUB_UAF,
				REFCOUNT_DEC_LEAK };
extern unsigned long wg_shim_refcount_warn[5];       /* refcount_warn_saturate calls, by type */
void wg_shim_refcount_inc(unsigned int *r);          /* refcount_inc (kref_get) */
bool wg_shim_refcount_inc_not_zero(unsigned int *r); /* refcount_inc_not_zero (kref_get_unless_zero) */
bool wg_shim_refcount_dec_and_test(unsigned int *r); /* refcount_dec_and_test (kref_put) */
/* struct kref { unsigned int refcount; } and kref_init (count 1) as in quickproof_kernel.h */
#undef kref_get
#undef kref_put
#define kref_get(k) wg_shim_refcount_inc(&(k)->refcount)
#define kref_get_unless_zero(k) wg_shim_refcount_inc_not_zero(&(k)->refcount)
#define kref_put(k, release) do { if (wg_shim_refcount_dec_and_test(&(k)->refcount)) release(k); } while (0)

#endif /* QUICKPROOF_KREF_H */
