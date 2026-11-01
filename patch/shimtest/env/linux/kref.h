/* shimtest only (native, not verified), the -DUPSTREAM build: kref as include/linux/kref.h and refcount.h at the
 * pinned commit for one thread (refcount_inc_not_zero: no change at 0; else +1, saturating at INT_MAX + 1 or from a
 * negative count; refcount_inc; refcount_dec_and_test: true at 1 -> 0, saturating from 0 or a negative count).
 * The shim's quickproof_kref.h declares out-of-line functions of patch/wg_shim.c, which this build does not link; the
 * peer table code compared here only takes references on counts in 1 .. INT_MAX - 1 and 0. */
#ifndef SHIMTEST_KREF_H
#define SHIMTEST_KREF_H
#include "quickproof_kref.h"
#define SHIMTEST_RC_NEG(v) ((v) >= 0x80000000u)
static inline bool shimtest_refcount_inc_not_zero(unsigned int *r)
{
	unsigned int old = *r;
	if (old == 0)
		return false;
	*r = SHIMTEST_RC_NEG(old) || SHIMTEST_RC_NEG(old + 1u) ? REFCOUNT_SATURATED : old + 1u;
	return true;
}
static inline void shimtest_refcount_inc(unsigned int *r)
{
	unsigned int old = *r;
	*r = old == 0 || SHIMTEST_RC_NEG(old) || SHIMTEST_RC_NEG(old + 1u) ? REFCOUNT_SATURATED : old + 1u;
}
static inline bool shimtest_refcount_dec_and_test(unsigned int *r)
{
	unsigned int old = *r;
	if (old == 1u) {
		*r = 0;
		return true;
	}
	*r = old == 0 || SHIMTEST_RC_NEG(old) ? REFCOUNT_SATURATED : old - 1u;
	return false;
}
#undef kref_get
#undef kref_get_unless_zero
#undef kref_put
#define kref_get(k) shimtest_refcount_inc(&(k)->refcount)
#define kref_get_unless_zero(k) shimtest_refcount_inc_not_zero(&(k)->refcount)
#define kref_put(k, release) do { if (shimtest_refcount_dec_and_test(&(k)->refcount)) release(k); } while (0)
#endif
