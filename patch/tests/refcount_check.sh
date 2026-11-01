#!/usr/bin/env bash
# patch/tests/refcount_check.sh [TREE]: QUICKPROOF S04 - the shim's refcount_t (patch/wg_shim.c:
# wg_shim_refcount_inc / _inc_not_zero / _dec_and_test) against the KERNEL'S OWN TEXT at the pinned commit:
# __refcount_add_not_zero, __refcount_add, __refcount_sub_and_test (include/linux/refcount.h) and
# refcount_warn_saturate (lib/refcount.c), copied out of the upstream files (patch/upstream.sh) and compiled
# single-threaded (atomics as plain int operations, gcc -fwrapv as the kernel's -fno-strict-overflow).  For every
# operation and every start value in a set of edges (0..3, INT_MAX - 3 .. INT_MAX + 3, REFCOUNT_SATURATED +- 3,
# UINT_MAX - 3 .. UINT_MAX) plus random ones, and for random operation sequences: same result, same count bits,
# same warnings by type.
set -euo pipefail
T=$(realpath "${1:-.}")
U=$("$(dirname "$0")/../upstream.sh")
D=$(mktemp -d)
trap 'rm -rf "$D"' EXIT
cp "$U/include/linux/refcount.h" "$D/refcount.h"
cp "$U/lib/refcount.c" "$D/refcount.c"
python3 - "$D" <<'PY'
import sys
d = sys.argv[1]
h = open(d + '/refcount.h').read()
c = open(d + '/refcount.c').read()
def fn(src, head):
    i = src.index(head)
    j = src.index('\n}\n', i) + 3
    return src[i:j]
parts = [fn(h, 'static inline __must_check\nbool __refcount_add_not_zero('),
         fn(h, 'static inline\nvoid __refcount_add('),
         fn(h, 'static inline __must_check\nbool __refcount_sub_and_test('),
         fn(c, 'void refcount_warn_saturate(')]
pre = r'''
#include <limits.h>
#include <stdbool.h>
#include <stddef.h>
typedef struct { int counter; } atomic_t;
typedef struct refcount_struct { atomic_t refs; } refcount_t;
enum refcount_saturation_type { REFCOUNT_ADD_NOT_ZERO_OVF, REFCOUNT_ADD_OVF, REFCOUNT_ADD_UAF, REFCOUNT_SUB_UAF,
                                REFCOUNT_DEC_LEAK };
#define REFCOUNT_SATURATED (INT_MIN / 2)
#define __must_check
#define __signed_wrap
#define unlikely(x) (x)
#define smp_acquire__after_ctrl_dep() ((void)0)
#define EXPORT_SYMBOL(x)
unsigned long kernel_warn[5];
#define REFCOUNT_WARN(str) (kernel_warn[t]++)
static inline int atomic_read(const atomic_t *v) { return v->counter; }
static inline void atomic_set(atomic_t *v, int i) { v->counter = i; }
static inline bool atomic_try_cmpxchg_relaxed(atomic_t *v, int *old, int new)
{ if (v->counter == *old) { v->counter = new; return true; } *old = v->counter; return false; }
static inline int atomic_fetch_add_relaxed(int i, atomic_t *v) { int o = v->counter; v->counter = o + i; return o; }
static inline int atomic_fetch_sub_release(int i, atomic_t *v) { int o = v->counter; v->counter = o - i; return o; }
static inline unsigned int refcount_read(const refcount_t *r) { return atomic_read(&r->refs); }
static inline void refcount_set(refcount_t *r, int n) { atomic_set(&r->refs, n); }
void refcount_warn_saturate(refcount_t *r, enum refcount_saturation_type t);
'''
post = r'''
bool k_inc_not_zero(unsigned int *v) { refcount_t r = { { (int)*v } }; bool b = __refcount_add_not_zero(1, &r, NULL); *v = (unsigned int)r.refs.counter; return b; }
void k_inc(unsigned int *v) { refcount_t r = { { (int)*v } }; __refcount_add(1, &r, NULL); *v = (unsigned int)r.refs.counter; }
bool k_dec_and_test(unsigned int *v) { refcount_t r = { { (int)*v } }; bool b = __refcount_sub_and_test(1, &r, NULL); *v = (unsigned int)r.refs.counter; return b; }
'''
open(d + '/kernel_refcount.c', 'w').write(pre + '\n'.join(parts) + post)
PY
cd "$T"
gcc -O1 -fwrapv -w -o "$D/k.o" -c "$D/kernel_refcount.c"
gcc -O1 -w -fsanitize=address,undefined -fno-sanitize-recover=all -Ipatch/include -Idrivers/net/wireguard -Iinclude \
    -Iquickproof/include -c patch/wg_shim.c -o "$D/shim.o"
gcc -O1 -w -fsanitize=address,undefined -fno-sanitize-recover=all -c patch/tests/refcount_check.c -o "$D/drv.o"
gcc -fsanitize=address,undefined "$D/drv.o" "$D/shim.o" "$D/k.o" -o "$D/refcount_check"
"$D/refcount_check"
