/* SPDX-License-Identifier: GPL-2.0 */
/*
 * quickproof_kernel.h: the kernel environment of the WireGuard handshake, reduced to plain single-threaded C.
 *
 * QUICKPROOF SHIM (not upstream code); every item is a row S01..S21 of DEVIATIONS.md.  Every <linux/...> header the code under test includes is a one-line file
 * in patch/include/linux/ that includes this header.  What it replaces, and how:
 *   - types: u8..u64, s64, __le32/__be32/..., bool (x86_64, little endian);
 *   - compiler annotations (__must_check, __aligned, __rcu, at_least, ...), module and export macros: nothing;
 *   - locks (spinlock, rw_semaphore, mutex), RCU (rcu_dereference, rcu_assign_pointer, call_rcu, ...):
 *     single-threaded no-ops; call_rcu(head, fn) calls fn(head) at once (no grace period);
 *   - kref and atomic64: plain counters here, REPLACED by quickproof_kref.h (S04: the kernel's saturating
 *     refcount_t and a wrapping atomic64_inc_return) in every unit that uses kref (linux/kref.h includes it);
 *   - kzalloc/kfree/kfree_sensitive: calloc/free (patch/wg_shim.c; calls counted for the no-leak checks);
 *   - byte order: x86_64 (cpu_to_le* identity, cpu_to_be* byte swaps); unaligned accesses: byte by byte;
 *   - clocks and randomness: patch/wg_shim.c (the harness sets the clocks; randomness is nondet_* and logged);
 *   - memzero_explicit, crypto_memneq, crypto_xor_cpy: plain C (include/crypto/utils.h of this directory).
 * Concurrency is outside the claim: with the locks as no-ops, the laws say nothing about interleavings.
 */
#ifndef QUICKPROOF_KERNEL_H
#define QUICKPROOF_KERNEL_H

#include <stddef.h>
#include <stdint.h>

/* ---- libc (quickproof libc/libc.c provides the bodies) ---- */
void *memcpy(void *dest, const void *src, size_t n);
void *memmove(void *dest, const void *src, size_t n);
void *memset(void *s, int c, size_t n);
int memcmp(const void *s1, const void *s2, size_t n);
void *calloc(size_t nmemb, size_t size);
void *malloc(size_t n);
void free(void *p);

/* QUICKPROOF S09 memzero_explicit (linux/string.h): memset (no optimisation barrier needed in plain C semantics) */
static inline void memzero_explicit(void *s, size_t count)
{
	memset(s, 0, count);
}

/* ---- QUICKPROOF S01 types ---- */
typedef uint8_t u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;
typedef int8_t s8;
typedef int16_t s16;
typedef int32_t s32;
typedef int64_t s64;
typedef u16 __le16;
typedef u16 __be16;
typedef u32 __le32;
typedef u32 __be32;
typedef u64 __le64;
typedef u64 __be64;
typedef _Bool bool;
#define true 1
#define false 0
typedef unsigned int gfp_t;
#define GFP_KERNEL 0u

#define U64_MAX ((u64)~0ULL)
#define INT_MAX 2147483647
/* QUICKPROOF S25: the limit the series P22/P23 uses, with the kernel's own text (include/vdso/limits.h UINT_MAX);
 * min() is S20's (patch/tests/macrocheck.sh) */
#define UINT_MAX	(~0U)
#define BITS_PER_LONG 64
#define HZ 1000
#define NSEC_PER_SEC 1000000000L
#define PAGE_SIZE 4096

/* ---- QUICKPROOF S01 annotations, WARN_ON (DEBUG off: C07), export and module macros ---- */
#define __must_check
#define __maybe_unused
#undef __always_inline
#define __always_inline inline
#define noinline
#define __init
#define __exit
#define __ro_after_init
#define __nonstring
#define __aligned(x)
#define __force
#define __rcu
#define __packed
#define at_least
#define unrolled_full
#define likely(x) (x)
#define unlikely(x) (x)
#define IS_ENABLED(x) 0
#define READ_ONCE(x) (x)
#define WARN_ON(x) (!!(x))
#define WARN_ON_ONCE(x) (!!(x))
#define RCU_LOCKDEP_WARN(c, s) ((void)0)
#define net_dbg_ratelimited(...) ((void)0)
#define EXPORT_SYMBOL(x) extern int quickproof_export_marker
#define EXPORT_SYMBOL_GPL(x) extern int quickproof_export_marker
#define MODULE_LICENSE(x) extern int quickproof_export_marker
#define MODULE_DESCRIPTION(x) extern int quickproof_export_marker
#define MODULE_AUTHOR(x) extern int quickproof_export_marker

/* QUICKPROOF S11 */
#define ARRAY_SIZE(a) (sizeof(a) / sizeof((a)[0]))
#define DIV_ROUND_UP(n, d) (((n) + (d) - 1) / (d))
#define round_down(x, y) ((x) & ~((y) - 1))
#define ALIGN_DOWN(x, a) ((x) & ~((a) - 1))
#define container_of(ptr, type, member) ((type *)((char *)(ptr) - offsetof(type, member)))

/* QUICKPROOF S11 rounddown_pow_of_two(n) for n >= 1: the largest power of two <= n (the kernel macro, for a constant). */
static inline unsigned long quickproof_rounddown_pow_of_two(unsigned long n)
{
	unsigned long r = 1;
	while (r <= n / 2)
		r = r * 2;
	return r;
}
#define rounddown_pow_of_two(n) quickproof_rounddown_pow_of_two(n)

/* QUICKPROOF S11 ilog2(n) for n >= 1: the index of the highest set bit (the kernel macro, for a constant). */
static inline int quickproof_ilog2(unsigned long n)
{
	int r = 0;
	while (n > 1) {
		n = n / 2;
		r++;
	}
	return r;
}
#define ilog2(n) quickproof_ilog2(n)
#define min_t(type, a, b) ((type)(a) < (type)(b) ? (type)(a) : (type)(b))
#define WRITE_ONCE(x, v) ((x) = (v))

/* ---- QUICKPROOF S10 bit operations ---- */
static inline u32 rol32(u32 word, unsigned int shift)
{
	return (word << (shift & 31)) | (word >> ((-shift) & 31));
}
static inline u32 ror32(u32 word, unsigned int shift)
{
	return (word >> (shift & 31)) | (word << ((-shift) & 31));
}

/* QUICKPROOF S11 test_and_set_bit: the generic (non-atomic) semantics: set bit nr of the bitmap at addr, return its old value. */
static inline int test_and_set_bit(unsigned long nr, unsigned long *addr)
{
	unsigned long mask = 1UL << (nr % BITS_PER_LONG);
	unsigned long *p = addr + nr / BITS_PER_LONG;
	unsigned long old = *p;
	*p = old | mask;
	return (old & mask) != 0;
}

/* ---- QUICKPROOF S10 byte order (x86_64: little endian) ---- */
#define cpu_to_le32(x) ((u32)(x))
#define le32_to_cpu(x) ((u32)(x))
#define cpu_to_le64(x) ((u64)(x))
static inline u32 quickproof_swab32(u32 x)
{
	return (x >> 24) | ((x >> 8) & 0xff00) | ((x << 8) & 0xff0000) | (x << 24);
}
static inline u64 quickproof_swab64(u64 x)
{
	return ((u64)quickproof_swab32((u32)x) << 32) | quickproof_swab32((u32)(x >> 32));
}
#define cpu_to_be32(x) quickproof_swab32((u32)(x))
#define cpu_to_be64(x) quickproof_swab64((u64)(x))
static inline u16 quickproof_swab16(u16 x) { return (u16)((x >> 8) | (x << 8)); }
#define htons(x) quickproof_swab16((u16)(x))
#define cpu_to_le32_array(buf, words) ((void)0)
#define le32_to_cpu_array(buf, words) ((void)0)

/* ---- QUICKPROOF S10 unaligned accesses, byte by byte ---- */
static inline u32 get_unaligned_le32(const void *p)
{
	const u8 *b = (const u8 *)p;
	return (u32)b[0] | ((u32)b[1] << 8) | ((u32)b[2] << 16) | ((u32)b[3] << 24);
}
static inline void put_unaligned_le32(u32 v, void *p)
{
	u8 *b = (u8 *)p;
	b[0] = (u8)v;
	b[1] = (u8)(v >> 8);
	b[2] = (u8)(v >> 16);
	b[3] = (u8)(v >> 24);
}
static inline void put_unaligned_le64(u64 v, void *p)
{
	put_unaligned_le32((u32)v, p);
	put_unaligned_le32((u32)(v >> 32), (u8 *)p + 4);
}
static inline void put_unaligned_be32(u32 v, void *p)
{
	u8 *b = (u8 *)p;
	b[0] = (u8)(v >> 24);
	b[1] = (u8)(v >> 16);
	b[2] = (u8)(v >> 8);
	b[3] = (u8)v;
}
static inline void put_unaligned_be64(u64 v, void *p)
{
	put_unaligned_be32((u32)(v >> 32), p);
	put_unaligned_be32((u32)v, (u8 *)p + 4);
}

/* ---- QUICKPROOF S02 locks and RCU: single-threaded no-ops (S03: call_rcu calls at once) ---- */
typedef struct { int unused; } spinlock_t;
struct rw_semaphore { int unused; };
struct mutex { int unused; };
struct rcu_head { int unused; };
#define spin_lock_init(l) ((void)0)
#define spin_lock_bh(l) ((void)0)
#define spin_unlock_bh(l) ((void)0)
#define init_rwsem(l) ((void)0)
#define down_read(l) ((void)0)
#define up_read(l) ((void)0)
#define down_write(l) ((void)0)
#define up_write(l) ((void)0)
#define rcu_read_lock_bh() ((void)0)
#define rcu_read_unlock_bh() ((void)0)
#define rcu_dereference_protected(p, c) (p)
#define rcu_access_pointer(p) (p)
#define rcu_assign_pointer(p, v) ((p) = (v))
#define RCU_INIT_POINTER(p, v) ((p) = (v))
#define call_rcu(head, fn) fn(head)

/* ---- QUICKPROOF S04 counters (kref and atomic64_inc_return are replaced by quickproof_kref.h wherever
 * kref is used; this text stays so that the units that do not use kref translate to the same Clight) ---- */
typedef struct { s64 counter; } atomic64_t;
#define ATOMIC64_INIT(i) { (i) }
#define atomic64_inc_return(v) (++(v)->counter)
#define atomic64_set(v, i) ((v)->counter = (i))
struct kref { unsigned int refcount; };
#define kref_init(k) ((k)->refcount = 1)
#define kref_get(k) ((k)->refcount++)
static inline int kref_get_unless_zero(struct kref *k)
{
	if (k->refcount == 0)
		return 0;
	k->refcount++;
	return 1;
}
#define kref_put(k, release) do { if (--(k)->refcount == 0) release(k); } while (0)

/* ---- QUICKPROOF S05 allocation (patch/wg_shim.c) ---- */
void *kzalloc(size_t size, gfp_t flags);
void kfree(const void *p);
void kfree_sensitive(const void *p);
#define kzalloc_obj(x) kzalloc(sizeof(x), GFP_KERNEL)

/* ---- QUICKPROOF S06 clocks, S07 randomness (patch/wg_shim.c) ---- */
struct timespec64 { s64 tv_sec; long tv_nsec; };
u64 ktime_get_coarse_boottime_ns(void);
void ktime_get_real_ts64(struct timespec64 *ts);
void get_random_bytes(void *buf, size_t len);
void get_random_bytes_wait(void *buf, size_t len);
u32 get_random_u32(void);
#define wait_for_random_bytes() ((void)0)

/* ---- QUICKPROOF S08 the zero page read by the AEAD for padding (patch/wg_shim.c; 64 bytes, the code reads at most 32) ---- */
extern const u8 quickproof_zero_page[64];
#define ZERO_PAGE(x) quickproof_zero_page
#define page_address(p) (p)

/* ---- QUICKPROOF S20 scatterlists: only for the upstream (unpatched) chacha20poly1305.c to compile; its scatterlist functions
 * are data-path code that the handshake never calls, and the patch compiles them out (DEVIATIONS.md). ---- */
struct scatterlist { int unused; };
struct sg_mapping_iter { u8 *addr; size_t length; };
#define SG_MITER_TO_SG 1u
#define SG_MITER_ATOMIC 2u
#define min(a, b) ((a) < (b) ? (a) : (b))
static inline int sg_nents(struct scatterlist *sg) { (void)sg; return 0; }
static inline void sg_miter_start(struct sg_mapping_iter *m, struct scatterlist *sg, unsigned int n, unsigned int f)
{ (void)sg; (void)n; (void)f; m->addr = 0; m->length = 0; }
static inline bool sg_miter_next(struct sg_mapping_iter *m) { (void)m; return false; }
static inline void sg_miter_stop(struct sg_mapping_iter *m) { (void)m; }
static inline size_t sg_copy_buffer(struct scatterlist *sg, unsigned int n, void *b, size_t l, size_t s, bool to)
{ (void)sg; (void)n; (void)b; (void)l; (void)s; (void)to; return 0; }

#endif /* QUICKPROOF_KERNEL_H */
