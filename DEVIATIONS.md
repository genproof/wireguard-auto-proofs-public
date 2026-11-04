# Deviations from a Linux kernel build

The proof is about Linux at commit `551c722f40809618230001baccf219193e22fc5a` (2026-09-29), compiled for the
proof as described here. Four kinds of differences from a kernel build are listed, each with an identifier that the
source code refers to:

- P: the patch, `patch/wgpatch.py`. It first applies two patches of the lib/crypto series in `patch/series/`
  (P22, P23), then rewrites some idioms that VST or CompCert cannot handle (P01 to P21). Every rewrite carries a
  `QUICKPROOF Pnn` comment on its block. The series' lines carry none: they are the series' text itself, and
  `patch/wgpatch.py` checks them instead (every hunk at exactly its stated line with its exact context, and the git
  blob of every file it touches before and after).
- S: the kernel shim, `patch/include/` and `patch/wg_shim.c`, which stands in for the parts of the kernel that
  the code under test includes or calls and that are not in this proof (types, locks, allocation, clocks,
  randomness, the peer and device structures, the lookup tables). The shim's C is compiled and proved with the rest
  of the code; that it behaves as the kernel does is tested. Shim code carries `QUICKPROOF Snn` comments.
- C: the configuration: which variant of each primitive is compiled, for which target.
- L: what the specs exclude or assume.

P01 to P21 rewrite idioms (`goto`, struct copies, type punning, empty compound literals), and `patch/diff.sh` finds
the same outputs as upstream on random inputs. P22 and P23 are the two lib/crypto patches; they change results only
at lengths of about 4 GiB and more, where upstream's results are wrong. The S rows replace the kernel around the code
with plain C. Nothing proves that they behave as the kernel does, so they deserve the closest reading; each row
names its test, or says there is none. C01 to C07 are the configuration, among them the generic C of the primitives
(32-bit limbs for Poly1305 and Curve25519), so x86_64's own variants are not covered. L01 to L17 list what the specs
exclude or assume. The specs named here are those of `harness/`: the 19 short specs (`rp_`, `ae_`, `hs_`) and the
19 longer `x_` specs.

`patch/check.sh` shows that the patched files of this repository are exactly upstream plus `patch/wgpatch.py`: it
takes the unmodified files at the pinned commit, runs the patch and compares the result byte for byte. The patch is
checked by testing, not by proof.

## Tests

The scripts are in `patch/`. They fetch the unmodified upstream files they compare with through
`patch/upstream.sh` (from a local Linux clone in `$LINUX`, or a shallow fetch of the pinned commit from GitHub) and
build native programs with gcc. The results below are those of this repository's code.

- **check**: `patch/check.sh`. The 21 files of the code under test equal upstream plus `patch/wgpatch.py`.
- **diff**: `patch/diff.sh 100000 5`. The driver `patch/diff.c` is built twice, against the unmodified upstream
  code and against this repository's, with the same shim, at `-O1` with AddressSanitizer and
  UndefinedBehaviorSanitizer (the first report aborts the run). Both run on the same pseudo-random inputs (degenerate
  keys, zero points, arbitrary handshake states, corrupted messages, every verdict path) and every output byte and
  return value is folded into one hash per section: BLAKE2s, ChaCha, AEAD, Poly1305, Curve25519, full handshakes,
  handshakes from arbitrary states, keypair rotation, cookies, the replay counter, and two exhaustive sections for
  the series (`poly_split`: every buffered state of 0 to 47 bytes, every chunk of 0 to 299 bytes and a rest of 0, 1
  or 17 bytes; `aead_lens`: every associated-data length up to 64 and message length up to 130, for both
  constructions, each encryption decrypted and also decrypted with one byte changed). The series' loops only
  iterate at about 4 GiB, so the script also builds two copies of the patched code with small limits put in the
  series' lines (`small1`: chunks of 64 bytes for ChaCha while more than 127 remain, at most 16 bytes per
  `poly1305_blocks` call; `small2`: 192 bytes while more than 255 remain, at most 48 bytes per call); their outputs
  must equal upstream's too. As a check of the test, two wrong copies (`badchacha`: ChaCha chunks of 32 bytes,
  `badpoly`: Poly1305 chunks of 8 bytes) must give different outputs. Result: identical outputs for 5 seeds of
  100,000 iterations, also for `small1` and `small2`; `badchacha` and `badpoly` differ; no sanitizer report.
  `patch/diff.sh 20000 1 --coverage` prints how often each `QUICKPROOF` line and each line of the series was
  executed: every rewrite is executed (P18 is compiled out), apart from the branches listed at the end of the P
  table; of the series, the chunked call of `chacha_crypt` runs only in `small1` (2,703 times), every other line
  also in the patched code itself.
- **shimtest**: `patch/shimtest/shimtest.sh 20000 5`. The shim against the kernel code it stands in for, taken from
  the pinned commit: the index and public-key tables (`drivers/net/wireguard/peerlookup.c` with the kernel's list
  primitives), `crypto_memneq` and `crypto_xor(_cpy)` (`lib/crypto/memneq.c`, `utils.c`, `include/crypto/utils.h`
  in the x86_64 configuration) and the byte-order helpers, on the same random operation sequences, with ASan and
  UBSan. Result: identical outputs for 5 seeds of 20,000 iterations.
- **refcount**: `patch/tests/refcount_check.sh`. The shim's `refcount_t` against the kernel's own text at the pinned
  commit (`include/linux/refcount.h`, `lib/refcount.c`), compiled for one thread: every operation from every start
  value in a set of edges (around 0, `INT_MAX`, `REFCOUNT_SATURATED` and `UINT_MAX`) and random ones, and random
  operation sequences. Result: 4,503,408 operations, no difference in results, counts or warnings.
- **saturation**: `patch/tests/keypairs_sat.sh`. The spec `x_keypairs` run natively past the saturation of a
  reference count (2^31 + 64 gets of one keypair) with the scripted environment `patch/tests/env_sat.c`. It takes
  hours per seed and was run when the shim's `refcount_t` was written; it is not rerun here.
- **macrocheck**: `patch/tests/macrocheck.sh` (S25). The shim's `UINT_MAX` has the value and the type of the
  kernel's text at the pinned commit; `round_down(UINT_MAX, CHACHA_BLOCK_SIZE)` is 2^32 - 64; and
  `round_down(min(nbytes, UINT_MAX), POLY1305_BLOCK_SIZE)`, as the shim expands it, gives the kernel's value on
  1,000,551 values of `nbytes` (every boundary around 0, 2^31, 2^32, 2^63 and `SIZE_MAX`, and random values).
- **extract**: `patch/tests/extract_check.py` (S22). The two blocks of `patch/receive_handshake.c` equal
  `receive.c`.
- **enumcheck**: `patch/tests/enumcheck.sh` (C04). The uses of enumeration constants above `INT_MAX` give the same
  values with gcc and in CompCert's interpreter.
- **refkat**: `patch/tests/refkat.sh`. The reference primitives of `harness/common.h`, which the `x_` specs compare
  the kernel's primitives with, give the published test vectors (RFC 7748, RFC 7693, RFC 8439).
- **big**: `patch/tests/big.sh`. The lengths at which the series changes results, natively (gcc `-O2`, 4 GiB
  buffers, about 17 GiB of memory, each case in a child process), against the reference primitives: Poly1305 with
  chunks that cross 2^32 bytes after 1 to 15 buffered bytes, single `poly1305_update` calls of 2^32 bytes and more
  and of 2^31 bytes and more, and ChaCha20-Poly1305 / XChaCha20-Poly1305 with messages and associated data of
  2^32 bytes and more, of exactly 2^32 bytes and of 2^32 - 1 bytes. On this repository's code every case must
  give the RFC 8439 result; on the unmodified upstream code the cases of 2^32 bytes and more fail. It needs hours
  and much memory and was not run for this version; for this code the specs `x_prim_poly1305` and `x_prim_aead`
  cover these lengths by proof.

## P: the patch (`patch/wgpatch.py`)

P01 to P21 rewrite idioms and change no result. VST 2.15 has no rule for `goto` and none for struct assignment, and
it reasons about typed memory: a `u32` stored and read back as bytes, or a union read through another member, needs
byte-level reasoning it does not automate. CompCert rejects the empty compound literal `(T){}` of C23. P22 and P23
are patches 4/5 and 5/5 of the lib/crypto series "lib/crypto: Handle large lengths in poly1305 and
chacha20poly1305", applied verbatim. They change results only where upstream gives wrong results, at lengths of
about 4 GiB; without them the specs `x_prim_poly1305` and `x_prim_aead` are false. The `ae_` specs take such
lengths too, so they are also about the patched code.

| id | where | change | why | test |
|---|---|---|---|---|
| P01 | noise.c `kdf` | three `if (!x) goto out;` become nested `if (x) { ... }` | goto | diff |
| P02 | noise.c `tai64n_now` | the `__be64` and `__be32` stores into the output become `put_unaligned_be64/be32` (byte stores of the same 12 bytes) | typed memory | diff |
| P03 | noise.c `wg_noise_handshake_create_initiation` | `goto out` becomes `break` out of a `do { } while (0)` block that ends where the label was | goto | diff |
| P04 | noise.c `wg_noise_handshake_consume_initiation` | the same | goto | diff |
| P05 | noise.c `wg_noise_handshake_create_response` | the same | goto | diff |
| P06 | noise.c `wg_noise_handshake_consume_response` | `goto out` breaks from an outer block, `goto fail` from an inner one; the statement after `fail:` (`wg_peer_put`) runs exactly when the inner block did not complete (flag `quickproof_success`) | goto | diff |
| P07 | noise.c `wg_noise_handshake_begin_session` | `goto out` becomes `break` | goto | diff, with forced allocation failures |
| P08 | cookie.c `wg_cookie_validate_packet` | the same | goto | diff, all four verdicts |
| P09 | cookie.c `wg_cookie_message_consume` | the same | goto | diff |
| P10 | patch/counter_validate.c `counter_validate` | the same (the loop inside the block has no goto; the script checks it) | goto | diff |
| P11 | blake2s.c `blake2s_compress_generic` | `memcpy(m, data, 64); le32_to_cpu_array(m, 16)` becomes 16 `get_unaligned_le32` loads | typed memory | diff |
| P12 | blake2s.c `blake2s_compress_generic` | `memcpy(v, ctx->h, 32)` becomes 8 word copies | typed memory | diff |
| P13 | blake2s.c `blake2s_final` | `cpu_to_le32_array(h); memcpy(out, h, outlen)` writes the first `outlen` bytes of the words, little endian (the context is zeroed afterwards in both) | typed memory | diff |
| P14 | chacha-block-generic.c `chacha_block_generic` | `struct chacha_state permuted_state = *state` becomes 16 word copies | struct assignment | diff |
| P15 | chacha-block-generic.c `hchacha_block_generic` | the same struct copy, and two 16-byte `memcpy` between `u32` arrays become word copies | struct assignment, typed memory | diff (HChaCha with 20 and 12 rounds) |
| P16 | chacha20poly1305.c, the encryption and decryption functions | `__le64 iv[2]` read through `(u8 *)iv` becomes `u8 iv[16]` written with `put_unaligned_le64` | typed memory | diff |
| P17 | chacha20poly1305.c, the same functions | the union `b` (`block0`, `mac`, `__le64 lens[2]`) becomes a struct with only `u8 block0[32]`; the lengths are stored with `put_unaligned_le64` into `block0`, and `b.mac` (the first 16 bytes) is `block0` (the same bytes; `sizeof(b)` is 32 in both) | union punning, typed memory | diff |
| P18 | chacha20poly1305.c | the scatterlist functions `chacha20poly1305_{en,de}crypt_sg_inplace` are inside `#if 0` | data-path code with scatterlist iterators, which nothing in scope calls | `patch/diff.sh` checks with `nm` that the upstream `noise.o` and `cookie.o` do not refer to them |
| P19 | poly1305.c `poly1305_final` | `*desc = (struct poly1305_desc_ctx){};` becomes `memset(desc, 0, sizeof(*desc))` (the padding bytes become zero too) | empty compound literal, struct assignment | diff |
| P20 | include/crypto/internal/poly1305.h `poly1305_core_init` | `*state = (struct poly1305_state){};` becomes `memset` | the same | diff |
| P21 | curve25519-fiat32.c `fe_copy`, `fe_copy_lt`, `fe_0`, `fe_1` | `memmove` / `memset` of the 10 `u32` limbs become limb loops (a forward copy equals `memmove`, also when source and destination are the same) | typed memory | diff |
| P22 | include/crypto/poly1305.h, poly1305.c `poly1305_update` | patch 4/5 of the series (`patch/series/0004-*.patch`): `nbytes` becomes a `size_t`; the test for a full block `desc->buflen + nbytes >= POLY1305_BLOCK_SIZE` becomes `nbytes >= POLY1305_BLOCK_SIZE - desc->buflen`; the bulk call becomes a loop that gives `poly1305_blocks()` at most `round_down(min(nbytes, UINT_MAX), POLY1305_BLOCK_SIZE)` bytes per call | upstream adds `buflen` and `nbytes` as `unsigned int`: with 1 to 15 bytes buffered and `nbytes` of 2^32 - `buflen` or more the sum wraps and the tail path copies `nbytes` bytes into the 16-byte buffer; and the `unsigned int` parameter truncates the `size_t` lengths of its callers | diff (with `poly_split`, `small1`, `small2`, `badpoly`); macrocheck; spec `x_prim_poly1305` |
| P23 | include/crypto/chacha.h, chacha.c `chacha_crypt` | patch 5/5 of the series (`patch/series/0005-*.patch`): `chacha_crypt()` and `chacha20_crypt()` take a `size_t` length; `chacha_crypt` gives `chacha_crypt_arch` (here `chacha_crypt_generic`, whose length is an `unsigned int`) chunks of `round_down(UINT_MAX, CHACHA_BLOCK_SIZE)` = 2^32 - 64 bytes while more than `UINT_MAX` bytes remain, then the rest | the lengths of `chacha20poly1305.c`, which are `size_t`, were truncated to 32 bits: data beyond 4 GiB was neither encrypted nor authenticated | diff (with `aead_lens`, `small1`, `small2`, `badchacha`); macrocheck; spec `x_prim_aead` |

Where upstream is correct, P22 and P23 give the same results: `buflen` is at most 15, so the two tests for a full
block agree whenever the sum does not wrap; below 2^32 bytes per call the loop makes the one `poly1305_blocks`
call that upstream made; up to `UINT_MAX` bytes `chacha_crypt` makes exactly the call upstream made, and above it
the chunks are whole ChaCha blocks, so the keystream continues.

Patches 1/5 to 3/5 of the series (`lib/crypto: riscv/poly1305`, `mips/poly1305` and `arm64/poly1305: Fix 32-bit
length treated as 64-bit`) make the poly1305 assembly of those architectures handle such lengths; it is not built
here.

Not reached by any test, and equivalent by construction (each `break` leaves its block exactly where the `goto`
jumped): in `create_initiation` and `create_response`, `curve25519_generate_public()` failing on a clamped secret
(X25519(k, 9) is never zero for a clamped k); in `consume_response`, `DH(S_i, E)` zero while `DH(E_i, E)` is not
(for a point E the two clamped scalars give zero together or not at all), and the handshake state changing between
the two reads under the lock (one thread).

## S: the kernel shim (`patch/include/`, `patch/wg_shim.c`)

| id | where | what stands in for what | effect claimed | test |
|---|---|---|---|---|
| S01 | quickproof_kernel.h, linux/*.h | types (`u8` to `u64`, `__le32`, `bool`); annotations (`__must_check`, `__aligned`, `at_least`, `__rcu`, ...) as nothing; `likely`; `IS_ENABLED` as 0; `WARN_ON(x)` as `(!!(x))` (every use has `IS_ENABLED(DEBUG) && ...`, so nothing is evaluated); `EXPORT_SYMBOL` and `MODULE_*` as an extern declaration; each `<linux/...>` header the code includes is a one-line file | none | builds |
| S02 | quickproof_kernel.h | spinlocks, rw-semaphores, mutexes, `rcu_read_lock_bh`, `rcu_dereference_protected`, `rcu_assign_pointer`, `RCU_INIT_POINTER` are no-ops or plain accesses | none for one thread (L01) | none possible |
| S03 | quickproof_kernel.h | `call_rcu(head, fn)` calls `fn(head)` at once | a keypair is freed at its last `put`, not after a grace period | spec `x_keypairs` counts the frees |
| S04 | quickproof_kref.h, linux/kref.h, wg_shim.c | `kref` is the kernel's `refcount_t` for one thread: get, get-unless-zero and put as in `include/linux/refcount.h` and `lib/refcount.c`, saturating at `REFCOUNT_SATURATED` (sticky, never released), the kernel's warnings counted by type (`wg_shim_refcount_warn`); `atomic64_inc_return` wraps. `quickproof_kernel.h` keeps an older plain-counter text, unused where kref is used, so that the units without kref translate to the same Clight | the kernel's states and warnings, for one thread | refcount; saturation; shimtest (whose upstream build takes the kernel's kref from `patch/shimtest/env/linux/kref.h`) |
| S05 | quickproof_kernel.h, wg_shim.c | `kzalloc` is `calloc` (NULL is an allocation failure, possible at any call); `kfree` and `kfree_sensitive` are `free`; calls are counted; `wg_shim_fail_next_alloc` (used by `patch/diff.c` only) | `kfree_sensitive` does not zero before freeing (not observable); the counters let the specs check that nothing leaks | specs |
| S06 | wg_shim.c | `ktime_get_coarse_boottime_ns` and `ktime_get_real_ts64` read globals the spec sets | the specs quantify over clock values (L02) | specs |
| S07 | wg_shim.c | `get_random_bytes(_wait)` and `get_random_u32` call `nondet_bytes` and `nondet_u32` (the last two draws are kept, for the models); `wait_for_random_bytes` does nothing | the specs quantify over every random value, a superset of the kernel's | specs |
| S08 | wg_shim.c | `page_address(ZERO_PAGE(0))` is a 64-byte array of zeros | none: the AEAD reads at most 32 bytes of it, and an overread would be undefined behaviour in the proof | specs; diff |
| S09 | crypto/utils.h, wg_shim.c | `crypto_memneq`, `crypto_xor(_cpy)` and `memzero_explicit` are byte loops and `memset` (upstream uses word accesses chosen by pointer alignment, through pointer-to-integer casts) | none on the results (`crypto_memneq` returns 0 or 1 as upstream does); the constant-time property is not claimed | shimtest |
| S10 | quickproof_kernel.h | byte order as on x86_64; `get/put_unaligned_le32/le64/be32/be64` byte by byte; `rol32` and `ror32` with upstream's bodies; `htons` | none on x86_64 | shimtest |
| S11 | quickproof_kernel.h | `rounddown_pow_of_two` and `ilog2` (loops, for the constants used), `ALIGN_DOWN`, `round_down`, `DIV_ROUND_UP`, `ARRAY_SIZE`, `min_t`, `container_of`, `READ_ONCE`/`WRITE_ONCE`, `test_and_set_bit` (the non-atomic generic semantics) as plain macros (the kernel's use `typeof` and builtins) | none for the uses in scope, including P22/P23's `round_down` of an `unsigned int` and of a `size_t` | shimtest; macrocheck |
| S12 | peer.h, wg_shim.c | `struct wg_peer` has only the fields that the handshake and cookie code use (upstream names and types) and `pubkey_next`; `wg_peer_get_maybe_zero` has upstream's body; `wg_peer_put` counts and never frees (the spec owns the peers) | none on the code in scope | shimtest; specs (references balanced) |
| S13 | device.h | `struct wg_device` has the identity, the cookie checker and the two tables | none | specs |
| S14 | peerlookup.h, wg_shim.c | the public-key hash table (siphash buckets, RCU) is a list of peers; the lookup does upstream's comparison and takes a reference | none observable: the same peer is returned, also with duplicate keys (the most recently added first, as upstream's `hlist_add_head`) | shimtest |
| S15 | peerlookup.h, wg_shim.c | the index hash table (2^13 buckets, RCU) is a list of entries with a `hashed` flag; insert (unhash, draw random indices until one is unused, add), replace, remove and lookup (type mask, reference, NULL peer at 0 references) behave as upstream's | none observable | shimtest, with 0-reference peers and duplicate indices |
| S16 | quickproof_net.h, linux/skbuff.h, net/ipv6.h | `struct sk_buff` with `data`, `len`, `protocol` and the IPv4, IPv6 and UDP source fields that cookie.c reads; `ip_hdr` and the like point to them | none on cookie.c's reads | specs `x_cookie_mac`, `x_cookie_reply` |
| S17 | ratelimiter.h, wg_shim.c | `wg_ratelimiter_allow` returns a global the spec sets | the specs quantify over both answers | specs |
| S18 | timers.h, wg_shim.c | `wg_birthdate_has_expired` has upstream's body (timers.c); the rest of timers.c is not compiled | none | `patch/wgpatch.py` checks that the text equals upstream's |
| S19 | patch/counter_validate.c | `counter_validate` is copied out of receive.c byte for byte (receive.c itself is not compiled), with a non-static wrapper `wg_counter_validate` for the specs | none | `patch/wgpatch.py` checks the text against receive.c at the pin |
| S20 | quickproof_kernel.h | empty scatterlist types and iterators, so that the unpatched chacha20poly1305.c compiles for the native runs of the unmodified code; with them, `min(a, b)` is `((a) < (b) ? (a) : (b))`, which P22 also uses (`min(nbytes, UINT_MAX)`) | the stubs are never called; for P22's use (a `size_t` and the `unsigned int` constant `UINT_MAX`) the kernel's macro compares both as `size_t` and yields the smaller, as the plain conditional does | builds; diff's `nm` check; macrocheck |
| S21 | queueing.h | empty (includes peer.h) | not used by the code in scope | builds |
| S22 | patch/receive_handshake.c | receive.c's `SKB_TYPE_LE32`, `validate_header_len` and `wg_receive_handshake_packet`, byte for byte between BEGIN and END markers; compiled into `harness/x_handshake_receive.c` only (it is not a library unit, so no other spec's program changes) | none | extract |
| S23 | patch/receive_handshake.c | the calls of the extracted text out of the verified units: `wg_packet_send_handshake_cookie` is send.c's body without the socket send (it builds the reply with the verified `wg_cookie_message_create`); `wg_socket_set_peer_endpoint_from_skb`, `wg_packet_send_handshake_response`, `wg_timers_session_derived`, `wg_timers_handshake_complete`, `wg_packet_send_keepalive`, `update_rx_stats` and `wg_timers_any_authenticated_packet_received/_traversal` are recorded in `wg_shim_rx`; `atomic_read(&wg->handshake_queue_len)` is `wg_shim_handshake_queue_len`, set by the spec; `net_dbg_*`, `WARN` and `local_bh_*` do nothing | send.c, socket.c and timers.c are not verified (L07); the spec states which of these run, how often, for which peer and packet | spec `x_handshake_receive` |
| S24 | patch/data_header.c | `validate_header_len` of receive.c with exactly three substitutions: the signature `static size_t validate_header_len(struct sk_buff *skb)` becomes `size_t wg_validate_header_len(u32 type, size_t len)`, `SKB_TYPE_LE32(skb)` becomes `type` and `skb->len` becomes `len`; every branch and constant is upstream's | none on the length decision: the same branches, constants and results for the same type word and length; how the type word and the length are read from the packet is not covered (L15) | `patch/wgpatch.py` checks the text against receive.c after the three substitutions, and that the upstream function reads the skb only through those two accessors; spec `x_transport_len` |
| S25 | quickproof_kernel.h | `UINT_MAX` as `(~0U)`, the kernel's own text (include/vdso/limits.h), which P22 and P23 use | none | macrocheck |

## C: configuration (`quickproof.conf`)

| id | choice | the kernel build it differs from | why | effect |
|---|---|---|---|---|
| C01 | Curve25519: `curve25519-fiat32.c`, the generic 32-bit limb code | x86_64 builds `curve25519-hacl64.c`, which needs `__int128`, or the ADX assembly | CompCert has no `__int128` and no assembly | another implementation of the same function; the proof is about fiat32, which 32-bit architectures use |
| C02 | Poly1305: `poly1305-donna32.c` | the x86_64 generic build uses donna64 (`__int128`) or the assembly | the same | the same |
| C03 | BLAKE2s and ChaCha20: the generic C, without `CONFIG_CRYPTO_LIB_*_ARCH` | x86_64 uses SSSE3 and AVX assembly | no assembly | the same functions |
| C04 | enumeration constants have type `int` in CompCert: the values above `INT_MAX` (`BLAKE2S_IV1/2/3/5`, `REKEY_AFTER_MESSAGES`, `REJECT_AFTER_MESSAGES`) are truncated with a warning; the constants of `enum limits` are `unsigned long` in gcc and `int` in CompCert, so receive.c compares the queue length with `MAX_QUEUED_INCOMING_HANDSHAKES / 8` unsigned in gcc and signed in CompCert (the same for the non-negative lengths the spec draws), and noise.c's flood test `(s64)last + NSEC_PER_SEC / INITIATIONS_PER_SECOND > (s64)now` is unsigned in gcc and signed in CompCert (the same below 2^63, that is under L02) | gcc gives these constants a wider type | the toolchain | none for the uses in scope (`REKEY_AFTER_MESSAGES` is not used in scope); checked by enumcheck, and the specs `x_handshake_receive` and `x_consume_initiation_any` give the same results natively and in CompCert's interpreter |
| C05 | x86_64: little endian, 64-bit `long` and pointers | 32-bit and big-endian kernels | the toolchain's target | the proof is for this target |
| C06 | `CONFIG_CRYPTO_LIB_POLY1305_RSIZE=1` | as for the generic Poly1305 | the header needs a value | none |
| C07 | `DEBUG` off: the `WARN_ON(IS_ENABLED(DEBUG) && ...)` checks of the arguments are not evaluated | debug builds | as in release kernels | none |

## L: what the specs exclude or assume

| id | exclusion or assumption | why | where it is stated |
|---|---|---|---|
| L01 | One thread. The locks and RCU are no-ops (S02); nothing is claimed about calls that run at the same time, about RCU readers, or about the second check of the handshake state under the write lock | VST's sequential logic, which these proofs use, is about one thread | every spec |
| L02 | The boot clock is below 2^62 ns (146 years of uptime) | the kernel adds 20 ms and 120 s to clock values as `s64`; that wraps with `-fno-strict-overflow` and in CompCert, and UBSan reports it natively | `harness/common.h` `draw_boottime`; `harness/hs_laws.h` `any_clocks` for the `hs_` specs |
| L03 | The public keys of a device's peers are unique, and a peer in the tables holds 1 to `INT_MAX - 1` references, never 0 | the device's invariants: peer.c refuses duplicate keys and removes a peer from the tables before its last reference goes; at `INT_MAX` the kernel's get saturates and leaks the peer, which takes 2^31 - 1 holders | `harness/common.h` `hnodes_add`, `draw_peer_refs` |
| L04 | `wg_noise_received_with_keypair(keypairs, NULL)` is covered: receive.c always passes the keypair it looked up, but the function's behaviour on NULL is defined (with no next keypair, NULL is the next keypair and the slots rotate) and the spec `x_keypairs` states it | - | `harness/x_keypairs.c` |
| L05 | The Diffie-Hellman agreement of X25519 that handshake completeness needs is proved, not assumed: the proof's model of the Curve25519 code, `x25519_m`, refines the verified Montgomery ladder of fiat-crypto, and X25519(a, X25519(b, 9)) = X25519(b, X25519(a, 9)) for 32-byte scalars follows from the group law of fiat-crypto's Montgomery curve (`x25519fiat/`, with fiat-crypto, Coqprime and Rewriter vendored unmodified in `vendor/fiat-crypto/`). `x_handshake` states completeness only when the Diffie-Hellman values agree, so its first comment calls the agreement "not proved here"; the proof of `hs_matching_keys` uses it, among others | - | `harness/x_handshake.c`; `x25519fiat/` |
| L06 | `wg_cookie_validate_packet`, `wg_cookie_add_mac_to_packet` and `wg_cookie_message_create` are called on messages of at least 32 bytes (the two MACs) | their callers pass only handshake messages of fixed sizes (148 and 92 bytes) | `harness/x_cookie_mac.c`, `x_cookie_reply.c` |
| L07 | Not covered: peer.c, device.c, netlink.c, send.c, receive.c (except `counter_validate` (S19), the reduced `validate_header_len` of the data path (S24) and the handshake receive path (S22, S23, with L14)), timers.c (except `wg_birthdate_has_expired`), ratelimiter.c, allowedips.c, socket.c, queueing.c, the scatterlist AEAD and the architecture-specific crypto | outside the handshake and the part of the data path that can be extracted | the specs |
| L08 | `x_prim_aead` covers every `size_t` length of message and associated data | with P22 and P23, `poly1305_update` and `chacha_crypt` take the `size_t` lengths themselves | `harness/x_prim_aead.c` |
| L09 | `hmac` with a key longer than 64 bytes: no caller passes one (all keys are 32 bytes), so that branch is claimed only as far as the callers reach it | dead code in this context | - |
| L10 | `x_prim_x25519` (fiat32's Curve25519 equals RFC 7748's X25519 on every input) is not proved and not claimed; it is tested only. The protocol specs are about `curve25519()` as linked (C01) | a separate proof target | `src/contracts/laws.v` |
| L11 | `x_prim_poly1305` gives `poly1305_update` chunks of any `size_t` length, bounded only by the message, itself bounded by L13 | with P22, `poly1305_update` takes a `size_t` | `harness/x_prim_poly1305.c` |
| L12 | The primitive specs (`x_prim_*` and the `ae_` specs) end the run when `malloc` returns NULL for an empty buffer (`n = 0`) instead of continuing with a NULL pointer; `n = 0` stays covered when `malloc(0)` returns a pointer | the spec would compute `NULL + 0` | the specs |
| L13 | The specs `x_prim_blake2s`, `x_prim_poly1305` and `x_prim_aead` end the run when a drawn buffer length (message, associated data, the bytes given to decrypt) exceeds `PTRDIFF_MAX` (2^63 - 1), and so do `x_transport_order` (payload length above `PTRDIFF_MAX - 32`) and `x_transport_len` (packet length above `PTRDIFF_MAX - 32`). The lengths are otherwise unbounded. The `ae_` specs draw their lengths up to `PTRDIFF_MAX` (`PTRDIFF_MAX - 16` for a message that gets a 16-byte tag) | no C implementation creates an object larger than `PTRDIFF_MAX` (pointer differences inside it must fit `ptrdiff_t`; glibc's `malloc` returns NULL beyond it), but CompCert's memory model and VST's `malloc_spec'` allow objects of up to 2^64 - 1 bytes, which would make the specs cover buffers that cannot exist: `blake2s_update`'s `DIV_ROUND_UP(inlen, 64)` wraps for `inlen` of 2^64 - 63 or more. This is an assumption about the environment, not about the code | the specs' first comments; `x_prim_aead` bounds the message by `PTRDIFF_MAX - 16`, since its ciphertext buffers have `n + 16` bytes |
| L14 | Of receive.c's handshake path, `prepare_skb_header` (UDP and IP parsing, length trim, `pskb_may_pull`) and the handshake queue (`ptr_ring`, worker, queue-length accounting) are not verified: `harness/x_handshake_receive.c` hands a packet over as `wg_packet_receive`'s type switch does (`validate_header_len`, then types 1 to 3), and the queue length is an input | the queue is concurrent, and the parsing is the network stack | `harness/x_handshake_receive.c` |
| L15 | The specs `x_transport_order` and `x_transport_keepalive`, and the admitted-packet half of `x_transport_len`, assume that receive.c runs the AEAD check and the replay counter in this order: `decrypt_packet` (in `wg_packet_decrypt_worker`) verifies the tag and marks the packet `PACKET_STATE_CRYPTED` or `PACKET_STATE_DEAD` without touching the counter; `wg_packet_rx_poll` calls `counter_validate(&keypair->receiving_counter, nonce)` only for a `CRYPTED` packet and delivers only an accepted one (`wg_packet_consume_data_done`). The specs compose the real functions of the two stages (the kernel's `chacha20poly1305_decrypt`, the contiguous-buffer form of what `decrypt_packet` runs through `chacha20poly1305_decrypt_sg_inplace`, and `wg_counter_validate` of S19) in that order and check the invariants: a bad tag leaves the replay counter unchanged byte for byte and delivers nothing; a good tag reaches the counter, whose verdict and new state agree with the window model; a keepalive delivers 0 bytes. The wiring itself is assumed: `decrypt_packet`, `wg_packet_rx_poll` and `wg_packet_consume_data_done` use `sk_buff`, scatterlists, `skb_cow_data`, NAPI, RCU and the per-peer queues, which are not modelled; likewise how the type word and the length reach `validate_header_len` (S24) | the pipeline cannot be extracted to Clight | `harness/transport.h`, `x_transport_order.c`, `x_transport_keepalive.c`, `x_transport_len.c` |
| L16 | `x_transport_send_nonce` is a model only: send.c is not in the code under test, so the spec runs the send path's nonce draw as the spec writes it out from send.c at the pin (`wg_packet_send_staged_packets`: no draw on an invalid key; `nonce = atomic64_inc_return(&keypair->sending_counter) - 1`; `nonce >= REJECT_AFTER_MESSAGES` invalidates the key), with the shim's `atomic64_inc_return` (S04) and the kernel's `REJECT_AFTER_MESSAGES` as compiled (C04). The run also ends before the counter would step from 2^63 - 1 to 2^63 (a key never sends 2^63 messages: it expires after `REJECT_AFTER_TIME`, 180 s); nonces of 2^63 and more are still covered, from start counters in [2^63, `REJECT_AFTER_MESSAGES`] | send.c needs skb allocation, padding to `MESSAGE_PADDING_MULTIPLE` and the per-peer transmit queue | `harness/x_transport_send_nonce.c` |
| L17 | `hs_stale_response` assumes that A's second initiation drew a sender index other than the first's; when they are equal, which happens with probability 2^-32, the spec claims nothing | the index is a random 32-bit value, and with the same index the old response would name A's new handshake | `harness/hs_stale_response.c` (its ASSUMPTION, a `gp_assume`) |
