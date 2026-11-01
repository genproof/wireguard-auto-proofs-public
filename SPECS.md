# The specs

This repository proves specs of WireGuard in the Linux kernel. Each spec is a small C program, `harness/<name>.c`,
that you can run. QuickProof turns each spec into a Coq theorem: for every input the spec allows, none of its checks
fails and nothing it runs has undefined behaviour (through VST's adequacy theorem, whose instance for QuickProof's
environment is upcoming). This page explains WireGuard in a few lines, how to read a spec, and what each spec says.

## WireGuard in two minutes

- WireGuard is a VPN: two peers that know each other's public key set up shared keys, then send each other
  encrypted packets. In Linux it lives in `drivers/net/wireguard/`.
- The handshake is Noise_IKpsk2 (the Noise framework, plus a preshared key). The initiator sends a 148-byte
  *initiation*, the responder answers with a 92-byte *response*, and both derive a pair of transport keys
  (`noise.c`). Each message carries a random sender index that names the handshake it belongs to, and two MACs
  (`cookie.c`) that let a device under load demand a cookie before it does any expensive work.
- Each peer holds up to three keypairs: *current*, *previous* and *next*. `wg_noise_handshake_begin_session` turns a
  finished handshake into a new keypair and erases the handshake's secrets.
- Each transport data packet is encrypted with ChaCha20-Poly1305 under the sending key and a 64-bit counter (the
  nonce). The receiver keeps a *replay window* (`counter_validate`, RFC 6479's algorithm): it accepts a nonce once,
  and only if it is not too far below the newest one it has accepted (`COUNTER_WINDOW_SIZE`, 8128), and never once
  the counter reaches `REJECT_AFTER_MESSAGES` (2^64 - 8130).
- The primitives, from `lib/crypto/`, are BLAKE2s (hashing and the key derivation), ChaCha20 and Poly1305, their
  combination ChaCha20-Poly1305 and its extended-nonce variant XChaCha20-Poly1305 (authenticated encryption), and
  Curve25519 (the Diffie-Hellman agreement).

## How to read a spec

```c
size_t len = upto(PTRDIFF_MAX - 16);          // any length
u8 *message = any_bytes(len);                 // any len bytes
... call the kernel ...
gp_assert(ok != 0);                           // what must hold
gp_assert(bytes_eq(opened, message, len));
```

- `nondet_*`, `upto(max)`, `any_u64()` and `any_bytes(n)` stand for *any* value: the theorem covers all of them at
  once, not a sample. Keys, nonces, messages, the order of calls, clocks, randomness and prior states are arbitrary
  wherever the spec allows.
- `gp_assert(c)` is the property; the `x_` specs write it `CHECK(c)`. Where a spec restricts its inputs, its first
  comment says so (for example `hs_stale_response`'s ASSUMPTION).
- "A failed malloc ends the run": when the spec cannot allocate one of its own buffers, the run stops and the spec
  claims nothing about it. Allocations inside the kernel code may fail at any call, and the theorems cover what the
  kernel then does.
- The first comment of each file is the claim, in full; the tables below only summarize it. Where they differ, the
  comment is right.
- The short specs share small headers with no models of WireGuard: `wg_laws.h` (40 lines: any bytes, a copy, a
  comparison, a new replay counter), `hs_laws.h` (63 lines: two devices with a peer for each other, set up field by
  field as `device.c`, `netlink.c` and `peer.c` set them up, since those files are not in the code under test, and
  any clocks) and `hs_unchanged.h` (45 lines: a field-by-field copy and comparison of a peer's state). The line
  counts below include the headers each spec includes.
- The RFC, paper or kernel text a spec comes from is quoted in the file.

## The code under test

Linux at commit `551c722f`, with the two lib/crypto patches and the edits that [DEVIATIONS.md](DEVIATIONS.md) lists:
the handshake (`drivers/net/wireguard/noise.c`, `cookie.c`), the replay window of `receive.c`
(`patch/counter_validate.c`, copied byte for byte, then with its `goto` rewritten: P10) and the generic C of the
primitives (`lib/crypto/`), with the kernel environment of `patch/wg_shim.c` and `patch/include/`. Each short spec's
program contains only the C files it needs: the replay specs contain `counter_validate` alone, and the primitive
specs the primitives they use. The `x_` specs link every file of the code under test, without `patch/data_header.c`
except in the four transport specs (`UNITS_x_<name>` in `quickproof.conf`). Each contract, `src/contracts/<name>.v`,
lists its program's files.

## The short specs

All 19 are proved, together with the 19 `x_` specs below. Each is a theorem of its own in `src/contracts/laws.v` and
a conjunct of `suite` (`src/contracts/suite.v`).

### The replay window (`rp_`)

Each starts from a new key's replay window (zero, as `keypair_create` makes it); the nonces are any 64-bit values.

| spec | lines | what it says |
|---|---|---|
| `rp_fresh` | 73 | A nonce below `REJECT_AFTER_MESSAGES` and at most 8128 below the newest accepted nonce (or with none accepted yet) is accepted, after any other nonces. |
| `rp_duplicate` | 65 | A nonce that was accepted is rejected when it comes again, after any nonces in between. |
| `rp_too_old` | 66 | A nonce more than 8128 below the newest accepted nonce is rejected. |
| `rp_limit` | 59 | Every nonce at or above `REJECT_AFTER_MESSAGES` (2^64 - 8130) is rejected. |
| `rp_any_order` | 70 | For any start s with s + 8128 below `REJECT_AFTER_MESSAGES`, after any nonces below s, any distinct nonces from s to s + 8128, given in any order, are all accepted. |

### Authenticated encryption and the primitives (`ae_`)

Messages, associated data and ciphertexts are of any length up to `PTRDIFF_MAX` bytes, and `PTRDIFF_MAX - 16` for a
message that gets a 16-byte tag (DEVIATIONS.md L13).

| spec | lines | what it says |
|---|---|---|
| `ae_roundtrip` | 69 | ChaCha20-Poly1305: for any message, associated data, 64-bit nonce and key, decrypting what encryption wrote succeeds and gives back exactly the message. |
| `ae_xroundtrip` | 70 | The same for XChaCha20-Poly1305, with a 24-byte nonce. |
| `ae_fail_untouched` | 91 | A decryption that fails (either AEAD, any bytes as ciphertext) leaves every byte of its output buffer as it was. |
| `ae_split_blake2s` | 77 | BLAKE2s in one call gives the same hash as init, update over the message in any pieces, and final, for any key of 0 to 32 bytes and any output length of 1 to 32 bytes. |
| `ae_split_chacha20` | 79 | ChaCha20 over the whole message writes the same bytes as over it in pieces, all but the last a multiple of 64 bytes, for any key, block counter and nonce. |
| `ae_split_poly1305` | 73 | Poly1305 gives the same tag for the message in one update or in any pieces, for any key. |

### The handshake (`hs_`)

Each sets up devices A and B with any private keys and any preshared key, and runs with any randomness. All but
`hs_begin_session_state` also draw any clocks, with the boot clock below 2^62 ns (DEVIATIONS.md L02). A spec whose
handshake steps must succeed claims nothing about a run in which one of them fails.

| spec | lines | what it says |
|---|---|---|
| `hs_matching_keys` | 99 | When a handshake between A and B completes on both sides, A's sending key is B's receiving key and the other way round, and only A's keypair is the initiator's. |
| `hs_session_erases` | 106 | After an initiation and a response have been exchanged, a `wg_noise_handshake_begin_session` that succeeds leaves that side's handshake in state `HANDSHAKE_ZEROED`, with its ephemeral private key, the peer's ephemeral key and the chaining key all zero. |
| `hs_begin_session_state` | 105 | Beginning a session from a handshake in any state but `HANDSHAKE_CREATED_RESPONSE` or `HANDSHAKE_CONSUMED_RESPONSE` fails, allocates nothing and leaves the three keypair slots as they were. |
| `hs_response_state` | 96 | A response is taken only by a handshake that is waiting for one: in any state but `HANDSHAKE_CREATED_INITIATION`, consuming B's genuine response fails. |
| `hs_replay_initiation` | 93 | An initiation that B accepted is rejected when the same 148 bytes come again, at any later clocks, whether or not B answered it and began its session in between. |
| `hs_stale_response` | 97 | After a new initiation, B's response to the old one is rejected (assuming the new random sender index differs from the old one). |
| `hs_reject_initiation` | 153 | A consume_initiation that fails, on any 148 bytes and with B's handshake with A in any state, leaves B's peer for A as it was: every field of its handshake, its three keypair slots and its reference count. |
| `hs_reject_response` | 149 | A consume_response that fails, on any 92 bytes and after A's initiation, leaves A's peer for B as it was: every field of its handshake, its three keypair slots and its reference count. |

## The longer specs (`x_`)

The 19 specs whose names start with `x_` are longer. They check the kernel against a model of the handshake written
as plain C, and the primitives against reference implementations written from the RFCs, both in
`harness/common.h`. They were first proved under the names without the prefix, with the same statements, and their
first comments still use those names (`x_handshake.c` begins "Law `handshake`"). A twentieth, `x_prim_x25519`
(Curve25519 against RFC 7748's X25519), is stated but left out of `suite`: it is tested, not proved, and has no
theorem.

"Any" in the table means every value: any number of peers, table entries and operations, and any bytes, lengths and
clock values, up to the bounds the first comment states. Bounds shared by several specs are stated once: the boot
clock is below 2^62 ns (`draw_boottime` in `harness/common.h`, DEVIATIONS.md L02), buffer lengths are at most
`PTRDIFF_MAX` (L13), and the other exclusions are the L rows of DEVIATIONS.md.

| spec | what it says |
|---|---|
| `x_create_any` | From any prior state of the device, the peer and its handshake, `wg_noise_handshake_create_initiation` and `wg_noise_handshake_create_response` return what the model returns, write exactly the model's message bytes and handshake fields, and change nothing else, on every failure path too. |
| `x_consume_initiation_any` | `wg_noise_handshake_consume_initiation` on any 148 bytes, with any peers in any state, accepts exactly when the model does (the static key decrypts to a known peer, the timestamp is newer, the 20 ms flood limit holds, ...); it then updates that peer exactly as the model does, and on rejection it changes nothing. |
| `x_consume_response_any` | The same for `wg_noise_handshake_consume_response` on any 92 bytes and any contents of the index table. |
| `x_handshake` | For two devices with any keys, preshared key, clocks and randomness, every step of a full handshake returns the model's result and writes the model's bytes. When both identities are usable, the Diffie-Hellman values agree and none of them is zero, the timestamp is not zero, B's boot clock is at least 20 ms and the one allocation succeeds, every step succeeds and each side's sending key is the other's receiving key. Clearing the keypairs frees everything. |
| `x_replay` | Over any sequence of fresh and replayed initiations, with the clocks moving (the real-time clock also backwards), an initiation is accepted exactly when its timestamp is newer than every accepted one and the last acceptance was at least 20 ms earlier; a replay is always rejected and changes nothing. |
| `x_keypairs` | Over any sequence of session starts, key use, expiry, clearing, and gets and puts of references, the three keypair slots, every keypair, its reference count (with the saturation of the kernel's `refcount_t`), the index table and the frees agree with a model after every step, with no bound on references or sessions. |
| `x_handshake_clear` | From any state, `wg_noise_handshake_clear` zeroes exactly the handshake's session state, takes its entry out of the index table, and changes nothing else. |
| `x_config_any` | The seven configuration functions of `noise.c` and `cookie.c`, called over any prior contents, set exactly what the model says (a degenerate private key gives an unusable identity) and change nothing else. |
| `x_cookie_mac` | On any message of 32 to `UINT_MAX` bytes and any cookie state, `wg_cookie_add_mac_to_packet` and `wg_cookie_validate_packet` compute exactly the model's mac1, mac2 and verdict, the cookie secret is renewed once it is at least 120 seconds old, and nothing else changes. |
| `x_cookie_reply` | `wg_cookie_message_create` writes exactly the model's cookie reply, and `wg_cookie_message_consume` on any 64 bytes, with any peers and tables, updates exactly the cookie the model updates, or nothing. |
| `x_handshake_receive` | Over any sequence of packets of any bytes and lengths, `receive.c`'s `validate_header_len` and `wg_receive_handshake_packet` let only messages of the right type and length reach the handshake code, check mac1 (and under load mac2) before any of them, send exactly one cookie reply under load, and update the endpoint, timers and statistics only of the authenticated peer; a rejected packet changes nothing. |
| `x_counter` | Over any sequence of 64-bit nonces, the data path's replay window `counter_validate` accepts a nonce exactly when it is below the message limit, within 8128 of the highest accepted nonce, and not accepted before. |
| `x_transport_order` | With the kernel's AEAD decryption and `counter_validate` run in `receive.c`'s order (assumed, L15), for any sequence of received data packets (authentic, corrupted, replayed or random bytes), a packet with a bad tag leaves the replay window unchanged and delivers nothing, and an authentic one gets the window model's verdict. |
| `x_transport_keepalive` | With the same assumed order (L15), a keepalive (a data packet with an empty payload) follows the same authentication and replay rules as other data packets and delivers nothing, and a packet too short to hold a tag is rejected without a read past its end. |
| `x_transport_len` | For a data packet of any length and type word, the length check admits exactly the packets the length rules admit, and decryption never reads past the packet (for an admitted packet, decrypted as L15 assumes). |
| `x_transport_send_nonce` | The sending nonce, drawn as `send.c` draws it, never repeats or wraps, and sending is refused exactly from `REJECT_AFTER_MESSAGES` on. The spec contains a copy of `send.c`'s nonce draw (`send.c` itself is not in the code under test), and the run ends before the counter would step from 2^63 - 1 to 2^63 (L16). |
| `x_prim_blake2s` | BLAKE2s (`blake2s_init`, keyed init, `blake2s_update` in any chunks, `blake2s_final`, and the one-shot `blake2s()`) computes RFC 7693's BLAKE2s for any key of 0 to 32 bytes, output length of 1 to 32 bytes and message, and zeroes its context. |
| `x_prim_poly1305` | Poly1305, fed in any chunks of any length up to `PTRDIFF_MAX` (2^63 - 1 bytes), computes RFC 8439's Poly1305 for any key and message, and zeroes its context. |
| `x_prim_aead` | ChaCha20-Poly1305 encryption is RFC 8439's construction, and XChaCha20-Poly1305 encryption is that construction with the subkey that HChaCha20 derives from the key and the first 16 bytes of the nonce, and the last 8 bytes as the nonce, for any lengths of message and associated data up to `PTRDIFF_MAX`. Decryption of any bytes succeeds exactly when the reference tag verifies and leaves the output unchanged otherwise. |

## What the specs do not say

- **Time.** A theorem says what holds *if* a call returns; it does not say that it returns.
- **The binary.** The theorems are about the C code as CompCert's semantics defines it, in the configuration of
  `quickproof.conf` (the generic C of the primitives, no architecture-specific code), not about a kernel built by
  another compiler; one thread only, without the kernel's locking.
- **The kernel around the code.** The shim (`patch/wg_shim.c`, `patch/include/`) stands for the kernel's
  allocator, clocks and randomness; [DEVIATIONS.md](DEVIATIONS.md) lists every difference from a kernel build.
- **What is not here.** `allowedips.c`; `ratelimiter.c`, whose answer is an input (S17); `peerlookup.c`, whose hash
  tables are replaced by lists tested against it (S14, S15); `send.c`, `timers.c`, `peer.c`, `device.c`,
  `netlink.c`, `socket.c`; and the parts of `receive.c` other than the replay window, the length check and the
  handshake path. The README's "Limits" section lists the rest.
