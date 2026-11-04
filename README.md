# WireGuard in Linux: proved C specs

This repository proves 38 specs of WireGuard in the Linux kernel at commit `551c722f` (2026-09-29). They cover the
replay window and the handshake checks of `receive.c`, the Noise_IKpsk2 handshake and its cookies (`noise.c`,
`cookie.c`), and the generic C of the cryptographic primitives these call: BLAKE2s, ChaCha20, Poly1305,
ChaCha20-Poly1305, XChaCha20-Poly1305 and Curve25519. A spec is a small C program, `harness/<name>.c`, that calls the
kernel's functions on any inputs and checks the results; you can run it. Its theorem says that for every value the
spec draws, no run has undefined behaviour in CompCert's semantics of C (through VST's adequacy theorem, whose
instance for QuickProof's environment is upcoming) and every check holds. AI agents wrote the proofs in Coq, with VST
and QuickProof v0.1.0. Coq checks them, and nothing the agents wrote in the proofs is trusted. The proofs contain no `Admitted` and
no axiom of their own. AI agents drafted the specs too, and they have not had a human review yet.

## What is proved

Nineteen short specs each state one property in a few dozen lines of C, with no model of the protocol.
[SPECS.md](SPECS.md) states each of them in one sentence; `harness/rp_fresh.c` and `harness/hs_matching_keys.c` are
good first reads. They say that:

- the replay window of the data path (`counter_validate` in `receive.c`, specs `rp_*`) accepts a new nonce that is
  below `REJECT_AFTER_MESSAGES` (2^64 - 8130) and at most 8128 below the newest accepted one, whatever nonces came
  before. It rejects a nonce it has accepted before, a nonce more than 8128 below the newest, and every nonce from
  `REJECT_AFTER_MESSAGES` on. After any nonces below a window of 8129 nonces that ends below
  `REJECT_AFTER_MESSAGES`, it accepts the window's nonces, each once, in any order;
- ChaCha20-Poly1305 and XChaCha20-Poly1305 (specs `ae_*`) give back the message when they decrypt what they
  encrypted, for any key and nonce, any message of up to `PTRDIFF_MAX - 16` bytes and any associated data of up to
  `PTRDIFF_MAX` bytes. A decryption that fails leaves its output buffer as it was. BLAKE2s, ChaCha20 and Poly1305
  give the same result over a message of up to `PTRDIFF_MAX` bytes in one call or in pieces (for ChaCha20, every
  piece but the last is a multiple of 64 bytes);
- in the handshake (specs `hs_*`), between two devices with any keys, any clocks (the boot clock below 2^62 ns) and
  any randomness, when every step succeeds on both sides, each side's sending key is the other's receiving key. A
  session that begins erases the handshake's ephemeral keys and chaining key. A session does not begin, and a
  response is not taken, unless the handshake is in a state that allows it. A replayed initiation is rejected, and
  so is a response to an older initiation if the new random sender index differs from the old one. A rejected
  initiation or response leaves the receiving side's peer for the sender as it was: its handshake, its keypair
  slots and its reference count.

The other 19 specs, prefixed `x_`, are longer: they compare the kernel with a model of the protocol written in C.
[The longer specs](#the-longer-specs) describes them.

The theorem of a spec is `harness_safe whole_prog`, where `whole_prog` is the spec linked with the kernel code it
calls (`src/contracts/<name>.v`). A failing check is undefined behaviour, so the theorem also says that every check
holds. The 38 theorems are proved together as `suite` in `src/contracts/suite.v`, their conjunction, and each is
also a theorem of its own in `src/contracts/laws.v`. [Limits](#limits) says what the step from the theorem to runs
relies on.

## Limits

The theorems are about the C code as CompCert's semantics defines it, on CompCert's model of 64-bit x86 (little
endian, 64-bit `long` and pointers), in the configuration described under [The code](#the-code). Allocation in the
kernel code may fail at any call, and the theorems cover both outcomes; when a spec cannot allocate one of its own
buffers, the run ends and the spec claims nothing about it. The code under test is changed: two lib/crypto patches,
idioms rewritten for VST, and a shim of plain C for the kernel around it ([The code](#the-code),
[DEVIATIONS.md](DEVIATIONS.md)). The changes are tested, not proved.

Not covered:

- runs of more than one thread: the locks, RCU and atomics are those of one thread (DEVIATIONS.md S02, L01);
- termination: VST proves partial correctness, so a run that never returns is not a counterexample;
- the rest of the driver (`peer.c`, `device.c`, `netlink.c`, `send.c`, `timers.c`, `ratelimiter.c`,
  `allowedips.c`, `peerlookup.c`, `socket.c`, `queueing.c`), `receive.c`'s parsing of UDP and IP headers and its
  handshake queue, and the scatterlist versions of the AEAD (L07, L14). The rate limiter's answer is an input
  (S17), and the hash tables of `peerlookup.c` are replaced by lists, tested against it (S14, S15);
- how `receive.c` wires the data path together: `x_transport_order`, `x_transport_keepalive` and `x_transport_len`
  assume that it checks the tag before the replay window, as its code does (L15);
- constant time and erasure on free: `crypto_memneq` and `crypto_xor` are byte loops in the shim (S09), and
  `kfree_sensitive` is a plain `free` (S05);
- that the model in `harness/common.h`, which the `x_` specs use, is WireGuard: it is written from the WireGuard
  paper, and reading it is the only check here;
- X25519 itself (`x_prim_x25519`), the primitives' other implementations (x86_64 assembly, donna64, hacl64), other
  configurations, the unpatched source, Eric Biggers' version of the lib/crypto fix, and binaries built by other
  compilers.

The result relies on Coq, VST, CompCert's semantics of C, and `clightgen`, which translates the C files into the
Clight programs the theorems are about. It also relies on QuickProof's model of the environment
(`quickproof/include/quickproof.h`, `quickproof/coq/QuickProof/Env.v` and `Contract.v`), its translation scripts and
`qp verify`, which decides what is accepted; on the specs, which are the statements; and on the patch and the shim of
DEVIATIONS.md, which are tested. Each theorem is VST's judgement `semax_prog` about its program. VST's adequacy
theorem, which takes a proved `semax_prog` to "no run has undefined behaviour", is proved in VST but not yet
instantiated in Coq for this environment; that instance is upcoming. QuickProof's
[docs/GUARANTEES.md](https://github.com/genproof/quickproof-public/blob/v0.1.0/docs/GUARANTEES.md) (also
`quickproof/docs/GUARANTEES.md` in a clone) explains what a theorem means and what it trusts.

## The code

The code is from Linux at commit `551c722f40809618230001baccf219193e22fc5a` (2026-09-29): the WireGuard files
`noise.c` and `cookie.c` (the handshake, about 1,100 lines), `receive.c` and their headers, and `lib/crypto/` with
the headers of `include/crypto/`. It is compiled the way an architecture without optimised crypto and without
`__int128` compiles it, because CompCert has neither: the generic C of BLAKE2s and ChaCha20, Poly1305 with 32-bit
limbs (`poly1305-donna32.c`), and Curve25519 with 32-bit limbs (`curve25519-fiat32.c`). An x86_64 kernel builds
other variants of Poly1305 and Curve25519. Three pieces of `receive.c` are copied out and verified: the replay
window `counter_validate`, copied byte for byte and then with its `goto` rewritten (P10); `validate_header_len` and
`wg_receive_handshake_packet`, byte for byte, for `x_handshake_receive`; and `validate_header_len` once more, as a
reduction that takes the packet's type word and length as parameters, for `x_transport_len`.

The code carries two patches on top of `551c722f`, patches 4 and 5 of our series "lib/crypto: Handle large lengths
in poly1305 and chacha20poly1305"
([v1 on linux-crypto](https://lore.kernel.org/r/20261012-libcrypto-4gib-lengths-v1-0-ea566c129a2e@genproof.com)):

- lib/crypto: poly1305: Take a size_t length in poly1305_update()
- lib/crypto: chacha: Take a size_t length in chacha_crypt()

They are in `patch/series/` and are applied verbatim: the four files they change are identical at `551c722f` and at
the base of the series. Without them, `x_prim_poly1305` and `x_prim_aead` are false at lengths of 4 GiB and more:
`poly1305_update()` can copy past its 16-byte buffer, and ChaCha20-Poly1305 uses only the low 32 bits of its lengths.
The proof work on these two specs found this. The `ae_` specs take such lengths too, so they are also about the
patched code. Patches 1 to 3 of the series make the Poly1305 assembly of other architectures handle such lengths; it
is not built here.

Eric Biggers then fixed the same lengths upstream in his own series, "lib/crypto: Use size_t lengths for Poly1305
and ChaCha" ([linux-crypto, 2026-10-14](https://lore.kernel.org/all/20261014152604.323310-1-ebiggers@kernel.org/)),
which converts Poly1305 and ChaCha to `size_t` lengths throughout and credits our report. On 2026-10-16 he applied
it to the lib/crypto tree,
[libcrypto-next](https://git.kernel.org/pub/scm/linux/kernel/git/ebiggers/linux.git/log/?h=libcrypto-next),
together with our follow-up for 32-bit arm and MIPS
([linux-crypto](https://lore.kernel.org/r/20261014-libcrypto-chacha-32bit-2gib-v1-0-e0719ca0be89@genproof.com)).
The code verified here has our two patches, not Eric's series. Proving the specs again on his series is future
work.

Besides these two patches, the code is changed in two ways, each described in [DEVIATIONS.md](DEVIATIONS.md) with
its test:

- idioms VST cannot reason about are rewritten (rows P01 to P21): `goto` becomes `break` out of a block, struct
  copies and type-punning stores are written element by element, and an empty compound literal becomes `memset`.
  Every rewrite carries a `QUICKPROOF` comment on its block. `patch/check.sh` shows that the code is exactly upstream plus
  `patch/wgpatch.py`, and `patch/diff.sh` runs the unmodified and the changed code on the same pseudo-random inputs
  under sanitizers and finds the same outputs;
- the kernel around the code (types, locks, allocation, clocks, randomness, the peer and device structures, the two
  lookup tables) is a shim of plain C for one thread (rows S01 to S25), compared with the kernel's own code by
  `patch/shimtest/shimtest.sh` and `patch/tests/refcount_check.sh`.

Rows C01 to C07 list the configuration above.

## How to check it

```sh
git clone --branch v0.1.0 https://github.com/genproof/quickproof-public.git quickproof
git clone --recursive https://github.com/genproof/wireguard-auto-proofs-public.git
quickproof/tools/qp verify wireguard-auto-proofs-public --base contract
```

Run `qp` from a QuickProof checkout of your own at the tag `v0.1.0`, as above. `qp verify` checks that the
files of this repository's `quickproof/` that decide what a theorem says equal those of the framework the `qp` you
run belongs to, so your checkout is the framework you trust. The `quickproof/` submodule pins QuickProof
v0.1.0 (commit `80c8cd5`) and is this repository's own copy, a convenience for building the proof and running
the specs: `quickproof/tools/qp verify` run from it would only compare that copy with itself, and its report says so.

This needs the toolchain that [QuickProof's README](https://github.com/genproof/quickproof-public/blob/v0.1.0/README.md)
lists (Coq 8.20.1, CompCert 3.15 and VST 2.15, from opam), on `PATH` or with `QP_OPAM_SWITCH` set to its opam
switch. QuickProof's Docker image ships the same toolchain
([docs/DOCKER.md](https://github.com/genproof/quickproof-public/blob/v0.1.0/docs/DOCKER.md)).

`qp verify` clones the repository again and builds the vendored fiat-crypto, Coqprime and Rewriter from source (the
directories listed in `run/prebuild`). It checks that nothing that defines the statements has changed since the
commit tagged `contract`. It regenerates the Clight (the C dialect, defined by CompCert, that the
theorems are about) from the C sources and compares it with the committed files. It builds the proof and compares
each theorem's statement with the one at `contract`. It prints `Print Assumptions`, searches the sources
for `Admitted`, `admit`, `Axiom`, `Parameter` and `Conjecture`, and exits 0 when everything passes.

The proof has about 1,500 modules; a run of `qp verify` takes about 19 hours with 4 build jobs on 16 CPUs.

`contract` holds the statements of the 38 specs, each `Admitted`, and everything else that defines them, without the
proof in `src/proof/`. It is the commit before the proof. The short specs were stated before any proof of them, on 20
October 2026. One of them, `ae_fail_untouched`, was corrected on 22 October, when the proof attempt showed that the
spec itself could read through a null pointer; the proof came after. This repository's history is a two-commit export
of that work. `contract` also states `x_prim_x25519`, which is tested, not proved: the proof commit removes its
contract file, and in the other 38 it moves each statement to `src/contracts/laws.v`.

To build without the checks, build each directory of `run/prebuild` with
`coq_makefile -f _CoqProject -o CoqMakefile && make -f CoqMakefile`, then do the same at the top of the repository.

`qp verify` prints `Print Assumptions` once for all the theorems together, so its list is an upper bound for each
spec. The list has 13 entries:

- standard axioms: classical logic (`Classical_Prop.classic`), functional and propositional extensionality,
  `Eq_rect_eq.eq_rect_eq`, CompCert's `proof_irr`, `Extensionality_Ensembles`, and two axioms of Coq's classical
  reals (`sig_forall_dec`, `sig_not_dec`);
- the declarations of VST's abstract `malloc`/`free` library: `mem_mgr` and `malloc_token`, and the axioms
  about them `malloc_token_valid_pointer`, `malloc_token_local_facts` and `create_mem_mgr`.

The tests of DEVIATIONS.md need gcc with AddressSanitizer and UndefinedBehaviorSanitizer, and the unmodified
upstream files, which `patch/upstream.sh` fetches from GitHub (only the files needed, at the pinned commit) or reads
from a local Linux clone named by `LINUX`.

## Layout

- `drivers/net/wireguard/`, `lib/crypto/`, `include/crypto/`: the Linux files, with the patch applied;
  `COPYING` and `LICENSES/`: the kernel's licence texts;
- `harness/`: the specs; `common.h`, the model and the reference primitives of the `x_` specs; `wg_laws.h`,
  `hs_laws.h` and `hs_unchanged.h`, the small helpers of the short specs; `prim_aead.h` and `transport.h`, the shared
  parts of the AEAD and transport specs;
- `patch/`: the patch (`wgpatch.py`, `series/`, `check.sh`), the shim (`include/`, `wg_shim.c`), the functions
  copied out of `receive.c` (`counter_validate.c`, `data_header.c`, `receive_handshake.c`), `upstream.sh` and
  `upstream/` (`counter_validate.c` before the goto rewrite), `tree.sh` (the C side copied out for native tests),
  and the tests of DEVIATIONS.md;
- `env.c` and `env/`: value distributions for native and interpreter test runs (`env/` for the `rp_` specs; not
  part of any theorem);
- `quickproof.conf`: which C files are translated to Clight and, for the `x_` specs, which are linked into each
  spec's program; `quickproof/`: the framework, a submodule pinned at QuickProof v0.1.0 (commit `80c8cd5`);
- `src/<unit>/`, `src/harness/*/`: the generated Clight (`code.v`); `src/units/`, `src/contracts/`: the contracts,
  with the theorems in `laws.v` and `suite.v`; `docs/laws-gen/laws.py`: the generator of `laws.v`;
- `src/proof/`, `x25519fiat/`: the proof, about 300,000 lines of Coq; `vendor/fiat-crypto/`: the vendored Coq
  libraries; `run/prebuild`: the vendored directories `qp verify` builds first.

## The longer specs

The 19 specs whose names start with `x_` check the kernel against a model. The model, in `harness/common.h`, is the
handshake of the WireGuard paper written as plain C: its own HMAC, HKDF, TAI64N timestamps, message layout, mac1,
mac2 and cookies, over the kernel's primitives. The specs about the primitives compare the kernel's code with
reference implementations written from the RFCs, also in `harness/common.h`. They cover the handshake functions
from any prior state, a full handshake, replayed initiations, keypair rotation and reference counts, the
configuration functions, the MACs and cookie replies, the handshake checks of `receive.c`, the replay window, the
length check of data packets, the data path's order of tag check and replay window (assumed, L15), the sending
nonce (a model of `send.c`'s draw, L16), and BLAKE2s, Poly1305, ChaCha20-Poly1305 and XChaCha20-Poly1305.
[SPECS.md](SPECS.md) states each of them in one sentence. They write their checks as `CHECK(c)`, as the short specs
write `gp_assert(c)`.

Several proofs, `hs_matching_keys` among them, use the Diffie-Hellman agreement of X25519: X25519(a, X25519(b, 9)) =
X25519(b, X25519(a, 9)). It is proved, not assumed. The proof's model of the Curve25519 code refines the verified
Montgomery ladder of [fiat-crypto](https://github.com/mit-plv/fiat-crypto), and the agreement follows from the group
law of fiat-crypto's Montgomery curve (`x25519fiat/`). fiat-crypto, Coqprime and Rewriter are vendored unmodified in
`vendor/fiat-crypto/` (pins and licences in `vendor/fiat-crypto/PIN`). `x_handshake` states its completeness only
for the case where the Diffie-Hellman values agree, which is why its first comment calls the agreement "not proved
here".

A twentieth long spec, `harness/x_prim_x25519.c`, states that fiat32's Curve25519 computes RFC 7748's X25519 on
every input. It is tested but not proved, and it has no theorem here.

## Related work

The WireGuard protocol has had formal proofs of its own. Jason Donenfeld and Kevin Milner checked the handshake's
security properties in a symbolic model with Tamarin
([wireguard.com/formal-verification](https://www.wireguard.com/formal-verification/)), and Benjamin Lipp, Bruno
Blanchet and Karthikeyan Bhargavan gave a computational proof of the protocol with CryptoVerif
([EuroS&P 2019](https://bblanche.gitlabpages.inria.fr/publications/LippBlanchetBhargavanEuroSP19.pdf)). Those proofs
are about the protocol, not about an implementation. The proofs here are about the kernel's C. The model in
`harness/common.h` is not formally connected to theirs.

The closest project is HighVoltage, conceived and funded by RAND's Center for AI, Security and Technology, in which
Galois (with VST in Rocq) and Math, Inc. (with Lean) set out to verify "the ~1,200 lines of code in the deployed
Linux kernel WireGuard handshake" ([project page](https://www.galois.com/project/high-voltage)). It had published no
theorem statements when we checked in October 2026, so only the scopes can be compared.

## Licences

Our files (the proof and the contracts in `src/proof/`, `src/contracts/`, `src/units/` and `x25519fiat/`, the
scripts, `env.c`, `env/` and the documentation) are under the PolyForm Noncommercial License 1.0.0, copyright 2026
GenProof ([LICENSE](LICENSE), [NOTICE](NOTICE)), except what is under GPL-2.0, whether or not it carries an SPDX
header: the C files of `harness/` and `patch/`, which are compiled with the kernel's code and contain kernel code in
places (from `receive.c`, `send.c`, `timers.c`, `lib/refcount.c` and `include/linux/`), the kernel patches in
`patch/series/`, and the kernel code that `patch/wgpatch.py` writes into the kernel's files. The rest keeps the
licence it comes with: the Linux files are under GPL-2.0, some crypto files under GPL-2.0 or MIT ([COPYING](COPYING),
[LICENSES/](LICENSES)), and the changes to them are the patches in `patch/series/` and the rewrites marked `QUICKPROOF`,
which DEVIATIONS.md lists; each Clight file `src/**/code.v` has the licence of the C file `clightgen` generates it
from; the Coq libraries in `vendor/fiat-crypto/` are under MIT, Apache 2.0 or BSD 1-Clause (fiat-crypto, Rewriter)
and LGPL 2.1 (Coqprime), as `vendor/fiat-crypto/PIN` says; and the framework in `quickproof/` is QuickProof, under
its own licence (`quickproof/LICENSE`).

We chose a noncommercial license to make QuickProof freely available for community use while reflecting CompCert’s
licensing restrictions. We remind users that commercial use of CompCert requires separate permission.

Maintained by Vladimir Kukharenko.
