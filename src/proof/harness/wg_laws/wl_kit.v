(* The small shared bodies every ae_ law needs, as one proposition: the wg_laws.h helpers (wl_spec.v) and the byte
   inlines memzero_explicit / get_unaligned_le32 (blake2s/spec_shared.v), each proved for ANY compspecs with a
   context of its callees only.  Such a body moves into every per-law program that contains the function
   (asm_lib's asm_body_lift): its compspecs is the law's own and every spec of its context is a function the
   program contains.

   A law is proved as `wl_kit_ok -> harness_safe <law>.whole_prog`; wl_kit_proof.v proves wl_kit_ok once
   (wl_kit_holds, from wl_bodies.v and inline_bodies_any.v), and ae_laws_parts.v gives it to each law. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.proof.assembly.asm_env.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.harness.wg_laws.wl_spec.
Require WgNoise.harness.ae_roundtrip.code.
Require WgNoise.chacha20poly1305.code.

Definition wl_kit_ok : Prop :=
  (forall cs: compspecs,
     @semax_body nil [nondet_size_spec] cs WgNoise.harness.ae_roundtrip.code.f_upto upto_spec) /\
  (forall cs: compspecs,
     @semax_body nil [nondet_u32_spec] cs WgNoise.harness.ae_roundtrip.code.f_any_u64 any_u64_spec) /\
  (forall cs: compspecs,
     @semax_body nil [(_quickproof_malloc, @malloc_spec' cs); @asm_env.nondet_bytes_spec cs] cs
       WgNoise.harness.ae_roundtrip.code.f_any_bytes (@any_bytes_spec cs)) /\
  (forall cs: compspecs,
     @semax_body nil nil cs WgNoise.harness.ae_roundtrip.code.f_bytes_eq (@bytes_eq_spec cs)) /\
  (forall cs: compspecs,
     @semax_body nil [@memset_spec cs] cs WgNoise.chacha20poly1305.code.f_memzero_explicit
       (@memzero_explicit_spec cs)) /\
  (forall cs: compspecs,
     @semax_body nil nil cs WgNoise.chacha20poly1305.code.f_get_unaligned_le32 (@get_unaligned_le32_spec cs)).
