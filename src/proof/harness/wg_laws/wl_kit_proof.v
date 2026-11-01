(* wl_kit_ok holds: the callee-only bodies of wl_bodies.v and inline_bodies_any.v. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.harness.wg_laws.wl_kit.
Require WgNoise.proof.harness.wg_laws.wl_bodies.
Require WgNoise.proof.libc.inline_bodies_any.

Lemma wl_kit_holds : wl_kit_ok.
Proof.
  unfold wl_kit_ok.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); intro cs.
  - exact (@wl_bodies.wl_body_upto_ctx cs).
  - exact (@wl_bodies.wl_body_any_u64_ctx cs).
  - exact (@wl_bodies.wl_body_any_bytes_ctx cs).
  - exact (@wl_bodies.wl_body_bytes_eq_ctx cs).
  - exact (@inline_bodies_any.inl_body_memzero_explicit cs).
  - exact (@inline_bodies_any.inl_body_get_unaligned_le32 cs).
Qed.
