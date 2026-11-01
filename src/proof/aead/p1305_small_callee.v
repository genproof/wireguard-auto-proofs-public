(* The bodies of the small functions of poly1305.c (poly1305_core_init, poly1305_block_init_generic,
   poly1305_blocks_generic, poly1305_emit_generic, poly1305_init) with a context of their callees only, against
   the specifications of aead_spec.v (the same as aead_poly_small_body.v, whose context is the whole AEAD
   piece).  A program that links poly1305.c without the ChaCha20 and AEAD units (law ae_split_poly1305) can take
   these bodies: every function of their contexts is in it. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.poly1305.code WgNoise.poly1305_donna32.code.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.aead.aead_spec3.
Require Import WgNoise.proof.aead.aead_cce.
Require Import WgNoise.proof.aead.aead_bytes.
Require Import WgNoise.proof.aead.aead_poly_small_ctx.
Require Import WgNoise.proof.aead.aead_poly_small_body.

Local Open Scope Z_scope.

#[local] Existing Instance Poly1305.CS.

Lemma body_poly1305_core_init_callee :
  @semax_body (QPvarspecs Poly1305.qp) [@memset_spec Poly1305.CS] Poly1305.CS
    WgNoise.poly1305.code.f_poly1305_core_init poly1305_core_init_spec.
Proof.
  start_function.
  assert_PROP (field_compatible t_p1305_state [] hp) as FC by entailer!.
  rewrite data_at__memory_block. Intros.
  change (sizeof t_p1305_state) with 24.
  rewrite memory_block_data_at__tarray_tuchar_eq by rep_lia.
  forward_call (sh, hp, 0, 24).
  sep_apply (aead_ps_state_zero sh hp); auto.
  entailer!.
Qed.

Lemma body_poly1305_block_init_generic_callee :
  @semax_body (QPvarspecs Poly1305.qp) [poly1305_core_init_spec; poly1305_core_setkey_spec] Poly1305.CS
    WgNoise.poly1305.code.f_poly1305_block_init_generic poly1305_block_init_generic_spec.
Proof.
  start_function.
  assert_PROP (field_compatible t_p1305_block_state [] bp) as FC by entailer!.
  pose proof (aead_ps_fc_core_r bp FC) as FCU.
  sep_apply (aead_ps_bstate_split_ sh bp FC).
  forward_call (sh, bp).
  { cancel. }
  rewrite (@aead_data_at_tuchar_cs Poly1305.CS Poly1305Donna32.CS).
  forward_call (sh, offset_val 24 bp, rsh, raw, rk).
  rewrite (aead_ps_bstate_split sh [0; 0; 0; 0; 0] (p1305_r rk) bp FC).
  entailer!.
Qed.

Lemma body_poly1305_blocks_generic_callee :
  @semax_body (QPvarspecs Poly1305.qp) [poly1305_core_blocks_spec] Poly1305.CS
    WgNoise.poly1305.code.f_poly1305_blocks_generic poly1305_blocks_generic_spec.
Proof.
  start_function.
  assert_PROP (field_compatible t_p1305_block_state [] bp) as FC by entailer!.
  pose proof (aead_ps_fc_core_r bp FC) as FCU.
  rewrite (aead_ps_bstate_split sh h r bp FC).
  assert (HL: Zlength bs = 16 * (Zlength bs / 16)) by (rewrite (Z_div_mod_eq_full (Zlength bs) 16) at 1; lia).
  pose proof (Zlength_nonneg bs).
  rewrite aead_ps_prim_bytes_cs.
  forward_call (sh, bp, h, sh, offset_val 24 bp, r, msh, src, bs, Zlength bs / 16, hibit).
  { cancel. }
  Intros h'. Exists h'. rewrite (aead_ps_bstate_split sh h' r bp FC), aead_ps_prim_bytes_cs. entailer!.
Qed.

Lemma body_poly1305_emit_generic_callee :
  @semax_body (QPvarspecs Poly1305.qp) [poly1305_core_emit_spec] Poly1305.CS
    WgNoise.poly1305.code.f_poly1305_emit_generic poly1305_emit_generic_spec.
Proof.
  start_function.
  rewrite aead_ps_h_cs, aead_ps_words_cs, (@aead_data_at__tuchar_cs Poly1305.CS Poly1305Donna32.CS).
  forward_call (hsh, hp, h, nsh, np, s, dsh, dst).
  entailer!.
Qed.

Lemma body_poly1305_init_callee :
  @semax_body (QPvarspecs Poly1305.qp) [@get_unaligned_le32_spec Poly1305.CS; poly1305_block_init_generic_spec]
    Poly1305.CS WgNoise.poly1305.code.f_poly1305_init poly1305_init_spec.
Proof.
  start_function.
  assert_PROP (field_compatible t_p1305_ctx [] desc) as FC by entailer!.
  pose proof (field_compatible_nested_field t_p1305_ctx (DOT poly1305.code._state) desc
                ltac:(auto with field_compatible)) as FCs.
  simpl in FCs.
  assert (E: data_at ksh (tarray tuchar 32) (map Vubyte key) kp =
             data_at ksh (tarray tuchar (Zlength key)) (map Vubyte key) kp) by (rewrite H; auto).
  rewrite E.
  sep_apply (aead_ps_ctx_pre sh desc FC).
  flatten_sepcon_in_SEP. flatten_sepcon_in_SEP. flatten_sepcon_in_SEP. flatten_sepcon_in_SEP.
  assert_PROP (isptr kp) as Pkp by entailer!.
  forward_call (ksh, kp, 16, key). forward.
  forward_call (ksh, kp, 20, key). forward.
  forward_call (ksh, kp, 24, key). forward.
  forward_call (ksh, kp, 28, key). forward.
  forward.
  forward_call (sh, offset_val 40 desc, ksh, kp, key).
  rewrite E.
  sep_apply (aead_ps_init_post sh key desc H FC).
  entailer!.
Qed.

(* all of them *)
Theorem p1305_small_callee_bodies :
  (@semax_body (QPvarspecs Poly1305.qp) [@memset_spec Poly1305.CS] Poly1305.CS WgNoise.poly1305.code.f_poly1305_core_init poly1305_core_init_spec)
  /\ (@semax_body (QPvarspecs Poly1305.qp) [poly1305_core_init_spec; poly1305_core_setkey_spec] Poly1305.CS WgNoise.poly1305.code.f_poly1305_block_init_generic poly1305_block_init_generic_spec)
  /\ (@semax_body (QPvarspecs Poly1305.qp) [poly1305_core_blocks_spec] Poly1305.CS WgNoise.poly1305.code.f_poly1305_blocks_generic poly1305_blocks_generic_spec)
  /\ (@semax_body (QPvarspecs Poly1305.qp) [poly1305_core_emit_spec] Poly1305.CS WgNoise.poly1305.code.f_poly1305_emit_generic poly1305_emit_generic_spec)
  /\ (@semax_body (QPvarspecs Poly1305.qp) [@get_unaligned_le32_spec Poly1305.CS; poly1305_block_init_generic_spec] Poly1305.CS WgNoise.poly1305.code.f_poly1305_init poly1305_init_spec).
Proof. exact (conj body_poly1305_core_init_callee (conj body_poly1305_block_init_generic_callee (conj body_poly1305_blocks_generic_callee (conj body_poly1305_emit_generic_callee body_poly1305_init_callee)))). Qed.
