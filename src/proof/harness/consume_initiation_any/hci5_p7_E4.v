(* law consume_initiation_any, phase P7, segment E4: if (t'26) target = p.  Port of v1's hci3_p7_E4.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_cut.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_model.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_globals.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_spec.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_conv.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p7_pure.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p7_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p7_sep.
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hci5_p7_E4_ok {Espec: OracleKind} gv L FR R S w NS PS T head na KE m M s key ck1 h1 a P :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hci5_p7_c1 x25519 aead_dec (hci5_IB x25519 R) M = Some (s, key, ck1, h1) ->
  pk_find PS s = Some (a, P) ->
  semax (hci5_Delta x25519 aead_enc aead_dec)
    (hci5_p7_Q8 x25519 aead_dec gv L FR R S w NS PS T head na KE m M s ck1 h1 a P) hci5_p7_if17
    (overridePost (hci5_S7 x25519 aead_dec gv L FR) (hci5_R gv)).
Proof.
  intros HH Hc1 Hpk.
  destruct (hci5_p7_c1_some x25519 aead_dec _ _ _ _ _ _ Hc1) as [Hok H1m].
  destruct HH as (Hx & Ha & Hxa & Hrep).
  destruct (hci5_p7_len_ok x25519 aead_enc aead_dec Hx Ha) as (HlIB & Hl1 & Hlpre & Hl2).
  pose proof (hci5_p7_tgt_some x25519 aead_dec (hci5_IB x25519 R) PS M (s_boot S) _ _ _ _ _ _ Hc1 Hpk) as Htg.
  unfold hci5_p7_Q8, hci5_p7_st, hci5_p7_ci2, hci5_p7_b15, hci5_Delta, hci5_R, hci5_p7_if17,
    hci5_lvars, hci5_world, hci5_globs.
  cbv zeta. cbn [app].
  set (SS := hci5_p7_SS x25519 (hci5_IB x25519 R) P) in *.
  assert (HlSS: Zlength SS = 32) by apply Hlpre.
  destruct (hci5_p7_c2v aead_dec SS ck1 h1 M) as [[[t ck2] h2]|] eqn:H2m;
    cbv beta iota; cbv beta iota in Htg.
  2: {
    simplify_func_tycontext. abbreviate_semax. Intros.
    forward_if. 1: { hci5_p7_absurd. }
    forward.
    sep_apply (hci5_p7_hout SS (l_ss2 L) HlSS).
    unfold hci5_S7. Exists R S w NS PS T head na KE m M.
    rewrite Htg.
    unfold hci5_lvars, hci5_world, hci5_globs. cbn [hci5_tnode hci5_ci_rep app].
    entailer!. }
  destruct ((ts_newer t (hs_ts (p_hs P)) && not_flood (hs_lic (p_hs P)) (s_boot S))%bool) eqn:Hacc;
    cbv beta iota; cbv beta iota in Htg.
  2: {
    simplify_func_tycontext. abbreviate_semax. Intros.
    forward_if. 1: { hci5_p7_absurd. }
    forward.
    sep_apply (hci5_p7_hout SS (l_ss2 L) HlSS).
    sep_apply (@data_at_data_at_ HCS Tsh t_mcinit (mcinit_val ck2 h2 (bytes (kdf2 ck1 SS)) (bytes s) (bytes t)) (l_ci L)).
    unfold hci5_S7. Exists R S w NS PS T head na KE m M.
    rewrite Htg.
    unfold hci5_lvars, hci5_world, hci5_globs. cbn [hci5_tnode hci5_ci_rep app].
    entailer!. }
  simplify_func_tycontext. abbreviate_semax. Intros.
  forward_if. 2: { hci5_p7_absurd. }
  forward.
  sep_apply (hci5_p7_hout SS (l_ss2 L) HlSS).
  destruct (Hl1 _ _ _ s key ck1 h1 (proj1 (proj2 H1)) H1m) as (Hls & Hlkey & Hlck1 & Hlh1).
  assert (Hci: @data_at HCS Tsh t_mcinit (mcinit_val ck2 h2 (bytes (kdf2 ck1 SS)) (bytes s) (bytes t)) (l_ci L) |--
               hci5_ci_rep (Some (a, P, t, ck2, h2)) (l_ci L)).
  { unfold hci5_ci_rep. Exists (bytes (kdf2 ck1 SS)) (bytes s).
    apply andp_right; [apply prop_right; split; unfold bytes; rewrite Zlength_map; auto using hci5_p7_kdf2_len | apply derives_refl]. }
  sep_apply Hci.
  unfold hci5_S7. Exists R S w NS PS T head na KE m M.
  rewrite Htg.
  unfold hci5_lvars, hci5_world, hci5_globs. cbn [hci5_tnode app].
  entailer!.
Qed.

End Seg.
