(* law consume_initiation_any, phase P7, segment E2a: t'23 = m_consume_initiation_2(&ci, ss__2, msg->encrypted_timestamp).  Port of v1's hci3_p7_E2a.v. *)
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

Lemma hci5_p7_E2a_ok {Espec: OracleKind} gv L FR R S w NS PS T head na KE m M s key ck1 h1 a P :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hci5_p7_c1 x25519 aead_dec (hci5_IB x25519 R) M = Some (s, key, ck1, h1) ->
  pk_find PS s = Some (a, P) ->
  semax (hci5_Delta x25519 aead_enc aead_dec)
    (hci5_p7_Q5 x25519 aead_dec gv L FR R S w NS PS T head na KE m M s key ck1 h1 a P) hci5_p7_c2
    (overridePost (hci5_p7_Q6 x25519 aead_dec gv L FR R S w NS PS T head na KE m M s ck1 h1 a P) (hci5_R gv)).
Proof.
  intros HH Hc1 Hpk.
  destruct (hci5_p7_c1_some x25519 aead_dec _ _ _ _ _ _ Hc1) as [Hok H1m].
  destruct HH as (Hx & Ha & Hxa & Hrep).
  destruct (hci5_p7_len_ok x25519 aead_enc aead_dec Hx Ha) as (HlIB & Hl1 & Hlpre & Hl2).
  unfold hci5_p7_Q5, hci5_p7_Q6, hci5_p7_st, hci5_p7_ci1, hci5_p7_ci2, hci5_p7_c2v, hci5_Delta, hci5_R,
    hci5_p7_c2, hci5_lvars, hci5_world, hci5_globs, hci5_consts, wg_consts.
  cbv zeta. cbn [app].
  set (SS := hci5_p7_SS x25519 (hci5_IB x25519 R) P).
  assert (HlSS: Zlength SS = 32) by apply Hlpre.
  simplify_func_tycontext. abbreviate_semax. Intros.
  destruct (Hl1 _ _ _ s key ck1 h1 (proj1 (proj2 H1)) H1m) as (Hls & Hlkey & Hlck1 & Hlh1).
  assert (Hlt: Zlength (im_enct M) = 28) by apply H1.
  assert_PROP (isptr m) as Hm. { entailer!. }
  sep_apply (hci5_p7_msg_t Ews m M). Intros.
  sep_apply (hci5_p7_split_T SS (l_ss2 L)).
  forward_call (gv, Tsh, l_ci L, ck1, h1, bytes key, bytes s, Zrepeat Vundef 12, Ews, l_ss2 L,
                SS, offset_val 88 m, im_enct M).
  1: { cancel. }
  1: { split; unfold bytes; rewrite Zlength_map; auto. }
  sep_apply (hci5_p7_join_T SS (l_ss2 L)).
  sep_apply (hci5_p7_wand1 (hbytes Ews (im_enct M) (offset_val 88 m)) (init_rep Ews m M)).
  entailer!.
Qed.

End Seg.
