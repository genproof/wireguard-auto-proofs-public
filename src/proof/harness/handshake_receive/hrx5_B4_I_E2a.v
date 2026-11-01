(* law handshake_receive, phase B4, segment I, part E2a:
   c2 = `t'78 = m_consume_initiation_2(&ci, sst, mi->encrypted_timestamp)` (port of hci5_p7_E2a).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_cut.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mspec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require WgNoise.contracts.x_handshake_receive.
Require WgNoise.harness.x_handshake_receive.code.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
#[local] Existing Instance W_handshake_receive.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_defs.
Local Open Scope logic.

Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_I_pure.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_I_sep.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_I_defs.
Local Open Scope logic.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_B4_I_E2a_ok {Espec: OracleKind} gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s key ck1 h1 a P :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hrx5_B4_I_c1f x25519 aead_dec (hrx5_ID x25519 R) M = Some (s, key, ck1, h1) ->
  pk_find PS s = Some (a, P) ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B4_I_Q5 x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s key ck1 h1 a P) hrx5_B4_I_c2
    (overridePost (hrx5_B4_I_Q6 x25519 aead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s ck1 h1 a P) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HH Hc1f Hpk.
  destruct (hrx5_B4_I_c1f_some x25519 aead_dec _ _ _ _ _ _ Hc1f) as [Hfwd Hc1].
  destruct (hrx5_B4_I_c1_some x25519 aead_dec _ _ _ _ _ _ Hc1) as [Hok H1m].
  destruct HH as (Hx & Ha & Hxa).
  destruct (hrx5_B4_I_len_ok x25519 aead_enc aead_dec Hx Ha) as (HlIB & Hl1 & Hlpre & Hl2).
  unfold hrx5_B4_I_Q5, hrx5_B4_I_Q6, hrx5_B4_I_st, hrx5_B4_I_scr, hrx5_B4_I_ci1, hrx5_B4_I_ci2, hrx5_B4_I_c2v,
    hrx5_Delta, hrx5_RB, hrx5_B4_I_c2, hrx5_ltemps, hrx5_ptrs, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, wg_consts.
  cbn [app obj_bytes obj_kind obj_rep obj_ok].
  set (SS := hrx5_B4_I_SS x25519 (hrx5_ID x25519 R) P).
  assert (HlSS: Zlength SS = 32) by apply Hlpre.
  simplify_func_tycontext. abbreviate_semax. Intros.
  destruct (Hl1 _ _ _ s key ck1 h1 (proj1 (proj2 H3)) H1m) as (Hls & Hlkey & Hlck1 & Hlh1).
  assert (Hlt: Zlength (im_enct M) = 28) by apply H3.
  assert_PROP (isptr dp) as Hm. { entailer!. }
  sep_apply (hrx5_B4_I_msg_t Ews dp M). Intros.
  sep_apply (hrx5_B4_I_split_T SS (l_sst L)).
  forward_call (gv, Tsh, l_ci L, ck1, h1, bytes key, bytes s, Zrepeat Vundef 12, Ews, l_sst L,
                SS, offset_val 88 dp, im_enct M).
  1: { cancel. }
  1: { split; unfold bytes; rewrite Zlength_map; auto. }
  sep_apply (hrx5_B4_I_join_T SS (l_sst L)).
  sep_apply (hrx5_B4_I_wand1 (hbytes Ews (im_enct M) (offset_val 88 dp)) (init_rep Ews dp M)).
  unfold hrx5_R, frame_ret_assert, loop1_ret_assert, function_body_ret_assert; cbn [RA_normal].
  entailer!.
Qed.

End Seg.
