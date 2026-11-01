(* law handshake_receive, phase B4, segment I, part E3:
   if15 = `if (t'79) { t'357 = target->snap.last_initiation_consumption; t'82 = m_not_flood(t'357, now); t'81 = (bool) t'82 } else t'81 = 0` (port of hci5_p7_E3).
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

Lemma hrx5_B4_I_E3_ok {Espec: OracleKind} gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s key ck1 h1 a P :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hrx5_B4_I_c1f x25519 aead_dec (hrx5_ID x25519 R) M = Some (s, key, ck1, h1) ->
  pk_find PS s = Some (a, P) ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B4_I_Q7 x25519 aead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s ck1 h1 a P) hrx5_B4_I_if15
    (overridePost (hrx5_B4_I_Q8 x25519 aead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s ck1 h1 a P) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HH Hc1f Hpk.
  destruct (hrx5_B4_I_c1f_some x25519 aead_dec _ _ _ _ _ _ Hc1f) as [Hfwd Hc1].
  unfold hrx5_B4_I_Q7, hrx5_B4_I_Q8, hrx5_B4_I_st, hrx5_B4_I_scr, hrx5_B4_I_ci2, hrx5_B4_I_c2v, hrx5_B4_I_b15,
    hrx5_Delta, hrx5_RB, hrx5_B4_I_if15, hrx5_ltemps, hrx5_ptrs, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, wg_consts.
  cbn [app obj_bytes obj_kind obj_rep obj_ok].
  set (SS := hrx5_B4_I_SS x25519 (hrx5_ID x25519 R) P).
  destruct (m_consume_init2_model aead_dec SS ck1 h1 (im_enct M)) as [[[t ck2] h2]|] eqn:H2m;
    cbv beta iota.
  2: {
    simplify_func_tycontext. abbreviate_semax. Intros.
    forward_if. 1: { hrx5_B4_I_absurd. }
    forward.
    unfold hrx5_R, frame_ret_assert, loop1_ret_assert, function_body_ret_assert; cbn [RA_normal].
    entailer!. }
  destruct (ts_newer t (hs_ts (p_hs P))) eqn:Htn;
    cbv beta iota.
  2: {
    simplify_func_tycontext. abbreviate_semax. Intros.
    forward_if. 1: { hrx5_B4_I_absurd. }
    forward.
    unfold hrx5_R, frame_ret_assert, loop1_ret_assert, function_body_ret_assert; cbn [RA_normal].
    entailer!. }
  simplify_func_tycontext. abbreviate_semax. Intros.
  destruct (hrx5_B4_I_after_ok x25519 R L NS PS KE T head nk H0) as (Hpe & Hsh & Hnone & Hsome).
  destruct (Hsome s a P Hpk) as (NS1 & N & NS2 & P' & sn & Hfm & HNS & HinP & Hnf & Hrest).
  destruct Hrest as (HpN & Hrs & Hsn & Hsnhs & HokP & Hlic).
  assert (Hhp: hnodes_peers4 NS PS) by apply H0.
  assert (Hh: hrx5_head (hnodes_snapped4 T NS PS) = hrx5_head NS)
    by (apply hrx5_B4_I_head_snapped; exact Hhp).
  assert (Hnode: hnodes_rep4 W (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS) |--
    (@data_at W Ews t_hnode4 (hrx5_B4_I_nv N (hrx5_head NS2)) (hn_addr N) *
     (@data_at W Ews t_hnode4 (hrx5_B4_I_nv N (hrx5_head NS2)) (hn_addr N) -*
      hnodes_rep4 W (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS)))%logic).
  { rewrite HNS. apply hrx5_B4_I_nv_node. }
  rewrite <- Hnf.
  forward_if. 2: { hrx5_B4_I_absurd. }
  sep_apply Hnode. Intros.
  rewrite (hrx5_B4_I_nv_nvs Ews N (hrx5_head NS2) (hn_addr N) sn Hsn).
  forward.
  match goal with |- semax _ (PROPx _ (LOCALx (temp _ ?v :: _) _)) _ _ => set (vv := v) end.
  assert (Hv: vv = Vlong (hs_lic (sn_hs sn))) by (subst vv; unfold hrx5_B4_I_nvs, hsnap_val; reflexivity).
  clearbody vv. subst vv. rewrite Hsnhs.
  rewrite <- (hrx5_B4_I_nv_nvs Ews N (hrx5_head NS2) (hn_addr N) sn Hsn).
  sep_apply (hrx5_B4_I_wand1 (@data_at W Ews t_hnode4 (hrx5_B4_I_nv N (hrx5_head NS2)) (hn_addr N))
    (hnodes_rep4 W (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS))).
  clear Hnode Hsome Hnone.
  rewrite Hnf.
  freeze [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31;32;33;34;35;36;37;38;39;40;41;42;43] FZ.
  forward_call (hs_lic (p_hs P), s_boot S).
  1: { rewrite Int64.signed_eq_unsigned; rep_lia. }
  forward.
  thaw FZ.
  unfold hrx5_R, frame_ret_assert, loop1_ret_assert, function_body_ret_assert; cbn [RA_normal].
  destruct (not_flood (hs_lic (p_hs P)) (s_boot S)); entailer!.
Qed.

End Seg.
