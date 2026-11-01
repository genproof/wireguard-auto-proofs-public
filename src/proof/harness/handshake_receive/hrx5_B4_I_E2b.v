(* law handshake_receive, phase B4, segment I, part E2b:
   if14 = `if (t'78) { t'80 = m_ts_newer(ci.ts, target->snap.latest_timestamp); t'79 = (bool) t'80 } else t'79 = 0` (port of hci5_p7_E2b).
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

Lemma hrx5_B4_I_E2b_ok {Espec: OracleKind} gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s key ck1 h1 a P :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hrx5_B4_I_c1f x25519 aead_dec (hrx5_ID x25519 R) M = Some (s, key, ck1, h1) ->
  pk_find PS s = Some (a, P) ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B4_I_Q6 x25519 aead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s ck1 h1 a P) hrx5_B4_I_if14
    (overridePost (hrx5_B4_I_Q7 x25519 aead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s ck1 h1 a P) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HH Hc1 Hpk.
  destruct (hrx5_B4_I_c1f_some x25519 aead_dec _ _ _ _ _ _ Hc1) as [Hfwd Hc1'].
  destruct (hrx5_B4_I_c1_some x25519 aead_dec _ _ _ _ _ _ Hc1') as [Hok H1m].
  destruct HH as (Hx & Ha & Hxa).
  destruct (hrx5_B4_I_len_ok x25519 aead_enc aead_dec Hx Ha) as (HlIB & Hl1 & Hlpre & Hl2).
  unfold hrx5_B4_I_Q6, hrx5_B4_I_Q7, hrx5_B4_I_st, hrx5_B4_I_ci2, hrx5_B4_I_c2v, hrx5_B4_I_b15,
    hrx5_B4_I_if14, hrx5_B4_I_scr, hrx5_rest, hrx5_ltemps, hrx5_ptrs, hrx5_lvars, hrx5_wcore, hrx5_globs.
  cbn [app obj_bytes obj_kind obj_rep obj_ok].
  set (SS := hrx5_B4_I_SS x25519 (hrx5_ID x25519 R) P).
  destruct (m_consume_init2_model aead_dec SS ck1 h1 (im_enct M)) as [[[t ck2] h2]|] eqn:H2m;
    cbv beta iota.
  2: {
    unfold hrx5_Delta. simplify_func_tycontext. abbreviate_semax. Intros.
    forward_if. 1: { hrx5_B4_I_absurd. }
    forward. destruct (hrx5_RB x25519 gv L FR); cbv beta iota; cbn [tycontext.RA_normal]. entailer!. }
  unfold hrx5_Delta. simplify_func_tycontext. abbreviate_semax. Intros.
  destruct (Hl1 _ _ _ s key ck1 h1 (proj1 (proj2 H3)) H1m) as (Hls & Hlkey & Hlck1 & Hlh1).
  assert (Hlt: Zlength (im_enct M) = 28) by apply H3.
  destruct (hrx5_B4_I_after_ok x25519 R L NS PS KE T head nk H0) as (Hpe & Hsh & Hnone & Hsome).
  destruct (Hsome s a P Hpk) as (NS1 & N & NS2 & P' & sn & Hfm & HNS & HinP & Hnf & HpN & Hrs & Hsn & Hsnhs & HokP & Hlic).
  assert (Hhp: hnodes_peers4 NS PS) by (destruct H0 as (_ & _ & _ & _ & X & _); exact X).
  assert (Hh: hrx5_head (hnodes_snapped4 T NS PS) = hrx5_head NS)
    by (apply hrx5_B4_I_head_snapped; exact Hhp).
  assert (Hnode: hnodes_rep4 W (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS) |--
    (@data_at W_handshake_receive Ews t_hnode4 (hrx5_B4_I_nv N (hrx5_head NS2)) (hn_addr N) *
     (@data_at W_handshake_receive Ews t_hnode4 (hrx5_B4_I_nv N (hrx5_head NS2)) (hn_addr N) -*
      hnodes_rep4 W (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS)))%logic).
  { rewrite HNS. apply hrx5_B4_I_nv_node. }
  destruct (Hl2 _ _ _ _ _ _ _ Hlt H2m) as (Hlt12 & Hlck2 & Hlh2).
  assert (Hts: Zlength (hs_ts (sn_hs sn)) = 12) by (rewrite Hsnhs; apply HokP).
  assert (HinN: In (hn_addr N) (map hn_addr (hnodes_snapped4 T NS PS))).
  { rewrite HNS, map_app. apply in_or_app. right. left. reflexivity. }
  assert_PROP (Forall isptr (map hn_addr (hnodes_snapped4 T NS PS))) as Hptrs.
  { sep_apply (hrx5_B4_I_hn_isptr (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS)). entailer!. }
  assert (HpNa: isptr (hn_addr N)). { rewrite Forall_forall in Hptrs. auto. }
  remember (kdf2 ck1 SS) as K2 eqn:HK2.
  rewrite <- Hnf.
  forward_if. 2: { hrx5_B4_I_absurd. }
  sep_apply Hnode. Intros.
  sep_apply (hrx5_B4_I_ci_ts Tsh ck2 h2 (bytes K2) (bytes s) t (l_ci L) Hlt12).
  sep_apply (hrx5_B4_I_nv_ts Ews N (hrx5_head NS2) (hn_addr N) sn Hsn Hts).
  Intros.
  eapply semax_seq'.
  forward_call (Tsh, offset_val 128 (l_ci L), t, Ews, offset_val 280 (hn_addr N), hs_ts (sn_hs sn)).
  apply ENTAIL_refl.
  unfold MORE_COMMANDS, abbreviate. forward.
  sep_apply (hrx5_B4_I_wand1 (hbytes Tsh t (offset_val 128 (l_ci L)))
    (@data_at HCS Tsh t_mcinit (mcinit_val ck2 h2 (bytes K2) (bytes s) (bytes t)) (l_ci L))).
  sep_apply (hrx5_B4_I_wand1 (hbytes Ews (hs_ts (sn_hs sn)) (offset_val 280 (hn_addr N)))
    (@data_at W_handshake_receive Ews t_hnode4 (hrx5_B4_I_nv N (hrx5_head NS2)) (hn_addr N))).
  sep_apply (hrx5_B4_I_wand1 (@data_at W_handshake_receive Ews t_hnode4 (hrx5_B4_I_nv N (hrx5_head NS2)) (hn_addr N))
    (hnodes_rep4 W (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS))).
  rewrite <- Hnf, Hsnhs.
  destruct (hrx5_RB x25519 gv L FR); cbv beta iota; cbn [tycontext.RA_normal].
  destruct (ts_newer t (hs_ts (p_hs P))); entailer!.
Qed.

End Seg.
