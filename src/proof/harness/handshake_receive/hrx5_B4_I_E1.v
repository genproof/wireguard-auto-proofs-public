(* law handshake_receive, phase B4, segment I, part E1:
   e1 = `t'358 = target->p; m_precomputed(sst, &id, t'358->handshake.remote_static)` (port of hci5_p7_E1).
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

Lemma hrx5_B4_I_E1_ok {Espec: OracleKind} gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s key ck1 h1 a P :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hrx5_B4_I_c1f x25519 aead_dec (hrx5_ID x25519 R) M = Some (s, key, ck1, h1) ->
  pk_find PS s = Some (a, P) ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B4_I_Qf x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s key ck1 h1 a) hrx5_B4_I_e1
    (overridePost (hrx5_B4_I_Q5 x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img s key ck1 h1 a P) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HH Hc1f Hpk.
  destruct (hrx5_B4_I_c1f_some x25519 aead_dec _ _ _ _ _ _ Hc1f) as [Hfwd Hc1].
  destruct (hrx5_B4_I_c1_some x25519 aead_dec _ _ _ _ _ _ Hc1) as [Hok H1m].
  destruct HH as (Hx & Ha & Hxa).
  destruct (hrx5_B4_I_len_ok x25519 aead_enc aead_dec Hx Ha) as (HlID & Hl1 & Hlpre & Hl2).
  unfold hrx5_B4_I_Qf, hrx5_B4_I_Q5, hrx5_B4_I_SS, hrx5_B4_I_st, hrx5_B4_I_ci1, hrx5_B4_I_scr, hrx5_Delta, hrx5_RB,
    hrx5_B4_I_e1, hrx5_ltemps, hrx5_ptrs, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs.
  cbn [app obj_bytes obj_kind obj_rep obj_ok]. simplify_func_tycontext. abbreviate_semax. Intros.
  destruct (HlID R (proj1 H)) as [HIDpriv HIDpub].
  destruct (hrx5_B4_I_after_ok x25519 R L NS PS KE T head nk H0) as (Hpe & Hsh & Hnone & Hsome).
  destruct (Hsome s a P Hpk) as (NS1 & N & NS2 & P' & sn & Hfm & HNS & HinP & Hnf & Hrest).
  destruct Hrest as (HpN & Hrs & Hsn & Hsnhs & HokP & Hlic).
  assert (Hnode: hnodes_rep4 W (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS) |--
    (@data_at W Ews t_hnode4 (hrx5_B4_I_nv N (hrx5_head NS2)) (hn_addr N) *
     (@data_at W Ews t_hnode4 (hrx5_B4_I_nv N (hrx5_head NS2)) (hn_addr N) -*
      hnodes_rep4 W (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS)))%logic).
  { rewrite HNS. apply hrx5_B4_I_nv_node. }
  assert (HrsP: Zlength (hs_rstatic (p_hs P)) = 32) by apply HokP.
  rewrite <- Hnf.
  assert_PROP (isptr a) as Hpa.
  { sep_apply (hrx5_B4_I_peers_hsok _ a Ews P' HinP). entailer!. }
  sep_apply Hnode. Intros.
  forward.
  match goal with |- context [temp hrx5_cut.HRM._t'358 ?v] =>
    replace v with a by (unfold hrx5_B4_I_nv; cbv beta iota; symmetry; exact HpN) end.
  sep_apply (hrx5_B4_I_peer_rs _ a Ews P' HinP). Intros.
  rewrite Hrs.
  forward_call (Tsh, l_sst L, Tsh, l_id L, hrx5_ID x25519 R, Ews, offset_val 136 a, hs_rstatic (p_hs P)).
  sep_apply (hrx5_B4_I_wand1 (hbytes Ews (hs_rstatic (p_hs P)) (offset_val 136 a)) (peers_rep PS)).
  sep_apply (hrx5_B4_I_wand1 (@data_at W Ews t_hnode4 (hrx5_B4_I_nv N (hrx5_head NS2)) (hn_addr N))
    (hnodes_rep4 W (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS))).
  rewrite <- Hnf. destruct (hrx5_R gv). unfold loop1_ret_assert. cbv iota beta. cbn [tycontext.RA_normal]. entailer!.
Qed.

End Seg.
