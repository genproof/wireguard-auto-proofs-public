(* law consume_initiation_any, phase P7, segment E1: t'94 = p->p; m_precomputed(ss__2, &ib, t'94->handshake.remote_static).  Port of v1's hci3_p7_E1.v. *)
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

Lemma hci5_p7_E1_ok {Espec: OracleKind} gv L FR R S w NS PS T head na KE m M s key ck1 h1 a P :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hci5_p7_c1 x25519 aead_dec (hci5_IB x25519 R) M = Some (s, key, ck1, h1) ->
  pk_find PS s = Some (a, P) ->
  semax (hci5_Delta x25519 aead_enc aead_dec)
    (hci5_p7_Qf x25519 aead_dec gv L FR R S w NS PS T head na KE m M s key ck1 h1 a) hci5_p7_e1
    (overridePost (hci5_p7_Q5 x25519 aead_dec gv L FR R S w NS PS T head na KE m M s key ck1 h1 a P) (hci5_R gv)).
Proof.
  intros HH Hc1 Hpk.
  destruct (hci5_p7_c1_some x25519 aead_dec _ _ _ _ _ _ Hc1) as [Hok H1m].
  destruct HH as (Hx & Ha & Hxa & Hrep).
  destruct (hci5_p7_len_ok x25519 aead_enc aead_dec Hx Ha) as (HlIB & Hl1 & Hlpre & Hl2).
  unfold hci5_p7_Qf, hci5_p7_Q5, hci5_p7_SS, hci5_p7_st, hci5_p7_ci1, hci5_Delta, hci5_R, hci5_p7_e1,
    hci5_lvars, hci5_world, hci5_globs.
  cbn [app]. simplify_func_tycontext. abbreviate_semax. Intros.
  destruct (HlIB R H) as [HIBpriv HIBpub].
  destruct (Hl1 _ _ _ s key ck1 h1 (proj1 (proj2 H1)) H1m) as (Hls & Hlkey & Hlck1 & Hlh1).
  assert (Hlt: Zlength (im_enct M) = 28) by apply H1.
  assert_PROP (itable_wf T) as Hwf. { unfold itable. entailer!. }
  assert (Hnd: NoDup (map peer_addr4 PS)) by (apply (hci5_p7_pure_nodup PS KE T Hwf); apply H0).
  destruct (hci5_p7_after_ok x25519 aead_dec R L NS PS KE T head na (hci5_DB x25519 R L) M S H0 Hnd)
    as (Hpe & Hsh & Hnone & Hsome).
  destruct (Hsome s a P Hpk) as (NS1 & N & NS2 & P' & sn & Hfm & HNS & HinP & Hnf & HpN & Hrs & Hsn & Hsnhs & HokP & Hlic).
  assert (Hhp: hnodes_peers4 NS PS) by apply H0.
  assert (Hh: hci5_head (hnodes_snapped4 T NS PS) = hci5_head NS)
    by (apply hci5_p7_head_snapped; exact Hhp).
  assert (Hnode: hnodes_rep4 W (hci5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS) |--
    (@data_at W Ews t_hnode4 (hci5_p7_nv N (hci5_head NS2)) (hn_addr N) *
     (@data_at W Ews t_hnode4 (hci5_p7_nv N (hci5_head NS2)) (hn_addr N) -*
      hnodes_rep4 W (hci5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS)))%logic).
  { rewrite HNS. apply hci5_p7_nv_node. }
  assert (HrsP: Zlength (hs_rstatic (p_hs P)) = 32) by apply HokP.
  rewrite <- Hnf, <- Hh.
  assert_PROP (hs_ok (p_hs P') /\ isptr a) as HokPa.
  { sep_apply (hci5_p7_peers_hsok _ a Ews P' HinP). entailer!. }
  destruct HokPa as [HokP' Hpa].
  sep_apply Hnode. Intros.
  forward.
  match goal with |- context [temp HC._t'94 ?v] => replace v with a by (unfold hci5_p7_nv; cbv beta iota; symmetry; exact HpN) end.
  sep_apply (hci5_p7_peer_rs _ a Ews P' HinP). Intros.
  rewrite Hrs.
  forward_call (Tsh, l_ss2 L, Tsh, l_ib L, hci5_IB x25519 R, Ews, offset_val 136 a, hs_rstatic (p_hs P)).
  sep_apply (hci5_p7_wand1 (hbytes Ews (hs_rstatic (p_hs P)) (offset_val 136 a))
    (peers_rep (peers_after PS (cin_res x25519 aead_dec (hci5_DB x25519 R L) PS M S)))).
  sep_apply (hci5_p7_wand1 (@data_at W Ews t_hnode4 (hci5_p7_nv N (hci5_head NS2)) (hn_addr N))
    (hnodes_rep4 W (hci5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS))).
  rewrite Hh, <- Hnf. entailer!.
Qed.

End Seg.
