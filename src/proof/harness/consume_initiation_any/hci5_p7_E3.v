(* law consume_initiation_any, phase P7, segment E3: if (t'24) t'26 = (bool) m_not_flood(p->snap.last_initiation_consumption, now) else t'26 = 0.  Port of v1's hci3_p7_E3.v. *)
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

Lemma hci5_p7_E3_ok {Espec: OracleKind} gv L FR R S w NS PS T head na KE m M s key ck1 h1 a P :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hci5_p7_c1 x25519 aead_dec (hci5_IB x25519 R) M = Some (s, key, ck1, h1) ->
  pk_find PS s = Some (a, P) ->
  semax (hci5_Delta x25519 aead_enc aead_dec)
    (hci5_p7_Q7 x25519 aead_dec gv L FR R S w NS PS T head na KE m M s ck1 h1 a P) hci5_p7_if15
    (overridePost (hci5_p7_Q8 x25519 aead_dec gv L FR R S w NS PS T head na KE m M s ck1 h1 a P) (hci5_R gv)).
Proof.
  intros HH Hc1 Hpk.
  destruct (hci5_p7_c1_some x25519 aead_dec _ _ _ _ _ _ Hc1) as [Hok H1m].
  destruct HH as (Hx & Ha & Hxa & Hrep).
  destruct (hci5_p7_len_ok x25519 aead_enc aead_dec Hx Ha) as (HlIB & Hl1 & Hlpre & Hl2).
  unfold hci5_p7_Q7, hci5_p7_Q8, hci5_p7_st, hci5_p7_ci2, hci5_p7_c2v, hci5_p7_b15, hci5_Delta, hci5_R,
    hci5_p7_if15, hci5_lvars, hci5_world, hci5_globs.
  cbv zeta. cbn [app].
  set (SS := hci5_p7_SS x25519 (hci5_IB x25519 R) P).
  destruct (m_consume_init2_model aead_dec SS ck1 h1 (im_enct M)) as [[[t ck2] h2]|] eqn:H2m;
    cbv beta iota.
  2: {
    simplify_func_tycontext. abbreviate_semax. Intros.
    forward_if. 1: { hci5_p7_absurd. }
    forward. entailer!. }
  destruct (ts_newer t (hs_ts (p_hs P))) eqn:Htn;
    cbv beta iota.
  2: {
    simplify_func_tycontext. abbreviate_semax. Intros.
    forward_if. 1: { hci5_p7_absurd. }
    forward. entailer!. }
  simplify_func_tycontext. abbreviate_semax. Intros.
  destruct (HlIB R H) as [HIBpriv HIBpub].
  destruct (Hl1 _ _ _ s key ck1 h1 (proj1 (proj2 H1)) H1m) as (Hls & Hlkey & Hlck1 & Hlh1).
  assert (Hlt: Zlength (im_enct M) = 28) by apply H1.
  assert_PROP (itable_wf T) as Hwf. { unfold itable. entailer!. }
  pose proof (hci5_p7_pure_nodup PS KE T Hwf (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 H0))))))) as Hnd.
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
  assert (HinN: In (hn_addr N) (map hn_addr (hnodes_snapped4 T NS PS))).
  { rewrite HNS, map_app. apply in_or_app. right. left. reflexivity. }
  assert_PROP (Forall isptr (map hn_addr (hnodes_snapped4 T NS PS))) as Hptrs.
  { sep_apply (hci5_p7_hn_isptr (hci5_head NS) (hnodes_snapped4 T NS PS)). entailer!. }
  assert (HpNa: isptr (hn_addr N)). { rewrite Forall_forall in Hptrs. auto. }
  remember (kdf2 ck1 SS) as K2 eqn:HK2.
  rewrite <- Hnf, <- Hh.
  forward_if. 2: { hci5_p7_absurd. }
  sep_apply Hnode. Intros.
  rewrite (hci5_p7_nv_nvs Ews N (hci5_head NS2) (hn_addr N) sn Hsn).
  forward.
  eapply semax_seq'.
  forward_call (hs_lic (sn_hs sn), s_boot S).
  1: { rewrite Hsnhs, Int64.signed_eq_unsigned; rep_lia. }
  apply ENTAIL_refl.
  unfold MORE_COMMANDS, abbreviate. forward.
  rewrite <- (hci5_p7_nv_nvs Ews N (hci5_head NS2) (hn_addr N) sn Hsn).
  sep_apply (hci5_p7_wand1 (@data_at W Ews t_hnode4 (hci5_p7_nv N (hci5_head NS2)) (hn_addr N))
    (hnodes_rep4 W (hci5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS))).
  rewrite Hh, <- Hnf, Hsnhs.
  destruct (not_flood (hs_lic (p_hs P)) (s_boot S)); entailer!.
Qed.

End Seg.
