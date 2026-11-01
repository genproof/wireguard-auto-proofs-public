(* law keypairs: the hashed part of check_all's segment NODE
   (the cut: hkp5_check_body_node_st.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_node_st.

#[local] Existing Instance W_keypairs.
Local Open Scope Z_scope.
Local Open Scope logic.

(* the node closed, the keypair closed, temp kp *)
Definition hkc5n_PK (F: hkp5_fix) (T: tstate) (P: peer) (m: val) (M: hk5_mk) (nx: val) (K: keypair) (n: Z)
  (FR: mpred) : environ -> mpred :=
  PROPx []
  (LOCALx (temp KC._kp (m5_kp M) :: temp KC._k m :: hkc5_lv F n)
  (SEPx [hk5_node m M nx; keypair_rep W_keypairs (m5_kp M) K; itable Tsh (f_t F) T; peer_rep Tsh (f_p F) P; FR])).

Lemma hkc5n_h_ok {Espec: OracleKind} F T P m M nx K n FR R :
  hk5_match (f_p F) T M K ->
  (m5_hashed M = true -> count_index T (m5_index M) = 1) ->
  semax hkc5_Delta (hkc5n_PK F T P m M nx K n FR) (Ssequence hkc5n_s56 hkc5n_ifh)
    (overridePost (hkc5_PN F T P m M nx K (n + if m5_hashed M then 1 else 0) FR) R).
Proof.
  intros HM Hcnt.
  destruct HM as (Hrefs & Hsf & Hvin & _).
  destruct R as [Rn Rb Rc Rr].
  unfold hkc5n_PK, hkc5_PN, hkc5_lv, hkc5n_s56, hkc5n_ifh.
  sep_apply (hkc5n_node_open_d M nx m). Intros. rename H into Ls. rename H0 into Lr.
  assert_PROP (isptr (m5_kp M)) as Pk.
  { unfold keypair_rep. entailer!. match goal with Hf: field_compatible t_kp [] (m5_kp M) |- _ => destruct Hf as [Hp _]; exact Hp end. }
  forward. { entailer!. apply hkc5n_tc_bool. }
  forward_if.
  - assert (Eh: m5_hashed M = true) by (revert H; destruct (m5_hashed M); intro H; [reflexivity | inv H]).
    forward_call (Tsh, f_t F, T, m5_kp M).
    { exact (hkc5n_sfind_in _ _ _ _ Hsf). }
    rewrite Hvin, Eh.
    match goal with |- semax _ (PROPx ?P (LOCALx (_ :: _ :: ?Q0) (SEPx ?S))) _ _ =>
      forward_if (PROPx P (LOCALx (temp KC._t'32 (Vint Int.zero) :: Q0) (SEPx S))) end.
    { exfalso; apply Int.one_not_zero; assumption. }
    + forward.
      forward_call (Tsh, f_t F, T, m5_index M).
      { rewrite Hcnt by exact Eh. lia. }
      forward.
      { entailer!. rewrite (Hcnt Eh). reflexivity. }
    + match goal with |- semax _ (PROPx ?P (LOCALx (_ :: ?Q0) (SEPx ?S))) _ _ =>
        forward_if (PROPx P (LOCALx Q0 (SEPx S))) end.
      { exfalso; congruence. }
      { forward. entailer!. }
      forward.
      sep_apply (hkc5n_node_close M nx m Ls Lr).
      rewrite Eh.
      entailer!.
  - assert (Eh: m5_hashed M = false) by (revert H; destruct (m5_hashed M); intro H; [inv H | reflexivity]).
    forward.
    sep_apply (hkc5n_node_close M nx m Ls Lr).
    rewrite Eh, Z.add_0_r.
    entailer!.
Qed.
