(* law keypairs: the segment NODE (one live node vs its keypair).
*)
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
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_defs.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_node_st.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_node_c1.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_node_c2.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_node_c3.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_node_h.

#[local] Existing Instance W_keypairs.
Local Open Scope Z_scope.
Local Open Scope logic.

(* kp = k->kp *)
Lemma hkc5n_skp_ok {Espec: OracleKind} F T P m M nx K n FR R :
  semax hkc5_Delta (hkc5_PN F T P m M nx K n FR) hkc5n_skp (overridePost (hkc5n_PK F T P m M nx K n FR) R).
Proof.
  destruct R as [Rn Rb Rc Rr].
  unfold hkc5_PN, hkc5n_PK, hkc5_lv, hkc5n_skp.
  sep_apply (hkc5n_node_open_d M nx m). Intros.
  assert_PROP (isptr (m5_kp M)) as Pk.
  { unfold keypair_rep. entailer!.
    match goal with Hf: field_compatible t_kp [] (m5_kp M) |- _ => destruct Hf as [Hp _]; exact Hp end. }
  forward.
  sep_apply (hkc5n_node_close M nx m H H0).
  entailer!.
Qed.

(* the || chain and its final test, on the opened state *)
Lemma hkc5n_X_ok {Espec: OracleKind} F P m M nx n lk bt sx Fr R : hkc5n_facts m M ->
  semax hkc5_Delta (hkc5n_St0 F P m M nx n lk bt sx Fr) (Ssequence hkc5n_X hkc5n_i30)
    (overridePost (hkc5n_St0 F P m M nx n lk bt sx Fr) R).
Proof.
  intros HF. rewrite hkc5n_X_eq.
  eapply semax_seq; [| apply hkc5n_i30_ok; exact HF].
  eapply semax_seq; [| apply hkc5n_c30_ok; exact HF].
  eapply semax_seq; [| apply hkc5n_c29_ok; exact HF].
  eapply semax_seq; [| apply hkc5n_c28_ok; exact HF].
  eapply semax_seq; [| apply hkc5n_c27_ok; exact HF].
  eapply semax_seq; [| apply hkc5n_c26_ok; exact HF].
  eapply semax_seq; [| apply hkc5n_c25_ok; exact HF].
  eapply semax_seq; [| apply hkc5n_c24_ok; exact HF].
  eapply semax_seq; [| apply hkc5n_c23_ok; exact HF].
  eapply semax_seq; [| apply hkc5n_c22_ok; exact HF].
  eapply semax_seq; [| apply hkc5n_c20_ok; exact HF].
  eapply semax_seq; [| apply hkc5n_c18_ok; exact HF].
  eapply semax_seq; [| apply hkc5n_c17_ok; exact HF].
  eapply semax_seq; [| apply hkc5n_c16_ok; exact HF].
  eapply semax_seq; [| apply hkc5n_c15_ok; exact HF].
  apply hkc5n_c14_ok; exact HF.
Qed.

(* the closed state with temp kp is the opened one *)
Definition hkc5n_Fr (F: hkp5_fix) (T: tstate) (m: val) (M: hk5_mk) (K: keypair) (FR: mpred) : mpred :=
  @malloc_token W_keypairs Ews t_mk5 m * hkc5n_kp_rest (m5_kp M) K * hkc5n_itab_rest Tsh (f_t F) T (m5_kp M) * FR.

Lemma hkc5n_mid_ok {Espec: OracleKind} F T P m M nx K n FR R :
  hk5_match (f_p F) T M K ->
  semax hkc5_Delta (hkc5n_PK F T P m M nx K n FR) (Ssequence hkc5n_X hkc5n_i30)
    (overridePost (hkc5n_PK F T P m M nx K n FR) R).
Proof.
  intros HM. pose proof HM as (Hrefs & Hsf & Hvin & Hsend & Hrecv & Hinit & Hri & Hid & Hsc & Hrc).
  unfold hkc5n_PK, hkc5_lv.
  sep_apply (hkc5n_node_open_d M nx m). Intros. rename H into Ls. rename H0 into Lr.
  sep_apply (hkc5n_kp_open_d (m5_kp M) K). Intros lk. rename H into FCk. rename H0 into Kok.
  sep_apply (hkc5n_itab_open_d Tsh (f_t F) T (m5_kp M) _ FCk Hsf). Intros. rename H into Wt.
  assert_PROP (isptr m) as Pm by entailer!.
  assert (Pk: isptr (m5_kp M)) by (destruct FCk; auto).
  assert (HF: hkc5n_facts m M) by (unfold hkc5n_facts; auto).
  eapply semax_pre;
    [| eapply semax_post;
       [| | | | apply (hkc5n_X_ok F P m M nx n lk (kp_backtrack K) (succ_in (t_L T) (m5_kp M))
                   (hkc5n_Fr F T m M K FR) R HF)]].
  - unfold hkc5n_St0, hkc5n_sep, hkc5n_base, hkc5n_Fr, hkc5n_kp_fields, hkc5_lv.
    rewrite Hsend, Hrecv, Hinit, Hri, Hid, Hrefs, Hsc, Hrc, Hvin.
    entailer!.
  - destruct R as [Rn Rb Rc Rr]; cbn [overridePost RA_normal].
    unfold hkc5n_St0, hkc5n_sep, hkc5n_base, hkc5n_Fr, hkc5_lv.
    Intros.
    sep_apply (hkc5n_itab_close Tsh (f_t F) T (m5_kp M) _ (m5_hashed M) FCk Hsf Wt Hvin).
    sep_apply (hkc5n_node_close M nx m Ls Lr).
    assert (KC: hkc5n_kp_fields (m5_kp M) K lk * hkc5n_kp_rest (m5_kp M) K |-- keypair_rep W_keypairs (m5_kp M) K)
      by (apply hkc5n_kp_close; auto).
    unfold hkc5n_kp_fields in KC. rewrite Hsend, Hrecv, Hinit, Hri, Hid, Hrefs, Hsc, Hrc in KC.
    sep_apply KC.
    entailer!.
  - destruct R as [Rn Rb Rc Rr]; cbn [overridePost RA_break]. apply andp_left2. apply derives_refl.
  - destruct R as [Rn Rb Rc Rr]; cbn [overridePost RA_continue]. apply andp_left2. apply derives_refl.
  - intros vl. destruct R as [Rn Rb Rc Rr]; cbn [overridePost RA_return]. apply andp_left2. apply derives_refl.
Qed.

Lemma hkc5_node_ok : hkc5_node_stmt.
Proof.
  intros Espec F T P m M nx K n FR R HM Hcnt.
  rewrite hkc5n_node_eq_stmt.
  eapply semax_seq; [apply hkc5n_skp_ok |].
  eapply semax_seq; [apply (hkc5n_mid_ok F T P m M nx K n FR); exact HM |].
  apply hkc5n_h_ok; assumption.
Qed.
