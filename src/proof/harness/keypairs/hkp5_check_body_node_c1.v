(* law keypairs: the stages t'14 .. t'20 of check_all's segment NODE
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

Ltac hkc5n_ld := forward; try (entailer!; apply hkc5n_tc_bool).

Ltac hkc5n_start :=
  intros [Pm [Pk [Ls Lr]]]; match goal with R: ret_assert |- _ => destruct R as [Rn Rb Rc Rr] end;
  unfold hkc5n_St0, hkc5n_St1, hkc5n_sep, hkc5n_base, hkc5_lv.

Ltac hkc5n_fif tN :=
  match goal with |- semax _ (PROPx ?P (LOCALx (_ :: ?Q0) (SEPx ?S))) _ _ =>
    forward_if (PROPx P (LOCALx (temp tN (Vint Int.zero) :: Q0) (SEPx S))) end;
  [ exfalso; congruence | ].

Lemma hkc5n_c14_ok {Espec: OracleKind} F P m M nx n lk bt sx Fr R : hkc5n_facts m M ->
  semax hkc5_Delta (hkc5n_St0 F P m M nx n lk bt sx Fr) hkc5n_c14
    (overridePost (hkc5n_St1 F P m M nx n lk bt sx Fr KC._t'14) R).
Proof.
  hkc5n_start. unfold hkc5n_c14.
  forward. forward.
  match goal with |- semax _ (PROPx ?P (LOCALx (_ :: _ :: ?Q0) (SEPx ?S))) _ _ =>
    forward_if (PROPx P (LOCALx (temp KC._t'14 (Vint Int.zero) :: Q0) (SEPx S))) end.
  { contradiction. }
  - forward. { entailer!. apply hkc5n_tc_bool. }
    forward.
    forward.
    { entailer!. destruct (m5_hashed M); reflexivity. }
Qed.

Lemma hkc5n_c15_ok {Espec: OracleKind} F P m M nx n lk bt sx Fr R : hkc5n_facts m M ->
  semax hkc5_Delta (hkc5n_St1 F P m M nx n lk bt sx Fr KC._t'14) hkc5n_c15
    (overridePost (hkc5n_St1 F P m M nx n lk bt sx Fr KC._t'15) R).
Proof.
  hkc5n_start. unfold hkc5n_c15.
  hkc5n_fif KC._t'15.
  - forward. forward. forward.
    { entailer!. cbn [e_index]. rewrite Int.eq_true. reflexivity. }
Qed.

Lemma hkc5n_c16_ok {Espec: OracleKind} F P m M nx n lk bt sx Fr R : hkc5n_facts m M ->
  semax hkc5_Delta (hkc5n_St1 F P m M nx n lk bt sx Fr KC._t'15) hkc5n_c16
    (overridePost (hkc5n_St1 F P m M nx n lk bt sx Fr KC._t'16) R).
Proof.
  hkc5n_start. unfold hkc5n_c16.
  hkc5n_fif KC._t'16.
  forward. forward.
  { entailer!. }
Qed.

Lemma hkc5n_c17_ok {Espec: OracleKind} F P m M nx n lk bt sx Fr R : hkc5n_facts m M ->
  semax hkc5_Delta (hkc5n_St1 F P m M nx n lk bt sx Fr KC._t'16) hkc5n_c17
    (overridePost (hkc5n_St1 F P m M nx n lk bt sx Fr KC._t'17) R).
Proof.
  hkc5n_start. unfold hkc5n_c17.
  assert_PROP (isptr (f_p F)) as Pp by (sep_apply (hkc5n_peer_ptr Tsh (f_p F) P); entailer!).
  hkc5n_fif KC._t'17.
  forward. forward.
  { entailer!. apply denote_tc_test_eq_split; apply sepcon_valid_pointer1; apply sepcon_valid_pointer2;
    apply hkc5n_peer_valid; auto. }
  { entailer!. first [apply hkc5n_cmp_self; auto | rewrite if_true by auto; reflexivity]. }
Qed.

Ltac hkc5n_args L :=
  apply prop_right; rewrite L;
  let b := fresh "b" in let i := fresh "i" in let Ek := fresh "Ek" in
  destruct (m5_kp _) as [| | | | | b i] eqn:Ek; try (exfalso; assumption);
  match goal with Pm: isptr ?m |- _ => destruct m; try contradiction end;
  simpl; rewrite ?Ek; simpl; rewrite ?Ptrofs.add_zero; reflexivity.

Lemma hkc5n_c18_ok {Espec: OracleKind} F P m M nx n lk bt sx Fr R : hkc5n_facts m M ->
  semax hkc5_Delta (hkc5n_St1 F P m M nx n lk bt sx Fr KC._t'17) hkc5n_c18
    (overridePost (hkc5n_St1 F P m M nx n lk bt sx Fr KC._t'18) R).
Proof.
  hkc5n_start. unfold hkc5n_c18.
  hkc5n_fif KC._t'18.
  sep_apply (hkc5n_focus_kp_send (mkSym (m5_send M) (m5_birth M) (m5_sv M)) (m5_kp M) Ls).
  sep_apply (hkc5n_focus_node_send M nx m Ls).
  change (sk_key (mkSym (m5_send M) (m5_birth M) (m5_sv M))) with (m5_send M).
  flatten_sepcon_in_SEP.
  forward_call (Ews, offset_val 32 (m5_kp M), m5_send M, Ews, offset_val 32 m, m5_send M).
  { hkc5n_args Ls. }
  forward.
  sep_apply (wand_frame_elim (hbytes Ews (m5_send M) (offset_val 32 m)) (@data_at W_keypairs Ews t_mk5 (hk5_mk_val M nx) m)).
  sep_apply (wand_frame_elim (hbytes Ews (m5_send M) (offset_val 32 (m5_kp M)))
    (@field_at W_keypairs Ews t_kp (DOT KC._sending) (symkey_val (mkSym (m5_send M) (m5_birth M) (m5_sv M))) (m5_kp M))).
  entailer!. rewrite hkc5n_bytes_eqb_refl. reflexivity.
Qed.
