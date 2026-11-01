(* law keypairs: the stages t'26 .. t'30 and the final test of check_all's segment NODE
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

Lemma hkc5n_c26_ok {Espec: OracleKind} F P m M nx n lk bt sx Fr R : hkc5n_facts m M ->
  semax hkc5_Delta (hkc5n_St1 F P m M nx n lk bt sx Fr KC._t'25) hkc5n_c26
    (overridePost (hkc5n_St1 F P m M nx n lk bt sx Fr KC._t'26) R).
Proof.
  hkc5n_start. unfold hkc5n_c26.
  hkc5n_fif KC._t'26.
  hkc5n_ld. hkc5n_ld. forward.
  { entailer!. destruct (m5_init M); reflexivity. }
Qed.

Lemma hkc5n_c27_ok {Espec: OracleKind} F P m M nx n lk bt sx Fr R : hkc5n_facts m M ->
  semax hkc5_Delta (hkc5n_St1 F P m M nx n lk bt sx Fr KC._t'26) hkc5n_c27
    (overridePost (hkc5n_St1 F P m M nx n lk bt sx Fr KC._t'27) R).
Proof.
  hkc5n_start. unfold hkc5n_c27.
  hkc5n_fif KC._t'27.
  hkc5n_ld. hkc5n_ld. forward.
  { entailer!. first [apply hkc5n_cmpu64 | apply hkc5n_cmp32]. }
Qed.

Lemma hkc5n_c28_ok {Espec: OracleKind} F P m M nx n lk bt sx Fr R : hkc5n_facts m M ->
  semax hkc5_Delta (hkc5n_St1 F P m M nx n lk bt sx Fr KC._t'27) hkc5n_c28
    (overridePost (hkc5n_St1 F P m M nx n lk bt sx Fr KC._t'28) R).
Proof.
  hkc5n_start. unfold hkc5n_c28.
  hkc5n_fif KC._t'28.
  hkc5n_ld. hkc5n_ld. forward.
  { entailer!. first [apply hkc5n_cmpu64 | apply hkc5n_cmp32]. }
Qed.

Lemma hkc5n_c29_ok {Espec: OracleKind} F P m M nx n lk bt sx Fr R : hkc5n_facts m M ->
  semax hkc5_Delta (hkc5n_St1 F P m M nx n lk bt sx Fr KC._t'28) hkc5n_c29
    (overridePost (hkc5n_St1 F P m M nx n lk bt sx Fr KC._t'29) R).
Proof.
  hkc5n_start. unfold hkc5n_c29.
  hkc5n_fif KC._t'29.
  hkc5n_ld. hkc5n_ld. forward.
  { entailer!. first [apply hkc5n_cmpu64 | apply hkc5n_cmp32]. }
Qed.

Lemma hkc5n_c30_ok {Espec: OracleKind} F P m M nx n lk bt sx Fr R : hkc5n_facts m M ->
  semax hkc5_Delta (hkc5n_St1 F P m M nx n lk bt sx Fr KC._t'29) hkc5n_c30
    (overridePost (hkc5n_St1 F P m M nx n lk bt sx Fr KC._t'30) R).
Proof.
  hkc5n_start. unfold hkc5n_c30.
  hkc5n_fif KC._t'30.
  hkc5n_ld. hkc5n_ld. forward.
  { entailer!. first [apply hkc5n_cmpu64 | apply hkc5n_cmp32]. }
Qed.

Lemma hkc5n_i30_ok {Espec: OracleKind} F P m M nx n lk bt sx Fr R : hkc5n_facts m M ->
  semax hkc5_Delta (hkc5n_St1 F P m M nx n lk bt sx Fr KC._t'30) hkc5n_i30
    (overridePost (hkc5n_St0 F P m M nx n lk bt sx Fr) R).
Proof.
  hkc5n_start. unfold hkc5n_i30.
  match goal with |- semax _ (PROPx ?P (LOCALx (_ :: ?Q0) (SEPx ?S))) _ _ =>
    forward_if (PROPx P (LOCALx Q0 (SEPx S))) end.
  { exfalso; congruence. }
  { forward. entailer!. }
Qed.
