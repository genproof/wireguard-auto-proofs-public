(* law handshake, phase P5, segment D, part cc: POS c_fin (eph / ts / lic == snap's, table_has(&ita, entry), entry index == snap's).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.handshake.hhs3_spec.
Require Import WgNoise.proof.harness.handshake.hhs3_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_conv.
Require Import WgNoise.proof.harness.handshake.hhs3_p5_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_p5_D_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_p5_D_ca_view.
Require Import WgNoise.proof.harness.handshake.hhs3_p5_D_cc_view.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Lemma hhs3_p5_D_cc_vin L I : vin (hs_addr (l_pb L)) (t_L (hhs3_TA1 L I)) = true.
Proof.
  rewrite hhs3_p5_D_cc_view_TA1. unfold vin. cbn [t_L].
  destruct (in_dec eq_dec (hs_addr (l_pb L)) [hs_addr (l_pb L)]) as [_|N]; [reflexivity | exfalso; apply N; left; auto].
Qed.

Lemma hhs3_p5_D_cc_in L I : In (hs_addr (l_pb L)) (saddrs (t_D (hhs3_TA1 L I))).
Proof. rewrite hhs3_p5_D_cc_view_TA1. left. reflexivity. Qed.

Ltac hhs3_p5_D_cc_ptr p q :=
  repeat match goal with Hx: @field_compatible _ _ [] p |- _ => let I := fresh in pose proof (field_compatible_isptr _ _ _ Hx) as I; revert I; clear Hx end;
  repeat match goal with Hx: @field_compatible _ _ [] q |- _ => let I := fresh in pose proof (field_compatible_isptr _ _ _ Hx) as I; revert I; clear Hx end;
  intros; destruct p; try contradiction; destruct q; try contradiction;
  simpl; rewrite ?Ptrofs.add_assoc, ?Ptrofs.add_zero; reflexivity.

Section Part.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p5_D_cc_ok {Espec: OracleKind} gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb PA1 CI1 CI2 Q M2 H2 MR nowa ST2 (Rp: ret_assert) :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hhs3_p5_D_Q x25519 aead_enc aead_dec gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb PA1 CI1 CI2 Q M2 H2 MR nowa ST2)
    (hhs3_p5_D_cfin)
    (overridePost (hhs3_p5_D_Q x25519 aead_enc aead_dec gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb PA1 CI1 CI2 Q M2 H2 MR nowa ST2) Rp).
Proof.
  intros HH. destruct Rp as [Rn Rb Rc Rr]. unfold overridePost.
  unfold hhs3_p5_D_Q, hhs3_p5_D_st, hhs3_Delta, hhs3_p5_D_cfin.
  simplify_func_tycontext.
  destruct (hhs3_p5_D_cc_view_new x25519 R L I M1 H1 M2 ST2) as (Ee & Et & El & Ei).
  set (P := p_set_refs (hhs3_p5_new x25519 R L M1 H1 M2 ST2) Int.one) in *.
  unfold hhs3_p5_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
  set (sn := hhs3_p5_snap x25519 R L I M1 H1) in *.
  abbreviate_semax.
  Intros.
  rewrite (hhs3_p5_D_cc_view_eq Tsh (l_pb L) P). Intros.
  match goal with Hx: @field_compatible Noise.CS t_peer [] (l_pb L) |- _ => rename Hx into Hfc end.
  match goal with Hx: hs_ok (p_hs P) |- _ => pose proof Hx as (Le & _ & _ & _ & _ & _ & _ & Lt) end.
  rewrite Ee in Le. rewrite Et in Lt.
  assert_PROP (@field_compatible HCS t_hsnap [] (l_snap L)) as FCs.
  { entailer!. }
  rewrite (hhs3_p5_D_cc_view_snap Tsh (l_snap L) sn FCs Le Lt).
  unfold hhs3_p5_D_cc_view. rewrite Ee, Et, El, Ei.
  Intros.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  + apply ENTAIL_refl.
  + forward_call (Tsh, offset_val 104 (l_pb L), hs_eph (sn_hs sn), Tsh, offset_val 48 (l_snap L), hs_eph (sn_hs sn)).
    { entailer!. rewrite Le. hhs3_p5_D_cc_ptr (l_pb L) (l_snap L). }
    rewrite hhs3_p5_D_ca_view_eqb_refl.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HC._t'147 (Vint Int.one) :: Q) (SEPx R))) end.
    { forward_call (Tsh, offset_val 328 (l_pb L), hs_ts (sn_hs sn), Tsh, offset_val 272 (l_snap L), hs_ts (sn_hs sn)).
      { entailer!. rewrite Lt. hhs3_p5_D_cc_ptr (l_pb L) (l_snap L). }
      rewrite hhs3_p5_D_ca_view_eqb_refl. forward. entailer!. }
    { exfalso. match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HC._t'149 (Vint Int.one) :: Q) (SEPx R))) end.
    { forward. forward. forward. entailer!. rewrite Int64.eq_true. reflexivity. }
    { exfalso. match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HC._t'150 (Vint Int.one) :: Q) (SEPx R))) end.
    { forward_call (Tsh, l_ita L, hhs3_TA1 L I, hs_addr (l_pb L)).
      { apply hhs3_p5_D_cc_in. }
      rewrite hhs3_p5_D_cc_vin. forward. entailer!. }
    { exfalso. match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HC._t'152 (Vint Int.one) :: Q) (SEPx R))) end.
    { rewrite (hhs3_p5_D_cc_view_open1 L I Hfc). Intros.
      forward. forward. forward. entailer!.
      all: try (rewrite Int.eq_true; reflexivity).
      all: rewrite (hhs3_p5_D_cc_view_open1 L I Hfc); cancel. }
    { exfalso. match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
    forward_if.
    { forward_call tt. all: [> exfalso; match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end | entailer!]. }
    forward. entailer!.
  + forward. apply ENTAIL_refl.
  + unfold POSTCONDITION, abbreviate. simpl RA_normal. entailer!.
    rewrite (hhs3_p5_D_cc_view_eq Tsh (l_pb L) P), (hhs3_p5_D_cc_view_snap Tsh (l_snap L) sn FCs Le Lt).
    unfold hhs3_p5_D_cc_view, hhs3_p5_st2. rewrite Ee, Et, El, Ei. entailer!.
Qed.

End Part.
