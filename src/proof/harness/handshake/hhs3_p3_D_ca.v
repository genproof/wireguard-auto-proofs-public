(* law handshake, phase P3, segment D, part: POS c_state, c_reph, c_ts.
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
Require Import WgNoise.proof.harness.handshake.hhs3_p3_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_p3_D_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_p3_D_ca_view.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Ltac hhs3_p3_D_ca_dead :=
  match goal with Hc: _ = Int.zero |- _ =>
    rewrite ?Int.eq_true in Hc; exfalso; exact (Int.one_not_zero Hc) end.

Section Part.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p3_D_ca_ok {Espec: OracleKind} gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb CI1 CI2 (Rp: ret_assert) :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hhs3_p3_D_Q x25519 aead_enc aead_dec gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb CI1 CI2)
    (Ssequence hhs3_p3_D_cstate (Ssequence hhs3_p3_D_creph hhs3_p3_D_cts))
    (overridePost (hhs3_p3_D_Q x25519 aead_enc aead_dec gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb CI1 CI2) Rp).
Proof.
  intros HH. destruct Rp as [Rn Rb Rc Rr]. unfold overridePost.
  unfold hhs3_p3_D_Q, hhs3_p3_D_st, hhs3_Delta, hhs3_p3_D_cstate, hhs3_p3_D_creph, hhs3_p3_D_cts.
  simplify_func_tycontext.
  destruct CI2 as [[t ck] h]. destruct CI1 as [[[s key] ck1] h1].
  destruct (hhs3_p3_D_ca_view_new x25519 R L M1 nowb t ck h) as (Es & Er & Et).
  set (P := hhs3_PA2 (hhs3_p3_new x25519 R L M1 nowb (t, ck, h))) in *.
  unfold hhs3_p3_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps, hhs3_p3_civ; cbn [app].
  abbreviate_semax.
  Intros.
  rewrite (hhs3_p3_D_ca_view_eq Tsh (l_pa L) P). Intros.
  rewrite (hhs3_p3_D_ca_view_init Ews m1 _). Intros.
  rename H11 into Hok, H12 into IMok, H13 into IMfc, H10 into Hfc.
  cbn [fst] in H9. clearbody P. revert Et. subst t. intros Et.
  pose proof Hok as (_ & _ & Lr & _ & _ & _ & _ & Lt). rewrite Er in Lr. rewrite Et in Lt.
  assert_PROP (@field_compatible HCS t_mcinit [] (l_ci L)) as CIfc by entailer!.
  rewrite (hhs3_p3_D_ca_view_ci Tsh (l_ci L) ck h _ _ _ CIfc Lt).
  unfold hhs3_p3_D_ca_view. rewrite Es, Er, Et, hhs3_p3_D_ca_view_M1eph. Intros.
  (* hide the BLAKE2s term (forward_call diverges on it) *)
  remember (kdf2 ck1 (hhs3_ssb x25519 R)) as KK eqn:EKK.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  + apply ENTAIL_refl.
  + forward. forward_if.
    { hhs3_p3_D_ca_dead. }
    forward. entailer!.
  + forward. apply ENTAIL_refl.
  + match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
    * apply ENTAIL_refl.
    * forward_call (Tsh, offset_val 168 (l_pa L), im_eph M1, Ews, offset_val 8 m1, im_eph M1).
      all: try (exact (field_compatible_isptr _ _ _ IMfc)).
      { apply prop_right. rewrite Lr. pose proof (field_compatible_isptr _ _ _ IMfc) as Im1.
        pose proof (field_compatible_isptr _ _ _ Hfc) as Ipa.
        destruct (l_pa L); try contradiction. destruct m1; try contradiction.
        simpl. rewrite ?Ptrofs.add_assoc. reflexivity. }
      rewrite hhs3_p3_D_ca_view_eqb_refl. forward_if.
      { hhs3_p3_D_ca_dead. }
      forward. entailer!.
    * forward. apply ENTAIL_refl.
    * pose proof (field_compatible_isptr _ _ _ Hfc) as Ipa.
      pose proof (field_compatible_isptr _ _ _ CIfc) as Ici.
      match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
      -- apply ENTAIL_refl.
      -- forward_call (Tsh, offset_val 328 (l_pa L), hhs3_ts I, Tsh, offset_val 128 (l_ci L), hhs3_ts I).
         rewrite hhs3_p3_D_ca_view_eqb_refl.
         match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
           forward_if (PROPx P (LOCALx (temp HC._t'79 (Vint Int.one) :: Q) (SEPx R))) end.
         ++ forward_call (Tsh, offset_val 128 (l_ci L), hhs3_ts I, Tsh, l_ts L, hhs3_ts I).
            rewrite hhs3_p3_D_ca_view_eqb_refl. forward. entailer!.
         ++ hhs3_p3_D_ca_dead.
         ++ forward_if.
            { hhs3_p3_D_ca_dead. }
            forward. entailer!.
      -- forward. apply ENTAIL_refl.
      -- unfold POSTCONDITION, abbreviate. cbn [RA_normal].
         rewrite (hhs3_p3_D_ca_view_eq Tsh (l_pa L) P), (hhs3_p3_D_ca_view_init Ews m1 _),
           (hhs3_p3_D_ca_view_ci Tsh (l_ci L) ck h _ _ _ CIfc Lt).
         unfold hhs3_p3_D_ca_view. rewrite Es, Er, Et, hhs3_p3_D_ca_view_M1eph.
         entailer!.
Qed.

End Part.
