(* law handshake, phase P5, segment D, part cb: POS c_hck + c_ridx (hash / ck == st2's; remote_index == m2's sender).
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
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Section Part.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p5_D_cb_ok {Espec: OracleKind} gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb PA1 CI1 CI2 Q M2 H2 MR nowa ST2 (Rp: ret_assert) :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hhs3_p5_D_Q x25519 aead_enc aead_dec gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb PA1 CI1 CI2 Q M2 H2 MR nowa ST2)
    (Ssequence hhs3_p5_D_chck hhs3_p5_D_cridx)
    (overridePost (hhs3_p5_D_Q x25519 aead_enc aead_dec gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb PA1 CI1 CI2 Q M2 H2 MR nowa ST2) Rp).
Proof.
  intros HH. destruct Rp as [Rn Rb Rc Rr]. unfold overridePost.
  unfold hhs3_p5_D_Q, hhs3_p5_D_st, hhs3_Delta, hhs3_p5_D_chck, hhs3_p5_D_cridx.
  simplify_func_tycontext.
  destruct ST2 as [ck h].
  destruct (hhs3_p5_D_ca_view_new x25519 R L M1 H1 M2 ck h) as (Es & Er & Eh & Eck & Eri).
  set (P := p_set_refs (hhs3_p5_new x25519 R L M1 H1 M2 (ck, h)) Int.one) in *.
  unfold hhs3_p5_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
  abbreviate_semax.
  Intros.
  rewrite (hhs3_p5_D_ca_view_eq Tsh (l_pb L) P). Intros.
  assert_PROP (rm_ok (hhs3_M2m x25519 R M2) /\ @field_compatible Noise.CS t_resp [] m2) as RM.
  { unfold resp_rep. Intros. entailer!. }
  destruct RM as [RMok RMfc].
  match goal with Hx: @field_compatible Noise.CS t_peer [] (l_pb L) |- _ => rename Hx into Hfc end.
  match goal with Hx: hs_ok (p_hs P) |- _ => pose proof Hx as (_ & _ & _ & _ & _ & Lh & Lck & _) end.
  rewrite Eh in Lh. rewrite Eck in Lck.
  assert_PROP (@field_compatible HCS t_mstate [] (l_st2 L)) as FCst.
  { unfold hhs3_p5_st2. entailer!. }
  rewrite (hhs3_p5_D_ca_view_resp Ews m2 _ RMok RMfc).
  unfold hhs3_p5_D_ca_view, hhs3_p5_st2. rewrite Eh, Eck, Eri.
  rewrite (hhs3_p5_D_ca_view_mstate Tsh (l_st2 L) ck h FCst Lck Lh).
  assert (ES: rm_sender (hhs3_M2m x25519 R M2) = rm_sender M2) by reflexivity. rewrite ES.
  Intros.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  + apply ENTAIL_refl.
  + forward_call (Tsh, offset_val 264 (l_pb L), h, Tsh, offset_val 32 (l_st2 L), h).
    { entailer!. rewrite Lh. pose proof (field_compatible_isptr _ _ _ FCst) as Ist.
      pose proof (field_compatible_isptr _ _ _ Hfc) as Ipb.
      destruct (l_pb L); try contradiction. destruct (l_st2 L); try contradiction.
      simpl. rewrite ?Ptrofs.add_assoc. reflexivity. }
    rewrite hhs3_p5_D_ca_view_eqb_refl.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HC._t'144 (Vint Int.one) :: Q) (SEPx R))) end.
    { forward_call (Tsh, offset_val 296 (l_pb L), ck, Tsh, l_st2 L, ck).
      { entailer!. rewrite Lck. pose proof (field_compatible_isptr _ _ _ FCst) as Ist.
        pose proof (field_compatible_isptr _ _ _ Hfc) as Ipb.
        destruct (l_pb L); try contradiction. destruct (l_st2 L); try contradiction.
        simpl. rewrite ?Ptrofs.add_assoc, ?Ptrofs.add_zero. reflexivity. }
      rewrite hhs3_p5_D_ca_view_eqb_refl. forward. entailer!. }
    { exfalso. match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
    forward_if.
    { forward_call tt. all: [> exfalso; match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end | entailer!]. }
    forward. entailer!.
  + forward. apply ENTAIL_refl.
  + match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
    * apply ENTAIL_refl.
    * forward. forward. forward_if.
      { forward_call tt. all: [> exfalso; match goal with Hc: _ = Int.zero |- _ => rewrite Int.eq_true in Hc; exact (Int.one_not_zero Hc) end | entailer!]. }
      forward. entailer!.
    * forward. apply ENTAIL_refl.
    * unfold POSTCONDITION, abbreviate. simpl RA_normal. entailer!.
      rewrite (hhs3_p5_D_ca_view_eq Tsh (l_pb L) P), (hhs3_p5_D_ca_view_resp Ews m2 _ RMok RMfc).
      unfold hhs3_p5_D_ca_view, hhs3_p5_st2. rewrite Eh, Eck, Eri, ES.
      rewrite (hhs3_p5_D_ca_view_mstate Tsh (l_st2 L) ck h FCst Lck Lh).
      entailer!.
Qed.

End Part.
