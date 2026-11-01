(* law handshake, phase P5, segment E.
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
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.

(* ---------------------------------------------------------------------- *)
(* Helpers                                                                 *)
(* ---------------------------------------------------------------------- *)
Local Open Scope logic.

Lemma hhs3_p5_E_eqb_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

(* the harness's m_state: two byte buffers *)
Lemma hhs3_p5_E_mstate_open sh p ck h :
  @field_compatible HCS t_mstate [] p -> Zlength ck = 32 -> Zlength h = 32 ->
  @data_at HCS sh t_mstate (mstate_val ck h) p = hbytes sh ck p * hbytes sh h (offset_val 32 p).
Proof.
  intros FC L1 L2.
  unfold mstate_val, hbytes. rewrite L1, L2.
  unfold_data_at (@data_at HCS sh t_mstate _ p).
  rewrite (@field_at_data_at HCS sh t_mstate (DOT HC._ck)), (@field_at_data_at HCS sh t_mstate (DOT HC._h)).
  rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  assert (isptr p) by (destruct FC; auto).
  rewrite !(isptr_offset_val_zero p) by auto.
  apply pred_ext; cancel.
Qed.

(* the harness's m_response: five byte buffers *)
Lemma hhs3_p5_E_mresp_open sh p E encn ep ck h :
  @field_compatible HCS t_mresp [] p ->
  Zlength E = 32 -> Zlength encn = 16 -> Zlength ep = 32 -> Zlength ck = 32 -> Zlength h = 32 ->
  @data_at HCS sh t_mresp (mresp_val E encn ep ck h) p =
  hbytes sh E p * hbytes sh encn (offset_val 32 p) * hbytes sh ep (offset_val 48 p) *
  hbytes sh ck (offset_val 80 p) * hbytes sh h (offset_val 112 p).
Proof.
  intros FC L1 L2 L3 L4 L5.
  unfold mresp_val, hbytes. rewrite L1, L2, L3, L4, L5.
  unfold_data_at (@data_at HCS sh t_mresp _ p).
  rewrite (@field_at_data_at HCS sh t_mresp (DOT HC._ephemeral)),
    (@field_at_data_at HCS sh t_mresp (DOT HC._enc_nothing)),
    (@field_at_data_at HCS sh t_mresp (DOT HC._eph_priv)),
    (@field_at_data_at HCS sh t_mresp (DOT HC._st)).
  rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  assert (FC2: @field_compatible HCS t_mstate [] (offset_val 80 p)).
  { pose proof (@field_compatible_app HCS [] t_mresp (DOT HC._st) p) as X.
    rewrite field_address_offset in X by auto with field_compatible. apply X. simpl app.
    auto with field_compatible. }
  change (Tstruct HH._m_state noattr) with t_mstate.
  unfold_data_at (@data_at HCS sh t_mstate _ (offset_val 80 p)).
  rewrite (@field_at_data_at HCS sh t_mstate (DOT HC._ck)), (@field_at_data_at HCS sh t_mstate (DOT HC._h)).
  rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  assert (isptr p) by (destruct FC; auto).
  rewrite !offset_offset_val. simpl Z.add. rewrite !(isptr_offset_val_zero p) by auto.
  apply pred_ext; cancel.
Qed.

Ltac hhs3_p5_E_ptr :=
  repeat match goal with
  | |- context [l_st2 ?L] => let H := fresh in assert (H: isptr (l_st2 L)) by auto;
                             destruct (l_st2 L); try contradiction; clear H
  | |- context [l_mr ?L] => let H := fresh in assert (H: isptr (l_mr L)) by auto;
                            destruct (l_mr L); try contradiction; clear H
  end;
  simpl; rewrite ?Ptrofs.add_zero, ?Ptrofs.add_assoc; reflexivity.

Local Open Scope Z_scope.

Section P5E.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p5_E_ok {Espec: OracleKind} gv L FR :
  hhs3_p5_crypto_stmt x25519 aead_enc aead_dec ->
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p5_SD x25519 aead_enc aead_dec gv L FR) hhs3_p5_E
    (overridePost (hhs3_p5_SD x25519 aead_enc aead_dec gv L FR) (hhs3_R gv)).
Proof.
  intros HC HH. unfold hhs3_p5_SD, hhs3_Delta, hhs3_R, hhs3_p5_E. simplify_func_tycontext. abbreviate_semax.
  Intros R S m1 m2 a0 f0 l0 I M1 H1. Intros MI nowb PA1 CI1 CI2 Q M2 H2 MR. Intros nowa acc PB2 ST2.
  destruct MR as [[[[E encn] ep] ck] h].
  forward_if.
  2: { (* all_ok false *)
    forward.
    try unfold POSTCONDITION, abbreviate; try rewrite overridePost_normal'.
    unfold hhs3_p5_SD.
    Exists R S m1 m2 a0 f0 l0 I M1 H1. Exists MI nowb PA1 CI1 CI2 Q M2 H2 (E, encn, ep, ck, h).
    Exists nowa acc PB2 ST2.
    unfold hhs3_p5_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app]. entailer!. }
  (* all_ok true *)
  assert (OK: hhs3_ok4 x25519 (hhs3_ok3 x25519 R I nowb MI) MI R (E, encn, ep, ck, h) = true).
  { destruct (hhs3_ok4 x25519 (hhs3_ok3 x25519 R I nowb MI) MI R (E, encn, ep, ck, h)); [reflexivity | contradiction]. }
  destruct HH as (Hx & Ha & _ & Hc & _).
  destruct (HC Hc Hx Ha R L I M1 H1 MI nowb PA1 CI1 CI2 Q M2 H2 (E, encn, ep, ck, h) H H3 H4 H5 OK) as [A1 A2].
  cbv beta iota in A2.
  assert (Hacc: acc = true) by (rewrite H8; exact A1).
  destruct (H9 Hacc) as [M _]. rewrite A2 in M. injection M as <-. rewrite Hacc.
  unfold hhs3_p5_st2, hhs3_p5_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
  assert_PROP (Zlength E = 32 /\ Zlength encn = 16 /\ Zlength ep = 32 /\ Zlength ck = 32 /\ Zlength h = 32 /\
               @field_compatible HCS t_mresp [] (l_mr L) /\ @field_compatible HCS t_mstate [] (l_st2 L)) as LMR.
  { entailer!.
    match goal with Hv: value_fits t_mresp (mresp_val _ _ _ _ _) |- _ =>
      unfold mresp_val in Hv; simplify_value_fits in Hv;
      destruct Hv as ((A1'&_)&(A2'&_)&(A3'&_)&(A4'&_)&(A5'&_));
      unfold bytes in A1', A2', A3', A4', A5'; unfold unfold_reptype in A1', A2', A3', A4', A5';
      simpl in A1', A2', A3', A4', A5'; rewrite !Zlength_map in A1', A2', A3', A4', A5' end.
    repeat split; assumption. }
  destruct LMR as (LE & Lencn & Lep & Lck & Lh & FCmr & FCst).
  rewrite (hhs3_p5_E_mresp_open Tsh (l_mr L) E encn ep ck h FCmr) by assumption.
  rewrite (hhs3_p5_E_mstate_open Tsh (l_st2 L) ck h FCst) by assumption.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  + apply ENTAIL_refl.
  + forward_if (temp HC._t'153 (Vint Int.one)).
    { forward_call (Tsh, l_st2 L, ck, Tsh, offset_val 80 (l_mr L), ck).
      { entailer!. rewrite Lck. simpl. hhs3_p5_E_ptr. }
      { cancel. }
      forward. entailer!. rewrite hhs3_p5_E_eqb_refl. reflexivity. }
    { exfalso; apply Int.one_not_zero; assumption. }
    forward_if (temp HC._t'155 (Vint Int.one)).
    { forward_call (Tsh, offset_val 32 (l_st2 L), h, Tsh, offset_val 112 (l_mr L), h).
      { entailer!. rewrite Lh. simpl. hhs3_p5_E_ptr. }
      { cancel. }
      forward. entailer!. rewrite hhs3_p5_E_eqb_refl. reflexivity. }
    { exfalso; apply Int.one_not_zero; assumption. }
    forward_if.
    * exfalso; apply Int.one_not_zero; assumption.
    * forward. entailer!.
  + forward. apply ENTAIL_refl.
  + try unfold POSTCONDITION, abbreviate; try rewrite overridePost_normal'.
    unfold hhs3_p5_SD.
    Exists R S m1 m2 a0 f0 l0 I M1 H1. Exists MI nowb PA1 CI1 CI2 Q M2 H2 (E, encn, ep, ck, h).
    Exists nowa acc PB2 (ck, h).
    unfold hhs3_p5_st2, hhs3_p5_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
    rewrite (hhs3_p5_E_mresp_open Tsh (l_mr L) E encn ep ck h FCmr) by assumption.
    rewrite (hhs3_p5_E_mstate_open Tsh (l_st2 L) ck h FCst) by assumption.
    rewrite Hacc. entailer!.
Qed.

End P5E.
