(* law cookie_mac: main's phase P6c, statements 81 of hck5_cut.v:
   r = wg_cookie_validate_packet(&wb.cookie_checker, &skb, check_cookie) (v1 P6's last statement).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_mac.hck5_cut.
Require Import WgNoise.proof.harness.cookie_mac.hck5_spec.
Require Import WgNoise.proof.harness.cookie_mac.hck5_defs.
Require Import WgNoise.proof.harness.cookie_mac.hck5_conv.
Require WgNoise.harness.x_cookie_mac.code.

#[local] Existing Instance W_cookie_mac.
Local Open Scope Z_scope.

(* byte arrays are the same predicate in every compspecs (copy of libc_bytes.v, whose .vo is absent) *)
Section Bytes.
Context {cs1 cs2: compspecs}.

Lemma hck5_p6c_align_tuchar: forall (ce: composite_env) n z,
  align_compatible_rec ce (tarray tuchar n) z.
Proof.
  intros. apply align_compatible_rec_Tarray. intros.
  eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l].
Qed.

Lemma hck5_p6c_fc_tuchar: forall n p,
  @field_compatible cs1 (tarray tuchar n) nil p <-> @field_compatible cs2 (tarray tuchar n) nil p.
Proof.
  intros. unfold field_compatible, size_compatible, align_compatible.
  destruct p; simpl; try tauto.
  pose proof (hck5_p6c_align_tuchar (@cenv_cs cs1) n (Ptrofs.unsigned i)).
  pose proof (hck5_p6c_align_tuchar (@cenv_cs cs2) n (Ptrofs.unsigned i)).
  tauto.
Qed.

Lemma hck5_p6c_tuchar_cs: forall sh n (v: list val) p,
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  intros. unfold data_at, field_at.
  f_equal. f_equal. apply prop_ext. apply hck5_p6c_fc_tuchar.
Qed.

Lemma hck5_p6c_tuchar__cs: forall sh n p,
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof.
  intros. unfold data_at_, field_at_. apply hck5_p6c_tuchar_cs.
Qed.
End Bytes.

Lemma hck5_p6c_hb_at sh l p : hbytes sh l p = bytes_at sh l p.
Proof. unfold hbytes, bytes_at. apply hck5_p6c_tuchar_cs. Qed.

Lemma hck5_p6c_ss (S: shim) (r: list byte) w : shimsnap_val (shim_draw S r) w = shimsnap_val S w.
Proof. reflexivity. Qed.

Ltac hck5_p6c_flat :=
  cbv beta iota delta [app hck5_bside hck5_bufs hck5_scr2 hck5_snaps hck5_globs hck5_lvars].

Section P6c.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hck5_P6c_ok {Espec: OracleKind} gv L FR :
  hck5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hck5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hck5_S6b x25519 gv L FR) hck5_P6c
    (overridePost (hck5_S6 x25519 gv L FR) (hck5_R gv)).
Proof.
  intros HH. unfold hck5_S6b, hck5_Delta, hck5_R, hck5_P6c. simplify_func_tycontext. abbreviate_semax.
  Intros R S A m c Q cmode C ck.
  Intros MSG1 C1 MSG2 corrupted chk rl.
  hck5_p6c_flat.
  rewrite (hck5_p6c_hb_at Ews MSG2 m).
  replace (bytes_at Ews MSG2 m) with (bytes_at Ews MSG2 (sk_data (hck5_skb Q m))) by reflexivity.
  set (CC2 := hck5_CC2 x25519 R L (q_now Q) cmode).
  forward_call (gv, S, hck5_w0, Tsh, cc_addr (l_wb L), CC2, Tsh, l_skb L, hck5_skb Q m, Ews, MSG2, chk).
  { entailer!. unfold cc_addr, OFS_DEV_CHECKER. simpl.
    destruct (l_wb L); try contradiction. destruct (l_skb L); try contradiction.
    destruct chk; simpl; rewrite ?Ptrofs.add_zero; reflexivity. }
  { destruct H6 as (_&HL2&_). destruct H1 as (Hn&_). split; [lia |]. simpl. rewrite Int.unsigned_repr by rep_lia. lia. }
  Intros r.
  forward.
  set (VR := validate_model CC2 (hck5_skb Q m) MSG2 chk (s_boot S) (s_rlallow S) r).
  set (S'' := if validate_rotates CC2 MSG2 chk (s_boot S) then shim_draw S r else S).
  assert (HAV: hck5_after_val x25519 R L Q m cmode MSG1 MSG2 corrupted chk rl r VR S'').
  { destruct H6 as (Hc & HL2 & Hb & Hrl).
    unfold hck5_after_val. split; [auto |]. split; [auto |]. split; [auto |].
    split; [unfold hck5_is, VR; rewrite Hb, Hrl; reflexivity |].
    unfold S''. destruct (validate_rotates CC2 MSG2 chk (s_boot S)) eqn:Erot; simpl.
    - split; [auto |]. split; [auto |]. intros _.
      match goal with Hr: Zlength r = 32 |- _ => rewrite Hr end. change (Z.min 32 32) with 32.
      rewrite sublist_same by auto. rewrite sublist_nil. apply app_nil_r.
    - split; [auto |]. split; [auto |]. intros E. unfold CC2 in Erot. rewrite Hb in Erot. congruence. }
  assert (Hss: shimsnap_val S'' hck5_w0 = shimsnap_val S hck5_w0)
    by (unfold S''; destruct (validate_rotates _ _ _ _); reflexivity).
  unfold hck5_S6. Exists R S'' A m c Q cmode C ck. Exists MSG1 C1 MSG2 corrupted chk rl. Exists r VR.
  hck5_p6c_flat. rewrite Hss.
  change (sk_data (hck5_skb Q m)) with m. rewrite <- hck5_p6c_hb_at.
  entailer!.
  apply derives_refl.
Qed.

End P6c.
