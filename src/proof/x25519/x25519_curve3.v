(* part of x25519_part3: the bodies of lib/crypto/curve25519.c (unit Curve25519; curve25519_generic is specified at Curve25519Fiat32.CS: byte arrays are the same in both compspecs).
   Specifications: x25519_spec.v, model: x25519_model.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.x25519.x25519_spec.

#[local] Existing Instance Curve25519.CS.

(* byte arrays are the same predicates in every compspecs *)
Section Bytes3.
Context {cs1 cs2: compspecs}.

Lemma x25c3_align_tuchar: forall (ce: composite_env) n z,
  align_compatible_rec ce (tarray tuchar n) z.
Proof.
  intros. apply align_compatible_rec_Tarray. intros.
  eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l].
Qed.

Lemma x25c3_field_compatible_cs: forall n p,
  @field_compatible cs1 (tarray tuchar n) nil p <-> @field_compatible cs2 (tarray tuchar n) nil p.
Proof.
  intros. unfold field_compatible, size_compatible, align_compatible.
  destruct p; simpl; try tauto.
  pose proof (x25c3_align_tuchar (@cenv_cs cs1) n (Ptrofs.unsigned i)).
  pose proof (x25c3_align_tuchar (@cenv_cs cs2) n (Ptrofs.unsigned i)).
  tauto.
Qed.

Lemma x25c3_data_at_cs: forall sh n (v: list val) p,
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  intros. unfold data_at, field_at.
  f_equal. f_equal. apply prop_ext. apply x25c3_field_compatible_cs.
Qed.

Lemma x25c3_data_at__cs: forall sh n p,
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof.
  intros. unfold data_at_, field_at_. apply x25c3_data_at_cs.
Qed.

End Bytes3.

Lemma x25c3_body_arch: semax_body x25_V_c x25_Gprog_c C.f_curve25519_arch curve25519_arch_spec.
Proof.
  start_function.
  rewrite (@x25c3_data_at__cs Curve25519.CS Curve25519Fiat32.CS osh),
    (@x25c3_data_at_cs Curve25519.CS Curve25519Fiat32.CS ssh),
    (@x25c3_data_at_cs Curve25519.CS Curve25519Fiat32.CS psh).
  forward_call (osh, out, ssh, s, sc, psh, p, pt).
  rewrite (@x25c3_data_at_cs Curve25519Fiat32.CS Curve25519.CS osh),
    (@x25c3_data_at_cs Curve25519Fiat32.CS Curve25519.CS ssh),
    (@x25c3_data_at_cs Curve25519Fiat32.CS Curve25519.CS psh).
  entailer!.
Qed.

Lemma x25c3_body_base_arch:
  semax_body x25_V_c x25_Gprog_c C.f_curve25519_base_arch curve25519_base_arch_spec.
Proof.
  start_function.
  unfold curve25519_globals. Intros.
  rewrite (@x25c3_data_at__cs Curve25519.CS Curve25519Fiat32.CS osh),
    (@x25c3_data_at_cs Curve25519.CS Curve25519Fiat32.CS ssh).
  rewrite (@x25c3_data_at_cs Curve25519.CS Curve25519Fiat32.CS Ers 32 (map Vubyte basepoint9)).
  forward_call (osh, out, ssh, s, sc, Ers, gv C._curve25519_base_point, basepoint9).
  rewrite (@x25c3_data_at_cs Curve25519Fiat32.CS Curve25519.CS osh),
    (@x25c3_data_at_cs Curve25519Fiat32.CS Curve25519.CS ssh),
    (@x25c3_data_at_cs Curve25519Fiat32.CS Curve25519.CS Ers 32 (map Vubyte basepoint9)).
  unfold curve25519_globals. entailer!.
Qed.

Lemma x25c3_body_curve25519:
  semax_body x25_V_c x25_Gprog_c C.f_curve25519 (@curve25519_spec_of Curve25519.CS x25519_m).
Proof.
  start_function.
  forward_call (osh, out, ssh, s, sc, psh, p, pt).
  unfold curve25519_globals. Intros.
  pose proof (x25519_m_length sc pt).
  forget (x25519_m sc pt) as r.
  forward_call (osh, Ers, out, gv C._curve25519_null_point, 32, r, zeros32).
  forward.
  unfold curve25519_globals.
  destruct (memneq_bool r zeros32); entailer!.
Qed.

Lemma x25c3_body_generate_public:
  semax_body x25_V_c x25_Gprog_c C.f_curve25519_generate_public
    (@curve25519_generate_public_spec_of Curve25519.CS x25519_m).
Proof.
  start_function.
  unfold curve25519_globals. Intros.
  forward_call (ssh, Ers, s, gv C._curve25519_null_point, 32, sc, zeros32).
  destruct (memneq_bool sc zeros32) eqn:E.
  - forward_if.
    { exfalso; first [now elim H1 | discriminate H1 | inv H1]. }
    sep_apply (data_at_data_at_ osh (tarray tuchar 32) old out).
    forward_call (osh, out, ssh, s, sc, gv).
    { unfold curve25519_globals. cancel. }
    unfold curve25519_globals. Intros.
    pose proof (x25519_m_length sc basepoint9).
    forget (x25519_m sc basepoint9) as r.
    forward_call (osh, Ers, out, gv C._curve25519_null_point, 32, r, zeros32).
    forward.
    unfold curve25519_globals.
    destruct (memneq_bool r zeros32); entailer!.
  - forward_if.
    + forward. unfold curve25519_globals. entailer!.
    + exfalso; first [now elim H1 | discriminate H1 | inv H1].
Qed.

Theorem x25519_curve3 :
  semax_body x25_V_c x25_Gprog_c C.f_curve25519_arch curve25519_arch_spec /\
  semax_body x25_V_c x25_Gprog_c C.f_curve25519_base_arch curve25519_base_arch_spec /\
  semax_body x25_V_c x25_Gprog_c C.f_curve25519 (@curve25519_spec_of Curve25519.CS x25519_m) /\
  semax_body x25_V_c x25_Gprog_c C.f_curve25519_generate_public (@curve25519_generate_public_spec_of Curve25519.CS x25519_m).
Proof.
  split; [apply x25c3_body_arch |].
  split; [apply x25c3_body_base_arch |].
  split; [apply x25c3_body_curve25519 | apply x25c3_body_generate_public].
Qed.
