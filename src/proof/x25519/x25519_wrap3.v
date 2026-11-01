(* part of x25519_part3: the wrappers of curve25519-fiat32.c (they pass h->v = offset_val 0 h) and fe_invert.
   Specifications: x25519_spec.v, model: x25519_model.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.x25519.x25519_spec.

#[local] Existing Instance Curve25519Fiat32.CS.

Lemma body3_fe_frombytes : semax_body x25_V x25_Gprog F.f_fe_frombytes fe_frombytes_spec.
Proof.
  start_function.
  forward_call (osh, h, ssh, s, bs).
  { entailer!. simpl. rewrite !isptr_offset_val_zero by auto. reflexivity. }
  entailer!.
Qed.

Lemma body3_fe_add : semax_body x25_V x25_Gprog F.f_fe_add fe_add_spec.
Proof.
  start_function.
  forward_call (osh, out, sh1, in1, f, sh2, in2, g).
  { entailer!. simpl. rewrite !isptr_offset_val_zero by auto. reflexivity. }
  entailer!.
Qed.

Lemma body3_fe_sub : semax_body x25_V x25_Gprog F.f_fe_sub fe_sub_spec.
Proof.
  start_function.
  forward_call (osh, out, sh1, in1, f, sh2, in2, g).
  { entailer!. simpl. rewrite !isptr_offset_val_zero by auto. reflexivity. }
  entailer!.
Qed.

Lemma body3_fe_mul_ttt : semax_body x25_V x25_Gprog F.f_fe_mul_ttt fe_mul_ttt_spec.
Proof.
  start_function.
  destruct m; simpl in H1; subst; simpl fe3_pre; simpl fe3_post; repeat flatten_sepcon_in_SEP.
  - assert_PROP (isptr out /\ isptr in1 /\ isptr in2) by entailer!.
    forward_call (FA_none, osh, out, sh1, in1, f, sh2, in2, g).
    { entailer!. simpl. rewrite !isptr_offset_val_zero by tauto. reflexivity. }
    { simpl fe3_pre. cancel. }
    entailer!.
  - assert_PROP (isptr in1 /\ isptr in2) by entailer!.
    forward_call (FA_out1, osh, in1, sh1, in1, f, sh2, in2, g).
    { entailer!. simpl. rewrite !isptr_offset_val_zero by tauto. reflexivity. }
    { simpl fe3_pre. cancel. }
    entailer!.
  - assert_PROP (isptr in1 /\ isptr in2) by entailer!.
    forward_call (FA_out2, osh, in2, sh1, in1, f, sh2, in2, g).
    { entailer!. simpl. rewrite !isptr_offset_val_zero by tauto. reflexivity. }
    { simpl fe3_pre. cancel. }
    entailer!.
Qed.

Lemma body3_fe_mul_tlt : semax_body x25_V x25_Gprog F.f_fe_mul_tlt fe_mul_tlt_spec.
Proof.
  start_function.
  destruct m; simpl in H1; subst; simpl fe3_pre; simpl fe3_post; repeat flatten_sepcon_in_SEP.
  - assert_PROP (isptr out /\ isptr in1 /\ isptr in2) by entailer!.
    forward_call (FA_none, osh, out, sh1, in1, f, sh2, in2, g).
    { entailer!. simpl. rewrite !isptr_offset_val_zero by tauto. reflexivity. }
    { simpl fe3_pre. cancel. }
    entailer!.
  - assert_PROP (isptr in1 /\ isptr in2) by entailer!.
    forward_call (FA_out1, osh, in1, sh1, in1, f, sh2, in2, g).
    { entailer!. simpl. rewrite !isptr_offset_val_zero by tauto. reflexivity. }
    { simpl fe3_pre. cancel. }
    entailer!.
  - assert_PROP (isptr in1 /\ isptr in2) by entailer!.
    forward_call (FA_out2, osh, in2, sh1, in1, f, sh2, in2, g).
    { entailer!. simpl. rewrite !isptr_offset_val_zero by tauto. reflexivity. }
    { simpl fe3_pre. cancel. }
    entailer!.
Qed.

Lemma body3_fe_mul_tll : semax_body x25_V x25_Gprog F.f_fe_mul_tll fe_mul_tll_spec.
Proof.
  start_function.
  destruct m; simpl in H1; subst; simpl fe3_pre; simpl fe3_post; repeat flatten_sepcon_in_SEP.
  - assert_PROP (isptr out /\ isptr in1 /\ isptr in2) by entailer!.
    forward_call (FA_none, osh, out, sh1, in1, f, sh2, in2, g).
    { entailer!. simpl. rewrite !isptr_offset_val_zero by tauto. reflexivity. }
    { simpl fe3_pre. cancel. }
    entailer!.
  - assert_PROP (isptr in1 /\ isptr in2) by entailer!.
    forward_call (FA_out1, osh, in1, sh1, in1, f, sh2, in2, g).
    { entailer!. simpl. rewrite !isptr_offset_val_zero by tauto. reflexivity. }
    { simpl fe3_pre. cancel. }
    entailer!.
  - assert_PROP (isptr in1 /\ isptr in2) by entailer!.
    forward_call (FA_out2, osh, in2, sh1, in1, f, sh2, in2, g).
    { entailer!. simpl. rewrite !isptr_offset_val_zero by tauto. reflexivity. }
    { simpl fe3_pre. cancel. }
    entailer!.
Qed.

Lemma body3_fe_sq_tl : semax_body x25_V x25_Gprog F.f_fe_sq_tl fe_sq_tl_spec.
Proof.
  start_function.
  destruct m; simpl in H0; subst; simpl fe2_pre; simpl fe2_post; repeat flatten_sepcon_in_SEP.
  - assert_PROP (isptr out /\ isptr in1) by entailer!.
    forward_call (FS_none, osh, out, sh1, in1, f).
    { entailer!. simpl. rewrite !isptr_offset_val_zero by tauto. reflexivity. }
    { simpl fe2_pre. cancel. }
    entailer!.
  - assert_PROP (isptr in1) by entailer!.
    forward_call (FS_out, osh, in1, sh1, in1, f).
    entailer!.
Qed.

Lemma body3_fe_sq_tt : semax_body x25_V x25_Gprog F.f_fe_sq_tt fe_sq_tt_spec.
Proof.
  start_function.
  destruct m; simpl in H0; subst; simpl fe2_pre; simpl fe2_post; repeat flatten_sepcon_in_SEP.
  - assert_PROP (isptr out /\ isptr in1) by entailer!.
    forward_call (FS_none, osh, out, sh1, in1, f).
    { entailer!. simpl. rewrite !isptr_offset_val_zero by tauto. reflexivity. }
    { simpl fe2_pre. cancel. }
    entailer!.
  - assert_PROP (isptr in1) by entailer!.
    forward_call (FS_out, osh, in1, sh1, in1, f).
    entailer!.
Qed.

Lemma body3_fe_mul121666 : semax_body x25_V x25_Gprog F.f_fe_mul121666 fe_mul121666_spec.
Proof.
  start_function.
  forward_call (osh, out, sh1, in1, f).
  { entailer!. simpl. rewrite !isptr_offset_val_zero by auto. reflexivity. }
  entailer!.
Qed.

Lemma fel_limbs3 (sh: share) (p: val) :
  field_compatible t_fel nil p -> data_at_ sh t_fel p = data_at_ sh t_limbs p.
Proof.
  intros FC.
  assert (FC2: field_compatible t_limbs nil p).
  { pose proof (field_compatible_nested_field t_fel (DOT F._v) p) as K.
    assert (FC1: field_compatible t_fel (DOT F._v) p)
      by (apply field_compatible_cons; simpl; split; [left; reflexivity | exact FC]).
    specialize (K FC1). simpl in K. assert (isptr p) by (destruct FC; auto).
    rewrite isptr_offset_val_zero in K by auto. exact K. }
  rewrite !data_at__memory_block.
  rewrite !prop_true_andp by auto.
  reflexivity.
Qed.

Lemma body3_fe_invert : semax_body x25_V x25_Gprog F.f_fe_invert fe_invert_spec.
Proof.
  start_function.
  assert_PROP (field_compatible t_fel nil v_l) by entailer!.
  change (data_at_ Tsh (Tstruct F._fe_loose noattr) v_l) with (data_at_ Tsh t_fel v_l).
  rewrite (fel_limbs3 Tsh v_l H0).
  forward_call (Tsh, v_l, sh, p, f).
  forward_call (sh, p, Tsh, v_l, f).
  sep_apply (data_at_data_at_ Tsh t_limbs (map Vint f) v_l).
  rewrite <- (fel_limbs3 Tsh v_l H0).
  unfold fe_invert_m. entailer!.
Qed.

Theorem x25519_wrap3 :
  semax_body x25_V x25_Gprog F.f_fe_frombytes fe_frombytes_spec /\
  semax_body x25_V x25_Gprog F.f_fe_add fe_add_spec /\
  semax_body x25_V x25_Gprog F.f_fe_sub fe_sub_spec /\
  semax_body x25_V x25_Gprog F.f_fe_mul_ttt fe_mul_ttt_spec /\
  semax_body x25_V x25_Gprog F.f_fe_mul_tlt fe_mul_tlt_spec /\
  semax_body x25_V x25_Gprog F.f_fe_mul_tll fe_mul_tll_spec /\
  semax_body x25_V x25_Gprog F.f_fe_sq_tl fe_sq_tl_spec /\
  semax_body x25_V x25_Gprog F.f_fe_sq_tt fe_sq_tt_spec /\
  semax_body x25_V x25_Gprog F.f_fe_mul121666 fe_mul121666_spec /\
  semax_body x25_V x25_Gprog F.f_fe_invert fe_invert_spec.
Proof.
  split; [exact body3_fe_frombytes|]. split; [exact body3_fe_add|]. split; [exact body3_fe_sub|].
  split; [exact body3_fe_mul_ttt|]. split; [exact body3_fe_mul_tlt|]. split; [exact body3_fe_mul_tll|].
  split; [exact body3_fe_sq_tl|]. split; [exact body3_fe_sq_tt|]. split; [exact body3_fe_mul121666|].
  exact body3_fe_invert.
Qed.
