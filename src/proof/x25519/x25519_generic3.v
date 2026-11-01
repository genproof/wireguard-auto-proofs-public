(* part of x25519_part3: the body of curve25519_generic (the Montgomery ladder: ladder_steps).
   Specifications: x25519_spec.v, model: x25519_model.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.x25519.x25519_spec.

#[local] Existing Instance Curve25519Fiat32.CS.

Local Open Scope Z_scope.

Lemma fe_fc_limbs3 : forall p, field_compatible t_fe nil p -> field_compatible t_limbs nil p.
Proof.
  intros.
  assert (field_compatible t_fe (DOT F._v) p).
  { apply field_compatible_cons; split; auto. left. reflexivity. }
  apply field_compatible_nested_field in H0.
  simpl in H0. rewrite isptr_offset_val_zero in H0 by auto. exact H0.
Qed.

Lemma fel_fc_limbs3 : forall p, field_compatible t_fel nil p -> field_compatible t_limbs nil p.
Proof.
  intros.
  assert (field_compatible t_fel (DOT F._v) p).
  { apply field_compatible_cons; split; auto. left. reflexivity. }
  apply field_compatible_nested_field in H0.
  simpl in H0. rewrite isptr_offset_val_zero in H0 by auto. exact H0.
Qed.

Lemma limbs_fc_bytes3 : forall p, field_compatible t_limbs nil p -> field_compatible (tarray tuchar 40) nil p.
Proof.
  intros. unfold field_compatible in *. destruct H as (? & ? & ? & ? & ?).
  repeat split; auto.
  hnf in H2 |- *. destruct p; try contradiction.
  apply align_compatible_rec_Tarray; intros.
  eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l].
Qed.

Lemma fe_limbs3 : forall sh p, field_compatible t_fe nil p ->
  data_at_ sh (Tstruct F._fe noattr) p = data_at_ sh t_limbs p.
Proof.
  intros. rewrite !data_at__memory_block. simpl sizeof.
  apply pred_ext; entailer!; auto using fe_fc_limbs3.
Qed.

Lemma fel_limbs3 : forall sh p, field_compatible t_fel nil p ->
  data_at_ sh (Tstruct F._fe_loose noattr) p = data_at_ sh t_limbs p.
Proof.
  intros. rewrite !data_at__memory_block. simpl sizeof.
  apply pred_ext; entailer!; auto using fel_fc_limbs3.
Qed.

Lemma limbs_bytes3 : forall sh p, field_compatible t_limbs nil p ->
  data_at_ sh t_limbs p = data_at_ sh (tarray tuchar 40) p.
Proof.
  intros. rewrite !data_at__memory_block. simpl sizeof.
  apply pred_ext; entailer!; auto using limbs_fc_bytes3.
Qed.

Lemma fe_mul_len3 : forall f g, Zlength (fe_mul_m f g) = 10.
Proof. intros. reflexivity. Qed.
Lemma fe_sqr_len3 : forall f, Zlength (fe_sqr_m f) = 10.
Proof. intros. reflexivity. Qed.
Lemma fe_mul121666_len3 : forall f, Zlength (fe_mul121666_m f) = 10.
Proof. intros. reflexivity. Qed.
Lemma fe_add_len3 : forall f g, Zlength (fe_add_m f g) = 10.
Proof. intros. reflexivity. Qed.
Lemma fe_sub_len3 : forall f g, Zlength (fe_sub_m f g) = 10.
Proof. intros. reflexivity. Qed.
Lemma fe_cswap1_len3 : forall f g b, Zlength (fst (fe_cswap_m f g b)) = 10.
Proof. intros. reflexivity. Qed.
Lemma fe_cswap2_len3 : forall f g b, Zlength (snd (fe_cswap_m f g b)) = 10.
Proof. intros. reflexivity. Qed.
Lemma fe_frombytes_len3 : forall s, Zlength (fe_frombytes_m s) = 10.
Proof. intros. reflexivity. Qed.
Lemma fe_invert_len3 : forall f, Zlength (fe_invert_m f) = 10.
Proof. intros. unfold fe_invert_m, fe_loose_invert_m. apply fe_mul_len3. Qed.

Lemma ladder_step_len3 : forall e x1 pos st,
  Zlength (ls_x2 (ladder_step e x1 pos st)) = 10 /\ Zlength (ls_z2 (ladder_step e x1 pos st)) = 10 /\
  Zlength (ls_x3 (ladder_step e x1 pos st)) = 10 /\ Zlength (ls_z3 (ladder_step e x1 pos st)) = 10.
Proof.
  intros. unfold ladder_step.
  split; [apply fe_mul_len3 | split; [apply fe_mul_len3 | split; [apply fe_sqr_len3 | apply fe_mul_len3]]].
Qed.

Ltac post3 := try unfold fe3_post; try unfold fe2_post; cbv beta iota; repeat flatten_sepcon_in_SEP.

Definition hide3 (P: Prop) : Prop := P.
Ltac nm3 t X E := remember t as X eqn:E; change (hide3 (X = t)) in E.

Ltac undat3 v := match goal with |- context [data_at Tsh t_limbs ?l v] =>
  sep_apply (data_at_data_at_ Tsh t_limbs l v) end.

Ltac fc3 := first [apply fe_fc_limbs3; assumption | apply fel_fc_limbs3; assumption].

Ltac mz3 v := try undat3 v; rewrite (limbs_bytes3 Tsh v) by fc3; forward_call (Tsh, v, 40);
  match goal with |- context [data_at Tsh (tarray tuchar 40) ?l v] =>
    sep_apply (data_at_data_at_ Tsh (tarray tuchar 40) l v) end;
  rewrite <- (limbs_bytes3 Tsh v) by fc3.

Definition gst3 (e: list byte) (x1: list int) (i: Z) : ladder_state :=
  ladder_steps e x1 (Z.to_nat (254 - i)) (ladder_init x1).

Lemma ladder_steps_S3 : forall e x1 n st,
  ladder_steps e x1 (S n) st = ladder_step e x1 (254 - Z.of_nat n) (ladder_steps e x1 n st).
Proof. intros. reflexivity. Qed.

Lemma gst3_len : forall e x1 i, Zlength x1 = 10 ->
  Zlength (ls_x2 (gst3 e x1 i)) = 10 /\ Zlength (ls_z2 (gst3 e x1 i)) = 10 /\
  Zlength (ls_x3 (gst3 e x1 i)) = 10 /\ Zlength (ls_z3 (gst3 e x1 i)) = 10.
Proof.
  intros. unfold gst3. destruct (Z.to_nat (254 - i)).
  - simpl. auto.
  - rewrite ladder_steps_S3. apply ladder_step_len3.
Qed.

Lemma gst3_next : forall e x1 i, 0 <= i <= 254 ->
  gst3 e x1 (i - 1) = ladder_step e x1 i (gst3 e x1 i).
Proof.
  intros. unfold gst3.
  replace (Z.to_nat (254 - (i - 1))) with (S (Z.to_nat (254 - i))) by lia.
  rewrite ladder_steps_S3.
  f_equal. lia.
Qed.

Theorem x25519_generic3 :
  semax_body x25_V x25_Gprog F.f_curve25519_generic (@curve25519_generic_spec_of Curve25519Fiat32.CS x25519_m).
Proof.
start_function.
repeat match goal with
| |- context [data_at_ Tsh (Tstruct F._fe noattr) ?v] =>
   assert_PROP (field_compatible t_fe nil v) by entailer!;
   rewrite (fe_limbs3 Tsh v) by auto
| |- context [data_at_ Tsh (Tstruct F._fe_loose noattr) ?v] =>
   assert_PROP (field_compatible t_fel nil v) by entailer!;
   rewrite (fel_limbs3 Tsh v) by auto
end.
forward.
forward_call (Tsh, ssh, v_e, s, 32, sc).
forward_call (Tsh, v_e, sc).
forward_call (Tsh, v_x1, psh, p, pt).
forward_call (Tsh, v_x2).
forward_call (Tsh, v_z2).
forward_call (Tsh, v_x3, Tsh, v_x1, fe_frombytes_m pt).
forward_call (Tsh, v_z3).
remember (clamp sc) as e eqn:Ee.
assert (Hlen: Zlength (clamp sc) = 32) by (unfold clamp; list_solve).
assert (Hx1: Zlength (fe_frombytes_m pt) = 10) by apply fe_frombytes_len3.
remember (fe_frombytes_m pt) as x1 eqn:Ex1.
forward_loop (EX i: Z,
  PROP (-1 <= i <= 254)
  LOCAL (temp F._pos (Vint (Int.repr i)); temp F._swap (Vint (ls_swap (gst3 e x1 i)));
   lvar F._tmp1l (Tstruct F._fe_loose noattr) v_tmp1l;
   lvar F._tmp0l (Tstruct F._fe_loose noattr) v_tmp0l;
   lvar F._tmp1 (Tstruct F._fe noattr) v_tmp1;
   lvar F._tmp0 (Tstruct F._fe noattr) v_tmp0;
   lvar F._e (tarray tuchar 32) v_e;
   lvar F._x3l (Tstruct F._fe_loose noattr) v_x3l;
   lvar F._z2l (Tstruct F._fe_loose noattr) v_z2l;
   lvar F._x2l (Tstruct F._fe_loose noattr) v_x2l;
   lvar F._z3 (Tstruct F._fe noattr) v_z3;
   lvar F._x3 (Tstruct F._fe noattr) v_x3;
   lvar F._z2 (Tstruct F._fe noattr) v_z2;
   lvar F._x2 (Tstruct F._fe noattr) v_x2;
   lvar F._x1 (Tstruct F._fe noattr) v_x1; temp F._out out;
   temp F._scalar s; temp F._point p)
  SEP (data_at Tsh t_limbs (map Vint (ls_z3 (gst3 e x1 i))) v_z3;
   data_at Tsh t_limbs (map Vint (ls_x3 (gst3 e x1 i))) v_x3;
   data_at Tsh t_limbs (map Vint x1) v_x1;
   data_at Tsh t_limbs (map Vint (ls_z2 (gst3 e x1 i))) v_z2;
   data_at Tsh t_limbs (map Vint (ls_x2 (gst3 e x1 i))) v_x2;
   data_at psh (tarray tuchar 32) (map Vubyte pt) p;
   data_at Tsh (tarray tuchar 32) (map Vubyte e) v_e;
   data_at ssh (tarray tuchar 32) (map Vubyte sc) s;
   data_at_ Tsh t_limbs v_tmp1l; data_at_ Tsh t_limbs v_tmp0l;
   data_at_ Tsh t_limbs v_tmp1; data_at_ Tsh t_limbs v_tmp0;
   data_at_ Tsh t_limbs v_x3l; data_at_ Tsh t_limbs v_z2l;
   data_at_ Tsh t_limbs v_x2l; data_at_ osh (tarray tuchar 32) out))%assert
 continue: (EX i: Z,
  PROP (0 <= i <= 254)
  LOCAL (temp F._pos (Vint (Int.repr i)); temp F._swap (Vint (ls_swap (gst3 e x1 (i - 1))));
   lvar F._tmp1l (Tstruct F._fe_loose noattr) v_tmp1l;
   lvar F._tmp0l (Tstruct F._fe_loose noattr) v_tmp0l;
   lvar F._tmp1 (Tstruct F._fe noattr) v_tmp1;
   lvar F._tmp0 (Tstruct F._fe noattr) v_tmp0;
   lvar F._e (tarray tuchar 32) v_e;
   lvar F._x3l (Tstruct F._fe_loose noattr) v_x3l;
   lvar F._z2l (Tstruct F._fe_loose noattr) v_z2l;
   lvar F._x2l (Tstruct F._fe_loose noattr) v_x2l;
   lvar F._z3 (Tstruct F._fe noattr) v_z3;
   lvar F._x3 (Tstruct F._fe noattr) v_x3;
   lvar F._z2 (Tstruct F._fe noattr) v_z2;
   lvar F._x2 (Tstruct F._fe noattr) v_x2;
   lvar F._x1 (Tstruct F._fe noattr) v_x1; temp F._out out;
   temp F._scalar s; temp F._point p)
  SEP (data_at Tsh t_limbs (map Vint (ls_z3 (gst3 e x1 (i - 1)))) v_z3;
   data_at Tsh t_limbs (map Vint (ls_x3 (gst3 e x1 (i - 1)))) v_x3;
   data_at Tsh t_limbs (map Vint x1) v_x1;
   data_at Tsh t_limbs (map Vint (ls_z2 (gst3 e x1 (i - 1)))) v_z2;
   data_at Tsh t_limbs (map Vint (ls_x2 (gst3 e x1 (i - 1)))) v_x2;
   data_at psh (tarray tuchar 32) (map Vubyte pt) p;
   data_at Tsh (tarray tuchar 32) (map Vubyte e) v_e;
   data_at ssh (tarray tuchar 32) (map Vubyte sc) s;
   data_at_ Tsh t_limbs v_tmp1l; data_at_ Tsh t_limbs v_tmp0l;
   data_at_ Tsh t_limbs v_tmp1; data_at_ Tsh t_limbs v_tmp0;
   data_at_ Tsh t_limbs v_x3l; data_at_ Tsh t_limbs v_z2l;
   data_at_ Tsh t_limbs v_x2l; data_at_ osh (tarray tuchar 32) out))%assert
 break: (
  PROP ()
  LOCAL (temp F._swap (Vint (ls_swap (gst3 e x1 (-1))));
   lvar F._tmp1l (Tstruct F._fe_loose noattr) v_tmp1l;
   lvar F._tmp0l (Tstruct F._fe_loose noattr) v_tmp0l;
   lvar F._tmp1 (Tstruct F._fe noattr) v_tmp1;
   lvar F._tmp0 (Tstruct F._fe noattr) v_tmp0;
   lvar F._e (tarray tuchar 32) v_e;
   lvar F._x3l (Tstruct F._fe_loose noattr) v_x3l;
   lvar F._z2l (Tstruct F._fe_loose noattr) v_z2l;
   lvar F._x2l (Tstruct F._fe_loose noattr) v_x2l;
   lvar F._z3 (Tstruct F._fe noattr) v_z3;
   lvar F._x3 (Tstruct F._fe noattr) v_x3;
   lvar F._z2 (Tstruct F._fe noattr) v_z2;
   lvar F._x2 (Tstruct F._fe noattr) v_x2;
   lvar F._x1 (Tstruct F._fe noattr) v_x1; temp F._out out;
   temp F._scalar s; temp F._point p)
  SEP (data_at Tsh t_limbs (map Vint (ls_z3 (gst3 e x1 (-1)))) v_z3;
   data_at Tsh t_limbs (map Vint (ls_x3 (gst3 e x1 (-1)))) v_x3;
   data_at Tsh t_limbs (map Vint x1) v_x1;
   data_at Tsh t_limbs (map Vint (ls_z2 (gst3 e x1 (-1)))) v_z2;
   data_at Tsh t_limbs (map Vint (ls_x2 (gst3 e x1 (-1)))) v_x2;
   data_at psh (tarray tuchar 32) (map Vubyte pt) p;
   data_at Tsh (tarray tuchar 32) (map Vubyte e) v_e;
   data_at ssh (tarray tuchar 32) (map Vubyte sc) s;
   data_at_ Tsh t_limbs v_tmp1l; data_at_ Tsh t_limbs v_tmp0l;
   data_at_ Tsh t_limbs v_tmp1; data_at_ Tsh t_limbs v_tmp0;
   data_at_ Tsh t_limbs v_x3l; data_at_ Tsh t_limbs v_z2l;
   data_at_ Tsh t_limbs v_x2l; data_at_ osh (tarray tuchar 32) out))%assert.
{ forward. Exists 254. entailer!. }
{ Intros i.
  forward_if.
  2: { assert (i = -1) by lia. subst i. forward. entailer!. }
  destruct (gst3_len e x1 i Hx1) as (Lx2 & Lz2 & Lx3 & Lz3).
  pose proof (gst3_next e x1 i) as Hnext.
  assert (Hle: Zlength e = 32) by (rewrite Ee; auto).
  remember (gst3 e x1 i) as st eqn:Est.
  clear Est Ee Ex1.
  assert (Hdiv: Int.divs (Int.repr i) (Int.repr 8) = Int.repr (i / 8)).
  1: (unfold Int.divs; rewrite !Int.signed_repr by rep_lia; rewrite Z.quot_div_nonneg by lia; auto).
  assert (Hi8: 0 <= i / 8 < 32) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  forward.
  1: (entailer!; rewrite Hdiv, Int.signed_repr by rep_lia; lia).
  1: (go_lower; rewrite Hdiv, Int.signed_repr by rep_lia; rewrite Znth_map by lia; apply prop_right;
     generalize (Znth (i / 8) e); intro b; pose proof (Byte.unsigned_range_2 b);
     simpl; rewrite Int.unsigned_repr by rep_lia; lia).
  1: entailer!.
  1: (match goal with Hx: _ /\ Int.repr 8 = Int.mone |- _ => destruct Hx as [_ Hx]; inv Hx end).
  rewrite Hdiv, Int.signed_repr by rep_lia. rewrite Znth_map by lia.
  assert (Hand: Int.and (Int.repr i) (Int.repr 7) = Int.repr (i mod 8)).
  { replace (Int.repr 7) with (Int.sub (Int.repr 8) Int.one) by reflexivity.
    rewrite <- (Int.modu_and _ _ (Int.repr 3)) by reflexivity.
    unfold Int.modu. rewrite !Int.unsigned_repr by rep_lia. reflexivity. }
  pose proof (Z.mod_pos_bound i 8 ltac:(lia)) as Hm8.
  forward.
  { entailer!. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
    rewrite Int.unsigned_repr by rep_lia. change (Int.unsigned Int.iwordsize) with 32; lia. }
  replace (Int.and (Int.repr 1) (Int.shr (Int.repr (Byte.unsigned (Znth (i / 8) e)))
             (Int.and (Int.repr i) (Int.repr 7)))) with (ladder_bit e i) by reflexivity.
  set (b := ladder_bit e i).
  forward.
  set (sw := Int.xor (ls_swap st) b).
  forward_call (Tsh, v_x2, ls_x2 st, Tsh, v_x3, ls_x3 st, sw).
  set (X2 := fst (fe_cswap_m (ls_x2 st) (ls_x3 st) sw)).
  set (X3 := snd (fe_cswap_m (ls_x2 st) (ls_x3 st) sw)).
  assert (LX2: Zlength X2 = 10) by apply fe_cswap1_len3.
  assert (LX3: Zlength X3 = 10) by apply fe_cswap2_len3.
  forward_call (Tsh, v_z2, ls_z2 st, Tsh, v_z3, ls_z3 st, sw).
  set (Z2 := fst (fe_cswap_m (ls_z2 st) (ls_z3 st) sw)).
  set (Z3 := snd (fe_cswap_m (ls_z2 st) (ls_z3 st) sw)).
  assert (LZ2: Zlength Z2 = 10) by apply fe_cswap1_len3.
  assert (LZ3: Zlength Z3 = 10) by apply fe_cswap2_len3.
  forward.
  forward_call (Tsh, v_tmp0l, Tsh, v_x3, X3, Tsh, v_z3, Z3).
  assert (LT0L: Zlength (fe_sub_m X3 Z3) = 10) by apply fe_sub_len3. nm3 (fe_sub_m X3 Z3) T0L ET0L.
  forward_call (Tsh, v_tmp1l, Tsh, v_x2, X2, Tsh, v_z2, Z2).
  assert (LT1L: Zlength (fe_sub_m X2 Z2) = 10) by apply fe_sub_len3. nm3 (fe_sub_m X2 Z2) T1L ET1L.
  forward_call (Tsh, v_x2l, Tsh, v_x2, X2, Tsh, v_z2, Z2).
  assert (LX2L: Zlength (fe_add_m X2 Z2) = 10) by apply fe_add_len3. nm3 (fe_add_m X2 Z2) X2L EX2L.
  forward_call (Tsh, v_z2l, Tsh, v_x3, X3, Tsh, v_z3, Z3).
  assert (LZ2L: Zlength (fe_add_m X3 Z3) = 10) by apply fe_add_len3. nm3 (fe_add_m X3 Z3) Z2L EZ2L.
  undat3 v_z3.
  forward_call (FA_none, Tsh, v_z3, Tsh, v_tmp0l, T0L, Tsh, v_x2l, X2L).
  1: (unfold fe3_pre; cancel).
  post3.
  assert (LZ3a: Zlength (fe_mul_m T0L X2L) = 10) by apply fe_mul_len3. nm3 (fe_mul_m T0L X2L) Z3a EZ3a.
  undat3 v_z2.
  forward_call (FA_none, Tsh, v_z2, Tsh, v_z2l, Z2L, Tsh, v_tmp1l, T1L).
  1: (unfold fe3_pre; cancel).
  post3.
  assert (LZ2a: Zlength (fe_mul_m Z2L T1L) = 10) by apply fe_mul_len3. nm3 (fe_mul_m Z2L T1L) Z2a EZ2a.
  forward_call (FS_none, Tsh, v_tmp0, Tsh, v_tmp1l, T1L).
  1: (unfold fe2_pre; cancel).
  post3.
  assert (LT0: Zlength (fe_sqr_m T1L) = 10) by apply fe_sqr_len3. nm3 (fe_sqr_m T1L) T0 ET0.
  forward_call (FS_none, Tsh, v_tmp1, Tsh, v_x2l, X2L).
  1: (unfold fe2_pre; cancel).
  post3.
  assert (LT1: Zlength (fe_sqr_m X2L) = 10) by apply fe_sqr_len3. nm3 (fe_sqr_m X2L) T1 ET1.
  forward_call (Tsh, v_x3l, Tsh, v_z3, Z3a, Tsh, v_z2, Z2a).
  assert (LX3L: Zlength (fe_add_m Z3a Z2a) = 10) by apply fe_add_len3. nm3 (fe_add_m Z3a Z2a) X3L EX3L.
  undat3 v_z2l.
  forward_call (Tsh, v_z2l, Tsh, v_z3, Z3a, Tsh, v_z2, Z2a).
  assert (LZ2L': Zlength (fe_sub_m Z3a Z2a) = 10) by apply fe_sub_len3. nm3 (fe_sub_m Z3a Z2a) Z2L' EZ2L'.
  undat3 v_x2.
  forward_call (FA_none, Tsh, v_x2, Tsh, v_tmp1, T1, Tsh, v_tmp0, T0).
  1: (unfold fe3_pre; cancel).
  post3.
  assert (LX2b: Zlength (fe_mul_m T1 T0) = 10) by apply fe_mul_len3. nm3 (fe_mul_m T1 T0) X2b EX2b.
  undat3 v_tmp1l.
  forward_call (Tsh, v_tmp1l, Tsh, v_tmp1, T1, Tsh, v_tmp0, T0).
  assert (LT1L': Zlength (fe_sub_m T1 T0) = 10) by apply fe_sub_len3. nm3 (fe_sub_m T1 T0) T1L' ET1L'.
  undat3 v_z2.
  forward_call (FS_none, Tsh, v_z2, Tsh, v_z2l, Z2L').
  1: (unfold fe2_pre; cancel).
  post3.
  assert (LZ2b: Zlength (fe_sqr_m Z2L') = 10) by apply fe_sqr_len3. nm3 (fe_sqr_m Z2L') Z2b EZ2b.
  undat3 v_z3.
  forward_call (Tsh, v_z3, Tsh, v_tmp1l, T1L').
  assert (LZ3b: Zlength (fe_mul121666_m T1L') = 10) by apply fe_mul121666_len3. nm3 (fe_mul121666_m T1L') Z3b EZ3b.
  undat3 v_x3.
  forward_call (FS_none, Tsh, v_x3, Tsh, v_x3l, X3L).
  1: (unfold fe2_pre; cancel).
  post3.
  assert (LX3b: Zlength (fe_sqr_m X3L) = 10) by apply fe_sqr_len3. nm3 (fe_sqr_m X3L) X3b EX3b.
  undat3 v_tmp0l.
  forward_call (Tsh, v_tmp0l, Tsh, v_tmp0, T0, Tsh, v_z3, Z3b).
  assert (LT0L': Zlength (fe_add_m T0 Z3b) = 10) by apply fe_add_len3. nm3 (fe_add_m T0 Z3b) T0L' ET0L'.
  undat3 v_z3.
  forward_call (FA_none, Tsh, v_z3, Tsh, v_x1, x1, Tsh, v_z2, Z2b).
  1: (unfold fe3_pre; cancel).
  post3.
  assert (LZ3c: Zlength (fe_mul_m x1 Z2b) = 10) by apply fe_mul_len3. nm3 (fe_mul_m x1 Z2b) Z3c EZ3c.
  undat3 v_z2.
  forward_call (FA_none, Tsh, v_z2, Tsh, v_tmp1l, T1L', Tsh, v_tmp0l, T0L').
  1: (unfold fe3_pre; cancel).
  post3.
  assert (LZ2c: Zlength (fe_mul_m T1L' T0L') = 10) by apply fe_mul_len3. nm3 (fe_mul_m T1L' T0L') Z2c EZ2c.
  Exists i.
  assert (Hstep: ladder_step e x1 i st = mk_ls X2b Z2c X3b Z3c b).
  { unfold hide3 in *.
    subst Z2c Z3c T0L' X3b Z3b Z2b T1L' X2b Z2L' X3L T1 T0 Z2a Z3a Z2L X2L T1L T0L.
    reflexivity. }
  rewrite (Hnext ltac:(lia)), Hstep. cbn [ls_x2 ls_z2 ls_x3 ls_z3 ls_swap].
  entailer!. }
{ Intros i. forward. Exists (i - 1). entailer!. }
destruct (gst3_len e x1 (-1) Hx1) as (Lx2 & Lz2 & Lx3 & Lz3).
assert (Hres: x25519_m sc pt =
  fe_tobytes_m (fe_mul_m (fst (fe_cswap_m (ls_x2 (gst3 e x1 (-1))) (ls_x3 (gst3 e x1 (-1))) (ls_swap (gst3 e x1 (-1)))))
     (fe_invert_m (fst (fe_cswap_m (ls_z2 (gst3 e x1 (-1))) (ls_z3 (gst3 e x1 (-1))) (ls_swap (gst3 e x1 (-1))))))))
  by (subst e x1; reflexivity).
remember (gst3 e x1 (-1)) as st eqn:Est.
clear Est.
forward_call (Tsh, v_x2, ls_x2 st, Tsh, v_x3, ls_x3 st, ls_swap st).
forward_call (Tsh, v_z2, ls_z2 st, Tsh, v_z3, ls_z3 st, ls_swap st).
assert (LX2: Zlength (fst (fe_cswap_m (ls_x2 st) (ls_x3 st) (ls_swap st))) = 10) by apply fe_cswap1_len3.
assert (LZ2: Zlength (fst (fe_cswap_m (ls_z2 st) (ls_z3 st) (ls_swap st))) = 10) by apply fe_cswap1_len3.
nm3 (fst (fe_cswap_m (ls_x2 st) (ls_x3 st) (ls_swap st))) X2 EX2.
nm3 (snd (fe_cswap_m (ls_x2 st) (ls_x3 st) (ls_swap st))) X3 EX3.
nm3 (fst (fe_cswap_m (ls_z2 st) (ls_z3 st) (ls_swap st))) Z2 EZ2.
nm3 (snd (fe_cswap_m (ls_z2 st) (ls_z3 st) (ls_swap st))) Z3 EZ3.
forward_call (Tsh, v_z2, Z2).
assert (LZ2i: Zlength (fe_invert_m Z2) = 10) by apply fe_invert_len3.
nm3 (fe_invert_m Z2) Z2i EZ2i.
forward_call (FA_out1, Tsh, v_x2, Tsh, v_x2, X2, Tsh, v_z2, Z2i).
1: (unfold fe3_pre; cancel).
post3.
assert (LX2r: Zlength (fe_mul_m X2 Z2i) = 10) by apply fe_mul_len3.
nm3 (fe_mul_m X2 Z2i) X2r EX2r.
forward_call (osh, out, Tsh, v_x2, X2r).
assert (Hout: fe_tobytes_m X2r = x25519_m sc pt).
{ rewrite Hres. unfold hide3 in *. subst X2r Z2i X2 Z2. reflexivity. }
clear Hres. change (hide3 (fe_tobytes_m X2r = x25519_m sc pt)) in Hout.
change (hide3 (e = clamp sc)) in Ee. change (hide3 (x1 = fe_frombytes_m pt)) in Ex1.
mz3 v_x1. mz3 v_x2. mz3 v_z2. mz3 v_x3. mz3 v_z3. mz3 v_x2l. mz3 v_z2l. mz3 v_x3l.
sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (map Vubyte e) v_e).
forward_call (Tsh, v_e, 32).
rewrite <- (fe_limbs3 Tsh v_x1), <- (fe_limbs3 Tsh v_x2), <- (fe_limbs3 Tsh v_z2), <- (fe_limbs3 Tsh v_x3),
  <- (fe_limbs3 Tsh v_z3), <- (fe_limbs3 Tsh v_tmp0), <- (fe_limbs3 Tsh v_tmp1) by assumption.
rewrite <- (fel_limbs3 Tsh v_x2l), <- (fel_limbs3 Tsh v_z2l), <- (fel_limbs3 Tsh v_x3l),
  <- (fel_limbs3 Tsh v_tmp0l), <- (fel_limbs3 Tsh v_tmp1l) by assumption.
unfold hide3 in Hout. rewrite Hout.
entailer!.
Qed.
