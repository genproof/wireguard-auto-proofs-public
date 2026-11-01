(* part of x25519_part3: the body of fe_loose_invert (squaring loops: fe_sqn_m).
   Specifications: x25519_spec.v, model: x25519_model.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.x25519.x25519_spec.

#[local] Existing Instance Curve25519Fiat32.CS.

Lemma fe_mul_m_len3 : forall f g, Zlength (fe_mul_m f g) = 10.
Proof. intros. unfold fe_mul_m. reflexivity. Qed.

Lemma fe_sqr_m_len3 : forall f, Zlength (fe_sqr_m f) = 10.
Proof. intros. unfold fe_sqr_m. reflexivity. Qed.

Lemma fe_sqn_m_len3 : forall n f, Zlength f = 10 -> Zlength (fe_sqn_m n f) = 10.
Proof. intros n f H. destruct n; [exact H | ]. unfold fe_sqn_m. simpl Nat.iter. apply fe_sqr_m_len3. Qed.

Lemma fe_sqn_m_S3 : forall n f, fe_sqn_m (S n) f = fe_sqr_m (fe_sqn_m n f).
Proof. intros. reflexivity. Qed.

Lemma fe_limbs3 : forall sh p, field_compatible t_fe nil p -> data_at_ sh (Tstruct F._fe noattr) p = data_at_ sh t_limbs p.
Proof.
  intros sh p H. rewrite !data_at__memory_block. f_equal. f_equal.
  apply prop_ext; split; intros _; auto.
  assert (H1: field_compatible t_fe (DOT F._v) p).
  { apply field_compatible_cons. split; [ | exact H]. unfold t_fe; simpl. left; reflexivity. }
  apply field_compatible_nested_field in H1. unfold t_fe in H1. simpl in H1.
  rewrite isptr_offset_val_zero in H1 by (destruct H; tauto). exact H1.
Qed.

Definition is3 (x y: list int) : Prop := x = y.

Ltac side3 := first [ solve [ cbn [fe2_pre fe3_pre]; cancel ] | idtac ].

Ltac drop_i3 Q :=
  match Q with
  | temp F._i _ :: ?r => r
  | ?x :: ?r => let r' := drop_i3 r in constr:(x :: r')
  | nil => constr:(@nil localdef)
  end.

(* for (i = 1; i < n; ++i) fe_sq_tt(&t, &t);  with t's limbs the atom a at v: b = fe_sqn_m (n-1) a *)
Ltac sqloop_inv3 n a :=
  match goal with |- semax _ (PROPx nil (LOCALx ?Q (SEPx ?R))) _ _ =>
    let Q' := drop_i3 Q in
    match eval pattern a in R with ?F _ =>
      forward_for_simple_bound n (EX i:Z, PROP () (LOCALx Q' (SEPx (F (fe_sqn_m (Z.to_nat (i-1)) a)))))%assert
    end
  end.

Tactic Notation "sqloop3" constr(n) constr(v) constr(a) "as" ident(b) ident(Eb) ident(Lb) :=
  sqloop_inv3 n a;
  [ change (fe_sqn_m (Z.to_nat (1 - 1)) a) with a; entailer!
  | match goal with |- semax _ (PROPx _ (LOCALx (temp F._i (Vint (Int.repr ?j)) :: _) _)) _ _ =>
      assert (Zlength (fe_sqn_m (Z.to_nat (j-1)) a) = 10) by (apply fe_sqn_m_len3; auto);
      forward_call (FS_out, Tsh, v, Tsh, v, fe_sqn_m (Z.to_nat (j-1)) a); [ side3 .. ];
      cbn [fe2_post];
      replace (Z.to_nat (j+1-1)) with (S (Z.to_nat (j-1))) by lia; rewrite fe_sqn_m_S3; entailer!
    end
  | let k := eval compute in (Z.to_nat (n - 1)) in change (Z.to_nat (n - 1)) with k;
    remember (fe_sqn_m k a) as b eqn:Eb; change (is3 b (fe_sqn_m k a)) in Eb;
    assert (Lb: Zlength b = 10) by (rewrite Eb; apply fe_sqn_m_len3; auto) ].

Tactic Notation "sq3" constr(m) constr(osh) constr(out) constr(ish) constr(inp) constr(a)
    "as" ident(b) ident(Eb) ident(Lb) :=
  forward_call (m, osh, out, ish, inp, a); [ side3 .. ];
  remember (fe_sqr_m a) as b eqn:Eb; change (is3 b (fe_sqr_m a)) in Eb;
  cbn [fe2_post]; repeat flatten_sepcon_in_SEP;
  assert (Lb: Zlength b = 10) by (rewrite Eb; apply fe_sqr_m_len3).

Tactic Notation "mul3" constr(m) constr(osh) constr(out) constr(sh1) constr(in1) constr(a)
    constr(sh2) constr(in2) constr(c) "as" ident(b) ident(Eb) ident(Lb) :=
  forward_call (m, osh, out, sh1, in1, a, sh2, in2, c); [ side3 .. ];
  remember (fe_mul_m a c) as b eqn:Eb; change (is3 b (fe_mul_m a c)) in Eb;
  cbn [fe3_post]; repeat flatten_sepcon_in_SEP;
  assert (Lb: Zlength b = 10) by (rewrite Eb; apply fe_mul_m_len3).

Theorem x25519_invert3 : semax_body x25_V x25_Gprog F.f_fe_loose_invert fe_loose_invert_spec.
Proof.
  start_function.
  assert_PROP (field_compatible t_fe nil v_t0 /\ field_compatible t_fe nil v_t1 /\
               field_compatible t_fe nil v_t2 /\ field_compatible t_fe nil v_t3) by entailer!.
  destruct H0 as [FC0 [FC1 [FC2 FC3]]].
  rewrite (fe_limbs3 Tsh v_t0 FC0), (fe_limbs3 Tsh v_t1 FC1), (fe_limbs3 Tsh v_t2 FC2), (fe_limbs3 Tsh v_t3 FC3).
  sq3 FS_none Tsh v_t0 sh1 in1 f as a0 E0 L0.
  sq3 FS_none Tsh v_t1 Tsh v_t0 a0 as a1 E1 L1.
  sqloop3 2 v_t1 a1 as a2 E2 L2.
  mul3 FA_out2 Tsh v_t1 sh1 in1 f Tsh v_t1 a2 as a3 E3 L3.
  mul3 FA_out1 Tsh v_t0 Tsh v_t0 a0 Tsh v_t1 a3 as a4 E4 L4.
  sq3 FS_none Tsh v_t2 Tsh v_t0 a4 as a5 E5 L5.
  mul3 FA_out1 Tsh v_t1 Tsh v_t1 a3 Tsh v_t2 a5 as a6 E6 L6.
  sq3 FS_none Tsh v_t2 Tsh v_t1 a6 as a7 E7 L7.
  sqloop3 5 v_t2 a7 as a8 E8 L8.
  mul3 FA_out2 Tsh v_t1 Tsh v_t2 a8 Tsh v_t1 a6 as a9 E9 L9.
  sq3 FS_none Tsh v_t2 Tsh v_t1 a9 as a10 E10 L10.
  sqloop3 10 v_t2 a10 as a11 E11 L11.
  mul3 FA_out1 Tsh v_t2 Tsh v_t2 a11 Tsh v_t1 a9 as a12 E12 L12.
  sq3 FS_none Tsh v_t3 Tsh v_t2 a12 as a13 E13 L13.
  sqloop3 20 v_t3 a13 as a14 E14 L14.
  mul3 FA_out2 Tsh v_t2 Tsh v_t3 a14 Tsh v_t2 a12 as a15 E15 L15.
  sq3 FS_out Tsh v_t2 Tsh v_t2 a15 as a16 E16 L16.
  sqloop3 10 v_t2 a16 as a17 E17 L17.
  mul3 FA_out2 Tsh v_t1 Tsh v_t2 a17 Tsh v_t1 a9 as a18 E18 L18.
  sq3 FS_none Tsh v_t2 Tsh v_t1 a18 as a19 E19 L19.
  sqloop3 50 v_t2 a19 as a20 E20 L20.
  mul3 FA_out1 Tsh v_t2 Tsh v_t2 a20 Tsh v_t1 a18 as a21 E21 L21.
  sq3 FS_none Tsh v_t3 Tsh v_t2 a21 as a22 E22 L22.
  sqloop3 100 v_t3 a22 as a23 E23 L23.
  mul3 FA_out2 Tsh v_t2 Tsh v_t3 a23 Tsh v_t2 a21 as a24 E24 L24.
  sq3 FS_out Tsh v_t2 Tsh v_t2 a24 as a25 E25 L25.
  sqloop3 50 v_t2 a25 as a26 E26 L26.
  mul3 FA_out2 Tsh v_t1 Tsh v_t2 a26 Tsh v_t1 a18 as a27 E27 L27.
  sq3 FS_out Tsh v_t1 Tsh v_t1 a27 as a28 E28 L28.
  sqloop3 5 v_t1 a28 as a29 E29 L29.
  mul3 FA_none osh out Tsh v_t1 a29 Tsh v_t0 a4 as a30 E30 L30.
  assert (Hfin: a30 = fe_loose_invert_m f).
  { unfold is3 in *. subst. unfold fe_loose_invert_m. reflexivity. }
  rewrite Hfin. clear E30. entailer!.
  rewrite (fe_limbs3 Tsh v_t0 FC0), (fe_limbs3 Tsh v_t1 FC1), (fe_limbs3 Tsh v_t2 FC2), (fe_limbs3 Tsh v_t3 FC3).
  cancel.
Qed.
