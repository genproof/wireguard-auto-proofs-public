(* Field elements of curve25519-fiat32.c as the model represents them (10 limbs of 26/25 bits, list int):
   their value, the bounds the code keeps, and the limb-wise operations fe_add / fe_sub / fe_cswap.
   VST-side file: no fiat-crypto here. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.x25519.x25519_model.

Local Open Scope Z_scope.

Definition P25519 : Z := 2 ^ 255 - 19.

(* the value of 10 limbs (radix 2^25.5: limb i has weight 2^ceil(25.5 i)) *)
Definition fevalZ (l: list Z) : Z :=
  match l with
  | [a0; a1; a2; a3; a4; a5; a6; a7; a8; a9] =>
      a0 + 2^26 * a1 + 2^51 * a2 + 2^77 * a3 + 2^102 * a4 + 2^128 * a5 + 2^153 * a6 + 2^179 * a7
      + 2^204 * a8 + 2^230 * a9
  | _ => 0
  end.
Definition feval (h: list int) : Z := fevalZ (map Int.unsigned h).

(* limb-wise upper bounds *)
Definition bounded (B: list Z) (h: list int) : Prop := Forall2 (fun b x => Int.unsigned x <= b) B h.

(* tight: 1.125 * 2^26 / 1.125 * 2^25 (outputs of mul/sqr/frombytes); loose: fe_sub_bias + tight
   (outputs of add/sub of tight inputs; accepted by mul/sqr) *)
Definition tight : list Z :=
  [75497472; 37748736; 75497472; 37748736; 75497472; 37748736; 75497472; 37748736; 75497472; 37748736].
Definition loose : list Z :=
  [209715162; 104857598; 209715198; 104857598; 209715198; 104857598; 209715198; 104857598; 209715198;
   104857598].

Lemma bounded_length B h : bounded B h -> length h = length B.
Proof. intros H. symmetry. eapply Forall2_length; eauto. Qed.

Lemma bounded_10 B h : length B = 10%nat -> bounded B h ->
  exists h0 h1 h2 h3 h4 h5 h6 h7 h8 h9, h = [h0; h1; h2; h3; h4; h5; h6; h7; h8; h9].
Proof.
  intros L H. pose proof (bounded_length _ _ H) as E. rewrite L in E.
  do 10 (destruct h as [|? h]; [discriminate|]). destruct h; [|discriminate]. eauto 20.
Qed.

Lemma bounded_Znth B h : bounded B h -> forall i, 0 <= i < Zlength B -> Int.unsigned (Znth i h) <= Znth i B.
Proof.
  induction 1; intros i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi. destruct (zeq i 0).
    + subst. rewrite !Znth_0_cons. auto.
    + rewrite !Znth_pos_cons by lia. apply IHForall2. lia.
Qed.

Lemma bounded_weaken B B' h : Forall2 Z.le B B' -> bounded B h -> bounded B' h.
Proof.
  unfold bounded. intros HB. revert h. induction HB as [|b b' B B' Hb HB IH]; intros h Hh.
  - inversion Hh; constructor.
  - inversion Hh; subst. constructor; [lia | apply IH; assumption].
Qed.

Lemma tight_loose h : bounded tight h -> bounded loose h.
Proof. apply bounded_weaken. repeat constructor; cbv; discriminate. Qed.

Lemma bounded_range B h : bounded B h -> Forall (fun x => 0 <= Int.unsigned x) h.
Proof. induction 1; constructor; auto. apply Int.unsigned_range. Qed.

Lemma Znth10_0 {A} {d: Inhabitant A} (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : A) : Znth 0 [a0; a1; a2; a3; a4; a5; a6; a7; a8; a9] = a0.
Proof. reflexivity. Qed.
Lemma Znth10_1 {A} {d: Inhabitant A} (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : A) : Znth 1 [a0; a1; a2; a3; a4; a5; a6; a7; a8; a9] = a1.
Proof. reflexivity. Qed.
Lemma Znth10_2 {A} {d: Inhabitant A} (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : A) : Znth 2 [a0; a1; a2; a3; a4; a5; a6; a7; a8; a9] = a2.
Proof. reflexivity. Qed.
Lemma Znth10_3 {A} {d: Inhabitant A} (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : A) : Znth 3 [a0; a1; a2; a3; a4; a5; a6; a7; a8; a9] = a3.
Proof. reflexivity. Qed.
Lemma Znth10_4 {A} {d: Inhabitant A} (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : A) : Znth 4 [a0; a1; a2; a3; a4; a5; a6; a7; a8; a9] = a4.
Proof. reflexivity. Qed.
Lemma Znth10_5 {A} {d: Inhabitant A} (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : A) : Znth 5 [a0; a1; a2; a3; a4; a5; a6; a7; a8; a9] = a5.
Proof. reflexivity. Qed.
Lemma Znth10_6 {A} {d: Inhabitant A} (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : A) : Znth 6 [a0; a1; a2; a3; a4; a5; a6; a7; a8; a9] = a6.
Proof. reflexivity. Qed.
Lemma Znth10_7 {A} {d: Inhabitant A} (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : A) : Znth 7 [a0; a1; a2; a3; a4; a5; a6; a7; a8; a9] = a7.
Proof. reflexivity. Qed.
Lemma Znth10_8 {A} {d: Inhabitant A} (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : A) : Znth 8 [a0; a1; a2; a3; a4; a5; a6; a7; a8; a9] = a8.
Proof. reflexivity. Qed.
Lemma Znth10_9 {A} {d: Inhabitant A} (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : A) : Znth 9 [a0; a1; a2; a3; a4; a5; a6; a7; a8; a9] = a9.
Proof. reflexivity. Qed.

Ltac znth10 := rewrite ?Znth10_0, ?Znth10_1, ?Znth10_2, ?Znth10_3, ?Znth10_4, ?Znth10_5, ?Znth10_6,
  ?Znth10_7, ?Znth10_8, ?Znth10_9.

(* ------------------------------------------------------------------ *)
(* fe_add / fe_sub                                                     *)
(* ------------------------------------------------------------------ *)

Lemma upto_10 : upto 10 = [0; 1; 2; 3; 4; 5; 6; 7; 8; 9].
Proof. reflexivity. Qed.

Lemma add_nowrap (a b: int) : Int.unsigned a + Int.unsigned b < Int.modulus ->
  Int.unsigned (Int.add a b) = Int.unsigned a + Int.unsigned b.
Proof.
  intros. unfold Int.add. apply Int.unsigned_repr.
  pose proof (Int.unsigned_range a); pose proof (Int.unsigned_range b). unfold Int.max_unsigned. lia.
Qed.

Lemma sub_nowrap (a b: int) : 0 <= Int.unsigned a - Int.unsigned b ->
  Int.unsigned (Int.sub a b) = Int.unsigned a - Int.unsigned b.
Proof.
  intros. unfold Int.sub. apply Int.unsigned_repr.
  pose proof (Int.unsigned_range a); pose proof (Int.unsigned_range b). unfold Int.max_unsigned. lia.
Qed.

Ltac destruct10 h :=
  let H := fresh in
  match goal with B: bounded ?T h |- _ =>
    destruct (bounded_10 T h eq_refl B) as (?&?&?&?&?&?&?&?&?&?&H); subst h
  end.

Ltac bnd_limbs B :=
  unfold bounded, tight, loose in B; repeat match type of B with
  | Forall2 _ (_ :: _) (_ :: _) => let H := fresh "Bl" in apply Forall2_cons_iff in B; destruct B as [H B]
  | Forall2 _ [] [] => clear B
  end.

Lemma fe_add_ok f g : bounded tight f -> bounded tight g ->
  bounded loose (fe_add_m f g) /\ feval (fe_add_m f g) = feval f + feval g.
Proof.
  intros Hf Hg. destruct10 f. destruct10 g. bnd_limbs Hf. bnd_limbs Hg.
  unfold fe_add_m. rewrite upto_10. simpl map. unfold Znth. simpl.
  split.
  - unfold bounded, loose. repeat constructor; rewrite add_nowrap by (change Int.modulus with (2^32); rep_lia); rep_lia.
  - unfold feval. cbn [map fevalZ]. rewrite !add_nowrap by (change Int.modulus with (2^32); rep_lia). ring.
Qed.

Lemma fe_sub_ok f g : bounded tight f -> bounded tight g ->
  bounded loose (fe_sub_m f g) /\ feval (fe_sub_m f g) = 2 * P25519 + feval f - feval g.
Proof.
  intros Hf Hg. destruct10 f. destruct10 g. bnd_limbs Hf. bnd_limbs Hg.
  unfold fe_sub_m, fe_sub_bias. rewrite upto_10. simpl map. unfold Znth. simpl.
  assert (S: forall (c: Z) (a b: int), 0 <= c <= 134217726 -> Int.unsigned a <= 75497472 ->
            Int.unsigned b <= c ->
            Int.unsigned (Int.sub (Int.add (Int.repr c) a) b) = c + Int.unsigned a - Int.unsigned b).
  { intros c a b Hc Ha Hb. rewrite sub_nowrap; rewrite add_nowrap; rewrite ?Int.unsigned_repr; rep_lia. }
  split.
  - unfold bounded, loose. repeat constructor; rewrite S by rep_lia; rep_lia.
  - unfold feval, P25519. cbn [map fevalZ]. rewrite !S by rep_lia. ring.
Qed.

(* ------------------------------------------------------------------ *)
(* fe_cswap                                                            *)
(* ------------------------------------------------------------------ *)

Lemma map_Znth_10 (f: list int) : length f = 10%nat ->
  map (fun i => Znth i f) (upto 10) = f.
Proof.
  intros L. do 10 (destruct f as [|? f]; [discriminate|]). destruct f; [|discriminate]. reflexivity.
Qed.

Lemma fe_cswap_ok f g (b: bool) : length f = 10%nat -> length g = 10%nat ->
  fe_cswap_m f g (if b then Int.one else Int.zero) = if b then (g, f) else (f, g).
Proof.
  intros Lf Lg. unfold fe_cswap_m, cswap_x. destruct b.
  - replace (Int.sub Int.zero Int.one) with Int.mone by reflexivity.
    f_equal.
    + transitivity (map (fun i => Znth i g) (upto 10)); [|apply map_Znth_10; auto].
      apply map_ext. intros i.
      rewrite Int.and_mone, <- Int.xor_assoc, Int.xor_idem, Int.xor_zero_l. reflexivity.
    + transitivity (map (fun i => Znth i f) (upto 10)); [|apply map_Znth_10; auto].
      apply map_ext. intros i.
      rewrite Int.and_mone, (Int.xor_commut (Znth i f)), <- Int.xor_assoc, Int.xor_idem,
        Int.xor_zero_l. reflexivity.
  - replace (Int.sub Int.zero Int.zero) with Int.zero by reflexivity.
    f_equal.
    + transitivity (map (fun i => Znth i f) (upto 10)); [|apply map_Znth_10; auto].
      apply map_ext. intros i. rewrite Int.and_zero, Int.xor_zero. reflexivity.
    + transitivity (map (fun i => Znth i g) (upto 10)); [|apply map_Znth_10; auto].
      apply map_ext. intros i. rewrite Int.and_zero, Int.xor_zero. reflexivity.
Qed.
