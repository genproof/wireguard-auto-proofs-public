(* hrp_init_r's value is aead_model's p1305_r. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.aead.aead_model.
Require Import WgNoise.proof.harness.hrp1305_math3.

Local Open Scope Z_scope.

Lemma hpr_land_split a y M : 0 <= a < 256 -> 0 <= y -> 0 <= M ->
  Z.land (a + 256 * y) M = Z.land a (M mod 256) + 256 * Z.land y (M / 256).
Proof.
  intros Ha Hy HM.
  set (X := a + 256 * y).
  assert (HX0: 0 <= X) by (subst X; lia).
  assert (HXm: X mod 256 = a) by (subst X; rewrite Z.add_mod, Z.mul_comm, Z.mod_mul, Z.add_0_r, !Z.mod_mod,
    Z.mod_small by lia; auto; lia).
  assert (HXd: X / 256 = y) by (subst X; rewrite Z.mul_comm, Z.div_add, Z.div_small by lia; lia).
  rewrite (Z.div_mod (Z.land X M) 256) by lia.
  assert (E1: Z.land X M mod 256 = Z.land a (M mod 256)).
  { change 256 with (2 ^ 8). rewrite <- !Z.land_ones by lia.
    rewrite <- HXm. change 256 with (2 ^ 8). rewrite <- !Z.land_ones by lia.
    rewrite <- !Z.land_assoc. f_equal.
    rewrite (Z.land_comm M (Z.ones 8)), Z.land_assoc, Z.land_diag. reflexivity. }
  assert (E2: Z.land X M / 256 = Z.land y (M / 256)).
  { change 256 with (2 ^ 8). rewrite <- !Z.shiftr_div_pow2 by lia.
    rewrite Z.shiftr_land. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. rewrite HXd. reflexivity. }
  rewrite E1, E2. lia.
Qed.

Lemma hpr_land_lt256 x m : 0 <= x -> 0 <= m < 256 -> 0 <= Z.land x m < 256.
Proof.
  intros Hx Hm.
  assert (Em: m = Z.land m (Z.ones 8)) by (rewrite Z.land_ones by lia; rewrite Z.mod_small; lia).
  rewrite Em, Z.land_assoc, Z.land_ones by lia.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma hpr_and_u8 b m : 0 <= m < 256 ->
  Int.unsigned (Int.and (hrp_u8 b) (Int.repr m)) = Z.land (Byte.unsigned b) m.
Proof.
  intros Hm. unfold Int.and, hrp_u8. rewrite (Int.unsigned_repr (Byte.unsigned b)), (Int.unsigned_repr m) by rep_lia.
  apply Int.unsigned_repr. pose proof (hpr_land_lt256 (Byte.unsigned b) m ltac:(rep_lia) Hm). rep_lia.
Qed.

Lemma hpr_land_byte b : Z.land (Byte.unsigned b) 255 = Byte.unsigned b.
Proof.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. rep_lia.
Qed.

Lemma hpr_u8 b : Int.unsigned (hrp_u8 b) = Byte.unsigned b.
Proof. unfold hrp_u8. apply Int.unsigned_repr. rep_lia. Qed.

Lemma hpr_mask_shape (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16: int) :
  hrp_mask 15 15 (hrp_mask 12 252 (hrp_mask 11 15 (hrp_mask 8 252 (hrp_mask 7 15 (hrp_mask 4 252
    (hrp_mask 3 15 [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16])))))) =
  [x0; x1; x2; Int.and x3 (Int.repr 15); Int.and x4 (Int.repr 252); x5; x6; Int.and x7 (Int.repr 15);
   Int.and x8 (Int.repr 252); x9; x10; Int.and x11 (Int.repr 15); Int.and x12 (Int.repr 252); x13; x14;
   Int.and x15 (Int.repr 15); x16].
Proof. reflexivity. Qed.

Lemma hpr_init_r_ok key : 16 <= Zlength key ->
  Zlength (hrp_init_r key) = 17 /\ Forall (fun w => Int.unsigned w <= 255) (hrp_init_r key) /\
  hrp_val (hrp_init_r key) = p1305_r key.
Proof.
  intros Hk. unfold hrp_init_r, p1305_r.
  assert (Hl: Zlength (sublist 0 16 key) = 16) by (rewrite Zlength_sublist; lia).
  destruct (sublist 0 16 key) as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 [|b9 [|b10 [|b11 [|b12 [|b13
    [|b14 [|b15 [|b16 l]]]]]]]]]]]]]]]]];
    try (rewrite Zlength_correct in Hl; simpl length in Hl; lia).
  clear Hl Hk.
  cbn [map app]. rewrite hpr_mask_shape.
  repeat split.
  - repeat constructor; rewrite ?hpr_and_u8, ?hpr_u8, ?Int.unsigned_zero by lia; try rep_lia;
      match goal with |- Z.land (Byte.unsigned ?b) ?m <= 255 =>
        pose proof (hpr_land_lt256 (Byte.unsigned b) m ltac:(rep_lia) ltac:(lia)); lia end.
  - cbn [le_Z hrp_val].
    repeat (rewrite hpr_land_split at 1; [ | rep_lia | rep_lia | lia ];
      repeat match goal with |- context [?M / 256] =>
        let v := eval vm_compute in (M / 256) in change (M / 256) with v end;
      repeat match goal with |- context [?M mod 256] =>
        let v := eval vm_compute in (M mod 256) in change (M mod 256) with v end).
    rewrite ?hpr_and_u8, ?hpr_u8, ?Int.unsigned_zero by lia. rewrite ?hpr_land_byte. rewrite ?Z.land_0_l. lia.
Qed.
