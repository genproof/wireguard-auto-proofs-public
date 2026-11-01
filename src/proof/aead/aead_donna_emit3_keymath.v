(* poly1305_core_setkey, the pure part: the five
   26-bit limbs that the C code extracts with get_unaligned_le32 at offsets 0, 3, 6, 9, 12, a shift and a
   mask are the limbs of the clamped r = p1305_r rk (p1305_r_limbs). *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.aead.aead_model.
Require Import WgNoise.proof.aead.aead_spec.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* bits of a + 2^k Y                                                       *)
(* ---------------------------------------------------------------------- *)

Lemma key3_tb_lo a Y k i : 0 <= k -> 0 <= a < 2 ^ k -> 0 <= i < k ->
  Z.testbit (a + 2 ^ k * Y) i = Z.testbit a i.
Proof.
  intros Hk Ha Hi.
  rewrite <- (Z.mod_pow2_bits_low (a + 2 ^ k * Y) k i) by lia.
  rewrite (Z.mul_comm (2 ^ k)), Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma key3_tb_hi a Y k i : 0 <= k -> 0 <= a < 2 ^ k -> k <= i ->
  Z.testbit (a + 2 ^ k * Y) i = Z.testbit Y (i - k).
Proof.
  intros Hk Ha Hi.
  replace i with ((i - k) + k) at 1 by lia.
  rewrite <- Z.div_pow2_bits by lia.
  rewrite (Z.mul_comm (2 ^ k)), Z.div_add by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma key3_tb_small a k i : 0 <= a < 2 ^ k -> k <= i -> Z.testbit a i = false.
Proof.
  intros Ha Hi. destruct (Z.eq_dec a 0) as [->|Hn]; [apply Z.testbit_0_l|].
  apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|].
  assert (2 ^ k <= 2 ^ i) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* get_unaligned_le32 as a number                                          *)
(* ---------------------------------------------------------------------- *)

Ltac zw := change Int.zwordsize with 32 in *; lia.

Lemma key3_le32_of (b0 b1 b2 b3: byte) :
  Int.unsigned (le32_of b0 b1 b2 b3) = le_Z [b0; b1; b2; b3].
Proof.
  pose proof (Byte.unsigned_range b0); pose proof (Byte.unsigned_range b1);
  pose proof (Byte.unsigned_range b2); pose proof (Byte.unsigned_range b3).
  change Byte.modulus with (2 ^ 8) in *.
  assert (HZ: 0 <= le_Z [b0; b1; b2; b3] <= Int.max_unsigned).
  { simpl. change Int.max_unsigned with 4294967295. lia. }
  rewrite <- (Int.unsigned_repr _ HZ). f_equal.
  apply Int.same_bits_eq. intros i Hi. change Int.zwordsize with 32 in Hi.
  unfold le32_of. rewrite !Int.bits_or, !Int.bits_shl by zw.
  assert (Hi': 0 <= i < Int.zwordsize) by zw.
  rewrite !(fun x => Int.testbit_repr x i Hi').
  change (Int.unsigned (Int.repr 8)) with 8; change (Int.unsigned (Int.repr 16)) with 16;
  change (Int.unsigned (Int.repr 24)) with 24.
  simpl le_Z. rewrite Z.add_0_r.
  change 256 with (2 ^ 8).
  replace (Byte.unsigned b0 + 2 ^ 8 * (Byte.unsigned b1 + 2 ^ 8 * (Byte.unsigned b2 + 2 ^ 8 * Byte.unsigned b3)))
    with (Byte.unsigned b0 + 2 ^ 8 * (Byte.unsigned b1 + 2 ^ 8 * (Byte.unsigned b2 + 2 ^ 8 * (Byte.unsigned b3 + 2 ^ 8 * 0))))
    by ring.
  destruct (zlt i 8), (zlt i 16), (zlt i 24); try lia; rewrite ?Int.testbit_repr by zw;
  repeat first [rewrite key3_tb_hi by zw | rewrite key3_tb_lo by zw];
  try rewrite (key3_tb_small (Byte.unsigned b0) 8) by zw;
  try rewrite (key3_tb_small (Byte.unsigned b1) 8) by zw;
  try rewrite (key3_tb_small (Byte.unsigned b2) 8) by zw;
  repeat match goal with
         | |- context [?a - 8 - 8 - 8] => replace (a - 8 - 8 - 8) with (a - 24) by lia
         | |- context [?a - 8 - 8] => replace (a - 8 - 8) with (a - 16) by lia
         end;
  rewrite ?orb_false_l, ?orb_false_r; reflexivity.
Qed.

Lemma key3_le_Z_app a b : le_Z (a ++ b) = le_Z a + 256 ^ Zlength a * le_Z b.
Proof.
  induction a as [|x a IH]; simpl app; [simpl; rewrite ?Zlength_nil; simpl; lia|].
  simpl le_Z. rewrite IH, Zlength_cons, Z.pow_succ_r by (pose proof (Zlength_nonneg a); lia). ring.
Qed.

Lemma key3_le_Z_range a : 0 <= le_Z a < 256 ^ Zlength a.
Proof.
  induction a as [|x a IH]; [simpl; rewrite ?Zlength_nil; simpl; lia|].
  simpl le_Z. rewrite Zlength_cons, Z.pow_succ_r by (pose proof (Zlength_nonneg a); lia).
  pose proof (Byte.unsigned_range x). change Byte.modulus with 256 in *. nia.
Qed.

(* the word at byte offset o of the first 16 bytes *)
Lemma key3_le32_at (rk: list byte) o :
  16 <= Zlength rk -> 0 <= o -> o + 4 <= 16 ->
  Int.unsigned (le32_at rk o) = le_Z (sublist 0 16 rk) / 2 ^ (8 * o) mod 2 ^ 32.
Proof.
  intros Hl Ho Ho4. unfold le32_at. rewrite key3_le32_of.
  rewrite (sublist_split 0 o 16) by lia. rewrite (sublist_split o (o + 4) 16) by lia.
  rewrite !key3_le_Z_app.
  rewrite !Zlength_sublist by lia.
  replace (o - 0) with o by lia. replace (o + 4 - o) with 4 by lia.
  pose proof (key3_le_Z_range (sublist 0 o rk)). rewrite Zlength_sublist in H by lia.
  replace (o - 0) with o in H by lia.
  replace (2 ^ (8 * o)) with (256 ^ o) by (rewrite Z.pow_mul_r by lia; reflexivity).
  rewrite (Z.add_comm (le_Z (sublist 0 o rk))), (Z.mul_comm (256 ^ o)), Z.div_add_l by lia.
  rewrite (Z.div_small (le_Z (sublist 0 o rk))) by lia. rewrite Z.add_0_r.
  pose proof (key3_le_Z_range (sublist o (o + 4) rk)). rewrite Zlength_sublist in H0 by lia.
  replace (o + 4 - o) with 4 in H0 by lia.
  change (256 ^ 4) with (2 ^ 32) in *.
  rewrite (Z.mul_comm (2 ^ 32)), Z.mod_add by lia. rewrite Z.mod_small by lia.
  replace (sublist o (o + 4) rk) with [Znth o rk; Znth (o + 1) rk; Znth (o + 2) rk; Znth (o + 3) rk].
  { reflexivity. }
  list_solve.
Qed.

(* ---------------------------------------------------------------------- *)
(* the limbs                                                               *)
(* ---------------------------------------------------------------------- *)

Definition key3_M : Z := 21267647620597763993911028882763415551.

Lemma key3_shru_and (w: int) s m :
  0 <= s < 32 -> 0 <= m <= Int.max_unsigned ->
  Int.and (Int.shru w (Int.repr s)) (Int.repr m) = Int.repr (Z.land (Z.shiftr (Int.unsigned w) s) m).
Proof.
  intros Hs Hm. unfold Int.and, Int.shru. rewrite (Int.unsigned_repr s) by rep_lia.
  rewrite (Int.unsigned_repr m) by lia. rewrite Int.unsigned_repr. reflexivity.
  pose proof (Int.unsigned_range w). rewrite Z.shiftr_div_pow2 by lia. split.
  apply Z.div_pos; lia. apply Z.le_trans with (Int.unsigned w). apply Z.div_le_upper_bound; [lia|].
  pose proof (Z.pow_pos_nonneg 2 s). nia. rep_lia.
Qed.

(* limb k: bits 26k .. 26k+25 of X land M, from the word at byte offset o shifted by s, masked by m *)
Lemma key3_limb X o s m k :
  0 <= X -> 0 <= o -> 0 <= s -> 8 * o + s = 26 * k -> 0 <= m < 2 ^ 26 -> s + 26 <= 32 \/ m < 2 ^ (32 - s) ->
  0 <= k ->
  (forall n, 0 <= n < 26 -> Z.testbit m n = Z.testbit key3_M (26 * k + n)) ->
  Z.land (Z.shiftr (X / 2 ^ (8 * o) mod 2 ^ 32) s) m = Z.land X key3_M / 2 ^ (26 * k) mod 2 ^ 26.
Proof.
  intros HX Ho Hs Hk Hm Hsm Hk0 Hbits.
  apply Z.bits_inj'; intros n Hn.
  rewrite Z.land_spec, Z.shiftr_spec by lia.
  destruct (zlt n 26).
  - rewrite (Z.mod_pow2_bits_low (Z.land X key3_M / 2 ^ (26 * k)) 26 n) by lia.
    rewrite Z.div_pow2_bits, Z.land_spec by lia.
    replace (n + 26 * k) with (26 * k + n) by lia.
    destruct (zlt (n + s) 32).
    + rewrite Z.mod_pow2_bits_low, Z.div_pow2_bits by lia.
      replace (n + s + 8 * o) with (26 * k + n) by lia. rewrite Hbits by lia. reflexivity.
    + rewrite Z.mod_pow2_bits_high by lia.
      destruct Hsm as [Hsm|Hsm]; [lia|].
      rewrite <- Hbits by lia. rewrite (key3_tb_small m (32 - s) n) by lia.
      rewrite !andb_false_r. reflexivity.
  - rewrite (key3_tb_small m 26 n) by lia. rewrite andb_false_r.
    rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma key3_limb4 X :
  0 <= X ->
  Z.land (Z.shiftr (X / 2 ^ (8 * 12) mod 2 ^ 32) 8) 1048575 = Z.land X key3_M / 2 ^ 104.
Proof.
  intros HX. apply Z.bits_inj'; intros n Hn.
  rewrite Z.land_spec, Z.shiftr_spec by lia. rewrite Z.div_pow2_bits by lia. rewrite Z.land_spec.
  destruct (zlt n 20).
  - rewrite Z.mod_pow2_bits_low by lia. rewrite Z.div_pow2_bits by lia.
    replace (n + 8 + 8 * 12) with (n + 104) by lia. f_equal.
    assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/
            n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16 \/ n = 17 \/ n = 18 \/ n = 19)
      by lia.
    repeat (destruct H as [->|H]; [reflexivity|]). subst n. reflexivity.
  - rewrite (key3_tb_small 1048575 20 n) by lia. rewrite (key3_tb_small key3_M 124 (n + 104)).
    + rewrite !andb_false_r. reflexivity.
    + unfold key3_M. lia.
    + lia.
Qed.

Ltac key3_enum26 :=
  let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn;
  assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/
          n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16 \/ n = 17 \/ n = 18 \/ n = 19 \/
          n = 20 \/ n = 21 \/ n = 22 \/ n = 23 \/ n = 24 \/ n = 25) as Hc by lia;
  repeat (destruct Hc as [->|Hc]; [reflexivity|]); subst n; reflexivity.

Section Limbs.
Variable rk: list byte.
Hypothesis Hrk: 16 <= Zlength rk.

Let X := le_Z (sublist 0 16 rk).
Lemma key3_X_nonneg : 0 <= X.
Proof. apply key3_le_Z_range. Qed.

Lemma key3_r0 : Int.and (le32_at rk 0) (Int.repr 67108863) = Int.repr (p1305_r rk mod 2 ^ 26).
Proof.
  pose proof key3_X_nonneg.
  rewrite <- (Int.shru_zero (le32_at rk 0)). change Int.zero with (Int.repr 0).
  rewrite key3_shru_and by rep_lia. rewrite key3_le32_at by lia. f_equal.
  unfold p1305_r. fold X. change 21267647620597763993911028882763415551 with key3_M.
  rewrite <- (Z.div_1_r (Z.land X key3_M)). change 1 with (2 ^ (26 * 0)).
  apply key3_limb; try lia. key3_enum26.
Qed.

Lemma key3_r1 : Int.and (Int.shru (le32_at rk 3) (Int.repr 2)) (Int.repr 67108611) =
                Int.repr (p1305_r rk / 2 ^ 26 mod 2 ^ 26).
Proof.
  pose proof key3_X_nonneg.
  rewrite key3_shru_and by rep_lia. rewrite key3_le32_at by lia. f_equal.
  unfold p1305_r. fold X. change 21267647620597763993911028882763415551 with key3_M.
  change (2 ^ 26) with (2 ^ (26 * 1)) at 1.
  apply key3_limb; try lia. key3_enum26.
Qed.

Lemma key3_r2 : Int.and (Int.shru (le32_at rk 6) (Int.repr 4)) (Int.repr 67092735) =
                Int.repr (p1305_r rk / 2 ^ 52 mod 2 ^ 26).
Proof.
  pose proof key3_X_nonneg.
  rewrite key3_shru_and by rep_lia. rewrite key3_le32_at by lia. f_equal.
  unfold p1305_r. fold X. change 21267647620597763993911028882763415551 with key3_M.
  change (2 ^ 52) with (2 ^ (26 * 2)).
  apply key3_limb; try lia. key3_enum26.
Qed.

Lemma key3_r3 : Int.and (Int.shru (le32_at rk 9) (Int.repr 6)) (Int.repr 66076671) =
                Int.repr (p1305_r rk / 2 ^ 78 mod 2 ^ 26).
Proof.
  pose proof key3_X_nonneg.
  rewrite key3_shru_and by rep_lia. rewrite key3_le32_at by lia. f_equal.
  unfold p1305_r. fold X. change 21267647620597763993911028882763415551 with key3_M.
  change (2 ^ 78) with (2 ^ (26 * 3)).
  apply key3_limb; try lia. key3_enum26.
Qed.

Lemma key3_r4 : Int.and (Int.shru (le32_at rk 12) (Int.repr 8)) (Int.repr 1048575) =
                Int.repr (p1305_r rk / 2 ^ 104).
Proof.
  pose proof key3_X_nonneg.
  rewrite key3_shru_and by rep_lia. rewrite key3_le32_at by lia. f_equal.
  unfold p1305_r. fold X. change 21267647620597763993911028882763415551 with key3_M.
  apply key3_limb4; lia.
Qed.

End Limbs.

Lemma key3_mul5 z : Int.mul (Int.repr z) (Int.repr 5) = Int.repr (5 * z).
Proof.
  unfold Int.mul. apply Int.eqm_samerepr. rewrite (Z.mul_comm 5).
  apply Int.eqm_mult; apply Int.eqm_sym, Int.eqm_unsigned_repr.
Qed.
