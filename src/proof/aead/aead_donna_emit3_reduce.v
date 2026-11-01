(* poly1305_core_emit, the pure part: the full carry, the conditional subtraction of p and the packing into
   four words compute (h mod p) mod 2^128.  The hypotheses are
   the values of the C temporaries as VST's forward produces them (w = c, w0 = h1, ...). *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.aead.aead_model.
Require Import WgNoise.proof.aead.aead_spec.

Local Open Scope Z_scope.

Lemma emit3_u_shru (x: int) (k: Z): 0 <= k < 32 ->
  Int.unsigned (Int.shru x (Int.repr k)) = Int.unsigned x / 2 ^ k.
Proof.
  intros. pose proof (Int.unsigned_range x).
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (1 <= 2 ^ k) by lia.
  rewrite Int.shru_div_two_p, (Int.unsigned_repr k) by rep_lia.
  rewrite two_p_correct. apply Int.unsigned_repr. split.
  - apply Z.div_pos; lia.
  - apply Z.le_trans with (Int.unsigned x); [| rep_lia].
    apply Z.div_le_upper_bound; [lia |].
    rewrite <- (Z.mul_1_l (Int.unsigned x)) at 1. apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Lemma emit3_u_mask (x: int): Int.unsigned (Int.and x (Int.repr 67108863)) = Int.unsigned x mod 2 ^ 26.
Proof.
  change (Int.repr 67108863) with (Int.repr (two_p 26 - 1)).
  rewrite <- Int.zero_ext_and by (cbn; lia). rewrite Int.zero_ext_mod by (cbn; lia). reflexivity.
Qed.

Lemma emit3_split26 (X: int):
  Int.unsigned X = 2 ^ 26 * Int.unsigned (Int.shru X (Int.repr 26)) + Int.unsigned (Int.and X (Int.repr 67108863)) /\
  0 <= Int.unsigned (Int.and X (Int.repr 67108863)) < 2 ^ 26 /\ 0 <= Int.unsigned (Int.shru X (Int.repr 26)).
Proof.
  rewrite emit3_u_shru, emit3_u_mask by lia. pose proof (Int.unsigned_range X).
  split; [apply Z.div_mod; lia | split; [apply Z.mod_pos_bound; lia | apply Z.div_pos; lia]].
Qed.

Lemma emit3_u_add (x y: int): Int.unsigned x + Int.unsigned y < 2 ^ 32 ->
  Int.unsigned (Int.add x y) = Int.unsigned x + Int.unsigned y.
Proof.
  intros. pose proof (Int.unsigned_range x). pose proof (Int.unsigned_range y).
  rewrite Int.add_unsigned, Int.unsigned_repr; [auto | rep_lia].
Qed.

Lemma emit3_u_mul5 (x: int): Int.unsigned x < 2 ^ 26 ->
  Int.unsigned (Int.mul x (Int.repr 5)) = 5 * Int.unsigned x.
Proof.
  intros. pose proof (Int.unsigned_range x). unfold Int.mul.
  rewrite (Int.unsigned_repr 5), Int.unsigned_repr by rep_lia. lia.
Qed.

Lemma emit3_u_or_shl (a b: int) (n: Z): 0 < n < 32 -> Int.unsigned a < 2 ^ n ->
  Int.unsigned (Int.or a (Int.shl b (Int.repr n))) = Int.unsigned a + (Int.unsigned b mod 2 ^ (32 - n)) * 2 ^ n.
Proof.
  intros Hn Ha. pose proof (Int.unsigned_range a). pose proof (Int.unsigned_range b).
  assert (Hz: Int.and a (Int.shl b (Int.repr n)) = Int.zero).
  { apply Int.same_bits_eq; intros i Hi. rewrite Int.bits_and, Int.bits_shl, Int.bits_zero by auto.
    rewrite Int.unsigned_repr by rep_lia. destruct (zlt i n).
    - apply andb_false_r.
    - unfold Int.testbit.
      destruct (Z.eq_dec (Int.unsigned a) 0) as [E|E].
      + rewrite E, Z.testbit_0_l. reflexivity.
      + rewrite Z.bits_above_log2; [reflexivity | lia |].
        apply Z.log2_lt_pow2; [lia |].
        apply Z.lt_le_trans with (2 ^ n); [lia | apply Z.pow_le_mono_r; lia]. }
  rewrite <- Int.add_is_or by auto.
  rewrite Int.shl_mul_two_p, Int.unsigned_repr by rep_lia.
  assert (E2: 2 ^ 32 = 2 ^ (32 - n) * 2 ^ n) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (0 < 2 ^ n) by (apply Z.pow_pos_nonneg; lia).
  assert (0 < 2 ^ (32 - n)) by (apply Z.pow_pos_nonneg; lia).
  assert (2 ^ n <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia).
  assert (Em: Int.unsigned (Int.mul b (Int.repr (two_p n))) = Int.unsigned b mod 2 ^ (32 - n) * 2 ^ n).
  { unfold Int.mul. rewrite two_p_correct, (Int.unsigned_repr (2 ^ n)) by rep_lia.
    rewrite Int.unsigned_repr_eq. change Int.modulus with (2 ^ 32). rewrite E2.
    apply Z.mul_mod_distr_r; lia. }
  rewrite Int.add_unsigned, Em. apply Int.unsigned_repr.
  pose proof (Z.mod_pos_bound (Int.unsigned b) (2 ^ (32 - n))).
  change Int.max_unsigned with (2 ^ 32 - 1). nia.
Qed.

Lemma emit3_pack (x0 x1 x2 x3 x4: int):
  Int.unsigned x0 < 2 ^ 26 -> Int.unsigned x1 < 2 ^ 26 -> Int.unsigned x2 < 2 ^ 26 ->
  Int.unsigned x3 < 2 ^ 26 -> Int.unsigned x4 < 2 ^ 26 ->
  words_Z [Int.or x0 (Int.shl x1 (Int.repr 26));
           Int.or (Int.shru x1 (Int.repr 6)) (Int.shl x2 (Int.repr 20));
           Int.or (Int.shru x2 (Int.repr 12)) (Int.shl x3 (Int.repr 14));
           Int.or (Int.shru x3 (Int.repr 18)) (Int.shl x4 (Int.repr 8))]
  = (Int.unsigned x0 + Int.unsigned x1 * 2 ^ 26 + Int.unsigned x2 * 2 ^ 52 + Int.unsigned x3 * 2 ^ 78 +
     Int.unsigned x4 * 2 ^ 104) mod 2 ^ 128.
Proof.
  intros H0 H1 H2 H3 H4.
  pose proof (Int.unsigned_range x0). pose proof (Int.unsigned_range x1). pose proof (Int.unsigned_range x2).
  pose proof (Int.unsigned_range x3). pose proof (Int.unsigned_range x4).
  cbn [words_Z].
  assert (S1: Int.unsigned (Int.shru x1 (Int.repr 6)) = Int.unsigned x1 / 2 ^ 6) by (apply emit3_u_shru; lia).
  assert (S2: Int.unsigned (Int.shru x2 (Int.repr 12)) = Int.unsigned x2 / 2 ^ 12) by (apply emit3_u_shru; lia).
  assert (S3: Int.unsigned (Int.shru x3 (Int.repr 18)) = Int.unsigned x3 / 2 ^ 18) by (apply emit3_u_shru; lia).
  assert (D1 := Z.div_mod (Int.unsigned x1) (2 ^ 6) ltac:(lia)).
  assert (D2 := Z.div_mod (Int.unsigned x2) (2 ^ 12) ltac:(lia)).
  assert (D3 := Z.div_mod (Int.unsigned x3) (2 ^ 18) ltac:(lia)).
  assert (D4 := Z.div_mod (Int.unsigned x4) (2 ^ 24) ltac:(lia)).
  assert (M1 := Z.mod_pos_bound (Int.unsigned x1) (2 ^ 6) ltac:(lia)).
  assert (M2 := Z.mod_pos_bound (Int.unsigned x2) (2 ^ 12) ltac:(lia)).
  assert (M3 := Z.mod_pos_bound (Int.unsigned x3) (2 ^ 18) ltac:(lia)).
  assert (M4 := Z.mod_pos_bound (Int.unsigned x4) (2 ^ 24) ltac:(lia)).
  rewrite (emit3_u_or_shl x0 x1 26) by lia.
  rewrite (emit3_u_or_shl _ x2 20) by (try rewrite S1; lia).
  rewrite (emit3_u_or_shl _ x3 14) by (try rewrite S2; lia).
  rewrite (emit3_u_or_shl _ x4 8) by (try rewrite S3; lia).
  rewrite S1, S2, S3.
  change (32 - 26) with 6. change (32 - 20) with 12. change (32 - 14) with 18. change (32 - 8) with 24.
  apply Z.mod_unique with (q := Int.unsigned x4 / 2 ^ 24); lia.
Qed.

Lemma emit3_reduce_ok (a0 a1 a2 a3 a4: Z)
  (w w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27
   w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42: int) :
  0 <= a0 < 2 ^ 26 -> 0 <= a1 < 2 ^ 26 + 2 ^ 6 -> 0 <= a2 < 2 ^ 26 -> 0 <= a3 < 2 ^ 26 -> 0 <= a4 < 2 ^ 26 ->
  w = Int.shru (Int.repr a1) (Int.repr 26) ->
  w0 = Int.and (Int.repr a1) (Int.repr 67108863) ->
  w1 = Int.add (Int.repr a2) w ->
  w2 = Int.shru w1 (Int.repr 26) ->
  w3 = Int.and w1 (Int.repr 67108863) ->
  w4 = Int.add (Int.repr a3) w2 ->
  w5 = Int.shru w4 (Int.repr 26) ->
  w6 = Int.and w4 (Int.repr 67108863) ->
  w7 = Int.add (Int.repr a4) w5 ->
  w8 = Int.shru w7 (Int.repr 26) ->
  w9 = Int.and w7 (Int.repr 67108863) ->
  w10 = Int.add (Int.repr a0) (Int.mul w8 (Int.repr 5)) ->
  w11 = Int.shru w10 (Int.repr 26) ->
  w12 = Int.and w10 (Int.repr 67108863) ->
  w13 = Int.add w0 w11 ->
  w14 = Int.add w12 (Int.repr 5) ->
  w15 = Int.shru w14 (Int.repr 26) ->
  w16 = Int.and w14 (Int.repr 67108863) ->
  w17 = Int.add w13 w15 ->
  w18 = Int.shru w17 (Int.repr 26) ->
  w19 = Int.and w17 (Int.repr 67108863) ->
  w20 = Int.add w3 w18 ->
  w21 = Int.shru w20 (Int.repr 26) ->
  w22 = Int.and w20 (Int.repr 67108863) ->
  w23 = Int.add w6 w21 ->
  w24 = Int.shru w23 (Int.repr 26) ->
  w25 = Int.and w23 (Int.repr 67108863) ->
  w26 = Int.repr (Int64.unsigned (Int64.sub (Int64.repr (Int.unsigned (Int.add w9 w24)))
                                             (Int64.shl (Int64.repr 1) (Int64.repr (Int.unsigned (Int.repr 26)))))) ->
  w27 = Int.sub (Int.shru w26 (Int.repr 31)) (Int.repr 1) ->
  w28 = Int.and w16 w27 ->
  w29 = Int.and w19 w27 ->
  w30 = Int.and w22 w27 ->
  w31 = Int.and w25 w27 ->
  w32 = Int.and w26 w27 ->
  w33 = Int.not w27 ->
  w34 = Int.or (Int.and w12 w33) w28 ->
  w35 = Int.or (Int.and w13 w33) w29 ->
  w36 = Int.or (Int.and w3 w33) w30 ->
  w37 = Int.or (Int.and w6 w33) w31 ->
  w38 = Int.or (Int.and w9 w33) w32 ->
  w39 = Int.and (Int.or w34 (Int.shl w35 (Int.repr 26))) (Int.repr (-1)) ->
  w40 = Int.and (Int.or (Int.shru w35 (Int.repr 6)) (Int.shl w36 (Int.repr 20))) (Int.repr (-1)) ->
  w41 = Int.and (Int.or (Int.shru w36 (Int.repr 12)) (Int.shl w37 (Int.repr 14))) (Int.repr (-1)) ->
  w42 = Int.and (Int.or (Int.shru w37 (Int.repr 18)) (Int.shl w38 (Int.repr 8))) (Int.repr (-1)) ->
  words_Z [w39; w40; w41; w42] = (p1305_limbs_val [a0; a1; a2; a3; a4] mod p1305_p) mod 2 ^ 128.
Proof.
  intros B0 B1 B2 B3 B4 E E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 E15 E16 E17 E18 E19 E20 E21 E22
    E23 E24 E25 E26 E27 E28 E29 E30 E31 E32 E33 E34 E35 E36 E37 E38 E39 E40 E41 E42.
  assert (U0: Int.unsigned (Int.repr a0) = a0) by (apply Int.unsigned_repr; rep_lia).
  assert (U1: Int.unsigned (Int.repr a1) = a1) by (apply Int.unsigned_repr; rep_lia).
  assert (U2: Int.unsigned (Int.repr a2) = a2) by (apply Int.unsigned_repr; rep_lia).
  assert (U3: Int.unsigned (Int.repr a3) = a3) by (apply Int.unsigned_repr; rep_lia).
  assert (U4: Int.unsigned (Int.repr a4) = a4) by (apply Int.unsigned_repr; rep_lia).
  assert (LV: p1305_limbs_val [a0; a1; a2; a3; a4] = a0 + a1 * 2 ^ 26 + a2 * 2 ^ 52 + a3 * 2 ^ 78 + a4 * 2 ^ 104)
    by reflexivity.
  rewrite LV. clear LV.
  (* the first carry pass *)
  pose proof (emit3_split26 (Int.repr a1)) as S. rewrite <- E, <- E0, U1 in S. destruct S as (D0 & R0 & Q0).
  assert (V1: Int.unsigned w1 = a2 + Int.unsigned w) by (subst w1; rewrite emit3_u_add; rewrite ?U2; lia).
  pose proof (emit3_split26 w1) as S. rewrite <- E2, <- E3 in S. destruct S as (D1 & R1 & Q1).
  assert (V4: Int.unsigned w4 = a3 + Int.unsigned w2) by (subst w4; rewrite emit3_u_add; rewrite ?U3; lia).
  pose proof (emit3_split26 w4) as S. rewrite <- E5, <- E6 in S. destruct S as (D4 & R4 & Q4).
  assert (V7: Int.unsigned w7 = a4 + Int.unsigned w5) by (subst w7; rewrite emit3_u_add; rewrite ?U4; lia).
  pose proof (emit3_split26 w7) as S. rewrite <- E8, <- E9 in S. destruct S as (D7 & R7 & Q7).
  assert (M8: Int.unsigned (Int.mul w8 (Int.repr 5)) = 5 * Int.unsigned w8) by (apply emit3_u_mul5; lia).
  assert (V10: Int.unsigned w10 = a0 + 5 * Int.unsigned w8)
    by (subst w10; rewrite emit3_u_add; rewrite ?U0, ?M8; lia).
  pose proof (emit3_split26 w10) as S. rewrite <- E11, <- E12 in S. destruct S as (D10 & R10 & Q10).
  assert (V13: Int.unsigned w13 = Int.unsigned w0 + Int.unsigned w11) by (subst w13; rewrite emit3_u_add; lia).
  assert (B13: Int.unsigned w13 < 2 ^ 26).
  { assert (C: Int.unsigned w = 0 \/ Int.unsigned w = 1) by lia. destruct C; lia. }
  (* g = h + 5 *)
  assert (V14: Int.unsigned w14 = Int.unsigned w12 + 5)
    by (subst w14; rewrite emit3_u_add; rewrite ?(Int.unsigned_repr 5) by rep_lia; rep_lia).
  pose proof (emit3_split26 w14) as S. rewrite <- E15, <- E16 in S. destruct S as (D14 & R14 & Q14).
  assert (V17: Int.unsigned w17 = Int.unsigned w13 + Int.unsigned w15) by (subst w17; rewrite emit3_u_add; lia).
  pose proof (emit3_split26 w17) as S. rewrite <- E18, <- E19 in S. destruct S as (D17 & R17 & Q17).
  assert (V20: Int.unsigned w20 = Int.unsigned w3 + Int.unsigned w18) by (subst w20; rewrite emit3_u_add; lia).
  pose proof (emit3_split26 w20) as S. rewrite <- E21, <- E22 in S. destruct S as (D20 & R20 & Q20).
  assert (V23: Int.unsigned w23 = Int.unsigned w6 + Int.unsigned w21) by (subst w23; rewrite emit3_u_add; lia).
  pose proof (emit3_split26 w23) as S. rewrite <- E24, <- E25 in S. destruct S as (D23 & R23 & Q23).
  assert (Bs: Int.unsigned w9 + Int.unsigned w24 <= 2 ^ 26) by lia.
  assert (U26: Int.unsigned w26 = (Int.unsigned w9 + Int.unsigned w24 - 2 ^ 26) mod 2 ^ 32).
  { subst w26. rewrite emit3_u_add by lia. unfold Int64.sub.
    change (Int64.unsigned (Int64.shl (Int64.repr 1) (Int64.repr (Int.unsigned (Int.repr 26))))) with (2 ^ 26).
    rewrite (Int64.unsigned_repr (Int.unsigned w9 + Int.unsigned w24)) by rep_lia.
    rewrite Int64.unsigned_repr_eq, Int.unsigned_repr_eq.
    change Int64.modulus with (2 ^ 64). change Int.modulus with (2 ^ 32).
    symmetry; apply Znumtheory.Zmod_div_mod; [lia | lia | exists (2 ^ 32); reflexivity]. }
  pose proof (Int.unsigned_range w0) as N0. pose proof (Int.unsigned_range w3) as N3.
  pose proof (Int.unsigned_range w6) as N6. pose proof (Int.unsigned_range w9) as N9.
  pose proof (Int.unsigned_range w12) as N12. pose proof (Int.unsigned_range w13) as N13.
  pose proof (Int.unsigned_range w16) as N16. pose proof (Int.unsigned_range w19) as N19.
  pose proof (Int.unsigned_range w22) as N22. pose proof (Int.unsigned_range w25) as N25.
  subst w39 w40 w41 w42 w34 w35 w36 w37 w38 w33 w28 w29 w30 w31 w32.
  destruct (Z_lt_le_dec (Int.unsigned w9 + Int.unsigned w24) (2 ^ 26)) as [Lt | Ge].
  - (* h < p: keep h *)
    assert (U26': Int.unsigned w26 = Int.unsigned w9 + Int.unsigned w24 - 2 ^ 26 + 2 ^ 32).
    { rewrite U26. symmetry. apply Z.mod_unique with (q := -1); lia. }
    assert (Z27: w27 = Int.zero).
    { subst w27. rewrite <- (Int.repr_unsigned (Int.shru w26 (Int.repr 31))), emit3_u_shru, U26' by lia.
      replace ((Int.unsigned w9 + Int.unsigned w24 - 2 ^ 26 + 2 ^ 32) / 2 ^ 31) with 1.
      - apply Int.same_if_eq; reflexivity.
      - apply Z.div_unique with (r := Int.unsigned w9 + Int.unsigned w24 - 2 ^ 26 + 2 ^ 31); lia. }
    rewrite Z27, Int.not_zero, !Int.and_zero, !Int.and_mone, !Int.or_zero.
    rewrite emit3_pack by lia.
    f_equal. apply Z.mod_unique with (q := Int.unsigned w8); unfold p1305_p; lia.
  - (* h >= p: take g = h - p *)
    assert (Z26: w26 = Int.zero).
    { rewrite <- (Int.repr_unsigned w26), U26. replace (Int.unsigned w9 + Int.unsigned w24 - 2 ^ 26) with 0 by lia.
      reflexivity. }
    assert (Z27: w27 = Int.mone) by (subst w27; rewrite Z26; apply Int.same_if_eq; reflexivity).
    rewrite Z27, Int.not_mone, !Int.and_zero, !Int.and_mone, !(Int.or_commut Int.zero), !Int.or_zero.
    rewrite Z26. rewrite emit3_pack by (rewrite ?Int.unsigned_zero; lia).
    rewrite Int.unsigned_zero.
    f_equal. apply Z.mod_unique with (q := Int.unsigned w8 + 1); unfold p1305_p; lia.
Qed.
