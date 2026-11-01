(* the message limbs of poly1305_core_blocks (lib/crypto/poly1305-donna32.c): the five masked /
   shifted little-endian words at offsets 0, 3, 6, 9, 12 of a 16-byte block are its 26-bit limbs. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.aead.aead_model.
Require Import WgNoise.proof.aead.aead_donna3_math.

Local Open Scope Z_scope.

Lemma adb3_lor_add (a b k: Z) :
  0 <= k -> 0 <= a < 2 ^ k -> 0 <= b -> Z.lor a (b * 2 ^ k) = a + b * 2 ^ k.
Proof.
  intros Hk Ha Hb.
  assert (Hl: Z.land a (b * 2 ^ k) = 0).
  { apply Z.bits_inj'; intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases n k).
    - rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    - replace a with (a mod 2 ^ k) by (apply Z.mod_small; lia).
      rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite <- Z.lxor_lor by exact Hl. rewrite Z.add_nocarry_lxor by exact Hl. reflexivity.
Qed.

Lemma adb3_le32_of_unsigned (b0 b1 b2 b3: byte) :
  Int.unsigned (le32_of b0 b1 b2 b3) =
  Byte.unsigned b0 + Byte.unsigned b1 * 2 ^ 8 + Byte.unsigned b2 * 2 ^ 16 + Byte.unsigned b3 * 2 ^ 24.
Proof.
  pose proof (Byte.unsigned_range b0) as R0. pose proof (Byte.unsigned_range b1) as R1.
  pose proof (Byte.unsigned_range b2) as R2. pose proof (Byte.unsigned_range b3) as R3.
  change Byte.modulus with 256 in *.
  unfold le32_of, Int.or, Int.shl.
  rewrite !(Int.unsigned_repr 8), !(Int.unsigned_repr 16), !(Int.unsigned_repr 24) by rep_lia.
  rewrite !(Int.unsigned_repr (Byte.unsigned _)) by rep_lia.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (Int.unsigned_repr (_ * 2 ^ 8)) by rep_lia.
  rewrite adb3_lor_add by rep_lia.
  rewrite (Int.unsigned_repr (_ + _)) by rep_lia.
  rewrite (Int.unsigned_repr (_ * 2 ^ 16)) by rep_lia.
  rewrite adb3_lor_add by rep_lia.
  rewrite (Int.unsigned_repr (_ + _)) by rep_lia.
  rewrite (Int.unsigned_repr (_ * 2 ^ 24)) by rep_lia.
  rewrite adb3_lor_add by rep_lia.
  apply Int.unsigned_repr. rep_lia.
Qed.

Lemma adb3_le_Z_range (bs: list byte) : 0 <= le_Z bs < 2 ^ (8 * Zlength bs).
Proof.
  induction bs as [|b t IH].
  - cbn. lia.
  - simpl le_Z. rewrite Zlength_cons. pose proof (Byte.unsigned_range b). change Byte.modulus with 256 in *.
    replace (8 * Z.succ (Zlength t)) with (8 + 8 * Zlength t) by lia.
    rewrite Z.pow_add_r by (pose proof (Zlength_nonneg t); lia). change (2 ^ 8) with 256. lia.
Qed.

Lemma adb3_le_Z_byte (bs: list byte) (i: Z) :
  0 <= i < Zlength bs -> (le_Z bs / 2 ^ (8 * i)) mod 2 ^ 8 = Byte.unsigned (Znth i bs).
Proof.
  revert i; induction bs as [|b t IH]; intros i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi. simpl le_Z. pose proof (Byte.unsigned_range b).
    change Byte.modulus with 256 in *.
    destruct (Z.eq_dec i 0) as [->|Hne].
    + rewrite Znth_0_cons. change (2 ^ (8 * 0)) with 1. rewrite Z.div_1_r. change (2 ^ 8) with 256.
      rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
    + rewrite Znth_pos_cons by lia.
      replace (8 * i) with (8 + 8 * (i - 1)) by lia.
      rewrite Z.pow_add_r by lia. rewrite <- Z.div_div by lia. change (2 ^ 8) with 256.
      replace ((Byte.unsigned b + 256 * le_Z t) / 256) with (le_Z t).
      * rewrite <- IH by lia. reflexivity.
      * rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma adb3_le32_at_unsigned (bs: list byte) (i: Z) :
  0 <= i -> i + 4 <= Zlength bs ->
  Int.unsigned (le32_at bs i) = (le_Z bs / 2 ^ (8 * i)) mod 2 ^ 32.
Proof.
  intros H0 H1. unfold le32_at. rewrite adb3_le32_of_unsigned.
  rewrite <- !adb3_le_Z_byte by lia.
  set (X := le_Z bs).
  assert (Hd: forall k, 0 <= k -> X / 2 ^ (8 * (i + k)) = X / 2 ^ (8 * i) / 2 ^ (8 * k)).
  { intros k Hk. rewrite Z.div_div by lia. rewrite <- Z.pow_add_r by lia. f_equal; f_equal; lia. }
  rewrite !Hd by lia. set (Y := X / 2 ^ (8 * i)).
  change (2 ^ 32) with (2 ^ 8 * (2 ^ 8 * (2 ^ 8 * 2 ^ 8))).
  rewrite !Z.rem_mul_r by lia.
  rewrite !Z.div_div by lia.
  change (8 * 1) with 8. change (8 * 2) with 16. change (8 * 3) with 24.
  change (2 ^ 8 * 2 ^ 8) with (2 ^ 16). change (2 ^ 16 * 2 ^ 8) with (2 ^ 24).
  change (2 ^ 8 * 2 ^ 16) with (2 ^ 24).
  lia.
Qed.

Lemma adb3_field (Y: Z) (s m t: Z) :
  0 <= s -> 0 <= m -> m + s <= t ->
  (Y mod 2 ^ t) / 2 ^ s mod 2 ^ m = (Y / 2 ^ s) mod 2 ^ m.
Proof.
  intros Hs Hm Ht.
  replace t with (s + (t - s)) by lia. rewrite Z.pow_add_r by lia.
  rewrite Z.rem_mul_r by lia.
  rewrite (Z.mul_comm (2 ^ s)), Z.div_add by lia.
  rewrite (Z.div_small (Y mod 2 ^ s)) by (apply Z.mod_pos_bound; lia). rewrite Z.add_0_l.
  replace (t - s) with (m + (t - s - m)) by lia. rewrite Z.pow_add_r by lia.
  rewrite Z.rem_mul_r by lia.
  rewrite (Z.mul_comm (2 ^ m)), Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.

Lemma adb3_and_mask (x: int) :
  Int.unsigned (Int.and x (Int.repr 67108863)) = Int.unsigned x mod 2 ^ 26.
Proof.
  unfold Int.and. change (Int.unsigned (Int.repr 67108863)) with (Z.ones 26).
  rewrite Z.land_ones by lia. apply Int.unsigned_repr.
  pose proof (Z.mod_pos_bound (Int.unsigned x) (2 ^ 26) ltac:(lia)). rep_lia.
Qed.

Lemma adb3_shru (x: int) (k: Z) :
  0 <= k < 32 -> Int.unsigned (Int.shru x (Int.repr k)) = Int.unsigned x / 2 ^ k.
Proof.
  intros Hk. unfold Int.shru. rewrite (Int.unsigned_repr k) by rep_lia.
  rewrite Z.shiftr_div_pow2 by lia. apply Int.unsigned_repr.
  pose proof (Int.unsigned_range x). split.
  - apply Z.div_pos; lia.
  - assert (1 <= 2 ^ k) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia).
    assert (Int.unsigned x / 2 ^ k <= Int.unsigned x) by (apply Z.div_le_upper_bound; nia).
    rep_lia.
Qed.

Lemma adb3_m_le (blk: list byte) :
  Zlength blk = 16 ->
  adb3_m (le32_at blk 0) (le32_at blk 3) (le32_at blk 6) (le32_at blk 9) (le32_at blk 12) = le_Z blk.
Proof.
  intros Hl. unfold adb3_m.
  rewrite !adb3_and_mask, !adb3_shru by lia.
  rewrite !adb3_le32_at_unsigned by lia.
  pose proof (adb3_le_Z_range blk) as HX. rewrite Hl in HX. change (8 * 16) with 128 in HX.
  change (8 * 0) with 0. change (8 * 3) with 24. change (8 * 6) with 48.
  change (8 * 9) with 72. change (8 * 12) with 96.
  set (X := le_Z blk) in *.
  assert (Hdd: forall a b, 0 <= a -> 0 <= b -> X / 2 ^ a / 2 ^ b = X / 2 ^ (a + b)).
  { intros a b Ha Hb. rewrite Z.div_div by lia. rewrite Z.pow_add_r by lia. reflexivity. }
  assert (F0: (X / 2 ^ 0) mod 2 ^ 32 mod 2 ^ 26 = X mod 2 ^ 26).
  { pose proof (adb3_field (X / 2 ^ 0) 0 26 32 ltac:(lia) ltac:(lia) ltac:(lia)) as E.
    change (2 ^ 0) with 1 in *. rewrite !Z.div_1_r in *. exact E. }
  assert (F1: (X / 2 ^ 24) mod 2 ^ 32 / 2 ^ 2 mod 2 ^ 26 = X / 2 ^ 26 mod 2 ^ 26).
  { rewrite adb3_field by lia. rewrite Hdd by lia. reflexivity. }
  assert (F2: (X / 2 ^ 48) mod 2 ^ 32 / 2 ^ 4 mod 2 ^ 26 = X / 2 ^ 52 mod 2 ^ 26).
  { rewrite adb3_field by lia. rewrite Hdd by lia. reflexivity. }
  assert (F3: (X / 2 ^ 72) mod 2 ^ 32 / 2 ^ 6 mod 2 ^ 26 = X / 2 ^ 78 mod 2 ^ 26).
  { rewrite adb3_field by lia. rewrite Hdd by lia. reflexivity. }
  assert (F4: (X / 2 ^ 96) mod 2 ^ 32 / 2 ^ 8 = X / 2 ^ 104).
  { rewrite Z.mod_small.
    - rewrite Hdd by lia. reflexivity.
    - split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
      change (2 ^ 96 * 2 ^ 32) with (2 ^ 128). lia. }
  rewrite F0, F1, F2, F3, F4.
  assert (S: forall a, 0 <= a -> X / 2 ^ a = X / 2 ^ a mod 2 ^ 26 + X / 2 ^ (a + 26) * 2 ^ 26).
  { intros a Ha. rewrite <- Hdd by lia.
    rewrite (Z.div_mod (X / 2 ^ a) (2 ^ 26)) at 1 by lia. lia. }
  pose proof (S 0 ltac:(lia)) as S0. pose proof (S 26 ltac:(lia)) as S1.
  pose proof (S 52 ltac:(lia)) as S2. pose proof (S 78 ltac:(lia)) as S3.
  change (2 ^ 0) with 1 in S0. rewrite Z.div_1_r in S0.
  change (0 + 26) with 26 in S0. change (26 + 26) with 52 in S1.
  change (52 + 26) with 78 in S2. change (78 + 26) with 104 in S3.
  clear S F0 F1 F2 F3 F4 Hdd.
  set (q26 := X / 2 ^ 26) in *. set (q52 := X / 2 ^ 52) in *.
  set (q78 := X / 2 ^ 78) in *. set (q104 := X / 2 ^ 104) in *.
  clearbody q26 q52 q78 q104.
  change (2 ^ 26) with 67108864 in *. change (2 ^ 52) with 4503599627370496.
  change (2 ^ 78) with 302231454903657293676544.
  change (2 ^ 104) with 20282409603651670423947251286016.
  lia.
Qed.
