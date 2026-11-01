(* model facts for poly1305_final (aead_poly_final_body3.v): the padded last block, s as words. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.aead.aead_model.
Require Import WgNoise.proof.aead.aead_spec.

Local Open Scope Z_scope.

Lemma pf3_le_Z_app a b : le_Z (a ++ b) = le_Z a + 2 ^ (8 * Zlength a) * le_Z b.
Proof.
  induction a as [| x a IH]; simpl app; simpl le_Z.
  - rewrite Zlength_nil. simpl. lia.
  - rewrite IH, Zlength_cons.
    replace (8 * Z.succ (Zlength a)) with (8 + 8 * Zlength a) by lia.
    rewrite Z.pow_add_r by (pose proof (Zlength_nonneg a); lia). lia.
Qed.

Lemma pf3_le_Z_zeros n : le_Z (repeat Byte.zero n) = 0.
Proof. induction n; simpl; auto. rewrite IHn. reflexivity. Qed.

(* the padded last block of poly1305_final *)
Lemma pf3_core_last r acc rest :
  0 < Zlength rest < 16 ->
  p1305_core_blocks r 0 acc (rest ++ [Byte.one] ++ Zrepeat Byte.zero (15 - Zlength rest)) =
  (acc + le_Z rest + 2 ^ (8 * Zlength rest)) * r mod p1305_p.
Proof.
  intros Hr.
  set (bs := rest ++ [Byte.one] ++ Zrepeat Byte.zero (15 - Zlength rest)).
  assert (Hb: Zlength bs = 16).
  { unfold bs. rewrite !Zlength_app, Zlength_Zrepeat by lia. rewrite Zlength_cons, Zlength_nil. lia. }
  unfold p1305_core_blocks. rewrite Hb. simpl. unfold p1305_core_step.
  rewrite sublist_same by lia.
  f_equal. f_equal.
  unfold bs. rewrite pf3_le_Z_app. simpl le_Z. unfold Zrepeat. rewrite pf3_le_Z_zeros.
  change (Byte.unsigned Byte.one) with 1. lia.
Qed.

Lemma pf3_core_last_mod r a rest :
  0 < Zlength rest < 16 ->
  p1305_core_blocks r 0 a (rest ++ [Byte.one] ++ Zrepeat Byte.zero (15 - Zlength rest)) mod p1305_p =
  p1305_step r (a mod p1305_p) rest.
Proof.
  intros Hr. rewrite pf3_core_last by auto. unfold p1305_step.
  rewrite Zmod_mod.
  rewrite <- !Z.add_assoc.
  rewrite <- (Z.mul_mod_idemp_l (a + _)), <- (Z.mul_mod_idemp_l (a mod p1305_p + _)) by (unfold p1305_p; lia).
  rewrite Z.add_mod_idemp_l by (unfold p1305_p; lia). reflexivity.
Qed.

(* the blocks of a message: whole blocks, then the 1..15-byte rest *)
Lemma pf3_blocks_nat r (n: nat) acc msg :
  16 * Z.of_nat n <= Zlength msg ->
  fold_left (p1305_step r) (map (fun i => sublist (16 * i) (16 * i + 16) msg) (map Z.of_nat (seq 0 n))) acc =
  fold_left (p1305_step r)
    (map (fun i => sublist (16 * i) (16 * i + 16) (sublist 0 (16 * Z.of_nat n) msg)) (map Z.of_nat (seq 0 n)))
    acc.
Proof.
  intros Hn. f_equal. apply map_ext_in. intros i Hi.
  rewrite in_map_iff in Hi. destruct Hi as [k [Hk Hin]]. subst i.
  rewrite in_seq in Hin.
  rewrite sublist_sublist by lia. f_equal; lia.
Qed.

Lemma pf3_acc_split r msg :
  let n := Zlength msg / 16 * 16 in
  p1305_acc r 0 msg =
  if zlt n (Zlength msg) then p1305_step r (p1305_acc r 0 (sublist 0 n msg)) (sublist n (Zlength msg) msg)
  else p1305_acc r 0 (sublist 0 n msg).
Proof.
  intros n.
  pose proof (Zlength_nonneg msg).
  assert (Hn: 0 <= n <= Zlength msg) by (subst n; split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia |
    rewrite Z.mul_comm; apply Z.mul_div_le; lia]).
  assert (Hmod: Zlength msg = n + Zlength msg mod 16) by (subst n; pose proof (Z_div_mod_eq_full (Zlength msg) 16); lia).
  pose proof (Z.mod_pos_bound (Zlength msg) 16 ltac:(lia)).
  unfold p1305_acc, p1305_blocks.
  rewrite Zlength_sublist by lia. replace (n - 0) with n by lia.
  assert (Hq: (n + 15) / 16 = Zlength msg / 16) by (subst n; rewrite Z.div_add_l by lia; change (15 / 16) with 0; lia).
  assert (Hq0: 0 <= Zlength msg / 16) by (apply Z.div_pos; lia).
  assert (Hn': n = 16 * Z.of_nat (Z.to_nat (Zlength msg / 16))) by (rewrite Z2Nat.id; subst n; lia).
  rewrite Hq.
  destruct (zlt n (Zlength msg)) as [Hlt | Hge].
  - assert (Hq1: (Zlength msg + 15) / 16 = Zlength msg / 16 + 1).
    { rewrite Hmod at 1. subst n.
      replace (Zlength msg / 16 * 16 + Zlength msg mod 16 + 15) with ((Zlength msg mod 16 + 15) + (Zlength msg / 16) * 16) by lia.
      rewrite Z.div_add by lia.
      assert ((Zlength msg mod 16 + 15) / 16 = 1) by (symmetry; apply Z.div_unique with (Zlength msg mod 16 - 1); lia).
      lia. }
    rewrite Hq1. rewrite Z2Nat.inj_add by lia. rewrite seq_app, !map_app, fold_left_app.
    remember (Z.to_nat (Zlength msg / 16)) as k.
    change (Z.to_nat 1) with 1%nat. rewrite Nat.add_0_l. cbn [seq map fold_left].
    rewrite pf3_blocks_nat by lia. rewrite <- Hn'. f_equal.
    unfold sublist. f_equal. rewrite !firstn_all2; auto; rewrite <- ZtoNat_Zlength; lia.
  - assert (Hq1: (Zlength msg + 15) / 16 = Zlength msg / 16).
    { replace (Zlength msg) with n at 1 by lia. subst n.
      rewrite Z.div_add_l by lia. change (15 / 16) with 0. lia. }
    rewrite Hq1. rewrite pf3_blocks_nat by lia. rewrite <- Hn'. reflexivity.
Qed.

(* s as 4 little-endian words *)
Lemma pf3_lor_disj a b k : 0 <= k -> 0 <= a < 2 ^ k -> 0 <= b -> Z.lor a (b * 2 ^ k) = a + b * 2 ^ k.
Proof.
  intros Hk Ha Hb. assert (HL: Z.land a (b * 2 ^ k) = 0).
  2:{ rewrite <- Z.lxor_lor by exact HL. symmetry. apply Z.add_nocarry_lxor. exact HL. }
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  destruct (zlt n k).
  - rewrite <- Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite <- (Z.mod_small a (2 ^ k)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma pf3_le32_of_unsigned b0 b1 b2 b3 :
  Int.unsigned (le32_of b0 b1 b2 b3) =
  Byte.unsigned b0 + 2 ^ 8 * Byte.unsigned b1 + 2 ^ 16 * Byte.unsigned b2 + 2 ^ 24 * Byte.unsigned b3.
Proof.
  pose proof (Byte.unsigned_range_2 b0). pose proof (Byte.unsigned_range_2 b1).
  pose proof (Byte.unsigned_range_2 b2). pose proof (Byte.unsigned_range_2 b3).
  unfold le32_of, Int.or, Int.shl.
  rewrite !(Int.unsigned_repr (Byte.unsigned _)) by rep_lia.
  change (Int.unsigned (Int.repr 8)) with 8. change (Int.unsigned (Int.repr 16)) with 16.
  change (Int.unsigned (Int.repr 24)) with 24.
  rewrite !Z.shiftl_mul_pow2 by lia.
  change (2 ^ 8) with 256 in *. change (2 ^ 16) with 65536 in *. change (2 ^ 24) with 16777216 in *.
  rewrite (Int.unsigned_repr (Byte.unsigned b1 * 256)) by rep_lia.
  rewrite (pf3_lor_disj _ _ 8) by (change (2 ^ 8) with 256; rep_lia). change (2 ^ 8) with 256.
  rewrite (Int.unsigned_repr (_ + _)) by rep_lia.
  rewrite (Int.unsigned_repr (Byte.unsigned b2 * 65536)) by rep_lia.
  rewrite (pf3_lor_disj _ _ 16) by (change (2 ^ 16) with 65536; rep_lia). change (2 ^ 16) with 65536.
  rewrite (Int.unsigned_repr (_ + _)) by rep_lia.
  rewrite (Int.unsigned_repr (Byte.unsigned b3 * 16777216)) by rep_lia.
  rewrite (pf3_lor_disj _ _ 24) by (change (2 ^ 24) with 16777216; rep_lia). change (2 ^ 24) with 16777216.
  rewrite Int.unsigned_repr by rep_lia. lia.
Qed.

Lemma pf3_sublist4 {A} {d: Inhabitant A} (l: list A) i :
  0 <= i -> i + 4 <= Zlength l ->
  sublist i (i + 4) l = [Znth i l; Znth (i + 1) l; Znth (i + 2) l; Znth (i + 3) l].
Proof.
  intros.
  rewrite (sublist_split i (i + 1) (i + 4)), (sublist_split (i + 1) (i + 1 + 1) (i + 4)),
    (sublist_split (i + 1 + 1) (i + 1 + 1 + 1) (i + 4)) by lia.
  replace (i + 4) with (i + 1 + 1 + 1 + 1) by lia.
  rewrite !sublist_len_1 by lia. replace (i + 2) with (i + 1 + 1) by lia.
  replace (i + 3) with (i + 1 + 1 + 1) by lia. reflexivity.
Qed.

Lemma pf3_le_Z_4 (key: list byte) i j :
  j = i + 4 -> 0 <= i -> j <= Zlength key -> le_Z (sublist i j key) = Int.unsigned (le32_at key i).
Proof.
  intros -> ? ?. rewrite pf3_sublist4 by auto. unfold le32_at. rewrite pf3_le32_of_unsigned.
  simpl le_Z. lia.
Qed.

Lemma pf3_s_words key : Zlength key = 32 -> words_Z (p1305_s_words key) = p1305_s key.
Proof.
  intros HK. unfold p1305_s, p1305_s_words. simpl words_Z.
  rewrite (sublist_split 16 20 32), (sublist_split 20 24 32), (sublist_split 24 28 32) by lia.
  rewrite !pf3_le_Z_app, !Zlength_sublist by lia.
  rewrite (pf3_le_Z_4 key 16 20), (pf3_le_Z_4 key 20 24), (pf3_le_Z_4 key 24 28), (pf3_le_Z_4 key 28 32) by lia.
  simpl. lia.
Qed.

Lemma pf3_le_Z_nonneg bs : 0 <= le_Z bs.
Proof. induction bs; simpl; [lia |]. pose proof (Byte.unsigned_range_2 a). lia. Qed.

Lemma pf3_r_ok key : p1305_r_ok (p1305_r key).
Proof.
  unfold p1305_r_ok, p1305_r. split.
  - rewrite <- Z.land_assoc, Z.land_diag. reflexivity.
  - apply Z.land_nonneg. right. lia.
Qed.
