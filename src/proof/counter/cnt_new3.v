(* counter_validate's arithmetic, case t > top (new top). *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.counter.counter_spec.
Require Import WgNoise.proof.counter.cnt_math3.

Lemma cnew3_clear_n_len : forall bm ic k, Zlength bm = 128 -> Zlength (cnt_clear_n bm ic k) = 128.
Proof.
  induction k; intros; simpl; auto.
  rewrite upd_Znth_Zlength; rewrite IHk; auto. pose proof (Z.mod_pos_bound (Z.pos (Pos.of_succ_nat k) + ic) 128). lia.
Qed.

Lemma cnew3_clear_n_znth : forall bm ic k j, Zlength bm = 128 -> 0 <= j < 128 -> Z.of_nat k <= 128 ->
  Znth j (cnt_clear_n bm ic k) = if (j - ic - 1) mod 128 <? Z.of_nat k then 0 else Znth j bm.
Proof.
  intros bm ic k; induction k; intros j Hl Hj Hk.
  - simpl. pose proof (Z.mod_pos_bound (j - ic - 1) 128).
    destruct (Z.ltb_spec ((j - ic - 1) mod 128) 0); [lia | auto].
  - change (cnt_clear_n bm ic (S k)) with
      (upd_Znth ((Z.of_nat (S k) + ic) mod 128) (cnt_clear_n bm ic k) 0).
    pose proof (Z.mod_pos_bound (Z.of_nat (S k) + ic) 128).
    pose proof (cnew3_clear_n_len bm ic k Hl).
    destruct (Z.eq_dec j ((Z.of_nat (S k) + ic) mod 128)).
    + rewrite e, upd_Znth_same by lia. rewrite <- e.
      destruct (Z.ltb_spec ((j - ic - 1) mod 128) (Z.of_nat (S k))); auto.
      exfalso. rewrite Nat2Z.inj_succ in *. Z.to_euclidean_division_equations. lia.
    + rewrite upd_Znth_diff by lia. rewrite IHk by lia.
      destruct (Z.ltb_spec ((j - ic - 1) mod 128) (Z.of_nat k));
      destruct (Z.ltb_spec ((j - ic - 1) mod 128) (Z.of_nat (S k))); auto; try lia.
      exfalso. apply n. rewrite Nat2Z.inj_succ in *. Z.to_euclidean_division_equations. lia.
Qed.

Lemma cnew3_clear_znth : forall bm ic k j, Zlength bm = 128 -> 0 <= j < 128 -> 0 <= k <= 128 ->
  Znth j (cnt_clear bm ic k) = if (j - ic - 1) mod 128 <? k then 0 else Znth j bm.
Proof.
  intros. unfold cnt_clear. rewrite cnew3_clear_n_znth by lia. rewrite Z2Nat.id by lia. auto.
Qed.

Lemma cnew3_clear_words : forall bm ic k,
  Forall (fun w => 0 <= w <= Int64.max_unsigned) bm ->
  Forall (fun w => 0 <= w <= Int64.max_unsigned) (cnt_clear_n bm ic k).
Proof.
  induction k; intros; simpl; auto.
  apply Forall_upd_Znth; auto. rep_lia.
Qed.

Lemma cnew3_lor_bound : forall w m, 0 <= w <= Int64.max_unsigned -> 0 <= m < 64 ->
  0 <= Z.lor w (Z.shiftl 1 m) <= Int64.max_unsigned.
Proof.
  intros. rewrite Z.shiftl_1_l.
  assert (0 < 2 ^ m) by (apply Z.pow_pos_nonneg; lia).
  split. apply Z.lor_nonneg; lia.
  assert (Z.lor w (2 ^ m) < 2 ^ 64); [|rep_lia].
  assert (0 < Z.lor w (2 ^ m)).
  { destruct (Z.lt_trichotomy 0 (Z.lor w (2 ^ m))) as [?|[?|?]]; auto.
    - symmetry in H2. apply Z.lor_eq_0_iff in H2. lia.
    - pose proof (Z.lor_nonneg w (2 ^ m)). lia. }
  apply Z.log2_lt_pow2; auto. rewrite Z.log2_lor by lia. rewrite Z.log2_pow2 by lia.
  apply Z.max_lub_lt; [|lia].
  destruct (Z.eq_dec w 0). subst; simpl; lia.
  apply Z.log2_lt_pow2. lia. unfold Int64.max_unsigned in H; simpl in H. simpl. lia.
Qed.

Lemma cnew3_set_len : forall bm t, Zlength bm = 128 -> Zlength (cnt_set bm t) = 128.
Proof.
  intros. unfold cnt_set. pose proof (Z.mod_pos_bound (t / 64) 128).
  rewrite upd_Znth_Zlength; lia.
Qed.

Lemma cnew3_set_words : forall bm t, Zlength bm = 128 ->
  Forall (fun w => 0 <= w <= Int64.max_unsigned) bm ->
  Forall (fun w => 0 <= w <= Int64.max_unsigned) (cnt_set bm t).
Proof.
  intros. unfold cnt_set. pose proof (Z.mod_pos_bound (t / 64) 128).
  apply Forall_upd_Znth; auto. apply cnew3_lor_bound.
  apply Forall_Znth; auto. lia. apply Z.mod_pos_bound; lia.
Qed.

Lemma cnew3_bit_set : forall bm t s, Zlength bm = 128 ->
  cnt_bit (cnt_set bm t) s = orb (cnt_bit bm s) ((s - t) mod 8192 =? 0).
Proof.
  intros. unfold cnt_bit, cnt_set.
  pose proof (Z.mod_pos_bound (t / 64) 128). pose proof (Z.mod_pos_bound (s / 64) 128).
  pose proof (Z.mod_pos_bound s 64). pose proof (Z.mod_pos_bound t 64).
  destruct (Z.eq_dec ((s / 64) mod 128) ((t / 64) mod 128)).
  - rewrite e, upd_Znth_same by lia. rewrite Z.lor_spec, Z.shiftl_1_l, Z.pow2_bits_eqb by lia.
    f_equal.
    destruct (Z.eqb_spec (t mod 64) (s mod 64)); destruct (Z.eqb_spec ((s - t) mod 8192) 0); auto;
      exfalso; apply n; Z.to_euclidean_division_equations; lia.
  - rewrite upd_Znth_diff by lia.
    destruct (Z.eqb_spec ((s - t) mod 8192) 0); [|rewrite orb_false_r; auto].
    exfalso; apply n; Z.to_euclidean_division_equations; lia.
Qed.

Lemma cnew3_existsb_false : forall (L: list Z) n, (forall x, In x L -> x <> n) -> existsb (Z.eqb n) L = false.
Proof.
  induction L; intros; simpl; auto.
  destruct (Z.eqb_spec n a). subst; exfalso; apply (H a); simpl; auto.
  simpl. apply IHL. intros; apply H; simpl; auto.
Qed.

(* t = n + 1 > top: the new top; after the clearing loop the bit is clear and n is accepted *)
Lemma cnt_math_new : forall top L bm n,
  cnt_inv top L bm -> 0 <= n < CNT_R -> top < n + 1 ->
  let bm1 := cnt_clear bm (top / 64) (Z.min ((n + 1) / 64 - top / 64) 128) in
  cnt_bit bm1 (n + 1) = false /\ cnt_ok top L n = true /\ cnt_top' top L n = n + 1 /\
  cnt_L' top L n = n :: L /\ cnt_inv (n + 1) (n :: L) (cnt_set bm1 (n + 1)).
Proof.
  intros top L bm n Hinv Hn Hlt bm1. destruct Hinv as [Hlen Hw Htop HL Hwin Habove].
  assert (HW: CNT_W = 8128) by reflexivity.
  assert (Hic: top / 64 <= (n + 1) / 64) by (apply Z.div_le_mono; lia).
  set (k := Z.min ((n + 1) / 64 - top / 64) 128) in bm1.
  assert (Hk: 0 <= k <= 128) by lia.
  assert (Hlen1: Zlength bm1 = 128) by (apply cnew3_clear_n_len; auto).
  (* above the old top up to the end of t's word: clear *)
  assert (HB: forall s, top < s < 64 * ((n + 1) / 64 + 1) -> cnt_bit bm1 s = false).
  { intros s Hs. unfold cnt_bit. pose proof (Z.mod_pos_bound (s / 64) 128).
    subst bm1. rewrite cnew3_clear_znth by lia.
    destruct (Z.ltb_spec (((s / 64) mod 128 - top / 64 - 1) mod 128) k).
    - apply Z.testbit_0_l.
    - change (cnt_bit bm s = false). apply Habove. split; [lia|].
      subst k. clear - Hs H0 Hlt Hn Hic. Z.to_euclidean_division_equations. lia. }
  (* the old window's part of the new window: unchanged *)
  assert (HC: forall s, n + 1 - CNT_W <= s <= top -> cnt_bit bm1 s = cnt_bit bm s).
  { intros s Hs. unfold cnt_bit. pose proof (Z.mod_pos_bound (s / 64) 128).
    subst bm1. rewrite cnew3_clear_znth by lia.
    destruct (Z.ltb_spec (((s / 64) mod 128 - top / 64 - 1) mod 128) k); auto.
    exfalso. rewrite HW in Hs. subst k. clear - Hs H0 Hlt Hn Hic. Z.to_euclidean_division_equations. lia. }
  assert (HnL: existsb (Z.eqb n) L = false).
  { apply cnew3_existsb_false. intros x Hx; specialize (HL x Hx); lia. }
  assert (Hok: cnt_ok top L n = true).
  { unfold cnt_ok. rewrite HnL.
    destruct (Z.ltb_spec top (CNT_R + 1)); [|lia].
    destruct (Z.ltb_spec n CNT_R); [|lia].
    destruct (Z.leb_spec top (n + 1 + CNT_W)); [|lia]. reflexivity. }
  assert (Ht64: n + 1 < 64 * ((n + 1) / 64 + 1)) by (pose proof (Z.mod_pos_bound (n + 1) 64); pose proof (Z.div_mod (n + 1) 64); lia).
  split; [apply HB; lia|].
  split; [auto|].
  split; [unfold cnt_top'; rewrite Hok; lia|].
  split; [unfold cnt_L'; rewrite Hok; auto|].
  constructor.
  - apply cnew3_set_len; auto.
  - apply cnew3_set_words; auto. apply cnew3_clear_words; auto.
  - lia.
  - intros x [Hx|Hx]; [subst; lia|]. specialize (HL x Hx); lia.
  - intros s Hs. rewrite cnew3_bit_set by auto. simpl existsb.
    destruct (Z.eq_dec s (n + 1)).
    + subst s. replace (n + 1 - (n + 1)) with 0 by lia. rewrite Z.eqb_refl.
      rewrite orb_true_r. replace (n + 1 - 1) with n by lia. rewrite Z.eqb_refl. auto.
    + assert (((s - (n + 1)) mod 8192 =? 0) = false).
      { apply Z.eqb_neq. rewrite HW in Hs. clear - Hs n0. Z.to_euclidean_division_equations. lia. }
      rewrite H, orb_false_r.
      assert ((s - 1 =? n) = false) by (apply Z.eqb_neq; lia). rewrite H0. simpl.
      destruct (Z.le_gt_cases s top).
      * rewrite HC by lia. apply Hwin. lia.
      * rewrite HB by lia. symmetry. apply cnew3_existsb_false.
        intros x Hx; specialize (HL x Hx); lia.
  - intros s Hs. rewrite cnew3_bit_set by auto.
    assert (((s - (n + 1)) mod 8192 =? 0) = false).
    { apply Z.eqb_neq. clear - Hs Hlt. Z.to_euclidean_division_equations. lia. }
    rewrite H, orb_false_r. apply HB. lia.
Qed.
