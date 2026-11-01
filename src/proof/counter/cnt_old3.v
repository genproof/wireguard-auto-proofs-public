(* counter_validate's arithmetic, case t <= top (inside the window). *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.counter.counter_spec.
Require Import WgNoise.proof.counter.cnt_math3.

(* bit t lives at word (t / 64) mod 128, bit t mod 64: a function of t mod 8192 *)
Lemma cold3_mod_split : forall t, t mod 8192 = t mod 64 + 64 * ((t / 64) mod 128).
Proof.
  intros t. symmetry. apply Z.mod_unique with (q := (t / 64) / 128).
  - left. pose proof (Z.mod_pos_bound t 64 ltac:(lia)). pose proof (Z.mod_pos_bound (t / 64) 128 ltac:(lia)). lia.
  - pose proof (Z.div_mod t 64 ltac:(lia)). pose proof (Z.div_mod (t / 64) 128 ltac:(lia)). lia.
Qed.

Lemma cold3_lor_range : forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  0 <= Z.lor a b <= Int64.max_unsigned.
Proof.
  intros a b Ha Hb. split. apply Z.lor_nonneg; lia.
  assert (Z.lor a b < 2 ^ 64); [ | change Int64.max_unsigned with (2 ^ 64 - 1); lia].
  destruct (Z.eq_dec (Z.lor a b) 0) as [E | E]; [rewrite E; lia | ].
  apply Z.log2_lt_pow2; [ pose proof (Z.lor_nonneg a b); lia | ].
  rewrite Z.log2_lor by lia.
  change Int64.max_unsigned with (2 ^ 64 - 1) in *.
  apply Z.max_lub_lt.
  - destruct (Z.eq_dec a 0) as [-> | ]; [simpl; lia | apply Z.log2_lt_pow2; lia].
  - destruct (Z.eq_dec b 0) as [-> | ]; [simpl; lia | apply Z.log2_lt_pow2; lia].
Qed.

Lemma cold3_bit_set : forall bm t t', Zlength bm = 128 ->
  cnt_bit (cnt_set bm t) t' = orb (t' mod 8192 =? t mod 8192) (cnt_bit bm t').
Proof.
  intros bm t t' Hl. unfold cnt_bit, cnt_set.
  rewrite (cold3_mod_split t), (cold3_mod_split t').
  pose proof (Z.mod_pos_bound t 64 ltac:(lia)). pose proof (Z.mod_pos_bound t' 64 ltac:(lia)).
  pose proof (Z.mod_pos_bound (t / 64) 128 ltac:(lia)). pose proof (Z.mod_pos_bound (t' / 64) 128 ltac:(lia)).
  destruct (Z.eq_dec ((t' / 64) mod 128) ((t / 64) mod 128)) as [E | E].
  - rewrite E, upd_Znth_same by lia. rewrite Z.lor_spec, Z.shiftl_spec by lia.
    rewrite orb_comm. f_equal.
    destruct (Z.eq_dec (t' mod 64) (t mod 64)) as [E2 | E2].
    + rewrite E2, Z.sub_diag. simpl. symmetry. apply Z.eqb_eq. lia.
    + transitivity false; [ | symmetry; apply Z.eqb_neq; lia].
      destruct (Z_lt_le_dec (t' mod 64 - t mod 64) 0); [apply Z.testbit_neg_r; lia | ].
      change 1 with (2 ^ 0). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
  - rewrite upd_Znth_diff by lia.
    replace (t' mod 64 + 64 * ((t' / 64) mod 128) =? t mod 64 + 64 * ((t / 64) mod 128)) with false.
    reflexivity. symmetry. apply Z.eqb_neq. lia.
Qed.

Lemma cold3_mod_eq : forall a b, a mod 8192 = b mod 8192 -> -8192 < a - b < 8192 -> a = b.
Proof.
  intros a b E H. pose proof (Z.div_mod a 8192 ltac:(lia)). pose proof (Z.div_mod b 8192 ltac:(lia)).
  lia.
Qed.

(* t = n + 1 <= top: inside the window; the bit says whether n was accepted *)
Lemma cnt_math_old : forall top L bm n,
  cnt_inv top L bm -> 0 <= n < CNT_R -> top <= n + 1 + CNT_W -> n + 1 <= top ->
  cnt_ok top L n = negb (cnt_bit bm (n + 1)) /\ cnt_top' top L n = top /\
  cnt_inv top (cnt_L' top L n) (cnt_set bm (n + 1)).
Proof.
  intros top L bm n Hinv Hn Hw Ht. destruct Hinv as [Hlen Hwords Htop HL Hwin Habove].
  assert (Hb: cnt_bit bm (n + 1) = existsb (Z.eqb n) L).
  { rewrite Hwin by (unfold CNT_W in *; lia). f_equal. f_equal. lia. }
  assert (Hok: cnt_ok top L n = negb (cnt_bit bm (n + 1))).
  { unfold cnt_ok. rewrite Hb.
    replace (top <? CNT_R + 1) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (n <? CNT_R) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (top <=? n + 1 + CNT_W) with true by (symmetry; apply Z.leb_le; lia).
    reflexivity. }
  split; [exact Hok | ]. split.
  { unfold cnt_top'. destruct (cnt_ok top L n); lia. }
  assert (HL': forall x, existsb (Z.eqb x) (cnt_L' top L n) = orb (x =? n) (existsb (Z.eqb x) L)).
  { intros x. unfold cnt_L'. rewrite Hok, Hb.
    destruct (existsb (Z.eqb n) L) eqn:En; simpl; auto.
    destruct (Z.eqb_spec x n); subst; simpl; auto. }
  constructor.
  - unfold cnt_set. pose proof (Z.mod_pos_bound ((n + 1) / 64) 128 ltac:(lia)). rewrite upd_Znth_Zlength; lia.
  - unfold cnt_set. pose proof (Z.mod_pos_bound ((n + 1) / 64) 128 ltac:(lia)).
    apply Forall_upd_Znth; auto. apply cold3_lor_range.
    + apply Forall_Znth; auto; lia.
    + pose proof (Z.mod_pos_bound (n + 1) 64 ltac:(lia)). rewrite Z.shiftl_1_l. split.
      * apply Z.pow_nonneg; lia.
      * change Int64.max_unsigned with (2 ^ 64 - 1).
        assert (2 ^ ((n + 1) mod 64) < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia). lia.
  - auto.
  - intros x Hx. unfold cnt_L' in Hx. destruct (cnt_ok top L n).
    + destruct Hx as [<- | Hx]; [lia | auto].
    + auto.
  - intros t Hr. rewrite cold3_bit_set by auto. rewrite Hwin by auto.
    replace (existsb (Z.eqb (t - 1)) (cnt_L' top L n)) with (orb (t - 1 =? n) (existsb (Z.eqb (t - 1)) L))
      by (symmetry; apply HL').
    destruct (Z.eqb_spec (t mod 8192) ((n + 1) mod 8192)) as [E | E].
    + apply cold3_mod_eq in E; [ | unfold CNT_W in *; lia].
      replace (t - 1 =? n) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
    + replace (t - 1 =? n) with false by (symmetry; apply Z.eqb_neq; intro; apply E; f_equal; lia).
      reflexivity.
  - intros t Hr. rewrite cold3_bit_set by auto. rewrite Habove by auto.
    destruct (Z.eqb_spec (t mod 8192) ((n + 1) mod 8192)) as [E | E]; [ | reflexivity].
    exfalso. apply cold3_mod_eq in E.
    + lia.
    + pose proof (Z.mul_div_le top 64 ltac:(lia)). unfold CNT_W in *; lia.
Qed.
