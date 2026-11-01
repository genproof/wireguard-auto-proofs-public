(* model facts and byte-array helpers for the P23 loops chacha20_crypt_long / poly1305_update_long.  The first lemmas are copies of aead_chacha_body.v's (prefix lg3_). *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.aead.aead_model.

Local Open Scope Z_scope.

Lemma lg3_Zlength_qround x a b c d : Zlength (chacha_qround x a b c d) = Zlength x.
Proof.
  unfold chacha_qround. rewrite !Zlength_upd_Znth. reflexivity.
Qed.

Lemma lg3_Zlength_dround x : Zlength (chacha_dround x) = Zlength x.
Proof.
  unfold chacha_dround. rewrite !lg3_Zlength_qround. reflexivity.
Qed.

(* (the kernel compares the arguments of chacha_rounds right to left: never let it compare
   chacha_rounds (S n) x with chacha_rounds n (chacha_dround x), go through the unfolded fix) *)
Lemma lg3_Zlength_rounds n x : Zlength (chacha_rounds n x) = Zlength x.
Proof.
  revert x; induction n; intros x; [reflexivity |].
  change (Zlength ((fix rounds (n : nat) (x : list int) {struct n} : list int :=
                      match n with O => x | S k => rounds k (chacha_dround x) end) n (chacha_dround x))
          = Zlength x).
  transitivity (Zlength (chacha_dround x)).
  - exact (IHn (chacha_dround x)).
  - apply lg3_Zlength_dround.
Qed.

Lemma lg3_Zlength_words_bytes ws : Zlength (words_bytes ws) = 4 * Zlength ws.
Proof.
  unfold words_bytes. induction ws; cbn [map concat]; auto.
  rewrite Zlength_app, IHws, Zlength_cons. unfold le32_bytes. rewrite !Zlength_cons, Zlength_nil. lia.
Qed.

Lemma lg3_Zlength_add_words a b : Zlength a = Zlength b -> Zlength (add_words a b) = Zlength a.
Proof.
  intros H. unfold add_words. rewrite Zlength_map. rewrite !Zlength_correct in *.
  rewrite combine_length. lia.
Qed.

Lemma lg3_Zlength_block_bytes n st : Zlength st = 16 -> Zlength (chacha_block_bytes n st) = 64.
Proof.
  intros H. unfold chacha_block_bytes, chacha_block_words.
  rewrite lg3_Zlength_words_bytes, lg3_Zlength_add_words; rewrite ?lg3_Zlength_rounds; lia.
Qed.

Lemma lg3_Zlength_advance st k : Zlength (chacha_advance st k) = Zlength st.
Proof. unfold chacha_advance. apply Zlength_upd_Znth. Qed.

Lemma lg3_advance_0 st : Zlength st = 16 -> chacha_advance st 0 = st.
Proof.
  intros H. unfold chacha_advance. rewrite Int.add_zero. apply upd_Znth_triv; auto; lia.
Qed.

Lemma lg3_advance_advance st a b :
  Zlength st = 16 -> chacha_advance (chacha_advance st a) b = chacha_advance st (a + b).
Proof.
  intros H. unfold chacha_advance.
  rewrite upd_Znth_same by lia. rewrite upd_Znth_twice by lia.
  rewrite Int.add_assoc, add_repr. reflexivity.
Qed.

Lemma lg3_Zlength_stream n st k :
  Zlength st = 16 -> Zlength (chacha_stream n st k) = 64 * Z.of_nat k.
Proof.
  revert st; induction k; intros st H; cbn [chacha_stream]; auto.
  rewrite Zlength_app, lg3_Zlength_block_bytes, IHk by (rewrite ?lg3_Zlength_advance; auto). lia.
Qed.

Lemma lg3_stream_snoc n st k :
  Zlength st = 16 ->
  chacha_stream n st (S k) = chacha_stream n st k ++ chacha_block_bytes n (chacha_advance st (Z.of_nat k)).
Proof.
  revert st; induction k; intros st H.
  - cbn [chacha_stream Z.of_nat]. rewrite lg3_advance_0 by auto. rewrite app_nil_r; auto.
  - change (chacha_stream n st (S (S k))) with
      (chacha_block_bytes n st ++ chacha_stream n (chacha_advance st 1) (S k)).
    rewrite IHk by (rewrite lg3_Zlength_advance; auto).
    rewrite lg3_advance_advance by auto. rewrite app_assoc. do 2 f_equal. f_equal. lia.
Qed.

Lemma lg3_Zlength_xor a b : Zlength (xor_bytes a b) = Z.min (Zlength a) (Zlength b).
Proof.
  unfold xor_bytes. rewrite Zlength_map, !Zlength_correct, combine_length. lia.
Qed.

Lemma lg3_xor_app a1 a2 b1 b2 :
  Zlength a1 = Zlength b1 -> xor_bytes (a1 ++ a2) (b1 ++ b2) = xor_bytes a1 b1 ++ xor_bytes a2 b2.
Proof.
  revert b1; induction a1; intros b1 H; destruct b1; simpl; auto;
    rewrite ?Zlength_cons, ?Zlength_nil in H.
  - pose proof (Zlength_nonneg b1); lia.
  - pose proof (Zlength_nonneg a1); lia.
  - unfold xor_bytes in *; simpl. f_equal. apply IHa1. lia.
Qed.

Lemma lg3_xor_trunc a b : Zlength a <= Zlength b -> xor_bytes a b = xor_bytes a (sublist 0 (Zlength a) b).
Proof.
  intros H. pose proof (Zlength_nonneg a).
  assert (Hb: b = sublist 0 (Zlength a) b ++ sublist (Zlength a) (Zlength b) b)
    by (rewrite sublist_rejoin, sublist_same; auto; lia).
  rewrite Hb at 1. rewrite <- (app_nil_r a) at 1. rewrite lg3_xor_app.
  - change (xor_bytes [] (sublist (Zlength a) (Zlength b) b)) with (@nil byte). apply app_nil_r.
  - rewrite Zlength_sublist; lia.
Qed.

Lemma lg3_nblocks_full k : 0 <= k -> chacha_nblocks (64 * k) = k.
Proof.
  intros. unfold chacha_nblocks. symmetry. apply Z.div_unique with 63; lia.
Qed.

Lemma lg3_nblocks_tail k len : 0 <= k -> 64 * k < len < 64 * k + 64 -> chacha_nblocks len = k + 1.
Proof.
  intros. unfold chacha_nblocks. symmetry. apply Z.div_unique with (len + 63 - 64 * (k + 1)); lia.
Qed.

Lemma lg3_split3 {cs: compspecs} sh n i j (v: list val) p :
  0 <= i -> 0 <= j -> i + j <= n -> Zlength v = n -> field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) v p =
  (data_at sh (tarray tuchar i) (sublist 0 i v) p *
   data_at sh (tarray tuchar j) (sublist i (i + j) v) (offset_val i p) *
   data_at sh (tarray tuchar (n - (i + j))) (sublist (i + j) n v) (offset_val (i + j) p))%logic.
Proof.
  intros. unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh n i (i + j)) by lia.
  fold (tarray tuchar n). rewrite !arr_field_address0 by (auto; lia).
  change (sizeof tuchar) with 1. rewrite !Z.mul_1_l. replace (i + j - i) with j by lia. reflexivity.
Qed.

Lemma lg3_split2 {cs: compspecs} sh n i (v: list val) p :
  0 <= i <= n -> Zlength v = n -> field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) v p =
  (data_at sh (tarray tuchar i) (sublist 0 i v) p *
   data_at sh (tarray tuchar (n - i)) (sublist i n v) (offset_val i p))%logic.
Proof.
  intros. unfold tarray. rewrite (split2_data_at_Tarray_tuchar sh n i) by lia.
  fold (tarray tuchar n). rewrite arr_field_address0 by (auto; lia).
  change (sizeof tuchar) with 1. rewrite Z.mul_1_l. reflexivity.
Qed.

Lemma lg3_split2_ {cs: compspecs} sh n i p :
  0 <= i <= n -> field_compatible (tarray tuchar n) [] p ->
  data_at_ sh (tarray tuchar n) p =
  (data_at_ sh (tarray tuchar i) p * data_at_ sh (tarray tuchar (n - i)) (offset_val i p))%logic.
Proof.
  intros. rewrite !data_at__tarray. rewrite (lg3_split2 sh n i) by (auto; rewrite Zlength_Zrepeat; lia).
  rewrite !sublist_Zrepeat by lia. f_equal; f_equal; f_equal; lia.
Qed.

(* the keystream continues across a cut at a whole number of blocks *)
Lemma lg3_stream_app n st a b :
  Zlength st = 16 ->
  chacha_stream n st (a + b) = chacha_stream n st a ++ chacha_stream n (chacha_advance st (Z.of_nat a)) b.
Proof.
  revert st; induction a; intros st H.
  - cbn [chacha_stream Z.of_nat plus]. rewrite lg3_advance_0 by auto. reflexivity.
  - change (chacha_stream n st (S a + b)) with
      (chacha_block_bytes n st ++ chacha_stream n (chacha_advance st 1) (a + b)).
    change (chacha_stream n st (S a)) with
      (chacha_block_bytes n st ++ chacha_stream n (chacha_advance st 1) a).
    rewrite IHa by (rewrite lg3_Zlength_advance; auto).
    rewrite lg3_advance_advance by auto. rewrite app_assoc. do 3 f_equal. lia.
Qed.

Lemma lg3_nblocks_add k len : 0 <= k -> 0 <= len -> chacha_nblocks (64 * k + len) = k + chacha_nblocks len.
Proof.
  intros. unfold chacha_nblocks.
  replace (64 * k + len + 63) with ((len + 63) + k * 64) by lia. rewrite Z.div_add by lia. lia.
Qed.

Lemma lg3_nblocks_nonneg len : 0 <= len -> 0 <= chacha_nblocks len.
Proof. intros. unfold chacha_nblocks. apply Z.div_pos; lia. Qed.

Lemma lg3_chacha_xor_app m1 m2 n st :
  Zlength st = 16 -> Zlength m1 mod 64 = 0 ->
  chacha_xor n st (m1 ++ m2) =
  chacha_xor n st m1 ++ chacha_xor n (chacha_advance st (chacha_nblocks (Zlength m1))) m2.
Proof.
  intros H Hm. pose proof (Zlength_nonneg m1). pose proof (Zlength_nonneg m2).
  set (k := Zlength m1 / 64).
  assert (Hk: Zlength m1 = 64 * k) by (subst k; pose proof (Z.div_mod (Zlength m1) 64); lia).
  assert (Hk0: 0 <= k) by lia.
  unfold chacha_xor. rewrite Zlength_app, Hk, lg3_nblocks_add by lia. rewrite (lg3_nblocks_full k) by lia.
  rewrite Z2Nat.inj_add by (auto; apply lg3_nblocks_nonneg; lia).
  rewrite lg3_stream_app by auto. rewrite Z2Nat.id by lia.
  rewrite lg3_xor_app; auto.
  rewrite lg3_Zlength_stream, Z2Nat.id by lia. lia.
Qed.

Lemma lg3_Zlength_chacha_xor n st m : Zlength st = 16 -> Zlength (chacha_xor n st m) = Zlength m.
Proof.
  intros H. pose proof (Zlength_nonneg m). unfold chacha_xor.
  rewrite lg3_Zlength_xor, lg3_Zlength_stream by auto. rewrite Z2Nat.id by (apply lg3_nblocks_nonneg; lia).
  unfold chacha_nblocks. pose proof (Z.div_mod (Zlength m + 63) 64). pose proof (Z.mod_pos_bound (Zlength m + 63) 64).
  lia.
Qed.
