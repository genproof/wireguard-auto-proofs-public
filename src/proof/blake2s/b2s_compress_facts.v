(* blake2s_compress_generic: facts about the model (model.v) used by its body proof. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.blake2s.model.
Local Open Scope Z_scope.

(* the n-th block is compressed last *)
Lemma b2s_compress_n_snoc k h t f0 inc bs :
  64 * (Z.of_nat k + 1) <= Zlength bs ->
  b2s_compress_n (S k) h t f0 inc bs =
  b2s_compress_block (b2s_compress_n k h t f0 inc bs)
    (sublist (64 * Z.of_nat k) (64 * Z.of_nat k + 64) bs) (t + (Z.of_nat k + 1) * inc) f0.
Proof.
  revert h t bs. induction k; intros h t bs Hl.
  - change (Z.of_nat 0) with 0.
    change (b2s_compress_n 1 h t f0 inc bs) with
      (b2s_compress_n 0 (b2s_compress_block h (sublist 0 64 bs) (t + inc) f0)
                           (t + inc) f0 inc (sublist 64 (Zlength bs) bs)).
    cbn [b2s_compress_n]. f_equal. lia.
  - change (b2s_compress_n (S (S k)) h t f0 inc bs) with
      (b2s_compress_n (S k) (b2s_compress_block h (sublist 0 64 bs) (t + inc) f0)
                           (t + inc) f0 inc (sublist 64 (Zlength bs) bs)).
    rewrite IHk by (rewrite Zlength_sublist; lia).
    change (b2s_compress_n (S k) h t f0 inc bs) with
      (b2s_compress_n k (b2s_compress_block h (sublist 0 64 bs) (t + inc) f0)
                           (t + inc) f0 inc (sublist 64 (Zlength bs) bs)).
    f_equal.
    + rewrite sublist_sublist by lia. f_equal; lia.
    + lia.
Qed.

(* a word of a block is the word of the whole buffer at the block's offset *)
Lemma b2s_word_sublist bs o i :
  0 <= o -> 0 <= i < 16 -> o + 64 <= Zlength bs ->
  b2s_word (sublist o (o + 64) bs) i = le32_at bs (o + 4 * i).
Proof.
  intros. unfold b2s_word, le32_at.
  rewrite !Znth_sublist by lia.
  f_equal; f_equal; lia.
Qed.

Lemma b2s_words_Znth blk i : 0 <= i < 16 -> Znth i (b2s_words blk) = b2s_word blk i.
Proof.
  intros. unfold b2s_words. rewrite Znth_map by (rewrite Zlength_upto; change (Z.of_nat 16) with 16; lia).
  rewrite Znth_upto by (change (Z.of_nat 16) with 16; lia). reflexivity.
Qed.

Lemma b2s_Zlength_words blk : Zlength (b2s_words blk) = 16.
Proof. unfold b2s_words. rewrite Zlength_map, Zlength_upto. reflexivity. Qed.

Lemma b2s_Zlength_G v a b c d x y : Zlength (b2s_G v a b c d x y) = Zlength v.
Proof. unfold b2s_G. cbv zeta. rewrite !Zlength_upd_Znth. reflexivity. Qed.

Lemma b2s_Zlength_round m v s : Zlength (b2s_round m v s) = Zlength v.
Proof. unfold b2s_round. cbv zeta. rewrite !b2s_Zlength_G. reflexivity. Qed.

Lemma b2s_rounds_succ m v r : 0 <= r < 10 ->
  b2s_rounds m v (r + 1) = b2s_round m (b2s_rounds m v r) (Znth r b2s_sigma).
Proof.
  intros. unfold b2s_rounds.
  assert (Zlength b2s_sigma = 10) by reflexivity.
  rewrite (sublist_split 0 r (r + 1)) by lia. rewrite fold_left_app.
  rewrite sublist_len_1 by lia. reflexivity.
Qed.

Lemma b2s_fold_len {A B} (f: list A -> B -> list A) :
  (forall v s, Zlength (f v s) = Zlength v) -> forall l v, Zlength (fold_left f l v) = Zlength v.
Proof. intros H l; induction l; intros; simpl; auto. rewrite IHl, H; auto. Qed.

Lemma b2s_Zlength_rounds m v r : Zlength (b2s_rounds m v r) = Zlength v.
Proof. unfold b2s_rounds. apply b2s_fold_len. apply b2s_Zlength_round. Qed.

Lemma b2s_Znth_feed h v i : 0 <= i < 8 ->
  Znth i (b2s_feed h v) = Int.xor (Znth i h) (Int.xor (Znth i v) (Znth (i + 8) v)).
Proof.
  intros. unfold b2s_feed. rewrite Znth_map by (rewrite Zlength_upto; change (Z.of_nat 8) with 8; lia).
  rewrite Znth_upto by (change (Z.of_nat 8) with 8; lia). reflexivity.
Qed.

Lemma b2s_Zlength_feed h v : Zlength (b2s_feed h v) = 8.
Proof. unfold b2s_feed. rewrite Zlength_map, Zlength_upto. reflexivity. Qed.

Lemma b2s_Zlength_compress_n k h t f0 inc bs :
  Zlength h = 8 -> Zlength (b2s_compress_n k h t f0 inc bs) = 8.
Proof.
  revert h t bs. induction k; intros h t bs Hh; [exact Hh |].
  change (b2s_compress_n (S k) h t f0 inc bs) with
    (b2s_compress_n k (b2s_compress_block h (sublist 0 64 bs) (t + inc) f0)
                         (t + inc) f0 inc (sublist 64 (Zlength bs) bs)).
  apply IHk. unfold b2s_compress_block, b2s_compress. apply b2s_Zlength_feed.
Qed.
