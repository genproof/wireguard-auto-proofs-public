(* model facts for the body of blake2s_update (b2s_update_body3.v): the non-final blocks of a stream
   extended by a chunk, block by block. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.blake2s.model.
Local Open Scope Z_scope.

Lemma b2s_u3_compress_n_app a b h t f inc A B :
  Zlength A = 64 * Z.of_nat a ->
  b2s_compress_n (a + b) h t f inc (A ++ B) =
  b2s_compress_n b (b2s_compress_n a h t f inc A) (t + Z.of_nat a * inc) f inc B.
Proof.
  revert h t A; induction a; intros h t A HA.
  - simpl in HA. apply Zlength_nil_inv in HA. subst A. simpl. rewrite Z.add_0_r. reflexivity.
  - rewrite Nat2Z.inj_succ in HA.
    replace (S a + b)%nat with (S (a + b)) by reflexivity.
    cbn [b2s_compress_n].
    rewrite sublist_app1 by lia.
    replace (sublist 64 (Zlength (A ++ B)) (A ++ B)) with (sublist 64 (Zlength A) A ++ B) by list_solve.
    rewrite IHa by (rewrite Zlength_sublist; lia).
    f_equal. lia.
Qed.

Lemma b2s_u3_blocks_app h t A B :
  Zlength A mod 64 = 0 ->
  b2s_blocks h t (A ++ B) = b2s_blocks (b2s_blocks h t A) (t + Zlength A) B.
Proof.
  intros HA. unfold b2s_blocks.
  pose proof (Zlength_nonneg A). pose proof (Zlength_nonneg B).
  assert (EA: Zlength A = 64 * (Zlength A / 64)) by (pose proof (Z.div_mod (Zlength A) 64); lia).
  rewrite Zlength_app.
  replace (Zlength A + Zlength B) with (Zlength B + (Zlength A / 64) * 64) by lia.
  rewrite Z.div_add by lia.
  assert (0 <= Zlength A / 64) by (apply Z.div_pos; lia).
  assert (0 <= Zlength B / 64) by (apply Z.div_pos; lia).
  rewrite Z.add_comm, Z2Nat.inj_add by lia.
  rewrite b2s_u3_compress_n_app by (rewrite Z2Nat.id by lia; lia).
  f_equal. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma b2s_u3_blocks_n h t bs n :
  0 <= n -> Zlength bs = 64 * n ->
  b2s_compress_n (Z.to_nat n) h t Int.zero 64 bs = b2s_blocks h t bs.
Proof.
  intros. unfold b2s_blocks. rewrite H0. f_equal. f_equal.
  rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.

Lemma b2s_u3_blocks_nil h t : b2s_blocks h t [] = h.
Proof. reflexivity. Qed.

(* a stream = whole blocks ++ a nonempty last block of at most 64 bytes *)
Lemma b2s_u3_split s p rest :
  s = p ++ rest -> Zlength p mod 64 = 0 -> 1 <= Zlength rest <= 64 ->
  b2s_nfull s = Zlength p / 64 /\ b2s_lastblock s = rest /\ sublist 0 (64 * b2s_nfull s) s = p.
Proof.
  intros Es Hp Hr. pose proof (Zlength_nonneg p).
  assert (EA: Zlength p = 64 * (Zlength p / 64)) by (pose proof (Z.div_mod (Zlength p) 64); lia).
  assert (Hn: b2s_nfull s = Zlength p / 64).
  { unfold b2s_nfull. subst s. rewrite Zlength_app.
    destruct (Zlength p + Zlength rest =? 0) eqn:E; [apply Z.eqb_eq in E; lia|].
    replace (Zlength p + Zlength rest - 1) with ((Zlength rest - 1) + (Zlength p / 64) * 64) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  split; [exact Hn|]. split.
  - unfold b2s_lastblock. rewrite Hn, <- EA. subst s. list_solve.
  - rewrite Hn, <- EA. subst s. list_solve.
Qed.

(* the shape of a stream: its whole blocks and its last block *)
Lemma b2s_u3_decomp s :
  let k := b2s_nfull s in
  let last := b2s_lastblock s in
  0 <= k /\ s = sublist 0 (64 * k) s ++ last /\ Zlength (sublist 0 (64 * k) s) = 64 * k /\
  Zlength last <= 64 /\ (Zlength s = 0 \/ 1 <= Zlength last).
Proof.
  intros k last. unfold k, last, b2s_lastblock, b2s_nfull.
  pose proof (Zlength_nonneg s).
  destruct (Zlength s =? 0) eqn:E.
  - apply Z.eqb_eq in E. rewrite E. apply Zlength_nil_inv in E. subst s. simpl. list_solve.
  - apply Z.eqb_neq in E.
    assert (0 <= (Zlength s - 1) / 64) by (apply Z.div_pos; lia).
    pose proof (Z.mul_div_le (Zlength s - 1) 64 ltac:(lia)).
    pose proof (Z.mod_pos_bound (Zlength s - 1) 64 ltac:(lia)).
    pose proof (Z.div_mod (Zlength s - 1) 64 ltac:(lia)).
    split; [lia|]. split; [rewrite sublist_rejoin by lia; rewrite sublist_same by lia; reflexivity|].
    rewrite !Zlength_sublist by lia. lia.
Qed.

Lemma b2s_u3_compress_n_len n h t f inc d :
  Zlength h = 8 -> Zlength (b2s_compress_n n h t f inc d) = 8.
Proof.
  revert h t d; induction n; intros h t d Hh; simpl; auto.
Qed.

Lemma b2s_u3_blocks_len keylen outlen t bs :
  Zlength (b2s_blocks (b2s_h0 keylen outlen) t bs) = 8.
Proof.
  unfold b2s_blocks. apply b2s_u3_compress_n_len.
  unfold b2s_h0. rewrite upd_Znth_Zlength; [reflexivity | cbn; lia].
Qed.
