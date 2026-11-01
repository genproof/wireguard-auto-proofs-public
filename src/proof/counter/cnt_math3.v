(* the pure arithmetic of counter_validate: preservation of the RFC 6479 window
   invariant cnt_inv (counter_spec.v) by the three paths of the code.

   The code, with t = n + 1 (n the nonce), top = counter->counter, ic = top / 64:
   - reject early when top >= R + 1, n >= R or W + t < top: nothing changes;
   - if t > top: clear the words (ic + j) mod 128 for j = 1 .. min (t / 64 - ic, 128) (cnt_clear), set top := t;
   - then test_and_set_bit: bit t mod 64 of word (t / 64) mod 128 (cnt_set); accept iff the bit was clear. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.counter.counter_spec.

(* the loop: words (ic + j) mod 128 zeroed for j = 1 .. k *)
Fixpoint cnt_clear_n (bm: list Z) (ic: Z) (k: nat) : list Z :=
  match k with
  | O => bm
  | S k' => upd_Znth ((Z.of_nat k + ic) mod 128) (cnt_clear_n bm ic k') 0
  end.

Definition cnt_clear (bm: list Z) (ic k: Z) : list Z := cnt_clear_n bm ic (Z.to_nat k).

(* test_and_set_bit's store: bit t mod 64 of word (t / 64) mod 128 *)
Definition cnt_set (bm: list Z) (t: Z) : list Z :=
  upd_Znth ((t / 64) mod 128) bm (Z.lor (Znth ((t / 64) mod 128) bm) (Z.shiftl 1 (t mod 64))).

Lemma cnt_clear_0 : forall bm ic, cnt_clear bm ic 0 = bm.
Proof. reflexivity. Qed.

Lemma cnt_clear_step : forall bm ic i, 1 <= i ->
  cnt_clear bm ic i = upd_Znth ((i + ic) mod 128) (cnt_clear bm ic (i - 1)) 0.
Proof.
  intros. unfold cnt_clear.
  replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia.
  simpl cnt_clear_n. f_equal. f_equal. f_equal. lia.
Qed.

Lemma cnt_clear_len : forall bm ic k, Zlength (cnt_clear bm ic k) = Zlength bm.
Proof.
  intros. unfold cnt_clear. induction (Z.to_nat k) as [|k' IH]; simpl; auto.
  unfold upd_Znth; destruct (Sumbool.sumbool_and _ _ _ _ _ _); auto.
  rewrite Zlength_app, Zlength_cons, !Zlength_sublist; try lia; rewrite ?Zlength_cons, ?Zlength_nil; lia.
Qed.

Lemma cnt_clear_words : forall bm ic k,
  Forall (fun w => 0 <= w <= Int64.max_unsigned) bm ->
  Forall (fun w => 0 <= w <= Int64.max_unsigned) (cnt_clear bm ic k).
Proof.
  intros. unfold cnt_clear. induction (Z.to_nat k) as [|k' IH]; simpl; auto.
  unfold upd_Znth. destruct (Sumbool.sumbool_and _ _ _ _ _ _); auto.
  apply Forall_app; split; [apply Forall_sublist; auto|].
  constructor; [rep_lia|]. apply Forall_sublist; auto.
Qed.

(* early rejection *)
Lemma cnt_math_reject : forall top L n,
  (CNT_R + 1 <= top \/ CNT_R <= n \/ n + 1 + CNT_W < top) ->
  cnt_ok top L n = false /\ cnt_top' top L n = top /\ cnt_L' top L n = L.
Proof.
  intros. unfold cnt_top', cnt_L', cnt_ok.
  destruct H as [H|[H|H]].
  - destruct (top <? CNT_R + 1) eqn:E; [lia|]. auto.
  - destruct (top <? CNT_R + 1); destruct (n <? CNT_R) eqn:E; try lia; auto.
  - destruct (top <? CNT_R + 1); destruct (n <? CNT_R); destruct (top <=? n + 1 + CNT_W) eqn:E; try lia; auto.
Qed.
