(* model facts for the body of poly1305_update (aead_poly_update_body3.v): how the streaming
   accumulator p1305_acc over the whole 16-byte blocks evolves when the buffer is completed, when whole
   blocks are fed to poly1305_core_blocks (hibit 1), and when bytes are only buffered. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.aead.aead_model.

Local Open Scope Z_scope.

(* helpers: the 16-byte chunking peels off its first block *)
Ltac pu3_dl := Z.div_mod_to_equations; lia.

Lemma pu3_sublist_end (l: list byte) (lo: Z) :
  0 <= lo -> sublist lo (Zlength l) l = skipn (Z.to_nat lo) l.
Proof.
  intros. unfold sublist. rewrite firstn_all2; [reflexivity |].
  rewrite Zlength_correct, Nat2Z.id. lia.
Qed.

Lemma pu3_chunks_cons (l: list byte) (m: nat) :
  map (fun i => sublist (16 * i) (16 * i + 16) l) (map Z.of_nat (seq 0 (S m))) =
  sublist 0 16 l ::
    map (fun i => sublist (16 * i) (16 * i + 16) (sublist 16 (Zlength l) l)) (map Z.of_nat (seq 0 m)).
Proof.
  cbn [seq map]. f_equal. rewrite <- seq_shift, !map_map.
  apply map_ext. intros i. rewrite pu3_sublist_end by lia. unfold sublist.
  rewrite !skipn_firstn_comm, skipn_skipn. f_equal; [lia | f_equal; lia].
Qed.

Lemma pu3_blocks_cons (l: list byte) :
  0 < Zlength l -> p1305_blocks l = sublist 0 16 l :: p1305_blocks (sublist 16 (Zlength l) l).
Proof.
  intros H. unfold p1305_blocks.
  assert (E: Z.to_nat ((Zlength l + 15) / 16) =
             S (Z.to_nat ((Zlength (sublist 16 (Zlength l) l) + 15) / 16))).
  { destruct (Z_lt_le_dec (Zlength l) 16).
    - rewrite sublist_nil_gen by lia. rewrite Zlength_nil.
      replace ((Zlength l + 15) / 16) with 1 by pu3_dl. reflexivity.
    - rewrite Zlength_sublist by lia.
      replace ((Zlength l + 15) / 16) with (1 + (Zlength l - 16 + 15) / 16) by pu3_dl.
      rewrite Z2Nat.inj_add by pu3_dl. simpl. lia. }
  rewrite E. apply pu3_chunks_cons.
Qed.

Lemma pu3_acc_cons (r acc: Z) (l: list byte) :
  0 < Zlength l ->
  p1305_acc r acc l = p1305_acc r (p1305_step r acc (sublist 0 16 l)) (sublist 16 (Zlength l) l).
Proof.
  intros H. unfold p1305_acc. rewrite pu3_blocks_cons by lia. reflexivity.
Qed.

Lemma pu3_core_cons (r hibit acc: Z) (l: list byte) :
  16 <= Zlength l ->
  p1305_core_blocks r hibit acc l =
    p1305_core_blocks r hibit (p1305_core_step r hibit acc (sublist 0 16 l)) (sublist 16 (Zlength l) l).
Proof.
  intros H. unfold p1305_core_blocks.
  assert (E: Z.to_nat (Zlength l / 16) = S (Z.to_nat (Zlength (sublist 16 (Zlength l) l) / 16))).
  { rewrite Zlength_sublist by lia.
    replace (Zlength l / 16) with (1 + (Zlength l - 16) / 16) by pu3_dl.
    rewrite Z2Nat.inj_add by pu3_dl. simpl. lia. }
  rewrite E, pu3_chunks_cons. reflexivity.
Qed.

Lemma pu3_core_nil (r hibit acc: Z) (l: list byte) :
  Zlength l < 16 -> p1305_core_blocks r hibit acc l = acc.
Proof.
  intros H. unfold p1305_core_blocks.
  replace (Zlength l / 16) with 0 by (pose proof (Zlength_nonneg l); pu3_dl). reflexivity.
Qed.

Lemma pu3_fold_range (r acc: Z) (bs: list (list byte)) :
  0 <= acc < p1305_p -> 0 <= fold_left (p1305_step r) bs acc < p1305_p.
Proof.
  revert acc. induction bs as [|b bs IH]; intros acc H; simpl; auto.
  apply IH. unfold p1305_step. apply Z.mod_pos_bound. unfold p1305_p. lia.
Qed.

(* bulk_len = nbytes & ~(16 - 1) *)
Lemma pu3_round_down (n: Z) :
  0 <= n <= Int.max_unsigned ->
  Int.and (Int.repr n) (Int.not (Int.repr 15)) = Int.repr (n / 16 * 16).
Proof.
  intros Hn. apply Int.same_bits_eq. intros i Hi.
  rewrite Int.bits_and, Int.bits_not by lia. rewrite !Int.testbit_repr by lia.
  replace (n / 16 * 16) with (Z.shiftl (Z.shiftr n 4) 4)
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; reflexivity).
  destruct (Z_lt_le_dec i 4).
  - rewrite Z.shiftl_spec_low by lia.
    assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) as [-> | [-> | [-> | ->]]] by lia;
      simpl; apply andb_false_r.
  - rewrite Z.shiftl_spec_high, Z.shiftr_spec by lia.
    rewrite (Z.bits_above_log2 15 i) by (try lia; change (Z.log2 15) with 3; lia).
    rewrite andb_true_r. f_equal. lia.
Qed.

(* the accumulator over a whole number of blocks, then more *)
Lemma pu3_acc_app (r acc: Z) (a b: list byte) :
  Zlength a mod 16 = 0 -> p1305_acc r acc (a ++ b) = p1305_acc r (p1305_acc r acc a) b.
Proof.
  remember (Z.to_nat (Zlength a)) as k eqn:Ek. revert a acc Ek.
  induction k as [k IH] using lt_wf_ind. intros a acc Ek Hm.
  destruct (Z.eq_dec (Zlength a) 0) as [e | e].
  - apply Zlength_nil_inv in e. subst a. reflexivity.
  - assert (16 <= Zlength a) by (pose proof (Zlength_nonneg a); pu3_dl).
    rewrite (pu3_acc_cons r acc (a ++ b)) by (rewrite Zlength_app; list_solve).
    rewrite (pu3_acc_cons r acc a) by lia.
    rewrite sublist_app1 by lia.
    replace (sublist 16 (Zlength (a ++ b)) (a ++ b)) with (sublist 16 (Zlength a) a ++ b) by list_solve.
    apply (IH (Z.to_nat (Zlength a - 16))); [lia | rewrite Zlength_sublist by lia; lia |
      rewrite Zlength_sublist by lia; pu3_dl].
Qed.

(* whole blocks: the streaming accumulator is the core's with hibit 1 *)
Lemma pu3_acc_core (r acc: Z) (x: list byte) :
  Zlength x mod 16 = 0 -> p1305_acc r acc x = p1305_core_blocks r 1 acc x.
Proof.
  remember (Z.to_nat (Zlength x)) as k eqn:Ek. revert x acc Ek.
  induction k as [k IH] using lt_wf_ind. intros x acc Ek Hm.
  destruct (Z.eq_dec (Zlength x) 0) as [e | e].
  - apply Zlength_nil_inv in e. subst x. reflexivity.
  - assert (16 <= Zlength x) by (pose proof (Zlength_nonneg x); pu3_dl).
    unfold p1305_acc. rewrite pu3_blocks_cons by lia. rewrite pu3_core_cons by lia. simpl.
    replace (p1305_step r acc (sublist 0 16 x)) with (p1305_core_step r 1 acc (sublist 0 16 x)).
    + apply (IH (Z.to_nat (Zlength x - 16))); [lia | rewrite Zlength_sublist by lia; lia |
        rewrite Zlength_sublist by lia; pu3_dl].
    + unfold p1305_step, p1305_core_step. rewrite Zlength_sublist by lia. reflexivity.
Qed.

(* the core only depends on its start value mod p (up to mod p) *)
Lemma pu3_core_mod (r hibit a: Z) (x: list byte) :
  p1305_core_blocks r hibit a x mod p1305_p = p1305_core_blocks r hibit (a mod p1305_p) x mod p1305_p.
Proof.
  destruct (Z_lt_le_dec (Zlength x) 16).
  - rewrite !pu3_core_nil by lia. rewrite Zmod_mod. reflexivity.
  - rewrite !(pu3_core_cons r hibit _ x) by lia. f_equal. f_equal.
    unfold p1305_core_step. rewrite <- !Z.add_assoc.
    rewrite Zmult_mod, (Zmult_mod (a mod p1305_p + _)), Z.add_mod_idemp_l by (unfold p1305_p; lia).
    reflexivity.
Qed.

(* the accumulator stays reduced *)
Lemma pu3_acc_range (r acc: Z) (x: list byte) :
  0 <= acc < p1305_p -> 0 <= p1305_acc r acc x < p1305_p.
Proof.
  intros H. unfold p1305_acc. apply pu3_fold_range; auto.
Qed.

(* completing the buffer: the rest of msg (1..15 bytes) and the first 16 - |rest| bytes of data are one block *)
Lemma pu3_fill (r: Z) (msg data: list byte) (hv hv': Z) :
  Zlength msg mod 16 <> 0 -> 16 - Zlength msg mod 16 <= Zlength data ->
  hv mod p1305_p = p1305_acc r 0 (sublist 0 (Zlength msg / 16 * 16) msg) ->
  hv' mod p1305_p =
    p1305_core_blocks r 1 hv
      (sublist (Zlength msg / 16 * 16) (Zlength msg) msg ++ sublist 0 (16 - Zlength msg mod 16) data)
    mod p1305_p ->
  Zlength (msg ++ sublist 0 (16 - Zlength msg mod 16) data) mod 16 = 0 /\
  hv' mod p1305_p = p1305_acc r 0 (msg ++ sublist 0 (16 - Zlength msg mod 16) data).
Proof.
  intros Hm Hd Hhv Hhv'.
  set (q := Zlength msg / 16 * 16) in *.
  set (k := 16 - Zlength msg mod 16) in *.
  assert (Hq: 0 <= q <= Zlength msg) by (subst q; pose proof (Zlength_nonneg msg); pu3_dl).
  assert (Hk: 0 < k <= 16) by (subst k; pose proof (Zlength_nonneg msg); pu3_dl).
  assert (Hqk: Zlength msg + k = q + 16) by (subst q k; pu3_dl).
  split.
  - rewrite Zlength_app, Zlength_sublist by lia. rewrite Z.sub_0_r, Hqk. subst q; pu3_dl.
  - replace (msg ++ sublist 0 k data) with
      (sublist 0 q msg ++ (sublist q (Zlength msg) msg ++ sublist 0 k data))
      by (rewrite app_assoc, <- sublist_split, sublist_same by lia; reflexivity).
    rewrite pu3_acc_app by (rewrite Zlength_sublist by lia; subst q; pu3_dl).
    assert (HL: Zlength (sublist q (Zlength msg) msg ++ sublist 0 k data) = 16)
      by (rewrite Zlength_app, !Zlength_sublist by lia; lia).
    rewrite pu3_acc_core by (rewrite HL; reflexivity).
    rewrite Hhv', pu3_core_mod, Hhv, <- pu3_acc_core by (rewrite HL; reflexivity).
    apply Z.mod_small. apply pu3_acc_range, pu3_acc_range. unfold p1305_p; lia.
Qed.

(* feeding whole blocks to the core (hibit 1) after a whole number of blocks *)
Lemma pu3_bulk (r: Z) (msg x: list byte) (hv hv': Z) :
  Zlength msg mod 16 = 0 -> Zlength x mod 16 = 0 ->
  hv mod p1305_p = p1305_acc r 0 msg ->
  hv' mod p1305_p = p1305_core_blocks r 1 hv x mod p1305_p ->
  hv' mod p1305_p = p1305_acc r 0 (msg ++ x).
Proof.
  intros Hm Hx Hhv Hhv'.
  rewrite pu3_acc_app by auto. rewrite pu3_acc_core by auto.
  rewrite Hhv', pu3_core_mod, Hhv, <- pu3_acc_core by auto.
  apply Z.mod_small. apply pu3_acc_range, pu3_acc_range. unfold p1305_p; lia.
Qed.

(* a message of a whole number of blocks: everything is whole, nothing rests *)
Lemma pu3_whole (msg: list byte) :
  Zlength msg mod 16 = 0 ->
  Zlength msg / 16 * 16 = Zlength msg /\ sublist 0 (Zlength msg / 16 * 16) msg = msg /\
  sublist (Zlength msg / 16 * 16) (Zlength msg) msg = [].
Proof.
  intros H. assert (E: Zlength msg / 16 * 16 = Zlength msg) by pu3_dl.
  rewrite E. split; [reflexivity | split].
  - apply sublist_same; auto.
  - apply sublist_nil.
Qed.

(* buffering only: the whole blocks do not change, the rest grows *)
Lemma pu3_tail (msg x: list byte) :
  Zlength msg mod 16 + Zlength x < 16 ->
  Zlength (msg ++ x) / 16 * 16 = Zlength msg / 16 * 16 /\
  sublist 0 (Zlength (msg ++ x) / 16 * 16) (msg ++ x) = sublist 0 (Zlength msg / 16 * 16) msg /\
  sublist (Zlength (msg ++ x) / 16 * 16) (Zlength (msg ++ x)) (msg ++ x) =
    sublist (Zlength msg / 16 * 16) (Zlength msg) msg ++ x.
Proof.
  intros H. pose proof (Zlength_nonneg msg). pose proof (Zlength_nonneg x).
  assert (E: Zlength (msg ++ x) / 16 * 16 = Zlength msg / 16 * 16) by (rewrite Zlength_app; pu3_dl).
  rewrite E. split; [reflexivity | split].
  - apply sublist_app1; pu3_dl.
  - rewrite Zlength_app. rewrite sublist_app' by pu3_dl.
    replace (Zlength msg + Zlength x - Zlength msg) with (Zlength x) by lia.
    rewrite (sublist_same 0 (Zlength x) x) by lia. reflexivity.
Qed.

(* all of the above (the checker's target: every lemma proven) *)
Theorem pu3_model_ok :
  (forall n, 0 <= n <= Int.max_unsigned ->
     Int.and (Int.repr n) (Int.not (Int.repr 15)) = Int.repr (n / 16 * 16)) /\
  (forall r acc a b, Zlength a mod 16 = 0 -> p1305_acc r acc (a ++ b) = p1305_acc r (p1305_acc r acc a) b) /\
  (forall r acc x, Zlength x mod 16 = 0 -> p1305_acc r acc x = p1305_core_blocks r 1 acc x) /\
  (forall r hibit a x,
     p1305_core_blocks r hibit a x mod p1305_p = p1305_core_blocks r hibit (a mod p1305_p) x mod p1305_p) /\
  (forall r acc x, 0 <= acc < p1305_p -> 0 <= p1305_acc r acc x < p1305_p) /\
  (forall r msg data hv hv',
     Zlength msg mod 16 <> 0 -> 16 - Zlength msg mod 16 <= Zlength data ->
     hv mod p1305_p = p1305_acc r 0 (sublist 0 (Zlength msg / 16 * 16) msg) ->
     hv' mod p1305_p =
       p1305_core_blocks r 1 hv
         (sublist (Zlength msg / 16 * 16) (Zlength msg) msg ++ sublist 0 (16 - Zlength msg mod 16) data)
       mod p1305_p ->
     Zlength (msg ++ sublist 0 (16 - Zlength msg mod 16) data) mod 16 = 0 /\
     hv' mod p1305_p = p1305_acc r 0 (msg ++ sublist 0 (16 - Zlength msg mod 16) data)) /\
  (forall r msg x hv hv',
     Zlength msg mod 16 = 0 -> Zlength x mod 16 = 0 ->
     hv mod p1305_p = p1305_acc r 0 msg ->
     hv' mod p1305_p = p1305_core_blocks r 1 hv x mod p1305_p ->
     hv' mod p1305_p = p1305_acc r 0 (msg ++ x)) /\
  (forall msg: list byte, Zlength msg mod 16 = 0 ->
     Zlength msg / 16 * 16 = Zlength msg /\ sublist 0 (Zlength msg / 16 * 16) msg = msg /\
     sublist (Zlength msg / 16 * 16) (Zlength msg) msg = []) /\
  (forall msg x: list byte, Zlength msg mod 16 + Zlength x < 16 ->
     Zlength (msg ++ x) / 16 * 16 = Zlength msg / 16 * 16 /\
     sublist 0 (Zlength (msg ++ x) / 16 * 16) (msg ++ x) = sublist 0 (Zlength msg / 16 * 16) msg /\
     sublist (Zlength (msg ++ x) / 16 * 16) (Zlength (msg ++ x)) (msg ++ x) =
       sublist (Zlength msg / 16 * 16) (Zlength msg) msg ++ x).
Proof.
  split; [exact pu3_round_down |]. split; [exact pu3_acc_app |]. split; [exact pu3_acc_core |].
  split; [exact pu3_core_mod |]. split; [exact pu3_acc_range |]. split; [exact pu3_fill |].
  split; [exact pu3_bulk |]. split; [exact pu3_whole | exact pu3_tail].
Qed.
