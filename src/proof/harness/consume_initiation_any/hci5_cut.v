(* law consume_initiation_any: the cut of main's body
   into phases.
   main's body = S; return 0 (implicit) with S = 39 statements (the last one the explicit `return 0`):
     P1  =  0..8   peers = NULL, boot clock, wg_noise_init, raw keys, setup_device, the identities, A's node
     P2  =  9..10  n = draw_steps(); the loop adding n peers (hnodes_add)
     P3  = 11      the loop over the nodes: hs_randomize, peer_randomize_rest, maybe wg_index_hashtable_insert
     PK  = 12      kes = kents_add(&itb, peers, NULL, 1)
     P4  = 13..14  msg = malloc; NULL: kents_free, hnodes_free, return 0
     P5  = 15..19  fill_init, mode, A's initiation (optionally changed), the replay boundary (18), init_img(img)
     P6  = 20..28  now = draw_boottime(), the flood boundary (21), wg_shim_boottime_ns = now, hnodes_snap,
                   kents_snap, dev_take, head0 = itb.head, shim_take, ret = wg_noise_handshake_consume_initiation
     P7  = 29..30  target = NULL; the harness's model
     P8  = 31..38  init_img(img_after), CHECK(image), CHECK(dev_same && head0 && kents_same && shim_same),
                   if (target == NULL) ... else ..., free(msg), kents_free, hnodes_free, return 0 *)
Require Import VST.floyd.proofauto.
Require WgNoise.harness.x_consume_initiation_any.code.

Module HC5 := WgNoise.harness.x_consume_initiation_any.code.

Fixpoint hci5_seqs (l: list statement) (rest: statement) : statement :=
  match l with [] => rest | a :: l' => Ssequence a (hci5_seqs l' rest) end.

Fixpoint hci5_seql (l: list statement) : statement :=
  match l with [] => Sskip | [a] => a | a :: l' => Ssequence a (hci5_seql l') end.

Fixpoint hci5_flat (s: statement) : list statement :=
  match s with Ssequence a b => a :: hci5_flat b | _ => [s] end.

Lemma hci5_unfold_seql l : l <> [] ->
  unfold_Ssequence (hci5_seql l) = concat (map unfold_Ssequence l).
Proof.
  induction l as [|a l IH]; intros Hl; [congruence |].
  destruct l as [|b l']; simpl.
  - rewrite app_nil_r; reflexivity.
  - simpl in IH. rewrite IH by discriminate. reflexivity.
Qed.

Lemma hci5_unfold_seqs l rest :
  unfold_Ssequence (hci5_seqs l rest) = concat (map unfold_Ssequence l) ++ unfold_Ssequence rest.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity |]. rewrite IH, app_assoc. reflexivity.
Qed.

Lemma hci5_overridePost2 Q Q' R : overridePost Q (overridePost Q' R) = overridePost Q R.
Proof. destruct R; reflexivity. Qed.

Lemma hci5_semax_cut {Espec: OracleKind} {cs: compspecs} Delta P Q R l rest :
  l <> [] ->
  semax Delta P (hci5_seql l) (overridePost Q R) -> semax Delta Q rest R ->
  semax Delta P (hci5_seqs l rest) R.
Proof.
  intros Hl H1 H2.
  apply (semax_unfold_Ssequence (Ssequence (hci5_seql l) rest)).
  - simpl. rewrite hci5_unfold_seql, hci5_unfold_seqs by auto. reflexivity.
  - eapply semax_seq; eauto.
Qed.

(* a list cut into two consecutive non-empty pieces *)
Lemma hci5_seql_app {Espec: OracleKind} {cs: compspecs} Delta P Q R l1 l2 :
  l1 <> [] -> l2 <> [] ->
  semax Delta P (hci5_seql l1) (overridePost Q R) -> semax Delta Q (hci5_seql l2) R ->
  semax Delta P (hci5_seql (l1 ++ l2)) R.
Proof.
  intros H1 H2 S1 S2.
  assert (H12: l1 ++ l2 <> []) by (destruct l1; [congruence | discriminate]).
  apply (semax_unfold_Ssequence (Ssequence (hci5_seql l1) (hci5_seql l2))).
  - simpl. rewrite (hci5_unfold_seql _ H12), (hci5_unfold_seql _ H1), (hci5_unfold_seql _ H2), map_app, concat_app.
    reflexivity.
  - eapply semax_seq; eauto.
Qed.

(* main's statements *)
Definition hci5_stmts : list statement :=
  ltac:(let x := eval cbv beta iota delta [hci5_flat HC5.f_main fn_body] in
        (match fn_body HC5.f_main with Ssequence s _ => hci5_flat s | s => [s] end) in exact x).

Lemma hci5_stmts_length : length hci5_stmts = 39%nat.
Proof. reflexivity. Qed.

Definition hci5_l (i n: nat) : list statement := firstn n (skipn i hci5_stmts).

Definition hci5_P1 := ltac:(let x := eval cbv beta iota delta [hci5_l hci5_seql firstn skipn hci5_stmts] in (hci5_seql (hci5_l 0 9)) in exact x).
Definition hci5_P2 := ltac:(let x := eval cbv beta iota delta [hci5_l hci5_seql firstn skipn hci5_stmts] in (hci5_seql (hci5_l 9 2)) in exact x).
Definition hci5_P3 := ltac:(let x := eval cbv beta iota delta [hci5_l hci5_seql firstn skipn hci5_stmts] in (hci5_seql (hci5_l 11 1)) in exact x).
Definition hci5_PK := ltac:(let x := eval cbv beta iota delta [hci5_l hci5_seql firstn skipn hci5_stmts] in (hci5_seql (hci5_l 12 1)) in exact x).
Definition hci5_P4 := ltac:(let x := eval cbv beta iota delta [hci5_l hci5_seql firstn skipn hci5_stmts] in (hci5_seql (hci5_l 13 2)) in exact x).
Definition hci5_P5 := ltac:(let x := eval cbv beta iota delta [hci5_l hci5_seql firstn skipn hci5_stmts] in (hci5_seql (hci5_l 15 5)) in exact x).
Definition hci5_P6 := ltac:(let x := eval cbv beta iota delta [hci5_l hci5_seql firstn skipn hci5_stmts] in (hci5_seql (hci5_l 20 9)) in exact x).
Definition hci5_P7 := ltac:(let x := eval cbv beta iota delta [hci5_l hci5_seql firstn skipn hci5_stmts] in (hci5_seql (hci5_l 29 2)) in exact x).
Definition hci5_P8 := ltac:(let x := eval cbv beta iota delta [hci5_l hci5_seql firstn skipn hci5_stmts] in (hci5_seql (hci5_l 31 8)) in exact x).

Lemma hci5_body_eq :
  fn_body HC5.f_main =
  Ssequence
    (hci5_seqs (hci5_l 0 9) (hci5_seqs (hci5_l 9 2) (hci5_seqs (hci5_l 11 1) (hci5_seqs (hci5_l 12 1)
      (hci5_seqs (hci5_l 13 2) (hci5_seqs (hci5_l 15 5) (hci5_seqs (hci5_l 20 9) (hci5_seqs (hci5_l 29 2)
        (hci5_seql (hci5_l 31 8))))))))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.

Lemma hci5_phases_eq :
  hci5_P1 = hci5_seql (hci5_l 0 9) /\ hci5_P2 = hci5_seql (hci5_l 9 2) /\
  hci5_P3 = hci5_seql (hci5_l 11 1) /\ hci5_PK = hci5_seql (hci5_l 12 1) /\
  hci5_P4 = hci5_seql (hci5_l 13 2) /\ hci5_P5 = hci5_seql (hci5_l 15 5) /\
  hci5_P6 = hci5_seql (hci5_l 20 9) /\ hci5_P7 = hci5_seql (hci5_l 29 2) /\
  hci5_P8 = hci5_seql (hci5_l 31 8).
Proof. repeat split. Qed.
