(* law handshake_clear: the cut of main's body into phases.
   main's body = S; return 0 (implicit) with S = 27 statements (the last one the explicit `return 0`):
     P1 =  0..3   peers = NULL, the boot clock, raw, setup_device(&w, &it, &pt, raw)
     P2 =  4..5   n = draw_steps(); the loop adding n peers (hnodes_add)
     P3 =  6      if (peers == NULL) return 0
     P4 =  7      the loop over the nodes: hs_randomize, peer_randomize_rest, maybe wg_index_hashtable_insert
     PK =  8      kes = kents_add(&it, peers, NULL, 1)
     P5 =  9..15  target = hnodes_pick(peers), hnodes_snap, kents_snap, dev_take, shim_take,
                  h = &target->p->handshake, wg_noise_handshake_clear(h)
     P6 = 16..18  the CHECKs on P: hs_zeroed_from && !hashed && index; the list link; refcount && pr_same
     P7 = 19..20  hashed = 0; the loop over the other nodes (hs_same_but_next, refs, pr_same, table_has)
     P8 = 21..26  CHECK(kents_same_but_next), CHECK(table_len), CHECK(dev_same && shim_same), kents_free,
                  hnodes_free, return 0 *)
Require Import VST.floyd.proofauto.
Require WgNoise.harness.x_handshake_clear.code.

Module HCL5 := WgNoise.harness.x_handshake_clear.code.

Fixpoint hcl5_seqs (l: list statement) (rest: statement) : statement :=
  match l with [] => rest | a :: l' => Ssequence a (hcl5_seqs l' rest) end.

Fixpoint hcl5_seql (l: list statement) : statement :=
  match l with [] => Sskip | [a] => a | a :: l' => Ssequence a (hcl5_seql l') end.

Fixpoint hcl5_flat (s: statement) : list statement :=
  match s with Ssequence a b => a :: hcl5_flat b | _ => [s] end.

Lemma hcl5_unfold_seql l : l <> [] ->
  unfold_Ssequence (hcl5_seql l) = concat (map unfold_Ssequence l).
Proof.
  induction l as [|a l IH]; intros Hl; [congruence |].
  destruct l as [|b l']; simpl.
  - rewrite app_nil_r; reflexivity.
  - simpl in IH. rewrite IH by discriminate. reflexivity.
Qed.

Lemma hcl5_unfold_seqs l rest :
  unfold_Ssequence (hcl5_seqs l rest) = concat (map unfold_Ssequence l) ++ unfold_Ssequence rest.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity |]. rewrite IH, app_assoc. reflexivity.
Qed.

Lemma hcl5_overridePost2 Q Q' R : overridePost Q (overridePost Q' R) = overridePost Q R.
Proof. destruct R; reflexivity. Qed.

Lemma hcl5_semax_cut {Espec: OracleKind} {cs: compspecs} Delta P Q R l rest :
  l <> [] ->
  semax Delta P (hcl5_seql l) (overridePost Q R) -> semax Delta Q rest R ->
  semax Delta P (hcl5_seqs l rest) R.
Proof.
  intros Hl H1 H2.
  apply (semax_unfold_Ssequence (Ssequence (hcl5_seql l) rest)).
  - simpl. rewrite hcl5_unfold_seql, hcl5_unfold_seqs by auto. reflexivity.
  - eapply semax_seq; eauto.
Qed.

(* a list cut into two consecutive non-empty pieces (for children that cut their phase further) *)
Lemma hcl5_seql_app {Espec: OracleKind} {cs: compspecs} Delta P Q R l1 l2 :
  l1 <> [] -> l2 <> [] ->
  semax Delta P (hcl5_seql l1) (overridePost Q R) -> semax Delta Q (hcl5_seql l2) R ->
  semax Delta P (hcl5_seql (l1 ++ l2)) R.
Proof.
  intros H1 H2 S1 S2.
  assert (H12: l1 ++ l2 <> []) by (destruct l1; [congruence | discriminate]).
  apply (semax_unfold_Ssequence (Ssequence (hcl5_seql l1) (hcl5_seql l2))).
  - simpl. rewrite (hcl5_unfold_seql _ H12), (hcl5_unfold_seql _ H1), (hcl5_unfold_seql _ H2), map_app, concat_app.
    reflexivity.
  - eapply semax_seq; eauto.
Qed.

(* main's statements *)
Definition hcl5_stmts : list statement :=
  ltac:(let x := eval cbv beta iota delta [hcl5_flat HCL5.f_main fn_body] in
        (match fn_body HCL5.f_main with Ssequence s _ => hcl5_flat s | s => [s] end) in exact x).

Lemma hcl5_stmts_length : length hcl5_stmts = 27%nat.
Proof. reflexivity. Qed.

Definition hcl5_l (i n: nat) : list statement := firstn n (skipn i hcl5_stmts).

Definition hcl5_P1 := ltac:(let x := eval cbv beta iota delta [hcl5_l hcl5_seql firstn skipn hcl5_stmts] in (hcl5_seql (hcl5_l 0 4)) in exact x).
Definition hcl5_P2 := ltac:(let x := eval cbv beta iota delta [hcl5_l hcl5_seql firstn skipn hcl5_stmts] in (hcl5_seql (hcl5_l 4 2)) in exact x).
Definition hcl5_P3 := ltac:(let x := eval cbv beta iota delta [hcl5_l hcl5_seql firstn skipn hcl5_stmts] in (hcl5_seql (hcl5_l 6 1)) in exact x).
Definition hcl5_P4 := ltac:(let x := eval cbv beta iota delta [hcl5_l hcl5_seql firstn skipn hcl5_stmts] in (hcl5_seql (hcl5_l 7 1)) in exact x).
Definition hcl5_PK := ltac:(let x := eval cbv beta iota delta [hcl5_l hcl5_seql firstn skipn hcl5_stmts] in (hcl5_seql (hcl5_l 8 1)) in exact x).
Definition hcl5_P5 := ltac:(let x := eval cbv beta iota delta [hcl5_l hcl5_seql firstn skipn hcl5_stmts] in (hcl5_seql (hcl5_l 9 7)) in exact x).
Definition hcl5_P6 := ltac:(let x := eval cbv beta iota delta [hcl5_l hcl5_seql firstn skipn hcl5_stmts] in (hcl5_seql (hcl5_l 16 3)) in exact x).
Definition hcl5_P7 := ltac:(let x := eval cbv beta iota delta [hcl5_l hcl5_seql firstn skipn hcl5_stmts] in (hcl5_seql (hcl5_l 19 2)) in exact x).
Definition hcl5_P8 := ltac:(let x := eval cbv beta iota delta [hcl5_l hcl5_seql firstn skipn hcl5_stmts] in (hcl5_seql (hcl5_l 21 6)) in exact x).

Lemma hcl5_body_eq :
  fn_body HCL5.f_main =
  Ssequence
    (hcl5_seqs (hcl5_l 0 4) (hcl5_seqs (hcl5_l 4 2) (hcl5_seqs (hcl5_l 6 1) (hcl5_seqs (hcl5_l 7 1)
      (hcl5_seqs (hcl5_l 8 1) (hcl5_seqs (hcl5_l 9 7) (hcl5_seqs (hcl5_l 16 3) (hcl5_seqs (hcl5_l 19 2)
        (hcl5_seql (hcl5_l 21 6))))))))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.

Lemma hcl5_phases_eq :
  hcl5_P1 = hcl5_seql (hcl5_l 0 4) /\ hcl5_P2 = hcl5_seql (hcl5_l 4 2) /\
  hcl5_P3 = hcl5_seql (hcl5_l 6 1) /\ hcl5_P4 = hcl5_seql (hcl5_l 7 1) /\
  hcl5_PK = hcl5_seql (hcl5_l 8 1) /\ hcl5_P5 = hcl5_seql (hcl5_l 9 7) /\
  hcl5_P6 = hcl5_seql (hcl5_l 16 3) /\ hcl5_P7 = hcl5_seql (hcl5_l 19 2) /\
  hcl5_P8 = hcl5_seql (hcl5_l 21 6).
Proof. repeat split. Qed.
