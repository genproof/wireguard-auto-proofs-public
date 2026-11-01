(* law keypairs: the cut of main's body into segments.
   main's body = S; return 0 (implicit) with S = 41 statements (the last one the explicit `return 0`):
     A1 = 0..14   locals next_id / id_known, the harness's globals, m_warn, now, wg_noise_init, raw, pub,
                  setup_device, setup_peer, peer_randomize_rest(&p)
     A2 = 15..17  n = draw_steps(); the loop adding the other peers (hnodes_add); the loop randomizing them
                  (hs_randomize, peer_randomize_rest, maybe wg_index_hashtable_insert)
     A3 = 18..20  kes = kents_add(&t, others, NULL, 1); hnodes_snap(others); kents_snap(kes)
     A4 = 21..28  hs_take(&hsm), pr_take(&prm), prefs, dev_take(&dsm), allocs0, frees0, the warn0 loop, steps
     LOOP = 29    for (i = 0; i < steps; i++) BODY
     F  = 30..40  the end: clear, the three m_puts, the loop over live (held puts), CHECK(check_all), the nlive
                  loop, the allocation CHECK, the warning CHECK, kents_free, hnodes_free, return 0
   BODY = L0 (2 statements: op = nondet_u8() % 8; the clock moves) ; IFC (the if-chain on op) ; LC (2: the CHECKs
   check_all and frees).  IFC = if op==0 Op0 else if op==1 Op1 else if op==2 Op2 else if op==3 Op3 else if op==7 Op7
   else { t' = (op == 4 || op == 5); if (t') Op45 else Op6 }. *)
Require Import VST.floyd.proofauto.
Require WgNoise.harness.x_keypairs.code.

Module KC := WgNoise.harness.x_keypairs.code.

(* ---------------------------------------------------------------------- *)
(* Cutting a statement list (as law replay's hrp3 lemmas)                   *)
(* ---------------------------------------------------------------------- *)

Fixpoint hkp5_seqs (l: list statement) (rest: statement) : statement :=
  match l with [] => rest | a :: l' => Ssequence a (hkp5_seqs l' rest) end.

Fixpoint hkp5_seql (l: list statement) : statement :=
  match l with [] => Sskip | [a] => a | a :: l' => Ssequence a (hkp5_seql l') end.

Fixpoint hkp5_flat (s: statement) : list statement :=
  match s with Ssequence a b => a :: hkp5_flat b | _ => [s] end.

Lemma hkp5_unfold_seql l : l <> [] ->
  unfold_Ssequence (hkp5_seql l) = concat (map unfold_Ssequence l).
Proof.
  induction l as [|a l IH]; intros Hl; [congruence |].
  destruct l as [|b l']; simpl.
  - rewrite app_nil_r; reflexivity.
  - simpl in IH. rewrite IH by discriminate. reflexivity.
Qed.

Lemma hkp5_unfold_seqs l rest :
  unfold_Ssequence (hkp5_seqs l rest) = concat (map unfold_Ssequence l) ++ unfold_Ssequence rest.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity |]. rewrite IH, app_assoc. reflexivity.
Qed.

Lemma hkp5_overridePost2 Q Q' R : overridePost Q (overridePost Q' R) = overridePost Q R.
Proof. destruct R; reflexivity. Qed.

Lemma hkp5_semax_cut {Espec: OracleKind} {cs: compspecs} Delta P Q R l rest :
  l <> [] ->
  semax Delta P (hkp5_seql l) (overridePost Q R) -> semax Delta Q rest R ->
  semax Delta P (hkp5_seqs l rest) R.
Proof.
  intros Hl H1 H2.
  apply (semax_unfold_Ssequence (Ssequence (hkp5_seql l) rest)).
  - simpl. rewrite hkp5_unfold_seql, hkp5_unfold_seqs by auto. reflexivity.
  - eapply semax_seq; eauto.
Qed.

(* a list cut into two consecutive non-empty pieces *)
Lemma hkp5_seql_app {Espec: OracleKind} {cs: compspecs} Delta P Q R l1 l2 :
  l1 <> [] -> l2 <> [] ->
  semax Delta P (hkp5_seql l1) (overridePost Q R) -> semax Delta Q (hkp5_seql l2) R ->
  semax Delta P (hkp5_seql (l1 ++ l2)) R.
Proof.
  intros H1 H2 S1 S2.
  assert (H12: l1 ++ l2 <> []) by (destruct l1; [congruence | discriminate]).
  apply (semax_unfold_Ssequence (Ssequence (hkp5_seql l1) (hkp5_seql l2))).
  - simpl. rewrite (hkp5_unfold_seql _ H12), (hkp5_unfold_seql _ H1), (hkp5_unfold_seql _ H2), map_app, concat_app.
    reflexivity.
  - eapply semax_seq; eauto.
Qed.

(* ---------------------------------------------------------------------- *)
(* main                                                                     *)
(* ---------------------------------------------------------------------- *)

Definition hkp5_stmts : list statement :=
  ltac:(let x := eval cbv beta iota delta [hkp5_flat KC.f_main fn_body] in
        (match fn_body KC.f_main with Ssequence s _ => hkp5_flat s | s => [s] end) in exact x).

Lemma hkp5_stmts_length : length hkp5_stmts = 41%nat.
Proof. reflexivity. Qed.

Definition hkp5_l (i n: nat) : list statement := firstn n (skipn i hkp5_stmts).

Definition hkp5_segA1 := ltac:(let x := eval cbv beta iota delta [hkp5_l hkp5_seql firstn skipn hkp5_stmts] in (hkp5_seql (hkp5_l 0 15)) in exact x).
Definition hkp5_segA2 := ltac:(let x := eval cbv beta iota delta [hkp5_l hkp5_seql firstn skipn hkp5_stmts] in (hkp5_seql (hkp5_l 15 3)) in exact x).
Definition hkp5_segA3 := ltac:(let x := eval cbv beta iota delta [hkp5_l hkp5_seql firstn skipn hkp5_stmts] in (hkp5_seql (hkp5_l 18 3)) in exact x).
Definition hkp5_segA4 := ltac:(let x := eval cbv beta iota delta [hkp5_l hkp5_seql firstn skipn hkp5_stmts] in (hkp5_seql (hkp5_l 21 8)) in exact x).
Definition hkp5_loop := ltac:(let x := eval cbv beta iota delta [nth hkp5_stmts] in (nth 29 hkp5_stmts Sskip) in exact x).
Definition hkp5_segF := ltac:(let x := eval cbv beta iota delta [hkp5_l hkp5_seql firstn skipn hkp5_stmts] in (hkp5_seql (hkp5_l 30 11)) in exact x).

Lemma hkp5_body_eq :
  fn_body KC.f_main =
  Ssequence
    (hkp5_seqs (hkp5_l 0 15) (hkp5_seqs (hkp5_l 15 3) (hkp5_seqs (hkp5_l 18 3) (hkp5_seqs (hkp5_l 21 8)
      (hkp5_seqs (hkp5_l 29 1) (hkp5_seql (hkp5_l 30 11)))))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.

Lemma hkp5_segs_eq :
  hkp5_segA1 = hkp5_seql (hkp5_l 0 15) /\ hkp5_segA2 = hkp5_seql (hkp5_l 15 3) /\
  hkp5_segA3 = hkp5_seql (hkp5_l 18 3) /\ hkp5_segA4 = hkp5_seql (hkp5_l 21 8) /\
  hkp5_loop = hkp5_seql (hkp5_l 29 1) /\ hkp5_segF = hkp5_seql (hkp5_l 30 11).
Proof. repeat split. Qed.

(* the loop: i = 0; Sloop (if (i < steps) skip else break; BODY) (i++) *)
Definition hkp5_body : statement :=
  ltac:(let x := eval cbv beta iota delta [hkp5_loop] in
        (match hkp5_loop with Ssequence _ (Sloop (Ssequence _ b) _) => b | _ => Sskip end) in exact x).
Definition hkp5_bstmts : list statement :=
  ltac:(let x := eval cbv beta iota delta [hkp5_flat hkp5_body] in (hkp5_flat hkp5_body) in exact x).

Lemma hkp5_bstmts_length : length hkp5_bstmts = 5%nat.
Proof. reflexivity. Qed.

Definition hkp5_bl (i n: nat) : list statement := firstn n (skipn i hkp5_bstmts).

Definition hkp5_segL0 := ltac:(let x := eval cbv beta iota delta [hkp5_bl hkp5_seql firstn skipn hkp5_bstmts] in (hkp5_seql (hkp5_bl 0 2)) in exact x).
Definition hkp5_ifc := ltac:(let x := eval cbv beta iota delta [nth hkp5_bstmts] in (nth 2 hkp5_bstmts Sskip) in exact x).
Definition hkp5_segLC := ltac:(let x := eval cbv beta iota delta [hkp5_bl hkp5_seql firstn skipn hkp5_bstmts] in (hkp5_seql (hkp5_bl 3 2)) in exact x).

Lemma hkp5_loop_shape :
  hkp5_loop =
  Ssequence (Sset KC._i (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Sloop
       (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar KC._i tulong) (Etempvar KC._steps tulong) tint) Sskip Sbreak)
          (hkp5_seqs (hkp5_bl 0 2) (hkp5_seqs (hkp5_bl 2 1) (hkp5_seql (hkp5_bl 3 2)))))
       (Sset KC._i (Ebinop Oadd (Etempvar KC._i tulong) (Econst_int (Int.repr 1) tint) tulong))).
Proof. reflexivity. Qed.

Lemma hkp5_bsegs_eq :
  hkp5_segL0 = hkp5_seql (hkp5_bl 0 2) /\ hkp5_ifc = hkp5_seql (hkp5_bl 2 1) /\
  hkp5_segLC = hkp5_seql (hkp5_bl 3 2).
Proof. repeat split. Qed.

(* the branches of the if-chain on op *)
Definition hkp5_sOp0 := ltac:(let x := eval cbv beta iota delta [hkp5_ifc] in
  (match hkp5_ifc with Sifthenelse _ s _ => s | _ => Sskip end) in exact x).
Definition hkp5_sOp1 := ltac:(let x := eval cbv beta iota delta [hkp5_ifc] in
  (match hkp5_ifc with Sifthenelse _ _ (Sifthenelse _ s _) => s | _ => Sskip end) in exact x).
Definition hkp5_sOp2 := ltac:(let x := eval cbv beta iota delta [hkp5_ifc] in
  (match hkp5_ifc with Sifthenelse _ _ (Sifthenelse _ _ (Sifthenelse _ s _)) => s | _ => Sskip end) in exact x).
Definition hkp5_sOp3 := ltac:(let x := eval cbv beta iota delta [hkp5_ifc] in
  (match hkp5_ifc with Sifthenelse _ _ (Sifthenelse _ _ (Sifthenelse _ _ (Sifthenelse _ s _))) => s | _ => Sskip end)
  in exact x).
Definition hkp5_sOp7 := ltac:(let x := eval cbv beta iota delta [hkp5_ifc] in
  (match hkp5_ifc with Sifthenelse _ _ (Sifthenelse _ _ (Sifthenelse _ _ (Sifthenelse _ _ (Sifthenelse _ s _)))) => s
   | _ => Sskip end) in exact x).
Definition hkp5_s45 := ltac:(let x := eval cbv beta iota delta [hkp5_ifc] in
  (match hkp5_ifc with
   | Sifthenelse _ _ (Sifthenelse _ _ (Sifthenelse _ _ (Sifthenelse _ _ (Sifthenelse _ _ (Ssequence s _))))) => s
   | _ => Sskip end) in exact x).
Definition hkp5_sOp45 := ltac:(let x := eval cbv beta iota delta [hkp5_ifc] in
  (match hkp5_ifc with
   | Sifthenelse _ _ (Sifthenelse _ _ (Sifthenelse _ _ (Sifthenelse _ _ (Sifthenelse _ _
       (Ssequence _ (Sifthenelse _ s _)))))) => s
   | _ => Sskip end) in exact x).
Definition hkp5_sOp6 := ltac:(let x := eval cbv beta iota delta [hkp5_ifc] in
  (match hkp5_ifc with
   | Sifthenelse _ _ (Sifthenelse _ _ (Sifthenelse _ _ (Sifthenelse _ _ (Sifthenelse _ _
       (Ssequence _ (Sifthenelse _ _ s)))))) => s
   | _ => Sskip end) in exact x).

Definition hkp5_op_test (n: Z) : expr :=
  Ebinop Oeq (Etempvar KC._op tint) (Econst_int (Int.repr n) tint) tint.

Definition hkp5_t45 : ident :=
  ltac:(let x := eval cbv beta iota delta [hkp5_s45] in
        (match hkp5_s45 with Sifthenelse _ (Sset t _) _ => t | _ => xH end) in exact x).

Lemma hkp5_ifc_shape :
  hkp5_ifc =
  Sifthenelse (hkp5_op_test 0) hkp5_sOp0
    (Sifthenelse (hkp5_op_test 1) hkp5_sOp1
      (Sifthenelse (hkp5_op_test 2) hkp5_sOp2
        (Sifthenelse (hkp5_op_test 3) hkp5_sOp3
          (Sifthenelse (hkp5_op_test 7) hkp5_sOp7
            (Ssequence hkp5_s45 (Sifthenelse (Etempvar hkp5_t45 tint) hkp5_sOp45 hkp5_sOp6)))))).
Proof. reflexivity. Qed.

Lemma hkp5_s45_shape :
  hkp5_s45 =
  Sifthenelse (hkp5_op_test 4) (Sset hkp5_t45 (Econst_int (Int.repr 1) tint))
    (Sset hkp5_t45 (Ecast (hkp5_op_test 5) tbool)).
Proof. reflexivity. Qed.

(* the operations' statement lists (for further cuts) *)
Definition hkp5_op0_stmts := ltac:(let x := eval cbv beta iota delta [hkp5_flat hkp5_sOp0] in (hkp5_flat hkp5_sOp0) in exact x).
Definition hkp5_op1_stmts := ltac:(let x := eval cbv beta iota delta [hkp5_flat hkp5_sOp1] in (hkp5_flat hkp5_sOp1) in exact x).
Definition hkp5_op2_stmts := ltac:(let x := eval cbv beta iota delta [hkp5_flat hkp5_sOp2] in (hkp5_flat hkp5_sOp2) in exact x).
Definition hkp5_op3_stmts := ltac:(let x := eval cbv beta iota delta [hkp5_flat hkp5_sOp3] in (hkp5_flat hkp5_sOp3) in exact x).
Definition hkp5_op7_stmts := ltac:(let x := eval cbv beta iota delta [hkp5_flat hkp5_sOp7] in (hkp5_flat hkp5_sOp7) in exact x).

Lemma hkp5_op_lengths :
  length hkp5_op0_stmts = 15%nat /\ length hkp5_op1_stmts = 5%nat /\ length hkp5_op2_stmts = 9%nat /\
  length hkp5_op3_stmts = 10%nat /\ length hkp5_op7_stmts = 8%nat.
Proof. repeat split. Qed.

Lemma hkp5_op_seql :
  hkp5_sOp0 = hkp5_seql hkp5_op0_stmts /\ hkp5_sOp1 = hkp5_seql hkp5_op1_stmts /\
  hkp5_sOp2 = hkp5_seql hkp5_op2_stmts /\ hkp5_sOp3 = hkp5_seql hkp5_op3_stmts /\
  hkp5_sOp7 = hkp5_seql hkp5_op7_stmts.
Proof. repeat split. Qed.
