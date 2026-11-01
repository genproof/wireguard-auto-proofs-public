(* law handshake_receive: the cut of main's body into
   phases.
   main's body = S; return 0 (implicit) with S = 24 statements (the last one the explicit `return 0`):
     PA =  0..13  peers = NULL, m_lul = 0, now = draw_boottime(), the boot clock, wg_noise_init, raw_d, raw_k,
                  setup_device, m_identity_of (id, ik), m_precomputed(ss_k), mk1, D's cookie secret and birthdate
     PB = 14      nk = hnodes_add(&peers, &wd, ik.pub, 0)
     PC = 15..16  n = draw_steps(); the loop adding n peers (hnodes_add)
     PD = 17      the loop over the nodes: hs_randomize, peer_randomize_rest, maybe wg_index_hashtable_insert
     PE = 18..19  kes = kents_add(&itd, peers, NULL, 0); steps = draw_steps()
     PL = 20      i = 0; the packet loop: for (; i < steps; i++) BODY
     PZ = 21..23  kents_free, hnodes_free, return 0
   BODY (after the loop guard) = 44 statements:
     B1 =  0..11  mi = mr = mc = buf = NULL, acc_init = acc_resp = 0, target = NULL; the clock moves (the 20 ms,
                  120 s and 1 s edges); wg_shim_boottime_ns = now
     B2 = 12..17  the queue length, the rate limiter, the skb's protocol and source
     B3 = 18..20  kind; the packet (the four kinds; `continue` on an allocation failure); skb.len = len
     B4 = 21..25  tw, fwd, hnodes_snap, kents_snap, the harness's model of the consume functions (target, acc_init, acc_resp)
     B5 = 26..33  dev_take, head0, skb_take, shim_take, rx_reset, secret_birth, the secret, dispatch(&wd, &skb)
     B6 = 34..38  path = 0, rotated = 0, the harness's model (load, macs, path, the rotation CHECK), ds's secret
     B7 = 39..40  CHECK(skb_same && the packet unchanged), CHECK(dev_same)
     B8 = 41      the four cases of CHECKs (initiation accepted, response accepted, cookie accepted, else)
     B9 = 42..43  free(skb.data), free(img) *)
Require Import VST.floyd.proofauto.
Require WgNoise.harness.x_handshake_receive.code.

Module HRM := WgNoise.harness.x_handshake_receive.code.

Fixpoint hrx5_seqs (l: list statement) (rest: statement) : statement :=
  match l with [] => rest | a :: l' => Ssequence a (hrx5_seqs l' rest) end.

Fixpoint hrx5_seql (l: list statement) : statement :=
  match l with [] => Sskip | [a] => a | a :: l' => Ssequence a (hrx5_seql l') end.

Fixpoint hrx5_flat (s: statement) : list statement :=
  match s with Ssequence a b => a :: hrx5_flat b | _ => [s] end.

Lemma hrx5_unfold_seql l : l <> [] ->
  unfold_Ssequence (hrx5_seql l) = concat (map unfold_Ssequence l).
Proof.
  induction l as [|a l IH]; intros Hl; [congruence |].
  destruct l as [|b l']; simpl.
  - rewrite app_nil_r; reflexivity.
  - simpl in IH. rewrite IH by discriminate. reflexivity.
Qed.

Lemma hrx5_unfold_seqs l rest :
  unfold_Ssequence (hrx5_seqs l rest) = concat (map unfold_Ssequence l) ++ unfold_Ssequence rest.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity |]. rewrite IH, app_assoc. reflexivity.
Qed.

Lemma hrx5_overridePost2 Q Q' R : overridePost Q (overridePost Q' R) = overridePost Q R.
Proof. destruct R; reflexivity. Qed.

Lemma hrx5_semax_cut {Espec: OracleKind} {cs: compspecs} Delta P Q R l rest :
  l <> [] ->
  semax Delta P (hrx5_seql l) (overridePost Q R) -> semax Delta Q rest R ->
  semax Delta P (hrx5_seqs l rest) R.
Proof.
  intros Hl H1 H2.
  apply (semax_unfold_Ssequence (Ssequence (hrx5_seql l) rest)).
  - simpl. rewrite hrx5_unfold_seql, hrx5_unfold_seqs by auto. reflexivity.
  - eapply semax_seq; eauto.
Qed.

(* a list cut into two consecutive non-empty pieces (for children that cut their phase further) *)
Lemma hrx5_seql_app {Espec: OracleKind} {cs: compspecs} Delta P Q R l1 l2 :
  l1 <> [] -> l2 <> [] ->
  semax Delta P (hrx5_seql l1) (overridePost Q R) -> semax Delta Q (hrx5_seql l2) R ->
  semax Delta P (hrx5_seql (l1 ++ l2)) R.
Proof.
  intros H1 H2 S1 S2.
  assert (H12: l1 ++ l2 <> []) by (destruct l1; [congruence | discriminate]).
  apply (semax_unfold_Ssequence (Ssequence (hrx5_seql l1) (hrx5_seql l2))).
  - simpl. rewrite (hrx5_unfold_seql _ H12), (hrx5_unfold_seql _ H1), (hrx5_unfold_seql _ H2), map_app, concat_app.
    reflexivity.
  - eapply semax_seq; eauto.
Qed.

(* ---------------------------------------------------------------------- *)
(* main's top statements                                                   *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_stmts : list statement :=
  ltac:(let x := eval cbv beta iota delta [hrx5_flat HRM.f_main fn_body] in
        (match fn_body HRM.f_main with Ssequence s _ => hrx5_flat s | s => [s] end) in exact x).

Lemma hrx5_stmts_length : length hrx5_stmts = 24%nat.
Proof. reflexivity. Qed.

Definition hrx5_l (i n: nat) : list statement := firstn n (skipn i hrx5_stmts).

Definition hrx5_PA := ltac:(let x := eval cbv beta iota delta [hrx5_l hrx5_seql firstn skipn hrx5_stmts] in (hrx5_seql (hrx5_l 0 14)) in exact x).
Definition hrx5_PB := ltac:(let x := eval cbv beta iota delta [hrx5_l hrx5_seql firstn skipn hrx5_stmts] in (hrx5_seql (hrx5_l 14 1)) in exact x).
Definition hrx5_PC := ltac:(let x := eval cbv beta iota delta [hrx5_l hrx5_seql firstn skipn hrx5_stmts] in (hrx5_seql (hrx5_l 15 2)) in exact x).
Definition hrx5_PD := ltac:(let x := eval cbv beta iota delta [hrx5_l hrx5_seql firstn skipn hrx5_stmts] in (hrx5_seql (hrx5_l 17 1)) in exact x).
Definition hrx5_PE := ltac:(let x := eval cbv beta iota delta [hrx5_l hrx5_seql firstn skipn hrx5_stmts] in (hrx5_seql (hrx5_l 18 2)) in exact x).
Definition hrx5_PZ := ltac:(let x := eval cbv beta iota delta [hrx5_l hrx5_seql firstn skipn hrx5_stmts] in (hrx5_seql (hrx5_l 21 3)) in exact x).

(* ---------------------------------------------------------------------- *)
(* the packet loop (statement 20): i = 0; Sloop (if (i < steps) skip else break; BODY) (i++)              *)
(* ---------------------------------------------------------------------- *)

(* the loop's body after the guard, flattened *)
Definition hrx5_bstmts : list statement :=
  ltac:(let x := eval cbv beta iota delta [hrx5_flat hrx5_stmts nth] in
        (match nth 20 hrx5_stmts Sskip with
         | Ssequence _ (Sloop (Ssequence _ b) _) => hrx5_flat b
         | _ => [] end) in exact x).

Lemma hrx5_bstmts_length : length hrx5_bstmts = 44%nat.
Proof. reflexivity. Qed.

Definition hrx5_bl (i n: nat) : list statement := firstn n (skipn i hrx5_bstmts).

Definition hrx5_B1 := ltac:(let x := eval cbv beta iota delta [hrx5_bl hrx5_seql firstn skipn hrx5_bstmts] in (hrx5_seql (hrx5_bl 0 12)) in exact x).
Definition hrx5_B2 := ltac:(let x := eval cbv beta iota delta [hrx5_bl hrx5_seql firstn skipn hrx5_bstmts] in (hrx5_seql (hrx5_bl 12 6)) in exact x).
Definition hrx5_B3 := ltac:(let x := eval cbv beta iota delta [hrx5_bl hrx5_seql firstn skipn hrx5_bstmts] in (hrx5_seql (hrx5_bl 18 3)) in exact x).
Definition hrx5_B4 := ltac:(let x := eval cbv beta iota delta [hrx5_bl hrx5_seql firstn skipn hrx5_bstmts] in (hrx5_seql (hrx5_bl 21 5)) in exact x).
Definition hrx5_B5 := ltac:(let x := eval cbv beta iota delta [hrx5_bl hrx5_seql firstn skipn hrx5_bstmts] in (hrx5_seql (hrx5_bl 26 8)) in exact x).
Definition hrx5_B6 := ltac:(let x := eval cbv beta iota delta [hrx5_bl hrx5_seql firstn skipn hrx5_bstmts] in (hrx5_seql (hrx5_bl 34 5)) in exact x).
Definition hrx5_B7 := ltac:(let x := eval cbv beta iota delta [hrx5_bl hrx5_seql firstn skipn hrx5_bstmts] in (hrx5_seql (hrx5_bl 39 2)) in exact x).
Definition hrx5_B8 := ltac:(let x := eval cbv beta iota delta [hrx5_bl hrx5_seql firstn skipn hrx5_bstmts] in (hrx5_seql (hrx5_bl 41 1)) in exact x).
Definition hrx5_B9 := ltac:(let x := eval cbv beta iota delta [hrx5_bl hrx5_seql firstn skipn hrx5_bstmts] in (hrx5_seql (hrx5_bl 42 2)) in exact x).

(* the loop's body after the guard, cut *)
Definition hrx5_body : statement :=
  hrx5_seqs (hrx5_bl 0 12) (hrx5_seqs (hrx5_bl 12 6) (hrx5_seqs (hrx5_bl 18 3) (hrx5_seqs (hrx5_bl 21 5)
    (hrx5_seqs (hrx5_bl 26 8) (hrx5_seqs (hrx5_bl 34 5) (hrx5_seqs (hrx5_bl 39 2) (hrx5_seqs (hrx5_bl 41 1)
      (hrx5_seql (hrx5_bl 42 2))))))))).

(* the guard and the increment *)
Definition hrx5_guard : statement :=
  Sifthenelse (Ebinop Olt (Etempvar HRM._i tulong) (Etempvar HRM._steps tulong) tint) Sskip Sbreak.
Definition hrx5_incr : statement :=
  Sset HRM._i (Ebinop Oadd (Etempvar HRM._i tulong) (Econst_int (Int.repr 1) tint) tulong).
Definition hrx5_init : statement := Sset HRM._i (Ecast (Econst_int (Int.repr 0) tint) tulong).

Definition hrx5_PL : statement :=
  Ssequence hrx5_init (Sloop (Ssequence hrx5_guard hrx5_body) hrx5_incr).

Lemma hrx5_body_eq :
  fn_body HRM.f_main =
  Ssequence
    (hrx5_seqs (hrx5_l 0 14) (hrx5_seqs (hrx5_l 14 1) (hrx5_seqs (hrx5_l 15 2) (hrx5_seqs (hrx5_l 17 1)
      (hrx5_seqs (hrx5_l 18 2) (Ssequence hrx5_PL (hrx5_seql (hrx5_l 21 3))))))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.

Lemma hrx5_phases_eq :
  hrx5_PA = hrx5_seql (hrx5_l 0 14) /\ hrx5_PB = hrx5_seql (hrx5_l 14 1) /\
  hrx5_PC = hrx5_seql (hrx5_l 15 2) /\ hrx5_PD = hrx5_seql (hrx5_l 17 1) /\
  hrx5_PE = hrx5_seql (hrx5_l 18 2) /\ hrx5_PZ = hrx5_seql (hrx5_l 21 3).
Proof. repeat split. Qed.

Lemma hrx5_bphases_eq :
  hrx5_B1 = hrx5_seql (hrx5_bl 0 12) /\ hrx5_B2 = hrx5_seql (hrx5_bl 12 6) /\
  hrx5_B3 = hrx5_seql (hrx5_bl 18 3) /\ hrx5_B4 = hrx5_seql (hrx5_bl 21 5) /\
  hrx5_B5 = hrx5_seql (hrx5_bl 26 8) /\ hrx5_B6 = hrx5_seql (hrx5_bl 34 5) /\
  hrx5_B7 = hrx5_seql (hrx5_bl 39 2) /\ hrx5_B8 = hrx5_seql (hrx5_bl 41 1) /\
  hrx5_B9 = hrx5_seql (hrx5_bl 42 2).
Proof. repeat split. Qed.
