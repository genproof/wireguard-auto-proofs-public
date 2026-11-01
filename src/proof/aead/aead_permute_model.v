(* Model facts for chacha_permute (piece aead): the kernel's order of the 64 steps of a double round
   (lib/crypto/chacha-block-generic.c, columns interleaved) computes chacha_dround (RFC order). *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.aead.aead_model.

Local Open Scope Z_scope.
(* ---------------------------------------------------------------------- *)
(* the kernel's order of the 64 steps of a double round                  *)
(* ---------------------------------------------------------------------- *)

Definition kadd (l: list int) (a b: Z) : list int := upd_Znth a l (Int.add (Znth a l) (Znth b l)).
Definition krol (l: list int) (d a s: Z) : list int :=
  upd_Znth d l (Int.rol (Int.xor (Znth d l) (Znth a l)) (Int.repr s)).

Lemma Zlength_kadd : forall l a b, 0 <= a < Zlength l -> Zlength (kadd l a b) = Zlength l.
Proof. intros. unfold kadd. rewrite Zlength_upd_Znth; auto. Qed.
Lemma Zlength_krol : forall l d a s, 0 <= d < Zlength l -> Zlength (krol l d a s) = Zlength l.
Proof. intros. unfold krol. rewrite Zlength_upd_Znth; auto. Qed.


Definition k_dround (l: list int) : list int :=
  let l := kadd l 0 4 in
  let l := krol l 12 0 16 in
  let l := kadd l 1 5 in
  let l := krol l 13 1 16 in
  let l := kadd l 2 6 in
  let l := krol l 14 2 16 in
  let l := kadd l 3 7 in
  let l := krol l 15 3 16 in
  let l := kadd l 8 12 in
  let l := krol l 4 8 12 in
  let l := kadd l 9 13 in
  let l := krol l 5 9 12 in
  let l := kadd l 10 14 in
  let l := krol l 6 10 12 in
  let l := kadd l 11 15 in
  let l := krol l 7 11 12 in
  let l := kadd l 0 4 in
  let l := krol l 12 0 8 in
  let l := kadd l 1 5 in
  let l := krol l 13 1 8 in
  let l := kadd l 2 6 in
  let l := krol l 14 2 8 in
  let l := kadd l 3 7 in
  let l := krol l 15 3 8 in
  let l := kadd l 8 12 in
  let l := krol l 4 8 7 in
  let l := kadd l 9 13 in
  let l := krol l 5 9 7 in
  let l := kadd l 10 14 in
  let l := krol l 6 10 7 in
  let l := kadd l 11 15 in
  let l := krol l 7 11 7 in
  let l := kadd l 0 5 in
  let l := krol l 15 0 16 in
  let l := kadd l 1 6 in
  let l := krol l 12 1 16 in
  let l := kadd l 2 7 in
  let l := krol l 13 2 16 in
  let l := kadd l 3 4 in
  let l := krol l 14 3 16 in
  let l := kadd l 10 15 in
  let l := krol l 5 10 12 in
  let l := kadd l 11 12 in
  let l := krol l 6 11 12 in
  let l := kadd l 8 13 in
  let l := krol l 7 8 12 in
  let l := kadd l 9 14 in
  let l := krol l 4 9 12 in
  let l := kadd l 0 5 in
  let l := krol l 15 0 8 in
  let l := kadd l 1 6 in
  let l := krol l 12 1 8 in
  let l := kadd l 2 7 in
  let l := krol l 13 2 8 in
  let l := kadd l 3 4 in
  let l := krol l 14 3 8 in
  let l := kadd l 10 15 in
  let l := krol l 5 10 7 in
  let l := kadd l 11 12 in
  let l := krol l 6 11 7 in
  let l := kadd l 8 13 in
  let l := krol l 7 8 7 in
  let l := kadd l 9 14 in
  let l := krol l 4 9 7 in
  l.

(* ---------------------------------------------------------------------- *)
(* the model: the kernel's order is the RFC's double round                 *)
(* Both orders as lists of steps; a boolean check that one is a reordering *)
(* of the other by swaps of independent steps (proved sound once).         *)
(* ---------------------------------------------------------------------- *)

Inductive op := OAdd (a b: Z) | ORol (d a s: Z).

Definition apply_op (l: list int) (o: op) : list int :=
  match o with OAdd a b => kadd l a b | ORol d a s => krol l d a s end.
Definition run (os: list op) (l: list int) : list int := fold_left apply_op os l.

Definition op_w (o: op) : Z := match o with OAdd a _ => a | ORol d _ _ => d end.
Definition op_r (o: op) : Z := match o with OAdd _ b => b | ORol _ a _ => a end.
Definition in16 (z: Z) : bool := (0 <=? z) && (z <? 16).
Definition op_ok (o: op) : bool := in16 (op_w o) && in16 (op_r o).
Definition op_eqb (o1 o2: op) : bool :=
  match o1, o2 with
  | OAdd a b, OAdd a' b' => (a =? a') && (b =? b')
  | ORol d a s, ORol d' a' s' => (d =? d') && (a =? a') && (s =? s')
  | _, _ => false
  end.
(* o1 and o2 touch different words except for common reads *)
Definition indep (o1 o2: op) : bool :=
  op_ok o1 && op_ok o2 && negb (op_w o1 =? op_w o2) && negb (op_w o1 =? op_r o2) && negb (op_w o2 =? op_r o1).

(* remove o from os, if every step before it is independent of it *)
Fixpoint extract (o: op) (os: list op) : option (list op) :=
  match os with
  | [] => None
  | o' :: os' =>
      if op_eqb o' o then Some os'
      else if indep o' o then match extract o os' with Some r => Some (o' :: r) | None => None end
      else None
  end.

Fixpoint reorders (a b: list op) : bool :=
  match b with
  | [] => match a with [] => true | _ => false end
  | o :: b' => match extract o a with Some a' => op_ok o && reorders a' b' | None => false end
  end.

Lemma op_eqb_eq : forall o1 o2, op_eqb o1 o2 = true -> o1 = o2.
Proof.
  destruct o1, o2; simpl; intros H; try discriminate;
  repeat rewrite andb_true_iff in H; decompose [and] H; repeat match goal with H: (_ =? _) = true |- _ => apply Z.eqb_eq in H end; subst; auto.
Qed.

Lemma Zlength_apply_op : forall l o, op_ok o = true -> Zlength l = 16 -> Zlength (apply_op l o) = 16.
Proof.
  intros l o Ho Hl. unfold op_ok, in16 in Ho. rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt in Ho.
  destruct o; simpl in *; [rewrite Zlength_kadd | rewrite Zlength_krol]; lia.
Qed.

Lemma upd_Znth_comm16 : forall (l: list int) i j u v, Zlength l = 16 -> 0 <= i < 16 -> 0 <= j < 16 -> i <> j ->
  upd_Znth i (upd_Znth j l v) u = upd_Znth j (upd_Znth i l u) v.
Proof.
  intros. apply Znth_eq_ext; rewrite ?Zlength_upd_Znth; auto. intros k Hk.
  destruct (Z.eq_dec k i); [subst k; rewrite upd_Znth_same, upd_Znth_diff, upd_Znth_same; rewrite ?Zlength_upd_Znth; auto; lia|].
  destruct (Z.eq_dec k j); [subst k; rewrite upd_Znth_diff, upd_Znth_same, upd_Znth_same; rewrite ?Zlength_upd_Znth; auto; lia|].
  rewrite !upd_Znth_diff; rewrite ?Zlength_upd_Znth; auto; lia.
Qed.

Lemma apply_op_comm : forall l o1 o2, Zlength l = 16 -> indep o1 o2 = true ->
  apply_op (apply_op l o1) o2 = apply_op (apply_op l o2) o1.
Proof.
  intros l o1 o2 Hl H. unfold indep, op_ok, in16 in H.
  repeat rewrite andb_true_iff in H. repeat rewrite negb_true_iff in H. decompose [and] H; clear H.
  repeat match goal with H: (_ =? _) = false |- _ => apply Z.eqb_neq in H | H: (_ <=? _) = true |- _ => apply Z.leb_le in H
                    | H: (_ <? _) = true |- _ => apply Z.ltb_lt in H end.
  destruct o1 as [a1 b1|d1 a1 s1], o2 as [a2 b2|d2 a2 s2]; simpl in *; unfold kadd, krol;
  rewrite ?upd_Znth_diff by (rewrite ?Zlength_upd_Znth; lia); apply upd_Znth_comm16; auto; lia.
Qed.

Lemma extract_sound : forall o os os' l, Zlength l = 16 -> extract o os = Some os' ->
  run os l = run os' (apply_op l o).
Proof.
  intros o os; induction os as [|o' os IH]; intros os' l Hl H; simpl in H; [discriminate|].
  destruct (op_eqb o' o) eqn:E.
  - apply op_eqb_eq in E; subst o'. inversion H; subst. reflexivity.
  - destruct (indep o' o) eqn:I; [|discriminate].
    destruct (extract o os) eqn:X; inversion H; subst; clear H.
    unfold run; simpl. fold (run os (apply_op l o')). fold (run l0 (apply_op (apply_op l o) o')).
    assert (Ho': op_ok o' = true) by (unfold indep in I; destruct (op_ok o'); auto).
    rewrite (IH l0); [| apply Zlength_apply_op; auto | auto].
    rewrite apply_op_comm; auto.
Qed.

Lemma reorders_sound : forall b a l, Zlength l = 16 -> reorders a b = true -> run a l = run b l.
Proof.
  induction b as [|o b IH]; intros a l Hl H; simpl in H.
  - destruct a; [reflexivity | discriminate].
  - destruct (extract o a) eqn:X; [|discriminate]. apply andb_true_iff in H as [Ho H].
    rewrite (extract_sound o a l0 l); auto. unfold run at 2; simpl. apply IH; auto.
    apply Zlength_apply_op; auto.
Qed.

Definition qround_ops (a b c d: Z) : list op :=
  [OAdd a b; ORol d a 16; OAdd c d; ORol b c 12; OAdd a b; ORol d a 8; OAdd c d; ORol b c 7].
Definition rfc_ops : list op :=
  qround_ops 0 4 8 12 ++ qround_ops 1 5 9 13 ++ qround_ops 2 6 10 14 ++ qround_ops 3 7 11 15 ++
  qround_ops 0 5 10 15 ++ qround_ops 1 6 11 12 ++ qround_ops 2 7 8 13 ++ qround_ops 3 4 9 14.
Definition kernel_ops : list op :=
  [OAdd 0 4; ORol 12 0 16; OAdd 1 5; ORol 13 1 16;
   OAdd 2 6; ORol 14 2 16; OAdd 3 7; ORol 15 3 16;
   OAdd 8 12; ORol 4 8 12; OAdd 9 13; ORol 5 9 12;
   OAdd 10 14; ORol 6 10 12; OAdd 11 15; ORol 7 11 12;
   OAdd 0 4; ORol 12 0 8; OAdd 1 5; ORol 13 1 8;
   OAdd 2 6; ORol 14 2 8; OAdd 3 7; ORol 15 3 8;
   OAdd 8 12; ORol 4 8 7; OAdd 9 13; ORol 5 9 7;
   OAdd 10 14; ORol 6 10 7; OAdd 11 15; ORol 7 11 7;
   OAdd 0 5; ORol 15 0 16; OAdd 1 6; ORol 12 1 16;
   OAdd 2 7; ORol 13 2 16; OAdd 3 4; ORol 14 3 16;
   OAdd 10 15; ORol 5 10 12; OAdd 11 12; ORol 6 11 12;
   OAdd 8 13; ORol 7 8 12; OAdd 9 14; ORol 4 9 12;
   OAdd 0 5; ORol 15 0 8; OAdd 1 6; ORol 12 1 8;
   OAdd 2 7; ORol 13 2 8; OAdd 3 4; ORol 14 3 8;
   OAdd 10 15; ORol 5 10 7; OAdd 11 12; ORol 6 11 7;
   OAdd 8 13; ORol 7 8 7; OAdd 9 14; ORol 4 9 7].

Lemma kernel_ops_reorders : reorders kernel_ops rfc_ops = true.
Proof. vm_compute. reflexivity. Qed.

Lemma qround_run : forall l a b c d, chacha_qround l a b c d = run (qround_ops a b c d) l.
Proof.
  intros. unfold qround_ops, run. cbn [fold_left apply_op]. unfold kadd, krol, chacha_qround. cbv zeta.
  reflexivity.
Qed.

Lemma run_app : forall a b l, run (a ++ b) l = run b (run a l).
Proof. intros. unfold run. apply fold_left_app. Qed.

Lemma chacha_dround_run : forall l, chacha_dround l = run rfc_ops l.
Proof.
  intros. unfold chacha_dround. cbv zeta. rewrite !qround_run.
  unfold rfc_ops. rewrite !run_app. reflexivity.
Qed.

Lemma k_dround_run : forall l, k_dround l = run kernel_ops l.
Proof. intros. unfold k_dround, kernel_ops, run. cbn [fold_left apply_op]. cbv zeta. reflexivity. Qed.

Lemma k_dround_eq : forall l, Zlength l = 16 -> k_dround l = chacha_dround l.
Proof.
  intros. transitivity (run kernel_ops l); [apply k_dround_run |].
  transitivity (run rfc_ops l); [| symmetry; apply chacha_dround_run].
  exact (reorders_sound rfc_ops kernel_ops l H kernel_ops_reorders).
Qed.

Lemma Zlength_run : forall os l, forallb op_ok os = true -> Zlength l = 16 -> Zlength (run os l) = 16.
Proof.
  induction os as [|o os IH]; intros l H Hl; simpl in H; [exact Hl|].
  apply andb_true_iff in H as [Ho H]. unfold run; simpl. apply IH; auto. apply Zlength_apply_op; auto.
Qed.

Lemma Zlength_chacha_dround : forall l, Zlength l = 16 -> Zlength (chacha_dround l) = 16.
Proof.
  intros. rewrite chacha_dround_run. apply Zlength_run; [vm_compute; reflexivity | exact H].
Qed.

(* chacha_rounds is unfolded before any conversion: the kernel would otherwise compare
   chacha_rounds (S n) l with chacha_rounds n (chacha_dround l) argument by argument and evaluate
   chacha_dround l symbolically (exponential) *)
Lemma rounds_O : forall l, chacha_rounds O l = l.
Proof. intros. reflexivity. Qed.

Lemma rounds_S1 : forall n l, chacha_rounds (S n) l = chacha_rounds n (chacha_dround l).
Proof. intros. unfold chacha_rounds. reflexivity. Qed.

Lemma chacha_rounds_S : forall n l, chacha_rounds (S n) l = chacha_dround (chacha_rounds n l).
Proof.
  induction n; intros l.
  - rewrite rounds_S1, !rounds_O. reflexivity.
  - rewrite rounds_S1. rewrite IHn. rewrite rounds_S1. reflexivity.
Qed.

Lemma Zlength_chacha_rounds : forall n l, Zlength l = 16 -> Zlength (chacha_rounds n l) = 16.
Proof.
  induction n; intros l H.
  - rewrite rounds_O. exact H.
  - rewrite chacha_rounds_S. apply Zlength_chacha_dround. apply IHn. exact H.
Qed.

Lemma Zlength_kadd16 : forall l a b, Zlength l = 16 -> 0 <= a < 16 -> Zlength (kadd l a b) = 16.
Proof. intros. rewrite Zlength_kadd; lia. Qed.
Lemma Zlength_krol16 : forall l d a s, Zlength l = 16 -> 0 <= d < 16 -> Zlength (krol l d a s) = 16.
Proof. intros. rewrite Zlength_krol; lia. Qed.
Ltac zl16 := repeat first [assumption | apply Zlength_kadd16 | apply Zlength_krol16 | lia].

