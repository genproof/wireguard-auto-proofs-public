(* law counter, harness piece: the harness's shadow list (struct acc) and the pure facts main needs.
   All in the world compspecs W_counter. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.counter.counter_spec.
Require Import WgNoise.harness.x_counter.code.

#[local] Existing Instance W_counter.
Local Open Scope Z_scope.

Definition tacc := Tstruct _acc noattr.

(* the pruning of the harness: keep x when x + 1 + W >= top *)
Definition hcnt_prune (top: Z) (L: list Z) : list Z := filter (fun x => top <=? x + 1 + CNT_W) L.

Lemma existsb_prune top L t:
  top - CNT_W <= t -> existsb (Z.eqb (t - 1)) (hcnt_prune top L) = existsb (Z.eqb (t - 1)) L.
Proof.
  intros Ht. unfold hcnt_prune. induction L as [|x L IH]; simpl; auto.
  destruct (Z.eqb_spec (t - 1) x).
  - subst x. replace (top <=? t - 1 + 1 + CNT_W) with true by (symmetry; apply Z.leb_le; lia).
    simpl. rewrite Z.eqb_refl. auto.
  - destruct (top <=? x + 1 + CNT_W); simpl; auto.
    destruct (Z.eqb_spec (t - 1) x); [contradiction|auto].
Qed.

Lemma cnt_inv_prune3 top L bm: cnt_inv top L bm -> cnt_inv top (hcnt_prune top L) bm.
Proof.
  intros [H1 H2 H3 H4 H5 H6]. constructor; auto.
  - intros n Hn. apply H4. unfold hcnt_prune in Hn. apply filter_In in Hn. tauto.
  - intros t Ht. rewrite existsb_prune by lia. auto.
Qed.

(* the list of accepted nonces, malloc'd nodes struct acc { u64 n; struct acc *next; } *)
Fixpoint accs (L: list Z) (p: val) : mpred :=
  match L with
  | nil => !! (p = nullval) && emp
  | x :: L' => EX q: val,
      malloc_token Ews tacc p * data_at Ews tacc (Vlong (Int64.repr x), q) p * accs L' q
  end.

(* a segment of nodes from p up to q (excluded) *)
Fixpoint accseg (L: list Z) (p q: val) : mpred :=
  match L with
  | nil => !! (p = q) && emp
  | x :: L' => EX r: val,
      malloc_token Ews tacc p * data_at Ews tacc (Vlong (Int64.repr x), r) p * accseg L' r q
  end.

(* a chain of cells: the cell c (share sh) points to the first node of K, the next field of each node of K
   points to the following one, the last one's next field is the cell l (not included) *)
Fixpoint cseg (sh: share) (K: list Z) (c l: val) : mpred :=
  match K with
  | nil => !! (c = l) && emp
  | x :: K' => EX p: val,
      data_at sh (tptr tacc) p c * malloc_token Ews tacc p *
      field_at Ews tacc [StructField _n] (Vlong (Int64.repr x)) p *
      cseg Ews K' (field_address tacc [StructField _next] p) l
  end.

(* the share of the current cell after the chain K *)
Definition csh (sh: share) (K: list Z) : share := match K with nil => sh | _ => Ews end.

Lemma csh_Ews K: csh Ews K = Ews.
Proof. destruct K; reflexivity. Qed.

Lemma accs_local_facts L p: accs L p |-- !! (is_pointer_or_null p /\ (p = nullval <-> L = nil)).
Proof.
  destruct L as [|x L]; simpl; Intros; [entailer!; tauto|].
  Intros q. entailer!. split; intros; [subst; contradiction | discriminate].
Qed.
#[export] Hint Resolve accs_local_facts : saturate_local.

Lemma accs_valid_pointer L p: accs L p |-- valid_pointer p.
Proof. destruct L as [|x L]; simpl; Intros; [subst; auto with valid_pointer|]. Intros q. entailer!. Qed.
#[export] Hint Resolve accs_valid_pointer : valid_pointer.

Lemma accseg_app K x p q r:
  accseg K p q * malloc_token Ews tacc q * data_at Ews tacc (Vlong (Int64.repr x), r) q |--
  accseg (K ++ [x]) p r.
Proof.
  revert p. induction K as [|y K IH]; intros p; simpl.
  - Intros. subst. Exists r. entailer!.
  - Intros s. Exists s. sep_apply (IH s). entailer!.
Qed.

Lemma accseg_accs K R p q: accseg K p q * accs R q |-- accs (K ++ R) p.
Proof.
  revert p. induction K as [|y K IH]; intros p; simpl.
  - Intros. subst. entailer!.
  - Intros s. Exists s. sep_apply (IH s). entailer!.
Qed.

Lemma cseg_extend sh K c l p x:
  cseg sh K c l * data_at (csh sh K) (tptr tacc) p l * malloc_token Ews tacc p *
  field_at Ews tacc [StructField _n] (Vlong (Int64.repr x)) p |--
  cseg sh (K ++ [x]) c (field_address tacc [StructField _next] p).
Proof.
  revert sh c. induction K as [|y K IH]; intros sh c; simpl.
  - Intros. subst. Exists p. entailer!.
  - Intros s. Exists s. specialize (IH Ews (field_address tacc [StructField _next] s)).
    rewrite csh_Ews in IH. sep_apply IH. entailer!.
Qed.

Lemma cseg_close sh K R c l q:
  cseg sh K c l * data_at (csh sh K) (tptr tacc) q l * accs R q |--
  EX p: val, data_at sh (tptr tacc) p c * accs (K ++ R) p.
Proof.
  revert sh c. induction K as [|y K IH]; intros sh c; simpl.
  - Intros. subst. Exists q. entailer!.
  - Intros s. specialize (IH Ews (field_address tacc [StructField _next] s)).
    rewrite csh_Ews in IH. sep_apply IH. Intros p.
    Exists s p. unfold_data_at (data_at Ews tacc _ s). rewrite (field_at_data_at Ews tacc [StructField _next]).
    entailer!.
Qed.

Lemma upd_Znth_Zrepeat_step {A} {d: Inhabitant A} (a b: A) i n:
  0 <= i < n ->
  upd_Znth i (Zrepeat a i ++ Zrepeat b (n - i)) a = Zrepeat a (i + 1) ++ Zrepeat b (n - (i + 1)).
Proof.
  intros H.
  rewrite upd_Znth_app2 by (rewrite !Zlength_Zrepeat by lia; lia).
  rewrite Zlength_Zrepeat by lia. rewrite Z.sub_diag.
  unfold Zrepeat.
  replace (Z.to_nat (n - i)) with (S (Z.to_nat (n - (i + 1)))) by lia.
  replace (Z.to_nat (i + 1)) with (Z.to_nat i + 1)%nat by lia.
  rewrite repeat_app. change (repeat b (S ?k)) with (b :: repeat b k). rewrite upd_Znth0.
  rewrite <- app_assoc. reflexivity.
Qed.

Lemma cnt_bit_zero t: cnt_bit (Zrepeat 0 128) t = false.
Proof.
  unfold cnt_bit. rewrite Znth_Zrepeat by (pose proof (Z.mod_pos_bound (t / 64) 128); lia).
  apply Z.testbit_0_l.
Qed.

Lemma cnt_inv_init: cnt_inv 0 [] (Zrepeat 0 128).
Proof.
  constructor.
  - reflexivity.
  - apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst. rep_lia.
  - unfold CNT_R, CNT_W. rep_lia.
  - intros n [].
  - intros t _. rewrite cnt_bit_zero. reflexivity.
  - intros t _. apply cnt_bit_zero.
Qed.

Lemma int64_eq_repr x y:
  0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.eq (Int64.repr x) (Int64.repr y) = (x =? y).
Proof.
  intros Hx Hy. unfold Int64.eq. rewrite !Int64.unsigned_repr by lia.
  destruct (zeq x y), (Z.eqb_spec x y); congruence.
Qed.

Lemma existsb_snoc n K x: existsb (Z.eqb n) (K ++ [x]) = orb (existsb (Z.eqb n) K) (n =? x).
Proof. rewrite existsb_app. simpl. rewrite orb_false_r. reflexivity. Qed.

Lemma cnt_L_bound top L bm x: cnt_inv top L bm -> In x L -> 0 <= x < Int64.max_unsigned - CNT_W - 1.
Proof. intros H Hx. pose proof (cnt_L_range _ _ _ H x Hx). pose proof (cnt_top_range _ _ _ H). unfold CNT_R in *. lia. Qed.

Lemma u64_R: Int64.unsigned (Int64.repr (-1 - 8128 - 1)) = CNT_R.
Proof. reflexivity. Qed.
Lemma u64_R1: Int64.unsigned (Int64.repr (-1 - 8128 - 1 + 1)) = CNT_R + 1.
Proof. reflexivity. Qed.
Lemma CNT_R_val: CNT_R = Int64.max_unsigned - 8129.
Proof. reflexivity. Qed.

Lemma ltu_repr x y:
  0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr x) (Int64.repr y) = (x <? y).
Proof.
  intros Hx Hy. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt x y), (Z.ltb_spec x y); auto; lia.
Qed.

Lemma acc_split x r q:
  data_at Ews tacc (Vlong (Int64.repr x), r) q =
  (field_at Ews tacc [StructField _n] (Vlong (Int64.repr x)) q *
   data_at Ews (tptr tacc) r (field_address tacc [StructField _next] q))%logic.
Proof.
  unfold_data_at (data_at _ _ _ q). rewrite (field_at_data_at Ews tacc [StructField _next]). reflexivity.
Qed.
