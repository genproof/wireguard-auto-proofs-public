
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_body3_shim_table1.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

(* ---- the warning chains ---- *)
Lemma prot4_rot_add_warn_init_null P new W w :
  p_next P = nullval ->
  add_new_keypair_warn P new true W w = kp_put_warn (p_prev P) (kw_KS W) w.
Proof.
  intros E. unfold add_new_keypair_warn. rewrite E. destruct (eq_dec nullval nullval); [|congruence].
  reflexivity.
Qed.

Lemma prot4_rot_add_warn_init_next P new W w :
  p_next P <> nullval ->
  add_new_keypair_warn P new true W w =
  kp_put_warn (p_prev P) (kw_KS (kp_put (p_cur P) true W)) (kp_put_warn (p_cur P) (kw_KS W) w).
Proof.
  intros E. unfold add_new_keypair_warn. destruct (eq_dec (p_next P) nullval); [contradiction|].
  reflexivity.
Qed.

Lemma prot4_rot_add_warn_resp P new W w :
  add_new_keypair_warn P new false W w =
  kp_put_warn (p_prev P) (kw_KS (kp_put (p_next P) true W)) (kp_put_warn (p_next P) (kw_KS W) w).
Proof. reflexivity. Qed.

Lemma prot4_rot_recv_warn_eq P k W w :
  k = p_next P -> received_with_keypair_warn P k W w = kp_put_warn (p_prev P) (kw_KS W) w.
Proof.
  intros E. unfold received_with_keypair_warn. destruct (eq_dec k (p_next P)); [reflexivity | contradiction].
Qed.

Lemma prot4_rot_recv_warn_neq P k W w :
  k <> p_next P -> received_with_keypair_warn P k W w = w.
Proof.
  intros E. unfold received_with_keypair_warn. destruct (eq_dec k (p_next P)); [contradiction | reflexivity].
Qed.

Lemma prot4_rot_clear_warn P W w :
  keypairs_clear_warn P W w =
  kp_put_warn (p_cur P) (kw_KS (kp_put (p_prev P) true (kp_put (p_next P) true W)))
    (kp_put_warn (p_prev P) (kw_KS (kp_put (p_next P) true W)) (kp_put_warn (p_next P) (kw_KS W) w)).
Proof. reflexivity. Qed.

(* ---- a pool entry is a pointer ---- *)
Lemma prot4_rot_pool_isptr sht tab T a :
  In a (saddrs (t_D T)) -> itable sht tab T |-- !! isptr a.
Proof.
  intros Ha. destruct (prot3_shim_table1_sfind_in _ _ Ha) as (sh & E & HE).
  unfold itable. Intros. rewrite (prot3_shim_table1_split _ _ _ _ _ HE).
  unfold pool_item_rep, entry_at. entailer!.
Qed.

(* ---- pointer comparisons of a keypair (NULL or valid) with a slot (NULL or valid) ---- *)
Local Transparent denote_tc_test_eq.
Lemma prot4_rot_tc_ptrs (R: mpred) k n :
  k = nullval \/ (isptr k /\ (R |-- valid_pointer k)) ->
  n = nullval \/ (isptr n /\ (R |-- valid_pointer n)) ->
  R |-- denote_tc_test_eq k n.
Proof.
  intros [Ek|[Pk VK]] [En|[Pn VN]].
  - subst. unfold nullval, denote_tc_test_eq. simpl. apply andp_right; apply prop_right; auto.
  - subst. destruct n; try contradiction. unfold nullval, denote_tc_test_eq. simpl.
    apply andp_right; [apply prop_right; auto|]. apply valid_pointer_weak'. exact VN.
  - subst. destruct k; try contradiction. unfold nullval, denote_tc_test_eq. simpl.
    apply andp_right; [apply prop_right; auto|]. apply valid_pointer_weak'. exact VK.
  - destruct k; try contradiction. destruct n; try contradiction. unfold denote_tc_test_eq. simpl.
    unfold test_eq_ptrs. destruct (sameblock _ _); apply andp_right; auto; apply valid_pointer_weak'; auto.
Qed.

Lemma prot4_rot_cmp_eq t k n :
  k = nullval \/ isptr k -> n = nullval \/ isptr n ->
  force_val (sem_cast tint tbool (eval_binop Oeq (tptr t) (tptr t) k n)) =
  Val.of_bool (if eq_dec k n then true else false).
Proof.
  intros [Ek|Pk] [En|Pn].
  - subst. rewrite if_true by auto.
    unfold eval_binop, sem_binary_operation', sem_cmp. simpl. rewrite !andb_false_r. reflexivity.
  - subst. destruct n; try contradiction. rewrite if_false by discriminate.
    unfold eval_binop, sem_binary_operation', sem_cmp. simpl. rewrite !andb_false_r. reflexivity.
  - subst. destruct k; try contradiction. rewrite if_false by discriminate.
    unfold eval_binop, sem_binary_operation', sem_cmp. simpl. rewrite !andb_false_r. reflexivity.
  - destruct k; try contradiction. destruct n; try contradiction.
    destruct (eq_dec (Vptr b i) (Vptr b0 i0)) as [E|NE].
    + inversion E; subst. unfold eval_binop, sem_binary_operation', sem_cmp. simpl. rewrite !andb_false_r.
      unfold sem_cmp_pp. simpl. destruct (eq_block b0 b0); [|congruence]. simpl. rewrite Ptrofs.eq_true. reflexivity.
    + unfold eval_binop, sem_binary_operation', sem_cmp. simpl. rewrite !andb_false_r.
      unfold sem_cmp_pp. simpl. destruct (eq_block b b0).
      * subst. simpl. destruct (Ptrofs.eq i i0) eqn:Ei; [|reflexivity].
        apply Ptrofs.same_if_eq in Ei. subst. congruence.
      * reflexivity.
Qed.

Lemma prot4_rot_cmp_ne t k :
  k = nullval \/ isptr k -> eval_binop Cop.One (tptr t) (tptr t) k k = Vint Int.zero.
Proof.
  intros [Ek|Pk].
  - subst. unfold eval_binop, sem_binary_operation', sem_cmp. simpl. rewrite !andb_false_r. reflexivity.
  - destruct k; try contradiction.
    unfold eval_binop, sem_binary_operation', sem_cmp. simpl. rewrite !andb_false_r.
    unfold sem_cmp_pp. simpl. destruct (eq_block b b); [|congruence]. simpl. rewrite Ptrofs.eq_true. reflexivity.
Qed.
