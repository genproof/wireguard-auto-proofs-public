(* law config_any: pure facts about the comparisons of common.h's snapshots
   (hc_model3 / hc4_model): reflexivity, and a `true` comparison gives equal snapshot VALUES (the struct values
   main's snapshots hold), so that a step can rewrite a snapshot to the current object, edit both alike and
   compare again.  Shared by the phase children. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Local Open Scope bool_scope.

Lemma hcf5_bytes_eqb_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

Lemma hcf5_bytes_eqb_eq a b : bytes_eqb a b = true -> a = b.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a b); congruence. Qed.

Lemma hcf5_veqb_refl x : veqb x x = true.
Proof. unfold veqb. destruct (eq_dec x x); congruence. Qed.

Lemma hcf5_veqb_eq x y : veqb x y = true -> x = y.
Proof. unfold veqb. destruct (eq_dec x y); congruence. Qed.

Lemma hcf5_dec_refl (x: val) : (if eq_dec x x then true else false) = true.
Proof. destruct (eq_dec x x); congruence. Qed.

Lemma hcf5_dec_eq (x y: val) : (if eq_dec x y then true else false) = true -> x = y.
Proof. destruct (eq_dec x y); congruence. Qed.

Lemma hcf5_beqb_eq a b : Bool.eqb a b = true -> a = b.
Proof. apply Bool.eqb_prop. Qed.

Ltac hcf5_refl :=
  repeat first [ rewrite Int.eq_true | rewrite Int64.eq_true | rewrite Bool.eqb_reflx | rewrite hcf5_bytes_eqb_refl
               | rewrite hcf5_veqb_refl | rewrite hcf5_dec_refl | rewrite Z.eqb_refl ];
  reflexivity.

Ltac hcf5_split_true H :=
  repeat match goal with
  | K: (_ && _) = true |- _ => apply andb_prop in K; destruct K
  end.

Ltac hcf5_to_eq :=
  repeat match goal with
  | H: Int.eq _ _ = true |- _ => apply Int.same_if_eq in H
  | H: Int64.eq _ _ = true |- _ => apply Int64.same_if_eq in H
  | H: Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in H
  | H: bytes_eqb _ _ = true |- _ => apply hcf5_bytes_eqb_eq in H
  | H: veqb _ _ = true |- _ => apply hcf5_veqb_eq in H
  | H: (if ?d then true else false) = true |- _ => destruct d; [| discriminate H]; clear H
  end.

(* ---------- handshake snapshots ---------- *)
Lemma hcf5_entry_eqb_refl E : entry_eqb E E = true.
Proof. unfold entry_eqb. hcf5_refl. Qed.

Lemma hcf5_hs_eqb_refl H : hs_eqb H H = true.
Proof. unfold hs_eqb. hcf5_refl. Qed.

Lemma hcf5_snap_eqb_refl s : snap_eqb s s = true.
Proof. unfold snap_eqb. rewrite hcf5_entry_eqb_refl, hcf5_hs_eqb_refl. hcf5_refl. Qed.

Lemma hcf5_snap_eqb_eq s c : snap_eqb s c = true -> s = c.
Proof.
  destruct s as [[e1 t1 i1] n1 h1 [a1 b1 c1 d1 e1' f1 g1 k1 l1 m1 o1 q1]],
           c as [[e2 t2 i2] n2 h2 [a2 b2 c2 d2 e2' f2 g2 k2 l2 m2 o2 q2]].
  unfold snap_eqb, entry_eqb, hs_eqb; simpl. intros H. hcf5_split_true H. hcf5_to_eq. subst. reflexivity.
Qed.

(* ---------- cookies, peers ---------- *)
Lemma hcf5_cookie_eqb_refl C : cookie_eqb C C = true.
Proof. unfold cookie_eqb. hcf5_refl. Qed.

Lemma hcf5_cookie_eqb_eq C1 C2 : cookie_eqb C1 C2 = true -> C1 = C2.
Proof.
  destruct C1, C2. unfold cookie_eqb; simpl. intros H. hcf5_split_true H. hcf5_to_eq. subst. reflexivity.
Qed.

Lemma hcf5_pr_eqb_refl P : pr_eqb P P = true.
Proof. unfold pr_eqb, pr_eqb_nc. rewrite hcf5_cookie_eqb_refl. hcf5_refl. Qed.

(* pr_same compares every field of the snapshot (the handshake and the reference count are not in it) *)
Lemma hcf5_pr_eqb_val P0 P : pr_eqb P0 P = true -> prsnap_val P0 = prsnap_val P.
Proof.
  destruct P0, P. unfold pr_eqb, pr_eqb_nc; simpl. intros H. hcf5_split_true H.
  match goal with K: cookie_eqb _ _ = true |- _ => apply hcf5_cookie_eqb_eq in K end. hcf5_to_eq. subst.
  reflexivity.
Qed.

(* ---------- devices ---------- *)
Lemma hcf5_dev_eqb_refl D h : dev_eqb D h D h = true.
Proof. unfold dev_eqb. hcf5_refl. Qed.

Lemma hcf5_dev_eqb_eq D0 h0 D h : dev_eqb D0 h0 D h = true -> D0 = D /\ h0 = h.
Proof.
  destruct D0 as [d0 [pu0 pr0 ha0] [s0 e0 m0 b0 c0] pt0 it0], D as [d [pu pr ha] [s e m b c] pt it].
  unfold dev_eqb; simpl. intros H. hcf5_split_true H. hcf5_to_eq. subst. auto.
Qed.

(* ---------- the shim ---------- *)
Lemma hcf5_shim_eqb_refl S w : shim_eqb S w S w = true.
Proof. unfold shim_eqb, warn_eqb. simpl. hcf5_refl. Qed.

Lemma hcf5_shim_eqb_val S0 w0 S w : Zlength w0 = 5 -> Zlength w = 5 -> shim_eqb S0 w0 S w = true ->
  shimsnap_val S0 w0 = shimsnap_val S w.
Proof.
  intros L0 L H. destruct S0, S. unfold shim_eqb, warn_eqb in H; simpl in H. hcf5_split_true H. hcf5_to_eq.
  unfold shimsnap_val; simpl. subst. f_equal; f_equal; f_equal; f_equal; f_equal.
  do 5 (destruct w0 as [|? w0]; [rewrite Zlength_nil in L0; lia | rewrite Zlength_cons in L0]).
  do 5 (destruct w as [|? w]; [rewrite Zlength_nil in L; lia | rewrite Zlength_cons in L]).
  destruct w0; [| rewrite Zlength_cons in L0; pose proof (Zlength_nonneg w0); lia].
  destruct w; [| rewrite Zlength_cons in L; pose proof (Zlength_nonneg w); lia].
  cbv [Znth Z.ltb Z.compare nth Z.to_nat Pos.to_nat] in *. simpl in *. subst. reflexivity.
Qed.

(* ---------- kents ---------- *)
Lemma hcf5_symkey_eqb_refl K : symkey_eqb K K = true.
Proof. unfold symkey_eqb. hcf5_refl. Qed.

Lemma hcf5_int64s_eqb_refl l : int64s_eqb l l = true.
Proof. induction l; simpl; [reflexivity |]. rewrite Int64.eq_true, IHl. reflexivity. Qed.

Lemma hcf5_kp_eqb_refl K : kp_eqb K K = true.
Proof. unfold kp_eqb. rewrite !hcf5_symkey_eqb_refl, hcf5_int64s_eqb_refl. hcf5_refl. Qed.

(* a kent right after kents_snap compares equal *)
Lemma hcf5_kent_same_snapped T e : kent_same T (kent_snapped T e) = true.
Proof.
  unfold kent_same, kent_snapped, kent_eqb_cur, kent_eqb_nn; simpl.
  rewrite hcf5_entry_eqb_refl, Bool.eqb_reflx, hcf5_kp_eqb_refl, hcf5_veqb_refl. reflexivity.
Qed.

Lemma hcf5_kents_same_snapped T KE : forallb (kent_same T) (map (kent_snapped T) KE) = true.
Proof. induction KE; simpl; [reflexivity |]. rewrite hcf5_kent_same_snapped, IHKE. reflexivity. Qed.
