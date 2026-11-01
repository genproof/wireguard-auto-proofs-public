(* The limb operations of the model as operations of fiat-crypto's prime field F p (p = 2^255 - 19).
   This is the first file that loads both the WireGuard model (VST/CompCert) and fiat-crypto. *)
From Coq Require Import NArith.
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.x25519.x25519_model.
Require Import X25519.Limbs X25519.MulSqr X25519.Freeze X25519.Bytes.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Crypto.Spec.Curve25519.

Local Open Scope Z_scope.

Definition pP : positive := (2 ^ 255 - 19)%positive.
Notation Fp := (F.F pP).

Lemma pP_P25519 : Z.pos pP = P25519.
Proof. vm_compute. reflexivity. Qed.

Add Ring Fp_ring : (F.ring_theory pP)
  (morphism (F.ring_morph pP), constants [F.is_constant], div (F.morph_div_theory pP),
   power_tac (F.power_theory pP) [F.is_pow_constant]).

(* the field element a list of limbs denotes *)
Definition fe (h: list int) : Fp := F.of_Z pP (feval h).

Lemma fe_mod (a b: Z) : a mod P25519 = b mod P25519 -> F.of_Z pP a = F.of_Z pP b.
Proof. intros. apply F.eq_of_Z_iff. rewrite pP_P25519. assumption. Qed.

Lemma fe_add f g : bounded tight f -> bounded tight g ->
  bounded loose (fe_add_m f g) /\ fe (fe_add_m f g) = F.add (fe f) (fe g).
Proof.
  intros Hf Hg. destruct (fe_add_ok f g Hf Hg) as [B E]. split; [exact B|].
  unfold fe. rewrite E. apply F.of_Z_add.
Qed.

Lemma fe_sub f g : bounded tight f -> bounded tight g ->
  bounded loose (fe_sub_m f g) /\ fe (fe_sub_m f g) = F.sub (fe f) (fe g).
Proof.
  intros Hf Hg. destruct (fe_sub_ok f g Hf Hg) as [B E]. split; [exact B|].
  unfold fe. rewrite E. rewrite <- F.of_Z_sub. apply fe_mod.
  replace (2 * P25519 + feval f - feval g) with (feval f - feval g + 2 * P25519) by ring.
  apply Z_mod_plus_full.
Qed.

Lemma fe_mul f g : bounded loose f -> bounded loose g ->
  bounded tight (fe_mul_m f g) /\ fe (fe_mul_m f g) = F.mul (fe f) (fe g).
Proof.
  intros Hf Hg. destruct (fe_mul_ok f g Hf Hg) as [B E]. split; [exact B|].
  unfold fe. rewrite <- F.of_Z_mul. apply fe_mod. exact E.
Qed.

Lemma fe_sqr f : bounded loose f ->
  bounded tight (fe_sqr_m f) /\ fe (fe_sqr_m f) = F.mul (fe f) (fe f).
Proof.
  intros Hf. destruct (fe_sqr_ok f Hf) as [B E]. split; [exact B|].
  unfold fe. rewrite <- F.of_Z_mul. apply fe_mod. exact E.
Qed.

Lemma fe_mul121666 f : bounded loose f ->
  bounded tight (fe_mul121666_m f) /\ fe (fe_mul121666_m f) = F.mul (fe f) (F.of_Z pP 121666).
Proof.
  intros Hf. destruct (fe_mul121666_ok f Hf) as [B E]. split; [exact B|].
  unfold fe. rewrite <- F.of_Z_mul. apply fe_mod. exact E.
Qed.

(* ------------------------------------------------------------------ *)
(* inversion: the C's addition chain computes z^(p-2)                  *)
(* ------------------------------------------------------------------ *)

Definition inv_chain {A} (sqr: A -> A) (mul: A -> A -> A) (sqn: nat -> A -> A) (z: A) : A :=
  let t0 := sqr z in
  let t1 := sqr t0 in
  let t1 := sqn 1%nat t1 in
  let t1 := mul z t1 in
  let t0 := mul t0 t1 in
  let t2 := sqr t0 in
  let t1 := mul t1 t2 in
  let t2 := sqr t1 in
  let t2 := sqn 4%nat t2 in
  let t1 := mul t2 t1 in
  let t2 := sqr t1 in
  let t2 := sqn 9%nat t2 in
  let t2 := mul t2 t1 in
  let t3 := sqr t2 in
  let t3 := sqn 19%nat t3 in
  let t2 := mul t3 t2 in
  let t2 := sqr t2 in
  let t2 := sqn 9%nat t2 in
  let t1 := mul t2 t1 in
  let t2 := sqr t1 in
  let t2 := sqn 49%nat t2 in
  let t2 := mul t2 t1 in
  let t3 := sqr t2 in
  let t3 := sqn 99%nat t3 in
  let t2 := mul t3 t2 in
  let t2 := sqr t2 in
  let t2 := sqn 49%nat t2 in
  let t1 := mul t2 t1 in
  let t1 := sqr t1 in
  let t1 := sqn 4%nat t1 in
  mul t1 t0.

Lemma fe_loose_invert_m_chain z : fe_loose_invert_m z = inv_chain fe_sqr_m fe_mul_m fe_sqn_m z.
Proof. reflexivity. Qed.

Section Hom.
  Context {A B: Type} (P: A -> Prop) (h: A -> B)
          (sqrA: A -> A) (mulA: A -> A -> A) (sqnA: nat -> A -> A)
          (sqrB: B -> B) (mulB: B -> B -> B) (sqnB: nat -> B -> B)
          (Hs: forall a, P a -> P (sqrA a) /\ h (sqrA a) = sqrB (h a))
          (Hm: forall a b, P a -> P b -> P (mulA a b) /\ h (mulA a b) = mulB (h a) (h b))
          (Hn: forall n a, P a -> P (sqnA n a) /\ h (sqnA n a) = sqnB n (h a)).

  Lemma hs a b : P a /\ h a = b -> P (sqrA a) /\ h (sqrA a) = sqrB b.
  Proof. intros [Pa <-]. apply Hs, Pa. Qed.
  Lemma hm a b a' b' : P a /\ h a = a' -> P b /\ h b = b' -> P (mulA a b) /\ h (mulA a b) = mulB a' b'.
  Proof. intros [Pa <-] [Pb <-]. apply Hm; assumption. Qed.
  Lemma hn n a b : P a /\ h a = b -> P (sqnA n a) /\ h (sqnA n a) = sqnB n b.
  Proof. intros [Pa <-]. apply Hn, Pa. Qed.

  Lemma inv_chain_hom z : P z ->
    P (inv_chain sqrA mulA sqnA z) /\ h (inv_chain sqrA mulA sqnA z) = inv_chain sqrB mulB sqnB (h z).
  Proof.
    intros Pz. assert (H0: P z /\ h z = h z) by (split; [exact Pz | reflexivity]).
    unfold inv_chain. cbv zeta.
    let rec go t :=
      lazymatch t with
      | sqrA ?a => let H := go a in constr:(hs _ _ H)
      | mulA ?a ?b => let Ha := go a in let Hb := go b in constr:(hm _ _ _ _ Ha Hb)
      | sqnA ?n ?a => let H := go a in constr:(hn n _ _ H)
      | z => constr:(H0)
      end in
    lazymatch goal with |- P ?t /\ _ => let pf := go t in exact pf end.
  Qed.
End Hom.

Lemma fe_sqn n f : bounded tight f ->
  bounded tight (fe_sqn_m n f) /\ fe (fe_sqn_m n f) = Nat.iter n (fun y => F.mul y y) (fe f).
Proof.
  intros Hf. induction n as [|n [IHb IHe]]; [split; [exact Hf | reflexivity]|].
  unfold fe_sqn_m in *. rewrite !Nat.iter_succ. destruct (fe_sqr _ (tight_loose _ IHb)) as [B E].
  split; [exact B|]. rewrite E, IHe. reflexivity.
Qed.

Lemma fe_invert_pow z : bounded tight z ->
  bounded tight (fe_invert_m z) /\
  fe (fe_invert_m z) = inv_chain (fun y => F.mul y y) F.mul (fun n => Nat.iter n (fun y => F.mul y y)) (fe z).
Proof.
  intros Hz. unfold fe_invert_m. rewrite fe_loose_invert_m_chain.
  apply (inv_chain_hom (bounded tight) fe); auto.
  - intros a Ha. apply fe_sqr, tight_loose, Ha.
  - intros a b Ha Hb. apply fe_mul; apply tight_loose; assumption.
  - intros n a Ha. apply fe_sqn, Ha.
Qed.

Local Open Scope F_scope.

Lemma iter_sq_pow (x: Fp) (e: N) n :
  Nat.iter n (fun y => F.mul y y) (F.pow x e) = F.pow x (e * 2 ^ N.of_nat n)%N.
Proof.
  induction n as [|n IH].
  - cbn [Nat.iter]. rewrite N.pow_0_r, N.mul_1_r. reflexivity.
  - rewrite Nat.iter_succ, IH, <- F.pow_add_r. f_equal.
    rewrite Nat2N.inj_succ, N.pow_succ_r'. ring.
Qed.

Lemma inv_chain_exp (x: Fp) :
  inv_chain (fun y => F.mul y y) F.mul (fun n => Nat.iter n (fun y => F.mul y y)) (F.pow x 1%N) =
  F.pow x (inv_chain (fun e => e + e)%N N.add (fun n e => e * 2 ^ N.of_nat n)%N 1%N).
Proof.
  symmetry. apply (proj2 (inv_chain_hom (fun _ => True) (fun e => F.pow x e)
                  (fun e => e + e)%N N.add (fun n e => e * 2 ^ N.of_nat n)%N
                  (fun y => F.mul y y) F.mul (fun n => Nat.iter n (fun y => F.mul y y))
                  ltac:(intros; split; [exact I | apply F.pow_add_r])
                  ltac:(intros; split; [exact I | apply F.pow_add_r])
                  ltac:(intros; split; [exact I | symmetry; apply iter_sq_pow])
                  1%N I)).
Qed.

Lemma inv_chain_exp_value :
  inv_chain (fun e => e + e)%N N.add (fun n e => e * 2 ^ N.of_nat n)%N 1%N = Z.to_N (Z.pos pP - 2).
Proof. vm_compute. reflexivity. Qed.

Lemma fe_invert z : bounded tight z ->
  bounded tight (fe_invert_m z) /\ fe (fe_invert_m z) = F.inv (fe z).
Proof.
  intros Hz. destruct (fe_invert_pow z Hz) as [B E]. split; [exact B|]. rewrite E.
  rewrite <- (F.pow_1_r (fe z)) at 1. rewrite inv_chain_exp, inv_chain_exp_value.
  symmetry. apply (@F.Fq_inv_fermat pP Curve25519.prime_p). vm_compute. reflexivity.
Qed.
