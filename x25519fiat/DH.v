From Coq Require Import ZArith.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Algebra.Hierarchy Crypto.Algebra.ScalarMult.
Require Import Crypto.Spec.MontgomeryCurve Crypto.Curves.Montgomery.AffineInstances.
Require Import Crypto.Curves.Montgomery.XZ Crypto.Curves.Montgomery.XZProofs.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Util.Decidable.

About XZProofs.M.montladder_correct.
About AffineInstances.M.MontgomeryWeierstrassIsomorphism.
About ScalarMult.scalarmult_assoc.

Local Open Scope F_scope.

Lemma char_ge_12 : @Ring.char_ge (F p) eq F.zero F.one F.opp F.add F.sub F.mul 12.
Proof. eapply Hierarchy.char_ge_weaken; try apply ModularArithmeticTheorems.F.char_gt; Decidable.vm_decide. Qed.
Lemma char_ge_28 : @Ring.char_ge (F p) eq F.zero F.one F.opp F.add F.sub F.mul 28.
Proof. eapply Hierarchy.char_ge_weaken; try apply ModularArithmeticTheorems.F.char_gt; Decidable.vm_decide. Qed.

Lemma disc_nz : F.sub (F.mul M.a M.a) (F.add (F.add (F.add F.one F.one) F.one) F.one) <> F.zero.
Proof. Decidable.vm_decide. Qed.

Definition group :=
  (let (_, h, _, _) := @AffineInstances.M.MontgomeryWeierstrassIsomorphism
       (F p) eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div Curve25519.field _
       M.a M.b M.b_nonzero disc_nz Curve25519.char_ge_3 char_ge_12 char_ge_28 in h).

Lemma X0_proper P Q : MontgomeryCurve.M.eq P Q -> M.X0 P = M.X0 Q.
Proof.
  destruct P as [[[x y]|[]] HP], Q as [[[x' y']|[]] HQ];
    cbv [MontgomeryCurve.M.eq M.X0 MontgomeryCurve.M.X0 MontgomeryCurve.M.coordinates];
    intuition.
Qed.

Lemma dh_agree (a b : Z) :
  M.X0 (M.scalarmult a (M.scalarmult b M.B)) = M.X0 (M.scalarmult b (M.scalarmult a M.B)).
Proof.
  apply X0_proper.
  pose proof (@Hierarchy.commutative_group_group _ _ _ _ _ group) as G.
  cbv [M.scalarmult].
  rewrite !(@ScalarMult.scalarmult_assoc _ _ _ _ _ G _ (@ScalarMult.scalarmult_ref_is_scalarmult _ _ _ _ _ G)).
  rewrite Z.mul_comm; reflexivity.
Qed.
Print Assumptions dh_agree.
Print Assumptions XZProofs.M.montladder_correct.
