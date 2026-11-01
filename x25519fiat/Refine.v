(* x25519_m (the transliteration of the kernel's curve25519_generic that the VST proofs tie to the C) is
   RFC 7748's X25519 as fiat-crypto specifies it:

     x25519_m s u = enc (M.montladder 255 (Z.testbit (scalar_of (clamp s))) (dec u))

   over F p, where enc x is the 32 little-endian bytes of the canonical value of x, dec u the field element
   fe_frombytes_m reads (top bit ignored), and scalar_of the little-endian integer of the (clamped) scalar. *)
From Coq Require Import NArith.
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.prims.prim_api WgNoise.proof.x25519.x25519_model.
Require Import X25519.Limbs X25519.MulSqr X25519.Freeze X25519.Bytes X25519.Scalar X25519.FeF X25519.Ladder.
Require X25519.DH.
Require Import Crypto.Spec.ModularArithmetic Crypto.Arithmetic.PrimeFieldTheorems.
Require Crypto.Spec.Curve25519 Crypto.Spec.MontgomeryCurve.
Require Crypto.Curves.Montgomery.XZ Crypto.Curves.Montgomery.XZProofs.

Local Open Scope Z_scope.

Definition ML (tb: Z -> bool) (x: Fp) : Fp :=
  @XZ.M.montladder Fp F.zero F.one F.add F.sub F.mul F.inv Curve25519.M.a24 255 tb x.
Definition enc (x: Fp) : list byte := le_bytes (F.to_Z x).
Definition dec (u: list byte) : Fp := fe (fe_frombytes_m u).

Lemma P25519_pos : 0 < P25519.
Proof. unfold P25519. lia. Qed.

Lemma fe_tobytes_enc h : bounded tight h -> fe_tobytes_m h = enc (fe h).
Proof.
  intros H. rewrite fe_tobytes_m_limbs, fe_freeze_ok by assumption.
  unfold enc, fe. rewrite F.to_Z_of_Z, pP_P25519.
  apply limbs_to_bytes_canon.
  pose proof (Z.mod_pos_bound (feval h) P25519 P25519_pos). unfold P25519 in *. lia.
Qed.

Lemma dec_enc x : dec (enc x) = x.
Proof.
  unfold dec, enc, fe. pose proof (F.to_Z_range x ltac:(reflexivity)) as R.
  rewrite pP_P25519 in R.
  rewrite frombytes_le_bytes by lia. rewrite feval_canon by (unfold P25519 in R; lia).
  apply F.of_Z_to_Z.
Qed.

Theorem x25519_m_refines s u : x25519_m s u = enc (ML (Z.testbit (scalar_of (clamp s))) (dec u)).
Proof.
  unfold x25519_m. cbv zeta.
  destruct (ladder_refines (clamp s) (fe_frombytes_m u) (frombytes_tight u)) as [B E].
  cbv zeta in B, E.
  rewrite (fe_tobytes_enc _ B). rewrite E. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* fiat's ladder theorem, instantiated for Curve25519                  *)
(* ------------------------------------------------------------------ *)

Lemma a24_correct :
  F.mul (F.add (F.add (F.add F.one F.one) F.one) F.one) Curve25519.M.a24 = F.sub Curve25519.M.a (F.add F.one F.one).
Proof. apply F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

Lemma a2m4_nonsquare (r: Fp) :
  F.mul r r <> F.sub (F.mul Curve25519.M.a Curve25519.M.a) (F.add (F.add (F.add F.one F.one) F.one) F.one).
Proof.
  intros H. apply Curve25519.M.a2m4_nonsq. exists r. etransitivity; [exact H|].
  apply F.eq_to_Z_iff. vm_compute. reflexivity.
Qed.

Lemma inv_zero : F.inv (F.zero : Fp) = F.zero.
Proof. apply (F.inv_0 pP). Qed.

Lemma ML_X0 n (P: Curve25519.M.point) :
  ML (Z.testbit n) (Curve25519.M.X0 P) = Curve25519.M.X0 (Curve25519.M.scalarmult (n mod 2 ^ 255) P).
Proof.
  unfold ML.
  exact (@XZProofs.M.montladder_correct Fp eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div
           Curve25519.field _ X25519.DH.char_ge_28 Curve25519.char_ge_3
           Curve25519.M.a Curve25519.M.b Curve25519.M.b_nonzero Curve25519.M.a24 a24_correct
           a2m4_nonsquare inv_zero 255 ltac:(lia) n P).
Qed.

Lemma dec_basepoint9 : dec basepoint9 = Curve25519.M.X0 Curve25519.M.B.
Proof. apply F.eq_to_Z_iff. vm_compute. reflexivity. Qed.
