(* The Diffie-Hellman agreement x25519_m_dh_agree (on the base point), proved.

   src/proof/x25519/x25519_dh.v states it and takes its proof from here: a Theorem with the same statement
   (same imports, same scope), from
   - Refine.x25519_m_refines: x25519_m s u = enc (M.montladder 255 (Z.testbit (scalar_of (clamp s))) (dec u))
     (the limb-level refinement of the kernel's curve25519-fiat32 model to fiat-crypto's ladder over F p),
   - Refine.dec_enc / dec_basepoint9 (byte round trip; dec 9 is the u-coordinate of the base point),
   - fiat-crypto's M.montladder_correct (Refine.ML_X0) and the group law (DH.dh_agree). *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.x25519.x25519_model.
Require X25519.DH X25519.Refine.

Local Open Scope Z_scope.

Theorem x25519_m_dh_agree : forall a b : list byte,
  Zlength a = 32 -> Zlength b = 32 ->
  x25519_m a (x25519_m b basepoint9) = x25519_m b (x25519_m a basepoint9).
Proof.
  intros a b _ _.
  rewrite !X25519.Refine.x25519_m_refines, !X25519.Refine.dec_enc, !X25519.Refine.dec_basepoint9,
    !X25519.Refine.ML_X0.
  f_equal. apply X25519.DH.dh_agree.
Qed.

Print Assumptions x25519_m_dh_agree.
