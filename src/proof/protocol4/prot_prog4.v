(* the context of the protocol piece v4's body proofs = prot_prog3.v with
   the specifications of prot_specs4.v (exact refcount_t warnings).  The imports are v3's (prot_imports3: the
   lower pieces do not touch the shim), referred to without importing prot_prog3 (whose Export of prot_specs3
   would clash with prot_specs4's names). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import QuickProof.Env.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require WgNoise.proof.protocol.prot_prog3.
Require Export WgNoise.proof.protocol.prot_dec3.
Require Export WgNoise.proof.protocol.prot_model3.
Require Export WgNoise.proof.protocol.prot_repr3.
Require Export WgNoise.proof.protocol4.prot_repr4.
Require Export WgNoise.proof.protocol4.prot_model4.
Require Export WgNoise.proof.protocol4.prot_specs4.
Require Export WgNoise.proof.protocol.prot_cs.

Section Prog.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

Definition prot_imports4 (cs: compspecs) : funspecs :=
  WgNoise.proof.protocol.prot_prog3.prot_imports3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw cs.

Definition prot_G4 : funspecs := prot_G_list x25519 aead_enc aead_dec xaead_enc xaead_dec CSw.

(* the function context of a body proof in unit u *)
Definition Gprot4 (cs: compspecs) : funspecs := prot_imports4 cs ++ prot_G4.

End Prog.
