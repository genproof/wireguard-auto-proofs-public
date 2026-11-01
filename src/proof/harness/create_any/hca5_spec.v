(* law create_any, the law's own
   piece interface over the shared layers v4.
   main is the only function of the harness unit outside common.h; common.h's functions are hc4_G_create_any
   (the common4 layer, hc4_prog.v: v4 specifications with exact refcount_t warnings where they exist, else
   hc_specs3.v's), proved by the common4 piece of the owner.  main's body is proved in the world
   compspecs W_create_any with the imports of common.h's functions (hc4_imports at CSw := W_create_any: the
   environment, libc, the lower pieces' interfaces, the protocol piece v4 prot_G4) and common.h's functions.
   The unit, main's specification and the post are v1's (hca3_spec.v: they only depend on the contract). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Export WgNoise.proof.harness.create_any.hca3_spec.
Require WgNoise.contracts.x_create_any.
Require WgNoise.harness.x_create_any.code.

Section Piece.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Definition hca5_imports (cs: compspecs) : funspecs :=
  hc4_imports x25519 aead_enc aead_dec xaead_enc xaead_dec W_create_any cs ++
  hc4_G_create_any x25519 aead_enc aead_dec W_create_any.

End Piece.
