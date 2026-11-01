(* law create_any (harness/create_any.c): the law's own piece interface.
   main is the only function of the harness unit outside common.h (whose functions are hc_G3_create_any,
   proved by hc_pieces3).  main's body is proved in the world compspecs W_create_any (wg3_worlds.v), as law
   counter's harness; its imports are everything common.h's functions import (hc_imports3 at CSw :=
   W_create_any: the environment, libc, the lower pieces' interfaces, the protocol piece prot_G3) and the
   common.h functions themselves. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.harness.common.hc_prog3.
Require WgNoise.contracts.x_create_any.
Require WgNoise.harness.x_create_any.code.

(* the harness unit, in the world compspecs *)
Definition u_hca3 : unit_ctx :=
  mk_unit W_create_any (QPvarspecs WgNoise.contracts.x_create_any.Harness.qp) WgNoise.harness.x_create_any.code.prog.

Definition hca3_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition hca3_main_spec : ident * funspec :=
  (WgNoise.harness.x_create_any.code._main,
   QPmain_spec_ext' WgNoise.contracts.x_create_any.whole_prog tt hca3_post).

Section Piece.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Definition hca3_imports (cs: compspecs) : funspecs :=
  hc_imports3 x25519 aead_enc aead_dec xaead_enc xaead_dec W_create_any cs ++
  hc_G3_create_any x25519 aead_enc aead_dec.

End Piece.

Definition hca3_G : funspecs := [hca3_main_spec].
