(* law consume_response_any: the law's own piece
   interface.  main is the only function of the
   harness unit outside common.h; the common.h functions are hc4_G_consume_response_any (common4, piece
   hc4_piece_consume_response_any by the common4 owner).  main's body is proved in the world compspecs
   W_consume_response_any; its imports are everything common.h's functions import (hc4_imports at CSw := W: the
   environment, libc, the lower pieces' interfaces, the protocol piece prot_G4) and the common.h functions.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require WgNoise.contracts.x_consume_response_any.
Require WgNoise.harness.x_consume_response_any.code.

(* the varspecs of the WHOLE program (literal): main_pre describes every global (VST's main_pre_InitGpred needs
   each of them in main's glob_types) *)
Definition hcr5_V : varspecs :=
  ltac:(let x := eval vm_compute in (QPvarspecs WgNoise.contracts.x_consume_response_any.whole_prog) in exact x).

(* the harness unit, in the world compspecs, with the whole program's varspecs *)
Definition u_hcr5 : unit_ctx :=
  mk_unit W_consume_response_any hcr5_V WgNoise.harness.x_consume_response_any.code.prog.

Definition hcr5_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition hcr5_main_spec : ident * funspec :=
  (WgNoise.harness.x_consume_response_any.code._main,
   QPmain_spec_ext' WgNoise.contracts.x_consume_response_any.whole_prog tt hcr5_post).

Section Piece.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Definition hcr5_imports (cs: compspecs) : funspecs :=
  hc4_imports x25519 aead_enc aead_dec xaead_enc xaead_dec W_consume_response_any cs ++
  hc4_G_consume_response_any x25519 aead_enc aead_dec W_consume_response_any.

End Piece.

Definition hcr5_G : funspecs := [hcr5_main_spec].
