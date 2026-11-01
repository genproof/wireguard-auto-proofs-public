(* law handshake (harness/handshake.c): the law's own piece interface.
   main is the only function of the harness unit outside common.h (whose functions are hc_G3_handshake,
   proved by hc_pieces3).  main's body is proved in the world compspecs W_handshake (wg3_worlds.v); its
   imports are everything common.h's functions import (hc_imports3 at CSw := W_handshake: the environment,
   libc, the lower pieces' interfaces, the protocol piece prot_G3) and the common.h functions themselves.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.harness.common.hc_prog3.
Require WgNoise.contracts.x_handshake.
Require WgNoise.harness.x_handshake.code.

(* the varspecs of the WHOLE program (literal): main_pre describes every global (VST's main_pre_InitGpred needs
   each of them in main's glob_types), among them noise.c's, cookie.c's, the shim's and the primitives' *)
Definition hhs3_V : varspecs :=
  ltac:(let x := eval vm_compute in (QPvarspecs WgNoise.contracts.x_handshake.whole_prog) in exact x).

(* the harness unit, in the world compspecs, with the whole program's varspecs *)
Definition u_hhs3 : unit_ctx := mk_unit W_handshake hhs3_V WgNoise.harness.x_handshake.code.prog.

Definition hhs3_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition hhs3_main_spec : ident * funspec :=
  (WgNoise.harness.x_handshake.code._main,
   QPmain_spec_ext' WgNoise.contracts.x_handshake.whole_prog tt hhs3_post).

Section Piece.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* hc_imports3 has no nondet_size (env_specs_ns): this program has none *)
Definition hhs3_imports (cs: compspecs) : funspecs :=
  hc_imports3 x25519 aead_enc aead_dec xaead_enc xaead_dec W_handshake cs ++
  hc_G3_handshake x25519 aead_enc aead_dec.

End Piece.

Definition hhs3_G : funspecs := [hhs3_main_spec].

(* the property of X25519 the law relies on (the harness compares the two sides unconditionally:
   B's decrypted timestamp = A's, B's transport keys = those from A's chaining key): curve25519_generic
   clamps its copy of the scalar, and X25519 commutes on multiples of the base point for 32-byte scalars
   (interfaces v3: x25519_clamp_inv /\ x25519_dh_agree of wg3_iface3.v) *)
Definition hhs3_comm (x25519: list byte -> list byte -> list byte) : Prop :=
  (forall s p, x25519 (clamp s) p = x25519 s p) /\
  (forall a b, Zlength a = 32 -> Zlength b = 32 -> x25519 a (x25519 b basepoint9) = x25519 b (x25519 a basepoint9)).
