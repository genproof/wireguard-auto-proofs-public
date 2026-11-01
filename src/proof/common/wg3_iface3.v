(* interfaces v3.

   x25519_ok3c = x25519_ok3b plus the two facts the law handshake needs about the Curve25519 function x:
   - x25519_clamp_inv: curve25519_generic clamps a copy of its scalar, so a clamped scalar gives the same result
     (proved for the concrete model);
   - x25519_dh_agree: X25519 commutes on multiples of the base point, for 32-byte scalars (a theorem:
     src/proof/x25519/x25519_dh.v, x25519_m_dh_agree, proved from fiat-crypto in x25519fiat/).
   aead3b_ok (wg3_iface2.v) is unchanged. *)
Require Import VST.floyd.proofauto.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.prims.prim_api.
Require Export WgNoise.proof.common.wg3_iface2.

Local Open Scope Z_scope.

Definition x25519_clamp_inv (x: list byte -> list byte -> list byte) : Prop :=
  forall s p, x (clamp s) p = x s p.

Definition x25519_dh_agree (x: list byte -> list byte -> list byte) : Prop :=
  forall a b, Zlength a = 32 -> Zlength b = 32 -> x a (x b basepoint9) = x b (x a basepoint9).

Definition x25519_ok3c : Prop :=
  exists (G: funspecs) (x: list byte -> list byte -> list byte),
    x25519_props x /\
    piece_ok x25519_units3 x25519_imports3 G /\
    map fst G = x25519_idents3 /\
    asm_covers G (x25519_iface3 x) /\
    cc_default_all G /\
    x25519_clamp_inv x /\
    x25519_dh_agree x.
