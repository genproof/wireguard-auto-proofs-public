(* the function-specification contexts of the BLAKE2s piece for the new interface (b2s_spec3.v):
   blake2s_imports3 / blake2s_G3, i.e. b2s_prog.v with blake2s_update_spec3 and blake2s_spec3 (chunk length
   <= PTRDIFF_MAX).  Shared by the body-proof files b2s_*3.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Export WgNoise.proof.libc.spec.
Require Export WgNoise.proof.blake2s.spec.
Require Export WgNoise.proof.blake2s.b2s_spec3.

(* the context of a body proof in the unit blake2s (lib/crypto/blake2s.c) *)
Definition b2s_Gprog3 : funspecs := blake2s_imports3 Blake2s.CS ++ blake2s_G3.

(* the context of a body proof in the unit cookie (the blake2s.h inlines, cookie.c's copies) *)
Definition b2s_Gprog3_cookie : funspecs := blake2s_imports3 Cookie.CS ++ blake2s_G3.
