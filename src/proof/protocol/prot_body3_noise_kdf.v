(* Body proofs of the protocol piece, group noise_kdf.
   Target: prot_bodies3_noise_kdf.  Prove each function's body against its specification (prot_specs3.v) in the
   compspecs of its unit, with the context Gprot3 (prot_prog3.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_prog3.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.
Require Import WgNoise.proof.protocol.prot3_noise_kdf_hmac.
Require Import WgNoise.proof.protocol.prot3_noise_kdf_kdf.

Theorem prot_bodies3_noise_kdf :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body (QPvarspecs Noise.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_hmac hmac_spec) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_kdf kdf_spec).
Proof.
  intros x25519 aead_enc aead_dec xaead_enc xaead_dec CSw _ _ _.
  split.
  - exact (body_hmac_fix x25519 aead_enc aead_dec xaead_enc xaead_dec CSw).
  - exact (body_kdf x25519 aead_enc aead_dec xaead_enc xaead_dec CSw).
Qed.
