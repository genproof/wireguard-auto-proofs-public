(* port of v3's prot_body3_shim_table2.v to the v4 specifications (prot_specs4.v,
   context Gprot4: refcount_t warnings exact). v3 text follows. *)
(* Body proofs of the protocol piece, group shim_table2.
   Target: prot4_shim_bodies_table2.  Prove each function's body against its specification (prot_specs3.v) in the
   compspecs of its unit, with the context Gprot4 (prot_prog3.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.
Require Import WgNoise.proof.protocol4.prot4_shim_table2_replace.
Require Import WgNoise.proof.protocol4.prot4_shim_table2_ilookup.
Require Import WgNoise.proof.protocol4.prot4_shim_table2_pklookup.

Theorem prot4_shim_bodies_table2 :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body (QPvarspecs Shim.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_index_hashtable_replace wg_index_hashtable_replace_spec) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_index_hashtable_lookup wg_index_hashtable_lookup_spec) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_pubkey_hashtable_lookup wg_pubkey_hashtable_lookup_spec).
Proof.
  intros. split; [|split].
  - apply prot4_shim_table2_body_replace.
  - apply prot4_shim_table2_body_ilookup.
  - apply prot4_shim_table2_body_pklookup.
Qed.
