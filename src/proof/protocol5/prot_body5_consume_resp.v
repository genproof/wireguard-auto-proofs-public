(* The bodies of the protocol piece v5, group `consume_resp`: wg_noise_handshake_consume_response; port of prot4_cons_resp.v (resp_rep5, device_rep5, peers_rep5).
   Each function against its v5 specification (prot_specs5.v) in its unit's compspecs, with the context
   Gprot5 (prot_prog5.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require WgNoise.noise.code WgNoise.shim.code.
Require WgNoise.proof.protocol5.prot5_cons_resp.

Theorem prot_bodies5_consume_resp :
  forall x25519 aead_enc aead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_wg_noise_handshake_consume_response (wg_noise_handshake_consume_response_spec x25519 aead_dec).
Proof.
  intros x25519 aead_enc aead_dec CSw Hx Ha.
  eapply prot5_cons_resp.prot5_cons_resp_body; eauto.
Qed.
