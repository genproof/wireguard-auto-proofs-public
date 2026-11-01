(* the STATEMENTS of the shared v4 pieces as
   Props, so that a law can be proved from them (`<law>_from4 : prot4_piece_stmt -> hc4_piece_stmt_<law> -> ...`)
   while their proofs are still being completed: protocol_piece4 (prot_piece4.v) proves prot4_piece_stmt,
   hc4_piece_<law> (hc4_bodies.v) proves hc4_piece_stmt_<law>. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require WgNoise.proof.protocol.prot_piece3.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.common4.hc4_cs.

Definition prot4_piece_stmt : Prop :=
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  map fst (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw) =
    WgNoise.proof.protocol.prot_piece3.protocol_idents3 /\
  piece_ok [u_noise; u_cookie; u_shim]
    (prot_imports4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
    (prot_G4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw).

Definition hc4_piece_stmt (u: unit_ctx)
  (G: (list byte -> list byte -> list byte) -> (list byte -> Z -> list byte -> list byte -> list byte) ->
      (list byte -> Z -> list byte -> list byte -> option (list byte)) -> compspecs -> funspecs) : Prop :=
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec -> cspecs_sub CS4 CSw ->
  piece_ok [u] (hc4_imports x25519 aead_enc aead_dec xaead_enc xaead_dec CSw) (G x25519 aead_enc aead_dec CSw).

Definition hc4_piece_stmt_config_any := hc4_piece_stmt u_h4_config_any hc4_G_config_any.
Definition hc4_piece_stmt_consume_initiation_any :=
  hc4_piece_stmt u_h4_consume_initiation_any hc4_G_consume_initiation_any.
Definition hc4_piece_stmt_consume_response_any :=
  hc4_piece_stmt u_h4_consume_response_any hc4_G_consume_response_any.
Definition hc4_piece_stmt_cookie_mac := hc4_piece_stmt u_h4_cookie_mac hc4_G_cookie_mac.
Definition hc4_piece_stmt_cookie_reply := hc4_piece_stmt u_h4_cookie_reply hc4_G_cookie_reply.
Definition hc4_piece_stmt_create_any := hc4_piece_stmt u_h4_create_any hc4_G_create_any.
Definition hc4_piece_stmt_handshake_clear := hc4_piece_stmt u_h4_handshake_clear hc4_G_handshake_clear.
Definition hc4_piece_stmt_handshake_receive := hc4_piece_stmt u_h4_handshake_receive hc4_G_handshake_receive.
Definition hc4_piece_stmt_keypairs := hc4_piece_stmt u_h4_keypairs hc4_G_keypairs.
