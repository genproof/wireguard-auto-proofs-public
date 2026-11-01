(* law cookie_mac: the law from the assembly hck5_safe_from and the law's piece hck5_piece, for
   the statements of the shared v4 pieces (common4's hc4_stmt.v: prot4_piece_stmt, proved by protocol_piece4;
   hc4_piece_stmt_cookie_mac, proved by the owner's hc4_piece_cookie_mac).  cookie_mac_safe5 applies it to the
   proved pieces. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.common.wg3_iface3.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot3c_bridge.
Require Import WgNoise.proof.harness.common.hc_bodies3.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4_stmt.
Require WgNoise.contracts.x_cookie_mac.
Require Import WgNoise.proof.harness.cookie_mac.hck5_piece.
Require Import WgNoise.proof.harness.cookie_mac.hck5_asm.

(* the common.h structs of the bodies are in the world *)
Lemma hck5_cs4_sub : cspecs_sub CS4 W_cookie_mac.
Proof. hc3_cssub. Qed.

Lemma hck5_from4 :
  prot4_piece_stmt -> hc4_piece_stmt_cookie_mac ->
  blake2s3_ok -> aead3b_ok -> x25519_ok3c ->
  harness_safe WgNoise.contracts.x_cookie_mac.whole_prog.
Proof.
  intros HP HHC B A X. apply hck5_safe_from; [exact hck5_piece | exact HP | | exact B | exact (prot3c_aead A) |].
  - intros x25519 aead_enc aead_dec xaead_enc xaead_dec Hx Ha Hxa.
    exact (HHC x25519 aead_enc aead_dec xaead_enc xaead_dec W_cookie_mac Hx Ha Hxa hck5_cs4_sub).
  - destruct (prot3c_x25519 X) as (G & x & XP & HPX & HI & HC & HCC & _ & _).
    exists G, x. tauto.
Qed.
