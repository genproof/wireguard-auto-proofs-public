(* law create_any: the law's own piece = main's body over the shared layers v4. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.harness.create_any.hca3_model.
Require Import WgNoise.proof.harness.create_any.hca5_spec.
Require Import WgNoise.proof.harness.create_any.hca5_defs.
Require Import WgNoise.proof.harness.create_any.hca5_main.

(* the unit's projections, by explicit reduction (a plain reflexivity / change makes the unifier and the kernel
   unfold QPvarspecs: > 600 s) *)
Lemma hca5_piece_V : u_V u_hca3 = hca5_V.
Proof. unfold u_hca3, hca5_V. cbn [u_V]. reflexivity. Qed.
Lemma hca5_piece_cs : u_cs u_hca3 = W_create_any.
Proof. unfold u_hca3. cbn [u_cs]. reflexivity. Qed.

Theorem hca5_piece :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec,
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  hca3_init_agree x25519 aead_enc -> hca3_resp_agree x25519 aead_enc ->
  piece_ok [u_hca3] (hca5_imports x25519 aead_enc aead_dec xaead_enc xaead_dec) hca3_G.
Proof.
  intros x25519 aead_enc aead_dec xaead_enc xaead_dec Hx Ha Hxa Hi Hr. split.
  - unfold hca3_G, hca3_main_spec. cbn [map fst]. constructor; [intros [] | constructor].
  - constructor; [| constructor].
    exists u_hca3. split; [left; reflexivity |].
    exists WgNoise.harness.x_create_any.code.f_main. split; [reflexivity |].
    pose proof (@hca5_main_body x25519 aead_enc aead_dec xaead_enc xaead_dec
                  (conj Hx (conj Ha (conj Hxa (conj Hi Hr))))) as M.
    unfold hca5_Gprog in M. cbn [fst].
    rewrite hca5_piece_V, hca5_piece_cs. exact M.
Qed.
