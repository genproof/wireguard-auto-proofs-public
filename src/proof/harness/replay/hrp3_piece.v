(* law replay: the law's own piece (main and copy_init of harness/replay.c) in its unit u_hrp3, from
   the bodies proved against small contexts (hrp3_main.v, hrp3_copy.v), lifted with hrp3_lift.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_prog3.
Require Import WgNoise.proof.harness.common.hc_prog3.
Require Import WgNoise.proof.harness.replay.hrp3_spec.
Require Import WgNoise.proof.harness.replay.hrp3_defs.
Require Import WgNoise.proof.harness.replay.hrp3_lift.
Require Import WgNoise.proof.harness.replay.hrp3_copy.
Require Import WgNoise.proof.harness.replay.hrp3_main.
Require WgNoise.harness.x_replay.code.

Ltac hrp3_gsub :=
  repeat (apply Forall_cons; [eexists; split; [reflexivity | apply funspec_sub_refl] |]); apply Forall_nil.

Theorem hrp3_piece :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec,
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  piece_ok [u_hrp3] (hrp3_imports x25519 aead_enc aead_dec xaead_enc xaead_dec) hrp3_G.
Proof.
  intros x25519 aead_enc aead_dec xaead_enc xaead_dec Hx Ha Hxa.
  split; [apply compute_list_norepet_e; reflexivity |].
  constructor; [| constructor; [| constructor]].
  - exists u_hrp3; split; [left; reflexivity |].
    refine (hrp3l_lift _ _ _ _ _ _ _ hrp3_copy_init_body _ _ _ _ _).
    + reflexivity.
    + apply cspecs_sub_refl.
    + constructor.
    + hrp3_gsub.
    + constructor.
  - exists u_hrp3; split; [left; reflexivity |].
    refine (hrp3l_lift _ _ _ _ _ _ _ (hrp3_main_body x25519 aead_enc aead_dec Hx Ha) _ _ _ _ _).
    + reflexivity.
    + apply cspecs_sub_refl.
    + repeat constructor.
    + unfold hrp3_G0. hrp3_gsub.
    + unfold hrp3l_Vsub, hrp3_V0, hrp3_V.
      repeat (apply Forall_cons; [split; reflexivity |]); apply Forall_nil.
Qed.
