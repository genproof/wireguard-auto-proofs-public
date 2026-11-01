(* main's piece. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.harness.transport_keepalive.hka5_spec.
Require WgNoise.proof.harness.transport_keepalive.hka5_main.

#[local] Existing Instance W_transport_keepalive.

Theorem hka5_piece : piece_ok [u_hka5] hka5_imports hka5_G.
Proof.
  split; [vm_compute; repeat constructor; simpl; intuition discriminate |].
  constructor; [| constructor].
  exists u_hka5; split; [left; reflexivity |]. eexists; split; [reflexivity |].
  exact hka5_main.hka5_main_body.
Qed.
