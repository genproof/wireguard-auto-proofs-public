(* the harness piece of law prim_blake2s, from the body files. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.harness.prim_blake2s.hb2s_spec.
Require WgNoise.proof.harness.prim_blake2s.hb2s_small_body WgNoise.proof.harness.prim_blake2s.hb2s_compress_body
        WgNoise.proof.harness.prim_blake2s.hb2s_ref_body WgNoise.proof.harness.prim_blake2s.hb2s_main_body.

Theorem hb2s_piece : piece_ok [u_hb2s] hb2s_imports hb2s_G.
Proof.
  destruct hb2s_small_body.hb2s_small_bodies as [Hcf [Heq [Hz [Hcp [Hset [Hds [Hle Hrot]]]]]]].
  destruct hb2s_compress_body.hb2s_compress_bodies as [Hg Hcomp].
  pose proof hb2s_ref_body.hb2s_ref_body as Href.
  pose proof hb2s_main_body.hb2s_main_body as Hmain.
  split; [vm_compute; repeat constructor; simpl; intuition discriminate |].
  change (hb2s_imports (u_cs u_hb2s) ++ hb2s_G) with hb2s_Gprog.
  repeat constructor.
  all: exists u_hb2s; split; [left; reflexivity |]; eexists; split; [reflexivity | assumption].
Qed.
