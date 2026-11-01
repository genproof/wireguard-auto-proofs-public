(* the harness piece of law prim_poly1305, from the body files. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.harness.prim_poly1305.hp1305_spec3.
Require WgNoise.proof.harness.prim_poly1305.hp1305_small_body3 WgNoise.proof.harness.prim_poly1305.hp1305_rp_body3
        WgNoise.proof.harness.prim_poly1305.hp1305_rpmul_body3 WgNoise.proof.harness.prim_poly1305.hp1305_ref_body3
        WgNoise.proof.harness.prim_poly1305.hp1305_main_body3.

Theorem hp1305_piece3 : piece_ok [u_hp1305] hp1305_imports hp1305_G.
Proof.
  destruct hp1305_small_body3.hp1305_small_bodies as [Hcf [Heq [Hz [Hcp Hds]]]].
  destruct hp1305_rp_body3.hp1305_rp_bodies as [Hadd [Hinit [Hblock Hfinal]]].
  pose proof hp1305_rpmul_body3.hp1305_rpmul_body as Hmul.
  pose proof hp1305_ref_body3.hp1305_ref_body as Href.
  pose proof hp1305_main_body3.hp1305_main_body as Hmain.
  split; [vm_compute; repeat constructor; simpl; intuition discriminate |].
  change (hp1305_imports (u_cs u_hp1305) ++ hp1305_G) with hp1305_Gprog.
  repeat constructor.
  all: exists u_hp1305; split; [left; reflexivity |]; eexists; split; [reflexivity | assumption].
Qed.
