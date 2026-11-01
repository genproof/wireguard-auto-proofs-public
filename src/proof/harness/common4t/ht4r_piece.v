(* the piece of the four NULL-tolerant
   reference AEAD functions of common.h (ht4r_spec.v), for ANY identifier mp of rp_final's static minusp.  A law
   lifts it into its whole program with asm_lib's asm_piece_lift: its unit u_ht4r has prim_aead's Clight of the four
   functions (byte-identical in the transport harnesses), compspecs W_prim_aead (included in every transport world:
   ht4_worlds.v) and no varspecs; its imports are ht4c_G0 mp. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.harness.prim_aead.haead_lemmas3.
Require Import WgNoise.proof.harness.common4t.ht4r_spec.
Require WgNoise.proof.harness.common4t.ht4r_tag WgNoise.proof.harness.common4t.ht4r_dec.
Require WgNoise.harness.x_prim_aead.code.

#[local] Existing Instance W_prim_aead.
Local Open Scope Z_scope.

Theorem ht4r_piece (mp: ident) : haead_hyps -> piece_ok [u_ht4r] (fun _ => ht4c_G0 mp) (ht4r_G mp).
Proof.
  intros HH.
  destruct (ht4r_tag.ht4r_tag_bodies mp HH) as [B1 B2].
  destruct (ht4r_dec.ht4r_dec_bodies mp HH) as [B3 B4].
  split; [vm_compute; repeat constructor; simpl; intuition discriminate |].
  change ((fun _ => ht4c_G0 mp) (u_cs u_ht4r) ++ ht4r_G mp) with (ht4r_Gprog mp).
  repeat constructor.
  all: exists u_ht4r; split; [left; reflexivity |]; eexists; split; [reflexivity | assumption].
Qed.
