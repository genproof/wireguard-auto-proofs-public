(* law config_any: the law's own piece = main's body. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.harness.config_any.hcf5_spec.
Require Import WgNoise.proof.harness.config_any.hcf5_defs.
Require Import WgNoise.proof.harness.config_any.hcf5_main.

(* the statement the assembly takes (hcf5_asm.v) *)
Definition hcf5_piece_stmt : Prop :=
  forall x25519, x25519_props x25519 -> piece_ok [u_hcf5] (hcf5_imports x25519) hcf5_G.

Theorem hcf5_piece : hcf5_piece_stmt.
Proof.
  intros x25519 HX. split.
  - repeat constructor; simpl; intuition discriminate.
  - constructor; [| constructor].
    exists u_hcf5. split; [left; reflexivity |].
    exists WgNoise.harness.x_config_any.code.f_main. split; [reflexivity |].
    apply (hcf5_main_body x25519); exact HX.
Qed.
