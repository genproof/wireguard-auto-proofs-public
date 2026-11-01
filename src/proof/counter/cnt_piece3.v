(* the counter piece: the four functions of patch/counter_validate.c
   against counter_spec.v, in Counter.CS. *)
Require Import VST.floyd.proofauto.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.counter.counter_spec.
Require WgNoise.proof.counter.cnt_body3.

Module B := WgNoise.proof.counter.cnt_body3.

(* one entry of the Forall of piece_ok: the body lemma L proved in unit u_counter *)
Local Ltac cnt3_entry L :=
  apply Forall_cons; [exists u_counter; split; [left; reflexivity |]; eexists; split; [reflexivity | exact L] |].

Theorem cnt_piece3 : piece_ok [u_counter] cnt_imports cnt_G.
Proof.
  split; [repeat constructor; simpl; intuition discriminate |].
  unfold cnt_G at 1.
  cnt3_entry B.body_quickproof_ilog2.
  cnt3_entry B.body_test_and_set_bit.
  cnt3_entry B.body_counter_validate.
  cnt3_entry B.body_wg_counter_validate.
  constructor.
Qed.
