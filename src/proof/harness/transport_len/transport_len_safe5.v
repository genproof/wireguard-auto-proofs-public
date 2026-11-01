(* the law transport_len, closed (Qed; nothing assumed in its closure).
*)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.wg3_iface3.
Require WgNoise.contracts.x_transport_len.
Require WgNoise.proof.harness.prim_aead.haead_piece3.
Require WgNoise.proof.harness.common4t.ht4r_piece WgNoise.proof.harness.common4t.ht4r_sub.
Require WgNoise.proof.harness.transport_len.htl5_defs WgNoise.proof.harness.transport_len.htl5_asm.

Theorem transport_len_safe5 :
  blake2s3_ok -> aead3b_ok -> x25519_ok3c ->
  harness_safe WgNoise.contracts.x_transport_len.whole_prog.
Proof.
  (* the concrete AEAD piece (aead_piece3b) is used, not the abstract interface aead3b_ok *)
  intros [Gb [Hp [Hi Hc]]] _ _.
  exact (WgNoise.proof.harness.transport_len.htl5_asm.htl5_safe Gb Hp Hi Hc
           (WgNoise.proof.harness.common4t.ht4r_piece.ht4r_piece _ WgNoise.proof.harness.prim_aead.haead_piece3.haead_hyps_ok)
           (WgNoise.proof.harness.common4t.ht4r_sub.ht4r_dec_sub _ _)).
Qed.
