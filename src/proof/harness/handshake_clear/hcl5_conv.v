(* law handshake_clear: conversions between main's world compspecs W_handshake_clear
   and the compspecs of the specifications, for the stack frame of main (prologue, returns).  Port of consume_initiation_any's
   hci5_conv.v; *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_world.
Local Open Scope logic.

#[local] Instance hcl5_cce_N : change_composite_env Noise.CS W_handshake_clear.
Proof. make_cs_preserve Noise.CS W_handshake_clear. Defined.
#[local] Instance hcl5_cce_H : change_composite_env HCS W_handshake_clear.
Proof. make_cs_preserve HCS W_handshake_clear. Defined.
#[local] Instance hcl5_cce_K : change_composite_env CKS W_handshake_clear.
Proof. make_cs_preserve CKS W_handshake_clear. Defined.

Lemma hcl5_conv_dev sh p : @data_at_ Noise.CS sh t_dev p = @data_at_ W_handshake_clear sh t_dev p.
Proof. rewrite (@data_at__change_composite Noise.CS W_handshake_clear _ sh t_dev); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcl5_conv_itab sh p : @data_at_ Noise.CS sh t_itab p = @data_at_ W_handshake_clear sh t_itab p.
Proof. rewrite (@data_at__change_composite Noise.CS W_handshake_clear _ sh t_itab); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcl5_conv_ptab sh p : @data_at_ Noise.CS sh t_ptab p = @data_at_ W_handshake_clear sh t_ptab p.
Proof. rewrite (@data_at__change_composite Noise.CS W_handshake_clear _ sh t_ptab); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcl5_conv_peer sh p : @data_at_ Noise.CS sh t_peer p = @data_at_ W_handshake_clear sh t_peer p.
Proof. rewrite (@data_at__change_composite Noise.CS W_handshake_clear _ sh t_peer); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcl5_conv_devsnap sh p : @data_at_ CKS sh t_devsnap p = @data_at_ W_handshake_clear sh t_devsnap p.
Proof. rewrite (@data_at__change_composite CKS W_handshake_clear _ sh t_devsnap); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcl5_conv_shimsnap sh p : @data_at_ CKS sh t_shimsnap p = @data_at_ W_handshake_clear sh t_shimsnap p.
Proof. rewrite (@data_at__change_composite CKS W_handshake_clear _ sh t_shimsnap); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcl5_conv_bytes sh n p : hout sh n p = @data_at_ W_handshake_clear sh (tarray tuchar n) p.
Proof. unfold hout. rewrite (@data_at__change_composite HCS W_handshake_clear _ sh (tarray tuchar n)); [reflexivity | prove_cs_preserve_type]. Qed.

(* the local `peers` (struct hnode * ): kept at the world in the states; hnodes_add4's spec has it at CKS *)
Lemma hcl5_conv_hnodep_v sh (v: val) p :
  @data_at CKS sh (tptr t_hnode4) v p = @data_at W_handshake_clear sh (tptr t_hnode4) v p.
Proof. rewrite (@data_at_change_composite CKS W_handshake_clear _ sh (tptr t_hnode4) v v (JMeq_refl v)); [reflexivity | prove_cs_preserve_type]. Qed.

(* the snapshot locals, once taken, back to the stack frame *)
Lemma hcl5_conv_devsnap_v sh v p :
  @data_at CKS sh t_devsnap v p |-- @data_at_ W_handshake_clear sh t_devsnap p.
Proof. rewrite <- hcl5_conv_devsnap. apply data_at_data_at_. Qed.
Lemma hcl5_conv_shimsnap_v sh v p :
  @data_at CKS sh t_shimsnap v p |-- @data_at_ W_handshake_clear sh t_shimsnap p.
Proof. rewrite <- hcl5_conv_shimsnap. apply data_at_data_at_. Qed.
