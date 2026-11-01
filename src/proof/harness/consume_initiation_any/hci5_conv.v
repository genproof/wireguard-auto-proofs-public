(* law consume_initiation_any: conversions between main's world compspecs
   W_consume_initiation_any and the compspecs of the specifications, for the stack frame of main (prologue,
   returns).  Port of v1's hci3_conv.v; *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Local Open Scope logic.

#[local] Instance hci5_cce_N : change_composite_env Noise.CS W_consume_initiation_any.
Proof. make_cs_preserve Noise.CS W_consume_initiation_any. Defined.
#[local] Instance hci5_cce_H : change_composite_env HCS W_consume_initiation_any.
Proof. make_cs_preserve HCS W_consume_initiation_any. Defined.
#[local] Instance hci5_cce_K : change_composite_env CKS W_consume_initiation_any.
Proof. make_cs_preserve CKS W_consume_initiation_any. Defined.

Lemma hci5_conv_dev sh p : @data_at_ Noise.CS sh t_dev p = @data_at_ W_consume_initiation_any sh t_dev p.
Proof. rewrite (@data_at__change_composite Noise.CS W_consume_initiation_any _ sh t_dev); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hci5_conv_itab sh p : @data_at_ Noise.CS sh t_itab p = @data_at_ W_consume_initiation_any sh t_itab p.
Proof. rewrite (@data_at__change_composite Noise.CS W_consume_initiation_any _ sh t_itab); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hci5_conv_ptab sh p : @data_at_ Noise.CS sh t_ptab p = @data_at_ W_consume_initiation_any sh t_ptab p.
Proof. rewrite (@data_at__change_composite Noise.CS W_consume_initiation_any _ sh t_ptab); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hci5_conv_peer sh p : @data_at_ Noise.CS sh t_peer p = @data_at_ W_consume_initiation_any sh t_peer p.
Proof. rewrite (@data_at__change_composite Noise.CS W_consume_initiation_any _ sh t_peer); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hci5_conv_init sh p : @data_at_ Noise.CS sh t_init p = @data_at_ W_consume_initiation_any sh t_init p.
Proof. rewrite (@data_at__change_composite Noise.CS W_consume_initiation_any _ sh t_init); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hci5_conv_mident sh p : @data_at_ HCS sh t_mident p = @data_at_ W_consume_initiation_any sh t_mident p.
Proof. rewrite (@data_at__change_composite HCS W_consume_initiation_any _ sh t_mident); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hci5_conv_minit sh p : @data_at_ HCS sh t_minit p = @data_at_ W_consume_initiation_any sh t_minit p.
Proof. rewrite (@data_at__change_composite HCS W_consume_initiation_any _ sh t_minit); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hci5_conv_mcinit sh p : @data_at_ HCS sh t_mcinit p = @data_at_ W_consume_initiation_any sh t_mcinit p.
Proof. rewrite (@data_at__change_composite HCS W_consume_initiation_any _ sh t_mcinit); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hci5_conv_devsnap sh p : @data_at_ CKS sh t_devsnap p = @data_at_ W_consume_initiation_any sh t_devsnap p.
Proof. rewrite (@data_at__change_composite CKS W_consume_initiation_any _ sh t_devsnap); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hci5_conv_shimsnap sh p : @data_at_ CKS sh t_shimsnap p = @data_at_ W_consume_initiation_any sh t_shimsnap p.
Proof. rewrite (@data_at__change_composite CKS W_consume_initiation_any _ sh t_shimsnap); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hci5_conv_bytes sh n p : hout sh n p = @data_at_ W_consume_initiation_any sh (tarray tuchar n) p.
Proof. unfold hout. rewrite (@data_at__change_composite HCS W_consume_initiation_any _ sh (tarray tuchar n)); [reflexivity | prove_cs_preserve_type]. Qed.

(* the local `peers` (struct hnode * ): kept at the world in the states; hnodes_add4's spec has it at CKS *)
Lemma hci5_conv_hnodep_v sh (v: val) p :
  @data_at CKS sh (tptr t_hnode4) v p = @data_at W_consume_initiation_any sh (tptr t_hnode4) v p.
Proof. rewrite (@data_at_change_composite CKS W_consume_initiation_any _ sh (tptr t_hnode4) v v (JMeq_refl v)); [reflexivity | prove_cs_preserve_type]. Qed.
