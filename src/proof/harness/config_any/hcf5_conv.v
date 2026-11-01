(* law config_any: conversions between main's world compspecs
   W_config_any and the compspecs of the specifications, for the stack frame of main (prologue,
   returns).  Port of hci5_conv.v; *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.harness.config_any.hcf5_world.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Local Open Scope logic.

#[local] Instance hcf5_cce_N : change_composite_env Noise.CS W_config_any.
Proof. make_cs_preserve Noise.CS W_config_any. Defined.
#[local] Instance hcf5_cce_H : change_composite_env HCS W_config_any.
Proof. make_cs_preserve HCS W_config_any. Defined.
#[local] Instance hcf5_cce_K : change_composite_env CKS W_config_any.
Proof. make_cs_preserve CKS W_config_any. Defined.

Lemma hcf5_conv_dev sh p : @data_at_ Noise.CS sh t_dev p = @data_at_ W_config_any sh t_dev p.
Proof. rewrite (@data_at__change_composite Noise.CS W_config_any _ sh t_dev); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcf5_conv_itab sh p : @data_at_ Noise.CS sh t_itab p = @data_at_ W_config_any sh t_itab p.
Proof. rewrite (@data_at__change_composite Noise.CS W_config_any _ sh t_itab); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcf5_conv_ptab sh p : @data_at_ Noise.CS sh t_ptab p = @data_at_ W_config_any sh t_ptab p.
Proof. rewrite (@data_at__change_composite Noise.CS W_config_any _ sh t_ptab); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcf5_conv_peer sh p : @data_at_ Noise.CS sh t_peer p = @data_at_ W_config_any sh t_peer p.
Proof. rewrite (@data_at__change_composite Noise.CS W_config_any _ sh t_peer); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcf5_conv_init sh p : @data_at_ Noise.CS sh t_init p = @data_at_ W_config_any sh t_init p.
Proof. rewrite (@data_at__change_composite Noise.CS W_config_any _ sh t_init); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcf5_conv_mident sh p : @data_at_ HCS sh t_mident p = @data_at_ W_config_any sh t_mident p.
Proof. rewrite (@data_at__change_composite HCS W_config_any _ sh t_mident); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcf5_conv_devsnap sh p : @data_at_ CKS sh t_devsnap p = @data_at_ W_config_any sh t_devsnap p.
Proof. rewrite (@data_at__change_composite CKS W_config_any _ sh t_devsnap); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcf5_conv_shimsnap sh p : @data_at_ CKS sh t_shimsnap p = @data_at_ W_config_any sh t_shimsnap p.
Proof. rewrite (@data_at__change_composite CKS W_config_any _ sh t_shimsnap); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcf5_conv_bytes sh n p : hout sh n p = @data_at_ W_config_any sh (tarray tuchar n) p.
Proof. unfold hout. rewrite (@data_at__change_composite HCS W_config_any _ sh (tarray tuchar n)); [reflexivity | prove_cs_preserve_type]. Qed.

Lemma hcf5_conv_hsnap sh p : @data_at_ HCS sh t_hsnap p = @data_at_ W_config_any sh t_hsnap p.
Proof. rewrite (@data_at__change_composite HCS W_config_any _ sh t_hsnap); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcf5_conv_prsnap sh p : @data_at_ CKS sh t_prsnap p = @data_at_ W_config_any sh t_prsnap p.
Proof. rewrite (@data_at__change_composite CKS W_config_any _ sh t_prsnap); [reflexivity | prove_cs_preserve_type]. Qed.
