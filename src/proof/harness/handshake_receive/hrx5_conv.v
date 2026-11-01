(* law handshake_receive: conversions between main's world compspecs
   W_handshake_receive and the compspecs of the specifications, for main's stack
   frame (prologue, return).  Port of consume_initiation_any's hci5_conv.v; *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Local Open Scope logic.

Notation W := W_handshake_receive.

#[local] Instance hrx5_cce_N : change_composite_env Noise.CS W.
Proof. make_cs_preserve Noise.CS W. Defined.
#[local] Instance hrx5_cce_C : change_composite_env Cookie.CS W.
Proof. make_cs_preserve Cookie.CS W. Defined.
#[local] Instance hrx5_cce_H : change_composite_env HCS W.
Proof. make_cs_preserve HCS W. Defined.
#[local] Instance hrx5_cce_K : change_composite_env CKS W.
Proof. make_cs_preserve CKS W. Defined.

Lemma hrx5_conv_dev sh p : @data_at_ Noise.CS sh t_dev p = @data_at_ W sh t_dev p.
Proof. rewrite (@data_at__change_composite Noise.CS W _ sh t_dev); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hrx5_conv_itab sh p : @data_at_ Noise.CS sh t_itab p = @data_at_ W sh t_itab p.
Proof. rewrite (@data_at__change_composite Noise.CS W _ sh t_itab); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hrx5_conv_ptab sh p : @data_at_ Noise.CS sh t_ptab p = @data_at_ W sh t_ptab p.
Proof. rewrite (@data_at__change_composite Noise.CS W _ sh t_ptab); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hrx5_conv_peer sh p : @data_at_ Noise.CS sh t_peer p = @data_at_ W sh t_peer p.
Proof. rewrite (@data_at__change_composite Noise.CS W _ sh t_peer); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hrx5_conv_init sh p : @data_at_ Noise.CS sh t_init p = @data_at_ W sh t_init p.
Proof. rewrite (@data_at__change_composite Noise.CS W _ sh t_init); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hrx5_conv_resp sh p : @data_at_ Noise.CS sh t_resp p = @data_at_ W sh t_resp p.
Proof. rewrite (@data_at__change_composite Noise.CS W _ sh t_resp); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hrx5_conv_skb sh p : @data_at_ Cookie.CS sh t_skb p = @data_at_ W sh t_skb p.
Proof. rewrite (@data_at__change_composite Cookie.CS W _ sh t_skb); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hrx5_conv_mident sh p : @data_at_ HCS sh t_mident p = @data_at_ W sh t_mident p.
Proof. rewrite (@data_at__change_composite HCS W _ sh t_mident); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hrx5_conv_mcinit sh p : @data_at_ HCS sh t_mcinit p = @data_at_ W sh t_mcinit p.
Proof. rewrite (@data_at__change_composite HCS W _ sh t_mcinit); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hrx5_conv_mstate sh p : @data_at_ HCS sh t_mstate p = @data_at_ W sh t_mstate p.
Proof. rewrite (@data_at__change_composite HCS W _ sh t_mstate); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hrx5_conv_devsnap sh p : @data_at_ CKS sh t_devsnap p = @data_at_ W sh t_devsnap p.
Proof. rewrite (@data_at__change_composite CKS W _ sh t_devsnap); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hrx5_conv_shimsnap sh p : @data_at_ CKS sh t_shimsnap p = @data_at_ W sh t_shimsnap p.
Proof. rewrite (@data_at__change_composite CKS W _ sh t_shimsnap); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hrx5_conv_skbsnap sh p : @data_at_ CKS sh t_skbsnap p = @data_at_ W sh t_skbsnap p.
Proof. rewrite (@data_at__change_composite CKS W _ sh t_skbsnap); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hrx5_conv_bytes sh n p : hout sh n p = @data_at_ W sh (tarray tuchar n) p.
Proof. unfold hout. rewrite (@data_at__change_composite HCS W _ sh (tarray tuchar n)); [reflexivity | prove_cs_preserve_type]. Qed.

(* the local `peers` (struct hnode * ): kept at the world in the states; hnodes_add4's spec has it at CKS *)
Lemma hrx5_conv_hnodep_v sh (v: val) p :
  @data_at CKS sh (tptr t_hnode4) v p = @data_at W sh (tptr t_hnode4) v p.
Proof. rewrite (@data_at_change_composite CKS W _ sh (tptr t_hnode4) v v (JMeq_refl v)); [reflexivity | prove_cs_preserve_type]. Qed.
