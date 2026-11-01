(* law create_any: main's locals (stack frame at W := W_create_any) in the compspecs
   of the specifications.  v1: *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.create_any.hca5_defs.
Require WgNoise.harness.x_create_any.code.

#[local] Instance hca5_CCE_NW : change_composite_env Noise.CS W_create_any.
Proof. make_cs_preserve Noise.CS W_create_any. Defined.
#[local] Instance hca5_CCE_HW : change_composite_env HCS W_create_any.
Proof. make_cs_preserve HCS W_create_any. Defined.

Lemma hca5_conv_dev sh v :
  @data_at_ W_create_any sh (Tstruct HC._wg_device noattr) v = @data_at_ Noise.CS sh t_dev v.
Proof. symmetry. exact (equal_f (@data_at__change_composite Noise.CS W_create_any _ sh t_dev eq_refl) v). Qed.

Lemma hca5_conv_itab sh v :
  @data_at_ W_create_any sh (Tstruct HC._index_hashtable noattr) v = @data_at_ Noise.CS sh t_itab v.
Proof. symmetry. exact (equal_f (@data_at__change_composite Noise.CS W_create_any _ sh t_itab eq_refl) v). Qed.

Lemma hca5_conv_ptab sh v :
  @data_at_ W_create_any sh (Tstruct HC._pubkey_hashtable noattr) v = @data_at_ Noise.CS sh t_ptab v.
Proof. symmetry. exact (equal_f (@data_at__change_composite Noise.CS W_create_any _ sh t_ptab eq_refl) v). Qed.

Lemma hca5_conv_peer sh v :
  @data_at_ W_create_any sh (Tstruct HC._wg_peer noattr) v = @data_at_ Noise.CS sh t_peer v.
Proof. symmetry. exact (equal_f (@data_at__change_composite Noise.CS W_create_any _ sh t_peer eq_refl) v). Qed.

Lemma hca5_conv_mident sh v :
  @data_at_ W_create_any sh (Tstruct HC._m_identity noattr) v = @data_at_ HCS sh t_mident v.
Proof. symmetry. exact (equal_f (@data_at__change_composite HCS W_create_any _ sh t_mident eq_refl) v). Qed.

Lemma hca5_conv_hsnap sh v :
  @data_at_ W_create_any sh (Tstruct HC._hs_snap noattr) v = @data_at_ HCS sh t_hsnap v.
Proof. symmetry. exact (equal_f (@data_at__change_composite HCS W_create_any _ sh t_hsnap eq_refl) v). Qed.

Lemma hca5_conv_mstate sh v :
  @data_at_ W_create_any sh (Tstruct HC._m_state noattr) v = @data_at_ HCS sh t_mstate v.
Proof. symmetry. exact (equal_f (@data_at__change_composite HCS W_create_any _ sh t_mstate eq_refl) v). Qed.

Lemma hca5_conv_bytes sh n v :
  @data_at_ W_create_any sh (tarray tuchar n) v = hout sh n v.
Proof. unfold hout. symmetry. exact (equal_f (@data_at__change_composite HCS W_create_any _ sh (tarray tuchar n) eq_refl) v). Qed.

#[local] Instance hca5_CCE_KW : change_composite_env CKS W_create_any.
Proof. make_cs_preserve CKS W_create_any. Defined.

Lemma hca5_conv_prsnap sh v :
  @data_at_ W_create_any sh (Tstruct HC._pr_snap noattr) v = @data_at_ CKS sh t_prsnap v.
Proof. symmetry. exact (equal_f (@data_at__change_composite CKS W_create_any _ sh t_prsnap eq_refl) v). Qed.

Lemma hca5_conv_devsnap sh v :
  @data_at_ W_create_any sh (Tstruct HC._dev_snap noattr) v = @data_at_ CKS sh t_devsnap v.
Proof. symmetry. exact (equal_f (@data_at__change_composite CKS W_create_any _ sh t_devsnap eq_refl) v). Qed.

Lemma hca5_conv_shimsnap sh v :
  @data_at_ W_create_any sh (Tstruct HC._shim_snap noattr) v = @data_at_ CKS sh t_shimsnap v.
Proof. symmetry. exact (equal_f (@data_at__change_composite CKS W_create_any _ sh t_shimsnap eq_refl) v). Qed.
