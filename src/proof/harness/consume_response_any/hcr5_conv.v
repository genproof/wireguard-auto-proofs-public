(* law consume_response_any: conversions between main's world compspecs
   W_consume_response_any and the compspecs of the specifications (Noise.CS for the kernel structs, HCS for the
   harness's model structs, CKS for common4's structs), for the stack frame of main (prologue, returns), and the
   dissolution of an index table (returns).  The port of v1's hcr3_conv.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Local Open Scope logic.

#[local] Instance hcr5_cce_N : change_composite_env Noise.CS W_consume_response_any.
Proof. make_cs_preserve Noise.CS W_consume_response_any. Defined.
#[local] Instance hcr5_cce_H : change_composite_env HCS W_consume_response_any.
Proof. make_cs_preserve HCS W_consume_response_any. Defined.
#[local] Instance hcr5_cce_K : change_composite_env CKS W_consume_response_any.
Proof. make_cs_preserve CKS W_consume_response_any. Defined.

Lemma hcr5_conv_dev sh p : @data_at_ Noise.CS sh t_dev p = @data_at_ W_consume_response_any sh t_dev p.
Proof. rewrite (@data_at__change_composite Noise.CS W_consume_response_any _ sh t_dev); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcr5_conv_itab sh p : @data_at_ Noise.CS sh t_itab p = @data_at_ W_consume_response_any sh t_itab p.
Proof. rewrite (@data_at__change_composite Noise.CS W_consume_response_any _ sh t_itab); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcr5_conv_ptab sh p : @data_at_ Noise.CS sh t_ptab p = @data_at_ W_consume_response_any sh t_ptab p.
Proof. rewrite (@data_at__change_composite Noise.CS W_consume_response_any _ sh t_ptab); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcr5_conv_peer sh p : @data_at_ Noise.CS sh t_peer p = @data_at_ W_consume_response_any sh t_peer p.
Proof. rewrite (@data_at__change_composite Noise.CS W_consume_response_any _ sh t_peer); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcr5_conv_resp sh p : @data_at_ Noise.CS sh t_resp p = @data_at_ W_consume_response_any sh t_resp p.
Proof. rewrite (@data_at__change_composite Noise.CS W_consume_response_any _ sh t_resp); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcr5_conv_entry sh p : @data_at_ Noise.CS sh t_entry_s p = @data_at_ W_consume_response_any sh t_entry_s p.
Proof. rewrite (@data_at__change_composite Noise.CS W_consume_response_any _ sh t_entry_s); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcr5_conv_mident sh p : @data_at_ HCS sh t_mident p = @data_at_ W_consume_response_any sh t_mident p.
Proof. rewrite (@data_at__change_composite HCS W_consume_response_any _ sh t_mident); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcr5_conv_mstate sh p : @data_at_ HCS sh t_mstate p = @data_at_ W_consume_response_any sh t_mstate p.
Proof. rewrite (@data_at__change_composite HCS W_consume_response_any _ sh t_mstate); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcr5_conv_mresp sh p : @data_at_ HCS sh t_mresp p = @data_at_ W_consume_response_any sh t_mresp p.
Proof. rewrite (@data_at__change_composite HCS W_consume_response_any _ sh t_mresp); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcr5_conv_devsnap sh p : @data_at_ CKS sh t_devsnap p = @data_at_ W_consume_response_any sh t_devsnap p.
Proof. rewrite (@data_at__change_composite CKS W_consume_response_any _ sh t_devsnap); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcr5_conv_shimsnap sh p : @data_at_ CKS sh t_shimsnap p = @data_at_ W_consume_response_any sh t_shimsnap p.
Proof. rewrite (@data_at__change_composite CKS W_consume_response_any _ sh t_shimsnap); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcr5_conv_bytes sh n p : hout sh n p = @data_at_ W_consume_response_any sh (tarray tuchar n) p.
Proof. unfold hout. rewrite (@data_at__change_composite HCS W_consume_response_any _ sh (tarray tuchar n)); [reflexivity | prove_cs_preserve_type]. Qed.

(* the local `peers` (struct hnode * ): kept at the world in the states; hnodes_add4's spec has it at CKS *)
Lemma hcr5_conv_hnodep_v sh (v: val) p :
  @data_at CKS sh (tptr t_hnode4) v p = @data_at W_consume_response_any sh (tptr t_hnode4) v p.
Proof. rewrite (@data_at_change_composite CKS W_consume_response_any _ sh (tptr t_hnode4) v v (JMeq_refl v)); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcr5_conv_hnodep sh p :
  @data_at_ CKS sh (tptr t_hnode4) p = @data_at_ W_consume_response_any sh (tptr t_hnode4) p.
Proof. rewrite (@data_at__change_composite CKS W_consume_response_any _ sh (tptr t_hnode4)); [reflexivity | prove_cs_preserve_type]. Qed.

(* an index table gives back its own struct and every pool entry (any list fields) *)
Definition hcr5_pool_entry (x: val * share * entry) : mpred :=
  match x with (a, sh, E) => EX n: val, EX h: bool, entry_at sh a E n h end.

Lemma hcr5_itable_dissolve sht tab T :
  itable sht tab T |-- @data_at_ Noise.CS sht t_itab tab * iter_sepcon hcr5_pool_entry (t_D T).
Proof.
  unfold itable. Intros. apply sepcon_derives; [apply data_at_data_at_ |].
  apply iter_sepcon_derives. intros [[a sh] E] _. unfold pool_item_rep, hcr5_pool_entry.
  Exists (succ_in (t_L T) a) (vin a (t_L T)). apply derives_refl.
Qed.
