(* law handshake: conversions between main's world compspecs W_handshake and the compspecs of the
   specifications (Noise.CS for the kernel structs, HCS for the harness structs), for the stack frame of main
   (prologue, returns), and the dissolution of an index table (returns). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Local Open Scope logic.

#[local] Instance hhs3_cce_N : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.
#[local] Instance hhs3_cce_H : change_composite_env HCS W_handshake.
Proof. make_cs_preserve HCS W_handshake. Defined.

Lemma hhs3_conv_dev sh p : @data_at_ Noise.CS sh t_dev p = @data_at_ W_handshake sh t_dev p.
Proof. rewrite (@data_at__change_composite Noise.CS W_handshake _ sh t_dev); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hhs3_conv_itab sh p : @data_at_ Noise.CS sh t_itab p = @data_at_ W_handshake sh t_itab p.
Proof. rewrite (@data_at__change_composite Noise.CS W_handshake _ sh t_itab); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hhs3_conv_ptab sh p : @data_at_ Noise.CS sh t_ptab p = @data_at_ W_handshake sh t_ptab p.
Proof. rewrite (@data_at__change_composite Noise.CS W_handshake _ sh t_ptab); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hhs3_conv_peer sh p : @data_at_ Noise.CS sh t_peer p = @data_at_ W_handshake sh t_peer p.
Proof. rewrite (@data_at__change_composite Noise.CS W_handshake _ sh t_peer); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hhs3_conv_init sh p : @data_at_ Noise.CS sh t_init p = @data_at_ W_handshake sh t_init p.
Proof. rewrite (@data_at__change_composite Noise.CS W_handshake _ sh t_init); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hhs3_conv_resp sh p : @data_at_ Noise.CS sh t_resp p = @data_at_ W_handshake sh t_resp p.
Proof. rewrite (@data_at__change_composite Noise.CS W_handshake _ sh t_resp); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hhs3_conv_mident sh p : @data_at_ HCS sh t_mident p = @data_at_ W_handshake sh t_mident p.
Proof. rewrite (@data_at__change_composite HCS W_handshake _ sh t_mident); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hhs3_conv_minit sh p : @data_at_ HCS sh t_minit p = @data_at_ W_handshake sh t_minit p.
Proof. rewrite (@data_at__change_composite HCS W_handshake _ sh t_minit); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hhs3_conv_mcinit sh p : @data_at_ HCS sh t_mcinit p = @data_at_ W_handshake sh t_mcinit p.
Proof. rewrite (@data_at__change_composite HCS W_handshake _ sh t_mcinit); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hhs3_conv_mresp sh p : @data_at_ HCS sh t_mresp p = @data_at_ W_handshake sh t_mresp p.
Proof. rewrite (@data_at__change_composite HCS W_handshake _ sh t_mresp); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hhs3_conv_mstate sh p : @data_at_ HCS sh t_mstate p = @data_at_ W_handshake sh t_mstate p.
Proof. rewrite (@data_at__change_composite HCS W_handshake _ sh t_mstate); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hhs3_conv_hsnap sh p : @data_at_ HCS sh t_hsnap p = @data_at_ W_handshake sh t_hsnap p.
Proof. rewrite (@data_at__change_composite HCS W_handshake _ sh t_hsnap); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hhs3_conv_bytes sh n p : hout sh n p = @data_at_ W_handshake sh (tarray tuchar n) p.
Proof. unfold hout. rewrite (@data_at__change_composite HCS W_handshake _ sh (tarray tuchar n)); [reflexivity | prove_cs_preserve_type]. Qed.

(* an index table gives back its own struct and every pool entry (any list fields) *)
Definition hhs3_pool_entry (x: val * share * entry) : mpred :=
  match x with (a, sh, E) => EX n: val, EX h: bool, entry_at sh a E n h end.

Lemma hhs3_itable_dissolve sht tab T :
  itable sht tab T |-- @data_at_ Noise.CS sht t_itab tab * iter_sepcon hhs3_pool_entry (t_D T).
Proof.
  unfold itable. Intros. apply sepcon_derives; [apply data_at_data_at_ |].
  apply iter_sepcon_derives. intros [[a sh] E] _. unfold pool_item_rep, hhs3_pool_entry.
  Exists (succ_in (t_L T) a) (vin a (t_L T)). apply derives_refl.
Qed.
