(* law cookie_mac: conversions between main's world compspecs W_cookie_mac and the compspecs of
   the specifications (Noise.CS / Cookie.CS for the kernel structs, HCS / CKS for the harness structs), for the stack
   frame of main (prologue, returns), and the dissolution of the buffers into the stack frame (returns).  Port of
   v1's hck3_conv.v + the v2 snapshot structs. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.cookie_mac.hck5_defs.
Local Open Scope logic.

#[local] Instance hck5_cce_N : change_composite_env Noise.CS W_cookie_mac.
Proof. make_cs_preserve Noise.CS W_cookie_mac. Defined.
#[local] Instance hck5_cce_C : change_composite_env Cookie.CS W_cookie_mac.
Proof. make_cs_preserve Cookie.CS W_cookie_mac. Defined.
#[local] Instance hck5_cce_H : change_composite_env HCS W_cookie_mac.
Proof. make_cs_preserve HCS W_cookie_mac. Defined.
#[local] Instance hck5_cce_K : change_composite_env CKS W_cookie_mac.
Proof. make_cs_preserve CKS W_cookie_mac. Defined.

Lemma hck5_conv_dev sh p : @data_at_ Noise.CS sh t_dev p = @data_at_ W_cookie_mac sh t_dev p.
Proof. rewrite (@data_at__change_composite Noise.CS W_cookie_mac _ sh t_dev); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hck5_conv_itab sh p : @data_at_ Noise.CS sh t_itab p = @data_at_ W_cookie_mac sh t_itab p.
Proof. rewrite (@data_at__change_composite Noise.CS W_cookie_mac _ sh t_itab); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hck5_conv_ptab sh p : @data_at_ Noise.CS sh t_ptab p = @data_at_ W_cookie_mac sh t_ptab p.
Proof. rewrite (@data_at__change_composite Noise.CS W_cookie_mac _ sh t_ptab); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hck5_conv_peer sh p : @data_at_ Noise.CS sh t_peer p = @data_at_ W_cookie_mac sh t_peer p.
Proof. rewrite (@data_at__change_composite Noise.CS W_cookie_mac _ sh t_peer); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hck5_conv_skb sh p : @data_at_ Cookie.CS sh t_skb p = @data_at_ W_cookie_mac sh t_skb p.
Proof. rewrite (@data_at__change_composite Cookie.CS W_cookie_mac _ sh t_skb); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hck5_conv_mident sh p : @data_at_ HCS sh t_mident p = @data_at_ W_cookie_mac sh t_mident p.
Proof. rewrite (@data_at__change_composite HCS W_cookie_mac _ sh t_mident); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hck5_conv_cksnap sh p : @data_at_ CKS sh t_cksnap p = @data_at_ W_cookie_mac sh t_cksnap p.
Proof. rewrite (@data_at__change_composite CKS W_cookie_mac _ sh t_cksnap); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hck5_conv_bytes sh n p : hout sh n p = @data_at_ W_cookie_mac sh (tarray tuchar n) p.
Proof. unfold hout. rewrite (@data_at__change_composite HCS W_cookie_mac _ sh (tarray tuchar n)); [reflexivity | prove_cs_preserve_type]. Qed.

(* the v2 snapshot structs *)
Lemma hck5_conv_hsnap sh p : @data_at_ HCS sh t_hsnap p = @data_at_ W_cookie_mac sh t_hsnap p.
Proof. rewrite (@data_at__change_composite HCS W_cookie_mac _ sh t_hsnap); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hck5_conv_prsnap sh p : @data_at_ CKS sh t_prsnap p = @data_at_ W_cookie_mac sh t_prsnap p.
Proof. rewrite (@data_at__change_composite CKS W_cookie_mac _ sh t_prsnap); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hck5_conv_devsnap sh p : @data_at_ CKS sh t_devsnap p = @data_at_ W_cookie_mac sh t_devsnap p.
Proof. rewrite (@data_at__change_composite CKS W_cookie_mac _ sh t_devsnap); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hck5_conv_skbsnap sh p : @data_at_ CKS sh t_skbsnap p = @data_at_ W_cookie_mac sh t_skbsnap p.
Proof. rewrite (@data_at__change_composite CKS W_cookie_mac _ sh t_skbsnap); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hck5_conv_shimsnap sh p : @data_at_ CKS sh t_shimsnap p = @data_at_ W_cookie_mac sh t_shimsnap p.
Proof. rewrite (@data_at__change_composite CKS W_cookie_mac _ sh t_shimsnap); [reflexivity | prove_cs_preserve_type]. Qed.

(* ---------------------------------------------------------------------- *)
(* Dissolving buffers and snapshots into the stack frame (returns)          *)
(* ---------------------------------------------------------------------- *)

Section Dissolve.
Variable x25519: list byte -> list byte -> list byte.

Lemma hck5_skb_free sh p s : skb_rep sh p s |-- @data_at_ W_cookie_mac sh t_skb p.
Proof.
  unfold skb_rep. Intros. rewrite <- hck5_conv_skb. apply data_at_data_at_.
Qed.

Lemma hck5_hbytes_free sh bs p : hbytes sh bs p |-- @data_at_ W_cookie_mac sh (tarray tuchar (Zlength bs)) p.
Proof.
  unfold hbytes. rewrite <- hck5_conv_bytes. unfold hout. apply data_at_data_at_.
Qed.

Lemma hck5_bufs_free R L :
  hck5_run_ok x25519 R ->
  fold_right sepcon emp (hck5_bufs x25519 R L) |--
  @data_at_ W_cookie_mac Tsh t_mident (l_ib L) * @data_at_ W_cookie_mac Tsh (tarray tuchar 32) (l_rawa L) *
  @data_at_ W_cookie_mac Tsh (tarray tuchar 32) (l_rawb L) * @data_at_ W_cookie_mac Tsh (tarray tuchar 32) (l_pub L).
Proof.
  intros (LA & LB & _ & _ & _ & LP & _). unfold hck5_bufs. simpl fold_right.
  rewrite <- hck5_conv_mident. sep_apply (@data_at_data_at_ HCS).
  sep_apply (hck5_hbytes_free Tsh (r_rawa R)). sep_apply (hck5_hbytes_free Tsh (r_rawb R)).
  sep_apply (hck5_hbytes_free Tsh (r_pub R)). rewrite LA, LB, LP. cancel.
Qed.

Lemma hck5_snaps0_free L :
  fold_right sepcon emp (hck5_snaps0 L) =
  @data_at_ W_cookie_mac Tsh t_hsnap (l_hs0 L) * @data_at_ W_cookie_mac Tsh t_prsnap (l_ps0 L) *
  @data_at_ W_cookie_mac Tsh t_devsnap (l_da L) * @data_at_ W_cookie_mac Tsh t_devsnap (l_db L) *
  @data_at_ W_cookie_mac Tsh t_skbsnap (l_sks L) * @data_at_ W_cookie_mac Tsh t_shimsnap (l_ss L).
Proof.
  unfold hck5_snaps0. simpl fold_right. rewrite sepcon_emp.
  rewrite hck5_conv_hsnap, hck5_conv_prsnap, !hck5_conv_devsnap, hck5_conv_skbsnap, hck5_conv_shimsnap.
  rewrite <- !sepcon_assoc. reflexivity.
Qed.

End Dissolve.
