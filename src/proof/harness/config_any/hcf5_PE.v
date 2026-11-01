(* law config_any: main's phase PE, statements 94..95: kents_free(kes), return 0.
   (states: hcf5_defs.v).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.config_any.hcf5_world.
Require Import WgNoise.proof.harness.config_any.hcf5_cut.
Require Import WgNoise.proof.harness.config_any.hcf5_globals.
Require Import WgNoise.proof.harness.config_any.hcf5_spec.
Require Import WgNoise.proof.harness.config_any.hcf5_defs.
Require Import WgNoise.proof.harness.config_any.hcf5_conv.
Require Import WgNoise.proof.harness.config_any.hcf5_pure.
Require WgNoise.harness.x_config_any.code.

#[local] Existing Instance W_config_any.
Local Open Scope Z_scope.

(* the stack frame of a return: the locals back to data_at_ at the world (as hci5_p8_c.v) *)
Lemma hcf5_pe_hbytes32 bs p : Zlength bs = 32 ->
  hbytes Tsh bs p |-- @data_at_ W_config_any Tsh (tarray tuchar 32) p.
Proof. intros Hl. unfold hbytes. rewrite Hl, <- hcf5_conv_bytes. unfold hout. apply data_at_data_at_. Qed.

Lemma hcf5_pe_ptable p head : ptable Tsh p head |-- @data_at_ W_config_any Tsh t_ptab p.
Proof. unfold ptable. rewrite <- hcf5_conv_ptab. apply data_at_data_at_. Qed.

Lemma hcf5_pe_mident v p : @data_at HCS Tsh t_mident v p |-- @data_at_ W_config_any Tsh t_mident p.
Proof. rewrite <- hcf5_conv_mident. apply data_at_data_at_. Qed.

Lemma hcf5_pe_hsnap v p : @data_at HCS Tsh t_hsnap v p |-- @data_at_ W_config_any Tsh t_hsnap p.
Proof. rewrite <- hcf5_conv_hsnap. apply data_at_data_at_. Qed.

Lemma hcf5_pe_devsnap v p : @data_at CKS Tsh t_devsnap v p |-- @data_at_ W_config_any Tsh t_devsnap p.
Proof. rewrite <- hcf5_conv_devsnap. apply data_at_data_at_. Qed.

Lemma hcf5_pe_prsnap v p : @data_at CKS Tsh t_prsnap v p |-- @data_at_ W_config_any Tsh t_prsnap p.
Proof. rewrite <- hcf5_conv_prsnap. apply data_at_data_at_. Qed.

Lemma hcf5_pe_shimsnap v p : @data_at CKS Tsh t_shimsnap v p |-- @data_at_ W_config_any Tsh t_shimsnap p.
Proof. rewrite <- hcf5_conv_shimsnap. apply data_at_data_at_. Qed.

Section PE.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcf5_PE_ok {Espec: OracleKind} gv L FR :
  hcf5_hyps x25519 -> hcf5_sepH ->
  semax (hcf5_Delta x25519) (hcf5_SX5 x25519 gv L FR) hcf5_PE
    (overridePost (FF) (hcf5_R gv)).
Proof.
  intros HH HS. unfold hcf5_SX5, hcf5_F, hcf5_Fx, hcf5_Delta, hcf5_R, hcf5_PE. simplify_func_tycontext. abbreviate_semax.
  Intros R S w D P T KE D0 sn0 P0 r0. Intros S0 w0 h0 RAW H.
  unfold hcf5_lvars, hcf5_core, hcf5_globs, hcf5_X5; cbn [app].
  destruct HS as (HSq1 & HSq2 & HSd & HSt).
  destruct H2 as (Hrun & Hboot & Hw5 & Hdok & Hpok & Hsl & HT & Hks).
  sep_apply (HSt L KE true T HT). Intros. Intros Ep np hp. Intros Eq nq hq.
  forward_call (gv, hcf5_khead KE, KE).
  apply hcf5_post_canon.
  sep_apply (HSd Tsh (l_w L) D).
  sep_apply (prot_rep3_peer_whole Tsh (l_p L) P Ep np hp).
  sep_apply (HSq2 (l_q L) H Eq nq hq cookie_zero).
  forward.
  destruct Hrun as (Hra & _ & _ & Hpb). destruct H0 as (Hraw & _).
  rewrite hcf5_conv_dev, hcf5_conv_itab, !hcf5_conv_peer, !hcf5_conv_bytes.
  sep_apply (hcf5_pe_hbytes32 (r_raw0 R) (l_raw0 L) Hra).
  sep_apply (hcf5_pe_hbytes32 (r_pub R) (l_pub L) Hpb).
  sep_apply (hcf5_pe_hbytes32 RAW (l_raw L) Hraw).
  sep_apply (hcf5_pe_ptable (l_pt L) (l_p L)).
  sep_apply (hcf5_pe_mident (mident_val (mident_of x25519 RAW)) (l_id L)).
  sep_apply (hcf5_pe_hsnap (hsnap_val sn0) (l_hs0 L)).
  sep_apply (hcf5_pe_hsnap (hsnap_val (hs_snap_cur T (l_q L) (hcf5_qpeer H))) (l_hq L)).
  sep_apply (hcf5_pe_devsnap (devsnap_val D0 (l_p L)) (l_ds L)).
  sep_apply (hcf5_pe_prsnap (prsnap_val P0) (l_ps0 L)).
  sep_apply (hcf5_pe_shimsnap (shimsnap_val S0 w0) (l_ss L)).
  cancel.
Qed.

End PE.
