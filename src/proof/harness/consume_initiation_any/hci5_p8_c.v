(* law consume_initiation_any, phase P8, segment c: statements 35..38: free(msg); kents_free(kes); hnodes_free(peers); return 0.
   States and statements: hci5_p8_defs.v; (section P8).  The statement is
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_cut.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_model.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_globals.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_spec.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_conv.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_defs.
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

(* the message back to data_at_ at the world (free's spec) *)
Lemma hci5_p8_c_init m M : init_rep Ews m M |-- @data_at_ W_consume_initiation_any Ews t_init m.
Proof. unfold init_rep. Intros. rewrite <- hci5_conv_init. apply data_at_data_at_. Qed.

Lemma hci5_p8_c_initp m M : init_rep Ews m M |-- !! isptr m.
Proof. unfold init_rep. Intros. entailer!. match goal with Hf: field_compatible _ _ m |- _ => destruct Hf as [? _]; assumption end. Qed.

(* the stack frame of a return: the locals back to data_at_ at the world (as hci5_P4.v) *)
Lemma hci5_p8_c_hbytes32 bs p : Zlength bs = 32 ->
  hbytes Tsh bs p |-- @data_at_ W_consume_initiation_any Tsh (tarray tuchar 32) p.
Proof. intros Hl. unfold hbytes. rewrite Hl, <- hci5_conv_bytes. unfold hout. apply data_at_data_at_. Qed.

Lemma hci5_p8_c_hbytes148 bs p : Zlength bs = 148 ->
  hbytes Tsh bs p |-- @data_at_ W_consume_initiation_any Tsh (tarray tuchar 148) p.
Proof. intros Hl. unfold hbytes. rewrite Hl, <- hci5_conv_bytes. unfold hout. apply data_at_data_at_. Qed.

Lemma hci5_p8_c_init_len M : im_ok M -> Zlength (init_bytes M) = 148.
Proof.
  intros (H1 & H2 & H3 & H4 & H5). unfold init_bytes, le32.
  rewrite !Zlength_app, H1, H2, H3, H4, H5. reflexivity.
Qed.

Lemma hci5_p8_c_ptable p head : ptable Tsh p head |-- @data_at_ W_consume_initiation_any Tsh t_ptab p.
Proof. unfold ptable. rewrite <- hci5_conv_ptab. apply data_at_data_at_. Qed.

Lemma hci5_p8_c_mident v p : @data_at HCS Tsh t_mident v p |-- @data_at_ W_consume_initiation_any Tsh t_mident p.
Proof. rewrite <- hci5_conv_mident. apply data_at_data_at_. Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hci5_p8_c_ok {Espec: OracleKind} gv L FR :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> hci5_closeH ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_p8_Q2 x25519 gv L FR) hci5_p8_s3538 (overridePost FF (hci5_R gv)).
Proof.
  intros HH HC. unfold hci5_p8_Q2, hci5_Delta, hci5_R, hci5_p8_s3538. simplify_func_tycontext. abbreviate_semax.
  Intros R S w NS NS2 PS PS2. Intros T head na KE KE2 m M.
  unfold hci5_lvars, hci5_p8_scr, hci5_world, hci5_globs, hci5_snaps0, hci5_tok; cbn [app].
  assert_PROP (isptr m) as Hm by (sep_apply (hci5_p8_c_initp m M); entailer!).
  sep_apply (hci5_p8_c_init m M).
  forward_call (t_init, m, gv).
  { rewrite if_false by (intros Hn; subst m; contradiction). cancel. }
  destruct HC as [HCd HCp].
  destruct H0 as (Hok & Hwf & Hch & Hnp & Hna & HT & Hsl). destruct HT as (HT1 & HT2 & _ & _).
  rewrite <- H5 in HT1.
  sep_apply (HCp (l_itb L) T PS PS2 KE2 NS2 HT1 HT2 H2 H3).
  { unfold hnodes_peers4 in *. rewrite H4, H2. exact Hnp. }
  Intros.
  forward_call (gv, hci5_khead KE, KE2).
  assert_PROP (is_pointer_or_null (hci5_head NS)) as Hhd.
  { destruct NS2 as [|N NS2']; unfold hnodes_rep4; fold (hnodes_rep4 W).
    - Intros. entailer!.
      match goal with Hh: hci5_head NS = nullval |- _ => rewrite Hh; simpl; auto end.
    - Intros nx. entailer!.
      match goal with Hf: field_compatible t_hnode4 [] _ |- _ => destruct Hf as [? _] end.
      apply isptr_is_pointer_or_null; assumption. }
  forward.
  forward_call (gv, hci5_head NS, NS2).
  apply hci5_post_canon.
  sep_apply (HCd Tsh (l_wb L) (hci5_DB x25519 R L)).
  forward.
  destruct H as (Hra & Hrb & _).
  rewrite hci5_conv_dev, hci5_conv_itab, hci5_conv_mcinit, hci5_conv_minit, hci5_conv_devsnap,
    hci5_conv_shimsnap, !hci5_conv_bytes.
  sep_apply (hci5_p8_c_hbytes32 (r_rawa R) (l_rawa L) Hra).
  sep_apply (hci5_p8_c_hbytes32 (r_rawb R) (l_rawb L) Hrb).
  sep_apply (hci5_p8_c_ptable (l_ptb L) head).
  sep_apply (hci5_p8_c_mident (mident_val (hci5_IA x25519 R)) (l_ia L)).
  sep_apply (hci5_p8_c_mident (mident_val (hci5_IB x25519 R)) (l_ib L)).
  sep_apply (data_at_data_at_ Tsh (tptr t_hnode4) (hci5_head NS) (l_peers L)).
  sep_apply (hci5_p8_c_hbytes148 (init_bytes M) (l_img L) (hci5_p8_c_init_len M H1)).
  sep_apply (hci5_p8_c_hbytes148 (init_bytes M) (l_imga L) (hci5_p8_c_init_len M H1)).
  cancel.
Qed.

End Seg.
