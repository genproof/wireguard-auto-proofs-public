(* law consume_response_any, phase P7: statements 15..17 of main: kents_free(kes); hnodes_free(peers); return 0.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_cut.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_model.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_spec.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_conv.
Require WgNoise.harness.x_consume_response_any.code.

#[local] Existing Instance W_consume_response_any.
Local Open Scope logic.

Lemma hcr5_p7_hnodes_ptr l NS : @hnodes_rep4 W_consume_response_any l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [|N NS]; simpl.
  - entailer!.
  - Intros nx. subst l. entailer!.
    match goal with Hf: field_compatible _ _ (hn_addr N) |- _ => apply field_compatible_isptr in Hf end.
    destruct (hn_addr N); simpl in *; auto; contradiction.
Qed.

#[local] Hint Resolve hcr5_p7_hnodes_ptr : saturate_local.

Lemma hcr5_p7_hb (bs: list byte) (n: Z) (p: val) :
  Zlength bs = n -> hbytes Tsh bs p |-- @data_at_ W_consume_response_any Tsh (tarray tuchar n) p.
Proof.
  intros <-. unfold hbytes. sep_apply (@data_at_data_at_ HCS). rewrite <- hcr5_conv_bytes. apply derives_refl.
Qed.

Lemma hcr5_p7_mid (v: reptype t_mident) (p: val) :
  @data_at HCS Tsh t_mident v p |-- @data_at_ W_consume_response_any Tsh t_mident p.
Proof. sep_apply (@data_at_data_at_ HCS). rewrite hcr5_conv_mident. apply derives_refl. Qed.

Lemma hcr5_p7_ptab (h p: val) : ptable Tsh p h |-- @data_at_ W_consume_response_any Tsh t_ptab p.
Proof. unfold ptable. sep_apply (@data_at_data_at_ Noise.CS). rewrite hcr5_conv_ptab. apply derives_refl. Qed.

Section Phase.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcr5_P7_ok {Espec: OracleKind} gv L FR :
  hcr5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> hcr5_closeH -> 
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_SE x25519 gv L FR) hcr5_P7
    (overridePost FF (hcr5_R gv)).
Proof.
  intros HH HC. unfold hcr5_SE, hcr5_Delta, hcr5_R, hcr5_P7. apply hcr5_post_canon.
  simplify_func_tycontext. abbreviate_semax.
  Intros R S NS NS' PS head T KE.
  unfold hcr5_lvars, hcr5_scr, hcr5_snaps0, hcr5_world, hcr5_globs; cbn [app].
  destruct HC as [HCd HCt].
  sep_apply (HCt (l_ita L) KE PS NS' T H2 H0 H3).
  sep_apply (HCd Tsh (l_wa L) (hcr5_DAL x25519 R L)).
  forward_call (gv, hcr5_khead KE, KE).
  forward.
  forward_call (gv, hcr5_head NS, NS').
  forward.
  destruct H as (Hra & Hrb & _).
  sep_apply (hcr5_p7_hb (r5_rawa R) 32 (l_rawa L) Hra).
  sep_apply (hcr5_p7_hb (r5_rawb R) 32 (l_rawb L) Hrb).
  sep_apply (hcr5_p7_mid (mident_val (hcr5_IA x25519 R)) (l_ia L)).
  sep_apply (hcr5_p7_mid (mident_val (hcr5_IB x25519 R)) (l_ib L)).
  sep_apply (hcr5_p7_ptab head (l_pta L)).
  sep_apply (data_at_data_at_ Tsh (tptr t_hnode4) (hcr5_head NS) (l_peers L)).
  rewrite !hcr5_conv_bytes, hcr5_conv_dev, hcr5_conv_itab, !hcr5_conv_mstate, hcr5_conv_mresp,
    hcr5_conv_devsnap, hcr5_conv_shimsnap.
  cancel.
Qed.

End Phase.
