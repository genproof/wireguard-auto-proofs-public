(* law cookie_reply: phase P1 of main, statements
   0..10: peers / cns = NULL, boot clock, wg_noise_init, raw keys, setup_device x2, m_identity_of(ib, raw_b), B's cookie secret and its birthdate.

   (+ its children's files). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p1_lemmas.
Require Import WgNoise.proof.libc.libc_bytes.
Require WgNoise.harness.x_cookie_reply.code.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

Section Phase.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_P1_ok {Espec: OracleKind} gv L FR :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcy5_S0 gv L FR) hcy5_P1
    (overridePost (hcy5_S1 x25519 gv L FR) (hcy5_R gv)).
Proof.
  intros HH. unfold hcy5_S0, hcy5_Delta, hcy5_R, hcy5_P1. simplify_func_tycontext. abbreviate_semax.
  unfold hcy5_lvars.
  forward. forward.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
  forward_call tt. Intros boot. unfold shim_state4 at 1. unfold shim_core at 1. Intros.
  unfold hcy5_shim0 at 1. cbn [s_boot].
  rewrite (@hcy5_p1_tulong_cs Noise.CS W_cookie_reply _ _ (gv _wg_shim_boottime_ns)).
  change _wg_shim_boottime_ns with HY._wg_shim_boottime_ns. forward.
  rewrite (@hcy5_p1_tulong_cs W_cookie_reply Noise.CS _ _ (gv HY._wg_shim_boottime_ns)).
  change HY._wg_shim_boottime_ns with _wg_shim_boottime_ns.
  sep_apply (hcy5_p1_shim_fold gv (hcy5_p1_set_boot hcy5_shim0 boot) H0).
  assert (FS: forall S, shim_core gv S * refwarn4 gv hcy5_w0 |-- shim_state4 gv S hcy5_w0)
    by (intros; unfold shim_state4; cancel).
  sep_apply FS. clear FS.
  forward_call (gv, zeros32, zeros32, Int64.zero).
  forward_call (l_rawa L, 32, Tsh). Intros bsA.
  forward_call (l_rawb L, 32, Tsh). Intros bsB.
  rewrite (hcy5_p1_nd _ _ _ _ H1 H2), (hcy5_p1_nd _ _ _ _ H3 H4).
  assert (LA: Zlength (map Byte.repr bsA) = 32) by (rewrite Zlength_map; auto).
  assert (LB: Zlength (map Byte.repr bsB) = 32) by (rewrite Zlength_map; auto).
  rewrite !hcy5_p1_conv_dev, !hcy5_p1_conv_itab, !hcy5_p1_conv_ptab, hcy5_p1_conv_mident, hcy5_p1_conv_skb,
    !hcy5_p1_conv_bytes.
  forward_call (gv, hcy5_p1_set_boot hcy5_shim0 boot, hcy5_w0, Tsh, l_wa L, l_ita L, l_pta L, Tsh, l_rawa L,
    map Byte.repr bsA).
  Intros secA.
  forward_call (gv, shim_draw (hcy5_p1_set_boot hcy5_shim0 boot) secA, hcy5_w0, Tsh, l_wb L, l_itb L, l_ptb L,
    Tsh, l_rawb L, map Byte.repr bsB).
  Intros secB.
  change (s_boot (hcy5_p1_set_boot hcy5_shim0 boot)) with boot.
  change (s_boot (shim_draw (hcy5_p1_set_boot hcy5_shim0 boot) secA)) with boot.
  unfold hcy5_consts. repeat flatten_sepcon_in_SEP.
  forward_call (gv, Tsh, l_ib L, Tsh, l_rawb L, map Byte.repr bsB).
  set (RA := map Byte.repr bsA) in *. set (RB := map Byte.repr bsB) in *.
  set (DA := setup_dev x25519 (l_wa L) (l_ita L) (l_pta L) RA secA boot).
  set (DB := setup_dev x25519 (l_wb L) (l_itb L) (l_ptb L) RB secB boot).
  rewrite (hcy5_p1_dev_split Tsh (l_wb L) DB).
  assert_PROP (@field_compatible Noise.CS t_dev [] (l_wb L)) as FCB by (unfold hcy5_drest; entailer!).
  rewrite (hcy5_p1_cc_open Tsh (l_wb L)) by exact FCB. Intros.
  pose proof H7 as (LsB & LeB & LmB).
  sep_apply (hcy5_p1_hbytes_free Tsh (cc_secret (d_cc DB)) (cc_addr (l_wb L))). rewrite LsB.
  forward_call (cc_addr (l_wb L), 32, Tsh). Intros bsS.
  rewrite (hcy5_p1_nd _ _ _ _ H8 H9).
  forward_call tt. Intros birth.
  forward.
  set (CC1 := mkChk (map Byte.repr bsS) (cc_ekey (d_cc DB)) (cc_mkey (d_cc DB)) birth (cc_dev (d_cc DB))).
  assert (HCC1: cc_ok CC1) by (split; [unfold CC1; simpl; rewrite Zlength_map; auto | split; auto]).
  rewrite (hcy5_p1_ccrest_eq Tsh (cc_addr (l_wb L)) (d_cc DB) CC1) by reflexivity.
  change (hbytes Tsh (map Byte.repr bsS) (cc_addr (l_wb L))) with (hbytes Tsh (cc_secret CC1) (cc_addr (l_wb L))).
  change (Vlong birth) with (Vlong (cc_birth CC1)).
  sep_apply (hcy5_p1_cc_close Tsh (l_wb L) CC1 FCB HCC1).
  unfold hcy5_S1.
  Exists (mkRun RA RB secA secB boot (map Byte.repr bsS) birth)
         (shim_draw (shim_draw (hcy5_p1_set_boot hcy5_shim0 boot) secA) secB).
  unfold hcy5_aside0, hcy5_bside, hcy5_bufs, hcy5_scrA, hcy5_snaps0, hcy5_globs, hcy5_consts, hcy5_lvars.
  cbn [app r_rawa r_rawb r_seca r_secb r_boot0 r_secret r_birth].
  change (hcy5_DA x25519 _ L) with DA. change (hcy5_DB x25519 _ L) with DB.
  change (hcy5_CC1 x25519 _ L) with CC1. change (hcy5_IB x25519 _) with (mident_of x25519 RB).
  entailer!.
  unfold hcy5_run_ok; cbn [r_rawa r_rawb r_seca r_secb r_boot0 r_secret r_birth].
  rewrite Zlength_map. repeat split; auto; lia.
Qed.

End Phase.
