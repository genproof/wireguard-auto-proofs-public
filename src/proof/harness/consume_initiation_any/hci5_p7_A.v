(* law consume_initiation_any, phase P7, segment A: target = NULL; t'96 = ib.ok; if (t'96) t'28 = (bool) m_consume_initiation_1(..) else t'28 = 0.  Port of v1's hci3_p7_A.v. *)
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
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p7_pure.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p7_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p7_sep.
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hci5_p7_A_ok {Espec: OracleKind} gv L FR R S w NS PS T head na KE m M :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hci5_Delta x25519 aead_enc aead_dec)
    (hci5_p7_st x25519 aead_dec gv L FR R S w NS PS T head na KE m M [] []
       (@data_at_ HCS Tsh t_mcinit (l_ci L)) (hout Tsh 32 (l_ss2 L)))
    (Ssequence hci5_p7_s29 hci5_p7_a1)
    (overridePost (hci5_p7_Q1 x25519 aead_dec gv L FR R S w NS PS T head na KE m M) (hci5_R gv)).
Proof.
  intros HH. unfold hci5_p7_Q1, hci5_p7_st, hci5_Delta, hci5_R, hci5_p7_s29, hci5_p7_a1,
    hci5_p7_c1, hci5_p7_ci1, hci5_p7_ok1, hci5_lvars, hci5_world, hci5_globs.
  cbn [app].
  destruct HH as (Hx & Ha & Hxa & Hrep).
  destruct (hci5_p7_len_ok x25519 aead_enc aead_dec Hx Ha) as (HlIB & Hl1 & Hlpre & Hl2).
  destruct (mi_ok (hci5_IB x25519 R)) eqn:Hok.
  2: {
    simplify_func_tycontext. abbreviate_semax. Intros.
    destruct (HlIB R H) as [HIBpriv HIBpub].
    forward.
    rewrite (hci5_p7_mident_cs Tsh (hci5_IB x25519 R)). forward. rewrite <- hci5_p7_mident_cs.
    rewrite Hok.
    forward_if. 1: { hci5_p7_absurd. }
    forward.
    entailer!. }
  destruct (m_consume_init1_model x25519 aead_dec (hci5_IB x25519 R) (im_eph M) (im_encs M))
    as [[[[s key] ck1] h1]|] eqn:H1m.
  all: simplify_func_tycontext; abbreviate_semax; Intros.
  all: destruct (HlIB R H) as [HIBpriv HIBpub].
  all: forward.
  all: rewrite (hci5_p7_mident_cs Tsh (hci5_IB x25519 R)); forward; rewrite <- hci5_p7_mident_cs.
  all: rewrite Hok.
  all: forward_if; [ | hci5_p7_absurd].
  all: assert_PROP (isptr m) as Hm; [entailer! | ].
  all: sep_apply (hci5_p7_msg_es Ews m M); unfold hci5_consts, wg_consts; Intros.
  all: forward_call (gv, Tsh, l_ci L, Zrepeat Vundef 12, Tsh, l_ib L, hci5_IB x25519 R, Ews, offset_val 8 m, im_eph M,
                offset_val 40 m, im_encs M);
       [ destruct H1 as (?&?&?&?&?); auto | ].
  all: sep_apply (hci5_p7_wand2 (hbytes Ews (im_eph M) (offset_val 8 m)) (hbytes Ews (im_encs M) (offset_val 40 m)) (init_rep Ews m M)).
  all: rewrite H1m.
  all: forward.
  all: entailer!.
  all: unfold hci5_consts, wg_consts; cancel.
Qed.

End Seg.
