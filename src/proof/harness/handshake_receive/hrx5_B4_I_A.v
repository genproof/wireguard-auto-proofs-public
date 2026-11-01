(* law handshake_receive, phase B4, segment I, part A:
   a1 = the three conditionals into t'97 (fwd, kind == 1, id.ok, the call m_consume_initiation_1(&ci, &id, mi->unencrypted_ephemeral, mi->encrypted_static)); port of hci5_p7_A (which had id.ok and the call only).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_cut.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mspec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require WgNoise.contracts.x_handshake_receive.
Require WgNoise.harness.x_handshake_receive.code.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
#[local] Existing Instance W_handshake_receive.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_defs.
Local Open Scope logic.

Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_I_pure.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_I_sep.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_I_defs.
Local Open Scope logic.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_B4_I_A_ok {Espec: OracleKind} gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B4_I_st x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img [] nullval (@data_at_ HCS Tsh t_mcinit (l_ci L)) (hout Tsh 32 (l_sst L)))
    hrx5_B4_I_a1
    (overridePost (hrx5_B4_I_Q1 x25519 aead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HH. unfold hrx5_B4_I_Q1, hrx5_B4_I_st, hrx5_B4_I_scr, hrx5_Delta, hrx5_RB, hrx5_B4_I_a1,
    hrx5_B4_I_c1f, hrx5_B4_I_c1, hrx5_B4_I_ci1, hrx5_B4_I_ok1, hrx5_ltemps, hrx5_ptrs, hrx5_lvars,
    hrx5_wcore, hrx5_rest, hrx5_globs.
  cbn [app obj_bytes obj_kind obj_rep obj_ok].
  destruct HH as (Hx & Ha & Hxa).
  destruct (hrx5_B4_I_len_ok x25519 aead_enc aead_dec Hx Ha) as (HlIB & Hl1 & Hlpre & Hl2).
  simplify_func_tycontext. abbreviate_semax.
  Intros.
  destruct (HlIB R (proj1 H)) as [HIBpriv HIBpub].
  destruct (hrx5_fwd (init_bytes M)) eqn:Hf.
  2: {
    match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?SS))) _ _ =>
      forward_if (PROPx [] (LOCALx (temp HM._t'95 (Vint Int.zero) :: Q) (SEPx SS))) end.
    1: hrx5_B4_I_absurd.
    1: forward; entailer!.
    match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?Q) (SEPx ?SS))) _ _ =>
      forward_if (PROPx [] (LOCALx (temp HM._t'96 (Vint Int.zero) :: Q) (SEPx SS))) end.
    1: hrx5_B4_I_absurd.
    1: forward; entailer!.
    match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?Q) (SEPx ?SS))) _ _ =>
      forward_if (PROPx [] (LOCALx (temp HM._t'97 (Vint Int.zero) :: Q) (SEPx SS))) end.
    1: hrx5_B4_I_absurd.
    1: forward; entailer!.
    destruct (hrx5_R gv). unfold loop1_ret_assert. cbv iota beta. cbn [tycontext.RA_normal].
    entailer!. }
  match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?SS))) _ _ =>
    forward_if (PROPx [] (LOCALx (temp HM._t'95 (Vint Int.one) :: Q) (SEPx SS))) end.
  1: forward; entailer!.
  1: hrx5_B4_I_absurd.
  match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?Q) (SEPx ?SS))) _ _ =>
    forward_if (PROPx [] (LOCALx (temp HM._t'96 (Vint (if mi_ok (hrx5_ID x25519 R) then Int.one else Int.zero)) :: Q) (SEPx SS))) end.
  2: hrx5_B4_I_absurd.
  1: {
       rewrite (hrx5_B4_I_mident_cs Tsh (hrx5_ID x25519 R)). forward. forward. rewrite <- hrx5_B4_I_mident_cs.
       entailer!. destruct (mi_ok (hrx5_ID x25519 R)); reflexivity. }
  destruct (mi_ok (hrx5_ID x25519 R)) eqn:Hok.
  2: {
    match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?Q) (SEPx ?SS))) _ _ =>
      forward_if (PROPx [] (LOCALx (temp HM._t'97 (Vint Int.zero) :: Q) (SEPx SS))) end.
    1: hrx5_B4_I_absurd.
    1: forward; entailer!.
    destruct (hrx5_R gv). unfold loop1_ret_assert. cbv iota beta. cbn [tycontext.RA_normal].
    entailer!. }
  unfold POSTCONDITION, abbreviate. destruct (hrx5_R gv). unfold loop1_ret_assert. cbv iota beta.
  cbn [tycontext.RA_normal].
  assert (H3c := H3); destruct H3c as (HlE & HlS & HlT & Hm1 & Hm2).
  destruct (m_consume_init1_model x25519 aead_dec (hrx5_ID x25519 R) (im_eph M) (im_encs M))
    as [[[[s key] ck1] h1]|] eqn:H1m.
  all: forward_if; [ | hrx5_B4_I_absurd].
  all: assert_PROP (isptr dp) as Hdp; [entailer! | ].
  all: sep_apply (hrx5_B4_I_msg_es Ews dp M); unfold hrx5_consts, wg_consts; Intros.
  all: forward_call (gv, Tsh, l_ci L, Zrepeat Vundef 12, Tsh, l_id L, hrx5_ID x25519 R, Ews, offset_val 8 dp, im_eph M,
                offset_val 40 dp, im_encs M).
  all: try solve [auto | split; auto].
  all: sep_apply (hrx5_B4_I_wand2 (hbytes Ews (im_eph M) (offset_val 8 dp)) (hbytes Ews (im_encs M) (offset_val 40 dp)) (init_rep Ews dp M)).
  all: rewrite H1m.
  all: forward.
  all: entailer!.
  all: first [ assumption | unfold hrx5_consts, wg_consts; cancel ].
Qed.

End Seg.
