(* law handshake, phase P5, segment D, part neg: NEG (CHECK(ret == NULL && hs_same(&snap, &pb.handshake) && pb.refcount.refcount == 1)).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.handshake.hhs3_spec.
Require Import WgNoise.proof.harness.handshake.hhs3_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_conv.
Require Import WgNoise.proof.harness.handshake.hhs3_p5_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_p5_D_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_p5_acc.
Require Import WgNoise.proof.harness.handshake.hhs3_p5_D_put.
Require Import WgNoise.proof.harness.handshake.hhs3_p5_D_ca_view.
Require Import WgNoise.proof.harness.handshake.hhs3_p5_D_cc_view.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Lemma hhs3_p5_D_neg_snap_refl sn : snap_eqb sn sn = true.
Proof.
  destruct sn as [[ep et ei] nx hd [st lic sid eph rs reph ss psk h ck ts ri]].
  unfold snap_eqb, entry_eqb, hs_eqb; cbn [sn_entry sn_next sn_hashed sn_hs e_peer e_type e_index
    hs_state hs_lic hs_sid hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts hs_rindex].
  rewrite !if_true by auto. rewrite !Int.eq_true, Int64.eq_true, !hhs3_p5_D_ca_view_eqb_refl.
  destruct hd; reflexivity.
Qed.

Lemma hhs3_p5_D_neg_sfind1 {A: Type} a sh (v: A) : sfind [(a, sh, v)] a = Some (sh, v).
Proof. simpl. rewrite if_true by auto. reflexivity. Qed.

Lemma hhs3_p5_D_neg_sid x25519 aead_enc R L I M1 H1 MI :
  x25519_props x25519 -> hhs3_run_ok R -> hhs3_after_init x25519 aead_enc R L I M1 H1 MI ->
  hs_sid H1 = id_addr (l_wa L).
Proof.
  intros Hx HR (Hok & Hci & Hmi & _ & _ & Hr & _).
  pose proof (hhs3_p5_acc_agree x25519 aead_enc R L I Hx HR Hr Hok) as A.
  rewrite Hmi in A. destruct MI as [[[[[E encs] enct] ep] ck] h].
  rewrite Hci in A. injection A as _ EH. rewrite EH. reflexivity.
Qed.

Lemma hhs3_p5_D_neg_cmp x25519 R L I M1 H1 :
  hs_sid H1 = id_addr (l_wa L) ->
  hs_cmp_pre (hhs3_p5_snap x25519 R L I M1 H1) (hhs3_TA1 L I) (l_pb L) (l_wa L) (hhs3_PB1 x25519 R L M1 H1)
    (hhs3_p5_EB1 L I).
Proof.
  intros Hsid. unfold hs_cmp_pre, hhs3_p5_snap, snap_of. cbn [sn_entry sn_hs sn_next].
  split; [| split; [| split; [| split; [| split]]]].
  - rewrite hhs3_p5_D_cc_view_TA1. unfold t_entry. cbn [t_D]. rewrite hhs3_p5_D_neg_sfind1. reflexivity.
  - reflexivity.
  - reflexivity.
  - exact Hsid.
  - exact Hsid.
  - left. rewrite hhs3_p5_D_cc_view_TA1. cbn [t_L succ_in]. rewrite if_true by auto. reflexivity.
Qed.

Section Part.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p5_D_neg_ok {Espec: OracleKind} gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb PA1 CI1 CI2 Q M2 H2 MR nowa (Rp: ret_assert) :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hhs3_p5_D_N x25519 aead_enc aead_dec gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb PA1 CI1 CI2 Q M2 H2 MR nowa)
    (hhs3_p5_D_neg)
    (overridePost (hhs3_p5_D_N x25519 aead_enc aead_dec gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb PA1 CI1 CI2 Q M2 H2 MR nowa) Rp).
Proof.
  intros HH. destruct Rp as [Rn Rb Rc Rr]. unfold overridePost.
  unfold hhs3_p5_D_N, hhs3_Delta, hhs3_p5_D_neg.
  simplify_func_tycontext.
  unfold hhs3_p5_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
  abbreviate_semax.
  Intros.
  pose proof HH as (HX & _).
  assert (Hcmp := hhs3_p5_D_neg_cmp x25519 R L I M1 H1 (hhs3_p5_D_neg_sid x25519 aead_enc R L I M1 H1 MI HX H H3)).
  assert (Er: p_refs (hhs3_PB1 x25519 R L M1 H1) = Int.one) by reflexivity.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  + apply ENTAIL_refl.
  + match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HC._t'138 (Vint Int.one) :: Q) (SEPx R))) end.
    { forward_call (Tsh, l_snap L, hhs3_p5_snap x25519 R L I M1 H1, Tsh, l_pb L, hhs3_PB1 x25519 R L M1 H1,
                    Tsh, l_ita L, hhs3_TA1 L I, hhs3_p5_EB1 L I, Tsh, l_wa L, hhs3_DA x25519 R L).
      change (snap_of (hhs3_TA1 L I) (hs_addr (l_pb L)) (hhs3_p5_EB1 L I) (p_hs (hhs3_PB1 x25519 R L M1 H1)))
        with (hhs3_p5_snap x25519 R L I M1 H1).
      rewrite hhs3_p5_D_neg_snap_refl. forward. entailer!. }
    { exfalso. auto. }
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HC._t'140 (Vint Int.one) :: Q) (SEPx R))) end.
    { rewrite (hhs3_p5_D_put_split Tsh (l_pb L) (hhs3_PB1 x25519 R L M1 H1)). Intros.
      rewrite Er. forward. forward. entailer!.
      rewrite (hhs3_p5_D_put_split Tsh (l_pb L) (hhs3_PB1 x25519 R L M1 H1)), Er. entailer!. }
    { exfalso. match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
    forward_if.
    { forward_call tt. all: [> exfalso; match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end | entailer!]. }
    forward. entailer!.
  + forward. apply ENTAIL_refl.
  + unfold POSTCONDITION, abbreviate. simpl RA_normal. entailer!.
Qed.

End Part.
