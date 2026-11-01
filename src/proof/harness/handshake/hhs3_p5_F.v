(* law handshake, phase P5, segment F.
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
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Lemma hhs3_p5_F_ilen M : im_ok M -> Zlength (init_bytes M) = 148.
Proof.
  intros (A & B & C & D & E). unfold init_bytes. rewrite !Zlength_app, A, B, C, D, E. reflexivity.
Qed.

Lemma hhs3_p5_F_init_free sh m M : init_rep sh m M |-- @data_at_ W_handshake sh t_init m.
Proof. unfold init_rep. Intros. rewrite <- hhs3_conv_init. apply data_at_data_at_. Qed.

Lemma hhs3_p5_F_resp_free sh m M : resp_rep sh m M |-- @data_at_ W_handshake sh t_resp m.
Proof. unfold resp_rep. Intros. rewrite <- hhs3_conv_resp. apply data_at_data_at_. Qed.

Lemma hhs3_p5_F_snap_out sh v p : @data_at HCS sh t_hsnap v p |-- @data_at_ HCS sh t_hsnap p.
Proof. apply data_at_data_at_. Qed.

Lemma hhs3_p5_F_TA1 L I : exists Ea, t_D (hhs3_TA1 L I) = [(hs_addr (l_pb L), Tsh, Ea)].
Proof.
  unfold hhs3_TA1, t_insert, t_set_index, hhs3_TA0, t_upd, t_entry. simpl.
  destruct (EqDec_val (hs_addr (l_pb L)) (hs_addr (l_pb L))); [| congruence]. simpl. eauto.
Qed.

Lemma hhs3_p5_F_TB1 L Q : exists Eb, t_D (hhs3_TB1 L Q) = [(hs_addr (l_pa L), Tsh, Eb)].
Proof.
  unfold hhs3_TB1, t_insert, t_set_index, hhs3_TB0, t_upd, t_entry. simpl.
  destruct (EqDec_val (hs_addr (l_pa L)) (hs_addr (l_pa L))); [| congruence]. simpl. eauto.
Qed.

Section P5F.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p5_F_ok {Espec: OracleKind} gv L FR :
  hhs3_p5_free_stmt x25519 ->
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p5_SD x25519 aead_enc aead_dec gv L FR) hhs3_p5_F
    (overridePost (hhs3_S5 x25519 aead_enc aead_dec gv L FR) (hhs3_R gv)).
Proof.
  intros HF HH. unfold hhs3_p5_SD, hhs3_Delta, hhs3_R, hhs3_p5_F. apply hhs3_post_canon.
  simplify_func_tycontext. abbreviate_semax.
  Intros R S m1 m2 a0 f0 l0 I M1 H1. Intros MI nowb PA1 CI1 CI2 Q M2 H2 MR. Intros nowa acc PB2 ST2.
  unfold hhs3_p5_sep, hhs3_setup_sep, hhs3_globs, hhs3_lvars, hhs3_cnt_temps. cbn [app].
  destruct acc.
  - forward_if.
    { exfalso. apply Int.one_not_zero. assumption. }
    forward.
    destruct (H9 eq_refl) as [C1 C2].
    sep_apply (hhs3_p5_F_snap_out Tsh (hsnap_val (hhs3_p5_snap x25519 R L I M1 H1)) (l_snap L)).
    unfold hhs3_S5.
    Exists R S m1 m2 a0 f0 l0 I M1 H1. Exists MI nowb PA1 CI1 CI2 Q M2 H2 MR. Exists nowa PB2 ST2.
    unfold hhs3_setup_sep, hhs3_globs, hhs3_scr_tmp, hhs3_lvars, hhs3_cnt_temps, hhs3_p5_st2. cbn [app].
    entailer!.
    unfold hhs3_after_cre. auto.
  - forward_if.
    2: { exfalso. auto. }
    sep_apply (hhs3_p5_F_init_free Ews m1 (hhs3_M1m x25519 R M1)).
    sep_apply (hhs3_p5_F_resp_free Ews m2 (hhs3_M2m x25519 R M2)).
    unfold hhs3_tok.
    assert_PROP (isptr m1 /\ isptr m2) as Pm12 by entailer!. destruct Pm12 as [Pm1 Pm2].
    forward_call (t_init, m1, gv).
    { rewrite if_false by (intro; subst; contradiction). cancel. }
    forward_call (t_resp, m2, gv).
    { rewrite if_false by (intro; subst; contradiction). cancel. }
    forward.
    sep_apply (hhs3_p5_F_snap_out Tsh (hsnap_val (hhs3_p5_snap x25519 R L I M1 H1)) (l_snap L)).
    destruct MI as [[[[[E encs] enct] ep] ck] h].
    sep_apply (@data_at_data_at_ HCS Tsh t_minit (minit_val E encs enct ep ck h) (l_mi L)).
    destruct MR as [[[[Er encn] epr] ckr] hr].
    sep_apply (@data_at_data_at_ HCS Tsh t_mresp (mresp_val Er encn epr ckr hr) (l_mr L)).
    unfold hhs3_p5_st2.
    destruct (hhs3_p5_F_TA1 L I) as [Ea HEa].
    destruct (hhs3_p5_F_TB1 L Q) as [Eb HEb].
    eapply derives_trans; [| eapply derives_trans;
      [apply (HF (proj1 HH) gv L FR R S (hhs3_TA1 L I) (hhs3_TB1 L Q) Ea Eb
                 (hhs3_PB1 x25519 R L M1 H1) (hhs3_PA3 x25519 R PA1 M2 H2) H HEa HEb) | ]].
    { unfold hhs3_setup_sep, hhs3_globs, hhs3_scr_tmp. simpl fold_right_sepcon. cancel. }
    { unfold hhs3_p5_frame. simpl fold_right_sepcon. cancel. }
Qed.

End P5F.
