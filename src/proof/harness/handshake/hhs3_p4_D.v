(* law handshake, phase P4, segment D.
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
Require Import WgNoise.proof.harness.handshake.hhs3_p4_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Lemma hhs3_p4_D_ilen M : im_ok M -> Zlength (init_bytes M) = 148.
Proof.
  intros (A & B & C & D & E). unfold init_bytes. rewrite !Zlength_app, A, B, C, D, E. reflexivity.
Qed.

Lemma hhs3_p4_D_init_len sh m M : init_rep sh m M |-- !! (Zlength (init_bytes M) = 148).
Proof. unfold init_rep. Intros. apply prop_right. apply hhs3_p4_D_ilen; auto. Qed.

Lemma hhs3_p4_D_init_free sh m M : init_rep sh m M |-- @data_at_ W_handshake sh t_init m.
Proof. unfold init_rep. Intros. rewrite <- hhs3_conv_init. apply data_at_data_at_. Qed.

Lemma hhs3_p4_D_resp_free sh m M : resp_rep sh m M |-- @data_at_ W_handshake sh t_resp m.
Proof. unfold resp_rep. Intros. rewrite <- hhs3_conv_resp. apply data_at_data_at_. Qed.

Lemma hhs3_p4_D_rlen M : rm_ok M -> Zlength (resp_bytes M) = 92.
Proof.
  intros (A & B & C & D). unfold resp_bytes. rewrite !Zlength_app, A, B, C, D. reflexivity.
Qed.

Lemma hhs3_p4_D_hout sh bs p n : Zlength bs = n -> hbytes sh bs p |-- hout sh n p.
Proof. intros <-. unfold hbytes, hout. apply data_at_data_at_. Qed.

Lemma hhs3_p4_D_snap_out sh v p : @data_at HCS sh t_hsnap v p |-- @data_at_ HCS sh t_hsnap p.
Proof. apply data_at_data_at_. Qed.

Lemma hhs3_p4_D_TA1 L I : exists Ea, t_D (hhs3_TA1 L I) = [(hs_addr (l_pb L), Tsh, Ea)].
Proof.
  unfold hhs3_TA1, t_insert, t_set_index, hhs3_TA0, t_upd, t_entry. simpl.
  destruct (EqDec_val (hs_addr (l_pb L)) (hs_addr (l_pb L))); [| congruence]. simpl. eauto.
Qed.

Section P4D.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p4_D_ok {Espec: OracleKind} gv L FR :
  hhs3_p4_free_stmt x25519 ->
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p4_SC x25519 aead_enc aead_dec gv L FR) hhs3_p4_D
    (overridePost (hhs3_p4_SD x25519 aead_enc aead_dec gv L FR) (hhs3_R gv)).
Proof.
  intros HF HH. unfold hhs3_p4_SC, hhs3_p4_SD, hhs3_p4_SDE, hhs3_Delta, hhs3_R, hhs3_p4_D.
  apply hhs3_post_canon.
  simplify_func_tycontext. abbreviate_semax.
  Intros R S m1 m2 a0 f0 l0 I M1 H1 MI.
  Intros nowb PA1 CI1 CI2 Q ok2 M H MR aok.
  unfold hhs3_p4_sep, hhs3_setup_sep, hhs3_globs, hhs3_lvars, hhs3_cnt_temps. cbn [app].
  destruct ok2.
  - forward_if.
    { exfalso. apply Int.one_not_zero. assumption. }
    { forward.
      match goal with Hx: true = true -> aok = _ |- _ => rewrite (Hx eq_refl) end.
      Exists R S m1 m2 a0 f0 l0 I.
      Exists M1 H1 MI nowb PA1 CI1 CI2.
      Exists Q M H MR.
      unfold hhs3_p4_sep, hhs3_setup_sep, hhs3_globs, hhs3_lvars, hhs3_cnt_temps. cbn [app].
      entailer!. }
  - forward_if.
    2: { exfalso. auto. }
    assert (RM0: rm_ok (s_M0 Q)) by assumption.
    assert_PROP (Zlength (init_bytes (hhs3_M1m x25519 R M1)) = 148) as LI.
    { sep_apply (hhs3_p4_D_init_len Ews m1 (hhs3_M1m x25519 R M1)). entailer!. }
    sep_apply (hhs3_p4_D_init_free Ews m1 (hhs3_M1m x25519 R M1)).
    sep_apply (hhs3_p4_D_resp_free Ews m2 M).
    unfold hhs3_tok.
    assert_PROP (isptr m1 /\ isptr m2) as Pm12 by entailer!. destruct Pm12 as [Pm1 Pm2].
    sep_apply (hhs3_p4_D_hout Tsh _ (l_rimgb L) 92 (hhs3_p4_D_rlen _ RM0)).
    sep_apply (hhs3_p4_D_snap_out Tsh (hsnap_val (hhs3_p4_snap L PA1)) (l_snap L)).
    destruct MI as [[[[[E encs] enct] ep] ck] h].
    sep_apply (@data_at_data_at_ HCS Tsh t_minit (minit_val E encs enct ep ck h) (l_mi L)).
    destruct CI1 as [[[s k] ck1] h1]. destruct CI2 as [[t ck2] h2].
    sep_apply (@data_at_data_at_ HCS Tsh t_mcinit
      (mcinit_val ck2 h2 (bytes (kdf2 ck1 (hhs3_ssb x25519 R))) (bytes s) (bytes t)) (l_ci L)).
    forward_call (t_init, m1, gv).
    { rewrite if_false by (intro; subst; contradiction). cancel. }
    forward_call (t_resp, m2, gv).
    { rewrite if_false by (intro; subst; contradiction). cancel. }
    forward.
    destruct (hhs3_p4_D_TA1 L I) as [Ea HEa].
    eapply derives_trans; [| eapply derives_trans;
      [apply (HF (proj1 HH) gv L FR R S (hhs3_TA1 L I) (hhs3_TB0 L) Ea (hhs3_EA L)
                 (hhs3_PB1 x25519 R L M1 H1) (p_set_hs (hhs3_PA2 PA1) H) H0 HEa eq_refl) | ]].
    { unfold hhs3_setup_sep, hhs3_globs, hhs3_scr_tmp. simpl fold_right_sepcon. cancel. }
    { unfold hhs3_p4_frame. simpl fold_right_sepcon. cancel. }
Qed.

End P4D.

