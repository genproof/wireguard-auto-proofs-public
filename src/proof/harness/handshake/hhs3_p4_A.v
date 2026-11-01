(* law handshake, phase P4, segment A.
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

(* an equation kept out of reach of subst / entailer (hides a BLAKE2s term from forward_call) *)
Definition hhs3_p4_A_hide (P: Prop) : Prop := P.

Lemma hhs3_p4_A_log S r : Zlength r = 32 -> s_log (shim_draw S r) = r.
Proof.
  intros Hr. unfold shim_draw; cbn [s_log]. rewrite Hr. change (Z.min 32 32) with 32.
  rewrite sublist_same by auto. rewrite sublist_nil'. 2: reflexivity. apply app_nil_r.
Qed.

(* the two PROP facts of hs_take in the final spec layer (e_peer E <> Vundef, hs_sid (p_hs P) <> Vundef) *)
Lemma hhs3_p4_A_epeer L : isptr (l_pa L) -> e_peer (hhs3_EA L) <> Vundef.
Proof. intros Hp. unfold hhs3_EA; cbn [e_peer]. destruct (l_pa L); try contradiction; discriminate. Qed.

Section P4A.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p4_A_new_dev R L M1 nowb CI2 :
  p_device (hhs3_PA2 (hhs3_p4_new x25519 R L M1 nowb CI2)) = l_wb L /\
  hs_state (p_hs (hhs3_PA2 (hhs3_p4_new x25519 R L M1 nowb CI2))) = HS_CONSUMED_INITIATION /\
  hs_sid (p_hs (hhs3_PA2 (hhs3_p4_new x25519 R L M1 nowb CI2))) = id_addr (l_wb L).
Proof. destruct CI2 as [[t ck2] h2]. split; [|split]; reflexivity. Qed.

Lemma hhs3_p4_A_sid R L M1 nowb CI2 : isptr (l_wb L) ->
  hs_sid (p_hs (hhs3_PA2 (hhs3_p4_new x25519 R L M1 nowb CI2))) <> Vundef.
Proof.
  intros Hp. rewrite (proj2 (proj2 (hhs3_p4_A_new_dev R L M1 nowb CI2))).
  unfold id_addr. destruct (l_wb L); try contradiction; discriminate.
Qed.

Lemma hhs3_p4_A_ok {Espec: OracleKind} gv L FR :
  hhs3_p4_pa1_stmt x25519 aead_dec ->
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_S3 x25519 aead_enc aead_dec gv L FR) hhs3_p4_A
    (overridePost (hhs3_p4_SA x25519 aead_enc aead_dec gv L FR) (hhs3_R gv)).
Proof.
  intros Hpa1 HH. unfold hhs3_S3, hhs3_Delta, hhs3_R, hhs3_p4_A. simplify_func_tycontext. abbreviate_semax.
  Intros R S m1 m2 a0 f0 l0. Intros I M1 H1 MI nowb PA1 CI1 CI2.
  unfold hhs3_lvars, hhs3_scr_tmp, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
  destruct CI1 as [[[s k] ck1] h1]. destruct CI2 as [[t ck2] h2].
  destruct MI as [[[[[E encs] enct] ep] ck] h].
  assert (Hnew := Hpa1 _ _ _ _ _ _ _ H H3).
  destruct (hhs3_p4_A_new_dev R L M1 nowb (t, ck2, h2)) as (Hdev & Hst & Hsid).
  rewrite <- Hnew in Hdev, Hst, Hsid.
  remember (bytes (kdf2 ck1 (hhs3_ssb x25519 R))) as KK eqn:EKK.
  assert (HKK: hhs3_p4_A_hide (KK = bytes (kdf2 ck1 (hhs3_ssb x25519 R)))) by exact EKK.
  clear EKK Hnew.
  forward_call (Ews, m2). Intros M0.
  forward_call (Tsh, l_rimgb L, Ews, m2, M0).
  assert (HE: t_entry (hhs3_TB0 L) (hs_addr (l_pa L)) = Some (hhs3_EA L)).
  { unfold t_entry, hhs3_TB0; cbn [t_D sfind]. rewrite if_true by auto. reflexivity. }
  assert_PROP (isptr (l_pa L) /\ isptr (l_wb L)) as HPtr by entailer!.
  destruct HPtr as [HPa HPw].
  forward_call (Tsh, l_snap L, Tsh, l_pa L, hhs3_PA2 PA1, Tsh, l_itb L, hhs3_TB0 L, hhs3_EA L).
  { (* hs_take's round-4 side conditions *)
    split; [apply hhs3_p4_A_epeer; exact HPa
           | rewrite Hsid; unfold id_addr; destruct (l_wb L); try contradiction; discriminate]. }
  change (itable Tsh (l_itb L) (hhs3_TB0 L)) with (itable Tsh (d_itab (hhs3_DB x25519 R L)) (hhs3_TB0 L)).
  assert (HP: hs_in_pool (hhs3_TB0 L) (l_pa L)) by (exists (hhs3_EA L); split; [exact HE | reflexivity]).
  forward_call (gv, S, Ews, m2, M0, Tsh, l_pa L, hhs3_PA2 PA1, Tsh, l_wb L, hhs3_DB x25519 R L, Tsh, hhs3_TB0 L).
  Intros vret. destruct vret as [r idx]; cbn [fst snd] in *.
  assert (Ecr: cr_res x25519 aead_enc (hhs3_PA2 PA1) M0 r idx = hhs3_cr x25519 aead_enc PA1 (mkRsp M0 r idx))
    by reflexivity.
  rewrite Ecr in *.
  destruct (hhs3_cr x25519 aead_enc PA1 (mkRsp M0 r idx)) as [[ok2 M] Hs] eqn:Ecr2.
  cbn [fst snd] in *.
  rewrite Hst, Int.eq_true.
  forward.
  set (Sf := if ok2 then shim_u32 (shim_draw S r) idx else shim_draw S r).
  assert (Hcnt: hhs3_cnt Sf a0 f0 l0) by (subst Sf; destruct ok2; exact H0).
  assert (Hlog: s_log Sf = r) by (subst Sf; destruct ok2; apply hhs3_p4_A_log; auto).
  assert (Hu32: ok2 = true -> s_u32 Sf = idx) by (intros Ho; subst Sf; rewrite Ho; reflexivity).
  change (d_itab (hhs3_DB x25519 R L)) with (l_itb L).
  fold Sf.
  unfold hhs3_p4_SA, hhs3_p4_sep, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps, hhs3_lvars.
  Exists R Sf m1 m2 a0 f0 l0 I.
  Exists M1 H1 (E, encs, enct, ep, ck, h) nowb PA1 (s, k, ck1, h1) (t, ck2, h2).
  Exists (mkRsp M0 r idx) ok2 M Hs.
  cbn [app s_M0 s_r s_idx].
  unfold hhs3_p4_A_hide in HKK. subst KK.
  entailer!.
Qed.

End P4A.
