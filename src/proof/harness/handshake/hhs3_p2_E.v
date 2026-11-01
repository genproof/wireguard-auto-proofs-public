(* law handshake: main's phase P2, segment E (statements 59..65): hhs3_p2_SC x25519 aead_enc gv L FR -> hhs3_S2 x25519 aead_enc gv L FR.
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
Require Import WgNoise.proof.harness.handshake.hhs3_p2_defs.
Require WgNoise.harness.x_handshake.code.
Require WgNoise.proof.blake2s.model.
Require WgNoise.proof.blake2s.spec.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Helpers                                                                 *)
(* ---------------------------------------------------------------------- *)
Local Open Scope logic.

Lemma hhs3_p2_E_tuchar_cs {cs1 cs2: compspecs} sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible, size_compatible, align_compatible. destruct p; simpl; try tauto.
  assert (A: forall ce, align_compatible_rec ce (tarray tuchar n) (Ptrofs.unsigned i)).
  { intros ce. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  pose proof (A (@cenv_cs cs1)). pose proof (A (@cenv_cs cs2)). tauto.
Qed.

#[local] Instance hhs3_p2_E_CCE : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.

(* pure facts *)
Lemma hhs3_p2_E_MAC_len key m : Zlength (MAC key m) = 16.
Proof. unfold MAC, WgNoise.proof.blake2s.model.blake2s, WgNoise.proof.blake2s.model.b2s_digest_stream, WgNoise.proof.blake2s.model.b2s_out. rewrite Zlength_map. reflexivity. Qed.

Lemma hhs3_p2_E_lk_len l pub : Zlength (label_key l pub) = 32.
Proof. unfold label_key, WgNoise.proof.blake2s.model.blake2s, WgNoise.proof.blake2s.model.b2s_digest_stream, WgNoise.proof.blake2s.model.b2s_out. rewrite Zlength_map. reflexivity. Qed.

Lemma hhs3_p2_E_le32_len v : Zlength (le32 v) = 4.
Proof. reflexivity. Qed.

Lemma hhs3_p2_E_init_len M : im_ok M -> Zlength (init_bytes M) = 148.
Proof.
  intros (L1 & L2 & L3 & L4 & L5). unfold init_bytes.
  rewrite !Zlength_app, !hhs3_p2_E_le32_len, L1, L2, L3, L4, L5. reflexivity.
Qed.

Lemma hhs3_p2_E_init_split M : im_ok M ->
  init_bytes M = sublist 0 116 (init_bytes M) ++ im_mac1 M ++ im_mac2 M.
Proof.
  intros (L1 & L2 & L3 & L4 & L5). unfold init_bytes.
  pose proof (hhs3_p2_E_le32_len (im_type M)). pose proof (hhs3_p2_E_le32_len (im_sender M)).
  list_solve.
Qed.

Lemma hhs3_p2_E_macs_bytes M a b : im_ok M -> Zlength a = 16 ->
  init_bytes (im_set_macs M a b) = sublist 0 116 (init_bytes M) ++ a ++ b.
Proof.
  intros (L1 & L2 & L3 & L4 & L5) La. unfold init_bytes, im_set_macs; cbn [im_type im_sender im_eph im_encs im_enct im_mac1 im_mac2].
  pose proof (hhs3_p2_E_le32_len (im_type M)). pose proof (hhs3_p2_E_le32_len (im_sender M)).
  list_solve.
Qed.

Lemma hhs3_p2_E_macs_ok M a : im_ok M -> Zlength a = 16 -> im_ok (im_set_macs M a (zeros 16)).
Proof.
  intros (L1 & L2 & L3 & L4 & L5) La. unfold im_ok, im_set_macs; cbn [im_type im_sender im_eph im_encs im_enct im_mac1 im_mac2].
  repeat split; auto.
Qed.

Lemma hhs3_p2_E_mac1 key msg : Zlength msg = 148 -> mac1_of key msg = MAC key (sublist 0 116 msg).
Proof. intros H. unfold mac1_of. rewrite H. reflexivity. Qed.

Lemma hhs3_p2_E_addmac C msg now : ck_valid C = false -> Zlength msg = 148 ->
  add_mac_model C msg now =
  (sublist 0 116 msg ++ mac1_of (ck_mkey C) msg ++ zeros 16, ck_sent_mac1 C (mac1_of (ck_mkey C) msg)).
Proof.
  intros Hv Hl. unfold add_mac_model. rewrite Hv. cbn [andb]. rewrite Hl.
  assert (Lm: Zlength (mac1_of (ck_mkey C) msg) = 16) by (unfold mac1_of; apply hhs3_p2_E_MAC_len).
  f_equal; [list_solve | unfold ck_sent_mac1; rewrite Hv; reflexivity].
Qed.

Lemma hhs3_p2_E_eqb_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

(* byte buffers *)
Lemma hhs3_p2_E_ers_split bs p : hbytes Tsh bs p = hbytes Ers bs p * hbytes (Share.comp Ers) bs p.
Proof. unfold hbytes. symmetry. apply data_at_share_join. apply join_comp_Tsh. Qed.

Lemma hhs3_p2_E_hout sh bs p : hbytes sh bs p |-- hout sh (Zlength bs) p.
Proof. unfold hbytes, hout. apply data_at_data_at_. Qed.

Lemma hhs3_p2_E_hin sh bs p : Zlength bs <> 0 -> hin sh bs p = hbytes sh bs p.
Proof. intros H. unfold hin. destruct (Z.eq_dec (Zlength bs) 0); [contradiction | reflexivity]. Qed.

Lemma hhs3_p2_E_img3 sh A B C p : Zlength A = 116 -> Zlength B = 16 -> Zlength C = 16 ->
  @field_compatible HCS (tarray tuchar 148) [] p ->
  hbytes sh (A ++ B ++ C) p = hbytes sh A p * hbytes sh B (offset_val 116 p) * hbytes sh C (offset_val 132 p).
Proof.
  intros LA LB LC FC.
  pose proof (proj1 (field_compatible_Tarray_split tuchar 116 148 p ltac:(lia)) FC) as [FC1 FC2].
  rewrite arr_field_address0 in FC2 by (auto; lia). simpl (148 - 116) in FC2. simpl (sizeof tuchar * 116) in FC2.
  unfold hbytes. rewrite !Zlength_app, LA, LB, LC. simpl (116 + (16 + 16)). unfold bytes. rewrite !map_app.
  rewrite (split2_data_at_Tarray_app 116 148 sh tuchar (map Vubyte A)) by list_solve.
  rewrite arr_field_address0 by (auto; lia). simpl (148 - 116). simpl (sizeof tuchar * 116).
  rewrite (split2_data_at_Tarray_app 16 32 sh tuchar (map Vubyte B)) by list_solve.
  rewrite arr_field_address0 by (auto; lia). simpl (32 - 16). simpl (sizeof tuchar * 16).
  rewrite offset_offset_val. simpl (116 + 16). rewrite sepcon_assoc. reflexivity.
Qed.

(* the harness identity struct: its public key as a byte buffer (offset 32) and the rest *)
Definition hhs3_p2_E_irest (sh: share) (p: val) (I: mident) : mpred :=
  !! @field_compatible HCS t_mident [] p &&
  (@field_at HCS sh t_mident (DOT HH._priv) (bytes (mi_priv I)) p *
   @field_at HCS sh t_mident (DOT HH._ok) (Vint (if mi_ok I then Int.one else Int.zero)) p).

Lemma hhs3_p2_E_ib_open sh p I : Zlength (mi_pub I) = 32 ->
  @data_at HCS sh t_mident (mident_val I) p =
  hbytes sh (mi_pub I) (offset_val 32 p) * hhs3_p2_E_irest sh p I.
Proof.
  intros Hl. unfold hhs3_p2_E_irest, hbytes. rewrite Hl. apply pred_ext.
  - assert_PROP (@field_compatible HCS t_mident [] p) as FC by entailer!.
    unfold_data_at (@data_at HCS sh t_mident _ p).
    rewrite (@field_at_data_at HCS sh t_mident (DOT HH._pub)).
    rewrite field_address_offset by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset. entailer!.
  - Intros. rename H into FC.
    unfold_data_at (@data_at HCS sh t_mident _ p).
    rewrite (@field_at_data_at HCS sh t_mident (DOT HH._pub)).
    rewrite field_address_offset by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset. entailer!.
Qed.

(* the read-only globals: blake2s's sigma, the label constant *)
Definition hhs3_p2_E_wgrest (gv: globals) : mpred :=
  @curve25519_globals Noise.CS gv * @zero_page Noise.CS gv * cookie_globals gv.
Lemma hhs3_p2_E_wgc gv : wg_consts gv = WgNoise.proof.blake2s.spec.blake2s_globals gv * hhs3_p2_E_wgrest gv.
Proof. unfold wg_consts, hhs3_p2_E_wgrest. rewrite !sepcon_assoc. reflexivity. Qed.

Definition hhs3_p2_E_hcrest (gv: globals) : mpred :=
  hc_const gv HC._x_handshake__M_BASEPOINT basepoint9 *
  hc_const gv HC._x_handshake__M_CONSTRUCTION construction_bytes *
  hc_const gv HC._x_handshake__M_IDENTIFIER identifier_bytes *
  hc_const gv HC._x_handshake__M_LABEL_COOKIE cookie_label.
Lemma hhs3_p2_E_hcc gv : hhs3_consts gv =
  hbytes Ers mac1_label (gv HC._x_handshake__M_LABEL_MAC1) * hhs3_p2_E_hcrest gv.
Proof.
  unfold hhs3_consts, hhs3_p2_E_hcrest. change (hc_const gv HC._x_handshake__M_LABEL_MAC1 mac1_label)
    with (hbytes Ers mac1_label (gv HC._x_handshake__M_LABEL_MAC1)).
  apply pred_ext; cancel.
Qed.

Section Fields.
#[local] Existing Instance Noise.CS.

(* the peer without its cookie *)
Definition hhs3_p2_E_prest (sh: share) (p: val) (P: peer) : mpred :=
  !! field_compatible t_peer [] p &&
  (field_at sh t_peer [StructField I._device] (p_device P) p *
   field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   field_at sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   field_at sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   field_at sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   field_at sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Lemma hhs3_p2_E_peer_split sh p P :
  peer_rep sh p P = hhs3_p2_E_prest sh p P * cookie_rep sh (cookie_addr p) (p_cookie P).
Proof.
  unfold peer_rep, hhs3_p2_E_prest. apply pred_ext.
  - Intros. entailer!.
  - Intros. entailer!.
Qed.

Lemma hhs3_p2_E_ck_fc p : field_compatible t_peer [] p -> field_compatible t_cookie [] (cookie_addr p).
Proof.
  intros FC. pose proof (@field_compatible_app Noise.CS [] t_peer (DOT I._latest_cookie) p) as X.
  simpl app in X. specialize (X ltac:(auto with field_compatible)).
  rewrite field_address_offset in X by auto with field_compatible. exact X.
Qed.

(* the cookie without have_sent_mac1 and last_mac1_sent *)
Definition hhs3_p2_E_ckrest (sh: share) (c: val) (C: cookie) : mpred :=
  EX lk: val,
  field_at sh t_cookie (DOT I._birthdate) (Vlong (ck_birth C)) c *
  field_at sh t_cookie (DOT I._is_valid) (Val.of_bool (ck_valid C)) c *
  field_at sh t_cookie (DOT I._cookie) (bytes (ck_cookie C)) c *
  field_at sh t_cookie (DOT I._cookie_decryption_key) (bytes (ck_dkey C)) c *
  field_at sh t_cookie (DOT I._message_mac1_key) (bytes (ck_mkey C)) c *
  spacer sh 106 108 c * field_at sh t_cookie (DOT I._lock) lk c.

End Fields.

Lemma hhs3_p2_E_hsm sh p v : @field_compatible Noise.CS t_peer [] p ->
  @field_at Noise.CS sh t_cookie (DOT I._have_sent_mac1) v (cookie_addr p) =
  @field_at W_handshake sh t_peer (DOT HC._latest_cookie DOT HC._have_sent_mac1) v p.
Proof.
  intros FC. pose proof (hhs3_p2_E_ck_fc p FC) as FCc.
  assert (FCW: @field_compatible W_handshake t_peer [] p).
  { apply (@field_compatible_change_composite Noise.CS W_handshake _); [prove_cs_preserve_type | exact FC]. }
  rewrite !field_at_data_at. rewrite !field_address_offset by auto with field_compatible.
  unfold cookie_addr. rewrite offset_offset_val. simpl.
  apply equal_f, (@data_at_change_composite Noise.CS W_handshake _ sh tbool v v);
    [apply JMeq_refl | prove_cs_preserve_type].
Qed.

Lemma hhs3_p2_E_lm sh p bs : @field_compatible Noise.CS t_peer [] p -> Zlength bs = 16 ->
  @field_at Noise.CS sh t_cookie (DOT I._last_mac1_sent) (bytes bs) (cookie_addr p) =
  hbytes sh bs (offset_val 386 p).
Proof.
  intros FC Hl. pose proof (hhs3_p2_E_ck_fc p FC) as FCc.
  rewrite field_at_data_at. rewrite field_address_offset by auto with field_compatible.
  unfold cookie_addr. rewrite offset_offset_val. simpl. unfold hbytes. rewrite Hl.
  apply hhs3_p2_E_tuchar_cs.
Qed.

Lemma hhs3_p2_E_ck_open sh p C : @field_compatible Noise.CS t_peer [] p ->
  cookie_rep sh (cookie_addr p) C =
  !! cookie_ok C &&
  (@field_at W_handshake sh t_peer (DOT HC._latest_cookie DOT HC._have_sent_mac1) (Val.of_bool (ck_sent C)) p *
   hbytes sh (ck_last_mac1 C) (offset_val 386 p) * hhs3_p2_E_ckrest sh (cookie_addr p) C).
Proof.
  intros FC. pose proof (hhs3_p2_E_ck_fc p FC) as FCc.
  unfold cookie_rep, hhs3_p2_E_ckrest, cookie_val. apply pred_ext.
  - Intros lk. pose proof H as (L1 & L2 & L3 & L4).
    unfold_data_at (@data_at Noise.CS sh t_cookie _ (cookie_addr p)).
    rewrite hhs3_p2_E_hsm, hhs3_p2_E_lm by auto. Exists lk. entailer!.
  - Intros lk. pose proof H as (L1 & L2 & L3 & L4). Exists lk.
    unfold_data_at (@data_at Noise.CS sh t_cookie _ (cookie_addr p)).
    rewrite hhs3_p2_E_hsm, hhs3_p2_E_lm by auto. entailer!.
Qed.

Local Open Scope Z_scope.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p2_E_ok {Espec: OracleKind} gv L FR :
  hhs3_p2_agree_stmt x25519 aead_enc ->
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p2_SC x25519 aead_enc gv L FR) hhs3_p2_E
    (overridePost (hhs3_S2 x25519 aead_enc gv L FR) (hhs3_R gv)).
Proof.
  intros HA HH. unfold hhs3_p2_SC, hhs3_Delta, hhs3_R, hhs3_p2_E. simplify_func_tycontext. abbreviate_semax.
  Intros R S m1 m2 a0 f0 l0 I M1 H1 MI.
  unfold hhs3_p2_sepB, hhs3_lvars, hhs3_p2_scr, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
  destruct HH as (HX & _ & _ & _ & Hrep). destruct Hrep as (Rto & Rfrom & _).
  pose proof H2 as (Hok & Hci & Hmi & Hfr & Hm0 & Hr & Hns).
  assert_PROP (im_ok M1) as HM1 by (unfold init_rep; entailer!).
  assert_PROP (@field_compatible Noise.CS t_init [] m1) as FCm. { unfold init_rep. Intros. entailer!. }
  assert_PROP (@field_compatible Noise.CS t_peer [] (l_pb L)) as FCpb. { unfold peer_rep. Intros. entailer!. }
  assert_PROP (@field_compatible HCS (tarray tuchar 148) [] (l_img L)) as FCimg
    by (unfold hbytes; rewrite (hhs3_p2_E_init_len M1 HM1); entailer!).
  pose proof (hhs3_p2_E_init_len M1 HM1) as HL1.
  (* add_mac *)
  sep_apply (Rto Ews m1 M1).
  rewrite (hhs3_p2_E_peer_split Tsh (l_pb L)). flatten_sepcon_in_SEP.
  forward_call (gv, S, Ews, m1, init_bytes M1, Tsh, l_pb L, p_cookie (p_set_hs (hhs3_PB0 x25519 R L) H1)).
  { rewrite HL1. entailer!. }
  assert (Lm: Zlength (hhs3_mac1A x25519 R M1) = 16) by (unfold hhs3_mac1A, mac1_of; apply hhs3_p2_E_MAC_len).
  assert (Em: mac1_of (ck_mkey (p_cookie (p_set_hs (hhs3_PB0 x25519 R L) H1))) (init_bytes M1) = hhs3_mac1A x25519 R M1)
    by (unfold hhs3_mac1A, hhs3_PB0, setup_peer_val; cbn [p_cookie p_set_hs ck_mkey cookie_set_keys]; reflexivity).
  rewrite (hhs3_p2_E_addmac (p_cookie (p_set_hs (hhs3_PB0 x25519 R L) H1)) _ _ eq_refl HL1). cbn [fst snd]. rewrite Em.
  rewrite <- (hhs3_p2_E_macs_bytes M1 (hhs3_mac1A x25519 R M1) (zeros 16) HM1 Lm).
  sep_apply (Rfrom Ews m1 (im_set_macs M1 (hhs3_mac1A x25519 R M1) (zeros 16)) FCm (hhs3_p2_E_macs_ok M1 _ HM1 Lm)).
  change (im_set_macs M1 (hhs3_mac1A x25519 R M1) (zeros 16)) with (hhs3_M1m x25519 R M1).
  (* m_label_key *)
  rewrite hhs3_p2_E_wgc, hhs3_p2_E_hcc.
  assert (Hpub: Zlength (mi_pub (hhs3_IB x25519 R)) = 32) by (unfold hhs3_IB, mident_of; cbn [mi_pub]; apply HX).
  rewrite (hhs3_p2_E_ib_open Tsh (l_ib L) (hhs3_IB x25519 R) Hpub).
  rewrite (hhs3_p2_E_ers_split (mi_pub (hhs3_IB x25519 R)) (offset_val 32 (l_ib L))).
  repeat flatten_sepcon_in_SEP.
  forward_call (gv, Tsh, l_tmp L, Ers, gv HC._x_handshake__M_LABEL_MAC1, mac1_label, offset_val 32 (l_ib L), mi_pub (hhs3_IB x25519 R)).
  (* m_mac(img + 116, tmp, 32, img, 116) *)
  pose proof HM1 as (_ & _ & _ & Lma1 & Lma2).
  assert (L116: Zlength (sublist 0 116 (init_bytes M1)) = 116) by (rewrite Zlength_sublist by lia; lia).
  assert (EI: hbytes Tsh (init_bytes M1) (l_img L) =
    (hbytes Tsh (sublist 0 116 (init_bytes M1)) (l_img L) * hbytes Tsh (im_mac1 M1) (offset_val 116 (l_img L)) *
     hbytes Tsh (im_mac2 M1) (offset_val 132 (l_img L)))%logic).
  { rewrite (hhs3_p2_E_init_split M1 HM1) at 1. apply hhs3_p2_E_img3; auto. }
  rewrite EI. repeat flatten_sepcon_in_SEP.
  sep_apply (hhs3_p2_E_hout Tsh (im_mac1 M1) (offset_val 116 (l_img L))).
  sep_apply (hhs3_p2_E_hout Tsh (im_mac2 M1) (offset_val 132 (l_img L))).
  rewrite Lma1, Lma2.
  set (K := label_key mac1_label (mi_pub (hhs3_IB x25519 R))).
  assert (LK: Zlength K = 32) by apply hhs3_p2_E_lk_len.
  rewrite <- (hhs3_p2_E_hin Tsh K (l_tmp L)) by lia.
  rewrite <- (hhs3_p2_E_hin Tsh (sublist 0 116 (init_bytes M1)) (l_img L)) by lia.
  forward_call (gv, Tsh, offset_val 116 (l_img L), Tsh, l_tmp L, K, Tsh, l_img L, sublist 0 116 (init_bytes M1)).
  { rewrite LK, L116. entailer!. }
  rewrite (hhs3_p2_E_hin Tsh K (l_tmp L)) by lia.
  rewrite (hhs3_p2_E_hin Tsh (sublist 0 116 (init_bytes M1)) (l_img L)) by lia.
  (* bytes_set(img + 132, 0, 16) *)
  forward_call (Tsh, offset_val 132 (l_img L), Byte.zero, 16).
  assert (EM: MAC K (sublist 0 116 (init_bytes M1)) = hhs3_mac1A x25519 R M1)
    by (symmetry; exact (hhs3_p2_E_mac1 (label_key mac1_label (mi_pub (hhs3_IB x25519 R))) (init_bytes M1) HL1)).
  rewrite EM. change (Zrepeat Byte.zero 16) with (zeros 16).
  assert (EIMG: hbytes Tsh (init_bytes (hhs3_M1m x25519 R M1)) (l_img L) =
    (hbytes Tsh (sublist 0 116 (init_bytes M1)) (l_img L) *
     hbytes Tsh (hhs3_mac1A x25519 R M1) (offset_val 116 (l_img L)) *
     hbytes Tsh (zeros 16) (offset_val 132 (l_img L)))%logic).
  { unfold hhs3_M1m. rewrite (hhs3_p2_E_macs_bytes M1 (hhs3_mac1A x25519 R M1) (zeros 16) HM1 Lm).
    apply hhs3_p2_E_img3; [exact L116 | exact Lm | reflexivity | exact FCimg]. }
  sep_apply (derives_refl' _ _ (eq_sym EIMG)).
  pose proof (hhs3_p2_E_init_len _ (hhs3_p2_E_macs_ok M1 _ HM1 Lm)) as HL1m.
  change (im_set_macs M1 (hhs3_mac1A x25519 R M1) (zeros 16)) with (hhs3_M1m x25519 R M1) in HL1m.
  (* init_img(img_before, m1) *)
  sep_apply (hhs3_p2_E_hout Tsh (init_bytes (i_M0 I)) (l_imgb L)). rewrite (hhs3_p2_E_init_len _ Hm0).
  forward_call (Tsh, l_imgb L, Ews, m1, hhs3_M1m x25519 R M1).
  (* CHECK(bytes_eq(img, img_before, INIT_LEN)) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  - apply ENTAIL_refl.
  - forward_call (Tsh, l_img L, init_bytes (hhs3_M1m x25519 R M1), Tsh, l_imgb L, init_bytes (hhs3_M1m x25519 R M1)).
    { rewrite HL1m. entailer!. }
    rewrite hhs3_p2_E_eqb_refl.
    forward_if.
    + discriminate.
    + forward. entailer!.
  - forward. apply ENTAIL_refl.
  - (* CHECK(pb.latest_cookie.have_sent_mac1 && bytes_eq(last_mac1_sent, img + 116, 16)) *)
    rewrite (hhs3_p2_E_ck_open Tsh (l_pb L) _ FCpb). Intros.
    unfold ck_sent_mac1; cbn [ck_sent ck_last_mac1].
    rewrite EIMG. repeat flatten_sepcon_in_SEP.
    match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
    + apply ENTAIL_refl.
    + forward.
      forward_if (temp HC._t'57 (Vint Int.one)).
      { forward_call (Tsh, offset_val 386 (l_pb L), hhs3_mac1A x25519 R M1, Tsh, offset_val 116 (l_img L),
                      hhs3_mac1A x25519 R M1).
        rewrite hhs3_p2_E_eqb_refl. forward. entailer!. }
      { inv H5. }
      forward_if.
      { discriminate. }
      forward. entailer!.
    + forward. apply ENTAIL_refl.
    + assert (EPB1: hhs3_p2_E_prest Tsh (l_pb L) (hhs3_PB1 x25519 R L M1 H1) =
                    hhs3_p2_E_prest Tsh (l_pb L) (p_set_hs (hhs3_PB0 x25519 R L) H1)) by reflexivity.
      assert (ECK1: p_cookie (hhs3_PB1 x25519 R L M1 H1) =
                    ck_sent_mac1 (p_cookie (p_set_hs (hhs3_PB0 x25519 R L) H1)) (hhs3_mac1A x25519 R M1))
        by reflexivity.
      unfold POSTCONDITION, abbreviate. rewrite overridePost_normal'. unfold hhs3_S2.
      Exists R S m1 m2 a0 f0 l0 I M1 H1 MI.
      unfold hhs3_lvars, hhs3_scr_tmp, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
      rewrite (hhs3_p2_E_peer_split Tsh (l_pb L) (hhs3_PB1 x25519 R L M1 H1)), EPB1, ECK1.
      rewrite (hhs3_p2_E_ck_open Tsh (l_pb L) _ FCpb).
      rewrite hhs3_p2_E_wgc, hhs3_p2_E_hcc, (hhs3_p2_E_ib_open Tsh (l_ib L) (hhs3_IB x25519 R) Hpub),
        (hhs3_p2_E_ers_split (mi_pub (hhs3_IB x25519 R)) (offset_val 32 (l_ib L))), EIMG.
      sep_apply (hhs3_p2_E_hout Tsh K (l_tmp L)).
      sep_apply (hhs3_p2_E_hout Tsh (init_bytes (hhs3_M1m x25519 R M1)) (l_imgb L)). rewrite LK, HL1m.
      sep_apply (@data_at_data_at_ HCS Tsh t_hsnap
        (hsnap_val (snap_of (hhs3_TA0 L) (hs_addr (l_pb L)) (hhs3_EB L) (p_hs (hhs3_PB0 x25519 R L)))) (l_snap L)).
      unfold ck_sent_mac1; cbn [ck_sent ck_last_mac1].
      entailer!.
Qed.

End Seg.
