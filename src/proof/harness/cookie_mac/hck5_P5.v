(* law cookie_mac: main's phase P5, statements 59..67 of hck5_cut.v:
   v1 P5 (hck3_P5.v.old) without its first statement ck_take.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_mac.hck5_cut.
Require Import WgNoise.proof.harness.cookie_mac.hck5_spec.
Require Import WgNoise.proof.harness.cookie_mac.hck5_defs.
Require Import WgNoise.proof.harness.cookie_mac.hck5_conv.
Require WgNoise.harness.x_cookie_mac.code.

#[local] Existing Instance W_cookie_mac.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Helpers (v1 hck3_P5.v, renamed)                                        *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hck5_p5_cce_N : change_composite_env Noise.CS W_cookie_mac.
Proof. make_cs_preserve Noise.CS W_cookie_mac. Defined.
#[local] Instance hck5_p5_cce_K : change_composite_env CKS W_cookie_mac.
Proof. make_cs_preserve CKS W_cookie_mac. Defined.

Module HC := WgNoise.harness.x_cookie_mac.code.

(* byte arrays across compspecs (copied from libc_bytes.v) *)
Section Bytes.
Context {cs1 cs2: compspecs}.
Lemma hck5_p5_fc_cs n p :
  @field_compatible cs1 (tarray tuchar n) nil p <-> @field_compatible cs2 (tarray tuchar n) nil p.
Proof.
  assert (A: forall (ce: composite_env) z, align_compatible_rec ce (tarray tuchar n) z).
  { intros. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  unfold field_compatible, size_compatible, align_compatible.
  destruct p; simpl; try tauto.
  pose proof (A (@cenv_cs cs1) (Ptrofs.unsigned i)). pose proof (A (@cenv_cs cs2) (Ptrofs.unsigned i)).
  tauto.
Qed.
Lemma hck5_p5_data_at_cs sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof. unfold data_at, field_at. f_equal. f_equal. apply prop_ext. apply hck5_p5_fc_cs. Qed.
Lemma hck5_p5_data_at__cs sh n p :
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof. unfold data_at_, field_at_. apply hck5_p5_data_at_cs. Qed.
End Bytes.

Lemma hck5_p5_hbytes_W sh bs p :
  @data_at W_cookie_mac sh (tarray tuchar (Zlength bs)) (bytes bs) p = hbytes sh bs p.
Proof. unfold hbytes. apply hck5_p5_data_at_cs. Qed.

Lemma hck5_p5_cs_open sh C s : cookie_ok C ->
  @data_at CKS sh t_cksnap (cksnap_val C) s = (
  field_at sh t_cksnap (DOT HC._birthdate) (Vlong (ck_birth C)) s *
  field_at sh t_cksnap (DOT HC._is_valid) (Val.of_bool (ck_valid C)) s *
  hbytes sh (ck_cookie C) (field_address t_cksnap (DOT HC._cookie) s) *
  field_at sh t_cksnap (DOT HC._have_sent_mac1) (Val.of_bool (ck_sent C)) s *
  hbytes sh (ck_last_mac1 C) (field_address t_cksnap (DOT HC._last_mac1_sent) s) *
  hbytes sh (ck_dkey C) (field_address t_cksnap (DOT HC._cookie_decryption_key) s) *
  hbytes sh (ck_mkey C) (field_address t_cksnap (DOT HC._message_mac1_key) s) *
  spacer sh 106 112 s)%logic.
Proof.
  intros (L1 & L2 & L3 & L4).
  erewrite (@data_at_change_composite CKS W_cookie_mac _ sh t_cksnap _ _ (JMeq_refl _)) by reflexivity.
  unfold_data_at (data_at _ _ _ _).
  rewrite (field_at_data_at sh t_cksnap (DOT HC._cookie)), (field_at_data_at sh t_cksnap (DOT HC._last_mac1_sent)),
    (field_at_data_at sh t_cksnap (DOT HC._cookie_decryption_key)),
    (field_at_data_at sh t_cksnap (DOT HC._message_mac1_key)).
  rewrite <- (hck5_p5_hbytes_W sh (ck_cookie C)), <- (hck5_p5_hbytes_W sh (ck_last_mac1 C)),
    <- (hck5_p5_hbytes_W sh (ck_dkey C)), <- (hck5_p5_hbytes_W sh (ck_mkey C)), L1, L2, L3, L4.
  simpl. apply pred_ext; cancel.
Qed.

Definition hck5_p5_lc (f: ident) : list gfield := DOT HC._latest_cookie DOT f.

Lemma hck5_p5_ck_open sh p C lk : field_compatible t_peer [] p -> cookie_ok C ->
  @data_at Noise.CS sh t_cookie (cookie_val C lk) (cookie_addr p) = (
  field_at sh t_peer (hck5_p5_lc HC._birthdate) (Vlong (ck_birth C)) p *
  field_at sh t_peer (hck5_p5_lc HC._is_valid) (Val.of_bool (ck_valid C)) p *
  hbytes sh (ck_cookie C) (field_address t_peer (hck5_p5_lc HC._cookie) p) *
  field_at sh t_peer (hck5_p5_lc HC._have_sent_mac1) (Val.of_bool (ck_sent C)) p *
  hbytes sh (ck_last_mac1 C) (field_address t_peer (hck5_p5_lc HC._last_mac1_sent) p) *
  hbytes sh (ck_dkey C) (field_address t_peer (hck5_p5_lc HC._cookie_decryption_key) p) *
  hbytes sh (ck_mkey C) (field_address t_peer (hck5_p5_lc HC._message_mac1_key) p) *
  spacer sh 466 468 p *
  field_at sh t_peer (hck5_p5_lc HC._lock) lk p)%logic.
Proof.
  intros FC (L1 & L2 & L3 & L4).
  assert (E: cookie_addr p = field_address t_peer (DOT HC._latest_cookie) p).
  { rewrite field_address_offset by auto with field_compatible. reflexivity. }
  rewrite E.
  erewrite (@data_at_change_composite Noise.CS W_cookie_mac _ sh t_cookie _ _ (JMeq_refl _)) by reflexivity.
  transitivity (@field_at W_cookie_mac sh t_peer (DOT HC._latest_cookie) (cookie_val C lk) p).
  { rewrite field_at_data_at. reflexivity. }
  unfold_field_at 1%nat. unfold hck5_p5_lc.
  rewrite (field_at_data_at sh t_peer (DOT HC._latest_cookie DOT HC._cookie)),
    (field_at_data_at sh t_peer (DOT HC._latest_cookie DOT HC._last_mac1_sent)),
    (field_at_data_at sh t_peer (DOT HC._latest_cookie DOT HC._cookie_decryption_key)),
    (field_at_data_at sh t_peer (DOT HC._latest_cookie DOT HC._message_mac1_key)).
  rewrite <- (hck5_p5_hbytes_W sh (ck_cookie C)), <- (hck5_p5_hbytes_W sh (ck_last_mac1 C)),
    <- (hck5_p5_hbytes_W sh (ck_dkey C)), <- (hck5_p5_hbytes_W sh (ck_mkey C)), L1, L2, L3, L4.
  simpl. apply pred_ext; cancel.
Qed.

Lemma hck5_p5_fc_peer p : @field_compatible Noise.CS t_peer [] p -> @field_compatible W_cookie_mac t_peer [] p.
Proof. apply (@field_compatible_change_composite Noise.CS W_cookie_mac _ t_peer). reflexivity. Qed.

(* a byte buffer a ++ b (b not empty) as a possibly empty prefix and the rest *)
Lemma hck5_p5_split sh a b p : 0 < Zlength b ->
  @field_compatible HCS (tarray tuchar (Zlength (a ++ b))) [] p ->
  hbytes sh (a ++ b) p = (hin sh a p * hbytes sh b (offset_val (Zlength a) p))%logic.
Proof.
  intros Hb FC. unfold hin. destruct (Z.eq_dec (Zlength a) 0) as [Z0 | NZ].
  - apply Zlength_nil_inv in Z0. subst a. simpl app. rewrite emp_sepcon, Zlength_nil.
    rewrite isptr_offset_val_zero by (destruct FC; auto). reflexivity.
  - unfold hbytes, bytes. rewrite map_app.
    pose proof (Zlength_nonneg a).
    rewrite (split2_data_at_Tarray_app (Zlength a) (Zlength (a ++ b))) by (rewrite Zlength_map; try rewrite Zlength_app; lia).
    rewrite field_address0_offset by (apply arr_field_compatible0; [exact FC | rewrite Zlength_app; lia]).
    change (nested_field_offset (tarray tuchar (Zlength (a ++ b))) (SUB Zlength a)) with (0 + 1 * Zlength a).
    replace (0 + 1 * Zlength a) with (Zlength a) by lia.
    replace (Zlength (a ++ b) - Zlength a) with (Zlength b) by (rewrite Zlength_app; lia).
    reflexivity.
Qed.

Lemma hck5_p5_fc_shrink k n p : 0 <= k <= n ->
  @field_compatible HCS (tarray tuchar n) [] p -> @field_compatible HCS (tarray tuchar k) [] p.
Proof.
  intros Hk (H1 & H2 & H3 & H4 & H5).
  assert (A: forall (ce: composite_env) z, align_compatible_rec ce (tarray tuchar k) z).
  { intros. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  repeat split; auto.
  - destruct p; try contradiction. unfold size_compatible in *. simpl sizeof in *.
    rewrite Z.max_r in * by lia. lia.
  - destruct p; try contradiction. apply A.
Qed.

Lemma hck5_p5_hin_ne sh bs p : 0 < Zlength bs -> hin sh bs p = hbytes sh bs p.
Proof. intros. unfold hin. rewrite if_false by lia. reflexivity. Qed.

Lemma hck5_p5_to_hout sh bs p : (hbytes sh bs p |-- hout sh (Zlength bs) p)%logic.
Proof. unfold hbytes, hout. apply data_at_data_at_. Qed.

Lemma hck5_p5_ptr i n k : 0 <= k <= Int.max_signed ->
  Ptrofs.sub (Ptrofs.add i (Ptrofs.repr n)) (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr k))) =
  Ptrofs.add i (Ptrofs.repr (n - k)).
Proof.
  intros Hk. rewrite Ptrofs.mul_commut, Ptrofs.mul_one, Ptrofs.sub_add_opp, Ptrofs.add_assoc. f_equal.
  unfold Ptrofs.of_ints. rewrite Int.signed_repr by rep_lia. rewrite Ptrofs.neg_repr, ptrofs_add_repr.
  f_equal; lia.
Qed.

Lemma hck5_p5_bytes_at sh bs p : bytes_at sh bs p = hbytes sh bs p.
Proof. unfold bytes_at, hbytes. apply hck5_p5_data_at_cs. Qed.

Lemma hck5_p5_MAC_len k m : Zlength (MAC k m) = 16.
Proof. unfold MAC, blake2s, b2s_digest_stream, b2s_out. rewrite Zlength_map. reflexivity. Qed.

Lemma hck5_p5_bytes_eqb_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

(* the harness's mac2 *)
Definition hck5_p5_m2 (C: cookie) (now: int64) (pre m1: list byte) : list byte :=
  if andb (ck_valid C) (negb (birthdate_expired (ck_birth C) (Int64.repr 115) now))
  then MAC (ck_cookie C) (pre ++ m1) else zeros 16.

Lemma hck5_p5_m2_len C now pre m1 : Zlength (hck5_p5_m2 C now pre m1) = 16.
Proof. unfold hck5_p5_m2. destruct (andb _ _). apply hck5_p5_MAC_len. reflexivity. Qed.

Definition hck5_p5_C1 (C: cookie) (m1: list byte) : cookie :=
  mkCookie (ck_birth C) (ck_valid C) (ck_cookie C) true m1 (ck_dkey C) (ck_mkey C).

Lemma hck5_p5_model C msg now m1 : 32 <= Zlength msg -> m1 = mac1_of (ck_mkey C) msg ->
  add_mac_model C msg now =
  (sublist 0 (Zlength msg - 32) msg ++ m1 ++ hck5_p5_m2 C now (sublist 0 (Zlength msg - 32) msg) m1,
   hck5_p5_C1 C m1).
Proof.
  intros Hn E. unfold add_mac_model. cbv zeta. rewrite <- E.
  assert (L1: Zlength m1 = 16) by (rewrite E; unfold mac1_of; apply hck5_p5_MAC_len).
  unfold hck5_p5_m2, hck5_p5_C1, mac2_of.
  set (A := sublist 0 (Zlength msg - 32) msg). set (B := sublist (Zlength msg - 16) (Zlength msg) msg).
  assert (LA: Zlength A = Zlength msg - 32) by (unfold A; rewrite Zlength_sublist; lia).
  assert (LB: Zlength B = 16) by (unfold B; rewrite Zlength_sublist; lia).
  assert (E1: Zlength (A ++ m1 ++ B) - 16 = Zlength msg - 16) by (rewrite !Zlength_app; lia).
  assert (E2: sublist 0 (Zlength msg - 16) (A ++ m1 ++ B) = A ++ m1).
  { rewrite app_assoc. rewrite sublist0_app1 by (rewrite Zlength_app; lia).
    rewrite sublist_same by (try rewrite Zlength_app; lia). reflexivity. }
  rewrite E1, E2. rewrite app_assoc. reflexivity.
Qed.

Lemma hck5_p5_ck_close sh p C m1 lk : field_compatible t_peer [] p -> cookie_ok (hck5_p5_C1 C m1) ->
  (field_at sh t_peer (hck5_p5_lc HC._birthdate) (Vlong (ck_birth C)) p *
  field_at sh t_peer (hck5_p5_lc HC._is_valid) (Val.of_bool (ck_valid C)) p *
  hbytes sh (ck_cookie C) (field_address t_peer (hck5_p5_lc HC._cookie) p) *
  field_at sh t_peer (hck5_p5_lc HC._have_sent_mac1) (Val.of_bool true) p *
  hbytes sh m1 (field_address t_peer (hck5_p5_lc HC._last_mac1_sent) p) *
  hbytes sh (ck_dkey C) (field_address t_peer (hck5_p5_lc HC._cookie_decryption_key) p) *
  hbytes sh (ck_mkey C) (field_address t_peer (hck5_p5_lc HC._message_mac1_key) p) *
  spacer sh 466 468 p *
  field_at sh t_peer (hck5_p5_lc HC._lock) lk p |-- cookie_rep sh (cookie_addr p) (hck5_p5_C1 C m1))%logic.
Proof.
  intros FC OK. unfold cookie_rep. rewrite prop_true_andp by exact OK. Exists lk.
  rewrite (hck5_p5_ck_open sh p (hck5_p5_C1 C m1) lk FC OK). apply derives_refl.
Qed.

Ltac hck5_p5_fif x :=
  match goal with |- semax _ (PROPx ?Pr (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
    forward_if (PROPx Pr (LOCALx (temp x (Vint Int.one) :: Lc) (SEPx Sp))) end.

Section P5.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hck5_P5_ok {Espec: OracleKind} gv L FR :
  hck5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hck5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hck5_S5a x25519 gv L FR) hck5_P5
    (overridePost (hck5_S5 x25519 gv L FR) (hck5_R gv)).
Proof.
  intros HH. unfold hck5_S5a, hck5_Delta, hck5_R, hck5_P5. simplify_func_tycontext. abbreviate_semax.
  Intros R S A m c Q cmode C ck.
  rename H0 into HA, H1 into H0, H2 into H1, H3 into H2, H4 into H3.
  unfold hck5_bside, hck5_bufs, hck5_scr3, hck5_snaps, hck5_globs, hck5_lvars. cbn [app].
  pose proof H0 as (Hn & Hmsg & Hpr & Hip4 & Hip6 & Hport & Hnow).
  pose proof (proj1 HA) as FCp.
  assert_PROP (cookie_ok C) as COK. { unfold cookie_rep. entailer!. }
  assert_PROP (@field_compatible HCS (tarray tuchar (q_n Q)) [] c) as FCc. { unfold hout. entailer!. }
  freeze FZ := - (cookie_rep _ _ _) (hbytes _ _ m) (hout _ _ c) (hout _ _ (l_mac1 L)) (hout _ _ (l_mac2 L))
     (@data_at CKS _ _ _ (l_cs L)) (shim_state4 _ _ _) (wg_consts _).
  (* bytes_copy(copy, msg, len) *)
  replace (hout Ews (q_n Q) c) with (hout Ews (Zlength (q_msg Q)) c) by (rewrite Hmsg; reflexivity).
  forward_call (Ews, c, Ews, m, q_msg Q). { apply prop_right. rewrite Hmsg. reflexivity. }
  (* add_mac *)
  rewrite <- (hck5_p5_bytes_at Ews (q_msg Q) m).
  forward_call (gv, S, hck5_w0, Ews, m, q_msg Q, Tsh, l_p L, C).
  { apply prop_right. rewrite Hmsg. reflexivity. }
  rewrite H1.
  assert (Lm1: Zlength (mac1_of (ck_mkey C) (q_msg Q)) = 16) by (unfold mac1_of; apply hck5_p5_MAC_len).
  rewrite (hck5_p5_model C (q_msg Q) (q_now Q) _ ltac:(lia) eq_refl). cbn [fst snd].
  remember (mac1_of (ck_mkey C) (q_msg Q)) as m1 eqn:Em1.
  change (hck5_is m1 (mac1_of (ck_mkey C) (q_msg Q))) in Em1.
  remember (sublist 0 (Zlength (q_msg Q) - 32) (q_msg Q)) as pre eqn:Epre.
  assert (Lpre: Zlength pre = q_n Q - 32) by (subst pre; rewrite Zlength_sublist; lia).
  remember (hck5_p5_m2 C (q_now Q) pre m1) as m2 eqn:Em2.
  assert (Lm2: Zlength m2 = 16) by (subst m2; apply hck5_p5_m2_len).
  change (hck5_is m2 (hck5_p5_m2 C (q_now Q) pre m1)) in Em2.
  set (s1 := sublist (q_n Q - 32) (q_n Q - 16) (q_msg Q)).
  set (s2 := sublist (q_n Q - 16) (q_n Q) (q_msg Q)).
  assert (Ls1: Zlength s1 = 16) by (unfold s1; rewrite Zlength_sublist; lia).
  assert (Ls2: Zlength s2 = 16) by (unfold s2; rewrite Zlength_sublist; lia).
  assert (Emsg: q_msg Q = pre ++ s1 ++ s2).
  { subst pre. unfold s1, s2. rewrite Hmsg. rewrite !sublist_rejoin by lia. rewrite sublist_same by lia. reflexivity. }
  replace (hbytes Ews (q_msg Q) c) with (hbytes Ews (pre ++ s1 ++ s2) c) by (rewrite <- Emsg; reflexivity).
  rewrite (hck5_p5_split Ews pre (s1 ++ s2) c) by first [rewrite Zlength_app; lia | rewrite <- Emsg, Hmsg; exact FCc].
  assert_PROP (@field_compatible HCS (tarray tuchar (Zlength (s1 ++ s2))) [] (offset_val (Zlength pre) c)) as FCc2.
  { unfold hbytes. entailer!. }
  rewrite (hck5_p5_split Ews s1 s2 (offset_val (Zlength pre) c) ltac:(lia) FCc2).
  rewrite (hck5_p5_hin_ne Ews s1) by lia.
  rewrite offset_offset_val, Lpre, Ls1.
  replace (q_n Q - 32 + 16) with (q_n Q - 16) by lia.
  (* open p's cookie *)
  unfold cookie_rep. Intros lk.
  rewrite (hck5_p5_ck_open Tsh (l_p L) _ lk (hck5_p5_fc_peer _ FCp)) by assumption.
  unfold hck5_p5_C1. cbn [ck_birth ck_valid ck_cookie ck_sent ck_last_mac1 ck_dkey ck_mkey].
  unfold wg_consts. Intros.
  rewrite (hck5_p5_bytes_at Ews _ m).
  destruct COK as (LC1 & LC2 & LC3 & LC4).
  (* m_mac(mac1, p.latest_cookie.message_mac1_key, 32, copy, len - 32) *)
  rewrite <- (hck5_p5_hin_ne Tsh (ck_mkey C)) by lia.
  forward_call (gv, Tsh, l_mac1 L, Tsh, field_address t_peer (hck5_p5_lc HC._message_mac1_key) (l_p L),
    ck_mkey C, Ews, c, pre).
  { pose proof (hck5_p5_fc_peer _ FCp) as FCw. entailer!. simpl. rewrite LC4, Lpre. unfold hck5_p5_lc.
    rewrite field_address_offset by auto with field_compatible. simpl. rewrite offset_offset_val. reflexivity. }
  assert (EM: MAC (ck_mkey C) pre = m1) by (unfold hck5_is in Em1; rewrite Em1, Epre; reflexivity).
  rewrite EM, (hck5_p5_hin_ne Tsh (ck_mkey C)) by lia. clear EM.
  change (hck5_is pre (sublist 0 (Zlength (q_msg Q) - 32) (q_msg Q))) in Epre.
  (* bytes_copy(copy + len - 32, mac1, 16) *)
  sep_apply (hck5_p5_to_hout Ews s1 (offset_val (q_n Q - 32) c)).
  replace (Zlength s1) with (Zlength m1) by lia.
  forward_call (Ews, offset_val (q_n Q - 32) c, Tsh, l_mac1 L, m1).
  { destruct FCc as [Pc _]. destruct c; try contradiction. split; reflexivity. }
  { destruct FCc as [Pc _]. entailer!. rewrite Lm1. destruct c; try contradiction. simpl.
    rewrite hck5_p5_ptr by rep_lia. reflexivity. }
  (* if (cs.is_valid && !m_expired(cs.birthdate, 115, now)) *)
  rewrite (hck5_p5_cs_open Tsh C (l_cs L) (conj LC1 (conj LC2 (conj LC3 LC4)))).
  Intros. forward. { entailer!; destruct (ck_valid C); simpl; auto. }
  set (cnd := andb (ck_valid C) (negb (birthdate_expired (ck_birth C) (Int64.repr 115) (q_now Q)))).
  match goal with |- semax _ (PROPx ?Pr (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
    forward_if (PROPx Pr (LOCALx (temp HC._t'40 (Vint (if cnd then Int.one else Int.zero)) :: Lc) (SEPx Sp))) end.
  { forward. forward_call (ck_birth C, Int64.repr 115, q_now Q).
    forward. entailer!. unfold cnd. destruct (ck_valid C); try discriminate.
    destruct (birthdate_expired (ck_birth C) (Int64.repr 115) (q_now Q)); reflexivity. }
  { forward. entailer!. unfold cnd. destruct (ck_valid C); try reflexivity. discriminate. }
  assert (FCc3: @field_compatible HCS (tarray tuchar (Zlength (pre ++ m1))) [] c)
    by (apply (hck5_p5_fc_shrink _ (q_n Q)); [rewrite Zlength_app; lia | exact FCc]).
  match goal with |- semax _ (PROPx ?Pr (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
    let Sp' := eval cbv beta iota delta [removelast] in (removelast Sp) in
    forward_if (PROPx Pr (LOCALx Lc (SEPx (hbytes Tsh m2 (l_mac2 L) :: Sp')))) end.
  { (* m_mac(mac2, cs.cookie, 16, copy, len - 16) *)
    assert (Hc: cnd = true) by (destruct cnd; [reflexivity | contradiction H5; reflexivity]).
    replace (offset_val (q_n Q - 32) c) with (offset_val (Zlength pre) c) by (rewrite Lpre; reflexivity).
    sep_apply (derives_refl' _ _ (eq_sym (hck5_p5_split Ews pre m1 c ltac:(lia) FCc3))).
    rewrite <- (hck5_p5_hin_ne Ews (pre ++ m1)) by (rewrite Zlength_app; lia).
    rewrite <- (hck5_p5_hin_ne Tsh (ck_cookie C) (field_address t_cksnap (DOT HC._cookie) (l_cs L))) by lia.
    forward_call (gv, Tsh, l_mac2 L, Tsh, field_address t_cksnap (DOT HC._cookie) (l_cs L), ck_cookie C,
      Ews, c, pre ++ m1).
    { entailer!. simpl. rewrite LC1, Zlength_app, Lm1, Lpre.
      rewrite field_address_offset by auto with field_compatible. simpl.
      replace (q_n Q - 32 + 16) with (q_n Q - 16) by lia. reflexivity. }
    { rewrite Zlength_app. rep_lia. }
    assert (EM2: MAC (ck_cookie C) (pre ++ m1) = m2)
      by (unfold hck5_is in Em2; rewrite Em2; unfold hck5_p5_m2; unfold cnd in Hc; rewrite Hc; reflexivity).
    rewrite EM2. clear EM2.
    rewrite (hck5_p5_hin_ne Tsh (ck_cookie C)) by lia.
    rewrite (hck5_p5_hin_ne Ews (pre ++ m1)) by (rewrite Zlength_app; lia).
    rewrite (hck5_p5_split Ews pre m1 c ltac:(lia) FCc3), Lpre.
    entailer!. }
  { (* bytes_set(mac2, 0, 16) *)
    assert (Hc: cnd = false) by (destruct cnd; [contradiction (Int.one_not_zero H5) | reflexivity]).
    forward_call (Tsh, l_mac2 L, Byte.zero, 16).
    assert (EM2: Zrepeat Byte.zero 16 = m2)
      by (unfold hck5_is in Em2; rewrite Em2; unfold hck5_p5_m2; unfold cnd in Hc; rewrite Hc; reflexivity).
    rewrite EM2. clear EM2.
    entailer!. }
  (* bytes_copy(copy + len - 16, mac2, 16) *)
  sep_apply (hck5_p5_to_hout Ews s2 (offset_val (q_n Q - 16) c)).
  replace (Zlength s2) with (Zlength m2) by lia.
  forward_call (Ews, offset_val (q_n Q - 16) c, Tsh, l_mac2 L, m2).
  { destruct FCc as [Pc _]. destruct c; try contradiction. split; reflexivity. }
  { destruct FCc as [Pc _]. entailer!. rewrite Lm2. destruct c; try contradiction. simpl.
    rewrite hck5_p5_ptr by rep_lia. reflexivity. }
  (* the copy: pre ++ m1 ++ m2 *)
  replace (offset_val (q_n Q - 32) c) with (offset_val (Zlength pre) c) by (rewrite Lpre; reflexivity).
  sep_apply (derives_refl' _ _ (eq_sym (hck5_p5_split Ews pre m1 c ltac:(lia) FCc3))).
  rewrite <- (hck5_p5_hin_ne Ews (pre ++ m1)) by (rewrite Zlength_app; lia).
  assert (FCc4: @field_compatible HCS (tarray tuchar (Zlength ((pre ++ m1) ++ m2))) [] c)
    by (rewrite !Zlength_app, Lpre, Lm1, Lm2; replace (q_n Q - 32 + 16 + 16) with (q_n Q) by lia; exact FCc).
  replace (offset_val (q_n Q - 16) c) with (offset_val (Zlength (pre ++ m1)) c)
    by (rewrite Zlength_app, Lpre, Lm1; f_equal; lia).
  sep_apply (derives_refl' _ _ (eq_sym (hck5_p5_split Ews (pre ++ m1) m2 c ltac:(lia) FCc4))).
  rewrite <- app_assoc.
  assert (LM: Zlength (pre ++ m1 ++ m2) = q_n Q) by (rewrite !Zlength_app; lia).
  (* CHECK(bytes_eq(msg, copy, len)) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward_call (Ews, m, pre ++ m1 ++ m2, Ews, c, pre ++ m1 ++ m2).
    { entailer!. rewrite LM. reflexivity. }
    rewrite hck5_p5_bytes_eqb_refl.
    forward_if. { exfalso. contradiction (Int.one_not_zero). }
    forward. entailer!. }
  { forward. entailer!. }
  (* CHECK(p.latest_cookie.have_sent_mac1 && bytes_eq(p.latest_cookie.last_mac1_sent, mac1, 16)) *)
  pose proof (hck5_p5_fc_peer _ FCp) as FCw.
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward.
    hck5_p5_fif HC._t'43.
    { forward_call (Tsh, field_address t_peer (hck5_p5_lc HC._last_mac1_sent) (l_p L), m1, Tsh, l_mac1 L, m1).
      { entailer!. simpl. rewrite Lm1. unfold hck5_p5_lc.
        rewrite field_address_offset by auto with field_compatible. simpl. rewrite offset_offset_val. reflexivity. }
      rewrite hck5_p5_bytes_eqb_refl. forward. entailer!. }
    { exfalso. hnf in H5. simpl in H5. discriminate. }
    forward_if. { exfalso. contradiction (Int.one_not_zero). }
    forward. entailer!. }
  { forward. entailer!. }
  (* CHECK(birthdate, is_valid, cookie, keys unchanged) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward. forward.
    hck5_p5_fif HC._t'45.
    { forward. forward. forward. entailer!. destruct (ck_valid C); reflexivity. }
    { exfalso. apply H5. reflexivity. }
    hck5_p5_fif HC._t'46.
    { forward_call (Tsh, field_address t_peer (hck5_p5_lc HC._cookie) (l_p L), ck_cookie C,
        Tsh, field_address t_cksnap (DOT HC._cookie) (l_cs L), ck_cookie C).
      { entailer!. simpl. rewrite LC1. unfold hck5_p5_lc.
        rewrite !field_address_offset by auto with field_compatible. simpl. rewrite offset_offset_val. reflexivity. }
      rewrite hck5_p5_bytes_eqb_refl. forward. entailer!. }
    { exfalso. hnf in H5. simpl in H5. discriminate. }
    hck5_p5_fif HC._t'48.
    { forward_call (Tsh, field_address t_peer (hck5_p5_lc HC._cookie_decryption_key) (l_p L), ck_dkey C,
        Tsh, field_address t_cksnap (DOT HC._cookie_decryption_key) (l_cs L), ck_dkey C).
      { entailer!. simpl. rewrite LC3. unfold hck5_p5_lc.
        rewrite !field_address_offset by auto with field_compatible. simpl. rewrite offset_offset_val. reflexivity. }
      rewrite hck5_p5_bytes_eqb_refl. forward. entailer!. }
    { exfalso. hnf in H5. simpl in H5. discriminate. }
    hck5_p5_fif HC._t'50.
    { forward_call (Tsh, field_address t_peer (hck5_p5_lc HC._message_mac1_key) (l_p L), ck_mkey C,
        Tsh, field_address t_cksnap (DOT HC._message_mac1_key) (l_cs L), ck_mkey C).
      { entailer!. simpl. rewrite LC4. unfold hck5_p5_lc.
        rewrite !field_address_offset by auto with field_compatible. simpl. rewrite offset_offset_val. reflexivity. }
      rewrite hck5_p5_bytes_eqb_refl. forward. entailer!. }
    { exfalso. hnf in H5. simpl in H5. discriminate. }
    forward_if. { exfalso. contradiction (Int.one_not_zero). }
    forward. entailer!. }
  { forward. entailer!. }
  (* the post S5 *)
  assert (HIS: hck5_is (pre ++ m1 ++ m2, hck5_p5_C1 C m1) (add_mac_model C (q_msg Q) (q_now Q))).
  { unfold hck5_is in *. rewrite (hck5_p5_model C (q_msg Q) (q_now Q) m1) by (lia || exact Em1).
    rewrite Em2, Epre. reflexivity. }
  unfold POSTCONDITION, abbreviate. rewrite overridePost_normal'. unfold hck5_S5.
  thaw FZ.
  sep_apply (derives_refl' _ _ (eq_sym (hck5_p5_cs_open Tsh C (l_cs L) (conj LC1 (conj LC2 (conj LC3 LC4)))))).
  sep_apply (data_at_data_at_ (cs := CKS) Tsh t_cksnap (cksnap_val C) (l_cs L)).
  sep_apply (hck5_p5_ck_close Tsh (l_p L) C m1 lk FCw H4).
  sep_apply (hck5_p5_to_hout Tsh m1 (l_mac1 L)). sep_apply (hck5_p5_to_hout Tsh m2 (l_mac2 L)).
  rewrite Lm1, Lm2.
  Exists R S A m c Q cmode C ck (pre ++ m1 ++ m2) (hck5_p5_C1 C m1).
  unfold hck5_bside, hck5_bufs, hck5_scr2, hck5_snaps, hck5_globs, hck5_lvars, wg_consts. cbn [app].
  entailer!.
Qed.

End P5.
