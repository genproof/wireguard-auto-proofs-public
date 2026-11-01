(* hc_pieces3, group ck: common.h bodies, proved once at a small compspecs with the callee context
   of hc3_ctx.v.  One lemma per function (per law where the Clight
   reads a renamed constant). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.blake2s.b2s_spec3.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common.hc3_ctx.
Require WgNoise.harness.x_handshake.code WgNoise.harness.x_cookie_reply.code WgNoise.harness.x_consume_response_any.code
        WgNoise.harness.x_keypairs.code WgNoise.harness.x_create_any.code WgNoise.harness.x_replay.code
        WgNoise.harness.x_cookie_mac.code WgNoise.harness.x_consume_initiation_any.code.
Require WgNoise.contracts.x_cookie_reply.

Module FH := WgNoise.harness.x_handshake.code.
Module FK := WgNoise.harness.x_cookie_reply.code.
Module FR := WgNoise.harness.x_consume_response_any.code.

(* every lemma takes all the section variables and hypotheses (a stable signature for the assembly) *)
#[local] Set Default Proof Using "All".

(* byte arrays are the same in every compspecs (copy of WgNoise.proof.libc.libc_bytes) *)
Lemma hc3b_ck_data_at_cs {cs1 cs2: compspecs}: forall sh n (v: list val) p,
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  intros. unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  assert (forall (ce: composite_env) z, align_compatible_rec ce (tarray tuchar n) z).
  { intros. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  unfold field_compatible, size_compatible, align_compatible.
  destruct p; simpl; try tauto.
  pose proof (H (@cenv_cs cs1) (Ptrofs.unsigned i)). pose proof (H (@cenv_cs cs2) (Ptrofs.unsigned i)). tauto.
Qed.
Lemma hc3b_ck_data_at__cs {cs1 cs2: compspecs}: forall sh n p,
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof. intros. unfold data_at_, field_at_. apply hc3b_ck_data_at_cs. Qed.

Definition t_ck := Tstruct FK._cookie noattr.
Local Open Scope logic.

#[local] Existing Instance CSkck.
#[local] Instance hc3b_ck_i1 : change_composite_env CKS CSkck. make_cs_preserve CKS CSkck. Defined.
#[local] Instance hc3b_ck_i2 : change_composite_env CSkck CKS. make_cs_preserve CSkck CKS. Defined.
#[local] Instance hc3b_ck_i3 : change_composite_env Noise.CS CSkck. make_cs_preserve Noise.CS CSkck. Defined.
#[local] Instance hc3b_ck_i4 : change_composite_env CSkck Noise.CS. make_cs_preserve CSkck Noise.CS. Defined.

Lemma hc3b_ck_tcbool b : tc_val tbool (Val.of_bool b).
Proof. destruct b; hnf; auto. Qed.

Lemma hc3b_ck_tt (b: bool) : typed_true tint (if b then Vtrue else Vfalse) -> b = true.
Proof. destruct b; auto. intros X. inv X. Qed.
Lemma hc3b_ck_tf (b: bool) : typed_false tint (if b then Vtrue else Vfalse) -> b = false.
Proof. destruct b; auto. intros X. inv X. Qed.

Lemma hc3b_ck_cookie_split_k sh C lk c : cookie_ok C ->
  @data_at Noise.CS sh t_cookie (cookie_val C lk) c =
  field_at sh t_ck (DOT FK._birthdate) (Vlong (ck_birth C)) c *
  field_at sh t_ck (DOT FK._is_valid) (Val.of_bool (ck_valid C)) c *
  hbytes sh (ck_cookie C) (field_address t_ck (DOT FK._cookie) c) *
  field_at sh t_ck (DOT FK._have_sent_mac1) (Val.of_bool (ck_sent C)) c *
  hbytes sh (ck_last_mac1 C) (field_address t_ck (DOT FK._last_mac1_sent) c) *
  hbytes sh (ck_dkey C) (field_address t_ck (DOT FK._cookie_decryption_key) c) *
  hbytes sh (ck_mkey C) (field_address t_ck (DOT FK._message_mac1_key) c) *
  spacer sh 106 108 c * field_at sh t_ck (DOT FK._lock) lk c.
Proof.
  intros (L1 & L2 & L3 & L4).
  erewrite (@data_at_change_composite Noise.CS CSkck _ sh t_cookie _ _ (JMeq_refl _)) by reflexivity.
  unfold t_cookie. unfold_data_at (data_at _ _ _ c).
  rewrite !(field_at_data_at sh (Tstruct I._cookie noattr) (DOT FK._cookie)).
  rewrite (field_at_data_at sh (Tstruct I._cookie noattr) (DOT FK._last_mac1_sent)),
    (field_at_data_at sh (Tstruct I._cookie noattr) (DOT FK._cookie_decryption_key)),
    (field_at_data_at sh (Tstruct I._cookie noattr) (DOT FK._message_mac1_key)).
  unfold hbytes. rewrite L1, L2, L3, L4.
  rewrite !(@hc3b_ck_data_at_cs HCS CSkck).
  unfold t_ck, cookie_val. cbn [fst snd]. simpl nested_field_type.
  apply pred_ext; cancel.
Qed.

Lemma hc3b_ck_snap_split_k sh C s : cookie_ok C ->
  @data_at CKS sh t_cksnap (cksnap_val C) s =
  field_at sh t_cksnap (DOT FK._birthdate) (Vlong (ck_birth C)) s *
  field_at sh t_cksnap (DOT FK._is_valid) (Val.of_bool (ck_valid C)) s *
  hbytes sh (ck_cookie C) (field_address t_cksnap (DOT FK._cookie) s) *
  field_at sh t_cksnap (DOT FK._have_sent_mac1) (Val.of_bool (ck_sent C)) s *
  hbytes sh (ck_last_mac1 C) (field_address t_cksnap (DOT FK._last_mac1_sent) s) *
  hbytes sh (ck_dkey C) (field_address t_cksnap (DOT FK._cookie_decryption_key) s) *
  hbytes sh (ck_mkey C) (field_address t_cksnap (DOT FK._message_mac1_key) s) *
  spacer sh 106 112 s.
Proof.
  intros (L1 & L2 & L3 & L4).
  erewrite (@data_at_change_composite CKS CSkck _ sh t_cksnap _ _ (JMeq_refl _)) by reflexivity.
  unfold t_cksnap. unfold_data_at (data_at _ _ _ s).
  rewrite (field_at_data_at sh (Tstruct HK._ck_snap noattr) (DOT FK._cookie)),
    (field_at_data_at sh (Tstruct HK._ck_snap noattr) (DOT FK._last_mac1_sent)),
    (field_at_data_at sh (Tstruct HK._ck_snap noattr) (DOT FK._cookie_decryption_key)),
    (field_at_data_at sh (Tstruct HK._ck_snap noattr) (DOT FK._message_mac1_key)).
  unfold hbytes. rewrite L1, L2, L3, L4.
  rewrite !(@hc3b_ck_data_at_cs HCS CSkck).
  unfold cksnap_val. cbn [fst snd]. simpl nested_field_type.
  apply pred_ext; cancel.
Qed.

Lemma hc3b_ck_snap_split_k_ sh s :
  @data_at_ CKS sh t_cksnap s =
  field_at_ sh t_cksnap (DOT FK._birthdate) s *
  field_at_ sh t_cksnap (DOT FK._is_valid) s *
  hout sh 16 (field_address t_cksnap (DOT FK._cookie) s) *
  field_at_ sh t_cksnap (DOT FK._have_sent_mac1) s *
  hout sh 16 (field_address t_cksnap (DOT FK._last_mac1_sent) s) *
  hout sh 32 (field_address t_cksnap (DOT FK._cookie_decryption_key) s) *
  hout sh 32 (field_address t_cksnap (DOT FK._message_mac1_key) s) *
  spacer sh 106 112 s.
Proof.
  rewrite (@data_at__change_composite CKS CSkck _ sh t_cksnap) by reflexivity.
  unfold t_cksnap. unfold data_at_. unfold_field_at (field_at_ _ _ _ s).
  unfold field_at_.
  rewrite (field_at_data_at sh (Tstruct HK._ck_snap noattr) (DOT FK._cookie)),
    (field_at_data_at sh (Tstruct HK._ck_snap noattr) (DOT FK._last_mac1_sent)),
    (field_at_data_at sh (Tstruct HK._ck_snap noattr) (DOT FK._cookie_decryption_key)),
    (field_at_data_at sh (Tstruct HK._ck_snap noattr) (DOT FK._message_mac1_key)).
  unfold hout. rewrite !(@hc3b_ck_data_at__cs HCS CSkck).
  simpl nested_field_type. unfold data_at_, field_at_.
  apply pred_ext; cancel.
Qed.

Notation KCS := WgNoise.contracts.x_cookie_reply.Harness.CS.
#[local] Existing Instance KCS.
#[local] Instance hc3b_ck_i5 : change_composite_env CKS KCS. make_cs_preserve CKS KCS. Defined.
#[local] Instance hc3b_ck_i6 : change_composite_env KCS CKS. make_cs_preserve KCS CKS. Defined.
#[local] Instance hc3b_ck_i7 : change_composite_env Noise.CS KCS. make_cs_preserve Noise.CS KCS. Defined.
#[local] Instance hc3b_ck_i8 : change_composite_env KCS Noise.CS. make_cs_preserve KCS Noise.CS. Defined.

Lemma hc3b_ck_cookie_split_q sh C lk c : cookie_ok C ->
  @data_at Noise.CS sh t_cookie (cookie_val C lk) c =
  field_at sh t_ck (DOT FK._birthdate) (Vlong (ck_birth C)) c *
  field_at sh t_ck (DOT FK._is_valid) (Val.of_bool (ck_valid C)) c *
  hbytes sh (ck_cookie C) (field_address t_ck (DOT FK._cookie) c) *
  field_at sh t_ck (DOT FK._have_sent_mac1) (Val.of_bool (ck_sent C)) c *
  hbytes sh (ck_last_mac1 C) (field_address t_ck (DOT FK._last_mac1_sent) c) *
  hbytes sh (ck_dkey C) (field_address t_ck (DOT FK._cookie_decryption_key) c) *
  hbytes sh (ck_mkey C) (field_address t_ck (DOT FK._message_mac1_key) c) *
  spacer sh 106 108 c * field_at sh t_ck (DOT FK._lock) lk c.
Proof.
  intros (L1 & L2 & L3 & L4).
  erewrite (@data_at_change_composite Noise.CS KCS _ sh t_cookie _ _ (JMeq_refl _)) by reflexivity.
  unfold t_cookie. unfold_data_at (data_at _ _ _ c).
  rewrite !(field_at_data_at sh (Tstruct I._cookie noattr) (DOT FK._cookie)).
  rewrite (field_at_data_at sh (Tstruct I._cookie noattr) (DOT FK._last_mac1_sent)),
    (field_at_data_at sh (Tstruct I._cookie noattr) (DOT FK._cookie_decryption_key)),
    (field_at_data_at sh (Tstruct I._cookie noattr) (DOT FK._message_mac1_key)).
  unfold hbytes. rewrite L1, L2, L3, L4.
  rewrite !(@hc3b_ck_data_at_cs HCS KCS).
  unfold t_ck, cookie_val. cbn [fst snd]. simpl nested_field_type.
  apply pred_ext; cancel.
Qed.

Lemma hc3b_ck_snap_split_q sh C s : cookie_ok C ->
  @data_at CKS sh t_cksnap (cksnap_val C) s =
  field_at sh t_cksnap (DOT FK._birthdate) (Vlong (ck_birth C)) s *
  field_at sh t_cksnap (DOT FK._is_valid) (Val.of_bool (ck_valid C)) s *
  hbytes sh (ck_cookie C) (field_address t_cksnap (DOT FK._cookie) s) *
  field_at sh t_cksnap (DOT FK._have_sent_mac1) (Val.of_bool (ck_sent C)) s *
  hbytes sh (ck_last_mac1 C) (field_address t_cksnap (DOT FK._last_mac1_sent) s) *
  hbytes sh (ck_dkey C) (field_address t_cksnap (DOT FK._cookie_decryption_key) s) *
  hbytes sh (ck_mkey C) (field_address t_cksnap (DOT FK._message_mac1_key) s) *
  spacer sh 106 112 s.
Proof.
  intros (L1 & L2 & L3 & L4).
  erewrite (@data_at_change_composite CKS KCS _ sh t_cksnap _ _ (JMeq_refl _)) by reflexivity.
  unfold t_cksnap. unfold_data_at (data_at _ _ _ s).
  rewrite (field_at_data_at sh (Tstruct HK._ck_snap noattr) (DOT FK._cookie)),
    (field_at_data_at sh (Tstruct HK._ck_snap noattr) (DOT FK._last_mac1_sent)),
    (field_at_data_at sh (Tstruct HK._ck_snap noattr) (DOT FK._cookie_decryption_key)),
    (field_at_data_at sh (Tstruct HK._ck_snap noattr) (DOT FK._message_mac1_key)).
  unfold hbytes. rewrite L1, L2, L3, L4.
  rewrite !(@hc3b_ck_data_at_cs HCS KCS).
  unfold cksnap_val. cbn [fst snd]. simpl nested_field_type.
  apply pred_ext; cancel.
Qed.

Section Bodies.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Hypothesis X25519: x25519_props x25519.
Hypothesis AEAD: aead_props aead_enc aead_dec.
Hypothesis XAEAD: xaead_props xaead_enc xaead_dec.

#[local] Existing Instance CSkck.
Lemma hc3_body_ck_take :
  @semax_body [] (hc3_G_hs_take) CSkck FK.f_ck_take (ck_take_spec).
Proof.
  start_function.
  unfold cookie_rep. Intros lk.
  assert_PROP (field_compatible t_ck [] c).
  { erewrite (@data_at_change_composite Noise.CS CSkck _ shc t_cookie _ _ (JMeq_refl _)) by reflexivity.
    entailer!. }
  assert_PROP (field_compatible t_cksnap [] s).
  { rewrite (@data_at__change_composite CKS CSkck _ shs t_cksnap) by reflexivity. entailer!. }
  pose proof H as (L1 & L2 & L3 & L4).
  rewrite hc3b_ck_cookie_split_k by assumption. rewrite hc3b_ck_snap_split_k_.
  unfold t_ck, t_cksnap in *.
  repeat flatten_sepcon_in_SEP.
  forward. forward. forward. { entailer!. apply hc3b_ck_tcbool. } forward.
  replace (hout shs 16 (field_address (Tstruct HK._ck_snap noattr) (DOT FK._cookie) s))
    with (hout shs (Zlength (ck_cookie C)) (field_address (Tstruct HK._ck_snap noattr) (DOT FK._cookie) s))
    by (rewrite L1; reflexivity).
  forward_call (shs, field_address (Tstruct HK._ck_snap noattr) (DOT FK._cookie) s,
                shc, field_address (Tstruct FK._cookie noattr) (DOT FK._cookie) c, ck_cookie C).
  { entailer!. simpl. rewrite L1. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
  forward. { entailer!. apply hc3b_ck_tcbool. } forward.
  replace (hout shs 16 (field_address (Tstruct HK._ck_snap noattr) (DOT FK._last_mac1_sent) s))
    with (hout shs (Zlength (ck_last_mac1 C)) (field_address (Tstruct HK._ck_snap noattr) (DOT FK._last_mac1_sent) s))
    by (rewrite L2; reflexivity).
  forward_call (shs, field_address (Tstruct HK._ck_snap noattr) (DOT FK._last_mac1_sent) s,
                shc, field_address (Tstruct FK._cookie noattr) (DOT FK._last_mac1_sent) c, ck_last_mac1 C).
  { entailer!. simpl. rewrite L2. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
  replace (hout shs 32 (field_address (Tstruct HK._ck_snap noattr) (DOT FK._cookie_decryption_key) s))
    with (hout shs (Zlength (ck_dkey C)) (field_address (Tstruct HK._ck_snap noattr) (DOT FK._cookie_decryption_key) s))
    by (rewrite L3; reflexivity).
  forward_call (shs, field_address (Tstruct HK._ck_snap noattr) (DOT FK._cookie_decryption_key) s,
                shc, field_address (Tstruct FK._cookie noattr) (DOT FK._cookie_decryption_key) c, ck_dkey C).
  { entailer!. simpl. rewrite L3. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
  replace (hout shs 32 (field_address (Tstruct HK._ck_snap noattr) (DOT FK._message_mac1_key) s))
    with (hout shs (Zlength (ck_mkey C)) (field_address (Tstruct HK._ck_snap noattr) (DOT FK._message_mac1_key) s))
    by (rewrite L4; reflexivity).
  forward_call (shs, field_address (Tstruct HK._ck_snap noattr) (DOT FK._message_mac1_key) s,
                shc, field_address (Tstruct FK._cookie noattr) (DOT FK._message_mac1_key) c, ck_mkey C).
  { entailer!. simpl. rewrite L4. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
  forward.
  unfold cookie_rep. Exists lk.
  rewrite hc3b_ck_snap_split_k, hc3b_ck_cookie_split_k by assumption.
  unfold t_ck, t_cksnap. entailer!.
  destruct (ck_valid C), (ck_sent C); apply derives_refl.
Qed.

#[local] Existing Instance KCS | 0.
Lemma hc3_body_ck_same :
  @semax_body [] (hc3_G_hs_same) WgNoise.contracts.x_cookie_reply.Harness.CS FK.f_ck_same (ck_same_spec).
Proof.
  start_function.
  unfold cookie_rep. Intros lk.
  assert_PROP (field_compatible t_ck [] c).
  { erewrite (@data_at_change_composite Noise.CS KCS _ shc t_cookie _ _ (JMeq_refl _)) by reflexivity.
    entailer!. }
  assert_PROP (field_compatible t_cksnap [] s /\ cookie_ok C0).
  { erewrite (@data_at_change_composite CKS KCS _ shs t_cksnap _ _ (JMeq_refl _)) by reflexivity.
    entailer!.
    unfold t_cksnap, cksnap_val in H2. simplify_value_fits in H2. destruct H2 as (_ & _ & A1 & _ & A2 & A3 & A4).
    simplify_value_fits in A1. simplify_value_fits in A2. simplify_value_fits in A3. simplify_value_fits in A4.
    unfold cookie_ok, bytes in *. rewrite Zlength_map in *. tauto. }
  destruct H1 as [H1 H2].
  pose proof H as (L1 & L2 & L3 & L4). pose proof H2 as (M1 & M2 & M3 & M4).
  rewrite hc3b_ck_cookie_split_q by assumption. rewrite hc3b_ck_snap_split_q by assumption.
  unfold t_ck, t_cksnap in *.
  repeat flatten_sepcon_in_SEP.
  forward. forward.
  forward_if (temp FK._t'1 (Val.of_bool (Int64.eq (ck_birth C0) (ck_birth C) && Bool.eqb (ck_valid C0) (ck_valid C)))).
  { forward. { entailer!. apply hc3b_ck_tcbool. }
    forward. { entailer!. apply hc3b_ck_tcbool. }
    forward. entailer!. rewrite H3. destruct (ck_valid C0), (ck_valid C); reflexivity. }
  { forward. entailer!. rewrite Int64.eq_false by auto. reflexivity. }
  forward_if (temp FK._t'2 (Val.of_bool (Int64.eq (ck_birth C0) (ck_birth C) && Bool.eqb (ck_valid C0) (ck_valid C) && bytes_eqb (ck_cookie C0) (ck_cookie C)))).
  { forward_call (shs, field_address (Tstruct HK._ck_snap noattr) (DOT FK._cookie) s, ck_cookie C0,
                  shc, field_address (Tstruct FK._cookie noattr) (DOT FK._cookie) c, ck_cookie C).
    { entailer!. simpl. rewrite M1. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. entailer!. rewrite (hc3b_ck_tt _ H3). destruct (bytes_eqb (ck_cookie C0) (ck_cookie C)); reflexivity. }
  { forward. entailer!. rewrite (hc3b_ck_tf _ H3). reflexivity. }
  forward_if (temp FK._t'4 (Val.of_bool (Int64.eq (ck_birth C0) (ck_birth C) && Bool.eqb (ck_valid C0) (ck_valid C) && bytes_eqb (ck_cookie C0) (ck_cookie C) && Bool.eqb (ck_sent C0) (ck_sent C)))).
  { forward. { entailer!. apply hc3b_ck_tcbool. }
    forward. { entailer!. apply hc3b_ck_tcbool. }
    forward. entailer!. rewrite (hc3b_ck_tt _ H3). destruct (ck_sent C0), (ck_sent C); reflexivity. }
  { forward. entailer!. rewrite (hc3b_ck_tf _ H3). reflexivity. }
  forward_if (temp FK._t'5 (Val.of_bool (Int64.eq (ck_birth C0) (ck_birth C) && Bool.eqb (ck_valid C0) (ck_valid C) && bytes_eqb (ck_cookie C0) (ck_cookie C) && Bool.eqb (ck_sent C0) (ck_sent C) && bytes_eqb (ck_last_mac1 C0) (ck_last_mac1 C)))).
  { forward_call (shs, field_address (Tstruct HK._ck_snap noattr) (DOT FK._last_mac1_sent) s, ck_last_mac1 C0,
                  shc, field_address (Tstruct FK._cookie noattr) (DOT FK._last_mac1_sent) c, ck_last_mac1 C).
    { entailer!. simpl. rewrite M2. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. entailer!. rewrite (hc3b_ck_tt _ H3). destruct (bytes_eqb (ck_last_mac1 C0) (ck_last_mac1 C)); reflexivity. }
  { forward. entailer!. rewrite (hc3b_ck_tf _ H3). reflexivity. }
  forward_if (temp FK._t'7 (Val.of_bool (Int64.eq (ck_birth C0) (ck_birth C) && Bool.eqb (ck_valid C0) (ck_valid C) && bytes_eqb (ck_cookie C0) (ck_cookie C) && Bool.eqb (ck_sent C0) (ck_sent C) && bytes_eqb (ck_last_mac1 C0) (ck_last_mac1 C) && bytes_eqb (ck_dkey C0) (ck_dkey C)))).
  { forward_call (shs, field_address (Tstruct HK._ck_snap noattr) (DOT FK._cookie_decryption_key) s, ck_dkey C0,
                  shc, field_address (Tstruct FK._cookie noattr) (DOT FK._cookie_decryption_key) c, ck_dkey C).
    { entailer!. simpl. rewrite M3. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. entailer!. rewrite (hc3b_ck_tt _ H3). destruct (bytes_eqb (ck_dkey C0) (ck_dkey C)); reflexivity. }
  { forward. entailer!. rewrite (hc3b_ck_tf _ H3). reflexivity. }
  forward_if (temp FK._t'9 (Val.of_bool (Int64.eq (ck_birth C0) (ck_birth C) && Bool.eqb (ck_valid C0) (ck_valid C) && bytes_eqb (ck_cookie C0) (ck_cookie C) && Bool.eqb (ck_sent C0) (ck_sent C) && bytes_eqb (ck_last_mac1 C0) (ck_last_mac1 C) && bytes_eqb (ck_dkey C0) (ck_dkey C) && bytes_eqb (ck_mkey C0) (ck_mkey C)))).
  { forward_call (shs, field_address (Tstruct HK._ck_snap noattr) (DOT FK._message_mac1_key) s, ck_mkey C0,
                  shc, field_address (Tstruct FK._cookie noattr) (DOT FK._message_mac1_key) c, ck_mkey C).
    { entailer!. simpl. rewrite M4. rewrite ?field_address_offset by auto with field_compatible; reflexivity. }
    forward. entailer!. rewrite (hc3b_ck_tt _ H3). destruct (bytes_eqb (ck_mkey C0) (ck_mkey C)); reflexivity. }
  { forward. entailer!. rewrite (hc3b_ck_tf _ H3). reflexivity. }
  forward.
  unfold cookie_rep. Exists lk.
  rewrite hc3b_ck_snap_split_q, hc3b_ck_cookie_split_q by assumption.
  unfold t_ck, t_cksnap. entailer!.
  unfold cookie_eqb. match goal with |- Val.of_bool ?b = _ => destruct b end; reflexivity.
Qed.

(* the group *)
Theorem hc3_bodies_ck :
  (@semax_body [] (hc3_G_hs_take) CSkck FK.f_ck_take (ck_take_spec)) /\
  (@semax_body [] (hc3_G_hs_same) WgNoise.contracts.x_cookie_reply.Harness.CS FK.f_ck_same (ck_same_spec)).
Proof.
  split; [exact hc3_body_ck_take | exact hc3_body_ck_same].
Qed.

End Bodies.
