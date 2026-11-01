(* hc_pieces3, group mix: common.h bodies, proved once at a small compspecs with the callee context
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

(* byte arrays across compspecs (copies of libc_bytes.v's lemmas, not loaded here) *)
Lemma hc3b_mix_field_compatible_cs {cs1 cs2: compspecs}: forall n p,
  @field_compatible cs1 (tarray tuchar n) nil p <-> @field_compatible cs2 (tarray tuchar n) nil p.
Proof.
  assert (A: forall (ce: composite_env) n z, align_compatible_rec ce (tarray tuchar n) z).
  { intros. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  intros. unfold field_compatible, size_compatible, align_compatible.
  destruct p; simpl; try tauto.
  pose proof (A (@cenv_cs cs1) n (Ptrofs.unsigned i)).
  pose proof (A (@cenv_cs cs2) n (Ptrofs.unsigned i)).
  tauto.
Qed.

Lemma hc3b_mix_data_at_cs {cs1 cs2: compspecs}: forall sh n (v: list val) p,
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  intros. unfold data_at, field_at.
  f_equal. f_equal. apply prop_ext. apply hc3b_mix_field_compatible_cs.
Qed.

Lemma hc3b_mix_data_at__cs {cs1 cs2: compspecs}: forall sh n p,
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof.
  intros. unfold data_at_, field_at_. apply hc3b_mix_data_at_cs.
Qed.

Lemma hc3b_mix_HASH_len m : Zlength (HASH m) = 32.
Proof.
  unfold HASH, blake2s, WgNoise.proof.blake2s.model.b2s_digest_stream, WgNoise.proof.blake2s.model.b2s_out.
  rewrite Zlength_map. reflexivity.
Qed.

Lemma hc3b_mix_mh_len h d : Zlength (mix_hash h d) = 32.
Proof. unfold mix_hash. apply hc3b_mix_HASH_len. Qed.

Lemma hc3b_mix_hmac_len key m : Zlength (hmac key m) = 32.
Proof. unfold hmac. apply hc3b_mix_HASH_len. Qed.

Lemma hc3b_mix_kdf_len ck d : Zlength (kdf1 ck d) = 32 /\ Zlength (kdf2 ck d) = 32 /\ Zlength (kdf3 ck d) = 32.
Proof. unfold kdf1, kdf2, kdf3. rewrite !hc3b_mix_hmac_len. auto. Qed.

Lemma hc3b_mix_hin_ne sh bs p : Zlength bs <> 0 -> hin sh bs p = hbytes sh bs p.
Proof. intros. unfold hin. destruct (Z.eq_dec (Zlength bs) 0); [contradiction | reflexivity]. Qed.

Lemma hc3b_mix_zero_page gv : @zero_page Noise.CS gv = @zero_page CSks gv.
Proof. unfold zero_page. apply hc3b_mix_data_at_cs. Qed.

Lemma hc3b_mix_hin_prim sh bs p : hin sh bs p = @prim_bytes CSks sh bs p.
Proof.
  unfold hin, hbytes, prim_bytes. destruct (Z.eq_dec (Zlength bs) 0); [reflexivity |].
  apply hc3b_mix_data_at_cs.
Qed.

Lemma hc3b_mix_hbytes_prim sh bs p : Zlength bs <> 0 -> hbytes sh bs p = @prim_bytes CSks sh bs p.
Proof. intros. rewrite <- hc3b_mix_hin_prim. symmetry. apply hc3b_mix_hin_ne; auto. Qed.

Lemma hc3b_mix_hbytes_key sh bs p : Zlength bs = 32 ->
  hbytes sh bs p = @data_at CSks sh (tarray tuchar 32) (map Vubyte bs) p.
Proof. intros L. unfold hbytes. rewrite L. apply hc3b_mix_data_at_cs. Qed.

Lemma hc3b_mix_hbytes_cs sh bs p : hbytes sh bs p = @data_at CSks sh (tarray tuchar (Zlength bs)) (map Vubyte bs) p.
Proof. unfold hbytes. apply hc3b_mix_data_at_cs. Qed.

Lemma hc3b_mix_hout_cs sh n p : hout sh n p = @data_at_ CSks sh (tarray tuchar n) p.
Proof. unfold hout. apply hc3b_mix_data_at__cs. Qed.

Lemma hc3b_mix_prim_out_cs sh v p : @prim_out HCS sh v p = @prim_out CSks sh v p.
Proof. unfold prim_out. destruct (Z.eq_dec (Zlength v) 0); [reflexivity |]. apply hc3b_mix_data_at_cs. Qed.

(* the bodies' compspecs *)
#[local] Existing Instance CSks.
#[local] Instance hc3b_mix_HCS_CSks : change_composite_env HCS CSks.
Proof. make_cs_preserve HCS CSks. Defined.

Lemma hc3b_mix_mstate_eq sh ck h p :
  Zlength ck = 32 -> Zlength h = 32 ->
  @data_at HCS sh t_mstate (mstate_val ck h) p =
  (hbytes sh ck (@field_address CSks t_mstate (DOT FH._ck) p) *
   hbytes sh h (@field_address CSks t_mstate (DOT FH._h) p))%logic.
Proof.
  intros H1 H2.
  erewrite (@data_at_change_composite HCS CSks _ sh t_mstate); [| apply JMeq_refl | prove_cs_preserve_type].
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mstate (DOT FH._ck)), (field_at_data_at sh t_mstate (DOT FH._h)).
  unfold hbytes. rewrite H1, H2.
  rewrite <- !(@hc3b_mix_data_at_cs CSks HCS).
  reflexivity.
Qed.

Lemma hc3b_mix_mstate_fc sh v p : @data_at HCS sh t_mstate v p |-- !! @field_compatible CSks t_mstate [] p.
Proof.
  erewrite (@data_at_change_composite HCS CSks _ sh t_mstate); [| apply JMeq_refl | prove_cs_preserve_type].
  entailer!.
Qed.

Lemma hc3b_mix_out32 v : @data_at_ CSks Tsh (tarray tuchar 32) v = hout Tsh 32 v.
Proof. unfold hout. apply hc3b_mix_data_at__cs. Qed.

Lemma hc3b_mix_back32 bs v : Zlength bs = 32 -> hbytes Tsh bs v |-- @data_at_ CSks Tsh (tarray tuchar 32) v.
Proof. intros Hl. rewrite hc3b_mix_out32. unfold hbytes, hout. rewrite Hl. apply data_at_data_at_. Qed.

Lemma hc3b_mix_hbytes_out sh bs v : hbytes sh bs v |-- hout sh (Zlength bs) v.
Proof. unfold hbytes, hout. apply data_at_data_at_. Qed.

Ltac hc3b_mix_fa :=
  rewrite ?field_address_offset by auto with field_compatible; reflexivity.

(* every lemma takes all the section variables and hypotheses (a stable signature for the assembly) *)
#[local] Set Default Proof Using "All".

Section Bodies.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Hypothesis X25519: x25519_props x25519.
Hypothesis AEAD: aead_props aead_enc aead_dec.
Hypothesis XAEAD: xaead_props xaead_enc xaead_dec.

Lemma hc3_body_m_mix_hash :
  @semax_body [] (hc3_G_m_mix_hash) CSks FH.f_m_mix_hash (m_mix_hash_spec).
Proof.
start_function.
assert_PROP (field_compatible t_mstate [] s) as FC. { sep_apply (hc3b_mix_mstate_fc sh (mstate_val CK H) s). entailer!. }
assert (field_compatible t_mstate (DOT FH._h) s) as FCh by auto with field_compatible.
rewrite (hc3b_mix_mstate_eq sh CK H s H0 H1). flatten_sepcon_in_SEP.
rewrite hc3b_mix_out32.
rewrite <- (hc3b_mix_hin_ne sh H) by lia.
forward_call (gv, Tsh, v_t, sh, field_address t_mstate (DOT FH._h) s, H, shd, d, D).
{ entailer!. simpl. rewrite H1. hc3b_mix_fa. }
assert (LT: Zlength (mix_hash H D) = 32) by apply hc3b_mix_mh_len.
change (HASH (H ++ D)) with (mix_hash H D).
forget (mix_hash H D) as T.
rewrite (hc3b_mix_hin_ne sh H) by lia.
sep_apply (hc3b_mix_hbytes_out sh H (field_address t_mstate (DOT FH._h) s)).
rewrite H1.
replace (hout sh 32 (field_address t_mstate (DOT FH._h) s))
  with (hout sh (Zlength T) (field_address t_mstate (DOT FH._h) s)) by (rewrite LT; reflexivity).
forward_call (sh, field_address t_mstate (DOT FH._h) s, Tsh, v_t, T).
{ entailer!. simpl. rewrite ?LT. hc3b_mix_fa. }
sep_apply (hc3b_mix_back32 T v_t LT).
rewrite (hc3b_mix_mstate_eq sh CK T s H0 LT).
entailer!.
Qed.

Lemma hc3_body_m_mix_ck :
  @semax_body [] (hc3_G_m_mix_ck) CSks FH.f_m_mix_ck (m_mix_ck_spec).
Proof.
start_function.
assert_PROP (field_compatible t_mstate [] s) as FC. { sep_apply (hc3b_mix_mstate_fc sh (mstate_val CK H) s). entailer!. }
assert (field_compatible t_mstate (DOT FH._ck) s) as FCk by auto with field_compatible.
rewrite (hc3b_mix_mstate_eq sh CK H s H0 H1). flatten_sepcon_in_SEP.
rewrite !hc3b_mix_out32.
forward_call (gv, Tsh, v_t1, Tsh, v_t2, Tsh, v_t3, sh, field_address t_mstate (DOT FH._ck) s, CK, shd, d, D).
{ entailer!. simpl. hc3b_mix_fa. }
destruct (hc3b_mix_kdf_len CK D) as [L1 [L2 L3]].
forget (kdf1 CK D) as K1. forget (kdf2 CK D) as K2. forget (kdf3 CK D) as K3.
sep_apply (hc3b_mix_hbytes_out sh CK (field_address t_mstate (DOT FH._ck) s)).
rewrite H0.
replace (hout sh 32 (field_address t_mstate (DOT FH._ck) s))
  with (hout sh (Zlength K1) (field_address t_mstate (DOT FH._ck) s)) by (rewrite L1; reflexivity).
forward_call (sh, field_address t_mstate (DOT FH._ck) s, Tsh, v_t1, K1).
{ entailer!. simpl. rewrite ?L1. hc3b_mix_fa. }
sep_apply (hc3b_mix_back32 K1 v_t1 L1).
sep_apply (hc3b_mix_back32 K2 v_t2 L2).
sep_apply (hc3b_mix_back32 K3 v_t3 L3).
rewrite (hc3b_mix_mstate_eq sh K1 H s L1 H1).
entailer!.
Qed.

Lemma hc3_body_m_mix_key :
  @semax_body [] (hc3_G_m_mix_ck) CSks FH.f_m_mix_key (m_mix_key_spec).
Proof.
start_function.
assert_PROP (field_compatible t_mstate [] s) as FC. { sep_apply (hc3b_mix_mstate_fc sh (mstate_val CK H) s). entailer!. }
assert (field_compatible t_mstate (DOT FH._ck) s) as FCk by auto with field_compatible.
rewrite (hc3b_mix_mstate_eq sh CK H s H0 H1). flatten_sepcon_in_SEP.
rewrite !hc3b_mix_out32.
forward_call (gv, Tsh, v_t1, Tsh, v_t2, Tsh, v_t3, sh, field_address t_mstate (DOT FH._ck) s, CK, shd, d, D).
{ entailer!. simpl. hc3b_mix_fa. }
destruct (hc3b_mix_kdf_len CK D) as [L1 [L2 L3]].
forget (kdf1 CK D) as K1. forget (kdf2 CK D) as K2. forget (kdf3 CK D) as K3.
sep_apply (hc3b_mix_hbytes_out sh CK (field_address t_mstate (DOT FH._ck) s)).
rewrite H0.
replace (hout sh 32 (field_address t_mstate (DOT FH._ck) s))
  with (hout sh (Zlength K1) (field_address t_mstate (DOT FH._ck) s)) by (rewrite L1; reflexivity).
forward_call (sh, field_address t_mstate (DOT FH._ck) s, Tsh, v_t1, K1).
{ entailer!. simpl. rewrite ?L1. hc3b_mix_fa. }
replace (hout shk 32 k) with (hout shk (Zlength K2) k) by (rewrite L2; reflexivity).
forward_call (shk, k, Tsh, v_t2, K2).
{ entailer!. simpl. rewrite ?L2. reflexivity. }
sep_apply (hc3b_mix_back32 K1 v_t1 L1).
sep_apply (hc3b_mix_back32 K2 v_t2 L2).
sep_apply (hc3b_mix_back32 K3 v_t3 L3).
rewrite (hc3b_mix_mstate_eq sh K1 H s L1 H1).
entailer!.
Qed.

Lemma hc3_body_m_mix_psk :
  @semax_body [] (hc3_G_m_mix_psk) CSks FH.f_m_mix_psk (m_mix_psk_spec).
Proof.
start_function.
assert_PROP (field_compatible t_mstate [] s) as FC. { sep_apply (hc3b_mix_mstate_fc sh (mstate_val CK H) s). entailer!. }
assert (field_compatible t_mstate (DOT FH._ck) s) as FCk by auto with field_compatible.
rewrite (hc3b_mix_mstate_eq sh CK H s H0 H1). flatten_sepcon_in_SEP.
rewrite !hc3b_mix_out32.
rewrite <- (hc3b_mix_hin_ne shp PSK) by lia.
forward_call (gv, Tsh, v_t1, Tsh, v_t2, Tsh, v_t3, sh, field_address t_mstate (DOT FH._ck) s, CK, shp, p, PSK).
{ entailer!. simpl. rewrite H2. hc3b_mix_fa. }
destruct (hc3b_mix_kdf_len CK PSK) as [L1 [L2 L3]].
forget (kdf1 CK PSK) as K1. forget (kdf2 CK PSK) as K2. forget (kdf3 CK PSK) as K3.
rewrite (hc3b_mix_hin_ne shp PSK) by lia.
sep_apply (hc3b_mix_hbytes_out sh CK (field_address t_mstate (DOT FH._ck) s)).
rewrite H0.
replace (hout sh 32 (field_address t_mstate (DOT FH._ck) s))
  with (hout sh (Zlength K1) (field_address t_mstate (DOT FH._ck) s)) by (rewrite L1; reflexivity).
forward_call (sh, field_address t_mstate (DOT FH._ck) s, Tsh, v_t1, K1).
{ entailer!. simpl. rewrite ?L1. hc3b_mix_fa. }
replace (hout shk 32 k) with (hout shk (Zlength K3) k) by (rewrite L3; reflexivity).
forward_call (shk, k, Tsh, v_t3, K3).
{ entailer!. simpl. rewrite ?L3. reflexivity. }
sep_apply (derives_refl' _ _ (eq_sym (hc3b_mix_mstate_eq sh K1 H s L1 H1))).
rewrite <- (hc3b_mix_hin_ne Tsh K2) by lia.
forward_call (gv, sh, s, K1, H, Tsh, v_t2, K2).
{ entailer!. simpl. rewrite ?L2. reflexivity. }
rewrite (hc3b_mix_hin_ne Tsh K2) by lia.
sep_apply (hc3b_mix_back32 K1 v_t1 L1).
sep_apply (hc3b_mix_back32 K2 v_t2 L2).
sep_apply (hc3b_mix_back32 K3 v_t3 L3).
entailer!.
Qed.

Lemma hc3_body_m_encrypt_and_hash :
  @semax_body [] (hc3_G_m_encrypt_and_hash aead_enc) CSks FH.f_m_encrypt_and_hash (m_encrypt_and_hash_spec aead_enc).
Proof.
start_function.
assert_PROP (field_compatible t_mstate [] s) as FC. { sep_apply (hc3b_mix_mstate_fc sh (mstate_val CK H) s). entailer!. }
assert (field_compatible t_mstate (DOT FH._h) s) as FCh by auto with field_compatible.
rewrite (hc3b_mix_mstate_eq sh CK H s H0 H1). flatten_sepcon_in_SEP.
rewrite hc3b_mix_hout_cs, hc3b_mix_hin_prim, (hc3b_mix_hbytes_key shk KEY k H2), hc3b_mix_zero_page.
rewrite (hc3b_mix_hbytes_prim sh H) by lia.
forward_call (shc, c, shp, p, P, sh, field_address t_mstate (DOT FH._h) s, H, 0, shk, k, KEY, gv).
{ entailer!. simpl. rewrite H1. hc3b_mix_fa. }
pose proof (aead_enc_length _ _ AEAD KEY 0 H P) as LE.
forget (aead_enc KEY 0 H P) as E.
rewrite <- LE, <- hc3b_mix_hbytes_cs, <- hc3b_mix_hin_prim, <- (hc3b_mix_hbytes_key shk KEY k H2),
  <- hc3b_mix_zero_page.
rewrite <- (hc3b_mix_hbytes_prim sh H) by lia.
sep_apply (derives_refl' _ _ (eq_sym (hc3b_mix_mstate_eq sh CK H s H0 H1))).
rewrite <- (hc3b_mix_hin_ne shc E) by (rewrite LE; pose proof (Zlength_nonneg P); lia).
forward_call (gv, sh, s, CK, H, shc, c, E).
{ entailer!. simpl. rewrite LE. reflexivity. }
rewrite (hc3b_mix_hin_ne shc E) by (rewrite LE; pose proof (Zlength_nonneg P); lia).
entailer!.
Qed.

Lemma hc3_body_m_decrypt_and_hash :
  @semax_body [] (hc3_G_m_decrypt_and_hash aead_dec) CSks FH.f_m_decrypt_and_hash (m_decrypt_and_hash_spec aead_dec).
Proof.
start_function.
assert_PROP (field_compatible t_mstate [] s) as FC. { sep_apply (hc3b_mix_mstate_fc sh (mstate_val CK H) s). entailer!. }
assert (field_compatible t_mstate (DOT FH._h) s) as FCh by auto with field_compatible.
rewrite (hc3b_mix_mstate_eq sh CK H s H0 H1). flatten_sepcon_in_SEP.
rewrite hc3b_mix_prim_out_cs, hc3b_mix_hin_prim, (hc3b_mix_hbytes_key shk KEY k H2), hc3b_mix_zero_page.
rewrite (hc3b_mix_hbytes_prim sh H) by lia.
forward_call (shp, p, old, shc, c, C, sh, field_address t_mstate (DOT FH._h) s, H, 0, shk, k, KEY, gv).
{ entailer!. simpl. rewrite H1. hc3b_mix_fa. }
rewrite <- hc3b_mix_hin_prim, <- (hc3b_mix_hbytes_key shk KEY k H2), <- hc3b_mix_zero_page,
  <- hc3b_mix_prim_out_cs.
rewrite <- (hc3b_mix_hbytes_prim sh H) by lia.
sep_apply (derives_refl' _ _ (eq_sym (hc3b_mix_mstate_eq sh CK H s H0 H1))).
destruct (aead_dec KEY 0 H C) as [pt|] eqn:HD.
- forward_if.
  + exfalso; apply Int.one_not_zero; assumption.
  + forward_call (gv, sh, s, CK, H, shc, c, C).
    forward.
    unfold bytes. cancel.
- forward_if.
  + forward. cancel.
  + exfalso; apply H5; reflexivity.
Qed.

(* the group *)
Theorem hc3_bodies_mix :
  (@semax_body [] (hc3_G_m_mix_hash) CSks FH.f_m_mix_hash (m_mix_hash_spec)) /\
  (@semax_body [] (hc3_G_m_mix_ck) CSks FH.f_m_mix_ck (m_mix_ck_spec)) /\
  (@semax_body [] (hc3_G_m_mix_ck) CSks FH.f_m_mix_key (m_mix_key_spec)) /\
  (@semax_body [] (hc3_G_m_mix_psk) CSks FH.f_m_mix_psk (m_mix_psk_spec)) /\
  (@semax_body [] (hc3_G_m_encrypt_and_hash aead_enc) CSks FH.f_m_encrypt_and_hash (m_encrypt_and_hash_spec aead_enc)) /\
  (@semax_body [] (hc3_G_m_decrypt_and_hash aead_dec) CSks FH.f_m_decrypt_and_hash (m_decrypt_and_hash_spec aead_dec)).
Proof.
exact (conj hc3_body_m_mix_hash (conj hc3_body_m_mix_ck (conj hc3_body_m_mix_key (conj hc3_body_m_mix_psk
  (conj hc3_body_m_encrypt_and_hash hc3_body_m_decrypt_and_hash))))).
Qed.

End Bodies.
