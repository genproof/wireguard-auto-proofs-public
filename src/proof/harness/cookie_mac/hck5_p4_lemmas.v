(* law cookie_mac, phase P4: helpers (port of v1 hck3_p4_lemmas.v.old: p's cookie as main's
   field_ats at W_cookie_mac, B's checker's birthdate and secret). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.blake2s.model.
Require WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.harness.cookie_mac.hck5_cut.
Require Import WgNoise.proof.harness.cookie_mac.hck5_defs.
Local Open Scope logic.

Lemma hck5_p4_prest_fc sh p P : hck5_prest sh p P |-- !! @field_compatible Noise.CS t_peer [] p.
Proof. unfold hck5_prest. entailer!. Qed.

Lemma hck5_p4_drest_fc sh p D : hck5_drest sh p D |-- !! @field_compatible Noise.CS t_dev [] p.
Proof. unfold hck5_drest. entailer!. Qed.

#[local] Instance hck5_p4_cce_N : change_composite_env Noise.CS W_cookie_mac.
Proof. make_cs_preserve Noise.CS W_cookie_mac. Defined.

Section W.
#[local] Existing Instance W_cookie_mac.

Lemma hck5_p4_test p v :
  field_compatible t_peer [] p ->
  data_at Tsh t_cookie v (cookie_addr p) = field_at Tsh t_peer (DOT HK._latest_cookie) v p.
Proof.
  intros Hfc.
  rewrite field_at_data_at. f_equal.
  rewrite field_address_offset by auto with field_compatible. reflexivity.
Qed.

(* p's cookie: the fields main does not touch (keys, padding, lock) *)
Definition hck5_p4_ckrest (p: val) (C: cookie) (lk: val) : mpred :=
  field_at Tsh t_peer (DOT HK._latest_cookie DOT HK._cookie_decryption_key) (bytes (ck_dkey C)) p *
  field_at Tsh t_peer (DOT HK._latest_cookie DOT HK._message_mac1_key) (bytes (ck_mkey C)) p *
  spacer Tsh 466 468 p *
  field_at Tsh t_peer (DOT HK._latest_cookie DOT HK._lock) lk p.

Lemma hck5_p4_open p C lk :
  @field_compatible Noise.CS t_peer [] p ->
  @data_at Noise.CS Tsh t_cookie (cookie_val C lk) (cookie_addr p) =
  field_at Tsh t_peer (DOT HK._latest_cookie DOT HK._birthdate) (Vlong (ck_birth C)) p *
  field_at Tsh t_peer (DOT HK._latest_cookie DOT HK._is_valid) (Val.of_bool (ck_valid C)) p *
  data_at Tsh (tarray tuchar 16) (bytes (ck_cookie C)) (offset_val 369 p) *
  field_at Tsh t_peer (DOT HK._latest_cookie DOT HK._have_sent_mac1) (Val.of_bool (ck_sent C)) p *
  data_at Tsh (tarray tuchar 16) (bytes (ck_last_mac1 C)) (offset_val 386 p) *
  hck5_p4_ckrest p C lk.
Proof.
  intros Hfc0.
  assert (Hfc: field_compatible t_peer [] p).
  { revert Hfc0. apply field_compatible_change_composite. reflexivity. }
  rewrite (@data_at_change_composite Noise.CS W_cookie_mac _ Tsh t_cookie (cookie_val C lk) (cookie_val C lk) (JMeq_refl _))
    by prove_cs_preserve_type.
  rewrite hck5_p4_test by auto.
  unfold_field_at 1%nat.
  rewrite (field_at_data_at Tsh t_peer (DOT HK._latest_cookie DOT HK._cookie)).
  rewrite (field_at_data_at Tsh t_peer (DOT HK._latest_cookie DOT HK._last_mac1_sent)).
  rewrite !field_address_offset by auto with field_compatible.
  unfold hck5_p4_ckrest. simpl. apply pred_ext; cancel.
Qed.
(* B's checker: the fields main does not touch *)
Definition hck5_p4_ccrest (wb: val) (CC: checker) (lk: val) : mpred :=
  field_at Tsh t_dev (DOT HK._cookie_checker DOT HK._cookie_encryption_key) (bytes (cc_ekey CC)) wb *
  field_at Tsh t_dev (DOT HK._cookie_checker DOT HK._message_mac1_key) (bytes (cc_mkey CC)) wb *
  field_at Tsh t_dev (DOT HK._cookie_checker DOT HK._secret_lock) lk wb *
  spacer Tsh 188 192 wb *
  field_at Tsh t_dev (DOT HK._cookie_checker DOT HK._device) (cc_dev CC) wb.

Lemma hck5_p4_test_cc p v :
  field_compatible t_dev [] p ->
  data_at Tsh t_cc v (cc_addr p) = field_at Tsh t_dev (DOT HK._cookie_checker) v p.
Proof.
  intros Hfc.
  rewrite field_at_data_at. f_equal.
  rewrite field_address_offset by auto with field_compatible. reflexivity.
Qed.

Lemma hck5_p4_cc_open wb CC (lk: val) :
  @field_compatible Noise.CS t_dev [] wb ->
  @data_at Noise.CS Tsh t_cc (bytes (cc_secret CC), (bytes (cc_ekey CC), (bytes (cc_mkey CC),
                              (Vlong (cc_birth CC), (lk, cc_dev CC))))) (cc_addr wb) =
  data_at Tsh (tarray tuchar 32) (bytes (cc_secret CC)) (offset_val 80 wb) *
  field_at Tsh t_dev (DOT HK._cookie_checker DOT HK._secret_birthdate) (Vlong (cc_birth CC)) wb *
  hck5_p4_ccrest wb CC lk.
Proof.
  intros Hfc0.
  assert (Hfc: field_compatible t_dev [] wb).
  { revert Hfc0. apply field_compatible_change_composite. reflexivity. }
  erewrite (@data_at_change_composite Noise.CS W_cookie_mac _ Tsh t_cc _ _ (JMeq_refl _))
    by prove_cs_preserve_type.
  rewrite hck5_p4_test_cc by auto.
  unfold_field_at 1%nat.
  rewrite (field_at_data_at Tsh t_dev (DOT HK._cookie_checker DOT HK._secret)).
  rewrite !field_address_offset by auto with field_compatible.
  unfold hck5_p4_ccrest. simpl. apply pred_ext; cancel.
Qed.
Lemma hck5_p4_ck_fold p bd vd ckb sd m1 C0 lk :
  @field_compatible Noise.CS t_peer [] p ->
  Zlength ckb = 16 -> Zlength m1 = 16 -> cookie_ok C0 ->
  field_at Tsh t_peer (DOT HK._latest_cookie DOT HK._birthdate) (Vlong bd) p *
  field_at Tsh t_peer (DOT HK._latest_cookie DOT HK._is_valid) (Val.of_bool vd) p *
  data_at Tsh (tarray tuchar 16) (bytes ckb) (offset_val 369 p) *
  field_at Tsh t_peer (DOT HK._latest_cookie DOT HK._have_sent_mac1) (Val.of_bool sd) p *
  data_at Tsh (tarray tuchar 16) (bytes m1) (offset_val 386 p) *
  hck5_p4_ckrest p C0 lk
  |-- cookie_rep Tsh (cookie_addr p) (mkCookie bd vd ckb sd m1 (ck_dkey C0) (ck_mkey C0)).
Proof.
  intros Hfc L1 L2 (_ & _ & L3 & L4).
  unfold cookie_rep. Exists lk.
  rewrite (hck5_p4_open p (mkCookie bd vd ckb sd m1 (ck_dkey C0) (ck_mkey C0)) lk Hfc).
  unfold hck5_p4_ckrest; simpl. entailer!. unfold cookie_ok; simpl; auto.
Qed.

Lemma hck5_p4_cc_fold wb CC bd lk :
  @field_compatible Noise.CS t_dev [] wb -> cc_ok CC ->
  data_at Tsh (tarray tuchar 32) (bytes (cc_secret CC)) (offset_val 80 wb) *
  field_at Tsh t_dev (DOT HK._cookie_checker DOT HK._secret_birthdate) (Vlong bd) wb *
  hck5_p4_ccrest wb CC lk
  |-- checker_rep Tsh (cc_addr wb) (mkChk (cc_secret CC) (cc_ekey CC) (cc_mkey CC) bd (cc_dev CC)).
Proof.
  intros Hfc HCC.
  unfold checker_rep. Exists lk.
  rewrite (hck5_p4_cc_open wb (mkChk (cc_secret CC) (cc_ekey CC) (cc_mkey CC) bd (cc_dev CC)) lk Hfc).
  unfold hck5_p4_ccrest; simpl. entailer!.
Qed.

Lemma hck5_p4_cc_unfold wb CC :
  @field_compatible Noise.CS t_dev [] wb ->
  checker_rep Tsh (cc_addr wb) CC |--
  EX lk: val, !! cc_ok CC &&
  (data_at Tsh (tarray tuchar 32) (bytes (cc_secret CC)) (offset_val 80 wb) *
   field_at Tsh t_dev (DOT HK._cookie_checker DOT HK._secret_birthdate) (Vlong (cc_birth CC)) wb *
   hck5_p4_ccrest wb CC lk).
Proof.
  intros Hfc. unfold checker_rep. Intros lk. Exists lk.
  rewrite (hck5_p4_cc_open wb CC lk Hfc). entailer!.
Qed.
End W.

Lemma hck5_p4_nd (bs: list Z) :
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  map (fun b => Vint (Int.repr b)) bs = bytes (map Byte.repr bs).
Proof.
  intros HF. unfold bytes. rewrite map_map. apply map_ext_Forall. eapply Forall_impl; [| exact HF].
  intros b Hb. simpl. unfold Vubyte. rewrite Byte.unsigned_repr by (unfold Byte.max_unsigned in *; lia). reflexivity.
Qed.

Lemma hck5_p4_bool (x: int) :
  Vint (if Int.eq x Int.zero then Int.zero else Int.one) = Val.of_bool (negb (Int.eq x Int.zero)).
Proof. destruct (Int.eq x Int.zero); reflexivity. Qed.

Lemma hck5_p4_and1 (b: Z) :
  0 <= b <= Byte.max_unsigned ->
  Int.and (Int.repr b) (Int.repr 1) = if Z.odd b then Int.one else Int.zero.
Proof.
  intros Hb.
  replace (Int.repr 1) with (Int.sub (Int.repr 2) Int.one) by reflexivity.
  rewrite <- (Int.modu_and (Int.repr b) (Int.repr 2) (Int.repr 1)) by reflexivity.
  unfold Int.modu. rewrite !Int.unsigned_repr by (unfold Byte.max_unsigned in *; rep_lia).
  rewrite Zmod_odd. destruct (Z.odd b); reflexivity.
Qed.

Lemma hck5_p4_CC2_true x25519 R L now :
  hck5_CC2 x25519 R L now true =
  mkChk (cc_secret (hck5_CC1 x25519 R L)) (cc_ekey (hck5_CC1 x25519 R L)) (cc_mkey (hck5_CC1 x25519 R L))
        (if birthdate_expired (cc_birth (hck5_CC1 x25519 R L)) (Int64.repr 120) now then now
         else cc_birth (hck5_CC1 x25519 R L)) (cc_dev (hck5_CC1 x25519 R L)).
Proof.
  unfold hck5_CC2. cbv beta zeta. change (andb true ?b) with b.
  destruct (birthdate_expired (cc_birth (hck5_CC1 x25519 R L)) (Int64.repr 120) now); reflexivity.
Qed.

Lemma hck5_p4_CC2_false x25519 R L now : hck5_CC2 x25519 R L now false = hck5_CC1 x25519 R L.
Proof. reflexivity. Qed.

Lemma hck5_p4_cookie_len k s : Zlength (cookie_of k s) = 16.
Proof.
  unfold cookie_of, MAC, blake2s, b2s_digest_stream, b2s_out. rewrite Zlength_map. reflexivity.
Qed.

Lemma hck5_p4_hbytes sh n bs p :
  Zlength bs = n ->
  @data_at W_cookie_mac sh (tarray tuchar n) (bytes bs) p = hbytes sh bs p.
Proof.
  intros <-. unfold hbytes. apply WgNoise.proof.libc.libc_bytes.data_at_tarray_tuchar_cs.
Qed.

Lemma hck5_p4_hout sh n p :
  @data_at_ W_cookie_mac sh (tarray tuchar n) p = hout sh n p.
Proof.
  unfold hout. apply WgNoise.proof.libc.libc_bytes.data_at__tarray_tuchar_cs.
Qed.
