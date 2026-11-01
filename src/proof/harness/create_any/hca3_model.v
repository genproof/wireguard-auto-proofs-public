(* law create_any (harness/create_any.c): the harness's step-by-step expectation as Coq functions, and
   its agreement with the kernel's model (prot_model3's create_initiation_model / create_response_model, the
   models of prot_specs3's ci_res / cr_res).

   hca3_init_exp / hca3_resp_exp follow main's op == 0 / op == 1 branch statement by statement:
   - exp: the expected message image (148 / 92 bytes), starting from `before` (the image of the pre-filled
     message) and overwritten field by field (le32_store / bytes_copy / m_encrypt_and_hash at the offsets);
   - the handshake fields of the snapshot x (hs_snap) the harness updates: ephemeral private, chaining key,
     hash, state; every other field as in the snapshot's handshake H;
   - ok: the harness's `ok` flag.
   Arguments: okid = ia.ok (m_identity_of), SPUB = wa.static_identity.static_public, H = the snapshot's
   handshake (s), r = wg_shim_random_log after the call (the drawn ephemeral bytes), ts = m_tai64n of the real
   clock, u = wg_shim_random_u32 after the call (the index the table drew). *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.protocol.prot_model3.

Local Open Scope Z_scope.

Section Model.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.

(* write the bytes w at offset o of the image b *)
Definition hca3_put (b: list byte) (o: Z) (w: list byte) : list byte :=
  sublist 0 o b ++ w ++ sublist (o + Zlength w) (Zlength b) b.

(* main, op == 0, after wg_noise_handshake_create_initiation *)
Definition hca3_init_exp (okid: bool) (SPUB: list byte) (H: handshake) (before r ts: list byte) (u: int)
  : bool * list byte * handshake :=
  if negb okid then (false, before, H) else
  let exp0 := hca3_put before 0 (le32 (Int.repr 1)) in
  let ck0 := init_ck in
  let h0 := mix_hash init_hash (hs_rstatic H) in
  let eph := clamp r in
  let x0 := hs_set_eph (hs_set_ckh H ck0 h0) eph in
  let E := x25519 eph basepoint9 in
  let exp1 := hca3_put exp0 8 E in
  if is_zero E then (false, exp1, x0) else
  let h1 := mix_hash h0 E in
  let ck1 := kdf1 ck0 E in
  let x1 := hs_set_ckh x0 ck1 h1 in
  if negb (dh_ok x25519 eph (hs_rstatic H)) then (false, exp1, x1) else
  let dh := x25519 eph (hs_rstatic H) in
  let ck2 := kdf1 ck1 dh in
  let key2 := kdf2 ck1 dh in
  let encs := aead_enc key2 0 h1 SPUB in
  let h2 := mix_hash h1 encs in
  let exp2 := hca3_put exp1 40 encs in
  let x2 := hs_set_ckh x1 ck2 h2 in
  if is_zero (hs_ss H) then (false, exp2, x2) else
  let ck3 := kdf1 ck2 (hs_ss H) in
  let key3 := kdf2 ck2 (hs_ss H) in
  let enct := aead_enc key3 0 h2 ts in
  let h3 := mix_hash h2 enct in
  let exp3 := hca3_put exp2 88 enct in
  let exp4 := hca3_put exp3 4 (le32 u) in
  (true, exp4, hs_set_state (hs_set_ckh x2 ck3 h3) HS_CREATED_INITIATION).

(* main, op == 1, after wg_noise_handshake_create_response *)
Definition hca3_resp_exp (H: handshake) (before r: list byte) (u: int) : bool * list byte * handshake :=
  if negb (Int.eq (hs_state H) HS_CONSUMED_INITIATION) then (false, before, H) else
  let exp0 := hca3_put (hca3_put before 0 (le32 (Int.repr 2))) 8 (le32 (hs_rindex H)) in
  let eph := clamp r in
  let x0 := hs_set_eph H eph in
  let E := x25519 eph basepoint9 in
  let exp1 := hca3_put exp0 12 E in
  if is_zero E then (false, exp1, x0) else
  let h1 := mix_hash (hs_hash H) E in
  let ck1 := kdf1 (hs_ck H) E in
  let x1 := hs_set_ckh x0 ck1 h1 in
  if negb (dh_ok x25519 eph (hs_reph H)) then (false, exp1, x1) else
  let ck2 := kdf1 ck1 (x25519 eph (hs_reph H)) in
  let x2 := hs_set_ckh x1 ck2 h1 in
  if negb (dh_ok x25519 eph (hs_rstatic H)) then (false, exp1, x2) else
  let ck3 := kdf1 ck2 (x25519 eph (hs_rstatic H)) in
  let ck4 := kdf1 ck3 (hs_psk H) in
  let h2 := mix_hash h1 (kdf2 ck3 (hs_psk H)) in
  let key := kdf3 ck3 (hs_psk H) in
  let encn := aead_enc key 0 h2 [] in
  let h3 := mix_hash h2 encn in
  let exp2 := hca3_put exp1 44 encn in
  let exp3 := hca3_put exp2 4 (le32 u) in
  (true, exp3, hs_set_state (hs_set_ckh x2 ck4 h3) HS_CREATED_RESPONSE).

End Model.

(* the harness's CHECK(!bytes_zero(eph, 32)) after m_clamp *)
Lemma hca3_clamp_nonzero (r: list byte) : Zlength r = 32 -> is_zero (clamp r) = false.
Proof.
  intros L. unfold is_zero, bytes_eqb, clamp. destruct (list_eq_dec _ _ _) as [E|E]; [|reflexivity]. exfalso.
  assert (H31 := f_equal (Znth 31) E).
  rewrite upd_Znth_same in H31 by (rewrite Zlength_upd_Znth; lia).
  rewrite Zlength_upd_Znth, Zlength_upd_Znth, L in H31. unfold zeros in H31.
  rewrite Znth_Zrepeat in H31 by lia. revert H31.
  generalize (Byte.and (Znth 31 r) (Byte.repr 127)). intros c H. rewrite <- (Byte.repr_unsigned c) in H.
  assert (R := Byte.unsigned_range c). change Byte.modulus with 256 in R.
  revert H R. generalize (Byte.unsigned c). intros k H R.
  assert (forall k, 0 <= k < 256 -> Byte.eq (Byte.or (Byte.repr k) (Byte.repr 64)) Byte.zero = false).
  { intros j Hj.
    assert (forallb (fun j => negb (Byte.eq (Byte.or (Byte.repr j) (Byte.repr 64)) Byte.zero))
              (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in H0. specialize (H0 j). rewrite in_map_iff in H0.
    destruct (Byte.eq _ _); [|reflexivity]. discriminate H0.
    exists (Z.to_nat j). split; [lia|]. apply in_seq; lia. }
  specialize (H0 k R). rewrite H, Byte.eq_true in H0. discriminate.
Qed.

(* agreement with the kernel's model: the harness's expectation is exactly create_initiation_model's /
   create_response_model's result (its success flag, the message image, the handshake).  Stated as Props
   (hca3_init_agree, hca3_resp_agree) so that the law's piece can take them as hypotheses. *)
Definition hca3_init_agree (x25519: list byte -> list byte -> list byte)
    (aead_enc: list byte -> Z -> list byte -> list byte -> list byte) : Prop :=
  forall (ID: identity) (H: handshake) (M: init_msg) (r ts: list byte) (idx: int),
  Zlength (id_pub ID) = 32 -> Zlength (hs_rstatic H) = 32 -> Zlength (hs_ss H) = 32 ->
  Zlength (im_eph M) = 32 -> Zlength (im_encs M) = 48 -> Zlength (im_enct M) = 28 ->
  Zlength (im_mac1 M) = 16 -> Zlength (im_mac2 M) = 16 ->
  Zlength r = 32 -> Zlength ts = 12 ->
  let '(b, M', H') := create_initiation_model x25519 aead_enc ID H M r ts idx in
  hca3_init_exp x25519 aead_enc (id_has ID) (id_pub ID) H (init_bytes M) r ts idx = (b, init_bytes M', H').

Definition hca3_resp_agree (x25519: list byte -> list byte -> list byte)
    (aead_enc: list byte -> Z -> list byte -> list byte -> list byte) : Prop :=
  forall (H: handshake) (M: resp_msg) (r: list byte) (idx: int),
  Zlength (hs_reph H) = 32 -> Zlength (hs_rstatic H) = 32 ->
  Zlength (rm_eph M) = 32 -> Zlength (rm_encn M) = 16 -> Zlength (rm_mac1 M) = 16 -> Zlength (rm_mac2 M) = 16 ->
  Zlength r = 32 ->
  let '(b, M', H') := create_response_model x25519 aead_enc H M r idx in
  hca3_resp_exp x25519 aead_enc H (resp_bytes M) r idx = (b, resp_bytes M', H').

Lemma hca3_memneq_zeros32 (X: list byte) : Zlength X = 32 -> memneq_bool X zeros32 = negb (is_zero X).
Proof.
  intros L. unfold memneq_bool, is_zero, bytes_eqb, zeros32, zeros. rewrite L.
  destruct (list_eq_dec _ _ _); reflexivity.
Qed.

Lemma hca3_Zlength_le32 (v: int) : Zlength (le32 v) = 4.
Proof. unfold le32. rewrite Zlength_map. reflexivity. Qed.

Lemma hca3_put_mid (a b c w: list byte) :
  Zlength w = Zlength b -> hca3_put (a ++ b ++ c) (Zlength a) w = a ++ w ++ c.
Proof.
  intros L. unfold hca3_put. rewrite L.
  rewrite sublist_app1 by (try rewrite Zlength_app; list_solve).
  rewrite sublist_same by lia.
  rewrite app_assoc, Zlength_app, !Zlength_app.
  list_solve.
Qed.

Lemma hca3_put_at (a b c w: list byte) (o: Z) :
  o = Zlength a -> Zlength w = Zlength b -> hca3_put (a ++ b ++ c) o w = a ++ w ++ c.
Proof. intros ->. apply hca3_put_mid. Qed.

Lemma hca3_put_type (M: init_msg) (v: int) :
  hca3_put (init_bytes M) 0 (le32 v) =
  init_bytes (mkIM v (im_sender M) (im_eph M) (im_encs M) (im_enct M) (im_mac1 M) (im_mac2 M)).
Proof.
  unfold init_bytes. apply (hca3_put_at []); [reflexivity|]. rewrite !hca3_Zlength_le32. reflexivity.
Qed.

Lemma hca3_put_sender (M: init_msg) (v: int) :
  hca3_put (init_bytes M) 4 (le32 v) =
  init_bytes (mkIM (im_type M) v (im_eph M) (im_encs M) (im_enct M) (im_mac1 M) (im_mac2 M)).
Proof.
  unfold init_bytes. apply hca3_put_at; rewrite ?hca3_Zlength_le32; reflexivity.
Qed.

Lemma hca3_put_eph (M: init_msg) (w: list byte) :
  Zlength (im_eph M) = 32 -> Zlength w = 32 ->
  hca3_put (init_bytes M) 8 w =
  init_bytes (mkIM (im_type M) (im_sender M) w (im_encs M) (im_enct M) (im_mac1 M) (im_mac2 M)).
Proof.
  intros L1 L2. unfold init_bytes; simpl.
  pose proof (hca3_put_at (le32 (im_type M) ++ le32 (im_sender M)) (im_eph M)
    (im_encs M ++ im_enct M ++ im_mac1 M ++ im_mac2 M) w 8) as X.
  rewrite <- !app_assoc in X. apply X; [|lia]. rewrite Zlength_app, !hca3_Zlength_le32. reflexivity.
Qed.

Lemma hca3_put_encs (M: init_msg) (w: list byte) :
  Zlength (im_eph M) = 32 -> Zlength (im_encs M) = 48 -> Zlength w = 48 ->
  hca3_put (init_bytes M) 40 w =
  init_bytes (mkIM (im_type M) (im_sender M) (im_eph M) w (im_enct M) (im_mac1 M) (im_mac2 M)).
Proof.
  intros L1 L2 L3. unfold init_bytes; simpl.
  pose proof (hca3_put_at (le32 (im_type M) ++ le32 (im_sender M) ++ im_eph M) (im_encs M)
    (im_enct M ++ im_mac1 M ++ im_mac2 M) w 40) as X.
  rewrite <- !app_assoc in X. apply X; [|lia]. rewrite !Zlength_app, !hca3_Zlength_le32, L1. reflexivity.
Qed.

Lemma hca3_put_enct (M: init_msg) (w: list byte) :
  Zlength (im_eph M) = 32 -> Zlength (im_encs M) = 48 -> Zlength (im_enct M) = 28 -> Zlength w = 28 ->
  hca3_put (init_bytes M) 88 w =
  init_bytes (mkIM (im_type M) (im_sender M) (im_eph M) (im_encs M) w (im_mac1 M) (im_mac2 M)).
Proof.
  intros L1 L2 L3 L4. unfold init_bytes; simpl.
  pose proof (hca3_put_at (le32 (im_type M) ++ le32 (im_sender M) ++ im_eph M ++ im_encs M) (im_enct M)
    (im_mac1 M ++ im_mac2 M) w 88) as X.
  rewrite <- !app_assoc in X. apply X; [|lia]. rewrite !Zlength_app, !hca3_Zlength_le32, L1, L2. reflexivity.
Qed.

Lemma hca3_init_exp_ok (x25519: list byte -> list byte -> list byte)
    (aead_enc: list byte -> Z -> list byte -> list byte -> list byte) :
  x25519_props x25519 ->
  (forall k n ad m, Zlength (aead_enc k n ad m) = Zlength m + 16) ->
  hca3_init_agree x25519 aead_enc.
Proof.
  intros HX HA ID H M r ts idx L1 L2 L3 L4 L5 L6 L7 L8 L9 L10. unfold x25519_props in HX.
  unfold create_initiation_model, hca3_init_exp.
  destruct (id_has ID); [|reflexivity].
  cbv zeta. cbn [negb].
  assert (Lc: Zlength (clamp r) = 32) by (unfold clamp; rewrite !Zlength_upd_Znth; auto).
  rewrite (hca3_memneq_zeros32 (clamp r)), hca3_clamp_nonzero by auto. cbn [negb].
  rewrite (hca3_memneq_zeros32 (x25519 (clamp r) basepoint9)) by apply HX.
  rewrite hca3_put_type, hca3_put_eph by (cbn [im_eph]; auto).
  destruct (is_zero (x25519 (clamp r) basepoint9)); cbn [negb]; [reflexivity|].
  destruct (dh_ok x25519 (clamp r) (hs_rstatic H)); cbn [negb]; [|reflexivity].
  rewrite hca3_put_encs by (cbn [im_eph im_encs]; rewrite ?HA, ?HX; lia).
  rewrite (hca3_memneq_zeros32 (hs_ss H)) by auto.
  destruct (is_zero (hs_ss H)); cbn [negb]; [reflexivity|].
  rewrite hca3_put_enct by (cbn [im_eph im_encs im_enct]; rewrite ?HA, ?HX; lia).
  rewrite hca3_put_sender. reflexivity.
Qed.

Lemma hca3_resp_memneq (X: list byte) : Zlength X = 32 -> memneq_bool X zeros32 = negb (is_zero X).
Proof.
  intros L. unfold memneq_bool, is_zero, bytes_eqb, zeros32, zeros. rewrite L.
  destruct (list_eq_dec _ _ _); reflexivity.
Qed.

Lemma hca3_resp_le32_len (v: int) : Zlength (le32 v) = 4.
Proof. reflexivity. Qed.

Lemma hca3_resp_exp_ok (x25519: list byte -> list byte -> list byte)
    (aead_enc: list byte -> Z -> list byte -> list byte -> list byte) :
  x25519_props x25519 ->
  (forall k n ad m, Zlength (aead_enc k n ad m) = Zlength m + 16) ->
  hca3_resp_agree x25519 aead_enc.
Proof.
  intros X25 AE H M r idx L1 L2 L3 L4 L5 L6 Lr.
  destruct M as [t s rc e n m1 m2]; cbn [rm_type rm_sender rm_receiver rm_eph rm_encn rm_mac1 rm_mac2] in *.
  unfold create_response_model, hca3_resp_exp.
  destruct (Int.eq (hs_state H) HS_CONSUMED_INITIATION); cbn [negb]; [|reflexivity].
  rewrite (hca3_resp_memneq (clamp r)) by (unfold clamp; rewrite !Zlength_upd_Znth; auto).
  rewrite hca3_clamp_nonzero by auto. cbn [negb].
  rewrite (hca3_resp_memneq (x25519 (clamp r) basepoint9)) by apply X25.
  unfold resp_bytes; cbn [rm_type rm_sender rm_receiver rm_eph rm_encn rm_mac1 rm_mac2].
  set (E := x25519 (clamp r) basepoint9). assert (LE: Zlength E = 32) by apply X25.
  set (enc := aead_enc _ 0 _ []). assert (Lenc: Zlength enc = 16) by (unfold enc; rewrite AE; reflexivity).
  assert (I1: forall (a b c d: list byte), Zlength a = 4 -> Zlength b = 4 -> Zlength c = 4 -> Zlength d = 4 ->
     hca3_put (hca3_put (hca3_put (a ++ le32 s ++ b ++ e ++ n ++ m1 ++ m2) 0 c) 8 d) 12 E =
     c ++ le32 s ++ d ++ E ++ n ++ m1 ++ m2).
  { intros. assert (Zlength (le32 s) = 4) by apply hca3_resp_le32_len. unfold hca3_put. list_solve. }
  assert (I2: forall (a b c d: list byte), Zlength a = 4 -> Zlength b = 4 -> Zlength c = 4 -> Zlength d = 4 ->
     hca3_put (hca3_put (a ++ b ++ c ++ E ++ n ++ m1 ++ m2) 44 enc) 4 d = a ++ d ++ c ++ E ++ enc ++ m1 ++ m2).
  { intros. unfold hca3_put. list_solve. }
  rewrite !I1 by apply hca3_resp_le32_len. rewrite I2 by apply hca3_resp_le32_len.
  destruct (is_zero E); [reflexivity|]. cbn [negb].
  destruct (dh_ok x25519 (clamp r) (hs_reph H)); cbn [negb]; [|reflexivity].
  destruct (dh_ok x25519 (clamp r) (hs_rstatic H)); cbn [negb]; reflexivity.
Qed.
