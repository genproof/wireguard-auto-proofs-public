(* Body proofs of the protocol piece, group cookie_small.
   Target: prot4_ck_bodies_small.  Prove each function's body against its specification (prot_specs3.v) in the
   compspecs of its unit, with the context Gprot4 (prot_prog3.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require Import WgNoise.proof.blake2s.model WgNoise.proof.blake2s.spec WgNoise.proof.blake2s.b2s_spec3.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

(* helpers of wg_cookie_checker_init (Noise.CS) *)
Section CheckerInitNoise.
#[local] Existing Instance Noise.CS.

Lemma prot4_ck_small_ci_secret sh c :
  field_compatible t_cc (DOT N._secret) c ->
  field_at_ sh t_cc (DOT N._secret) c = data_at_ sh (tarray tuchar 32) c.
Proof.
  intros FC. rewrite field_at__data_at_.
  unfold field_address. rewrite if_true by auto. simpl.
  rewrite isptr_offset_val_zero by (apply field_compatible_isptr in FC; auto). reflexivity.
Qed.

Lemma prot4_ck_small_ci_secret_back sh c r :
  field_compatible t_cc (DOT N._secret) c -> Zlength r = 32 ->
  bytes_at sh r c = field_at sh t_cc (DOT N._secret) (bytes r) c.
Proof.
  intros FC Hr. rewrite field_at_data_at. unfold bytes_at. rewrite Hr.
  unfold field_address. rewrite if_true by auto. simpl.
  rewrite isptr_offset_val_zero by (apply field_compatible_isptr in FC; auto). reflexivity.
Qed.

Lemma prot4_ck_small_ci_fold sh c r ek mk b wg :
  Zlength r = 32 -> Zlength ek = 32 -> Zlength mk = 32 ->
  field_at sh t_cc (DOT N._secret) (bytes r) c *
  field_at sh t_cc (DOT N._cookie_encryption_key) (bytes ek) c *
  field_at sh t_cc (DOT N._message_mac1_key) (bytes mk) c *
  field_at sh t_cc (DOT N._secret_birthdate) (Vlong b) c *
  field_at_ sh t_cc (DOT N._secret_lock) c * spacer sh 108 112 c *
  field_at sh t_cc (DOT N._device) wg c
  |-- checker_rep sh c (mkChk r ek mk b wg).
Proof.
  intros Hr Hek Hmk. unfold checker_rep. Exists Vundef.
  unfold cc_ok; simpl.
  assert_PROP (field_compatible t_cc [] c) as FC.
  { rewrite (field_at_compatible' sh t_cc (DOT N._secret)). entailer!.
    destruct H as (? & ? & ? & ? & ?). repeat split; auto. }
  unfold_data_at (data_at sh t_cc _ c).
  unfold field_at_. entailer!.
Qed.
End CheckerInitNoise.

Section CookieSmall.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Cookie.CS.
Local Open Scope logic.

Definition prot4_ck_small_G := Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Cookie.CS.

#[local] Instance prot4_ck_small_CCE_b2s_cookie : change_composite_env Blake2s.CS Cookie.CS.
Proof. make_cs_preserve Blake2s.CS Cookie.CS. Defined.
#[local] Instance prot4_ck_small_CCE_cookie_b2s : change_composite_env Cookie.CS Blake2s.CS.
Proof. make_cs_preserve Cookie.CS Blake2s.CS. Defined.
#[local] Instance prot4_ck_small_CCE_noise_b2s : change_composite_env Noise.CS Blake2s.CS.
Proof. make_cs_preserve Noise.CS Blake2s.CS. Defined.
#[local] Instance prot4_ck_small_CCE_b2s_noise : change_composite_env Blake2s.CS Noise.CS.
Proof. make_cs_preserve Blake2s.CS Noise.CS. Defined.

Lemma prot4_ck_small_blake2s_len key outlen msg :
  0 <= outlen -> Zlength (blake2s key outlen msg) = outlen.
Proof.
  intros. unfold blake2s, b2s_digest_stream, b2s_out.
  rewrite Zlength_map, Zlength_correct, upto_length. lia.
Qed.

(* byte buffers of the specs (Noise.CS) as the BLAKE2s specs' (Blake2s.CS) *)
Lemma prot4_ck_small_ba_b2s sh bs p :
  Zlength bs <> 0 -> bytes_at sh bs p = b2s_bytes sh bs p.
Proof.
  intros. unfold bytes_at. rewrite b2s_bytes_nonempty by auto.
  apply (@data_at_cs_eq Noise.CS Blake2s.CS _); [apply JMeq_refl | reflexivity].
Qed.

Lemma prot4_ck_small_out_b2s sh n p :
  @data_at_ Noise.CS sh (tarray tuchar n) p = @data_at_ Blake2s.CS sh (tarray tuchar n) p.
Proof. apply (@data_at__cs_eq Noise.CS Blake2s.CS _). reflexivity. Qed.

Lemma prot4_ck_small_b2s_ba sh n bs p :
  Zlength bs = n ->
  @data_at Blake2s.CS sh (tarray tuchar n) (map Vubyte bs) p = bytes_at sh bs p.
Proof.
  intros; subst n. unfold bytes_at.
  apply (@data_at_cs_eq Blake2s.CS Noise.CS _); [apply JMeq_refl | reflexivity].
Qed.

Definition prot4_ck_small_swab16_ok (x: Z) : bool :=
  Int.eq (Int.zero_ext 16 (Int.or (Int.shr (Int.repr x) (Int.repr 8)) (Int.shl (Int.repr x) (Int.repr 8))))
         (Int.repr (swab16 x)).

Lemma prot4_ck_small_swab16_all :
  forallb (fun a => forallb (fun b => prot4_ck_small_swab16_ok (256 * Z.of_nat a + Z.of_nat b))
                            (seq 0 256)) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma prot4_ck_small_swab16_eq x :
  0 <= x <= 65535 ->
  Int.zero_ext 16 (Int.or (Int.shr (Int.repr x) (Int.repr 8)) (Int.shl (Int.repr x) (Int.repr 8))) =
  Int.repr (swab16 x).
Proof.
  intros Hx.
  pose proof prot4_ck_small_swab16_all as A.
  rewrite forallb_forall in A.
  assert (Ha: In (Z.to_nat (x / 256)) (seq 0 256)) by (apply in_seq; Z.div_mod_to_equations; lia).
  specialize (A _ Ha). rewrite forallb_forall in A.
  assert (Hb: In (Z.to_nat (x mod 256)) (seq 0 256)) by (apply in_seq; Z.div_mod_to_equations; lia).
  specialize (A _ Hb).
  rewrite !Z2Nat.id in A by (Z.div_mod_to_equations; lia).
  rewrite <- Z_div_mod_eq_full in A.
  unfold prot4_ck_small_swab16_ok in A.
  apply Int.same_if_eq. exact A.
Qed.

Lemma prot4_ck_small_body_swab16 :
  @semax_body (QPvarspecs Cookie.qp) prot4_ck_small_G Cookie.CS
      WgNoise.cookie.code.f_quickproof_swab16 quickproof_swab16_spec.
Proof.
start_function.
forward.
rewrite prot4_ck_small_swab16_eq by auto.
entailer!.
rewrite <- prot4_ck_small_swab16_eq by auto. rewrite Int.zero_ext_idem by lia. reflexivity.
Qed.

Lemma prot4_ck_small_body_checker_init :
  @semax_body (QPvarspecs Cookie.qp) prot4_ck_small_G Cookie.CS
      WgNoise.cookie.code.f_wg_cookie_checker_init wg_cookie_checker_init_spec.
Proof.
start_function.
forward_call (gv, S, w).
erewrite (@field_at__change_composite Noise.CS Cookie.CS _ sh t_cc (DOT N._secret_birthdate)); [| prove_cs_preserve_type].
erewrite (@field_at__change_composite Noise.CS Cookie.CS _ sh t_cc (DOT N._device)); [| prove_cs_preserve_type].
forward.
assert_PROP (@field_compatible Noise.CS t_cc (DOT N._secret) c) as FCs by entailer!.
rewrite (prot4_ck_small_ci_secret sh c FCs).
forward_call (gv, S, w, sh, c, 32).
{ entailer!. simpl. rewrite isptr_offset_val_zero by auto. reflexivity. }
Intros r.
forward.
Exists r.
rewrite (prot4_ck_small_ci_secret_back sh c r FCs) by auto.
erewrite (@field_at_change_composite Cookie.CS Noise.CS _ sh t_cc (DOT N._secret_birthdate)); [| apply JMeq_refl | prove_cs_preserve_type].
erewrite (@field_at_change_composite Cookie.CS Noise.CS _ sh t_cc (DOT N._device)); [| apply JMeq_refl | prove_cs_preserve_type].
sep_apply (prot4_ck_small_ci_fold sh c r ek mk (s_boot S) wg); auto.
entailer!.
Qed.

Lemma prot4_ck_small_body_precompute_key :
  @semax_body (QPvarspecs Cookie.qp) prot4_ck_small_G Cookie.CS
      WgNoise.cookie.code.f_precompute_key precompute_key_spec.
Proof.
start_function.
erewrite (@data_at__change_composite Cookie.CS Blake2s.CS _ Tsh); [| prove_cs_preserve_type].
forward_call (Tsh, v_blake, 32).
rewrite (prot4_ck_small_ba_b2s shl label lp) by lia.
rewrite (prot4_ck_small_ba_b2s shp pub pp) by lia.
forward_call (Tsh, v_blake, @nil byte, 32, @nil byte, shl, lp, label, gv).
{ entailer!. rewrite H0. reflexivity. }
rewrite app_nil_l.
forward_call (Tsh, v_blake, @nil byte, 32, label, shp, pp, pub, gv).
{ entailer!. rewrite H. reflexivity. }
rewrite (prot4_ck_small_out_b2s shk 32 kp).
forward_call (Tsh, v_blake, @nil byte, 32, label ++ pub, shk, kp, gv).
sep_apply (@data_at_data_at_ Blake2s.CS Tsh t_blake2s_ctx b2s_ctx_zero v_blake).
erewrite (@data_at__change_composite Blake2s.CS Cookie.CS _ Tsh t_blake2s_ctx); [| prove_cs_preserve_type].
rewrite (prot4_ck_small_b2s_ba shk 32 (blake2s [] 32 (label ++ pub)) kp)
  by (apply prot4_ck_small_blake2s_len; lia).
rewrite <- (prot4_ck_small_ba_b2s shl label lp) by lia.
rewrite <- (prot4_ck_small_ba_b2s shp pub pp) by lia.
unfold label_key.
entailer!.
Qed.

Lemma prot4_ck_small_dk_fc wg :
  @field_compatible Noise.CS t_dev [] wg -> @field_compatible Cookie.CS t_dev [] wg.
Proof. intros. apply (@field_compatible_change_composite Noise.CS Cookie.CS _ t_dev); [prove_cs_preserve_type | auto]. Qed.

Lemma prot4_ck_small_dk_id_split sh wg pub priv lk has :
  @field_compatible Noise.CS t_dev [] wg ->
  @data_at Noise.CS sh t_sid (bytes pub, (bytes priv, (lk, has))) (id_addr wg) =
  @data_at Noise.CS sh (tarray tuchar 32) (bytes pub) (field_address t_dev (DOT C._static_identity DOT C._static_public) wg) *
  @field_at Cookie.CS sh t_dev (DOT C._static_identity DOT C._has_identity) has wg *
  @field_at Noise.CS sh t_sid (DOT I._static_private) (bytes priv) (id_addr wg) *
  @field_at Noise.CS sh t_sid (DOT I._lock) lk (id_addr wg) *
  spacer sh 69 72 (id_addr wg).
Proof.
  intros FC.
  unfold_data_at (data_at sh t_sid _ (id_addr wg)).
  assert (FCc := prot4_ck_small_dk_fc wg FC).
  assert (FC0: @field_compatible Noise.CS t_dev (DOT I._static_identity) wg) by auto with field_compatible.
  assert (FCs: @field_compatible Noise.CS t_sid [] (id_addr wg))
    by exact (@field_compatible_nested_field Noise.CS t_dev (DOT I._static_identity) wg FC0).
  rewrite (@field_at_data_at Noise.CS sh t_sid (DOT I._static_public)).
  rewrite (@field_at_data_at Noise.CS sh t_sid (DOT I._has_identity)).
  rewrite (@field_at_data_at Cookie.CS sh t_dev (DOT C._static_identity DOT C._has_identity)).
  rewrite !(@field_address_offset Noise.CS) by auto with field_compatible.
  rewrite !(@field_address_offset Cookie.CS) by auto with field_compatible.
  simpl. unfold id_addr, OFS_DEV_IDENTITY. rewrite !offset_offset_val. simpl.
  rewrite (@data_at_cs_eq Cookie.CS Noise.CS _ sh tbool has has) by (apply JMeq_refl || reflexivity).
  apply pred_ext; cancel.
Qed.

Definition prot4_ck_small_dk_ccrest (sh: share) (sec: list val) (birth lk: val) (c: val) : mpred :=
  @field_at Noise.CS sh t_cc (DOT I._secret) sec c *
  @field_at Noise.CS sh t_cc (DOT I._secret_birthdate) birth c *
  @field_at Noise.CS sh t_cc (DOT I._secret_lock) lk c * spacer sh 108 112 c.

Lemma prot4_ck_small_dk_cc_split sh c (sec ek mk: list val) (birth lk dev: val) :
  @field_compatible Noise.CS t_cc [] c ->
  @data_at Noise.CS sh t_cc (sec, (ek, (mk, (birth, (lk, dev))))) c =
  @field_at Cookie.CS sh t_cc (DOT C._device) dev c *
  @data_at Noise.CS sh (tarray tuchar 32) ek (@field_address Cookie.CS t_cc (DOT C._cookie_encryption_key) c) *
  @data_at Noise.CS sh (tarray tuchar 32) mk (@field_address Cookie.CS t_cc (DOT C._message_mac1_key) c) *
  prot4_ck_small_dk_ccrest sh sec birth lk c.
Proof.
  intros FC.
  assert (FCc: @field_compatible Cookie.CS t_cc [] c)
    by (apply (@field_compatible_change_composite Noise.CS Cookie.CS _ t_cc); [prove_cs_preserve_type | auto]).
  unfold_data_at (@data_at Noise.CS sh t_cc _ c).
  rewrite (@field_at_data_at Noise.CS sh t_cc (DOT I._cookie_encryption_key)).
  rewrite (@field_at_data_at Noise.CS sh t_cc (DOT I._message_mac1_key)).
  rewrite !(@field_address_offset Noise.CS) by auto with field_compatible.
  rewrite !(@field_address_offset Cookie.CS) by auto with field_compatible.
  simpl.
  rewrite (@field_at_cs_eq Cookie.CS Noise.CS _ sh t_cc (DOT C._device) dev dev) by (apply JMeq_refl || prove_cs_preserve_type).
  unfold prot4_ck_small_dk_ccrest.
  apply pred_ext; cancel.
Qed.

Lemma prot4_ck_small_dk_bytes32 sh bs p :
  Zlength bs = 32 -> bytes_at sh bs p = @data_at Noise.CS sh (tarray tuchar 32) (bytes bs) p.
Proof. intros L. unfold bytes_at. rewrite L. reflexivity. Qed.

Lemma prot4_ck_small_dk_bytes8 sh bs p :
  Zlength bs = 8 -> bytes_at sh bs p = @data_at Noise.CS sh (tarray tuchar 8) (bytes bs) p.
Proof. intros L. unfold bytes_at. rewrite L. reflexivity. Qed.

Lemma prot4_ck_small_dk_label_key_len label pub : Zlength (label_key label pub) = 32.
Proof.
  unfold label_key, blake2s, b2s_digest_stream, b2s_out.
  rewrite Zlength_map, Zlength_correct, upto_length. reflexivity.
Qed.

Lemma prot4_ck_small_body_device_keys :
  @semax_body (QPvarspecs Cookie.qp) prot4_ck_small_G Cookie.CS
      WgNoise.cookie.code.f_wg_cookie_checker_precompute_device_keys wg_cookie_checker_precompute_device_keys_spec.
Proof.
start_function.
unfold device_rep, identity_rep, checker_rep. Intros lk1 lk2.
rewrite (prot4_ck_small_dk_id_split sh wg _ _ lk1 _ H0).
assert_PROP (@field_compatible Noise.CS t_cc [] (cc_addr wg)) as FCc by entailer!.
rewrite (prot4_ck_small_dk_cc_split sh (cc_addr wg) _ _ _ _ _ _ FCc).
assert (FCcc: @field_compatible Cookie.CS t_cc [] (cc_addr wg))
  by (apply (@field_compatible_change_composite Noise.CS Cookie.CS _ t_cc); [prove_cs_preserve_type|auto]).
assert (FCd := prot4_ck_small_dk_fc wg H0).
assert (F1: field_compatible t_cc (DOT C._cookie_encryption_key) (cc_addr wg)) by auto with field_compatible.
assert (F2: field_compatible t_cc (DOT C._message_mac1_key) (cc_addr wg)) by auto with field_compatible.
assert (F3: field_compatible t_dev (DOT C._static_identity DOT C._static_public) wg) by auto with field_compatible.
unfold wg_consts, cookie_globals. Intros.
assert (Lck: Zlength cookie_label = 8) by reflexivity.
assert (Lm1: Zlength mac1_label = 8) by reflexivity.
destruct H2 as [Lpub Lpriv].
rewrite <- (prot4_ck_small_dk_bytes8 Ers cookie_label) by exact Lck.
rewrite <- (prot4_ck_small_dk_bytes8 Ers mac1_label) by exact Lm1.
rewrite <- (prot4_ck_small_dk_bytes32 sh (id_pub (d_id D))) by exact Lpub.
forward. rewrite H.
forward.
{ entailer!. destruct (id_has (d_id D)); simpl; auto. }
forward_if.
- destruct (id_has (d_id D)) eqn:Eh; [| unfold typed_true in H2; simpl in H2; discriminate].
  forward.
  sep_apply (@data_at_data_at_ Noise.CS sh (tarray tuchar 32) (bytes (cc_ekey (d_cc D)))).
  forward_call (gv, sh, field_address t_cc (DOT C._cookie_encryption_key) (cc_addr wg), sh,
                field_address t_dev (DOT C._static_identity DOT C._static_public) wg, id_pub (d_id D), Ers,
                gv _cookie_key_label, cookie_label).
  forward.
  sep_apply (@data_at_data_at_ Noise.CS sh (tarray tuchar 32) (bytes (cc_mkey (d_cc D)))).
  forward_call (gv, sh, field_address t_cc (DOT C._message_mac1_key) (cc_addr wg), sh,
                field_address t_dev (DOT C._static_identity DOT C._static_public) wg, id_pub (d_id D), Ers,
                gv _mac1_key_label, mac1_label).
  unfold device_rep, identity_rep, checker_rep, wg_consts, cookie_globals, checker_keys.
  rewrite Eh. simpl d_id. simpl d_cc. simpl d_dev. simpl d_ptab. simpl d_itab.
  assert (LK1 := prot4_ck_small_dk_label_key_len cookie_label (id_pub (d_id D))).
  assert (LK2 := prot4_ck_small_dk_label_key_len mac1_label (id_pub (d_id D))).
  revert LK1 LK2. generalize (label_key cookie_label (id_pub (d_id D))) (label_key mac1_label (id_pub (d_id D))).
  intros K1 K2 LK1 LK2.
  rewrite (prot4_ck_small_dk_bytes32 sh K1) by exact LK1.
  rewrite (prot4_ck_small_dk_bytes32 sh K2) by exact LK2.
  rewrite (prot4_ck_small_dk_bytes32 sh (id_pub (d_id D))) by exact Lpub.
  rewrite (prot4_ck_small_dk_bytes8 Ers cookie_label) by exact Lck.
  rewrite (prot4_ck_small_dk_bytes8 Ers mac1_label) by exact Lm1.
  entailer!.
  + unfold cc_ok, id_ok; simpl. destruct H1 as (? & ? & ?). auto.
  + Exists lk2. rewrite exp_sepcon1. Exists lk1.
    rewrite Eh. cbn [checker_set_keys cc_secret cc_ekey cc_mkey cc_birth cc_dev fst snd].
    rewrite (prot4_ck_small_dk_id_split sh _ _ _ lk1 _ H0).
    rewrite (prot4_ck_small_dk_cc_split sh _ _ _ _ _ _ _ FCc).
    cancel.
- destruct (id_has (d_id D)) eqn:Eh; [unfold typed_false in H2; simpl in H2; discriminate |].
  sep_apply (@data_at_data_at_ Noise.CS sh (tarray tuchar 32) (bytes (cc_ekey (d_cc D)))).
  sep_apply (@data_at_data_at_ Noise.CS sh (tarray tuchar 32) (bytes (cc_mkey (d_cc D)))).
  rewrite !(@data_at__cs_eq Noise.CS Cookie.CS _ sh (tarray tuchar 32)) by reflexivity.
  forward_call (sh, field_address t_cc (DOT C._cookie_encryption_key) (cc_addr wg), 0, 32).
  forward_call (sh, field_address t_cc (DOT C._message_mac1_key) (cc_addr wg), 0, 32).
  unfold device_rep, identity_rep, checker_rep, wg_consts, cookie_globals, checker_keys.
  rewrite Eh. simpl d_id. simpl d_cc. simpl d_dev. simpl d_ptab. simpl d_itab.
  rewrite (prot4_ck_small_dk_bytes32 sh (id_pub (d_id D))) by exact Lpub.
  rewrite (prot4_ck_small_dk_bytes8 Ers cookie_label) by exact Lck.
  rewrite (prot4_ck_small_dk_bytes8 Ers mac1_label) by exact Lm1.
  rewrite !(@data_at_cs_eq Cookie.CS Noise.CS _ sh (tarray tuchar 32) (Zrepeat (Vubyte (Byte.repr 0)) 32) (bytes zeros32))
    by (apply JMeq_refl || reflexivity).
  entailer!.
  + unfold cc_ok, id_ok; simpl. destruct H1 as (? & ? & ?). auto.
  + Exists lk2. rewrite exp_sepcon1. Exists lk1.
    rewrite Eh. cbn [checker_set_keys cc_secret cc_ekey cc_mkey cc_birth cc_dev fst snd].
    rewrite (prot4_ck_small_dk_id_split sh _ _ _ lk1 _ H0).
    rewrite (prot4_ck_small_dk_cc_split sh _ _ _ _ _ _ _ FCc).
    cancel.
Qed.

Section PeerKeysNoise.
#[local] Existing Instance Noise.CS.

Lemma prot4_ck_small_pk_fd sh c v :
  field_compatible t_cookie [] c ->
  field_at sh t_cookie (DOT C._cookie_decryption_key) v c = data_at sh (tarray tuchar 32) v (offset_val 42 c).
Proof. intros. rewrite field_at_data_at, field_address_offset by auto with field_compatible. reflexivity. Qed.

Lemma prot4_ck_small_pk_fm sh c v :
  field_compatible t_cookie [] c ->
  field_at sh t_cookie (DOT C._message_mac1_key) v c = data_at sh (tarray tuchar 32) v (offset_val 74 c).
Proof. intros. rewrite field_at_data_at, field_address_offset by auto with field_compatible. reflexivity. Qed.

(* the two key fields of struct cookie at c (offsets 42, 74), with the rest of the cookie as a wand *)
Lemma prot4_ck_small_pk_cookie sh c Ck dk mk :
  Zlength dk = 32 -> Zlength mk = 32 ->
  cookie_rep sh c Ck |--
  @data_at_ Noise.CS sh (tarray tuchar 32) (offset_val 42 c) *
  @data_at_ Noise.CS sh (tarray tuchar 32) (offset_val 74 c) *
  (bytes_at sh dk (offset_val 42 c) * bytes_at sh mk (offset_val 74 c) -*
   cookie_rep sh c (mkCookie (ck_birth Ck) (ck_valid Ck) (ck_cookie Ck) (ck_sent Ck) (ck_last_mac1 Ck) dk mk)).
Proof.
  intros Ld Lm. unfold cookie_rep at 1. Intros lk.
  assert_PROP (field_compatible t_cookie [] c) as FC by entailer!.
  unfold cookie_val. unfold_data_at (data_at _ _ _ c).
  rewrite (prot4_ck_small_pk_fd sh c _ FC), (prot4_ck_small_pk_fm sh c _ FC).
  sep_apply (data_at_data_at_ sh (tarray tuchar 32) (bytes (ck_dkey Ck)) (offset_val 42 c)).
  sep_apply (data_at_data_at_ sh (tarray tuchar 32) (bytes (ck_mkey Ck)) (offset_val 74 c)).
  cancel.
  apply -> wand_sepcon_adjoint.
  unfold cookie_rep. Exists lk. unfold cookie_val. simpl.
  unfold_data_at (data_at _ _ _ c).
  rewrite (prot4_ck_small_pk_fd sh c _ FC), (prot4_ck_small_pk_fm sh c _ FC).
  unfold bytes_at. rewrite Ld, Lm.
  destruct H as (L1 & L2 & L3 & L4).
  entailer!.
  unfold cookie_ok; simpl; auto.
Qed.

(* the remote static key of struct noise_handshake at h (offset 88), with the rest as a wand *)
Lemma prot4_ck_small_pk_hs sh h H :
  hs_rep sh h H |--
  bytes_at sh (hs_rstatic H) (offset_val 88 h) * (bytes_at sh (hs_rstatic H) (offset_val 88 h) -* hs_rep sh h H).
Proof.
  unfold hs_rep at 1. Intros.
  assert_PROP (field_compatible t_hs (DOT I._remote_static) h) as FC by entailer!.
  assert (E: field_at sh t_hs (DOT I._remote_static) (bytes (hs_rstatic H)) h =
             bytes_at sh (hs_rstatic H) (offset_val 88 h)).
  { rewrite field_at_data_at, field_address_offset by auto. unfold bytes_at.
    destruct H0 as (_ & L & _). rewrite L. reflexivity. }
  rewrite E. cancel.
  apply -> wand_sepcon_adjoint.
  unfold hs_rep. rewrite E. entailer!.
Qed.

Lemma prot4_ck_small_pk_labels gv :
  cookie_globals gv =
  bytes_at Ers mac1_label (gv _mac1_key_label) * bytes_at Ers cookie_label (gv _cookie_key_label).
Proof. reflexivity. Qed.

End PeerKeysNoise.

Lemma prot4_ck_small_pk_lk_len label pub : Zlength (label_key label pub) = 32.
Proof.
  unfold label_key, blake2s, b2s_digest_stream, b2s_out.
  rewrite Zlength_map, Zlength_correct, upto_length. reflexivity.
Qed.

Lemma prot4_ck_small_body_peer_keys :
  @semax_body (QPvarspecs Cookie.qp) prot4_ck_small_G Cookie.CS
      WgNoise.cookie.code.f_wg_cookie_checker_precompute_peer_keys wg_cookie_checker_precompute_peer_keys_spec.
Proof.
  start_function.
  assert_PROP (hs_ok H) as HOK by (unfold hs_rep; entailer!).
  sep_apply (prot4_ck_small_pk_hs sh (hs_addr p) H).
  sep_apply (prot4_ck_small_pk_cookie sh (cookie_addr p) Ck
               (label_key cookie_label (hs_rstatic H)) (label_key mac1_label (hs_rstatic H))
               (prot4_ck_small_pk_lk_len _ _) (prot4_ck_small_pk_lk_len _ _)).
  unfold wg_consts. rewrite prot4_ck_small_pk_labels.
  unfold hs_addr, cookie_addr, OFS_PEER_HANDSHAKE, OFS_PEER_COOKIE. rewrite !offset_offset_val. simpl (48 + 88). simpl (360 + 42). simpl (360 + 74).
  destruct HOK as (_ & Lr & _).
  repeat flatten_sepcon_in_SEP.
  forward_call (gv, sh, offset_val 402 p, sh, offset_val 136 p, hs_rstatic H, Ers, gv _cookie_key_label, cookie_label).
  { split; apply H0. }
  forward_call (gv, sh, offset_val 434 p, sh, offset_val 136 p, hs_rstatic H, Ers, gv _mac1_key_label, mac1_label).
  { split; apply H0. }
  sep_apply (modus_ponens_wand (bytes_at sh (hs_rstatic H) (offset_val 136 p)) (hs_rep sh (offset_val 48 p) H)).
  sep_apply (modus_ponens_wand (bytes_at sh (label_key cookie_label (hs_rstatic H)) (offset_val 402 p) *
                                bytes_at sh (label_key mac1_label (hs_rstatic H)) (offset_val 434 p))).
  unfold hs_addr, cookie_addr, OFS_PEER_HANDSHAKE, OFS_PEER_COOKIE, cookie_set_keys, wg_consts.
  rewrite prot4_ck_small_pk_labels.
  entailer!.
Qed.

Lemma prot4_ck_small_body_mac1 :
  @semax_body (QPvarspecs Cookie.qp) prot4_ck_small_G Cookie.CS
      WgNoise.cookie.code.f_compute_mac1 compute_mac1_spec.
Proof.
start_function.
forward.
unfold wg_consts; Intros.
rewrite (prot4_ck_small_ba_b2s shk key kp) by lia.
rewrite (prot4_ck_small_out_b2s sho 16 o).
match goal with |- context [Int64.add (Int64.sub ?a ?b) ?c] =>
  replace (Int64.add (Int64.sub a b) c) with (Int64.repr (Zlength msg)) end.
2:{ change (Ptrofs.to_int64 (Ptrofs.repr (sizeof (Tstruct code._message_macs noattr)))) with (Int64.repr 32).
  rewrite sub64_repr, add64_repr. f_equal. lia. }
forward_call (shk, kp, key, shm, mp, msg, sho, o, 16, gv).
{ entailer!. rewrite H. reflexivity. }
rewrite (prot4_ck_small_b2s_ba sho 16 (blake2s key 16 msg) o)
  by (apply prot4_ck_small_blake2s_len; lia).
rewrite <- (prot4_ck_small_ba_b2s shk key kp) by lia.
unfold MAC, wg_consts.
entailer!.
Qed.

Lemma prot4_ck_small_body_mac2 :
  @semax_body (QPvarspecs Cookie.qp) prot4_ck_small_G Cookie.CS
      WgNoise.cookie.code.f_compute_mac2 compute_mac2_spec.
Proof.
start_function.
forward.
unfold wg_consts; Intros.
rewrite (prot4_ck_small_ba_b2s shk ck kp) by lia.
rewrite (prot4_ck_small_out_b2s sho 16 o).
match goal with |- context [Int64.add (Int64.sub ?a ?b) ?c] =>
  replace (Int64.add (Int64.sub a b) c) with (Int64.repr (Zlength msg)) end.
2:{ change (Ptrofs.to_int64 (Ptrofs.repr (sizeof (Tstruct code._message_macs noattr)))) with (Int64.repr 32).
  rewrite sub64_repr, add64_repr. f_equal. lia. }
forward_call (shk, kp, ck, shm, mp, msg, sho, o, 16, gv).
{ entailer!. rewrite H. reflexivity. }
rewrite (prot4_ck_small_b2s_ba sho 16 (blake2s ck 16 msg) o)
  by (apply prot4_ck_small_blake2s_len; lia).
rewrite <- (prot4_ck_small_ba_b2s shk ck kp) by lia.
unfold MAC, wg_consts.
entailer!.
Qed.

End CookieSmall.

Theorem prot4_ck_bodies_small :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body (QPvarspecs Cookie.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Cookie.CS) Cookie.CS
      WgNoise.cookie.code.f_quickproof_swab16 quickproof_swab16_spec) /\
  (@semax_body (QPvarspecs Cookie.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Cookie.CS) Cookie.CS
      WgNoise.cookie.code.f_wg_cookie_checker_init wg_cookie_checker_init_spec) /\
  (@semax_body (QPvarspecs Cookie.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Cookie.CS) Cookie.CS
      WgNoise.cookie.code.f_precompute_key precompute_key_spec) /\
  (@semax_body (QPvarspecs Cookie.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Cookie.CS) Cookie.CS
      WgNoise.cookie.code.f_wg_cookie_checker_precompute_device_keys wg_cookie_checker_precompute_device_keys_spec) /\
  (@semax_body (QPvarspecs Cookie.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Cookie.CS) Cookie.CS
      WgNoise.cookie.code.f_wg_cookie_checker_precompute_peer_keys wg_cookie_checker_precompute_peer_keys_spec) /\
  (@semax_body (QPvarspecs Cookie.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Cookie.CS) Cookie.CS
      WgNoise.cookie.code.f_compute_mac1 compute_mac1_spec) /\
  (@semax_body (QPvarspecs Cookie.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Cookie.CS) Cookie.CS
      WgNoise.cookie.code.f_compute_mac2 compute_mac2_spec).
Proof.
  intros.
  repeat match goal with |- _ /\ _ => split end.
  - apply prot4_ck_small_body_swab16.
  - apply prot4_ck_small_body_checker_init.
  - apply prot4_ck_small_body_precompute_key.
  - apply prot4_ck_small_body_device_keys.
  - apply prot4_ck_small_body_peer_keys.
  - apply prot4_ck_small_body_mac1.
  - apply prot4_ck_small_body_mac2.
Qed.
