(* hc_pieces3, group cinit: common.h bodies, proved once at a small compspecs with the callee context
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
Lemma hc3b_cinit_field_compatible_cs {cs1 cs2: compspecs}: forall n p,
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

Lemma hc3b_cinit_data_at_cs {cs1 cs2: compspecs}: forall sh n (v: list val) p,
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  intros. unfold data_at, field_at.
  f_equal. f_equal. apply prop_ext. apply hc3b_cinit_field_compatible_cs.
Qed.

Lemma hc3b_cinit_data_at__cs {cs1 cs2: compspecs}: forall sh n p,
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof.
  intros. unfold data_at_, field_at_. apply hc3b_cinit_data_at_cs.
Qed.

Lemma hc3b_cinit_HASH_len m : Zlength (HASH m) = 32.
Proof.
  unfold HASH, blake2s, WgNoise.proof.blake2s.model.b2s_digest_stream, WgNoise.proof.blake2s.model.b2s_out.
  rewrite Zlength_map. reflexivity.
Qed.

Lemma hc3b_cinit_mh_len h d : Zlength (mix_hash h d) = 32.
Proof. unfold mix_hash. apply hc3b_cinit_HASH_len. Qed.

Lemma hc3b_cinit_hmac_len key m : Zlength (hmac key m) = 32.
Proof. unfold hmac. apply hc3b_cinit_HASH_len. Qed.

Lemma hc3b_cinit_kdf_len ck d : Zlength (kdf1 ck d) = 32 /\ Zlength (kdf2 ck d) = 32 /\ Zlength (kdf3 ck d) = 32.
Proof. unfold kdf1, kdf2, kdf3. rewrite !hc3b_cinit_hmac_len. auto. Qed.

Lemma hc3b_cinit_hin_ne sh bs p : Zlength bs <> 0 -> hin sh bs p = hbytes sh bs p.
Proof. intros. unfold hin. destruct (Z.eq_dec (Zlength bs) 0); [contradiction | reflexivity]. Qed.

Lemma hc3b_cinit_is_zero a : Zlength a = 32 -> is_zero a = negb (memneq_bool a zeros32).
Proof.
  intros H. unfold is_zero, bytes_eqb, memneq_bool, zeros, zeros32. rewrite H.
  destruct (list_eq_dec Byte.eq_dec a (Zrepeat Byte.zero 32)); reflexivity.
Qed.

Lemma hc3b_cinit_out_hcs sh p : @data_at_ CSkci sh (tarray tuchar 32) p = hout sh 32 p.
Proof. unfold hout. apply hc3b_cinit_data_at__cs. Qed.

Lemma hc3b_cinit_hbytes_out sh bs p : Zlength bs = 32 -> hbytes sh bs p |-- hout sh 32 p.
Proof. intros L. unfold hbytes, hout. rewrite L. apply data_at_data_at_. Qed.

Lemma hc3b_cinit_fc_root {cs: compspecs} t gf gfs p :
  field_compatible t (gf :: gfs) p -> field_compatible t [] p.
Proof. intros (?&?&?&?&?). repeat split; auto. Qed.

(* the bodies' compspecs *)
#[local] Existing Instance CSkci.
#[local] Instance hc3b_cinit_HCS_CSkci : change_composite_env HCS CSkci.
Proof. make_cs_preserve HCS CSkci. Defined.

Lemma hc3b_cinit_mcinit_eq sh (ck h key spub ts: list val) p :
  @data_at HCS sh t_mcinit ((ck, h), (key, (spub, ts))) p =
  (@data_at HCS sh t_mstate (ck, h) (@field_address CSkci t_mcinit (DOT FH._st) p) *
   @data_at HCS sh (tarray tuchar 32) key (@field_address CSkci t_mcinit (DOT FH._key) p) *
   @data_at HCS sh (tarray tuchar 32) spub (@field_address CSkci t_mcinit (DOT FH._spub) p) *
   @data_at HCS sh (tarray tuchar 12) ts (@field_address CSkci t_mcinit (DOT FH._ts) p))%logic.
Proof.
  erewrite (@data_at_change_composite HCS CSkci _ sh t_mcinit); [| apply JMeq_refl | prove_cs_preserve_type].
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mcinit (DOT FH._st)), (field_at_data_at sh t_mcinit (DOT FH._key)),
    (field_at_data_at sh t_mcinit (DOT FH._spub)), (field_at_data_at sh t_mcinit (DOT FH._ts)).
  erewrite <- (@data_at_change_composite HCS CSkci _ sh t_mstate); [| apply JMeq_refl | prove_cs_preserve_type].
  change (nested_field_type t_mcinit (DOT FH._key)) with (tarray tuchar 32).
  change (nested_field_type t_mcinit (DOT FH._spub)) with (tarray tuchar 32).
  change (nested_field_type t_mcinit (DOT FH._ts)) with (tarray tuchar 12).
  rewrite <- !(@hc3b_cinit_data_at_cs HCS CSkci).
  rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma hc3b_cinit_mcinit_fc sh v p : @data_at HCS sh t_mcinit v p |-- !! @field_compatible CSkci t_mcinit [] p.
Proof.
  erewrite (@data_at_change_composite HCS CSkci _ sh t_mcinit); [| apply JMeq_refl | prove_cs_preserve_type].
  entailer!.
Qed.

Lemma hc3b_cinit_mident_eq sh I p :
  Zlength (mi_priv I) = 32 -> Zlength (mi_pub I) = 32 ->
  @data_at HCS sh t_mident (mident_val I) p =
  (hbytes sh (mi_priv I) (@field_address CSkci t_mident (DOT FH._priv) p) *
   hbytes sh (mi_pub I) (@field_address CSkci t_mident (DOT FH._pub) p) *
   @field_at CSkci sh t_mident (DOT FH._ok) (Vint (if mi_ok I then Int.one else Int.zero)) p)%logic.
Proof.
  intros H1 H2.
  erewrite (@data_at_change_composite HCS CSkci _ sh t_mident); [| apply JMeq_refl | prove_cs_preserve_type].
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mident (DOT FH._priv)), (field_at_data_at sh t_mident (DOT FH._pub)).
  unfold hbytes. rewrite H1, H2.
  rewrite <- !(@hc3b_cinit_data_at_cs CSkci HCS).
  rewrite sepcon_assoc. reflexivity.
Qed.

Lemma hc3b_cinit_mident_fc sh v p : @data_at HCS sh t_mident v p |-- !! @field_compatible CSkci t_mident [] p.
Proof.
  erewrite (@data_at_change_composite HCS CSkci _ sh t_mident); [| apply JMeq_refl | prove_cs_preserve_type].
  entailer!.
Qed.

Lemma hc3b_cinit_prim_out sh (v: list val) p : Zlength v <> 0 ->
  @data_at HCS sh (tarray tuchar (Zlength v)) v p = @prim_out HCS sh v p.
Proof. intros. unfold prim_out. destruct (Z.eq_dec (Zlength v) 0); [contradiction | reflexivity]. Qed.

Lemma hc3b_cinit_hout_eq sh p : @data_at HCS sh (tarray tuchar 32) (Zrepeat Vundef 32) p = hout sh 32 p.
Proof. reflexivity. Qed.

Lemma hc3b_cinit_out sh (ck h key spub ts: list val) p :
  @data_at HCS sh t_mstate (ck, h) (@field_address CSkci t_mcinit (DOT FH._st) p) *
  @data_at HCS sh (tarray tuchar 32) key (@field_address CSkci t_mcinit (DOT FH._key) p) *
  @data_at HCS sh (tarray tuchar 32) spub (@field_address CSkci t_mcinit (DOT FH._spub) p) *
  @data_at HCS sh (tarray tuchar 12) ts (@field_address CSkci t_mcinit (DOT FH._ts) p)
  |-- @data_at_ HCS sh t_mcinit p.
Proof.
  rewrite <- hc3b_cinit_mcinit_eq. apply data_at_data_at_.
Qed.

Lemma hc3b_cinit_mident_eq_k sh I p :
  Zlength (mi_priv I) = 32 -> Zlength (mi_pub I) = 32 ->
  @data_at CSkci sh t_mident (mident_val I) p =
  (hbytes sh (mi_priv I) (@field_address CSkci t_mident (DOT FH._priv) p) *
   hbytes sh (mi_pub I) (@field_address CSkci t_mident (DOT FH._pub) p) *
   @field_at CSkci sh t_mident (DOT FH._ok) (Vint (if mi_ok I then Int.one else Int.zero)) p)%logic.
Proof.
  intros H1 H2. rewrite <- hc3b_cinit_mident_eq by assumption.
  symmetry. erewrite (@data_at_change_composite HCS CSkci _ sh t_mident); [reflexivity | apply JMeq_refl | prove_cs_preserve_type].
Qed.

Lemma hc3b_cinit_out_k sh (ck h key spub ts: list val) p :
  @data_at HCS sh t_mstate (ck, h) (@field_address CSkci t_mcinit (DOT FH._st) p) *
  @data_at HCS sh (tarray tuchar 32) key (@field_address CSkci t_mcinit (DOT FH._key) p) *
  @data_at HCS sh (tarray tuchar 32) spub (@field_address CSkci t_mcinit (DOT FH._spub) p) *
  @data_at HCS sh (tarray tuchar 12) ts (@field_address CSkci t_mcinit (DOT FH._ts) p)
  |-- @data_at_ CSkci sh t_mcinit p.
Proof.
  sep_apply hc3b_cinit_out.
  erewrite (@data_at__change_composite HCS CSkci _ sh t_mcinit) by prove_cs_preserve_type.
  apply derives_refl.
Qed.

Lemma hc3b_cinit_mcinit_k sh (ck h key spub ts: list val) p :
  @data_at CSkci sh t_mcinit ((ck, h), (key, (spub, ts))) p =
  @data_at HCS sh t_mcinit ((ck, h), (key, (spub, ts))) p.
Proof.
  symmetry. erewrite (@data_at_change_composite HCS CSkci _ sh t_mcinit); [reflexivity | apply JMeq_refl | prove_cs_preserve_type].
Qed.

Ltac hc3b_cinit_contra :=
  exfalso; first [ apply Int.one_not_zero; assumption
                 | match goal with Hx: _ <> _ |- _ => apply Hx; reflexivity end
                 | match goal with Hx: ?a = ?a -> False |- _ => apply Hx; reflexivity end ].

Ltac hc3b_cinit_fa :=
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

Section CI.
Variables cons iden: ident.
Lemma hc3_body_m_consume_initiation_1 :
  @semax_body [] (hc3_G_m_consume_initiation_1 x25519 aead_dec cons iden) CSkci FH.f_m_consume_initiation_1 (m_consume_initiation_1_spec x25519 aead_dec cons iden).
Proof.
start_function.
assert_PROP (field_compatible t_mcinit [] o) as FC.
{ sep_apply (hc3b_cinit_mcinit_fc sho ((Zrepeat Vundef 32, Zrepeat Vundef 32), (Zrepeat Vundef 32, (Zrepeat Vundef 32, tsv))) o). entailer!. }
assert_PROP (field_compatible t_mident [] ri) as FCi.
{ sep_apply (hc3b_cinit_mident_fc shi (mident_val I) ri). entailer!. }
assert (field_compatible t_mcinit (DOT FH._key) o) as FCk by auto with field_compatible.
assert (field_compatible t_mcinit (DOT FH._spub) o) as FCp by auto with field_compatible.
assert (field_compatible t_mcinit (DOT FH._st) o) as FCs by auto with field_compatible.
assert (field_compatible t_mident (DOT FH._priv) ri) as FCip by auto with field_compatible.
assert (field_compatible t_mident (DOT FH._pub) ri) as FCiq by auto with field_compatible.
rewrite hc3b_cinit_mcinit_eq. flatten_sepcon_in_SEP.
rewrite (hc3b_cinit_mident_eq shi I ri) by assumption. repeat flatten_sepcon_in_SEP.
change (@data_at HCS sho t_mstate (Zrepeat Vundef 32, Zrepeat Vundef 32) (field_address t_mcinit (DOT FH._st) o))
  with (@data_at_ HCS sho t_mstate (field_address t_mcinit (DOT FH._st) o)).
forward_call (gv, sho, field_address t_mcinit (DOT FH._st) o, shi, field_address t_mident (DOT FH._pub) ri, mi_pub I).
{ entailer!. simpl. hc3b_cinit_fa. }
assert (Lck: Zlength init_ck = 32) by (unfold init_ck; apply hc3b_cinit_HASH_len).
assert (Lh1: Zlength (mix_hash init_hash (mi_pub I)) = 32) by apply hc3b_cinit_mh_len.
assert (Lh2: Zlength (mix_hash (mix_hash init_hash (mi_pub I)) EPH) = 32) by apply hc3b_cinit_mh_len.
destruct (hc3b_cinit_kdf_len init_ck EPH) as [Lk1 _].
rewrite <- (hc3b_cinit_hin_ne sh EPH) by lia.
forward_call (gv, sho, field_address t_mcinit (DOT FH._st) o, init_ck, mix_hash init_hash (mi_pub I), sh, pe, EPH).
{ entailer!. simpl. rewrite H1. hc3b_cinit_fa. }
forward_call (gv, sho, field_address t_mcinit (DOT FH._st) o, init_ck, mix_hash (mix_hash init_hash (mi_pub I)) EPH, sh, pe, EPH).
{ entailer!. simpl. rewrite H1. hc3b_cinit_fa. }
rewrite (hc3b_cinit_hin_ne sh EPH) by lia.
rewrite hc3b_cinit_out_hcs.
forward_call (Tsh, v_dh, shi, field_address t_mident (DOT FH._priv) ri, mi_priv I, sh, pe, EPH).
{ entailer!. simpl. hc3b_cinit_fa. }
assert (LDH: Zlength (x25519 (mi_priv I) EPH) = 32) by apply X25519.
destruct (dh_ok x25519 (mi_priv I) EPH) eqn:HDH.
2:{
  forward_if.
  2:{ hc3b_cinit_contra. }
  sep_apply (hc3b_cinit_hbytes_out Tsh (x25519 (mi_priv I) EPH) v_dh LDH).
  rewrite <- hc3b_cinit_out_hcs.
  forward.
  unfold m_consume_init1_model, consume_init_stage1. cbn [id_priv id_pub im_eph im_encs]. rewrite HDH. cbn [negb].
  rewrite (hc3b_cinit_mident_eq_k shi I ri) by assumption.
  unfold mstate_val.
  sep_apply (hc3b_cinit_out_k sho (bytes (kdf1 init_ck EPH)) (bytes (mix_hash (mix_hash init_hash (mi_pub I)) EPH))
    (Zrepeat Vundef 32) (Zrepeat Vundef 32) tsv o).
  entailer!. }
forward_if.
{ hc3b_cinit_contra. }
destruct (hc3b_cinit_kdf_len (kdf1 init_ck EPH) (x25519 (mi_priv I) EPH)) as [Lc2 [Lk2 _]].
rewrite hc3b_cinit_hout_eq.
rewrite <- (hc3b_cinit_hin_ne Tsh (x25519 (mi_priv I) EPH)) by lia.
forward_call (gv, sho, field_address t_mcinit (DOT FH._st) o, kdf1 init_ck EPH, mix_hash (mix_hash init_hash (mi_pub I)) EPH,
              sho, field_address t_mcinit (DOT FH._key) o, Tsh, v_dh, x25519 (mi_priv I) EPH).
{ entailer!. simpl. rewrite LDH. hc3b_cinit_fa. }
replace (@data_at HCS sho (tarray tuchar 32) (Zrepeat Vundef 32) (field_address t_mcinit (DOT FH._spub) o))
  with (@prim_out HCS sho (Zrepeat Vundef 32) (field_address t_mcinit (DOT FH._spub) o))
  by (rewrite <- hc3b_cinit_prim_out by (rewrite Zlength_Zrepeat; lia); rewrite Zlength_Zrepeat by lia; reflexivity).
rewrite <- (hc3b_cinit_hin_ne sh ENCS) by lia.
forward_call (gv, sho, field_address t_mcinit (DOT FH._st) o, kdf1 (kdf1 init_ck EPH) (x25519 (mi_priv I) EPH),
              mix_hash (mix_hash init_hash (mi_pub I)) EPH, sho, field_address t_mcinit (DOT FH._spub) o, Zrepeat Vundef 32,
              sh, pc, ENCS, sho, field_address t_mcinit (DOT FH._key) o, kdf2 (kdf1 init_ck EPH) (x25519 (mi_priv I) EPH)).
{ entailer!. simpl. rewrite H2. hc3b_cinit_fa. }
{ rewrite Zlength_Zrepeat by lia. lia. }
rewrite (hc3b_cinit_hin_ne sh ENCS) by lia.
rewrite (hc3b_cinit_hin_ne Tsh (x25519 (mi_priv I) EPH)) by lia.
sep_apply (hc3b_cinit_hbytes_out Tsh (x25519 (mi_priv I) EPH) v_dh LDH).
rewrite <- hc3b_cinit_out_hcs.
destruct (aead_dec (kdf2 (kdf1 init_ck EPH) (x25519 (mi_priv I) EPH)) 0 (mix_hash (mix_hash init_hash (mi_pub I)) EPH) ENCS) as [sp|] eqn:HD.
- pose proof (aead_dec_length _ _ AEAD _ _ _ _ _ HD) as LS. rewrite H2 in LS.
  assert (LBs: Zlength (bytes sp) = 32) by (unfold bytes; rewrite Zlength_map; lia).
  forward.
  unfold m_consume_init1_model, consume_init_stage1. cbn [id_priv id_pub im_eph im_encs]. rewrite HDH. cbn [negb].
  rewrite HD.
  unfold mcinit_val. rewrite hc3b_cinit_mcinit_eq.
  rewrite <- (hc3b_cinit_prim_out sho (bytes sp)) by lia. rewrite LBs.
  rewrite (hc3b_cinit_mident_eq_k shi I ri) by assumption.
  replace (hbytes sho (kdf2 (kdf1 init_ck EPH) (x25519 (mi_priv I) EPH)) (field_address t_mcinit (DOT FH._key) o))
    with (@data_at HCS sho (tarray tuchar 32) (bytes (kdf2 (kdf1 init_ck EPH) (x25519 (mi_priv I) EPH))) (field_address t_mcinit (DOT FH._key) o))
    by (unfold hbytes; rewrite Lk2; reflexivity).
  unfold mstate_val.
  entailer!.
- forward.
  unfold m_consume_init1_model, consume_init_stage1. cbn [id_priv id_pub im_eph im_encs]. rewrite HDH. cbn [negb].
  rewrite HD.
  rewrite <- (hc3b_cinit_prim_out sho (Zrepeat Vundef 32)) by (rewrite Zlength_Zrepeat; lia).
  rewrite Zlength_Zrepeat by lia.
  rewrite (hc3b_cinit_mident_eq_k shi I ri) by assumption.
  replace (hbytes sho (kdf2 (kdf1 init_ck EPH) (x25519 (mi_priv I) EPH)) (field_address t_mcinit (DOT FH._key) o))
    with (@data_at HCS sho (tarray tuchar 32) (bytes (kdf2 (kdf1 init_ck EPH) (x25519 (mi_priv I) EPH))) (field_address t_mcinit (DOT FH._key) o))
    by (unfold hbytes; rewrite Lk2; reflexivity).
  unfold mstate_val.
  sep_apply (hc3b_cinit_out_k sho (bytes (kdf1 (kdf1 init_ck EPH) (x25519 (mi_priv I) EPH)))
    (bytes (mix_hash (mix_hash init_hash (mi_pub I)) EPH)) (bytes (kdf2 (kdf1 init_ck EPH) (x25519 (mi_priv I) EPH))) (Zrepeat Vundef 32) tsv o).
  entailer!.
Unshelve.
all: make_cs_preserve CSkci HCS.
Qed.
End CI.

Lemma hc3_body_m_consume_initiation_2 :
  @semax_body [] (hc3_G_m_consume_initiation_2 aead_dec) CSkci FH.f_m_consume_initiation_2 (m_consume_initiation_2_spec aead_dec).
Proof.
start_function.
assert_PROP (field_compatible t_mcinit [] o) as FC. { sep_apply (hc3b_cinit_mcinit_fc sho (mcinit_val CK H keyv spubv tsv) o). entailer!. }
unfold mcinit_val. rewrite hc3b_cinit_mcinit_eq. flatten_sepcon_in_SEP.
forward_call (sh, ps, SS).
{ entailer!. simpl. rewrite H5. reflexivity. }
rewrite hc3b_cinit_is_zero by assumption.
destruct (memneq_bool SS zeros32) eqn:HZ; simpl negb.
2:{
  forward_if.
  2:{ hc3b_cinit_contra. }
  forward.
  unfold m_consume_init2_model, consume_init_stage2. rewrite HZ. simpl.
  sep_apply (hc3b_cinit_out sho (bytes CK) (bytes H) keyv spubv tsv o).
  entailer!. }
forward_if.
{ hc3b_cinit_contra. }
assert (field_compatible t_mcinit (DOT FH._key) o) as FCk by auto with field_compatible.
assert (field_compatible t_mcinit (DOT FH._ts) o) as FCt by auto with field_compatible.
assert (field_compatible t_mcinit (DOT FH._st) o) as FCs by auto with field_compatible.
sep_apply (@data_at_data_at_ HCS sho (tarray tuchar 32) keyv (field_address t_mcinit (DOT FH._key) o)).
change (@data_at_ HCS sho (tarray tuchar 32) (field_address t_mcinit (DOT FH._key) o))
  with (hout sho 32 (field_address t_mcinit (DOT FH._key) o)).
rewrite <- (hc3b_cinit_hin_ne sh SS) by lia.
forward_call (gv, sho, field_address t_mcinit (DOT FH._st) o, CK, H, sho, field_address t_mcinit (DOT FH._key) o, sh, ps, SS).
{ entailer!. simpl. rewrite H5. hc3b_cinit_fa. }
destruct (hc3b_cinit_kdf_len CK SS) as [L1 [L2 L3]].
rewrite (hc3b_cinit_hin_ne sh SS) by lia.
replace (@data_at HCS sho (tarray tuchar 12) tsv (field_address t_mcinit (DOT FH._ts) o))
  with (@prim_out HCS sho tsv (field_address t_mcinit (DOT FH._ts) o))
  by (rewrite <- hc3b_cinit_prim_out by lia; rewrite H4; reflexivity).
rewrite <- (hc3b_cinit_hin_ne sh ENCT) by lia.
forward_call (gv, sho, field_address t_mcinit (DOT FH._st) o, kdf1 CK SS, H, sho, field_address t_mcinit (DOT FH._ts) o, tsv,
              sh, pt, ENCT, sho, field_address t_mcinit (DOT FH._key) o, kdf2 CK SS).
{ entailer!. simpl. rewrite H6. hc3b_cinit_fa. }
rewrite (hc3b_cinit_hin_ne sh ENCT) by lia.
destruct (aead_dec (kdf2 CK SS) 0 H ENCT) as [t|] eqn:HD.
- pose proof (aead_dec_length _ _ AEAD _ _ _ _ _ HD) as LT. rewrite H6 in LT.
  assert (LBt: Zlength (bytes t) = 12) by (unfold bytes; rewrite Zlength_map; lia).
  forward.
  unfold m_consume_init2_model, consume_init_stage2. rewrite HZ. cbn [negb im_enct]. rewrite HD.
  unfold mcinit_val. rewrite hc3b_cinit_mcinit_eq.
  rewrite <- (hc3b_cinit_prim_out sho (bytes t)) by lia. rewrite LBt.
  unfold hbytes. rewrite L2. unfold mstate_val.
  entailer!.
- forward.
  unfold m_consume_init2_model, consume_init_stage2. rewrite HZ. cbn [negb im_enct]. rewrite HD.
  rewrite <- (hc3b_cinit_prim_out sho tsv) by lia. rewrite H4.
  replace (hbytes sho (kdf2 CK SS) (field_address t_mcinit (DOT FH._key) o))
    with (@data_at HCS sho (tarray tuchar 32) (bytes (kdf2 CK SS)) (field_address t_mcinit (DOT FH._key) o))
    by (unfold hbytes; rewrite L2; reflexivity).
  unfold mstate_val.
  sep_apply (hc3b_cinit_out sho (bytes (kdf1 CK SS)) (bytes H) (bytes (kdf2 CK SS)) spubv tsv o).
  entailer!.
Qed.

(* the group *)
Theorem hc3_bodies_cinit :
  (forall cons iden: ident, @semax_body [] (hc3_G_m_consume_initiation_1 x25519 aead_dec cons iden) CSkci FH.f_m_consume_initiation_1 (m_consume_initiation_1_spec x25519 aead_dec cons iden)) /\
  (@semax_body [] (hc3_G_m_consume_initiation_2 aead_dec) CSkci FH.f_m_consume_initiation_2 (m_consume_initiation_2_spec aead_dec)).
Proof.
exact (conj hc3_body_m_consume_initiation_1 hc3_body_m_consume_initiation_2).
Qed.

End Bodies.
