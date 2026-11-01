(* hc_pieces3, group init: common.h bodies, proved once at a small compspecs with the callee context
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
Lemma hc3b_init_field_compatible_cs {cs1 cs2: compspecs}: forall n p,
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

Lemma hc3b_init_data_at_cs {cs1 cs2: compspecs}: forall sh n (v: list val) p,
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  intros. unfold data_at, field_at.
  f_equal. f_equal. apply prop_ext. apply hc3b_init_field_compatible_cs.
Qed.

Lemma hc3b_init_data_at__cs {cs1 cs2: compspecs}: forall sh n p,
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof.
  intros. unfold data_at_, field_at_. apply hc3b_init_data_at_cs.
Qed.

Lemma hc3b_init_HASH_len m : Zlength (HASH m) = 32.
Proof.
  unfold HASH, blake2s, WgNoise.proof.blake2s.model.b2s_digest_stream, WgNoise.proof.blake2s.model.b2s_out.
  rewrite Zlength_map. reflexivity.
Qed.

Lemma hc3b_init_mh_len h d : Zlength (mix_hash h d) = 32.
Proof. unfold mix_hash. apply hc3b_init_HASH_len. Qed.

Lemma hc3b_init_hmac_len key m : Zlength (hmac key m) = 32.
Proof. unfold hmac. apply hc3b_init_HASH_len. Qed.

Lemma hc3b_init_kdf1_len ck d : Zlength (kdf1 ck d) = 32.
Proof. unfold kdf1. apply hc3b_init_hmac_len. Qed.

Lemma hc3b_init_kdf2_len ck d : Zlength (kdf2 ck d) = 32.
Proof. unfold kdf2. apply hc3b_init_hmac_len. Qed.

Lemma hc3b_init_init_ck_len : Zlength init_ck = 32.
Proof. unfold init_ck. apply hc3b_init_HASH_len. Qed.

Lemma hc3b_init_clamp_len raw : Zlength raw = 32 -> Zlength (clamp raw) = 32.
Proof. intros. unfold clamp. list_solve. Qed.

Lemma hc3b_init_hin_ne sh bs p : Zlength bs <> 0 -> hin sh bs p = hbytes sh bs p.
Proof. intros. unfold hin. destruct (Z.eq_dec (Zlength bs) 0); [contradiction | reflexivity]. Qed.

Lemma hc3b_init_hbytes_out sh bs v : hbytes sh bs v |-- hout sh (Zlength bs) v.
Proof. unfold hbytes, hout. apply data_at_data_at_. Qed.

Lemma hc3b_init_hbytes_out' sh bs n v : Zlength bs = n -> hbytes sh bs v |-- hout sh n v.
Proof. intros <-. apply hc3b_init_hbytes_out. Qed.

Lemma hc3b_init_fc_root {cs: compspecs} t gf gfs p :
  field_compatible t (gf :: gfs) p -> field_compatible t [] p.
Proof. intros (?&?&?&?&?). repeat split; auto. Qed.

(* the model's exits *)
Section Model.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.

Lemma hc3b_init_exit1 SPUB RPUB SS ERAW TS :
  dh_ok x25519 (clamp ERAW) basepoint9 = false ->
  m_create_initiation_model x25519 aead_enc SPUB RPUB SS ERAW TS = None.
Proof. intros D1. unfold m_create_initiation_model. cbv zeta. rewrite D1. reflexivity. Qed.

Lemma hc3b_init_exit2 SPUB RPUB SS ERAW TS :
  dh_ok x25519 (clamp ERAW) basepoint9 = true -> dh_ok x25519 (clamp ERAW) RPUB = false ->
  m_create_initiation_model x25519 aead_enc SPUB RPUB SS ERAW TS = None.
Proof. intros D1 D2. unfold m_create_initiation_model. cbv zeta. rewrite D1, D2. reflexivity. Qed.

Lemma hc3b_init_exit3 SPUB RPUB SS ERAW TS :
  dh_ok x25519 (clamp ERAW) basepoint9 = true -> dh_ok x25519 (clamp ERAW) RPUB = true ->
  is_zero SS = true ->
  m_create_initiation_model x25519 aead_enc SPUB RPUB SS ERAW TS = None.
Proof. intros D1 D2 D3. unfold m_create_initiation_model. cbv zeta. rewrite D1, D2, D3. reflexivity. Qed.

Lemma hc3b_init_success SPUB RPUB SS ERAW TS h0 E h1 ck1 DH ck2 key2 encs h2 ck3 key3 enct h3 :
  dh_ok x25519 (clamp ERAW) basepoint9 = true -> dh_ok x25519 (clamp ERAW) RPUB = true ->
  is_zero SS = false ->
  h0 = mix_hash init_hash RPUB -> E = x25519 (clamp ERAW) basepoint9 -> h1 = mix_hash h0 E ->
  ck1 = kdf1 init_ck E -> DH = x25519 (clamp ERAW) RPUB -> ck2 = kdf1 ck1 DH -> key2 = kdf2 ck1 DH ->
  encs = aead_enc key2 0 h1 SPUB -> h2 = mix_hash h1 encs -> ck3 = kdf1 ck2 SS -> key3 = kdf2 ck2 SS ->
  enct = aead_enc key3 0 h2 TS -> h3 = mix_hash h2 enct ->
  m_create_initiation_model x25519 aead_enc SPUB RPUB SS ERAW TS = Some (E, encs, enct, clamp ERAW, ck3, h3).
Proof.
  intros D1 D2 D3 -> -> -> -> -> -> -> -> -> -> -> -> ->.
  unfold m_create_initiation_model. cbv zeta. rewrite D1, D2, D3. reflexivity.
Qed.
End Model.

(* the body's compspecs *)
#[local] Existing Instance CSkinit.
#[local] Instance hc3b_init_HCS_CSkinit : change_composite_env HCS CSkinit.
Proof. make_cs_preserve HCS CSkinit. Defined.

Definition hc3b_init_CSkinit_HCS : change_composite_env CSkinit HCS.
Proof. make_cs_preserve CSkinit HCS. Defined.

Local Open Scope logic.

Definition hc3b_init_fa (f: ident) (p: val) : val := @field_address CSkinit t_minit (DOT f) p.

Lemma hc3b_init_minit_out sh p :
  @data_at_ HCS sh t_minit p =
  hout sh 32 (hc3b_init_fa FH._ephemeral p) * hout sh 48 (hc3b_init_fa FH._enc_static p) *
  hout sh 28 (hc3b_init_fa FH._enc_timestamp p) * hout sh 32 (hc3b_init_fa FH._eph_priv p) *
  @data_at_ HCS sh t_mstate (hc3b_init_fa FH._st p).
Proof.
  erewrite (@data_at__change_composite HCS CSkinit _ sh t_minit); [| prove_cs_preserve_type].
  rewrite data_at__eq. unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_minit (DOT FH._ephemeral)), (field_at_data_at sh t_minit (DOT FH._enc_static)),
    (field_at_data_at sh t_minit (DOT FH._enc_timestamp)), (field_at_data_at sh t_minit (DOT FH._eph_priv)),
    (field_at_data_at sh t_minit (DOT FH._st)).
  unfold hout, hc3b_init_fa. rewrite <- !(@hc3b_init_data_at__cs CSkinit HCS).
  erewrite (@data_at__change_composite HCS CSkinit _ sh t_mstate); [| prove_cs_preserve_type].
  rewrite !data_at__eq. rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma hc3b_init_minit_out_k sh p :
  @data_at_ CSkinit sh t_minit p =
  hout sh 32 (hc3b_init_fa FH._ephemeral p) * hout sh 48 (hc3b_init_fa FH._enc_static p) *
  hout sh 28 (hc3b_init_fa FH._enc_timestamp p) * hout sh 32 (hc3b_init_fa FH._eph_priv p) *
  @data_at_ HCS sh t_mstate (hc3b_init_fa FH._st p).
Proof.
  rewrite <- hc3b_init_minit_out.
  erewrite (@data_at__change_composite HCS CSkinit _ sh t_minit); [| prove_cs_preserve_type]. reflexivity.
Qed.

Lemma hc3b_init_minit_eq sh E encs enct ep ck h p :
  Zlength E = 32 -> Zlength encs = 48 -> Zlength enct = 28 -> Zlength ep = 32 ->
  @data_at HCS sh t_minit (minit_val E encs enct ep ck h) p =
  hbytes sh E (hc3b_init_fa FH._ephemeral p) * hbytes sh encs (hc3b_init_fa FH._enc_static p) *
  hbytes sh enct (hc3b_init_fa FH._enc_timestamp p) * hbytes sh ep (hc3b_init_fa FH._eph_priv p) *
  @data_at HCS sh t_mstate (mstate_val ck h) (hc3b_init_fa FH._st p).
Proof.
  intros H1 H2 H3 H4.
  erewrite (@data_at_change_composite HCS CSkinit _ sh t_minit); [| apply JMeq_refl | prove_cs_preserve_type].
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_minit (DOT FH._ephemeral)), (field_at_data_at sh t_minit (DOT FH._enc_static)),
    (field_at_data_at sh t_minit (DOT FH._enc_timestamp)), (field_at_data_at sh t_minit (DOT FH._eph_priv)),
    (field_at_data_at sh t_minit (DOT FH._st)).
  unfold hbytes, hc3b_init_fa. rewrite H1, H2, H3, H4. rewrite <- !(@hc3b_init_data_at_cs CSkinit HCS).
  erewrite (@data_at_change_composite HCS CSkinit _ sh t_mstate); [| apply JMeq_refl | prove_cs_preserve_type].
  rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma hc3b_init_minit_eq_k sh E encs enct ep ck h p :
  Zlength E = 32 -> Zlength encs = 48 -> Zlength enct = 28 -> Zlength ep = 32 ->
  @data_at CSkinit sh t_minit (minit_val E encs enct ep ck h) p =
  hbytes sh E (hc3b_init_fa FH._ephemeral p) * hbytes sh encs (hc3b_init_fa FH._enc_static p) *
  hbytes sh enct (hc3b_init_fa FH._enc_timestamp p) * hbytes sh ep (hc3b_init_fa FH._eph_priv p) *
  @data_at HCS sh t_mstate (mstate_val ck h) (hc3b_init_fa FH._st p).
Proof.
  intros. rewrite <- hc3b_init_minit_eq by auto.
  erewrite (@data_at_change_composite HCS CSkinit _ sh t_minit); [reflexivity | apply JMeq_refl | prove_cs_preserve_type].
Qed.

Lemma hc3b_init_minit_fc sh p : @data_at_ HCS sh t_minit p |-- !! @field_compatible CSkinit t_minit [] p.
Proof.
  erewrite (@data_at__change_composite HCS CSkinit _ sh t_minit) by prove_cs_preserve_type.
  entailer!.
Qed.

Lemma hc3b_init_local32 v : @data_at_ CSkinit Tsh (tarray tuchar 32) v = hout Tsh 32 v.
Proof. unfold hout. apply hc3b_init_data_at__cs. Qed.

Definition hc3b_init_is {A: Type} (x y: A) : Prop := x = y.
Lemma hc3b_init_isI {A: Type} (x y: A) : x = y -> hc3b_init_is x y.
Proof. auto. Qed.

Ltac hc3b_init_fa_tac :=
  unfold hc3b_init_fa; rewrite ?field_address_offset by auto with field_compatible; reflexivity.

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

Lemma hc3_body_m_create_initiation_handshake :
  @semax_body (hc3_V_bp WgNoise.harness.x_handshake.code._x_handshake__M_BASEPOINT) (hc3_G_m_create_initiation x25519 aead_enc WgNoise.harness.x_handshake.code._x_handshake__M_CONSTRUCTION WgNoise.harness.x_handshake.code._x_handshake__M_IDENTIFIER) CSkinit WgNoise.harness.x_handshake.code.f_m_create_initiation (m_create_initiation_spec x25519 aead_enc WgNoise.harness.x_handshake.code._x_handshake__M_BASEPOINT WgNoise.harness.x_handshake.code._x_handshake__M_CONSTRUCTION WgNoise.harness.x_handshake.code._x_handshake__M_IDENTIFIER).
Proof.
start_function.
assert_PROP (field_compatible t_minit [] o) as FC. { sep_apply (hc3b_init_minit_fc sho o). entailer!. }
rewrite hc3b_init_minit_out. repeat flatten_sepcon_in_SEP.
rewrite !hc3b_init_local32.
forward_call (gv, sho, hc3b_init_fa FH._st o, sh, pr, RPUB).
{ entailer!. simpl. hc3b_init_fa_tac. }
assert (L0: Zlength (mix_hash init_hash RPUB) = 32) by apply hc3b_init_mh_len.
remember (mix_hash init_hash RPUB) as h0 eqn:Eh0. apply hc3b_init_isI in Eh0.
replace (hout sho 32 (hc3b_init_fa FH._eph_priv o)) with (hout sho (Zlength ERAW) (hc3b_init_fa FH._eph_priv o)) by (rewrite H2; reflexivity).
forward_call (sho, hc3b_init_fa FH._eph_priv o, sh, pe, ERAW).
{ entailer!. simpl. rewrite H2. hc3b_init_fa_tac. }
forward_call (sho, hc3b_init_fa FH._eph_priv o, ERAW).
{ entailer!. simpl. hc3b_init_fa_tac. }
assert (LP: Zlength (clamp ERAW) = 32) by (apply hc3b_init_clamp_len; auto).
change (hc_const gv FH._x_handshake__M_BASEPOINT basepoint9) with (hbytes Ers basepoint9 (gv FH._x_handshake__M_BASEPOINT)).
forward_call (sho, hc3b_init_fa FH._ephemeral o, sho, hc3b_init_fa FH._eph_priv o, clamp ERAW, Ers, gv FH._x_handshake__M_BASEPOINT, basepoint9).
{ entailer!. simpl. hc3b_init_fa_tac. }
destruct (dh_ok x25519 (clamp ERAW) basepoint9) eqn:D1.
2:{ forward_if; [| contradiction]. forward. rewrite (hc3b_init_exit1 x25519 aead_enc SPUB RPUB SS ERAW TS D1).
  rewrite hc3b_init_minit_out_k, !hc3b_init_local32.
  apply andp_right; [apply prop_right; reflexivity |].
  sep_apply (hc3b_init_hbytes_out' sho _ 32 (hc3b_init_fa FH._ephemeral o) (X25519 (clamp ERAW) basepoint9)).
  sep_apply (hc3b_init_hbytes_out' sho _ 32 (hc3b_init_fa FH._eph_priv o) LP).
  sep_apply (@data_at_data_at_ HCS sho t_mstate).
  unfold hc_const. fold (hbytes Ers basepoint9 (gv FH._x_handshake__M_BASEPOINT)). cancel. }
forward_if; [ discriminate | ].
assert (LE: Zlength (x25519 (clamp ERAW) basepoint9) = 32) by apply X25519.
remember (x25519 (clamp ERAW) basepoint9) as E eqn:EE. apply hc3b_init_isI in EE.
pose proof hc3b_init_init_ck_len as LC0.
remember init_ck as ck0 eqn:Eck0. apply hc3b_init_isI in Eck0.
rewrite <- (hc3b_init_hin_ne sho E (hc3b_init_fa FH._ephemeral o)) by lia.
forward_call (gv, sho, hc3b_init_fa FH._st o, ck0, h0, sho, hc3b_init_fa FH._ephemeral o, E).
{ entailer!. simpl. rewrite LE. hc3b_init_fa_tac. }
assert (L1: Zlength (mix_hash h0 E) = 32) by apply hc3b_init_mh_len.
remember (mix_hash h0 E) as h1 eqn:Eh1. apply hc3b_init_isI in Eh1.
forward_call (gv, sho, hc3b_init_fa FH._st o, ck0, h1, sho, hc3b_init_fa FH._ephemeral o, E).
{ entailer!. simpl. rewrite LE. hc3b_init_fa_tac. }
assert (LC1: Zlength (kdf1 ck0 E) = 32) by apply hc3b_init_kdf1_len.
remember (kdf1 ck0 E) as ck1 eqn:Eck1. apply hc3b_init_isI in Eck1.
rewrite (hc3b_init_hin_ne sho E (hc3b_init_fa FH._ephemeral o)) by lia.
forward_call (Tsh, v_dh, sho, hc3b_init_fa FH._eph_priv o, clamp ERAW, sh, pr, RPUB).
{ entailer!. simpl. hc3b_init_fa_tac. }
destruct (dh_ok x25519 (clamp ERAW) RPUB) eqn:D2.
2:{ forward_if; [| contradiction]. forward. rewrite (hc3b_init_exit2 x25519 aead_enc SPUB RPUB SS ERAW TS D1 D2).
  rewrite hc3b_init_minit_out_k, !hc3b_init_local32.
  apply andp_right; [apply prop_right; reflexivity |].
  sep_apply (hc3b_init_hbytes_out' sho _ 32 (hc3b_init_fa FH._ephemeral o) LE).
  sep_apply (hc3b_init_hbytes_out' sho _ 32 (hc3b_init_fa FH._eph_priv o) LP).
  sep_apply (hc3b_init_hbytes_out' Tsh _ 32 v_dh (X25519 (clamp ERAW) RPUB)).
  sep_apply (@data_at_data_at_ HCS sho t_mstate).
  unfold hc_const. fold (hbytes Ers basepoint9 (gv FH._x_handshake__M_BASEPOINT)). cancel. }
forward_if; [ discriminate | ].
assert (LD: Zlength (x25519 (clamp ERAW) RPUB) = 32) by apply X25519.
remember (x25519 (clamp ERAW) RPUB) as DH eqn:EDH. apply hc3b_init_isI in EDH.
rewrite <- (hc3b_init_hin_ne Tsh DH v_dh) by lia.
forward_call (gv, sho, hc3b_init_fa FH._st o, ck1, h1, Tsh, v_key, Tsh, v_dh, DH).
{ entailer!. simpl. rewrite LD. hc3b_init_fa_tac. }
rewrite (hc3b_init_hin_ne Tsh DH v_dh) by lia.
assert (LC2: Zlength (kdf1 ck1 DH) = 32) by apply hc3b_init_kdf1_len.
assert (LK2: Zlength (kdf2 ck1 DH) = 32) by apply hc3b_init_kdf2_len.
remember (kdf1 ck1 DH) as ck2 eqn:Eck2. apply hc3b_init_isI in Eck2.
remember (kdf2 ck1 DH) as key2 eqn:Ekey2. apply hc3b_init_isI in Ekey2.
replace (hout sho 48 (hc3b_init_fa FH._enc_static o)) with (hout sho (Zlength SPUB + 16) (hc3b_init_fa FH._enc_static o)) by (rewrite H; reflexivity).
rewrite <- (hc3b_init_hin_ne sh SPUB ps) by lia.
forward_call (gv, sho, hc3b_init_fa FH._st o, ck2, h1, sho, hc3b_init_fa FH._enc_static o, sh, ps, SPUB, Tsh, v_key, key2).
{ entailer!. simpl. rewrite H. hc3b_init_fa_tac. }
rewrite (hc3b_init_hin_ne sh SPUB ps) by lia.
assert (LS: Zlength (aead_enc key2 0 h1 SPUB) = 48) by (rewrite (aead_enc_length _ _ AEAD), H; reflexivity).
remember (aead_enc key2 0 h1 SPUB) as encs eqn:Eencs. apply hc3b_init_isI in Eencs.
assert (L2: Zlength (mix_hash h1 encs) = 32) by apply hc3b_init_mh_len.
remember (mix_hash h1 encs) as h2 eqn:Eh2. apply hc3b_init_isI in Eh2.
forward_call (sh, pss, SS).
{ entailer!. simpl. rewrite H1. reflexivity. }
destruct (is_zero SS) eqn:D3.
{ forward_if; [| discriminate]. forward. rewrite (hc3b_init_exit3 x25519 aead_enc SPUB RPUB SS ERAW TS D1 D2 D3).
  rewrite hc3b_init_minit_out_k, !hc3b_init_local32.
  apply andp_right; [apply prop_right; reflexivity |].
  sep_apply (hc3b_init_hbytes_out' sho _ 32 (hc3b_init_fa FH._ephemeral o) LE).
  sep_apply (hc3b_init_hbytes_out' sho _ 32 (hc3b_init_fa FH._eph_priv o) LP).
  sep_apply (hc3b_init_hbytes_out' sho _ 48 (hc3b_init_fa FH._enc_static o) LS).
  sep_apply (hc3b_init_hbytes_out' Tsh _ 32 v_dh LD).
  sep_apply (hc3b_init_hbytes_out' Tsh _ 32 v_key LK2).
  sep_apply (@data_at_data_at_ HCS sho t_mstate).
  unfold hc_const. fold (hbytes Ers basepoint9 (gv FH._x_handshake__M_BASEPOINT)). cancel. }
forward_if; [ contradiction | ].
sep_apply (hc3b_init_hbytes_out' Tsh _ 32 v_key LK2).
rewrite <- (hc3b_init_hin_ne sh SS pss) by lia.
forward_call (gv, sho, hc3b_init_fa FH._st o, ck2, h2, Tsh, v_key, sh, pss, SS).
{ entailer!. simpl. rewrite H1. hc3b_init_fa_tac. }
rewrite (hc3b_init_hin_ne sh SS pss) by lia.
assert (LC3: Zlength (kdf1 ck2 SS) = 32) by apply hc3b_init_kdf1_len.
assert (LK3: Zlength (kdf2 ck2 SS) = 32) by apply hc3b_init_kdf2_len.
remember (kdf1 ck2 SS) as ck3 eqn:Eck3. apply hc3b_init_isI in Eck3.
remember (kdf2 ck2 SS) as key3 eqn:Ekey3. apply hc3b_init_isI in Ekey3.
replace (hout sho 28 (hc3b_init_fa FH._enc_timestamp o)) with (hout sho (Zlength TS + 16) (hc3b_init_fa FH._enc_timestamp o)) by (rewrite H3; reflexivity).
rewrite <- (hc3b_init_hin_ne sh TS pt) by lia.
forward_call (gv, sho, hc3b_init_fa FH._st o, ck3, h2, sho, hc3b_init_fa FH._enc_timestamp o, sh, pt, TS, Tsh, v_key, key3).
{ entailer!. simpl. rewrite H3. hc3b_init_fa_tac. }
rewrite (hc3b_init_hin_ne sh TS pt) by lia.
assert (LT: Zlength (aead_enc key3 0 h2 TS) = 28) by (rewrite (aead_enc_length _ _ AEAD), H3; reflexivity).
remember (aead_enc key3 0 h2 TS) as enct eqn:Eenct. apply hc3b_init_isI in Eenct.
remember (mix_hash h2 enct) as h3 eqn:Eh3. apply hc3b_init_isI in Eh3.
forward.
rewrite (hc3b_init_success x25519 aead_enc SPUB RPUB SS ERAW TS h0 E h1 ck1 DH ck2 key2 encs h2 ck3 key3 enct h3
  D1 D2 D3 Eh0 EE Eh1 ltac:(rewrite Eck1, Eck0; reflexivity) EDH Eck2 Ekey2 Eencs Eh2 Eck3 Ekey3 Eenct Eh3).
rewrite (hc3b_init_minit_eq sho E encs enct (clamp ERAW) ck3 h3 o LE LS LT LP), !hc3b_init_local32.
apply andp_right; [apply prop_right; reflexivity |].
sep_apply (hc3b_init_hbytes_out' Tsh _ 32 v_dh LD).
sep_apply (hc3b_init_hbytes_out' Tsh _ 32 v_key LK3).
unfold hc_const. fold (hbytes Ers basepoint9 (gv FH._x_handshake__M_BASEPOINT)). cancel.
Unshelve. all: exact hc3b_init_CSkinit_HCS.
Qed.

Lemma hc3_body_m_create_initiation_consume_initiation_any :
  @semax_body (hc3_V_bp WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_BASEPOINT) (hc3_G_m_create_initiation x25519 aead_enc WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_CONSTRUCTION WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_IDENTIFIER) CSkinit WgNoise.harness.x_consume_initiation_any.code.f_m_create_initiation (m_create_initiation_spec x25519 aead_enc WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_BASEPOINT WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_CONSTRUCTION WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_IDENTIFIER).
Proof.
start_function.
assert_PROP (field_compatible t_minit [] o) as FC. { sep_apply (hc3b_init_minit_fc sho o). entailer!. }
rewrite hc3b_init_minit_out. repeat flatten_sepcon_in_SEP.
rewrite !hc3b_init_local32.
forward_call (gv, sho, hc3b_init_fa FH._st o, sh, pr, RPUB).
{ entailer!. simpl. hc3b_init_fa_tac. }
assert (L0: Zlength (mix_hash init_hash RPUB) = 32) by apply hc3b_init_mh_len.
remember (mix_hash init_hash RPUB) as h0 eqn:Eh0. apply hc3b_init_isI in Eh0.
replace (hout sho 32 (hc3b_init_fa FH._eph_priv o)) with (hout sho (Zlength ERAW) (hc3b_init_fa FH._eph_priv o)) by (rewrite H2; reflexivity).
forward_call (sho, hc3b_init_fa FH._eph_priv o, sh, pe, ERAW).
{ entailer!. simpl. rewrite H2. hc3b_init_fa_tac. }
forward_call (sho, hc3b_init_fa FH._eph_priv o, ERAW).
{ entailer!. simpl. hc3b_init_fa_tac. }
assert (LP: Zlength (clamp ERAW) = 32) by (apply hc3b_init_clamp_len; auto).
change (hc_const gv WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_BASEPOINT basepoint9) with (hbytes Ers basepoint9 (gv WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_BASEPOINT)).
forward_call (sho, hc3b_init_fa FH._ephemeral o, sho, hc3b_init_fa FH._eph_priv o, clamp ERAW, Ers, gv WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_BASEPOINT, basepoint9).
{ entailer!. simpl. hc3b_init_fa_tac. }
destruct (dh_ok x25519 (clamp ERAW) basepoint9) eqn:D1.
2:{ forward_if; [| contradiction]. forward. rewrite (hc3b_init_exit1 x25519 aead_enc SPUB RPUB SS ERAW TS D1).
  rewrite hc3b_init_minit_out_k, !hc3b_init_local32.
  apply andp_right; [apply prop_right; reflexivity |].
  sep_apply (hc3b_init_hbytes_out' sho _ 32 (hc3b_init_fa FH._ephemeral o) (X25519 (clamp ERAW) basepoint9)).
  sep_apply (hc3b_init_hbytes_out' sho _ 32 (hc3b_init_fa FH._eph_priv o) LP).
  sep_apply (@data_at_data_at_ HCS sho t_mstate).
  unfold hc_const. fold (hbytes Ers basepoint9 (gv WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_BASEPOINT)). cancel. }
forward_if; [ discriminate | ].
assert (LE: Zlength (x25519 (clamp ERAW) basepoint9) = 32) by apply X25519.
remember (x25519 (clamp ERAW) basepoint9) as E eqn:EE. apply hc3b_init_isI in EE.
pose proof hc3b_init_init_ck_len as LC0.
remember init_ck as ck0 eqn:Eck0. apply hc3b_init_isI in Eck0.
rewrite <- (hc3b_init_hin_ne sho E (hc3b_init_fa FH._ephemeral o)) by lia.
forward_call (gv, sho, hc3b_init_fa FH._st o, ck0, h0, sho, hc3b_init_fa FH._ephemeral o, E).
{ entailer!. simpl. rewrite LE. hc3b_init_fa_tac. }
assert (L1: Zlength (mix_hash h0 E) = 32) by apply hc3b_init_mh_len.
remember (mix_hash h0 E) as h1 eqn:Eh1. apply hc3b_init_isI in Eh1.
forward_call (gv, sho, hc3b_init_fa FH._st o, ck0, h1, sho, hc3b_init_fa FH._ephemeral o, E).
{ entailer!. simpl. rewrite LE. hc3b_init_fa_tac. }
assert (LC1: Zlength (kdf1 ck0 E) = 32) by apply hc3b_init_kdf1_len.
remember (kdf1 ck0 E) as ck1 eqn:Eck1. apply hc3b_init_isI in Eck1.
rewrite (hc3b_init_hin_ne sho E (hc3b_init_fa FH._ephemeral o)) by lia.
forward_call (Tsh, v_dh, sho, hc3b_init_fa FH._eph_priv o, clamp ERAW, sh, pr, RPUB).
{ entailer!. simpl. hc3b_init_fa_tac. }
destruct (dh_ok x25519 (clamp ERAW) RPUB) eqn:D2.
2:{ forward_if; [| contradiction]. forward. rewrite (hc3b_init_exit2 x25519 aead_enc SPUB RPUB SS ERAW TS D1 D2).
  rewrite hc3b_init_minit_out_k, !hc3b_init_local32.
  apply andp_right; [apply prop_right; reflexivity |].
  sep_apply (hc3b_init_hbytes_out' sho _ 32 (hc3b_init_fa FH._ephemeral o) LE).
  sep_apply (hc3b_init_hbytes_out' sho _ 32 (hc3b_init_fa FH._eph_priv o) LP).
  sep_apply (hc3b_init_hbytes_out' Tsh _ 32 v_dh (X25519 (clamp ERAW) RPUB)).
  sep_apply (@data_at_data_at_ HCS sho t_mstate).
  unfold hc_const. fold (hbytes Ers basepoint9 (gv WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_BASEPOINT)). cancel. }
forward_if; [ discriminate | ].
assert (LD: Zlength (x25519 (clamp ERAW) RPUB) = 32) by apply X25519.
remember (x25519 (clamp ERAW) RPUB) as DH eqn:EDH. apply hc3b_init_isI in EDH.
rewrite <- (hc3b_init_hin_ne Tsh DH v_dh) by lia.
forward_call (gv, sho, hc3b_init_fa FH._st o, ck1, h1, Tsh, v_key, Tsh, v_dh, DH).
{ entailer!. simpl. rewrite LD. hc3b_init_fa_tac. }
rewrite (hc3b_init_hin_ne Tsh DH v_dh) by lia.
assert (LC2: Zlength (kdf1 ck1 DH) = 32) by apply hc3b_init_kdf1_len.
assert (LK2: Zlength (kdf2 ck1 DH) = 32) by apply hc3b_init_kdf2_len.
remember (kdf1 ck1 DH) as ck2 eqn:Eck2. apply hc3b_init_isI in Eck2.
remember (kdf2 ck1 DH) as key2 eqn:Ekey2. apply hc3b_init_isI in Ekey2.
replace (hout sho 48 (hc3b_init_fa FH._enc_static o)) with (hout sho (Zlength SPUB + 16) (hc3b_init_fa FH._enc_static o)) by (rewrite H; reflexivity).
rewrite <- (hc3b_init_hin_ne sh SPUB ps) by lia.
forward_call (gv, sho, hc3b_init_fa FH._st o, ck2, h1, sho, hc3b_init_fa FH._enc_static o, sh, ps, SPUB, Tsh, v_key, key2).
{ entailer!. simpl. rewrite H. hc3b_init_fa_tac. }
rewrite (hc3b_init_hin_ne sh SPUB ps) by lia.
assert (LS: Zlength (aead_enc key2 0 h1 SPUB) = 48) by (rewrite (aead_enc_length _ _ AEAD), H; reflexivity).
remember (aead_enc key2 0 h1 SPUB) as encs eqn:Eencs. apply hc3b_init_isI in Eencs.
assert (L2: Zlength (mix_hash h1 encs) = 32) by apply hc3b_init_mh_len.
remember (mix_hash h1 encs) as h2 eqn:Eh2. apply hc3b_init_isI in Eh2.
forward_call (sh, pss, SS).
{ entailer!. simpl. rewrite H1. reflexivity. }
destruct (is_zero SS) eqn:D3.
{ forward_if; [| discriminate]. forward. rewrite (hc3b_init_exit3 x25519 aead_enc SPUB RPUB SS ERAW TS D1 D2 D3).
  rewrite hc3b_init_minit_out_k, !hc3b_init_local32.
  apply andp_right; [apply prop_right; reflexivity |].
  sep_apply (hc3b_init_hbytes_out' sho _ 32 (hc3b_init_fa FH._ephemeral o) LE).
  sep_apply (hc3b_init_hbytes_out' sho _ 32 (hc3b_init_fa FH._eph_priv o) LP).
  sep_apply (hc3b_init_hbytes_out' sho _ 48 (hc3b_init_fa FH._enc_static o) LS).
  sep_apply (hc3b_init_hbytes_out' Tsh _ 32 v_dh LD).
  sep_apply (hc3b_init_hbytes_out' Tsh _ 32 v_key LK2).
  sep_apply (@data_at_data_at_ HCS sho t_mstate).
  unfold hc_const. fold (hbytes Ers basepoint9 (gv WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_BASEPOINT)). cancel. }
forward_if; [ contradiction | ].
sep_apply (hc3b_init_hbytes_out' Tsh _ 32 v_key LK2).
rewrite <- (hc3b_init_hin_ne sh SS pss) by lia.
forward_call (gv, sho, hc3b_init_fa FH._st o, ck2, h2, Tsh, v_key, sh, pss, SS).
{ entailer!. simpl. rewrite H1. hc3b_init_fa_tac. }
rewrite (hc3b_init_hin_ne sh SS pss) by lia.
assert (LC3: Zlength (kdf1 ck2 SS) = 32) by apply hc3b_init_kdf1_len.
assert (LK3: Zlength (kdf2 ck2 SS) = 32) by apply hc3b_init_kdf2_len.
remember (kdf1 ck2 SS) as ck3 eqn:Eck3. apply hc3b_init_isI in Eck3.
remember (kdf2 ck2 SS) as key3 eqn:Ekey3. apply hc3b_init_isI in Ekey3.
replace (hout sho 28 (hc3b_init_fa FH._enc_timestamp o)) with (hout sho (Zlength TS + 16) (hc3b_init_fa FH._enc_timestamp o)) by (rewrite H3; reflexivity).
rewrite <- (hc3b_init_hin_ne sh TS pt) by lia.
forward_call (gv, sho, hc3b_init_fa FH._st o, ck3, h2, sho, hc3b_init_fa FH._enc_timestamp o, sh, pt, TS, Tsh, v_key, key3).
{ entailer!. simpl. rewrite H3. hc3b_init_fa_tac. }
rewrite (hc3b_init_hin_ne sh TS pt) by lia.
assert (LT: Zlength (aead_enc key3 0 h2 TS) = 28) by (rewrite (aead_enc_length _ _ AEAD), H3; reflexivity).
remember (aead_enc key3 0 h2 TS) as enct eqn:Eenct. apply hc3b_init_isI in Eenct.
remember (mix_hash h2 enct) as h3 eqn:Eh3. apply hc3b_init_isI in Eh3.
forward.
rewrite (hc3b_init_success x25519 aead_enc SPUB RPUB SS ERAW TS h0 E h1 ck1 DH ck2 key2 encs h2 ck3 key3 enct h3
  D1 D2 D3 Eh0 EE Eh1 ltac:(rewrite Eck1, Eck0; reflexivity) EDH Eck2 Ekey2 Eencs Eh2 Eck3 Ekey3 Eenct Eh3).
rewrite (hc3b_init_minit_eq sho E encs enct (clamp ERAW) ck3 h3 o LE LS LT LP), !hc3b_init_local32.
apply andp_right; [apply prop_right; reflexivity |].
sep_apply (hc3b_init_hbytes_out' Tsh _ 32 v_dh LD).
sep_apply (hc3b_init_hbytes_out' Tsh _ 32 v_key LK3).
unfold hc_const. fold (hbytes Ers basepoint9 (gv WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_BASEPOINT)). cancel.
Unshelve. all: exact hc3b_init_CSkinit_HCS.
Qed.

(* the group *)
Theorem hc3_bodies_init :
  (@semax_body (hc3_V_bp WgNoise.harness.x_handshake.code._x_handshake__M_BASEPOINT) (hc3_G_m_create_initiation x25519 aead_enc WgNoise.harness.x_handshake.code._x_handshake__M_CONSTRUCTION WgNoise.harness.x_handshake.code._x_handshake__M_IDENTIFIER) CSkinit WgNoise.harness.x_handshake.code.f_m_create_initiation (m_create_initiation_spec x25519 aead_enc WgNoise.harness.x_handshake.code._x_handshake__M_BASEPOINT WgNoise.harness.x_handshake.code._x_handshake__M_CONSTRUCTION WgNoise.harness.x_handshake.code._x_handshake__M_IDENTIFIER)) /\
  (@semax_body (hc3_V_bp WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_BASEPOINT) (hc3_G_m_create_initiation x25519 aead_enc WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_CONSTRUCTION WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_IDENTIFIER) CSkinit WgNoise.harness.x_consume_initiation_any.code.f_m_create_initiation (m_create_initiation_spec x25519 aead_enc WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_BASEPOINT WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_CONSTRUCTION WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_IDENTIFIER)).
Proof.
exact (conj hc3_body_m_create_initiation_handshake hc3_body_m_create_initiation_consume_initiation_any).
Qed.

End Bodies.
