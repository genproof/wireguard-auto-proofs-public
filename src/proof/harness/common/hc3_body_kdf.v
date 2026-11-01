(* hc_pieces3, group kdf: common.h bodies, proved once at a small compspecs with the callee context
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
Lemma hc3b_kdf_field_compatible_cs {cs1 cs2: compspecs}: forall n p,
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

Lemma hc3b_kdf_data_at_cs {cs1 cs2: compspecs}: forall sh n (v: list val) p,
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  intros. unfold data_at, field_at.
  f_equal. f_equal. apply prop_ext. apply hc3b_kdf_field_compatible_cs.
Qed.

Lemma hc3b_kdf_data_at__cs {cs1 cs2: compspecs}: forall sh n p,
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof.
  intros. unfold data_at_, field_at_. apply hc3b_kdf_data_at_cs.
Qed.

Lemma hc3b_kdf_hmac_len key m : Zlength (hmac key m) = 32.
Proof. unfold hmac, HASH, blake2s, b2s_digest_stream, b2s_out. rewrite Zlength_map. reflexivity. Qed.

Lemma hc3b_kdf_kdf_len ck d : Zlength (kdf1 ck d) = 32 /\ Zlength (kdf2 ck d) = 32 /\ Zlength (kdf3 ck d) = 32.
Proof. unfold kdf1, kdf2, kdf3. rewrite !hc3b_kdf_hmac_len. auto. Qed.

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

#[local] Existing Instance CSk.

(* an equality hidden from VST's automation (entailer! does not substitute it): keeps BLAKE2s terms out of
   the unifier's reach *)
Definition hc3b_kdf_eqk (a b: list byte) : Prop := a = b.

Lemma hc3b_kdf_to_hbytes sh A p n : Zlength A = n ->
  @data_at CSk sh (tarray tuchar n) (bytes A) p = hbytes sh A p.
Proof. intros <-. unfold hbytes. apply hc3b_kdf_data_at_cs. Qed.

Lemma hc3b_kdf_to_hin sh A p n : Zlength A = n -> 0 < n ->
  @data_at CSk sh (tarray tuchar n) (bytes A) p = hin sh A p.
Proof.
  intros <- Hn. unfold hin. rewrite if_false by lia. apply hc3b_kdf_to_hbytes; reflexivity.
Qed.

Lemma hc3b_kdf_to_hout sh n p : @data_at_ CSk sh (tarray tuchar n) p = hout sh n p.
Proof. unfold hout. apply hc3b_kdf_data_at__cs. Qed.

Lemma hc3b_kdf_upd32 (K: list byte) (x v: val) (b: byte) : Zlength K = 32 -> v = Vubyte b ->
  upd_Znth 32 (bytes K ++ [x]) v = bytes (K ++ [b]).
Proof.
  intros HK ->. unfold bytes. rewrite map_app.
  rewrite upd_Znth_app2 by (rewrite Zlength_map; list_solve).
  rewrite Zlength_map, HK. reflexivity.
Qed.

Lemma hc3b_kdf_bytes_snoc (K: list byte) (b: byte) : bytes (K ++ [b]) = bytes K ++ [Vubyte b].
Proof. unfold bytes. rewrite map_app. reflexivity. Qed.

Lemma hc3b_kdf_is_zero_dh (a b: list byte) :
  is_zero (x25519 a b) = negb (dh_ok x25519 a b).
Proof.
  unfold is_zero, dh_ok, bytes_eqb, memneq_bool, zeros32, zeros.
  rewrite (X25519 a b).
  destruct (list_eq_dec Byte.eq_dec _ _); reflexivity.
Qed.

Lemma hc3_body_m_kdf :
  @semax_body [] (hc3_G_m_kdf) CSk FH.f_m_kdf (m_kdf_spec).
Proof.
start_function.
rewrite (@hc3b_kdf_data_at__cs CSk HCS Tsh 32 v_prk).
forward_call (gv, Tsh, v_prk, shc, c, CK, shi, i, IN).
remember (hmac CK IN) as P eqn:EP. change (hc3b_kdf_eqk P (hmac CK IN)) in EP.
assert (LP: Zlength P = 32) by (rewrite EP; apply hc3b_kdf_hmac_len).
(* buf[0] = 1; T1 = hmac(prk, buf[0..1)) *)
forward.
replace (upd_Znth 0 (default_val (tarray tuchar 33)) (Vint (Int.zero_ext 8 (Int.repr 1))))
  with (bytes [Byte.one] ++ Zrepeat Vundef 32) by (vm_compute; reflexivity).
rewrite (split2_data_at_Tarray_app 1 33 Tsh tuchar) by reflexivity.
rewrite (hc3b_kdf_to_hin Tsh [Byte.one] v_buf 1) by (reflexivity || lia).
forward_call (gv, sh1, t1, Tsh, v_prk, P, Tsh, v_buf, [Byte.one]).
{ cancel. }
{ compute; discriminate. }
remember (hmac P [Byte.one]) as K1 eqn:EK1. change (hc3b_kdf_eqk K1 (hmac P [Byte.one])) in EK1.
assert (LK1: Zlength K1 = 32) by (rewrite EK1; apply hc3b_kdf_hmac_len).
(* bytes_copy(buf, t1, 32) *)
rewrite <- (hc3b_kdf_to_hin Tsh [Byte.one] v_buf 1) by (reflexivity || lia).
sep_apply (derives_refl' _ _ (eq_sym (split2_data_at_Tarray_app 1 33 Tsh tuchar
  (bytes [Byte.one]) (Zrepeat Vundef 32) v_buf eq_refl eq_refl))).
replace (bytes [Byte.one] ++ Zrepeat Vundef 32) with ((bytes [Byte.one] ++ Zrepeat Vundef 31) ++ [Vundef])
  by (vm_compute; reflexivity).
rewrite (split2_data_at_Tarray_app 32 33 Tsh tuchar (bytes [Byte.one] ++ Zrepeat Vundef 31) [Vundef])
  by reflexivity.
sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (bytes [Byte.one] ++ Zrepeat Vundef 31) v_buf).
rewrite hc3b_kdf_to_hout.
replace (hout Tsh 32 v_buf) with (hout Tsh (Zlength K1) v_buf) by (rewrite LK1; reflexivity).
forward_call (Tsh, v_buf, sh1, t1, K1).
{ rewrite LK1; apply prop_right; reflexivity. }
(* buf[32] = 2; T2 = hmac(prk, T1 || 2) *)
rewrite <- (hc3b_kdf_to_hbytes Tsh K1 v_buf 32 LK1).
assert (LB1: Zlength (bytes K1) = 32) by (unfold bytes; rewrite Zlength_map; auto).
sep_apply (derives_refl' _ _ (eq_sym (split2_data_at_Tarray_app 32 33 Tsh tuchar (bytes K1) [Vundef] v_buf
  LB1 eq_refl))).
forward.
change (@upd_Znth (reptype tuchar)) with (@upd_Znth val). change (@app (reptype tuchar)) with (@app val).
rewrite (hc3b_kdf_upd32 K1 Vundef (Vint (Int.zero_ext 8 (Int.repr 2))) (Byte.repr 2) LK1 eq_refl).
rewrite (hc3b_kdf_to_hin Tsh (K1 ++ [Byte.repr 2]) v_buf 33) by (try rewrite Zlength_app, LK1; reflexivity || lia).
forward_call (gv, sh2, t2, Tsh, v_prk, P, Tsh, v_buf, K1 ++ [Byte.repr 2]).
{ rewrite Zlength_app, LK1; apply prop_right; reflexivity. }
{ rewrite Zlength_app, LK1; compute; discriminate. }
remember (hmac P (K1 ++ [Byte.repr 2])) as K2 eqn:EK2. change (hc3b_kdf_eqk K2 (hmac P (K1 ++ [Byte.repr 2]))) in EK2.
assert (LK2: Zlength K2 = 32) by (rewrite EK2; apply hc3b_kdf_hmac_len).
(* bytes_copy(buf, t2, 32) *)
rewrite <- (hc3b_kdf_to_hin Tsh (K1 ++ [Byte.repr 2]) v_buf 33) by (try rewrite Zlength_app, LK1; reflexivity || lia).
rewrite hc3b_kdf_bytes_snoc.
rewrite (split2_data_at_Tarray_app 32 33 Tsh tuchar (bytes K1) [Vubyte (Byte.repr 2)]) by (reflexivity || assumption).
sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (bytes K1) v_buf).
rewrite hc3b_kdf_to_hout.
replace (hout Tsh 32 v_buf) with (hout Tsh (Zlength K2) v_buf) by (rewrite LK2; reflexivity).
forward_call (Tsh, v_buf, sh2, t2, K2).
{ rewrite LK2; apply prop_right; reflexivity. }
(* buf[32] = 3; T3 = hmac(prk, T2 || 3) *)
rewrite <- (hc3b_kdf_to_hbytes Tsh K2 v_buf 32 LK2).
assert (LB2: Zlength (bytes K2) = 32) by (unfold bytes; rewrite Zlength_map; auto).
sep_apply (derives_refl' _ _ (eq_sym (split2_data_at_Tarray_app 32 33 Tsh tuchar (bytes K2) [Vubyte (Byte.repr 2)]
  v_buf LB2 eq_refl))).
forward.
change (@upd_Znth (reptype tuchar)) with (@upd_Znth val). change (@app (reptype tuchar)) with (@app val).
rewrite (hc3b_kdf_upd32 K2 (Vubyte (Byte.repr 2)) (Vint (Int.zero_ext 8 (Int.repr 3))) (Byte.repr 3) LK2 eq_refl).
rewrite (hc3b_kdf_to_hin Tsh (K2 ++ [Byte.repr 3]) v_buf 33) by (try rewrite Zlength_app, LK2; reflexivity || lia).
forward_call (gv, sh3, t3, Tsh, v_prk, P, Tsh, v_buf, K2 ++ [Byte.repr 3]).
{ rewrite Zlength_app, LK2; apply prop_right; reflexivity. }
{ rewrite Zlength_app, LK2; compute; discriminate. }
remember (hmac P (K2 ++ [Byte.repr 3])) as K3 eqn:EK3. change (hc3b_kdf_eqk K3 (hmac P (K2 ++ [Byte.repr 3]))) in EK3.
assert (LK3: Zlength K3 = 32) by (rewrite EK3; apply hc3b_kdf_hmac_len).
(* the outputs are KDF_1..3 *)
assert (E1: kdf1 CK IN = K1).
{ unfold hc3b_kdf_eqk in *. unfold kdf1, kdf_prk. rewrite <- EP. symmetry; exact EK1. }
assert (E2: kdf2 CK IN = K2).
{ unfold hc3b_kdf_eqk in *. unfold kdf2. rewrite E1. unfold kdf_prk. rewrite <- EP. symmetry; exact EK2. }
assert (E3: kdf3 CK IN = K3).
{ unfold hc3b_kdf_eqk in *. unfold kdf3. rewrite E2. unfold kdf_prk. rewrite <- EP. symmetry; exact EK3. }
rewrite E1, E2, E3.
rewrite <- (hc3b_kdf_to_hbytes Tsh P v_prk 32 LP).
rewrite <- (hc3b_kdf_to_hin Tsh (K2 ++ [Byte.repr 3]) v_buf 33) by (try rewrite Zlength_app, LK2; reflexivity || lia).
clear EP EK1 EK2 EK3 E1 E2 E3.
entailer!.
Qed.

Lemma hc3_body_m_dh :
  @semax_body [] (hc3_G_m_dh x25519) CSk FH.f_m_dh (m_dh_spec x25519).
Proof.
start_function.
unfold hout, hbytes in *.
rewrite (@hc3b_kdf_data_at__cs HCS CSk).
rewrite !(@hc3b_kdf_data_at_cs HCS CSk).
rewrite H, H0. unfold bytes.
forward_call (sho, o, shv, v, PRIV, shp, p, PUB).
rewrite <- !(@hc3b_kdf_data_at_cs HCS CSk).
assert (E: forall sh A a, Zlength A = 32 -> @data_at HCS sh (tarray tuchar 32) (map Vubyte A) a = hbytes sh A a)
  by (intros sh A a HA; unfold hbytes; rewrite HA; reflexivity).
pose proof (X25519 PRIV PUB) as HX.
rewrite !E by auto.
forward_call (sho, o, x25519 PRIV PUB).
{ rewrite HX; apply prop_right; reflexivity. }
{ unfold hbytes; cancel. }
rewrite hc3b_kdf_is_zero_dh.
forward.
{ destruct (dh_ok x25519 PRIV PUB); entailer!. }
Qed.

(* m_transport, once for both laws (bp = the law's M_BASEPOINT, passed as a 0-length input) *)
Ltac hc3b_kdf_transport gv sh1 f sh2 s v_t3 shc c CK bp :=
  rewrite (@hc3b_kdf_data_at__cs CSk HCS);
  forward_call (gv, sh1, f, sh2, s, Tsh, v_t3, shc, c, CK, Ers, gv bp, @nil byte);
  [ unfold hin; rewrite if_true by reflexivity; cancel
  | compute; discriminate
  | destruct (hc3b_kdf_kdf_len CK []) as [L1 [L2 L3]];
    unfold hin; rewrite if_true by reflexivity;
    revert L1 L2 L3;
    generalize (kdf1 CK []) (kdf2 CK []) (kdf3 CK []); intros k1 k2 k3 L1 L2 L3;
    unfold hbytes at 3; rewrite L3; rewrite (@hc3b_kdf_data_at_cs HCS CSk);
    entailer! ].

Lemma hc3_body_m_transport_keypairs :
  @semax_body (hc3_V_bp WgNoise.harness.x_keypairs.code._x_keypairs__M_BASEPOINT) (hc3_G_m_transport) CSk WgNoise.harness.x_keypairs.code.f_m_transport (m_transport_spec WgNoise.harness.x_keypairs.code._x_keypairs__M_BASEPOINT).
Proof.
start_function.
hc3b_kdf_transport gv sh1 f sh2 s v_t3 shc c CK WgNoise.harness.x_keypairs.code._x_keypairs__M_BASEPOINT.
Qed.

Lemma hc3_body_m_transport_handshake :
  @semax_body (hc3_V_bp WgNoise.harness.x_handshake.code._x_handshake__M_BASEPOINT) (hc3_G_m_transport) CSk WgNoise.harness.x_handshake.code.f_m_transport (m_transport_spec WgNoise.harness.x_handshake.code._x_handshake__M_BASEPOINT).
Proof.
start_function.
hc3b_kdf_transport gv sh1 f sh2 s v_t3 shc c CK WgNoise.harness.x_handshake.code._x_handshake__M_BASEPOINT.
Qed.

(* the group *)
Theorem hc3_bodies_kdf :
  (@semax_body [] (hc3_G_m_kdf) CSk FH.f_m_kdf (m_kdf_spec)) /\
  (@semax_body [] (hc3_G_m_dh x25519) CSk FH.f_m_dh (m_dh_spec x25519)) /\
  (@semax_body (hc3_V_bp WgNoise.harness.x_keypairs.code._x_keypairs__M_BASEPOINT) (hc3_G_m_transport) CSk WgNoise.harness.x_keypairs.code.f_m_transport (m_transport_spec WgNoise.harness.x_keypairs.code._x_keypairs__M_BASEPOINT)) /\
  (@semax_body (hc3_V_bp WgNoise.harness.x_handshake.code._x_handshake__M_BASEPOINT) (hc3_G_m_transport) CSk WgNoise.harness.x_handshake.code.f_m_transport (m_transport_spec WgNoise.harness.x_handshake.code._x_handshake__M_BASEPOINT)).
Proof.
exact (conj hc3_body_m_kdf (conj hc3_body_m_dh (conj hc3_body_m_transport_keypairs hc3_body_m_transport_handshake))).
Qed.

End Bodies.
