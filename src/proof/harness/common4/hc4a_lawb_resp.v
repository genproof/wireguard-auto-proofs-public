(* m_create_response for the unit handshake_receive (a copy of
   hc4a_body_resp.v's proof for consume_response_any). *)
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
Require WgNoise.harness.x_config_any.code WgNoise.harness.x_handshake_receive.code.

Module FH := WgNoise.harness.x_handshake.code.
Module FK := WgNoise.harness.x_cookie_reply.code.
Module FR := WgNoise.harness.x_consume_response_any.code.

(* byte arrays across compspecs (copies of libc_bytes.v's lemmas, not loaded here) *)
Lemma hc4ab_resp_field_compatible_cs {cs1 cs2: compspecs}: forall n p,
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

Lemma hc4ab_resp_data_at_cs {cs1 cs2: compspecs}: forall sh n (v: list val) p,
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  intros. unfold data_at, field_at.
  f_equal. f_equal. apply prop_ext. apply hc4ab_resp_field_compatible_cs.
Qed.

Lemma hc4ab_resp_data_at__cs {cs1 cs2: compspecs}: forall sh n p,
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof.
  intros. unfold data_at_, field_at_. apply hc4ab_resp_data_at_cs.
Qed.

Lemma hc4ab_resp_HASH_len m : Zlength (HASH m) = 32.
Proof.
  unfold HASH, blake2s, WgNoise.proof.blake2s.model.b2s_digest_stream, WgNoise.proof.blake2s.model.b2s_out.
  rewrite Zlength_map. reflexivity.
Qed.

Lemma hc4ab_resp_mh_len h d : Zlength (mix_hash h d) = 32.
Proof. unfold mix_hash. apply hc4ab_resp_HASH_len. Qed.

Lemma hc4ab_resp_hmac_len key m : Zlength (hmac key m) = 32.
Proof. unfold hmac. apply hc4ab_resp_HASH_len. Qed.

Lemma hc4ab_resp_kdf1_len ck d : Zlength (kdf1 ck d) = 32.
Proof. unfold kdf1. apply hc4ab_resp_hmac_len. Qed.

Lemma hc4ab_resp_kdf2_len ck d : Zlength (kdf2 ck d) = 32.
Proof. unfold kdf2. apply hc4ab_resp_hmac_len. Qed.

Lemma hc4ab_resp_kdf3_len ck d : Zlength (kdf3 ck d) = 32.
Proof. unfold kdf3. apply hc4ab_resp_hmac_len. Qed.

Lemma hc4ab_resp_clamp_len raw : Zlength raw = 32 -> Zlength (clamp raw) = 32.
Proof. intros. unfold clamp. list_solve. Qed.

Lemma hc4ab_resp_hin_ne sh bs p : Zlength bs <> 0 -> hin sh bs p = hbytes sh bs p.
Proof. intros. unfold hin. destruct (Z.eq_dec (Zlength bs) 0); [contradiction | reflexivity]. Qed.

Lemma hc4ab_resp_hin_nil sh p : hin sh [] p = emp.
Proof. reflexivity. Qed.

Lemma hc4ab_resp_hbytes_out sh bs v : hbytes sh bs v |-- hout sh (Zlength bs) v.
Proof. unfold hbytes, hout. apply data_at_data_at_. Qed.

Lemma hc4ab_resp_hbytes_out' sh bs n v : Zlength bs = n -> hbytes sh bs v |-- hout sh n v.
Proof. intros <-. apply hc4ab_resp_hbytes_out. Qed.

(* the model's exits *)
Section Model.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

Lemma hc4ab_resp_cexit1 CK H EI SI PSK ERAW :
  dh_ok x25519 (clamp ERAW) basepoint9 = false ->
  m_create_response_model x25519 aead_enc CK H EI SI PSK ERAW = None.
Proof. intros D1. unfold m_create_response_model. cbv zeta. rewrite D1. reflexivity. Qed.

Lemma hc4ab_resp_cexit2 CK H EI SI PSK ERAW :
  dh_ok x25519 (clamp ERAW) basepoint9 = true -> dh_ok x25519 (clamp ERAW) EI = false ->
  m_create_response_model x25519 aead_enc CK H EI SI PSK ERAW = None.
Proof. intros D1 D2. unfold m_create_response_model. cbv zeta. rewrite D1, D2. reflexivity. Qed.

Lemma hc4ab_resp_cexit3 CK H EI SI PSK ERAW :
  dh_ok x25519 (clamp ERAW) basepoint9 = true -> dh_ok x25519 (clamp ERAW) EI = true ->
  dh_ok x25519 (clamp ERAW) SI = false ->
  m_create_response_model x25519 aead_enc CK H EI SI PSK ERAW = None.
Proof. intros D1 D2 D3. unfold m_create_response_model. cbv zeta. rewrite D1, D2, D3. reflexivity. Qed.

Lemma hc4ab_resp_csuccess CK H EI SI PSK ERAW E h1 ck1 DH1 ck2 DH2 ck3 ck4 key h2 encn h3 :
  dh_ok x25519 (clamp ERAW) basepoint9 = true -> dh_ok x25519 (clamp ERAW) EI = true ->
  dh_ok x25519 (clamp ERAW) SI = true ->
  E = x25519 (clamp ERAW) basepoint9 -> h1 = mix_hash H E -> ck1 = kdf1 CK E ->
  DH1 = x25519 (clamp ERAW) EI -> ck2 = kdf1 ck1 DH1 -> DH2 = x25519 (clamp ERAW) SI -> ck3 = kdf1 ck2 DH2 ->
  ck4 = kdf1 ck3 PSK -> key = kdf3 ck3 PSK -> h2 = mix_hash h1 (kdf2 ck3 PSK) ->
  encn = aead_enc key 0 h2 [] -> h3 = mix_hash h2 encn ->
  m_create_response_model x25519 aead_enc CK H EI SI PSK ERAW = Some (E, encn, clamp ERAW, ck4, h3).
Proof.
  intros D1 D2 D3 -> -> -> -> -> -> -> -> -> -> -> ->.
  unfold m_create_response_model. cbv zeta. rewrite D1, D2, D3. reflexivity.
Qed.

Lemma hc4ab_resp_rexit1 CK H EPRIV SPRIV PSK E ENCN :
  dh_ok x25519 EPRIV E = false ->
  m_consume_response_model x25519 aead_dec CK H EPRIV SPRIV PSK E ENCN = None.
Proof. intros D1. unfold m_consume_response_model, consume_resp_crypto. simpl. rewrite D1. reflexivity. Qed.

Lemma hc4ab_resp_rexit2 CK H EPRIV SPRIV PSK E ENCN :
  dh_ok x25519 EPRIV E = true -> dh_ok x25519 SPRIV E = false ->
  m_consume_response_model x25519 aead_dec CK H EPRIV SPRIV PSK E ENCN = None.
Proof. intros D1 D2. unfold m_consume_response_model, consume_resp_crypto. simpl. rewrite D1, D2. reflexivity. Qed.

Lemma hc4ab_resp_rfinal CK H EPRIV SPRIV PSK E ENCN h1 ck1 DH1 ck2 DH2 ck3 ck4 key h2 :
  dh_ok x25519 EPRIV E = true -> dh_ok x25519 SPRIV E = true ->
  h1 = mix_hash H E -> ck1 = kdf1 CK E -> DH1 = x25519 EPRIV E -> ck2 = kdf1 ck1 DH1 ->
  DH2 = x25519 SPRIV E -> ck3 = kdf1 ck2 DH2 -> ck4 = kdf1 ck3 PSK -> key = kdf3 ck3 PSK ->
  h2 = mix_hash h1 (kdf2 ck3 PSK) ->
  m_consume_response_model x25519 aead_dec CK H EPRIV SPRIV PSK E ENCN =
  match aead_dec key 0 h2 ENCN with None => None | Some _ => Some (ck4, mix_hash h2 ENCN) end.
Proof.
  intros D1 D2 -> -> -> -> -> -> -> -> ->.
  unfold m_consume_response_model, consume_resp_crypto. simpl. rewrite D1, D2. reflexivity.
Qed.
End Model.

Local Open Scope logic.

Definition hc4ab_resp_is {A: Type} (x y: A) : Prop := x = y.
Lemma hc4ab_resp_isI {A: Type} (x y: A) : x = y -> hc4ab_resp_is x y.
Proof. auto. Qed.

(* m_state at HCS: its two fields at the bodies' compspecs (suffix r: CSkresp, s: CSks) *)
#[local] Instance hc4ab_resp_HCS_CSkresp : change_composite_env HCS CSkresp.
Proof. make_cs_preserve HCS CSkresp. Defined.
Definition hc4ab_resp_CSkresp_HCS : change_composite_env CSkresp HCS.
Proof. make_cs_preserve CSkresp HCS. Defined.
#[local] Instance hc4ab_resp_HCS_CSks : change_composite_env HCS CSks.
Proof. make_cs_preserve HCS CSks. Defined.
Definition hc4ab_resp_CSks_HCS : change_composite_env CSks HCS.
Proof. make_cs_preserve CSks HCS. Defined.

Section MStater.
#[local] Existing Instance CSkresp.
Lemma hc4ab_resp_mstate_eqr sh ck h p :
  Zlength ck = 32 -> Zlength h = 32 ->
  @data_at HCS sh t_mstate (mstate_val ck h) p =
  hbytes sh ck (@field_address CSkresp t_mstate (DOT FH._ck) p) *
  hbytes sh h (@field_address CSkresp t_mstate (DOT FH._h) p).
Proof.
  intros H1 H2.
  erewrite (@data_at_change_composite HCS CSkresp _ sh t_mstate); [| apply JMeq_refl | prove_cs_preserve_type].
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mstate (DOT FH._ck)), (field_at_data_at sh t_mstate (DOT FH._h)).
  unfold hbytes. rewrite H1, H2.
  rewrite <- !(@hc4ab_resp_data_at_cs CSkresp HCS).
  reflexivity.
Qed.

Lemma hc4ab_resp_mstate_outr sh p :
  @data_at_ HCS sh t_mstate p =
  hout sh 32 (@field_address CSkresp t_mstate (DOT FH._ck) p) *
  hout sh 32 (@field_address CSkresp t_mstate (DOT FH._h) p).
Proof.
  erewrite (@data_at__change_composite HCS CSkresp _ sh t_mstate); [| prove_cs_preserve_type].
  rewrite data_at__eq. unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mstate (DOT FH._ck)), (field_at_data_at sh t_mstate (DOT FH._h)).
  unfold hout. rewrite <- !(@hc4ab_resp_data_at__cs CSkresp HCS).
  rewrite !data_at__eq. reflexivity.
Qed.

Lemma hc4ab_resp_mstate_fcr sh v p : @data_at HCS sh t_mstate v p |-- !! @field_compatible CSkresp t_mstate [] p.
Proof.
  erewrite (@data_at_change_composite HCS CSkresp _ sh t_mstate); [| apply JMeq_refl | prove_cs_preserve_type].
  entailer!.
Qed.

Lemma hc4ab_resp_mstate_fc_r sh p : @data_at_ HCS sh t_mstate p |-- !! @field_compatible CSkresp t_mstate [] p.
Proof.
  erewrite (@data_at__change_composite HCS CSkresp _ sh t_mstate) by prove_cs_preserve_type.
  entailer!.
Qed.
End MStater.

Section MStates.
#[local] Existing Instance CSks.
Lemma hc4ab_resp_mstate_eqs sh ck h p :
  Zlength ck = 32 -> Zlength h = 32 ->
  @data_at HCS sh t_mstate (mstate_val ck h) p =
  hbytes sh ck (@field_address CSks t_mstate (DOT FH._ck) p) *
  hbytes sh h (@field_address CSks t_mstate (DOT FH._h) p).
Proof.
  intros H1 H2.
  erewrite (@data_at_change_composite HCS CSks _ sh t_mstate); [| apply JMeq_refl | prove_cs_preserve_type].
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mstate (DOT FH._ck)), (field_at_data_at sh t_mstate (DOT FH._h)).
  unfold hbytes. rewrite H1, H2.
  rewrite <- !(@hc4ab_resp_data_at_cs CSks HCS).
  reflexivity.
Qed.

Lemma hc4ab_resp_mstate_outs sh p :
  @data_at_ HCS sh t_mstate p =
  hout sh 32 (@field_address CSks t_mstate (DOT FH._ck) p) *
  hout sh 32 (@field_address CSks t_mstate (DOT FH._h) p).
Proof.
  erewrite (@data_at__change_composite HCS CSks _ sh t_mstate); [| prove_cs_preserve_type].
  rewrite data_at__eq. unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mstate (DOT FH._ck)), (field_at_data_at sh t_mstate (DOT FH._h)).
  unfold hout. rewrite <- !(@hc4ab_resp_data_at__cs CSks HCS).
  rewrite !data_at__eq. reflexivity.
Qed.

Lemma hc4ab_resp_mstate_fcs sh v p : @data_at HCS sh t_mstate v p |-- !! @field_compatible CSks t_mstate [] p.
Proof.
  erewrite (@data_at_change_composite HCS CSks _ sh t_mstate); [| apply JMeq_refl | prove_cs_preserve_type].
  entailer!.
Qed.

Lemma hc4ab_resp_mstate_fc_s sh p : @data_at_ HCS sh t_mstate p |-- !! @field_compatible CSks t_mstate [] p.
Proof.
  erewrite (@data_at__change_composite HCS CSks _ sh t_mstate) by prove_cs_preserve_type.
  entailer!.
Qed.
End MStates.

Section RespCS.
#[local] Existing Instance CSkresp.

Definition hc4ab_resp_fa (f: ident) (p: val) : val := @field_address CSkresp t_mresp (DOT f) p.
Definition hc4ab_resp_fs (f: ident) (p: val) : val := @field_address CSkresp t_mstate (DOT f) p.

Lemma hc4ab_resp_mresp_out sh p :
  @data_at_ HCS sh t_mresp p =
  hout sh 32 (hc4ab_resp_fa FH._ephemeral p) * hout sh 16 (hc4ab_resp_fa FH._enc_nothing p) *
  hout sh 32 (hc4ab_resp_fa FH._eph_priv p) * @data_at_ HCS sh t_mstate (hc4ab_resp_fa FH._st p).
Proof.
  erewrite (@data_at__change_composite HCS CSkresp _ sh t_mresp); [| prove_cs_preserve_type].
  rewrite data_at__eq. unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mresp (DOT FH._ephemeral)), (field_at_data_at sh t_mresp (DOT FH._enc_nothing)),
    (field_at_data_at sh t_mresp (DOT FH._eph_priv)), (field_at_data_at sh t_mresp (DOT FH._st)).
  unfold hout, hc4ab_resp_fa. rewrite <- !(@hc4ab_resp_data_at__cs CSkresp HCS).
  erewrite (@data_at__change_composite HCS CSkresp _ sh t_mstate); [| prove_cs_preserve_type].
  rewrite !data_at__eq. rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma hc4ab_resp_mresp_out_k sh p :
  @data_at_ CSkresp sh t_mresp p =
  hout sh 32 (hc4ab_resp_fa FH._ephemeral p) * hout sh 16 (hc4ab_resp_fa FH._enc_nothing p) *
  hout sh 32 (hc4ab_resp_fa FH._eph_priv p) * @data_at_ HCS sh t_mstate (hc4ab_resp_fa FH._st p).
Proof.
  rewrite <- hc4ab_resp_mresp_out.
  erewrite (@data_at__change_composite HCS CSkresp _ sh t_mresp); [| prove_cs_preserve_type]. reflexivity.
Qed.

Lemma hc4ab_resp_mresp_eq sh E encn ep ck h p :
  Zlength E = 32 -> Zlength encn = 16 -> Zlength ep = 32 ->
  @data_at HCS sh t_mresp (mresp_val E encn ep ck h) p =
  hbytes sh E (hc4ab_resp_fa FH._ephemeral p) * hbytes sh encn (hc4ab_resp_fa FH._enc_nothing p) *
  hbytes sh ep (hc4ab_resp_fa FH._eph_priv p) * @data_at HCS sh t_mstate (mstate_val ck h) (hc4ab_resp_fa FH._st p).
Proof.
  intros H1 H2 H3.
  erewrite (@data_at_change_composite HCS CSkresp _ sh t_mresp); [| apply JMeq_refl | prove_cs_preserve_type].
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mresp (DOT FH._ephemeral)), (field_at_data_at sh t_mresp (DOT FH._enc_nothing)),
    (field_at_data_at sh t_mresp (DOT FH._eph_priv)), (field_at_data_at sh t_mresp (DOT FH._st)).
  unfold hbytes, hc4ab_resp_fa. rewrite H1, H2, H3. rewrite <- !(@hc4ab_resp_data_at_cs CSkresp HCS).
  erewrite (@data_at_change_composite HCS CSkresp _ sh t_mstate); [| apply JMeq_refl | prove_cs_preserve_type].
  rewrite !sepcon_assoc. reflexivity.
Qed.

(* a failed call (round-4 spec): ephemeral and eph_priv written, enc_nothing not, the state partially mixed *)
Lemma hc4ab_resp_mresp_fail sh E ep ck h p :
  Zlength E = 32 -> Zlength ep = 32 ->
  hbytes sh E (hc4ab_resp_fa FH._ephemeral p) * hout sh 16 (hc4ab_resp_fa FH._enc_nothing p) *
  hbytes sh ep (hc4ab_resp_fa FH._eph_priv p) * @data_at HCS sh t_mstate (mstate_val ck h) (hc4ab_resp_fa FH._st p)
  |-- @data_at HCS sh t_mresp (bytes E, (Zrepeat Vundef 16, (bytes ep, (bytes ck, bytes h)))) p.
Proof.
  intros H1 H3.
  erewrite (@data_at_change_composite HCS CSkresp _ sh t_mresp); [| apply JMeq_refl | prove_cs_preserve_type].
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mresp (DOT FH._ephemeral)), (field_at_data_at sh t_mresp (DOT FH._enc_nothing)),
    (field_at_data_at sh t_mresp (DOT FH._eph_priv)), (field_at_data_at sh t_mresp (DOT FH._st)).
  unfold hbytes, hout, hc4ab_resp_fa. rewrite H1, H3. rewrite <- !(@hc4ab_resp_data_at_cs CSkresp HCS).
  rewrite <- (@hc4ab_resp_data_at__cs CSkresp HCS).
  erewrite (@data_at_change_composite HCS CSkresp _ sh t_mstate); [| apply JMeq_refl | prove_cs_preserve_type].
  rewrite data_at__eq. unfold mstate_val. rewrite !sepcon_assoc. apply derives_refl.
Qed.

Lemma hc4ab_resp_mresp_fc sh p : @data_at_ HCS sh t_mresp p |-- !! @field_compatible CSkresp t_mresp [] p.
Proof.
  erewrite (@data_at__change_composite HCS CSkresp _ sh t_mresp) by prove_cs_preserve_type.
  entailer!.
Qed.

Lemma hc4ab_resp_local32 v : @data_at_ CSkresp Tsh (tarray tuchar 32) v = hout Tsh 32 v.
Proof. unfold hout. apply hc4ab_resp_data_at__cs. Qed.
End RespCS.

Section KsCS.
#[local] Existing Instance CSks.
Lemma hc4ab_resp_local32s v : @data_at_ CSks Tsh (tarray tuchar 32) v = hout Tsh 32 v.
Proof. unfold hout. apply hc4ab_resp_data_at__cs. Qed.
End KsCS.

Ltac hc4ab_resp_fa_tac :=
  unfold hc4ab_resp_fa, hc4ab_resp_fs in *; rewrite ?field_address_offset by auto with field_compatible; reflexivity.

(* the bodies' compspecs: CSkresp for m_create_response, CSks (priority 0, below) for m_consume_response *)
#[local] Existing Instance CSkresp.

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

Lemma hc4a_body_m_create_response_handshake_receive :
  @semax_body (hc3_V_bp WgNoise.harness.x_handshake_receive.code._x_handshake_receive__M_BASEPOINT) (hc3_G_m_create_response x25519 aead_enc) CSkresp WgNoise.harness.x_handshake_receive.code.f_m_create_response (m_create_response_spec x25519 aead_enc WgNoise.harness.x_handshake_receive.code._x_handshake_receive__M_BASEPOINT).
Proof.
start_function.
assert_PROP (field_compatible t_mresp [] o) as FC. { sep_apply (hc4ab_resp_mresp_fc sho o). entailer!. }
assert_PROP (field_compatible t_mstate [] st) as FCs. { sep_apply (hc4ab_resp_mstate_fcr shs (mstate_val CK H) st). entailer!. }
rewrite hc4ab_resp_mresp_out. repeat flatten_sepcon_in_SEP.
assert_PROP (field_compatible t_mstate [] (hc4ab_resp_fa FH._st o)) as FCo.
{ sep_apply (hc4ab_resp_mstate_fc_r sho (hc4ab_resp_fa FH._st o)). entailer!. }
rewrite (hc4ab_resp_mstate_outr sho (hc4ab_resp_fa FH._st o)).
rewrite (hc4ab_resp_mstate_eqr shs CK H st H0 H1). repeat flatten_sepcon_in_SEP.
rewrite !hc4ab_resp_local32.
replace (hout sho 32 (field_address t_mstate (DOT FH._ck) (hc4ab_resp_fa FH._st o))) with (hout sho (Zlength CK) (field_address t_mstate (DOT FH._ck) (hc4ab_resp_fa FH._st o))) by (rewrite H0; reflexivity).
forward_call (sho, field_address t_mstate (DOT FH._ck) (hc4ab_resp_fa FH._st o), shs, field_address t_mstate (DOT FH._ck) st, CK).
{ entailer!. simpl. rewrite H0. hc4ab_resp_fa_tac. }
replace (hout sho 32 (field_address t_mstate (DOT FH._h) (hc4ab_resp_fa FH._st o))) with (hout sho (Zlength H) (field_address t_mstate (DOT FH._h) (hc4ab_resp_fa FH._st o))) by (rewrite H1; reflexivity).
forward_call (sho, field_address t_mstate (DOT FH._h) (hc4ab_resp_fa FH._st o), shs, field_address t_mstate (DOT FH._h) st, H).
{ entailer!. simpl. rewrite H1. hc4ab_resp_fa_tac. }
sep_apply (derives_refl' _ _ (eq_sym (hc4ab_resp_mstate_eqr shs CK H st H0 H1))).
sep_apply (derives_refl' _ _ (eq_sym (hc4ab_resp_mstate_eqr sho CK H (hc4ab_resp_fa FH._st o) H0 H1))).
replace (hout sho 32 (hc4ab_resp_fa FH._eph_priv o)) with (hout sho (Zlength ERAW) (hc4ab_resp_fa FH._eph_priv o)) by (rewrite H5; reflexivity).
forward_call (sho, hc4ab_resp_fa FH._eph_priv o, sh, pe, ERAW).
{ entailer!. simpl. rewrite H5. hc4ab_resp_fa_tac. }
forward_call (sho, hc4ab_resp_fa FH._eph_priv o, ERAW).
{ entailer!. simpl. hc4ab_resp_fa_tac. }
assert (LP: Zlength (clamp ERAW) = 32) by (apply hc4ab_resp_clamp_len; auto).
change (hc_const gv WgNoise.harness.x_handshake_receive.code._x_handshake_receive__M_BASEPOINT basepoint9) with (hbytes Ers basepoint9 (gv WgNoise.harness.x_handshake_receive.code._x_handshake_receive__M_BASEPOINT)).
forward_call (sho, hc4ab_resp_fa FH._ephemeral o, sho, hc4ab_resp_fa FH._eph_priv o, clamp ERAW, Ers, gv WgNoise.harness.x_handshake_receive.code._x_handshake_receive__M_BASEPOINT, basepoint9).
{ entailer!. simpl. hc4ab_resp_fa_tac. }
destruct (dh_ok x25519 (clamp ERAW) basepoint9) eqn:D1.
2:{ forward_if; [| contradiction]. forward. rewrite (hc4ab_resp_cexit1 x25519 aead_enc CK H EI SI PSK ERAW D1).
  rewrite !hc4ab_resp_local32.
  apply andp_right; [apply prop_right; reflexivity |]. Intros. Exists CK H.
  sep_apply (hc4ab_resp_mresp_fail sho _ _ CK H o (X25519 (clamp ERAW) basepoint9) LP).
  unfold hc_const. fold (hbytes Ers basepoint9 (gv WgNoise.harness.x_handshake_receive.code._x_handshake_receive__M_BASEPOINT)). cancel. }
forward_if; [ discriminate | ].
assert (LE: Zlength (x25519 (clamp ERAW) basepoint9) = 32) by apply X25519.
remember (x25519 (clamp ERAW) basepoint9) as E eqn:EE. apply hc4ab_resp_isI in EE.
rewrite <- (hc4ab_resp_hin_ne sho E (hc4ab_resp_fa FH._ephemeral o)) by lia.
forward_call (gv, sho, hc4ab_resp_fa FH._st o, CK, H, sho, hc4ab_resp_fa FH._ephemeral o, E).
{ entailer!. simpl. rewrite LE. hc4ab_resp_fa_tac. }
assert (L1: Zlength (mix_hash H E) = 32) by apply hc4ab_resp_mh_len.
remember (mix_hash H E) as h1 eqn:Eh1. apply hc4ab_resp_isI in Eh1.
forward_call (gv, sho, hc4ab_resp_fa FH._st o, CK, h1, sho, hc4ab_resp_fa FH._ephemeral o, E).
{ entailer!. simpl. rewrite LE. hc4ab_resp_fa_tac. }
assert (LC1: Zlength (kdf1 CK E) = 32) by apply hc4ab_resp_kdf1_len.
remember (kdf1 CK E) as ck1 eqn:Eck1. apply hc4ab_resp_isI in Eck1.
rewrite (hc4ab_resp_hin_ne sho E (hc4ab_resp_fa FH._ephemeral o)) by lia.
forward_call (Tsh, v_dh, sho, hc4ab_resp_fa FH._eph_priv o, clamp ERAW, sh, pi, EI).
{ entailer!. simpl. hc4ab_resp_fa_tac. }
destruct (dh_ok x25519 (clamp ERAW) EI) eqn:D2.
2:{ forward_if; [| contradiction]. forward. rewrite (hc4ab_resp_cexit2 x25519 aead_enc CK H EI SI PSK ERAW D1 D2).
  rewrite !hc4ab_resp_local32.
  apply andp_right; [apply prop_right; reflexivity |]. Intros. Exists ck1 h1.
  sep_apply (hc4ab_resp_mresp_fail sho _ _ ck1 h1 o LE LP).
  sep_apply (hc4ab_resp_hbytes_out' Tsh _ 32 v_dh (X25519 (clamp ERAW) EI)).
  unfold hc_const. fold (hbytes Ers basepoint9 (gv WgNoise.harness.x_handshake_receive.code._x_handshake_receive__M_BASEPOINT)). cancel. }
forward_if; [ discriminate | ].
assert (LD1: Zlength (x25519 (clamp ERAW) EI) = 32) by apply X25519.
remember (x25519 (clamp ERAW) EI) as DH1 eqn:EDH1. apply hc4ab_resp_isI in EDH1.
rewrite <- (hc4ab_resp_hin_ne Tsh DH1 v_dh) by lia.
forward_call (gv, sho, hc4ab_resp_fa FH._st o, ck1, h1, Tsh, v_dh, DH1).
{ entailer!. simpl. rewrite LD1. hc4ab_resp_fa_tac. }
rewrite (hc4ab_resp_hin_ne Tsh DH1 v_dh) by lia.
assert (LC2: Zlength (kdf1 ck1 DH1) = 32) by apply hc4ab_resp_kdf1_len.
remember (kdf1 ck1 DH1) as ck2 eqn:Eck2. apply hc4ab_resp_isI in Eck2.
sep_apply (hc4ab_resp_hbytes_out' Tsh _ 32 v_dh LD1).
forward_call (Tsh, v_dh, sho, hc4ab_resp_fa FH._eph_priv o, clamp ERAW, sh, psi, SI).
{ entailer!. simpl. hc4ab_resp_fa_tac. }
destruct (dh_ok x25519 (clamp ERAW) SI) eqn:D3.
2:{ forward_if; [| contradiction]. forward. rewrite (hc4ab_resp_cexit3 x25519 aead_enc CK H EI SI PSK ERAW D1 D2 D3).
  rewrite !hc4ab_resp_local32.
  apply andp_right; [apply prop_right; reflexivity |]. Intros. Exists ck2 h1.
  sep_apply (hc4ab_resp_mresp_fail sho _ _ ck2 h1 o LE LP).
  sep_apply (hc4ab_resp_hbytes_out' Tsh _ 32 v_dh (X25519 (clamp ERAW) SI)).
  unfold hc_const. fold (hbytes Ers basepoint9 (gv WgNoise.harness.x_handshake_receive.code._x_handshake_receive__M_BASEPOINT)). cancel. }
forward_if; [ discriminate | ].
assert (LD2: Zlength (x25519 (clamp ERAW) SI) = 32) by apply X25519.
remember (x25519 (clamp ERAW) SI) as DH2 eqn:EDH2. apply hc4ab_resp_isI in EDH2.
rewrite <- (hc4ab_resp_hin_ne Tsh DH2 v_dh) by lia.
forward_call (gv, sho, hc4ab_resp_fa FH._st o, ck2, h1, Tsh, v_dh, DH2).
{ entailer!. simpl. rewrite LD2. hc4ab_resp_fa_tac. }
rewrite (hc4ab_resp_hin_ne Tsh DH2 v_dh) by lia.
assert (LC3: Zlength (kdf1 ck2 DH2) = 32) by apply hc4ab_resp_kdf1_len.
remember (kdf1 ck2 DH2) as ck3 eqn:Eck3. apply hc4ab_resp_isI in Eck3.
forward_call (gv, sho, hc4ab_resp_fa FH._st o, ck3, h1, Tsh, v_key, sh, pp, PSK).
{ entailer!. simpl. hc4ab_resp_fa_tac. }
assert (LC4: Zlength (kdf1 ck3 PSK) = 32) by apply hc4ab_resp_kdf1_len.
assert (LK: Zlength (kdf3 ck3 PSK) = 32) by apply hc4ab_resp_kdf3_len.
assert (L2: Zlength (mix_hash h1 (kdf2 ck3 PSK)) = 32) by apply hc4ab_resp_mh_len.
remember (kdf1 ck3 PSK) as ck4 eqn:Eck4. apply hc4ab_resp_isI in Eck4.
remember (kdf3 ck3 PSK) as key eqn:Ekey. apply hc4ab_resp_isI in Ekey.
remember (mix_hash h1 (kdf2 ck3 PSK)) as h2 eqn:Eh2. apply hc4ab_resp_isI in Eh2.
replace (hout sho 16 (hc4ab_resp_fa FH._enc_nothing o)) with (hout sho (Zlength (@nil byte) + 16) (hc4ab_resp_fa FH._enc_nothing o)) by reflexivity.
forward_call (gv, sho, hc4ab_resp_fa FH._st o, ck4, h2, sho, hc4ab_resp_fa FH._enc_nothing o, Ers, gv WgNoise.harness.x_handshake_receive.code._x_handshake_receive__M_BASEPOINT, @nil byte, Tsh, v_key, key).
{ entailer!. simpl. hc4ab_resp_fa_tac. }
{ cancel. }
{ rewrite Zlength_nil. rep_lia. }
try rewrite (hc4ab_resp_hin_nil Ers (gv WgNoise.harness.x_handshake_receive.code._x_handshake_receive__M_BASEPOINT)).
assert (LN: Zlength (aead_enc key 0 h2 []) = 16) by (rewrite (aead_enc_length _ _ AEAD); reflexivity).
remember (aead_enc key 0 h2 []) as encn eqn:Eencn. apply hc4ab_resp_isI in Eencn.
remember (mix_hash h2 encn) as h3 eqn:Eh3. apply hc4ab_resp_isI in Eh3.
forward.
rewrite (hc4ab_resp_csuccess x25519 aead_enc CK H EI SI PSK ERAW E h1 ck1 DH1 ck2 DH2 ck3 ck4 key h2 encn h3
  D1 D2 D3 EE Eh1 Eck1 EDH1 Eck2 EDH2 Eck3 Eck4 Ekey Eh2 Eencn Eh3).
rewrite (hc4ab_resp_mresp_eq sho E encn (clamp ERAW) ck4 h3 o LE LN LP), !hc4ab_resp_local32.
apply andp_right; [apply prop_right; reflexivity |].
sep_apply (hc4ab_resp_hbytes_out' Tsh _ 32 v_dh LD2).
sep_apply (hc4ab_resp_hbytes_out' Tsh _ 32 v_key LK).
unfold hc_const. fold (hbytes Ers basepoint9 (gv WgNoise.harness.x_handshake_receive.code._x_handshake_receive__M_BASEPOINT)). cancel.
Unshelve. all: exact hc4ab_resp_CSkresp_HCS.
Qed.

End Bodies.
