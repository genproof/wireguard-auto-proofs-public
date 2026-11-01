(* law handshake_receive: body proofs of local
   functions of the harness unit (hrx5_spec.v), at the unit's compspecs HRX.  The recording shim S23 and the log readers (rx_reset, rx_only_cookie, rx_authenticated).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Local Open Scope logic.

#[local] Existing Instance HRX.

Lemma hrx5_s23_pfield_valid sh p d :
  readable_share sh -> rx_pfield sh p d |-- valid_pointer p.
Proof.
  intros Hsh. unfold rx_pfield.
  apply field_at_valid_ptr0.
  - apply readable_nonidentity; auto.
  - reflexivity.
  - reflexivity.
Qed.

Ltac hrx5_s23_tt :=
  match goal with H: typed_true _ (if ?b then _ else _) |- _ => destruct b; [clear H | inv H] end.
Ltac hrx5_s23_tf :=
  match goal with H: typed_false _ (if ?b then _ else _) |- _ => destruct b; [inv H | clear H] end.
Ltac hrx5_s23_fin :=
  first [ reflexivity
        | match goal with |- context [Int.eq ?a ?b] => destruct (Int.eq a b); reflexivity end
        | match goal with |- context [rx_other ?x] => destruct (rx_other x); reflexivity end
        | match goal with |- context [Int64.eq ?a ?b] => destruct (Int64.eq a b); reflexivity end ].

Lemma hrx5_body_rx_peer x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_wg_shim_rx_peer
    hrx5_rx_peer_spec.
Proof.
  intros _ _ _.
  start_function.
  unfold rxlog_rep, rxlog_val.
  forward.
  { unfold rx_pfield. destruct H as [H|H]; rewrite H; entailer!. }
  destruct H as [H|H].
  - rewrite H. forward_if.
    + forward. unfold rxlog_rep, rx_note, rxlog_val. rewrite H, if_true by reflexivity.
      cbn [rx_cookie rx_cindex rx_endpoint rx_eskb rx_response rx_session rx_complete rx_keepalive rx_stats rx_len
           rx_received rx_traversal rx_peer rx_other].
      entailer!.
    + contradiction.
  - rewrite H. forward_if.
    { sep_apply (hrx5_s23_pfield_valid sh (rx_peer X) d SH). entailer!. }
    + forward. unfold rxlog_rep, rx_note, rxlog_val. rewrite H, H0, if_true by reflexivity.
      cbn [rx_cookie rx_cindex rx_endpoint rx_eskb rx_response rx_session rx_complete rx_keepalive rx_stats rx_len
           rx_received rx_traversal rx_peer rx_other].
      entailer!.
    + forward. forward_if.
      { sep_apply (hrx5_s23_pfield_valid sh (rx_peer X) d SH). entailer!. }
      * contradiction.
      * forward. unfold rxlog_rep, rx_note. rewrite H, if_false by auto. rewrite if_true by auto. entailer!.
Qed.

#[local] Instance hrx5_s23_cce1 : change_composite_env HRX Cookie.CS.
Proof. make_cs_preserve HRX Cookie.CS. Defined.

Lemma hrx5_body_send_cookie x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_wg_packet_send_handshake_cookie
    (hrx5_send_cookie_spec xaead_enc).
Proof.
  intros _ _ _.
  start_function.
  change (data_at_ Tsh (Tstruct HRC._message_handshake_cookie noattr) v_packet)
    with (@data_at_ HRX Tsh t_cmsg v_packet).
  rewrite (@data_at__change_composite HRX Cookie.CS hrx5_s23_cce1 Tsh t_cmsg) by reflexivity.
  forward_call (gv, S, w, Tsh, v_packet, shs, sp, s, shm, msg, idx, shc, cc_addr wg, CC).
  { destruct H1; auto. }
  Intros vret. unfold rxlog_rep, rxlog_val. forward. forward. forward.
  unfold cmsg_rep. Intros. sep_apply (@data_at_data_at_ Cookie.CS).
  rewrite <- (@data_at__change_composite HRX Cookie.CS hrx5_s23_cce1 Tsh t_cmsg) by reflexivity.
  Exists (fst vret) (snd vret). unfold rx_send_cookie.
  cbn [rx_cookie rx_cindex rx_endpoint rx_eskb rx_response rx_session rx_complete rx_keepalive rx_stats rx_len
       rx_received rx_traversal rx_peer rx_other].
  entailer!.
Qed.

Lemma hrx5_body_set_endpoint x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_wg_socket_set_peer_endpoint_from_skb
    hrx5_set_endpoint_spec.
Proof.
  intros _ _ _.
  start_function.
  unfold rxlog_rep, rxlog_val.
  forward. forward. forward.
  forward_call (gv, mkRx (rx_cookie X) (rx_cindex X) (inc (rx_endpoint X)) sk (rx_response X) (rx_session X)
                (rx_complete X) (rx_keepalive X) (rx_stats X) (rx_len X) (rx_received X) (rx_traversal X)
                (rx_peer X) (rx_other X), p, sh, d).
  unfold rx_set_endpoint. entailer!.
Qed.

Lemma hrx5_body_send_response x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_wg_packet_send_handshake_response
    hrx5_send_response_spec.
Proof.
  intros _ _ _.
  start_function.
  unfold rxlog_rep, rxlog_val.
  forward. forward.
  forward_call (gv, mkRx (rx_cookie X) (rx_cindex X) (rx_endpoint X) (rx_eskb X) (inc (rx_response X)) (rx_session X) (rx_complete X) (rx_keepalive X) (rx_stats X) (rx_len X) (rx_received X) (rx_traversal X) (rx_peer X) (rx_other X), p, sh, d).
  unfold rx_send_response. entailer!.
Qed.

Lemma hrx5_body_session_derived x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_wg_timers_session_derived
    hrx5_session_derived_spec.
Proof.
  intros _ _ _.
  start_function.
  unfold rxlog_rep, rxlog_val.
  forward. forward.
  forward_call (gv, mkRx (rx_cookie X) (rx_cindex X) (rx_endpoint X) (rx_eskb X) (rx_response X) (inc (rx_session X)) (rx_complete X) (rx_keepalive X) (rx_stats X) (rx_len X) (rx_received X) (rx_traversal X) (rx_peer X) (rx_other X), p, sh, d).
  unfold rx_session_derived. entailer!.
Qed.

Lemma hrx5_body_handshake_complete x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_wg_timers_handshake_complete
    hrx5_handshake_complete_spec.
Proof.
  intros _ _ _.
  start_function.
  unfold rxlog_rep, rxlog_val.
  forward. forward.
  forward_call (gv, mkRx (rx_cookie X) (rx_cindex X) (rx_endpoint X) (rx_eskb X) (rx_response X) (rx_session X) (inc (rx_complete X)) (rx_keepalive X) (rx_stats X) (rx_len X) (rx_received X) (rx_traversal X) (rx_peer X) (rx_other X), p, sh, d).
  unfold rx_handshake_complete. entailer!.
Qed.

Lemma hrx5_body_send_keepalive x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_wg_packet_send_keepalive
    hrx5_send_keepalive_spec.
Proof.
  intros _ _ _.
  start_function.
  unfold rxlog_rep, rxlog_val.
  forward. forward.
  forward_call (gv, mkRx (rx_cookie X) (rx_cindex X) (rx_endpoint X) (rx_eskb X) (rx_response X) (rx_session X) (rx_complete X) (inc (rx_keepalive X)) (rx_stats X) (rx_len X) (rx_received X) (rx_traversal X) (rx_peer X) (rx_other X), p, sh, d).
  unfold rx_send_keepalive. entailer!.
Qed.

Lemma hrx5_body_auth_received x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_wg_timers_any_authenticated_packet_received
    hrx5_auth_received_spec.
Proof.
  intros _ _ _.
  start_function.
  unfold rxlog_rep, rxlog_val.
  forward. forward.
  forward_call (gv, mkRx (rx_cookie X) (rx_cindex X) (rx_endpoint X) (rx_eskb X) (rx_response X) (rx_session X) (rx_complete X) (rx_keepalive X) (rx_stats X) (rx_len X) (inc (rx_received X)) (rx_traversal X) (rx_peer X) (rx_other X), p, sh, d).
  unfold rx_auth_received. entailer!.
Qed.

Lemma hrx5_body_auth_traversal x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_wg_timers_any_authenticated_packet_traversal
    hrx5_auth_traversal_spec.
Proof.
  intros _ _ _.
  start_function.
  unfold rxlog_rep, rxlog_val.
  forward. forward.
  forward_call (gv, mkRx (rx_cookie X) (rx_cindex X) (rx_endpoint X) (rx_eskb X) (rx_response X) (rx_session X) (rx_complete X) (rx_keepalive X) (rx_stats X) (rx_len X) (rx_received X) (inc (rx_traversal X)) (rx_peer X) (rx_other X), p, sh, d).
  unfold rx_auth_traversal. entailer!.
Qed.

Lemma hrx5_body_update_rx_stats x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_update_rx_stats
    hrx5_update_rx_stats_spec.
Proof.
  intros _ _ _.
  start_function.
  unfold rxlog_rep, rxlog_val.
  forward. forward. forward.
  forward_call (gv, mkRx (rx_cookie X) (rx_cindex X) (rx_endpoint X) (rx_eskb X) (rx_response X) (rx_session X) (rx_complete X) (rx_keepalive X) (inc (rx_stats X)) len (rx_received X) (rx_traversal X) (rx_peer X) (rx_other X), p, sh, d).
  unfold rx_update_stats. entailer!.
Qed.

Lemma hrx5_body_rx_reset x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_rx_reset
    hrx5_rx_reset_spec.
Proof.
  intros _ _ _.
  start_function.
  repeat forward.
  unfold rxlog_rep, rxlog_val, rx0. cbn [rx_cookie rx_cindex rx_endpoint rx_eskb rx_response rx_session rx_complete
    rx_keepalive rx_stats rx_len rx_received rx_traversal rx_peer rx_other].
  entailer!.
Qed.

Lemma hrx5_body_rx_only_cookie x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_rx_only_cookie
    hrx5_rx_only_cookie_spec.
Proof.
  intros _ _ _.
  start_function.
  unfold rxlog_rep, rxlog_val.
  rewrite H.
  forward.
  forward_if (temp HRC._t'1 (Val.of_bool (Int.eq (rx_cookie X) c && Int.eq (rx_endpoint X) Int.zero))).
  { forward. forward. rewrite H0, Int.eq_true. cbn [andb]. entailer!. destruct (Int.eq _ _); reflexivity. }
  { forward. rewrite Int.eq_false by auto. entailer!. }
  forward_if (temp HRC._t'2 (Val.of_bool (Int.eq (rx_cookie X) c && Int.eq (rx_endpoint X) Int.zero && Int.eq (rx_response X) Int.zero))).
  { change Int.zero with (Int.repr 0) in *. hrx5_s23_tt. forward. forward. cbn [andb]. entailer!; hrx5_s23_fin. }
  { change Int.zero with (Int.repr 0) in *. hrx5_s23_tf. forward. cbn [andb]. entailer!. }
  forward_if (temp HRC._t'3 (Val.of_bool (Int.eq (rx_cookie X) c && Int.eq (rx_endpoint X) Int.zero && Int.eq (rx_response X) Int.zero && Int.eq (rx_session X) Int.zero))).
  { change Int.zero with (Int.repr 0) in *. hrx5_s23_tt. forward. forward. cbn [andb]. entailer!; hrx5_s23_fin. }
  { change Int.zero with (Int.repr 0) in *. hrx5_s23_tf. forward. cbn [andb]. entailer!. }
  forward_if (temp HRC._t'4 (Val.of_bool (Int.eq (rx_cookie X) c && Int.eq (rx_endpoint X) Int.zero && Int.eq (rx_response X) Int.zero && Int.eq (rx_session X) Int.zero && Int.eq (rx_complete X) Int.zero))).
  { change Int.zero with (Int.repr 0) in *. hrx5_s23_tt. forward. forward. cbn [andb]. entailer!; hrx5_s23_fin. }
  { change Int.zero with (Int.repr 0) in *. hrx5_s23_tf. forward. cbn [andb]. entailer!. }
  forward_if (temp HRC._t'5 (Val.of_bool (Int.eq (rx_cookie X) c && Int.eq (rx_endpoint X) Int.zero && Int.eq (rx_response X) Int.zero && Int.eq (rx_session X) Int.zero && Int.eq (rx_complete X) Int.zero && Int.eq (rx_keepalive X) Int.zero))).
  { change Int.zero with (Int.repr 0) in *. hrx5_s23_tt. forward. forward. cbn [andb]. entailer!; hrx5_s23_fin. }
  { change Int.zero with (Int.repr 0) in *. hrx5_s23_tf. forward. cbn [andb]. entailer!. }
  forward_if (temp HRC._t'6 (Val.of_bool (Int.eq (rx_cookie X) c && Int.eq (rx_endpoint X) Int.zero && Int.eq (rx_response X) Int.zero && Int.eq (rx_session X) Int.zero && Int.eq (rx_complete X) Int.zero && Int.eq (rx_keepalive X) Int.zero && Int.eq (rx_stats X) Int.zero))).
  { change Int.zero with (Int.repr 0) in *. hrx5_s23_tt. forward. forward. cbn [andb]. entailer!; hrx5_s23_fin. }
  { change Int.zero with (Int.repr 0) in *. hrx5_s23_tf. forward. cbn [andb]. entailer!. }
  forward_if (temp HRC._t'7 (Val.of_bool (Int.eq (rx_cookie X) c && Int.eq (rx_endpoint X) Int.zero && Int.eq (rx_response X) Int.zero && Int.eq (rx_session X) Int.zero && Int.eq (rx_complete X) Int.zero && Int.eq (rx_keepalive X) Int.zero && Int.eq (rx_stats X) Int.zero && Int.eq (rx_received X) Int.zero))).
  { change Int.zero with (Int.repr 0) in *. hrx5_s23_tt. forward. forward. cbn [andb]. entailer!; hrx5_s23_fin. }
  { change Int.zero with (Int.repr 0) in *. hrx5_s23_tf. forward. cbn [andb]. entailer!. }
  forward_if (temp HRC._t'8 (Val.of_bool (Int.eq (rx_cookie X) c && Int.eq (rx_endpoint X) Int.zero && Int.eq (rx_response X) Int.zero && Int.eq (rx_session X) Int.zero && Int.eq (rx_complete X) Int.zero && Int.eq (rx_keepalive X) Int.zero && Int.eq (rx_stats X) Int.zero && Int.eq (rx_received X) Int.zero && Int.eq (rx_traversal X) Int.zero))).
  { change Int.zero with (Int.repr 0) in *. hrx5_s23_tt. forward. forward. cbn [andb]. entailer!; hrx5_s23_fin. }
  { change Int.zero with (Int.repr 0) in *. hrx5_s23_tf. forward. cbn [andb]. entailer!. }
  forward_if (temp HRC._t'9 (Val.of_bool (Int.eq (rx_cookie X) c && Int.eq (rx_endpoint X) Int.zero && Int.eq (rx_response X) Int.zero && Int.eq (rx_session X) Int.zero && Int.eq (rx_complete X) Int.zero && Int.eq (rx_keepalive X) Int.zero && Int.eq (rx_stats X) Int.zero && Int.eq (rx_received X) Int.zero && Int.eq (rx_traversal X) Int.zero && true))).
  { change Int.zero with (Int.repr 0) in *. hrx5_s23_tt. forward. forward. cbn [andb]. entailer!; hrx5_s23_fin. }
  { change Int.zero with (Int.repr 0) in *. hrx5_s23_tf. forward. cbn [andb]. entailer!. }
  forward_if (temp HRC._t'10 (Val.of_bool (Int.eq (rx_cookie X) c && Int.eq (rx_endpoint X) Int.zero && Int.eq (rx_response X) Int.zero && Int.eq (rx_session X) Int.zero && Int.eq (rx_complete X) Int.zero && Int.eq (rx_keepalive X) Int.zero && Int.eq (rx_stats X) Int.zero && Int.eq (rx_received X) Int.zero && Int.eq (rx_traversal X) Int.zero && true && negb (rx_other X)))).
  { change Int.zero with (Int.repr 0) in *. hrx5_s23_tt. forward.
    { entailer!. destruct (rx_other X); simpl; auto. }
    destruct (rx_other X); forward; entailer!. }
  { change Int.zero with (Int.repr 0) in *. hrx5_s23_tf. forward. cbn [andb]. entailer!. }
  deadvars!.
  apply semax_pre with (PROP () LOCAL (temp HRC._t'10 (Vint (if rx_only_cookie_b X c then Int.one else Int.zero));
    gvars gv) SEP (rxlog_rep gv X)).
  { unfold rx_only_cookie_b. rewrite H, if_true by auto. unfold rxlog_rep, rxlog_val. rewrite H. entailer!.
    match goal with |- Vint (if ?b then _ else _) = _ => destruct b; reflexivity end. }
  forward.
Qed.

Definition hrx5_s23_peq (a b: val) : bool := if eq_dec a b then true else false.
Arguments hrx5_s23_peq : simpl never.
Lemma hrx5_s23_peq_r a : hrx5_s23_peq a a = true.
Proof. unfold hrx5_s23_peq. rewrite if_true; auto. Qed.
Lemma hrx5_s23_peq_n b o : hrx5_s23_peq nullval (Vptr b o) = false.
Proof. unfold hrx5_s23_peq. rewrite if_false; auto. discriminate. Qed.

Lemma hrx5_s23_ob (b: bool) : Vint (if b then Int.one else Int.zero) = Val.of_bool b.
Proof. destruct b; reflexivity. Qed.

#[local] Instance hrx5_s23_cce2 : change_composite_env Cookie.CS HRX.
Proof. make_cs_preserve Cookie.CS HRX. Defined.

Lemma hrx5_body_rx_authenticated x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_rx_authenticated
    hrx5_rx_authenticated_spec.
Proof.
  intros _ _ _.
  start_function.
  unfold skb_rep. Intros.
  erewrite (@data_at_change_composite Cookie.CS HRX hrx5_s23_cce2 shs t_skb _ _ (JMeq_refl _)) by reflexivity.
  assert_PROP (@field_compatible HRX t_skb [] sp) as FCsp by entailer!.
  assert_PROP (@field_compatible Noise.CS t_peer [StructField I._device] p) as FCp by (unfold rx_pfield; entailer!).
  destruct sp as [| | | | | bs os]; try (destruct FCsp; contradiction).
  destruct p as [| | | | | bp op]; try (destruct FCp; contradiction).
  unfold rxlog_rep, rxlog_val.
  forward.
  forward_if (temp HRC._t'1 (Val.of_bool (Int.eq (rx_cookie X) (Int.repr 0) && Int.eq (rx_endpoint X) (Int.repr 1)))).
  { forward. forward. match goal with E: rx_cookie X = _ |- _ => rewrite E, Int.eq_true end. cbn [andb].
    entailer!; hrx5_s23_fin. }
  { forward. rewrite Int.eq_false by auto. entailer!. }
  forward_if (temp HRC._t'2 (Val.of_bool (Int.eq (rx_cookie X) (Int.repr 0) && Int.eq (rx_endpoint X) (Int.repr 1) && hrx5_s23_peq (rx_eskb X) (Vptr bs os)))).
  { hrx5_s23_tt. destruct H0 as [E|E]; rewrite E.
    - forward. forward. cbn [andb]. entailer!.
      + rewrite E, hrx5_s23_peq_n. reflexivity.
      + rewrite E. cancel.
    - forward. forward. rewrite E, hrx5_s23_peq_r. cbn [andb]. entailer!.
      simpl. destruct (EqDec_block bs bs) as [e|n];
        [destruct (EqDec_ptr os os) as [e'|n']; [reflexivity|congruence]|congruence]. }
  { hrx5_s23_tf. forward. cbn [andb]. entailer!. }
  forward_if (temp HRC._t'3 (Val.of_bool (Int.eq (rx_cookie X) (Int.repr 0) && Int.eq (rx_endpoint X) (Int.repr 1) && hrx5_s23_peq (rx_eskb X) (Vptr bs os) && Int.eq (rx_response X) resp))).
  { hrx5_s23_tt. forward. forward. cbn [andb]. entailer!; hrx5_s23_fin. }
  { hrx5_s23_tf. forward. cbn [andb]. entailer!. }
  forward_if (temp HRC._t'4 (Val.of_bool (Int.eq (rx_cookie X) (Int.repr 0) && Int.eq (rx_endpoint X) (Int.repr 1) && hrx5_s23_peq (rx_eskb X) (Vptr bs os) && Int.eq (rx_response X) resp && Int.eq (rx_session X) sess))).
  { hrx5_s23_tt. forward. forward. cbn [andb]. entailer!; hrx5_s23_fin. }
  { hrx5_s23_tf. forward. cbn [andb]. entailer!. }
  forward_if (temp HRC._t'5 (Val.of_bool (Int.eq (rx_cookie X) (Int.repr 0) && Int.eq (rx_endpoint X) (Int.repr 1) && hrx5_s23_peq (rx_eskb X) (Vptr bs os) && Int.eq (rx_response X) resp && Int.eq (rx_session X) sess && Int.eq (rx_complete X) sess))).
  { hrx5_s23_tt. forward. forward. cbn [andb]. entailer!; hrx5_s23_fin. }
  { hrx5_s23_tf. forward. cbn [andb]. entailer!. }
  forward_if (temp HRC._t'6 (Val.of_bool (Int.eq (rx_cookie X) (Int.repr 0) && Int.eq (rx_endpoint X) (Int.repr 1) && hrx5_s23_peq (rx_eskb X) (Vptr bs os) && Int.eq (rx_response X) resp && Int.eq (rx_session X) sess && Int.eq (rx_complete X) sess && Int.eq (rx_keepalive X) sess))).
  { hrx5_s23_tt. forward. forward. cbn [andb]. entailer!; hrx5_s23_fin. }
  { hrx5_s23_tf. forward. cbn [andb]. entailer!. }
  forward_if (temp HRC._t'7 (Val.of_bool (Int.eq (rx_cookie X) (Int.repr 0) && Int.eq (rx_endpoint X) (Int.repr 1) && hrx5_s23_peq (rx_eskb X) (Vptr bs os) && Int.eq (rx_response X) resp && Int.eq (rx_session X) sess && Int.eq (rx_complete X) sess && Int.eq (rx_keepalive X) sess && Int.eq (rx_stats X) (Int.repr 1)))).
  { hrx5_s23_tt. forward. forward. cbn [andb]. entailer!; hrx5_s23_fin. }
  { hrx5_s23_tf. forward. cbn [andb]. entailer!. }
  forward_if (temp HRC._t'8 (Val.of_bool (Int.eq (rx_cookie X) (Int.repr 0) && Int.eq (rx_endpoint X) (Int.repr 1) && hrx5_s23_peq (rx_eskb X) (Vptr bs os) && Int.eq (rx_response X) resp && Int.eq (rx_session X) sess && Int.eq (rx_complete X) sess && Int.eq (rx_keepalive X) sess && Int.eq (rx_stats X) (Int.repr 1) && Int64.eq (rx_len X) (Int64.repr (Int.unsigned (sk_len s)))))).
  { hrx5_s23_tt. forward. forward. forward. cbn [andb]. entailer!; change (Int64.cmpu Ceq) with Int64.eq; hrx5_s23_fin. }
  { hrx5_s23_tf. forward. cbn [andb]. entailer!. }
  forward_if (temp HRC._t'9 (Val.of_bool (Int.eq (rx_cookie X) (Int.repr 0) && Int.eq (rx_endpoint X) (Int.repr 1) && hrx5_s23_peq (rx_eskb X) (Vptr bs os) && Int.eq (rx_response X) resp && Int.eq (rx_session X) sess && Int.eq (rx_complete X) sess && Int.eq (rx_keepalive X) sess && Int.eq (rx_stats X) (Int.repr 1) && Int64.eq (rx_len X) (Int64.repr (Int.unsigned (sk_len s))) && Int.eq (rx_received X) (Int.repr 1)))).
  { hrx5_s23_tt. forward. forward. cbn [andb]. entailer!; hrx5_s23_fin. }
  { hrx5_s23_tf. forward. cbn [andb]. entailer!. }
  forward_if (temp HRC._t'10 (Val.of_bool (Int.eq (rx_cookie X) (Int.repr 0) && Int.eq (rx_endpoint X) (Int.repr 1) && hrx5_s23_peq (rx_eskb X) (Vptr bs os) && Int.eq (rx_response X) resp && Int.eq (rx_session X) sess && Int.eq (rx_complete X) sess && Int.eq (rx_keepalive X) sess && Int.eq (rx_stats X) (Int.repr 1) && Int64.eq (rx_len X) (Int64.repr (Int.unsigned (sk_len s))) && Int.eq (rx_received X) (Int.repr 1) && Int.eq (rx_traversal X) (Int.repr 1)))).
  { hrx5_s23_tt. forward. forward. cbn [andb]. entailer!; hrx5_s23_fin. }
  { hrx5_s23_tf. forward. cbn [andb]. entailer!. }
  forward_if (temp HRC._t'11 (Val.of_bool (Int.eq (rx_cookie X) (Int.repr 0) && Int.eq (rx_endpoint X) (Int.repr 1) && hrx5_s23_peq (rx_eskb X) (Vptr bs os) && Int.eq (rx_response X) resp && Int.eq (rx_session X) sess && Int.eq (rx_complete X) sess && Int.eq (rx_keepalive X) sess && Int.eq (rx_stats X) (Int.repr 1) && Int64.eq (rx_len X) (Int64.repr (Int.unsigned (sk_len s))) && Int.eq (rx_received X) (Int.repr 1) && Int.eq (rx_traversal X) (Int.repr 1) && hrx5_s23_peq (rx_peer X) (Vptr bp op)))).
  { hrx5_s23_tt. destruct H as [E|E]; rewrite E.
    - forward. forward.
      { go_lower. apply denote_tc_test_eq_split; [apply valid_pointer_null |].
        rewrite sepcon_comm, sepcon_assoc. apply sepcon_valid_pointer1, hrx5_s23_pfield_valid; auto. }
      rewrite E, hrx5_s23_peq_n. entailer!.
    - forward. forward.
      { go_lower. apply denote_tc_test_eq_split;
          rewrite sepcon_comm, sepcon_assoc; apply sepcon_valid_pointer1, hrx5_s23_pfield_valid; auto. }
      rewrite E, hrx5_s23_peq_r. cbn [andb]. entailer!.
      simpl. destruct (EqDec_block bp bp) as [e|n];
        [destruct (EqDec_ptr op op) as [e'|n']; [reflexivity|congruence]|congruence]. }
  { hrx5_s23_tf. forward. cbn [andb]. entailer!. }
  forward_if (temp HRC._t'12 (Val.of_bool (Int.eq (rx_cookie X) (Int.repr 0) && Int.eq (rx_endpoint X) (Int.repr 1) && hrx5_s23_peq (rx_eskb X) (Vptr bs os) && Int.eq (rx_response X) resp && Int.eq (rx_session X) sess && Int.eq (rx_complete X) sess && Int.eq (rx_keepalive X) sess && Int.eq (rx_stats X) (Int.repr 1) && Int64.eq (rx_len X) (Int64.repr (Int.unsigned (sk_len s))) && Int.eq (rx_received X) (Int.repr 1) && Int.eq (rx_traversal X) (Int.repr 1) && hrx5_s23_peq (rx_peer X) (Vptr bp op) && negb (rx_other X)))).
  { hrx5_s23_tt. forward.
    { entailer!. destruct (rx_other X); simpl; auto. }
    destruct (rx_other X); forward; entailer!. }
  { hrx5_s23_tf. forward. cbn [andb]. entailer!. }
  deadvars!.
  apply semax_pre with (PROP () LOCAL (temp HRC._t'12
      (Vint (if rx_authenticated_b X (Vptr bp op) (Vptr bs os) (sk_len s) resp sess then Int.one else Int.zero));
    gvars gv) SEP (rxlog_rep gv X; rx_pfield sh (Vptr bp op) d; skb_rep shs (Vptr bs os) s)).
  { unfold rx_authenticated_b, rxlog_rep, rxlog_val, skb_rep, hrx5_s23_peq.
    rewrite <- (@data_at_change_composite Cookie.CS HRX hrx5_s23_cce2 shs t_skb (skb_val s) (skb_val s) (JMeq_refl _))
      by reflexivity.
    entailer!.
    apply hrx5_s23_ob. }
  forward.
Qed.

(* the conjunction of this file's body lemmas *)
Definition hrx5_bodies_s23 : Prop :=
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_wg_shim_rx_peer hrx5_rx_peer_spec) /\
  (@semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_wg_packet_send_handshake_cookie (hrx5_send_cookie_spec xaead_enc)) /\
  (@semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_wg_socket_set_peer_endpoint_from_skb hrx5_set_endpoint_spec) /\
  (@semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_wg_packet_send_handshake_response hrx5_send_response_spec) /\
  (@semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_wg_timers_session_derived hrx5_session_derived_spec) /\
  (@semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_wg_timers_handshake_complete hrx5_handshake_complete_spec) /\
  (@semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_wg_packet_send_keepalive hrx5_send_keepalive_spec) /\
  (@semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_wg_timers_any_authenticated_packet_received hrx5_auth_received_spec) /\
  (@semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_wg_timers_any_authenticated_packet_traversal hrx5_auth_traversal_spec) /\
  (@semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_update_rx_stats hrx5_update_rx_stats_spec) /\
  (@semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_rx_reset hrx5_rx_reset_spec) /\
  (@semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_rx_only_cookie hrx5_rx_only_cookie_spec) /\
  (@semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_rx_authenticated hrx5_rx_authenticated_spec).

Theorem hrx5_grp_s23 : hrx5_bodies_s23.
Proof.
  intros x25519 aead_enc aead_dec xaead_enc xaead_dec CSw H1 H2 H3.
  exact (conj (hrx5_body_rx_peer _ _ _ _ _ _ H1 H2 H3)
    (conj (hrx5_body_send_cookie _ _ _ _ _ _ H1 H2 H3)
    (conj (hrx5_body_set_endpoint _ _ _ _ _ _ H1 H2 H3)
    (conj (hrx5_body_send_response _ _ _ _ _ _ H1 H2 H3)
    (conj (hrx5_body_session_derived _ _ _ _ _ _ H1 H2 H3)
    (conj (hrx5_body_handshake_complete _ _ _ _ _ _ H1 H2 H3)
    (conj (hrx5_body_send_keepalive _ _ _ _ _ _ H1 H2 H3)
    (conj (hrx5_body_auth_received _ _ _ _ _ _ H1 H2 H3)
    (conj (hrx5_body_auth_traversal _ _ _ _ _ _ H1 H2 H3)
    (conj (hrx5_body_update_rx_stats _ _ _ _ _ _ H1 H2 H3)
    (conj (hrx5_body_rx_reset _ _ _ _ _ _ H1 H2 H3)
    (conj (hrx5_body_rx_only_cookie _ _ _ _ _ _ H1 H2 H3)
    (hrx5_body_rx_authenticated _ _ _ _ _ _ H1 H2 H3))))))))))))).
Qed.
