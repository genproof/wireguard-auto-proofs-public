(* hc_pieces3, group ident: common.h bodies, proved once at a small compspecs with the callee context
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
Require Import WgNoise.proof.libc.libc_bytes.

Module FH := WgNoise.harness.x_handshake.code.
Module FK := WgNoise.harness.x_cookie_reply.code.
Module FR := WgNoise.harness.x_consume_response_any.code.

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

#[local] Existing Instance CSki.
#[local] Instance hc3b_ident_HCS_CSki : change_composite_env HCS CSki.
Proof. make_cs_preserve HCS CSki. Defined.

Local Open Scope logic.

Lemma hc3b_ident_mident_eq sh I p :
  Zlength (mi_priv I) = 32 -> Zlength (mi_pub I) = 32 ->
  @data_at HCS sh t_mident (mident_val I) p =
  hbytes sh (mi_priv I) (@field_address CSki t_mident (DOT FH._priv) p) *
  hbytes sh (mi_pub I) (@field_address CSki t_mident (DOT FH._pub) p) *
  @field_at CSki sh t_mident (DOT FH._ok) (Vint (if mi_ok I then Int.one else Int.zero)) p.
Proof.
  intros H1 H2.
  erewrite (@data_at_change_composite HCS CSki _ sh t_mident); [| apply JMeq_refl | prove_cs_preserve_type].
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mident (DOT FH._priv)), (field_at_data_at sh t_mident (DOT FH._pub)).
  unfold hbytes. rewrite H1, H2.
  rewrite <- !(@data_at_tarray_tuchar_cs CSki HCS).
  rewrite sepcon_assoc. reflexivity.
Qed.

Lemma hc3b_ident_mident_out sh p :
  @data_at_ HCS sh t_mident p =
  hout sh 32 (@field_address CSki t_mident (DOT FH._priv) p) *
  hout sh 32 (@field_address CSki t_mident (DOT FH._pub) p) *
  @field_at_ CSki sh t_mident (DOT FH._ok) p.
Proof.
  erewrite (@data_at__change_composite HCS CSki _ sh t_mident); [| prove_cs_preserve_type].
  rewrite data_at__eq. unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mident (DOT FH._priv)), (field_at_data_at sh t_mident (DOT FH._pub)).
  unfold hout. rewrite <- !(@data_at__tarray_tuchar_cs CSki HCS).
  unfold field_at_. rewrite sepcon_assoc. reflexivity.
Qed.

Ltac hc3b_ident_priv_len :=
  match goal with Hv: value_fits t_mident _ |- _ =>
    rewrite value_fits_eq in Hv; simpl in Hv; destruct Hv as [Hv _];
    rewrite value_fits_eq in Hv; simpl in Hv; destruct Hv as [Hv _];
    unfold bytes in Hv; rewrite <- (Zlength_map _ _ Vubyte); exact Hv end.

Ltac hc3b_ident_pub_len :=
  match goal with Hv: value_fits t_mident _ |- _ =>
    rewrite value_fits_eq in Hv; simpl in Hv; destruct Hv as [_ [Hv _]];
    rewrite value_fits_eq in Hv; simpl in Hv; destruct Hv as [Hv _];
    unfold bytes in Hv; rewrite <- (Zlength_map _ _ Vubyte); exact Hv end.

Lemma hc3b_ident_if_out sh p (b: bool) bs :
  Zlength bs = 32 -> (if b then hbytes sh bs p else hout sh 32 p) |-- hout sh 32 p.
Proof.
  intros Hl. destruct b; [|apply derives_refl].
  unfold hbytes, hout. rewrite Hl. apply data_at_data_at_.
Qed.

Lemma hc3b_ident_clamp_len raw : Zlength raw = 32 -> Zlength (clamp raw) = 32.
Proof. intros. unfold clamp. list_solve. Qed.

Lemma hc3b_ident_fc_root {cs: compspecs} t gf gfs p :
  field_compatible t (gf :: gfs) p -> field_compatible t [] p.
Proof. intros (?&?&?&?&?). repeat split; auto. Qed.

Ltac hc3b_ident_fa :=
  match goal with Hf: field_compatible t_mident (_ :: _) ?p |- _ =>
    let Hr := fresh "Hr" in pose proof (hc3b_ident_fc_root _ _ _ _ Hf) as Hr end;
  rewrite ?field_address_offset by auto with field_compatible; reflexivity.

Lemma hc3b_ident_is_zero a : Zlength a = 32 -> is_zero a = negb (memneq_bool a zeros32).
Proof.
  intros H. unfold is_zero, bytes_eqb, memneq_bool, zeros, zeros32. rewrite H.
  destruct (list_eq_dec Byte.eq_dec a (Zrepeat Byte.zero 32)); reflexivity.
Qed.

Lemma hc3_body_m_identity_of_create_any :
  @semax_body (hc3_V_bp WgNoise.harness.x_create_any.code._x_create_any__M_BASEPOINT) (hc3_G_m_identity_of x25519) CSki WgNoise.harness.x_create_any.code.f_m_identity_of (m_identity_of_spec x25519 WgNoise.harness.x_create_any.code._x_create_any__M_BASEPOINT).
Proof.
  start_function.
  rewrite hc3b_ident_mident_out. flatten_sepcon_in_SEP. flatten_sepcon_in_SEP.
  assert_PROP (field_compatible t_mident [] d) as FC.
  { entailer!. eapply hc3b_ident_fc_root; eauto. }
  assert (field_compatible t_mident (DOT FH._priv) d) as FCp by auto with field_compatible.
  assert (field_compatible t_mident (DOT FH._pub) d) as FCq by auto with field_compatible.
  forward_call (sh, field_address t_mident (DOT FH._priv) d, shr, r, RAW).
  { entailer!. simpl. rewrite H. hc3b_ident_fa. }
  { rewrite H. cancel. }
  forward_call (sh, field_address t_mident (DOT FH._priv) d, RAW).
  { entailer!. simpl. hc3b_ident_fa. }
  unfold hc_const.
  forward_call (sh, field_address t_mident (DOT FH._pub) d, shr, r, RAW, Ers, gv WgNoise.harness.x_create_any.code._x_create_any__M_BASEPOINT, basepoint9).
  forward_call (shr, r, RAW).
  { apply prop_right; simpl; rewrite H; reflexivity. }
  forward_if (PROP () LOCAL (temp WgNoise.harness.x_create_any.code._t'3 (Val.of_bool (memneq_bool RAW zeros32 && dh_ok x25519 RAW basepoint9)%bool); gvars gv; temp WgNoise.harness.x_create_any.code._id d) SEP (hbytes sh (x25519 RAW basepoint9) (field_address t_mident (DOT FH._pub) d); hbytes shr RAW r; hbytes Ers basepoint9 (gv WgNoise.harness.x_create_any.code._x_create_any__M_BASEPOINT); hbytes sh (clamp RAW) (field_address t_mident (DOT FH._priv) d); field_at_ sh t_mident (DOT FH._ok) d)).
  - forward. entailer!. rewrite hc3b_ident_is_zero in H0 by auto.
    destruct (memneq_bool RAW zeros32); simpl in H0; [|apply Int.one_not_zero in H0; contradiction].
    destruct (dh_ok x25519 RAW basepoint9); reflexivity.
  - forward. entailer!. rewrite hc3b_ident_is_zero in H0 by auto.
    destruct (memneq_bool RAW zeros32); simpl in H0; [contradiction H0; reflexivity|]. reflexivity.
  - forward. entailer!.
    rewrite (hc3b_ident_mident_eq sh (mident_of x25519 RAW) d) by (simpl; auto using hc3b_ident_clamp_len).
    unfold hc_const, mident_of, dh_ok. cbn [mi_priv mi_pub mi_ok].
    destruct (memneq_bool RAW zeros32 && memneq_bool (x25519 RAW basepoint9) zeros32)%bool; unfold hbytes; cancel.
Qed.

Lemma hc3_body_m_identity_of_handshake :
  @semax_body (hc3_V_bp WgNoise.harness.x_handshake.code._x_handshake__M_BASEPOINT) (hc3_G_m_identity_of x25519) CSki WgNoise.harness.x_handshake.code.f_m_identity_of (m_identity_of_spec x25519 WgNoise.harness.x_handshake.code._x_handshake__M_BASEPOINT).
Proof.
  start_function.
  rewrite hc3b_ident_mident_out. flatten_sepcon_in_SEP. flatten_sepcon_in_SEP.
  assert_PROP (field_compatible t_mident [] d) as FC.
  { entailer!. eapply hc3b_ident_fc_root; eauto. }
  assert (field_compatible t_mident (DOT FH._priv) d) as FCp by auto with field_compatible.
  assert (field_compatible t_mident (DOT FH._pub) d) as FCq by auto with field_compatible.
  forward_call (sh, field_address t_mident (DOT FH._priv) d, shr, r, RAW).
  { entailer!. simpl. rewrite H. hc3b_ident_fa. }
  { rewrite H. cancel. }
  forward_call (sh, field_address t_mident (DOT FH._priv) d, RAW).
  { entailer!. simpl. hc3b_ident_fa. }
  unfold hc_const.
  forward_call (sh, field_address t_mident (DOT FH._pub) d, shr, r, RAW, Ers, gv WgNoise.harness.x_handshake.code._x_handshake__M_BASEPOINT, basepoint9).
  forward_call (shr, r, RAW).
  { apply prop_right; simpl; rewrite H; reflexivity. }
  forward_if (PROP () LOCAL (temp WgNoise.harness.x_handshake.code._t'3 (Val.of_bool (memneq_bool RAW zeros32 && dh_ok x25519 RAW basepoint9)%bool); gvars gv; temp WgNoise.harness.x_handshake.code._id d) SEP (hbytes sh (x25519 RAW basepoint9) (field_address t_mident (DOT FH._pub) d); hbytes shr RAW r; hbytes Ers basepoint9 (gv WgNoise.harness.x_handshake.code._x_handshake__M_BASEPOINT); hbytes sh (clamp RAW) (field_address t_mident (DOT FH._priv) d); field_at_ sh t_mident (DOT FH._ok) d)).
  - forward. entailer!. rewrite hc3b_ident_is_zero in H0 by auto.
    destruct (memneq_bool RAW zeros32); simpl in H0; [|apply Int.one_not_zero in H0; contradiction].
    destruct (dh_ok x25519 RAW basepoint9); reflexivity.
  - forward. entailer!. rewrite hc3b_ident_is_zero in H0 by auto.
    destruct (memneq_bool RAW zeros32); simpl in H0; [contradiction H0; reflexivity|]. reflexivity.
  - forward. entailer!.
    rewrite (hc3b_ident_mident_eq sh (mident_of x25519 RAW) d) by (simpl; auto using hc3b_ident_clamp_len).
    unfold hc_const, mident_of, dh_ok. cbn [mi_priv mi_pub mi_ok].
    destruct (memneq_bool RAW zeros32 && memneq_bool (x25519 RAW basepoint9) zeros32)%bool; unfold hbytes; cancel.
Qed.

Lemma hc3_body_m_identity_of_replay :
  @semax_body (hc3_V_bp WgNoise.harness.x_replay.code._x_replay__M_BASEPOINT) (hc3_G_m_identity_of x25519) CSki WgNoise.harness.x_replay.code.f_m_identity_of (m_identity_of_spec x25519 WgNoise.harness.x_replay.code._x_replay__M_BASEPOINT).
Proof.
  start_function.
  rewrite hc3b_ident_mident_out. flatten_sepcon_in_SEP. flatten_sepcon_in_SEP.
  assert_PROP (field_compatible t_mident [] d) as FC.
  { entailer!. eapply hc3b_ident_fc_root; eauto. }
  assert (field_compatible t_mident (DOT FH._priv) d) as FCp by auto with field_compatible.
  assert (field_compatible t_mident (DOT FH._pub) d) as FCq by auto with field_compatible.
  forward_call (sh, field_address t_mident (DOT FH._priv) d, shr, r, RAW).
  { entailer!. simpl. rewrite H. hc3b_ident_fa. }
  { rewrite H. cancel. }
  forward_call (sh, field_address t_mident (DOT FH._priv) d, RAW).
  { entailer!. simpl. hc3b_ident_fa. }
  unfold hc_const.
  forward_call (sh, field_address t_mident (DOT FH._pub) d, shr, r, RAW, Ers, gv WgNoise.harness.x_replay.code._x_replay__M_BASEPOINT, basepoint9).
  forward_call (shr, r, RAW).
  { apply prop_right; simpl; rewrite H; reflexivity. }
  forward_if (PROP () LOCAL (temp WgNoise.harness.x_replay.code._t'3 (Val.of_bool (memneq_bool RAW zeros32 && dh_ok x25519 RAW basepoint9)%bool); gvars gv; temp WgNoise.harness.x_replay.code._id d) SEP (hbytes sh (x25519 RAW basepoint9) (field_address t_mident (DOT FH._pub) d); hbytes shr RAW r; hbytes Ers basepoint9 (gv WgNoise.harness.x_replay.code._x_replay__M_BASEPOINT); hbytes sh (clamp RAW) (field_address t_mident (DOT FH._priv) d); field_at_ sh t_mident (DOT FH._ok) d)).
  - forward. entailer!. rewrite hc3b_ident_is_zero in H0 by auto.
    destruct (memneq_bool RAW zeros32); simpl in H0; [|apply Int.one_not_zero in H0; contradiction].
    destruct (dh_ok x25519 RAW basepoint9); reflexivity.
  - forward. entailer!. rewrite hc3b_ident_is_zero in H0 by auto.
    destruct (memneq_bool RAW zeros32); simpl in H0; [contradiction H0; reflexivity|]. reflexivity.
  - forward. entailer!.
    rewrite (hc3b_ident_mident_eq sh (mident_of x25519 RAW) d) by (simpl; auto using hc3b_ident_clamp_len).
    unfold hc_const, mident_of, dh_ok. cbn [mi_priv mi_pub mi_ok].
    destruct (memneq_bool RAW zeros32 && memneq_bool (x25519 RAW basepoint9) zeros32)%bool; unfold hbytes; cancel.
Qed.

Lemma hc3_body_m_identity_of_cookie_mac :
  @semax_body (hc3_V_bp WgNoise.harness.x_cookie_mac.code._x_cookie_mac__M_BASEPOINT) (hc3_G_m_identity_of x25519) CSki WgNoise.harness.x_cookie_mac.code.f_m_identity_of (m_identity_of_spec x25519 WgNoise.harness.x_cookie_mac.code._x_cookie_mac__M_BASEPOINT).
Proof.
  start_function.
  rewrite hc3b_ident_mident_out. flatten_sepcon_in_SEP. flatten_sepcon_in_SEP.
  assert_PROP (field_compatible t_mident [] d) as FC.
  { entailer!. eapply hc3b_ident_fc_root; eauto. }
  assert (field_compatible t_mident (DOT FH._priv) d) as FCp by auto with field_compatible.
  assert (field_compatible t_mident (DOT FH._pub) d) as FCq by auto with field_compatible.
  forward_call (sh, field_address t_mident (DOT FH._priv) d, shr, r, RAW).
  { entailer!. simpl. rewrite H. hc3b_ident_fa. }
  { rewrite H. cancel. }
  forward_call (sh, field_address t_mident (DOT FH._priv) d, RAW).
  { entailer!. simpl. hc3b_ident_fa. }
  unfold hc_const.
  forward_call (sh, field_address t_mident (DOT FH._pub) d, shr, r, RAW, Ers, gv WgNoise.harness.x_cookie_mac.code._x_cookie_mac__M_BASEPOINT, basepoint9).
  forward_call (shr, r, RAW).
  { apply prop_right; simpl; rewrite H; reflexivity. }
  forward_if (PROP () LOCAL (temp WgNoise.harness.x_cookie_mac.code._t'3 (Val.of_bool (memneq_bool RAW zeros32 && dh_ok x25519 RAW basepoint9)%bool); gvars gv; temp WgNoise.harness.x_cookie_mac.code._id d) SEP (hbytes sh (x25519 RAW basepoint9) (field_address t_mident (DOT FH._pub) d); hbytes shr RAW r; hbytes Ers basepoint9 (gv WgNoise.harness.x_cookie_mac.code._x_cookie_mac__M_BASEPOINT); hbytes sh (clamp RAW) (field_address t_mident (DOT FH._priv) d); field_at_ sh t_mident (DOT FH._ok) d)).
  - forward. entailer!. rewrite hc3b_ident_is_zero in H0 by auto.
    destruct (memneq_bool RAW zeros32); simpl in H0; [|apply Int.one_not_zero in H0; contradiction].
    destruct (dh_ok x25519 RAW basepoint9); reflexivity.
  - forward. entailer!. rewrite hc3b_ident_is_zero in H0 by auto.
    destruct (memneq_bool RAW zeros32); simpl in H0; [contradiction H0; reflexivity|]. reflexivity.
  - forward. entailer!.
    rewrite (hc3b_ident_mident_eq sh (mident_of x25519 RAW) d) by (simpl; auto using hc3b_ident_clamp_len).
    unfold hc_const, mident_of, dh_ok. cbn [mi_priv mi_pub mi_ok].
    destruct (memneq_bool RAW zeros32 && memneq_bool (x25519 RAW basepoint9) zeros32)%bool; unfold hbytes; cancel.
Qed.

Lemma hc3_body_m_identity_of_consume_initiation_any :
  @semax_body (hc3_V_bp WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_BASEPOINT) (hc3_G_m_identity_of x25519) CSki WgNoise.harness.x_consume_initiation_any.code.f_m_identity_of (m_identity_of_spec x25519 WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_BASEPOINT).
Proof.
  start_function.
  rewrite hc3b_ident_mident_out. flatten_sepcon_in_SEP. flatten_sepcon_in_SEP.
  assert_PROP (field_compatible t_mident [] d) as FC.
  { entailer!. eapply hc3b_ident_fc_root; eauto. }
  assert (field_compatible t_mident (DOT FH._priv) d) as FCp by auto with field_compatible.
  assert (field_compatible t_mident (DOT FH._pub) d) as FCq by auto with field_compatible.
  forward_call (sh, field_address t_mident (DOT FH._priv) d, shr, r, RAW).
  { entailer!. simpl. rewrite H. hc3b_ident_fa. }
  { rewrite H. cancel. }
  forward_call (sh, field_address t_mident (DOT FH._priv) d, RAW).
  { entailer!. simpl. hc3b_ident_fa. }
  unfold hc_const.
  forward_call (sh, field_address t_mident (DOT FH._pub) d, shr, r, RAW, Ers, gv WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_BASEPOINT, basepoint9).
  forward_call (shr, r, RAW).
  { apply prop_right; simpl; rewrite H; reflexivity. }
  forward_if (PROP () LOCAL (temp WgNoise.harness.x_consume_initiation_any.code._t'3 (Val.of_bool (memneq_bool RAW zeros32 && dh_ok x25519 RAW basepoint9)%bool); gvars gv; temp WgNoise.harness.x_consume_initiation_any.code._id d) SEP (hbytes sh (x25519 RAW basepoint9) (field_address t_mident (DOT FH._pub) d); hbytes shr RAW r; hbytes Ers basepoint9 (gv WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_BASEPOINT); hbytes sh (clamp RAW) (field_address t_mident (DOT FH._priv) d); field_at_ sh t_mident (DOT FH._ok) d)).
  - forward. entailer!. rewrite hc3b_ident_is_zero in H0 by auto.
    destruct (memneq_bool RAW zeros32); simpl in H0; [|apply Int.one_not_zero in H0; contradiction].
    destruct (dh_ok x25519 RAW basepoint9); reflexivity.
  - forward. entailer!. rewrite hc3b_ident_is_zero in H0 by auto.
    destruct (memneq_bool RAW zeros32); simpl in H0; [contradiction H0; reflexivity|]. reflexivity.
  - forward. entailer!.
    rewrite (hc3b_ident_mident_eq sh (mident_of x25519 RAW) d) by (simpl; auto using hc3b_ident_clamp_len).
    unfold hc_const, mident_of, dh_ok. cbn [mi_priv mi_pub mi_ok].
    destruct (memneq_bool RAW zeros32 && memneq_bool (x25519 RAW basepoint9) zeros32)%bool; unfold hbytes; cancel.
Qed.

Lemma hc3_body_m_identity_of_consume_response_any :
  @semax_body (hc3_V_bp WgNoise.harness.x_consume_response_any.code._x_consume_response_any__M_BASEPOINT) (hc3_G_m_identity_of x25519) CSki WgNoise.harness.x_consume_response_any.code.f_m_identity_of (m_identity_of_spec x25519 WgNoise.harness.x_consume_response_any.code._x_consume_response_any__M_BASEPOINT).
Proof.
  start_function.
  rewrite hc3b_ident_mident_out. flatten_sepcon_in_SEP. flatten_sepcon_in_SEP.
  assert_PROP (field_compatible t_mident [] d) as FC.
  { entailer!. eapply hc3b_ident_fc_root; eauto. }
  assert (field_compatible t_mident (DOT FH._priv) d) as FCp by auto with field_compatible.
  assert (field_compatible t_mident (DOT FH._pub) d) as FCq by auto with field_compatible.
  forward_call (sh, field_address t_mident (DOT FH._priv) d, shr, r, RAW).
  { entailer!. simpl. rewrite H. hc3b_ident_fa. }
  { rewrite H. cancel. }
  forward_call (sh, field_address t_mident (DOT FH._priv) d, RAW).
  { entailer!. simpl. hc3b_ident_fa. }
  unfold hc_const.
  forward_call (sh, field_address t_mident (DOT FH._pub) d, shr, r, RAW, Ers, gv WgNoise.harness.x_consume_response_any.code._x_consume_response_any__M_BASEPOINT, basepoint9).
  forward_call (shr, r, RAW).
  { apply prop_right; simpl; rewrite H; reflexivity. }
  forward_if (PROP () LOCAL (temp WgNoise.harness.x_consume_response_any.code._t'3 (Val.of_bool (memneq_bool RAW zeros32 && dh_ok x25519 RAW basepoint9)%bool); gvars gv; temp WgNoise.harness.x_consume_response_any.code._id d) SEP (hbytes sh (x25519 RAW basepoint9) (field_address t_mident (DOT FH._pub) d); hbytes shr RAW r; hbytes Ers basepoint9 (gv WgNoise.harness.x_consume_response_any.code._x_consume_response_any__M_BASEPOINT); hbytes sh (clamp RAW) (field_address t_mident (DOT FH._priv) d); field_at_ sh t_mident (DOT FH._ok) d)).
  - forward. entailer!. rewrite hc3b_ident_is_zero in H0 by auto.
    destruct (memneq_bool RAW zeros32); simpl in H0; [|apply Int.one_not_zero in H0; contradiction].
    destruct (dh_ok x25519 RAW basepoint9); reflexivity.
  - forward. entailer!. rewrite hc3b_ident_is_zero in H0 by auto.
    destruct (memneq_bool RAW zeros32); simpl in H0; [contradiction H0; reflexivity|]. reflexivity.
  - forward. entailer!.
    rewrite (hc3b_ident_mident_eq sh (mident_of x25519 RAW) d) by (simpl; auto using hc3b_ident_clamp_len).
    unfold hc_const, mident_of, dh_ok. cbn [mi_priv mi_pub mi_ok].
    destruct (memneq_bool RAW zeros32 && memneq_bool (x25519 RAW basepoint9) zeros32)%bool; unfold hbytes; cancel.
Qed.

Lemma hc3_body_m_identity_of_cookie_reply :
  @semax_body (hc3_V_bp WgNoise.harness.x_cookie_reply.code._x_cookie_reply__M_BASEPOINT) (hc3_G_m_identity_of x25519) CSki WgNoise.harness.x_cookie_reply.code.f_m_identity_of (m_identity_of_spec x25519 WgNoise.harness.x_cookie_reply.code._x_cookie_reply__M_BASEPOINT).
Proof.
  start_function.
  rewrite hc3b_ident_mident_out. flatten_sepcon_in_SEP. flatten_sepcon_in_SEP.
  assert_PROP (field_compatible t_mident [] d) as FC.
  { entailer!. eapply hc3b_ident_fc_root; eauto. }
  assert (field_compatible t_mident (DOT FH._priv) d) as FCp by auto with field_compatible.
  assert (field_compatible t_mident (DOT FH._pub) d) as FCq by auto with field_compatible.
  forward_call (sh, field_address t_mident (DOT FH._priv) d, shr, r, RAW).
  { entailer!. simpl. rewrite H. hc3b_ident_fa. }
  { rewrite H. cancel. }
  forward_call (sh, field_address t_mident (DOT FH._priv) d, RAW).
  { entailer!. simpl. hc3b_ident_fa. }
  unfold hc_const.
  forward_call (sh, field_address t_mident (DOT FH._pub) d, shr, r, RAW, Ers, gv WgNoise.harness.x_cookie_reply.code._x_cookie_reply__M_BASEPOINT, basepoint9).
  forward_call (shr, r, RAW).
  { apply prop_right; simpl; rewrite H; reflexivity. }
  forward_if (PROP () LOCAL (temp WgNoise.harness.x_cookie_reply.code._t'3 (Val.of_bool (memneq_bool RAW zeros32 && dh_ok x25519 RAW basepoint9)%bool); gvars gv; temp WgNoise.harness.x_cookie_reply.code._id d) SEP (hbytes sh (x25519 RAW basepoint9) (field_address t_mident (DOT FH._pub) d); hbytes shr RAW r; hbytes Ers basepoint9 (gv WgNoise.harness.x_cookie_reply.code._x_cookie_reply__M_BASEPOINT); hbytes sh (clamp RAW) (field_address t_mident (DOT FH._priv) d); field_at_ sh t_mident (DOT FH._ok) d)).
  - forward. entailer!. rewrite hc3b_ident_is_zero in H0 by auto.
    destruct (memneq_bool RAW zeros32); simpl in H0; [|apply Int.one_not_zero in H0; contradiction].
    destruct (dh_ok x25519 RAW basepoint9); reflexivity.
  - forward. entailer!. rewrite hc3b_ident_is_zero in H0 by auto.
    destruct (memneq_bool RAW zeros32); simpl in H0; [contradiction H0; reflexivity|]. reflexivity.
  - forward. entailer!.
    rewrite (hc3b_ident_mident_eq sh (mident_of x25519 RAW) d) by (simpl; auto using hc3b_ident_clamp_len).
    unfold hc_const, mident_of, dh_ok. cbn [mi_priv mi_pub mi_ok].
    destruct (memneq_bool RAW zeros32 && memneq_bool (x25519 RAW basepoint9) zeros32)%bool; unfold hbytes; cancel.
Qed.

Lemma hc3_body_m_precomputed :
  @semax_body [] (hc3_G_m_precomputed x25519) CSki FH.f_m_precomputed (m_precomputed_spec x25519).
Proof.
  start_function.
  assert_PROP (Zlength (mi_pub I) = 32) as HQ.
  { entailer!. hc3b_ident_pub_len. }
  rewrite (hc3b_ident_mident_eq shi I ri H HQ). flatten_sepcon_in_SEP. flatten_sepcon_in_SEP.
  assert_PROP (field_compatible t_mident [] ri) as FC.
  { entailer!. eapply hc3b_ident_fc_root; eauto. }
  assert (field_compatible t_mident (DOT FH._priv) ri) as FCp by auto with field_compatible.
  forward.
  forward_if (PROP () LOCAL (temp FH._t'1 (Val.of_bool (negb (mi_ok I && dh_ok x25519 (mi_priv I) PUB)));
      temp FH._out o; temp FH._id ri; temp FH._peer_pub p)
    SEP (if mi_ok I then hbytes sho (x25519 (mi_priv I) PUB) o else hout sho 32 o;
         hbytes shi (mi_priv I) (field_address t_mident (DOT FH._priv) ri);
         hbytes shi (mi_pub I) (field_address t_mident (DOT FH._pub) ri);
         field_at shi t_mident (DOT FH._ok) (Vint (if mi_ok I then Int.one else Int.zero)) ri;
         hbytes shp PUB p)).
  - forward. destruct (mi_ok I); [apply Int.one_not_zero in H1; contradiction|]. entailer!.
  - forward_call (sho, o, shi, field_address t_mident (DOT FH._priv) ri, mi_priv I, shp, p, PUB).
    { entailer!. simpl. hc3b_ident_fa. }
    forward. destruct (mi_ok I); [|contradiction H1; reflexivity]. entailer!.
    destruct (dh_ok x25519 (mi_priv I) PUB); reflexivity.
  - forward_if.
    + forward_call (sho, o, Byte.zero, 32).
      { sep_apply (hc3b_ident_if_out sho o (mi_ok I) (x25519 (mi_priv I) PUB) (X25519 _ _)). cancel. }
      entailer!. unfold m_precomputed_model.
      destruct (andb (mi_ok I) (dh_ok x25519 (mi_priv I) PUB)); simpl in H1; [inv H1|].
      rewrite (hc3b_ident_mident_eq shi I ri H HQ). unfold zeros32. cancel.
    + forward. entailer!. unfold m_precomputed_model.
      destruct (mi_ok I) eqn:Hok; destruct (dh_ok x25519 (mi_priv I) PUB) eqn:Hdh; simpl in H1; try (inv H1).
      rewrite (hc3b_ident_mident_eq shi I ri H HQ), Hok. simpl. cancel.
Qed.

Lemma hc3_body_m_static_public_field :
  @semax_body [] (hc3_G_m_static_public_field) CSki FH.f_m_static_public_field (m_static_public_field_spec).
Proof.
  start_function.
  assert_PROP (Zlength (mi_priv I) = 32) as HP.
  { entailer!. hc3b_ident_priv_len. }
  rewrite (hc3b_ident_mident_eq shi I ri HP H). flatten_sepcon_in_SEP.
  forward_call (shr, r, RAW).
  { apply prop_right; simpl; rewrite H0; reflexivity. }
  forward_if.
  - forward_call (sho, o, Byte.zero, 32).
    entailer!.
    rewrite hc3b_ident_is_zero in H1 by auto.
    unfold static_public_field. destruct (memneq_bool RAW zeros32); simpl in H1; [contradiction H1; reflexivity|].
    rewrite (hc3b_ident_mident_eq shi I ri HP H). unfold zeros32. cancel.
  - forward_call (sho, o, shi, field_address t_mident (DOT FH._pub) ri, mi_pub I).
    { rewrite H; entailer!. simpl. hc3b_ident_fa. }
    { rewrite H. cancel. }
    entailer!.
    rewrite hc3b_ident_is_zero in H1 by auto.
    unfold static_public_field. destruct (memneq_bool RAW zeros32); simpl in H1; [|apply Int.one_not_zero in H1; contradiction].
    rewrite (hc3b_ident_mident_eq shi I ri HP H). cancel.
Qed.

(* m_start: at CSks *)
#[local] Existing Instance CSks.
#[local] Instance hc3b_ident_HCS_CSks : change_composite_env HCS CSks.
Proof. make_cs_preserve HCS CSks. Defined.

Lemma hc3b_ident_mstate_eq sh ck h p :
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
  rewrite <- !(@data_at_tarray_tuchar_cs CSks HCS).
  reflexivity.
Qed.

Lemma hc3b_ident_mstate_out sh p :
  @data_at_ HCS sh t_mstate p =
  hout sh 32 (@field_address CSks t_mstate (DOT FH._ck) p) *
  hout sh 32 (@field_address CSks t_mstate (DOT FH._h) p).
Proof.
  erewrite (@data_at__change_composite HCS CSks _ sh t_mstate); [| prove_cs_preserve_type].
  rewrite data_at__eq. unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mstate (DOT FH._ck)), (field_at_data_at sh t_mstate (DOT FH._h)).
  unfold hout. rewrite <- !(@data_at__tarray_tuchar_cs CSks HCS).
  reflexivity.
Qed.

Ltac hc3b_ident_fa_st :=
  rewrite ?field_address_offset by auto with field_compatible; reflexivity.

Lemma hc3b_ident_h0_out v : @data_at_ CSks Tsh (tarray tuchar 32) v = hout Tsh 32 v.
Proof. unfold hout. apply data_at__tarray_tuchar_cs. Qed.

Lemma hc3b_ident_h0_back bs v : Zlength bs = 32 -> hbytes Tsh bs v |-- @data_at_ CSks Tsh (tarray tuchar 32) v.
Proof. intros Hl. rewrite hc3b_ident_h0_out. unfold hbytes, hout. rewrite Hl. apply data_at_data_at_. Qed.

Lemma hc3b_ident_HASH_len m : Zlength (HASH m) = 32.
Proof.
  unfold HASH, blake2s, WgNoise.proof.blake2s.model.b2s_digest_stream, WgNoise.proof.blake2s.model.b2s_out.
  rewrite Zlength_map. reflexivity.
Qed.

Lemma hc3b_ident_hin_ne sh bs p : Zlength bs <> 0 -> hin sh bs p = hbytes sh bs p.
Proof. intros. unfold hin. destruct (Z.eq_dec (Zlength bs) 0); [contradiction | reflexivity]. Qed.

Lemma hc3b_ident_hin_nil sh p : hin sh [] p = emp.
Proof. reflexivity. Qed.

Lemma hc3b_ident_hc_const gv i bs : hc_const gv i bs = hbytes Ers bs (gv i).
Proof. reflexivity. Qed.

Lemma hc3b_ident_cons_len : Zlength construction_bytes = 37.
Proof. reflexivity. Qed.

Lemma hc3b_ident_iden_len : Zlength identifier_bytes = 34.
Proof. reflexivity. Qed.

Lemma hc3b_ident_ck0 : HASH (construction_bytes ++ []) = init_ck.
Proof. rewrite app_nil_r. reflexivity. Qed.

Lemma hc3b_ident_h0 : HASH (init_ck ++ identifier_bytes) = init_hash.
Proof. reflexivity. Qed.

Lemma hc3b_ident_h1 PUB : HASH (init_hash ++ PUB) = mix_hash init_hash PUB.
Proof. reflexivity. Qed.

Lemma hc3b_ident_ck_len : Zlength init_ck = 32.
Proof. apply hc3b_ident_HASH_len. Qed.

Lemma hc3b_ident_ih_len : Zlength init_hash = 32.
Proof. apply hc3b_ident_HASH_len. Qed.

Lemma hc3b_ident_mh_len PUB : Zlength (mix_hash init_hash PUB) = 32.
Proof. unfold mix_hash. apply hc3b_ident_HASH_len. Qed.

Lemma hc3_body_m_start_create_any :
  @semax_body (hc3_V_start WgNoise.harness.x_create_any.code._x_create_any__M_CONSTRUCTION WgNoise.harness.x_create_any.code._x_create_any__M_IDENTIFIER) (hc3_G_m_start) CSks WgNoise.harness.x_create_any.code.f_m_start (m_start_spec WgNoise.harness.x_create_any.code._x_create_any__M_CONSTRUCTION WgNoise.harness.x_create_any.code._x_create_any__M_IDENTIFIER).
Proof.
  start_function.
  assert_PROP (field_compatible t_mstate [] s) as FC.
  { erewrite (@data_at__change_composite HCS CSks _ sh t_mstate) by prove_cs_preserve_type. entailer!. }
  assert (field_compatible t_mstate (DOT FH._ck) s) as FCk by auto with field_compatible.
  assert (field_compatible t_mstate (DOT FH._h) s) as FCh by auto with field_compatible.
  rewrite hc3b_ident_mstate_out. flatten_sepcon_in_SEP.
  forward_call (gv, sh, field_address t_mstate (DOT FH._ck) s, Ers, gv WgNoise.harness.x_create_any.code._x_create_any__M_CONSTRUCTION, construction_bytes, Ers, gv WgNoise.harness.x_create_any.code._x_create_any__M_CONSTRUCTION, @nil byte).
  { entailer!. simpl. rewrite hc3b_ident_cons_len. hc3b_ident_fa_st. }
  { rewrite hc3b_ident_hin_nil, (hc3b_ident_hin_ne Ers construction_bytes) by (rewrite hc3b_ident_cons_len; lia).
    rewrite hc3b_ident_hc_const. cancel. }
  { rewrite hc3b_ident_cons_len, Zlength_nil. rep_lia. }
  rewrite hc3b_ident_ck0, hc3b_ident_hin_nil, (hc3b_ident_hin_ne Ers construction_bytes) by (rewrite hc3b_ident_cons_len; lia).
  rewrite hc3b_ident_h0_out.
  forward_call (gv, Tsh, v_h0, sh, field_address t_mstate (DOT FH._ck) s, init_ck, Ers, gv WgNoise.harness.x_create_any.code._x_create_any__M_IDENTIFIER, identifier_bytes).
  { entailer!. simpl. rewrite hc3b_ident_iden_len, hc3b_ident_ck_len. hc3b_ident_fa_st. }
  { rewrite (hc3b_ident_hin_ne sh init_ck) by (rewrite hc3b_ident_ck_len; lia).
    rewrite (hc3b_ident_hin_ne Ers identifier_bytes) by (rewrite hc3b_ident_iden_len; lia).
    rewrite hc3b_ident_hc_const. cancel. }
  { rewrite hc3b_ident_iden_len, hc3b_ident_ck_len. rep_lia. }
  rewrite hc3b_ident_h0.
  rewrite (hc3b_ident_hin_ne sh init_ck) by (rewrite hc3b_ident_ck_len; lia).
  rewrite (hc3b_ident_hin_ne Ers identifier_bytes) by (rewrite hc3b_ident_iden_len; lia).
  forward_call (gv, sh, field_address t_mstate (DOT FH._h) s, Tsh, v_h0, init_hash, shp, p, PUB).
  { entailer!. simpl. rewrite H, hc3b_ident_ih_len. hc3b_ident_fa_st. }
  { rewrite (hc3b_ident_hin_ne Tsh init_hash) by (rewrite hc3b_ident_ih_len; lia).
    rewrite (hc3b_ident_hin_ne shp PUB) by lia. cancel. }
  { rewrite H, hc3b_ident_ih_len. rep_lia. }
  rewrite hc3b_ident_h1, (hc3b_ident_hin_ne Tsh init_hash) by (rewrite hc3b_ident_ih_len; lia).
  rewrite (hc3b_ident_hin_ne shp PUB) by lia.
  rewrite (hc3b_ident_mstate_eq sh init_ck (mix_hash init_hash PUB) s hc3b_ident_ck_len (hc3b_ident_mh_len PUB)).
  sep_apply (hc3b_ident_h0_back init_hash v_h0 hc3b_ident_ih_len).
  rewrite !hc3b_ident_hc_const.
  entailer!.
Qed.

Lemma hc3_body_m_start_handshake :
  @semax_body (hc3_V_start WgNoise.harness.x_handshake.code._x_handshake__M_CONSTRUCTION WgNoise.harness.x_handshake.code._x_handshake__M_IDENTIFIER) (hc3_G_m_start) CSks WgNoise.harness.x_handshake.code.f_m_start (m_start_spec WgNoise.harness.x_handshake.code._x_handshake__M_CONSTRUCTION WgNoise.harness.x_handshake.code._x_handshake__M_IDENTIFIER).
Proof.
  start_function.
  assert_PROP (field_compatible t_mstate [] s) as FC.
  { erewrite (@data_at__change_composite HCS CSks _ sh t_mstate) by prove_cs_preserve_type. entailer!. }
  assert (field_compatible t_mstate (DOT FH._ck) s) as FCk by auto with field_compatible.
  assert (field_compatible t_mstate (DOT FH._h) s) as FCh by auto with field_compatible.
  rewrite hc3b_ident_mstate_out. flatten_sepcon_in_SEP.
  forward_call (gv, sh, field_address t_mstate (DOT FH._ck) s, Ers, gv WgNoise.harness.x_handshake.code._x_handshake__M_CONSTRUCTION, construction_bytes, Ers, gv WgNoise.harness.x_handshake.code._x_handshake__M_CONSTRUCTION, @nil byte).
  { entailer!. simpl. rewrite hc3b_ident_cons_len. hc3b_ident_fa_st. }
  { rewrite hc3b_ident_hin_nil, (hc3b_ident_hin_ne Ers construction_bytes) by (rewrite hc3b_ident_cons_len; lia).
    rewrite hc3b_ident_hc_const. cancel. }
  { rewrite hc3b_ident_cons_len, Zlength_nil. rep_lia. }
  rewrite hc3b_ident_ck0, hc3b_ident_hin_nil, (hc3b_ident_hin_ne Ers construction_bytes) by (rewrite hc3b_ident_cons_len; lia).
  rewrite hc3b_ident_h0_out.
  forward_call (gv, Tsh, v_h0, sh, field_address t_mstate (DOT FH._ck) s, init_ck, Ers, gv WgNoise.harness.x_handshake.code._x_handshake__M_IDENTIFIER, identifier_bytes).
  { entailer!. simpl. rewrite hc3b_ident_iden_len, hc3b_ident_ck_len. hc3b_ident_fa_st. }
  { rewrite (hc3b_ident_hin_ne sh init_ck) by (rewrite hc3b_ident_ck_len; lia).
    rewrite (hc3b_ident_hin_ne Ers identifier_bytes) by (rewrite hc3b_ident_iden_len; lia).
    rewrite hc3b_ident_hc_const. cancel. }
  { rewrite hc3b_ident_iden_len, hc3b_ident_ck_len. rep_lia. }
  rewrite hc3b_ident_h0.
  rewrite (hc3b_ident_hin_ne sh init_ck) by (rewrite hc3b_ident_ck_len; lia).
  rewrite (hc3b_ident_hin_ne Ers identifier_bytes) by (rewrite hc3b_ident_iden_len; lia).
  forward_call (gv, sh, field_address t_mstate (DOT FH._h) s, Tsh, v_h0, init_hash, shp, p, PUB).
  { entailer!. simpl. rewrite H, hc3b_ident_ih_len. hc3b_ident_fa_st. }
  { rewrite (hc3b_ident_hin_ne Tsh init_hash) by (rewrite hc3b_ident_ih_len; lia).
    rewrite (hc3b_ident_hin_ne shp PUB) by lia. cancel. }
  { rewrite H, hc3b_ident_ih_len. rep_lia. }
  rewrite hc3b_ident_h1, (hc3b_ident_hin_ne Tsh init_hash) by (rewrite hc3b_ident_ih_len; lia).
  rewrite (hc3b_ident_hin_ne shp PUB) by lia.
  rewrite (hc3b_ident_mstate_eq sh init_ck (mix_hash init_hash PUB) s hc3b_ident_ck_len (hc3b_ident_mh_len PUB)).
  sep_apply (hc3b_ident_h0_back init_hash v_h0 hc3b_ident_ih_len).
  rewrite !hc3b_ident_hc_const.
  entailer!.
Qed.

Lemma hc3_body_m_start_replay :
  @semax_body (hc3_V_start WgNoise.harness.x_replay.code._x_replay__M_CONSTRUCTION WgNoise.harness.x_replay.code._x_replay__M_IDENTIFIER) (hc3_G_m_start) CSks WgNoise.harness.x_replay.code.f_m_start (m_start_spec WgNoise.harness.x_replay.code._x_replay__M_CONSTRUCTION WgNoise.harness.x_replay.code._x_replay__M_IDENTIFIER).
Proof.
  start_function.
  assert_PROP (field_compatible t_mstate [] s) as FC.
  { erewrite (@data_at__change_composite HCS CSks _ sh t_mstate) by prove_cs_preserve_type. entailer!. }
  assert (field_compatible t_mstate (DOT FH._ck) s) as FCk by auto with field_compatible.
  assert (field_compatible t_mstate (DOT FH._h) s) as FCh by auto with field_compatible.
  rewrite hc3b_ident_mstate_out. flatten_sepcon_in_SEP.
  forward_call (gv, sh, field_address t_mstate (DOT FH._ck) s, Ers, gv WgNoise.harness.x_replay.code._x_replay__M_CONSTRUCTION, construction_bytes, Ers, gv WgNoise.harness.x_replay.code._x_replay__M_CONSTRUCTION, @nil byte).
  { entailer!. simpl. rewrite hc3b_ident_cons_len. hc3b_ident_fa_st. }
  { rewrite hc3b_ident_hin_nil, (hc3b_ident_hin_ne Ers construction_bytes) by (rewrite hc3b_ident_cons_len; lia).
    rewrite hc3b_ident_hc_const. cancel. }
  { rewrite hc3b_ident_cons_len, Zlength_nil. rep_lia. }
  rewrite hc3b_ident_ck0, hc3b_ident_hin_nil, (hc3b_ident_hin_ne Ers construction_bytes) by (rewrite hc3b_ident_cons_len; lia).
  rewrite hc3b_ident_h0_out.
  forward_call (gv, Tsh, v_h0, sh, field_address t_mstate (DOT FH._ck) s, init_ck, Ers, gv WgNoise.harness.x_replay.code._x_replay__M_IDENTIFIER, identifier_bytes).
  { entailer!. simpl. rewrite hc3b_ident_iden_len, hc3b_ident_ck_len. hc3b_ident_fa_st. }
  { rewrite (hc3b_ident_hin_ne sh init_ck) by (rewrite hc3b_ident_ck_len; lia).
    rewrite (hc3b_ident_hin_ne Ers identifier_bytes) by (rewrite hc3b_ident_iden_len; lia).
    rewrite hc3b_ident_hc_const. cancel. }
  { rewrite hc3b_ident_iden_len, hc3b_ident_ck_len. rep_lia. }
  rewrite hc3b_ident_h0.
  rewrite (hc3b_ident_hin_ne sh init_ck) by (rewrite hc3b_ident_ck_len; lia).
  rewrite (hc3b_ident_hin_ne Ers identifier_bytes) by (rewrite hc3b_ident_iden_len; lia).
  forward_call (gv, sh, field_address t_mstate (DOT FH._h) s, Tsh, v_h0, init_hash, shp, p, PUB).
  { entailer!. simpl. rewrite H, hc3b_ident_ih_len. hc3b_ident_fa_st. }
  { rewrite (hc3b_ident_hin_ne Tsh init_hash) by (rewrite hc3b_ident_ih_len; lia).
    rewrite (hc3b_ident_hin_ne shp PUB) by lia. cancel. }
  { rewrite H, hc3b_ident_ih_len. rep_lia. }
  rewrite hc3b_ident_h1, (hc3b_ident_hin_ne Tsh init_hash) by (rewrite hc3b_ident_ih_len; lia).
  rewrite (hc3b_ident_hin_ne shp PUB) by lia.
  rewrite (hc3b_ident_mstate_eq sh init_ck (mix_hash init_hash PUB) s hc3b_ident_ck_len (hc3b_ident_mh_len PUB)).
  sep_apply (hc3b_ident_h0_back init_hash v_h0 hc3b_ident_ih_len).
  rewrite !hc3b_ident_hc_const.
  entailer!.
Qed.

Lemma hc3_body_m_start_consume_initiation_any :
  @semax_body (hc3_V_start WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_CONSTRUCTION WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_IDENTIFIER) (hc3_G_m_start) CSks WgNoise.harness.x_consume_initiation_any.code.f_m_start (m_start_spec WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_CONSTRUCTION WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_IDENTIFIER).
Proof.
  start_function.
  assert_PROP (field_compatible t_mstate [] s) as FC.
  { erewrite (@data_at__change_composite HCS CSks _ sh t_mstate) by prove_cs_preserve_type. entailer!. }
  assert (field_compatible t_mstate (DOT FH._ck) s) as FCk by auto with field_compatible.
  assert (field_compatible t_mstate (DOT FH._h) s) as FCh by auto with field_compatible.
  rewrite hc3b_ident_mstate_out. flatten_sepcon_in_SEP.
  forward_call (gv, sh, field_address t_mstate (DOT FH._ck) s, Ers, gv WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_CONSTRUCTION, construction_bytes, Ers, gv WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_CONSTRUCTION, @nil byte).
  { entailer!. simpl. rewrite hc3b_ident_cons_len. hc3b_ident_fa_st. }
  { rewrite hc3b_ident_hin_nil, (hc3b_ident_hin_ne Ers construction_bytes) by (rewrite hc3b_ident_cons_len; lia).
    rewrite hc3b_ident_hc_const. cancel. }
  { rewrite hc3b_ident_cons_len, Zlength_nil. rep_lia. }
  rewrite hc3b_ident_ck0, hc3b_ident_hin_nil, (hc3b_ident_hin_ne Ers construction_bytes) by (rewrite hc3b_ident_cons_len; lia).
  rewrite hc3b_ident_h0_out.
  forward_call (gv, Tsh, v_h0, sh, field_address t_mstate (DOT FH._ck) s, init_ck, Ers, gv WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_IDENTIFIER, identifier_bytes).
  { entailer!. simpl. rewrite hc3b_ident_iden_len, hc3b_ident_ck_len. hc3b_ident_fa_st. }
  { rewrite (hc3b_ident_hin_ne sh init_ck) by (rewrite hc3b_ident_ck_len; lia).
    rewrite (hc3b_ident_hin_ne Ers identifier_bytes) by (rewrite hc3b_ident_iden_len; lia).
    rewrite hc3b_ident_hc_const. cancel. }
  { rewrite hc3b_ident_iden_len, hc3b_ident_ck_len. rep_lia. }
  rewrite hc3b_ident_h0.
  rewrite (hc3b_ident_hin_ne sh init_ck) by (rewrite hc3b_ident_ck_len; lia).
  rewrite (hc3b_ident_hin_ne Ers identifier_bytes) by (rewrite hc3b_ident_iden_len; lia).
  forward_call (gv, sh, field_address t_mstate (DOT FH._h) s, Tsh, v_h0, init_hash, shp, p, PUB).
  { entailer!. simpl. rewrite H, hc3b_ident_ih_len. hc3b_ident_fa_st. }
  { rewrite (hc3b_ident_hin_ne Tsh init_hash) by (rewrite hc3b_ident_ih_len; lia).
    rewrite (hc3b_ident_hin_ne shp PUB) by lia. cancel. }
  { rewrite H, hc3b_ident_ih_len. rep_lia. }
  rewrite hc3b_ident_h1, (hc3b_ident_hin_ne Tsh init_hash) by (rewrite hc3b_ident_ih_len; lia).
  rewrite (hc3b_ident_hin_ne shp PUB) by lia.
  rewrite (hc3b_ident_mstate_eq sh init_ck (mix_hash init_hash PUB) s hc3b_ident_ck_len (hc3b_ident_mh_len PUB)).
  sep_apply (hc3b_ident_h0_back init_hash v_h0 hc3b_ident_ih_len).
  rewrite !hc3b_ident_hc_const.
  entailer!.
Qed.

(* the group *)
Theorem hc3_bodies_ident :
  (@semax_body (hc3_V_bp WgNoise.harness.x_create_any.code._x_create_any__M_BASEPOINT) (hc3_G_m_identity_of x25519) CSki WgNoise.harness.x_create_any.code.f_m_identity_of (m_identity_of_spec x25519 WgNoise.harness.x_create_any.code._x_create_any__M_BASEPOINT)) /\
  (@semax_body (hc3_V_bp WgNoise.harness.x_handshake.code._x_handshake__M_BASEPOINT) (hc3_G_m_identity_of x25519) CSki WgNoise.harness.x_handshake.code.f_m_identity_of (m_identity_of_spec x25519 WgNoise.harness.x_handshake.code._x_handshake__M_BASEPOINT)) /\
  (@semax_body (hc3_V_bp WgNoise.harness.x_replay.code._x_replay__M_BASEPOINT) (hc3_G_m_identity_of x25519) CSki WgNoise.harness.x_replay.code.f_m_identity_of (m_identity_of_spec x25519 WgNoise.harness.x_replay.code._x_replay__M_BASEPOINT)) /\
  (@semax_body (hc3_V_bp WgNoise.harness.x_cookie_mac.code._x_cookie_mac__M_BASEPOINT) (hc3_G_m_identity_of x25519) CSki WgNoise.harness.x_cookie_mac.code.f_m_identity_of (m_identity_of_spec x25519 WgNoise.harness.x_cookie_mac.code._x_cookie_mac__M_BASEPOINT)) /\
  (@semax_body (hc3_V_bp WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_BASEPOINT) (hc3_G_m_identity_of x25519) CSki WgNoise.harness.x_consume_initiation_any.code.f_m_identity_of (m_identity_of_spec x25519 WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_BASEPOINT)) /\
  (@semax_body (hc3_V_bp WgNoise.harness.x_consume_response_any.code._x_consume_response_any__M_BASEPOINT) (hc3_G_m_identity_of x25519) CSki WgNoise.harness.x_consume_response_any.code.f_m_identity_of (m_identity_of_spec x25519 WgNoise.harness.x_consume_response_any.code._x_consume_response_any__M_BASEPOINT)) /\
  (@semax_body (hc3_V_bp WgNoise.harness.x_cookie_reply.code._x_cookie_reply__M_BASEPOINT) (hc3_G_m_identity_of x25519) CSki WgNoise.harness.x_cookie_reply.code.f_m_identity_of (m_identity_of_spec x25519 WgNoise.harness.x_cookie_reply.code._x_cookie_reply__M_BASEPOINT)) /\
  (@semax_body [] (hc3_G_m_precomputed x25519) CSki FH.f_m_precomputed (m_precomputed_spec x25519)) /\
  (@semax_body [] (hc3_G_m_static_public_field) CSki FH.f_m_static_public_field (m_static_public_field_spec)) /\
  (@semax_body (hc3_V_start WgNoise.harness.x_create_any.code._x_create_any__M_CONSTRUCTION WgNoise.harness.x_create_any.code._x_create_any__M_IDENTIFIER) (hc3_G_m_start) CSks WgNoise.harness.x_create_any.code.f_m_start (m_start_spec WgNoise.harness.x_create_any.code._x_create_any__M_CONSTRUCTION WgNoise.harness.x_create_any.code._x_create_any__M_IDENTIFIER)) /\
  (@semax_body (hc3_V_start WgNoise.harness.x_handshake.code._x_handshake__M_CONSTRUCTION WgNoise.harness.x_handshake.code._x_handshake__M_IDENTIFIER) (hc3_G_m_start) CSks WgNoise.harness.x_handshake.code.f_m_start (m_start_spec WgNoise.harness.x_handshake.code._x_handshake__M_CONSTRUCTION WgNoise.harness.x_handshake.code._x_handshake__M_IDENTIFIER)) /\
  (@semax_body (hc3_V_start WgNoise.harness.x_replay.code._x_replay__M_CONSTRUCTION WgNoise.harness.x_replay.code._x_replay__M_IDENTIFIER) (hc3_G_m_start) CSks WgNoise.harness.x_replay.code.f_m_start (m_start_spec WgNoise.harness.x_replay.code._x_replay__M_CONSTRUCTION WgNoise.harness.x_replay.code._x_replay__M_IDENTIFIER)) /\
  (@semax_body (hc3_V_start WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_CONSTRUCTION WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_IDENTIFIER) (hc3_G_m_start) CSks WgNoise.harness.x_consume_initiation_any.code.f_m_start (m_start_spec WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_CONSTRUCTION WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_IDENTIFIER)).
Proof.
  exact (conj hc3_body_m_identity_of_create_any (conj hc3_body_m_identity_of_handshake
    (conj hc3_body_m_identity_of_replay (conj hc3_body_m_identity_of_cookie_mac
    (conj hc3_body_m_identity_of_consume_initiation_any (conj hc3_body_m_identity_of_consume_response_any
    (conj hc3_body_m_identity_of_cookie_reply (conj hc3_body_m_precomputed
    (conj hc3_body_m_static_public_field (conj hc3_body_m_start_create_any
    (conj hc3_body_m_start_handshake (conj hc3_body_m_start_replay hc3_body_m_start_consume_initiation_any)))))))))))).
Qed.

End Bodies.
