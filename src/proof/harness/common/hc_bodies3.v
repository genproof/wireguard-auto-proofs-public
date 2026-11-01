(* the common.h function bodies of every protocol law: for each law, its harness
   unit's copies of the common.h functions (hc_G3_<law>, hc_prog3.v) against their specifications
   (hc_specs3.v), with the imports hc_imports3, for ANY primitive models with the prim_api properties and ANY
   world compspecs CSw.  (The hnodes_* functions of the laws consume_initiation_any, consume_response_any,
   cookie_reply are not in hc_G3_<law>: stage 2, see spec-hc3.)

   Method: each body is proved once at a small compspecs with only its
   callees' specifications (hc3_body_*.v, contexts hc3_ctx.v, compspecs hc3_cs.v) and lifted to each law's unit
   by hc3_lift (hc3_lift.v; compspecs-polymorphic callees related by hc3_xcs.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.harness.common.hc_prog3.
Require Import QuickProof.Env.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common.hc3_ctx.
Require Import WgNoise.proof.harness.common.hc3_lift.
Require Import WgNoise.proof.harness.common.hc3_xcs.
Require Import WgNoise.proof.harness.common.hc3_body_loops WgNoise.proof.harness.common.hc3_body_draws
  WgNoise.proof.harness.common.hc3_body_sym WgNoise.proof.harness.common.hc3_body_kdf
  WgNoise.proof.harness.common.hc3_body_mix WgNoise.proof.harness.common.hc3_body_ident
  WgNoise.proof.harness.common.hc3_body_init WgNoise.proof.harness.common.hc3_body_cinit
  WgNoise.proof.harness.common.hc3_body_resp WgNoise.proof.harness.common.hc3_body_setup
  WgNoise.proof.harness.common.hc3_body_table WgNoise.proof.harness.common.hc3_body_snap
  WgNoise.proof.harness.common.hc3_body_msg WgNoise.proof.harness.common.hc3_body_ck.
Require WgNoise.contracts.x_cookie_reply.

Notation KCS := WgNoise.contracts.x_cookie_reply.Harness.CS.

Ltac hc3_cssub :=
  split3; intros ?i; apply sub_option_get; apply Forall_forall; intros ?x ?Hx; vm_compute in Hx;
  repeat destruct Hx as [<-|Hx]; try contradiction; vm_compute; reflexivity.

Ltac hc3_gsub :=
  unfold hc3_Gsub;
  repeat (apply Forall_cons;
          [eexists; split;
           [reflexivity
           | first [ apply funspec_sub_refl | apply hc3_curve25519_generic_xcs | apply hc3_chacha_enc_xcs
                   | apply hc3_chacha_dec3_xcs | apply hc3_nondet_bytes_xcs ] ] | ]);
  apply Forall_nil.

Ltac hc3_vsub := unfold hc3_Vsub; repeat (apply Forall_cons; [split; reflexivity | ]); apply Forall_nil.

(* one entry: the body lemma B lifted to the law's unit *)
Ltac hc3_entry B CSUB :=
  eexists; split; [left; reflexivity | ]; refine (hc3_lift _ _ _ _ _ _ _ B _ _ _ _ _);
  [ reflexivity | exact CSUB | repeat constructor | hc3_gsub | hc3_vsub ].

Lemma hc3_cs_CSk_consume_initiation_any: cspecs_sub CSk (u_cs u_h_consume_initiation_any).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSk_consume_response_any: cspecs_sub CSk (u_cs u_h_consume_response_any).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSk_cookie_mac: cspecs_sub CSk (u_cs u_h_cookie_mac).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSk_cookie_reply: cspecs_sub CSk (u_cs u_h_cookie_reply).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSk_create_any: cspecs_sub CSk (u_cs u_h_create_any).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSk_handshake: cspecs_sub CSk (u_cs u_h_handshake).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSk_keypairs: cspecs_sub CSk (u_cs u_h_keypairs).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSk_replay: cspecs_sub CSk (u_cs u_h_replay).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSkci_consume_initiation_any: cspecs_sub CSkci (u_cs u_h_consume_initiation_any).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSkci_handshake: cspecs_sub CSkci (u_cs u_h_handshake).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSkci_replay: cspecs_sub CSkci (u_cs u_h_replay).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSkck_cookie_mac: cspecs_sub CSkck (u_cs u_h_cookie_mac).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSkck_cookie_reply: cspecs_sub CSkck (u_cs u_h_cookie_reply).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSkh_consume_initiation_any: cspecs_sub CSkh (u_cs u_h_consume_initiation_any).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSkh_consume_response_any: cspecs_sub CSkh (u_cs u_h_consume_response_any).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSkh_cookie_reply: cspecs_sub CSkh (u_cs u_h_cookie_reply).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSkh_create_any: cspecs_sub CSkh (u_cs u_h_create_any).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSkh_handshake: cspecs_sub CSkh (u_cs u_h_handshake).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSkh_keypairs: cspecs_sub CSkh (u_cs u_h_keypairs).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSkh_replay: cspecs_sub CSkh (u_cs u_h_replay).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSki_consume_initiation_any: cspecs_sub CSki (u_cs u_h_consume_initiation_any).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSki_consume_response_any: cspecs_sub CSki (u_cs u_h_consume_response_any).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSki_cookie_mac: cspecs_sub CSki (u_cs u_h_cookie_mac).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSki_cookie_reply: cspecs_sub CSki (u_cs u_h_cookie_reply).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSki_create_any: cspecs_sub CSki (u_cs u_h_create_any).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSki_handshake: cspecs_sub CSki (u_cs u_h_handshake).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSki_replay: cspecs_sub CSki (u_cs u_h_replay).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSkinit_consume_initiation_any: cspecs_sub CSkinit (u_cs u_h_consume_initiation_any).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSkinit_handshake: cspecs_sub CSkinit (u_cs u_h_handshake).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSkresp_consume_response_any: cspecs_sub CSkresp (u_cs u_h_consume_response_any).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSkresp_handshake: cspecs_sub CSkresp (u_cs u_h_handshake).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSks_consume_initiation_any: cspecs_sub CSks (u_cs u_h_consume_initiation_any).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSks_consume_response_any: cspecs_sub CSks (u_cs u_h_consume_response_any).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSks_create_any: cspecs_sub CSks (u_cs u_h_create_any).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSks_handshake: cspecs_sub CSks (u_cs u_h_handshake).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSks_replay: cspecs_sub CSks (u_cs u_h_replay).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSmi_consume_initiation_any: cspecs_sub CSmi (u_cs u_h_consume_initiation_any).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSmi_create_any: cspecs_sub CSmi (u_cs u_h_create_any).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSmi_handshake: cspecs_sub CSmi (u_cs u_h_handshake).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSmi_replay: cspecs_sub CSmi (u_cs u_h_replay).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSmr_consume_response_any: cspecs_sub CSmr (u_cs u_h_consume_response_any).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSmr_create_any: cspecs_sub CSmr (u_cs u_h_create_any).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_CSmr_handshake: cspecs_sub CSmr (u_cs u_h_handshake).
Proof. hc3_cssub. Qed.
Lemma hc3_cs_KCS_cookie_reply: cspecs_sub KCS (u_cs u_h_cookie_reply).
Proof. hc3_cssub. Qed.

Section Pieces.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.
Hypothesis X25519: x25519_props x25519.
Hypothesis AEAD: aead_props aead_enc aead_dec.
Hypothesis XAEAD: xaead_props xaead_enc xaead_dec.

Lemma hc3_G3_keypairs_eq: hc_G3_keypairs x25519 aead_enc aead_dec =
  [check_failed_spec;
   bytes_eq_spec;
   bytes_zero_spec;
   bytes_copy_spec;
   bytes_set_spec;
   draw_steps_spec;
   draw_u64_spec;
   draw_boottime_spec;
   m_hash2_spec;
   m_hmac_spec;
   m_kdf_spec;
   (m_transport_spec WgNoise.harness.x_keypairs.code._x_keypairs__M_BASEPOINT);
   (setup_device_spec x25519);
   (setup_peer_spec x25519);
   table_has_spec;
   table_index_unique_spec;
   table_len_spec;
   hs_take_spec;
   hs_same_spec;
   hs_zeroed_from_spec;
   draw_hs_state_spec].
Proof. reflexivity. Qed.

Lemma hc3_G3_create_any_eq: hc_G3_create_any x25519 aead_enc aead_dec =
  [check_failed_spec;
   bytes_eq_spec;
   bytes_zero_spec;
   bytes_copy_spec;
   bytes_set_spec;
   draw_steps_spec;
   draw_u64_spec;
   draw_boottime_spec;
   le32_store_spec;
   m_hash2_spec;
   m_hmac_spec;
   m_kdf_spec;
   (m_dh_spec x25519);
   m_clamp_spec;
   (m_identity_of_spec x25519 WgNoise.harness.x_create_any.code._x_create_any__M_BASEPOINT);
   (m_start_spec WgNoise.harness.x_create_any.code._x_create_any__M_CONSTRUCTION WgNoise.harness.x_create_any.code._x_create_any__M_IDENTIFIER);
   m_mix_hash_spec;
   m_mix_ck_spec;
   m_mix_key_spec;
   m_mix_psk_spec;
   (m_encrypt_and_hash_spec aead_enc);
   m_tai64n_spec;
   (setup_device_spec x25519);
   (setup_peer_spec x25519);
   (m_precomputed_spec x25519);
   table_has_spec;
   table_index_unique_spec;
   table_len_spec;
   hs_take_spec;
   hs_same_spec;
   draw_hs_state_spec;
   init_img_spec;
   resp_img_spec;
   fill_init_spec;
   fill_resp_spec;
   draw_real_clock_spec;
   hs_randomize_spec].
Proof. reflexivity. Qed.

Lemma hc3_G3_handshake_eq: hc_G3_handshake x25519 aead_enc aead_dec =
  [check_failed_spec;
   bytes_eq_spec;
   bytes_zero_spec;
   bytes_copy_spec;
   bytes_set_spec;
   draw_u64_spec;
   draw_boottime_spec;
   le32_store_spec;
   m_hash2_spec;
   m_hmac_spec;
   m_kdf_spec;
   (m_dh_spec x25519);
   m_clamp_spec;
   (m_identity_of_spec x25519 WgNoise.harness.x_handshake.code._x_handshake__M_BASEPOINT);
   (m_start_spec WgNoise.harness.x_handshake.code._x_handshake__M_CONSTRUCTION WgNoise.harness.x_handshake.code._x_handshake__M_IDENTIFIER);
   m_mix_hash_spec;
   m_mix_ck_spec;
   m_mix_key_spec;
   m_mix_psk_spec;
   (m_encrypt_and_hash_spec aead_enc);
   (m_decrypt_and_hash_spec aead_dec);
   m_tai64n_spec;
   (m_create_initiation_spec x25519 aead_enc WgNoise.harness.x_handshake.code._x_handshake__M_BASEPOINT WgNoise.harness.x_handshake.code._x_handshake__M_CONSTRUCTION WgNoise.harness.x_handshake.code._x_handshake__M_IDENTIFIER);
   (m_consume_initiation_1_spec x25519 aead_dec WgNoise.harness.x_handshake.code._x_handshake__M_CONSTRUCTION WgNoise.harness.x_handshake.code._x_handshake__M_IDENTIFIER);
   (m_consume_initiation_2_spec aead_dec);
   (m_create_response_spec x25519 aead_enc WgNoise.harness.x_handshake.code._x_handshake__M_BASEPOINT);
   (m_consume_response_spec x25519 aead_dec);
   (m_transport_spec WgNoise.harness.x_handshake.code._x_handshake__M_BASEPOINT);
   m_label_key_spec;
   m_mac_spec;
   (setup_device_spec x25519);
   (setup_peer_spec x25519);
   (m_precomputed_spec x25519);
   table_has_spec;
   table_index_unique_spec;
   table_len_spec;
   hs_take_spec;
   hs_same_spec;
   hs_zeroed_from_spec;
   m_static_public_field_spec;
   init_img_spec;
   resp_img_spec;
   fill_init_spec;
   fill_resp_spec;
   draw_real_clock_spec;
   m_ts_newer_spec;
   m_not_flood_spec;
   m_last_consumption_spec].
Proof. reflexivity. Qed.

Lemma hc3_G3_replay_eq: hc_G3_replay x25519 aead_enc aead_dec =
  [check_failed_spec;
   bytes_eq_spec;
   bytes_zero_spec;
   bytes_copy_spec;
   bytes_set_spec;
   draw_steps_spec;
   draw_u64_spec;
   draw_boottime_spec;
   m_hash2_spec;
   m_hmac_spec;
   m_kdf_spec;
   (m_dh_spec x25519);
   m_clamp_spec;
   (m_identity_of_spec x25519 WgNoise.harness.x_replay.code._x_replay__M_BASEPOINT);
   (m_start_spec WgNoise.harness.x_replay.code._x_replay__M_CONSTRUCTION WgNoise.harness.x_replay.code._x_replay__M_IDENTIFIER);
   m_mix_hash_spec;
   m_mix_ck_spec;
   m_mix_key_spec;
   (m_decrypt_and_hash_spec aead_dec);
   (m_consume_initiation_1_spec x25519 aead_dec WgNoise.harness.x_replay.code._x_replay__M_CONSTRUCTION WgNoise.harness.x_replay.code._x_replay__M_IDENTIFIER);
   (m_consume_initiation_2_spec aead_dec);
   (setup_device_spec x25519);
   (setup_peer_spec x25519);
   (m_precomputed_spec x25519);
   hs_take_spec;
   hs_same_spec;
   fill_init_spec;
   draw_real_clock_spec;
   m_ts_newer_spec;
   m_not_flood_spec;
   m_last_consumption_spec].
Proof. reflexivity. Qed.

Lemma hc3_G3_cookie_mac_eq: hc_G3_cookie_mac x25519 aead_enc aead_dec =
  [check_failed_spec;
   bytes_eq_spec;
   bytes_zero_spec;
   bytes_copy_spec;
   bytes_set_spec;
   draw_size_spec;
   draw_u64_spec;
   draw_boottime_spec;
   m_hash2_spec;
   (m_dh_spec x25519);
   m_clamp_spec;
   (m_identity_of_spec x25519 WgNoise.harness.x_cookie_mac.code._x_cookie_mac__M_BASEPOINT);
   m_label_key_spec;
   m_mac_spec;
   (setup_device_spec x25519);
   (setup_peer_spec x25519);
   ck_take_spec].
Proof. reflexivity. Qed.

Lemma hc3_G3_consume_initiation_any_eq: hc_G3_consume_initiation_any x25519 aead_enc aead_dec =
  [check_failed_spec;
   bytes_eq_spec;
   bytes_zero_spec;
   bytes_copy_spec;
   bytes_set_spec;
   draw_steps_spec;
   draw_u64_spec;
   draw_boottime_spec;
   le32_store_spec;
   m_hash2_spec;
   m_hmac_spec;
   m_kdf_spec;
   (m_dh_spec x25519);
   m_clamp_spec;
   (m_identity_of_spec x25519 WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_BASEPOINT);
   (m_start_spec WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_CONSTRUCTION WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_IDENTIFIER);
   m_mix_hash_spec;
   m_mix_ck_spec;
   m_mix_key_spec;
   (m_encrypt_and_hash_spec aead_enc);
   (m_decrypt_and_hash_spec aead_dec);
   m_tai64n_spec;
   (m_create_initiation_spec x25519 aead_enc WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_BASEPOINT WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_CONSTRUCTION WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_IDENTIFIER);
   (m_consume_initiation_1_spec x25519 aead_dec WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_CONSTRUCTION WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_IDENTIFIER);
   (m_consume_initiation_2_spec aead_dec);
   (setup_device_spec x25519);
   (setup_peer_spec x25519);
   (m_precomputed_spec x25519);
   hs_take_spec;
   hs_same_spec;
   draw_hs_state_spec;
   init_img_spec;
   fill_init_spec;
   draw_real_clock_spec;
   m_ts_newer_spec;
   m_not_flood_spec;
   m_last_consumption_spec;
   hs_randomize_spec].
Proof. reflexivity. Qed.

Lemma hc3_G3_consume_response_any_eq: hc_G3_consume_response_any x25519 aead_enc aead_dec =
  [check_failed_spec;
   bytes_eq_spec;
   bytes_zero_spec;
   bytes_copy_spec;
   bytes_set_spec;
   draw_steps_spec;
   draw_u64_spec;
   draw_boottime_spec;
   le32_store_spec;
   m_hash2_spec;
   m_hmac_spec;
   m_kdf_spec;
   (m_dh_spec x25519);
   m_clamp_spec;
   (m_identity_of_spec x25519 WgNoise.harness.x_consume_response_any.code._x_consume_response_any__M_BASEPOINT);
   m_mix_hash_spec;
   m_mix_ck_spec;
   m_mix_psk_spec;
   (m_encrypt_and_hash_spec aead_enc);
   (m_decrypt_and_hash_spec aead_dec);
   (m_create_response_spec x25519 aead_enc WgNoise.harness.x_consume_response_any.code._x_consume_response_any__M_BASEPOINT);
   (m_consume_response_spec x25519 aead_dec);
   (setup_device_spec x25519);
   (setup_peer_spec x25519);
   hs_take_spec;
   hs_same_spec;
   draw_hs_state_spec;
   resp_img_spec;
   fill_resp_spec;
   hs_randomize_spec].
Proof. reflexivity. Qed.

Lemma hc3_G3_cookie_reply_eq: hc_G3_cookie_reply x25519 aead_enc aead_dec =
  [check_failed_spec;
   bytes_eq_spec;
   bytes_zero_spec;
   bytes_copy_spec;
   bytes_set_spec;
   draw_size_spec;
   draw_steps_spec;
   draw_u64_spec;
   draw_boottime_spec;
   le32_store_spec;
   m_hash2_spec;
   (m_dh_spec x25519);
   m_clamp_spec;
   (m_identity_of_spec x25519 WgNoise.harness.x_cookie_reply.code._x_cookie_reply__M_BASEPOINT);
   m_label_key_spec;
   m_mac_spec;
   (setup_device_spec x25519);
   (setup_peer_spec x25519);
   hs_take_spec;
   hs_same_spec;
   ck_take_spec;
   ck_same_spec;
   cookie_img_spec;
   fill_cookie_msg_spec].
Proof. reflexivity. Qed.

Lemma hc3_piece_keypairs: piece_ok [u_h_keypairs] (hc_imports3s x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
  (hc_G3_keypairs x25519 aead_enc aead_dec).
Proof.
  rewrite hc3_G3_keypairs_eq. split.
  { apply compute_list_norepet_e. reflexivity. }
  repeat apply Forall_cons; try apply Forall_nil.
  - (* check_failed *) hc3_entry (hc3_body_check_failed x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_keypairs.
  - (* bytes_eq *) hc3_entry (hc3_body_bytes_eq x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_keypairs.
  - (* bytes_zero *) hc3_entry (hc3_body_bytes_zero x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_keypairs.
  - (* bytes_copy *) hc3_entry (hc3_body_bytes_copy x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_keypairs.
  - (* bytes_set *) hc3_entry (hc3_body_bytes_set x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_keypairs.
  - (* draw_steps *) hc3_entry (hc3_body_draw_steps x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_keypairs.
  - (* draw_u64 *) hc3_entry (hc3_body_draw_u64 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_keypairs.
  - (* draw_boottime *) hc3_entry (hc3_body_draw_boottime x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_keypairs.
  - (* m_hash2 *) hc3_entry (hc3_body_m_hash2 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_keypairs.
  - (* m_hmac *) hc3_entry (hc3_body_m_hmac x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_keypairs.
  - (* m_kdf *) hc3_entry (hc3_body_m_kdf x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_keypairs.
  - (* m_transport *) hc3_entry (hc3_body_m_transport_keypairs x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_keypairs.
  - (* setup_device *) hc3_entry (hc3_body_setup_device x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_keypairs.
  - (* setup_peer *) hc3_entry (hc3_body_setup_peer x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_keypairs.
  - (* table_has *) hc3_entry (hc3_body_table_has x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_keypairs.
  - (* table_index_unique *) hc3_entry (hc3_body_table_index_unique x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_keypairs.
  - (* table_len *) hc3_entry (hc3_body_table_len x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_keypairs.
  - (* hs_take *) hc3_entry (hc3_body_hs_take x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSkh_keypairs.
  - (* hs_same *) hc3_entry (hc3_body_hs_same x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSkh_keypairs.
  - (* hs_zeroed_from *) hc3_entry (hc3_body_hs_zeroed_from x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSkh_keypairs.
  - (* draw_hs_state *) hc3_entry (hc3_body_draw_hs_state x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_keypairs.
Qed.

Lemma hc3_piece_create_any: piece_ok [u_h_create_any] (hc_imports3s x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
  (hc_G3_create_any x25519 aead_enc aead_dec).
Proof.
  rewrite hc3_G3_create_any_eq. split.
  { apply compute_list_norepet_e. reflexivity. }
  repeat apply Forall_cons; try apply Forall_nil.
  - (* check_failed *) hc3_entry (hc3_body_check_failed x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_create_any.
  - (* bytes_eq *) hc3_entry (hc3_body_bytes_eq x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_create_any.
  - (* bytes_zero *) hc3_entry (hc3_body_bytes_zero x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_create_any.
  - (* bytes_copy *) hc3_entry (hc3_body_bytes_copy x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_create_any.
  - (* bytes_set *) hc3_entry (hc3_body_bytes_set x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_create_any.
  - (* draw_steps *) hc3_entry (hc3_body_draw_steps x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_create_any.
  - (* draw_u64 *) hc3_entry (hc3_body_draw_u64 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_create_any.
  - (* draw_boottime *) hc3_entry (hc3_body_draw_boottime x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_create_any.
  - (* le32_store *) hc3_entry (hc3_body_le32_store x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_create_any.
  - (* m_hash2 *) hc3_entry (hc3_body_m_hash2 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_create_any.
  - (* m_hmac *) hc3_entry (hc3_body_m_hmac x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_create_any.
  - (* m_kdf *) hc3_entry (hc3_body_m_kdf x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_create_any.
  - (* m_dh *) hc3_entry (hc3_body_m_dh x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_create_any.
  - (* m_clamp *) hc3_entry (hc3_body_m_clamp x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_create_any.
  - (* m_identity_of *) hc3_entry (hc3_body_m_identity_of_create_any x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSki_create_any.
  - (* m_start *) hc3_entry (hc3_body_m_start_create_any x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_create_any.
  - (* m_mix_hash *) hc3_entry (hc3_body_m_mix_hash x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_create_any.
  - (* m_mix_ck *) hc3_entry (hc3_body_m_mix_ck x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_create_any.
  - (* m_mix_key *) hc3_entry (hc3_body_m_mix_key x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_create_any.
  - (* m_mix_psk *) hc3_entry (hc3_body_m_mix_psk x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_create_any.
  - (* m_encrypt_and_hash *) hc3_entry (hc3_body_m_encrypt_and_hash x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_create_any.
  - (* m_tai64n *) hc3_entry (hc3_body_m_tai64n x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_create_any.
  - (* setup_device *) hc3_entry (hc3_body_setup_device x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_create_any.
  - (* setup_peer *) hc3_entry (hc3_body_setup_peer x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_create_any.
  - (* m_precomputed *) hc3_entry (hc3_body_m_precomputed x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSki_create_any.
  - (* table_has *) hc3_entry (hc3_body_table_has x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_create_any.
  - (* table_index_unique *) hc3_entry (hc3_body_table_index_unique x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_create_any.
  - (* table_len *) hc3_entry (hc3_body_table_len x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_create_any.
  - (* hs_take *) hc3_entry (hc3_body_hs_take x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSkh_create_any.
  - (* hs_same *) hc3_entry (hc3_body_hs_same x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSkh_create_any.
  - (* draw_hs_state *) hc3_entry (hc3_body_draw_hs_state x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_create_any.
  - (* init_img *) hc3_entry (hc3_body_init_img x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSmi_create_any.
  - (* resp_img *) hc3_entry (hc3_body_resp_img x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSmr_create_any.
  - (* fill_init *) hc3_entry (hc3_body_fill_init x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSmi_create_any.
  - (* fill_resp *) hc3_entry (hc3_body_fill_resp x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSmr_create_any.
  - (* draw_real_clock *) hc3_entry (hc3_body_draw_real_clock x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_create_any.
  - (* hs_randomize *) hc3_entry (hc3_body_hs_randomize x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_create_any.
Qed.

Lemma hc3_piece_handshake: piece_ok [u_h_handshake] (hc_imports3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
  (hc_G3_handshake x25519 aead_enc aead_dec).
Proof.
  rewrite hc3_G3_handshake_eq. split.
  { apply compute_list_norepet_e. reflexivity. }
  repeat apply Forall_cons; try apply Forall_nil.
  - (* check_failed *) hc3_entry (hc3_body_check_failed x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_handshake.
  - (* bytes_eq *) hc3_entry (hc3_body_bytes_eq x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_handshake.
  - (* bytes_zero *) hc3_entry (hc3_body_bytes_zero x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_handshake.
  - (* bytes_copy *) hc3_entry (hc3_body_bytes_copy x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_handshake.
  - (* bytes_set *) hc3_entry (hc3_body_bytes_set x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_handshake.
  - (* draw_u64 *) hc3_entry (hc3_body_draw_u64 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_handshake.
  - (* draw_boottime *) hc3_entry (hc3_body_draw_boottime x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_handshake.
  - (* le32_store *) hc3_entry (hc3_body_le32_store x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_handshake.
  - (* m_hash2 *) hc3_entry (hc3_body_m_hash2 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_handshake.
  - (* m_hmac *) hc3_entry (hc3_body_m_hmac x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_handshake.
  - (* m_kdf *) hc3_entry (hc3_body_m_kdf x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_handshake.
  - (* m_dh *) hc3_entry (hc3_body_m_dh x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_handshake.
  - (* m_clamp *) hc3_entry (hc3_body_m_clamp x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_handshake.
  - (* m_identity_of *) hc3_entry (hc3_body_m_identity_of_handshake x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSki_handshake.
  - (* m_start *) hc3_entry (hc3_body_m_start_handshake x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_handshake.
  - (* m_mix_hash *) hc3_entry (hc3_body_m_mix_hash x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_handshake.
  - (* m_mix_ck *) hc3_entry (hc3_body_m_mix_ck x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_handshake.
  - (* m_mix_key *) hc3_entry (hc3_body_m_mix_key x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_handshake.
  - (* m_mix_psk *) hc3_entry (hc3_body_m_mix_psk x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_handshake.
  - (* m_encrypt_and_hash *) hc3_entry (hc3_body_m_encrypt_and_hash x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_handshake.
  - (* m_decrypt_and_hash *) hc3_entry (hc3_body_m_decrypt_and_hash x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_handshake.
  - (* m_tai64n *) hc3_entry (hc3_body_m_tai64n x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_handshake.
  - (* m_create_initiation *) hc3_entry (hc3_body_m_create_initiation_handshake x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSkinit_handshake.
  - (* m_consume_initiation_1 *) hc3_entry (hc3_body_m_consume_initiation_1 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD WgNoise.harness.x_handshake.code._x_handshake__M_CONSTRUCTION WgNoise.harness.x_handshake.code._x_handshake__M_IDENTIFIER) hc3_cs_CSkci_handshake.
  - (* m_consume_initiation_2 *) hc3_entry (hc3_body_m_consume_initiation_2 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSkci_handshake.
  - (* m_create_response *) hc3_entry (hc3_body_m_create_response_handshake x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSkresp_handshake.
  - (* m_consume_response *) hc3_entry (hc3_body_m_consume_response x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_handshake.
  - (* m_transport *) hc3_entry (hc3_body_m_transport_handshake x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_handshake.
  - (* m_label_key *) hc3_entry (hc3_body_m_label_key x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_handshake.
  - (* m_mac *) hc3_entry (hc3_body_m_mac x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_handshake.
  - (* setup_device *) hc3_entry (hc3_body_setup_device x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_handshake.
  - (* setup_peer *) hc3_entry (hc3_body_setup_peer x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_handshake.
  - (* m_precomputed *) hc3_entry (hc3_body_m_precomputed x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSki_handshake.
  - (* table_has *) hc3_entry (hc3_body_table_has x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_handshake.
  - (* table_index_unique *) hc3_entry (hc3_body_table_index_unique x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_handshake.
  - (* table_len *) hc3_entry (hc3_body_table_len x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_handshake.
  - (* hs_take *) hc3_entry (hc3_body_hs_take x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSkh_handshake.
  - (* hs_same *) hc3_entry (hc3_body_hs_same x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSkh_handshake.
  - (* hs_zeroed_from *) hc3_entry (hc3_body_hs_zeroed_from x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSkh_handshake.
  - (* m_static_public_field *) hc3_entry (hc3_body_m_static_public_field x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSki_handshake.
  - (* init_img *) hc3_entry (hc3_body_init_img x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSmi_handshake.
  - (* resp_img *) hc3_entry (hc3_body_resp_img x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSmr_handshake.
  - (* fill_init *) hc3_entry (hc3_body_fill_init x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSmi_handshake.
  - (* fill_resp *) hc3_entry (hc3_body_fill_resp x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSmr_handshake.
  - (* draw_real_clock *) hc3_entry (hc3_body_draw_real_clock x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_handshake.
  - (* m_ts_newer *) hc3_entry (hc3_body_m_ts_newer x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_handshake.
  - (* m_not_flood *) hc3_entry (hc3_body_m_not_flood x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_handshake.
  - (* m_last_consumption *) hc3_entry (hc3_body_m_last_consumption x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_handshake.
Qed.

Lemma hc3_piece_replay: piece_ok [u_h_replay] (hc_imports3s x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
  (hc_G3_replay x25519 aead_enc aead_dec).
Proof.
  rewrite hc3_G3_replay_eq. split.
  { apply compute_list_norepet_e. reflexivity. }
  repeat apply Forall_cons; try apply Forall_nil.
  - (* check_failed *) hc3_entry (hc3_body_check_failed x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_replay.
  - (* bytes_eq *) hc3_entry (hc3_body_bytes_eq x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_replay.
  - (* bytes_zero *) hc3_entry (hc3_body_bytes_zero x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_replay.
  - (* bytes_copy *) hc3_entry (hc3_body_bytes_copy x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_replay.
  - (* bytes_set *) hc3_entry (hc3_body_bytes_set x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_replay.
  - (* draw_steps *) hc3_entry (hc3_body_draw_steps x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_replay.
  - (* draw_u64 *) hc3_entry (hc3_body_draw_u64 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_replay.
  - (* draw_boottime *) hc3_entry (hc3_body_draw_boottime x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_replay.
  - (* m_hash2 *) hc3_entry (hc3_body_m_hash2 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_replay.
  - (* m_hmac *) hc3_entry (hc3_body_m_hmac x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_replay.
  - (* m_kdf *) hc3_entry (hc3_body_m_kdf x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_replay.
  - (* m_dh *) hc3_entry (hc3_body_m_dh x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_replay.
  - (* m_clamp *) hc3_entry (hc3_body_m_clamp x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_replay.
  - (* m_identity_of *) hc3_entry (hc3_body_m_identity_of_replay x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSki_replay.
  - (* m_start *) hc3_entry (hc3_body_m_start_replay x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_replay.
  - (* m_mix_hash *) hc3_entry (hc3_body_m_mix_hash x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_replay.
  - (* m_mix_ck *) hc3_entry (hc3_body_m_mix_ck x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_replay.
  - (* m_mix_key *) hc3_entry (hc3_body_m_mix_key x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_replay.
  - (* m_decrypt_and_hash *) hc3_entry (hc3_body_m_decrypt_and_hash x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_replay.
  - (* m_consume_initiation_1 *) hc3_entry (hc3_body_m_consume_initiation_1 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD WgNoise.harness.x_replay.code._x_replay__M_CONSTRUCTION WgNoise.harness.x_replay.code._x_replay__M_IDENTIFIER) hc3_cs_CSkci_replay.
  - (* m_consume_initiation_2 *) hc3_entry (hc3_body_m_consume_initiation_2 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSkci_replay.
  - (* setup_device *) hc3_entry (hc3_body_setup_device x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_replay.
  - (* setup_peer *) hc3_entry (hc3_body_setup_peer x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_replay.
  - (* m_precomputed *) hc3_entry (hc3_body_m_precomputed x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSki_replay.
  - (* hs_take *) hc3_entry (hc3_body_hs_take x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSkh_replay.
  - (* hs_same *) hc3_entry (hc3_body_hs_same x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSkh_replay.
  - (* fill_init *) hc3_entry (hc3_body_fill_init x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSmi_replay.
  - (* draw_real_clock *) hc3_entry (hc3_body_draw_real_clock x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_replay.
  - (* m_ts_newer *) hc3_entry (hc3_body_m_ts_newer x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_replay.
  - (* m_not_flood *) hc3_entry (hc3_body_m_not_flood x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_replay.
  - (* m_last_consumption *) hc3_entry (hc3_body_m_last_consumption x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_replay.
Qed.

Lemma hc3_piece_cookie_mac: piece_ok [u_h_cookie_mac] (hc_imports3s x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
  (hc_G3_cookie_mac x25519 aead_enc aead_dec).
Proof.
  rewrite hc3_G3_cookie_mac_eq. split.
  { apply compute_list_norepet_e. reflexivity. }
  repeat apply Forall_cons; try apply Forall_nil.
  - (* check_failed *) hc3_entry (hc3_body_check_failed x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_mac.
  - (* bytes_eq *) hc3_entry (hc3_body_bytes_eq x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_mac.
  - (* bytes_zero *) hc3_entry (hc3_body_bytes_zero x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_mac.
  - (* bytes_copy *) hc3_entry (hc3_body_bytes_copy x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_mac.
  - (* bytes_set *) hc3_entry (hc3_body_bytes_set x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_mac.
  - (* draw_size *) hc3_entry (hc3_body_draw_size x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_mac.
  - (* draw_u64 *) hc3_entry (hc3_body_draw_u64 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_mac.
  - (* draw_boottime *) hc3_entry (hc3_body_draw_boottime x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_mac.
  - (* m_hash2 *) hc3_entry (hc3_body_m_hash2 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_mac.
  - (* m_dh *) hc3_entry (hc3_body_m_dh x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_mac.
  - (* m_clamp *) hc3_entry (hc3_body_m_clamp x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_mac.
  - (* m_identity_of *) hc3_entry (hc3_body_m_identity_of_cookie_mac x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSki_cookie_mac.
  - (* m_label_key *) hc3_entry (hc3_body_m_label_key x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_mac.
  - (* m_mac *) hc3_entry (hc3_body_m_mac x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_mac.
  - (* setup_device *) hc3_entry (hc3_body_setup_device x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_mac.
  - (* setup_peer *) hc3_entry (hc3_body_setup_peer x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_mac.
  - (* ck_take *) hc3_entry (hc3_body_ck_take x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSkck_cookie_mac.
Qed.

Lemma hc3_piece_consume_initiation_any: piece_ok [u_h_consume_initiation_any] (hc_imports3s x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
  (hc_G3_consume_initiation_any x25519 aead_enc aead_dec).
Proof.
  rewrite hc3_G3_consume_initiation_any_eq. split.
  { apply compute_list_norepet_e. reflexivity. }
  repeat apply Forall_cons; try apply Forall_nil.
  - (* check_failed *) hc3_entry (hc3_body_check_failed x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_initiation_any.
  - (* bytes_eq *) hc3_entry (hc3_body_bytes_eq x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_initiation_any.
  - (* bytes_zero *) hc3_entry (hc3_body_bytes_zero x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_initiation_any.
  - (* bytes_copy *) hc3_entry (hc3_body_bytes_copy x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_initiation_any.
  - (* bytes_set *) hc3_entry (hc3_body_bytes_set x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_initiation_any.
  - (* draw_steps *) hc3_entry (hc3_body_draw_steps x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_initiation_any.
  - (* draw_u64 *) hc3_entry (hc3_body_draw_u64 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_initiation_any.
  - (* draw_boottime *) hc3_entry (hc3_body_draw_boottime x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_initiation_any.
  - (* le32_store *) hc3_entry (hc3_body_le32_store x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_initiation_any.
  - (* m_hash2 *) hc3_entry (hc3_body_m_hash2 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_initiation_any.
  - (* m_hmac *) hc3_entry (hc3_body_m_hmac x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_initiation_any.
  - (* m_kdf *) hc3_entry (hc3_body_m_kdf x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_initiation_any.
  - (* m_dh *) hc3_entry (hc3_body_m_dh x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_initiation_any.
  - (* m_clamp *) hc3_entry (hc3_body_m_clamp x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_initiation_any.
  - (* m_identity_of *) hc3_entry (hc3_body_m_identity_of_consume_initiation_any x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSki_consume_initiation_any.
  - (* m_start *) hc3_entry (hc3_body_m_start_consume_initiation_any x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_consume_initiation_any.
  - (* m_mix_hash *) hc3_entry (hc3_body_m_mix_hash x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_consume_initiation_any.
  - (* m_mix_ck *) hc3_entry (hc3_body_m_mix_ck x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_consume_initiation_any.
  - (* m_mix_key *) hc3_entry (hc3_body_m_mix_key x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_consume_initiation_any.
  - (* m_encrypt_and_hash *) hc3_entry (hc3_body_m_encrypt_and_hash x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_consume_initiation_any.
  - (* m_decrypt_and_hash *) hc3_entry (hc3_body_m_decrypt_and_hash x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_consume_initiation_any.
  - (* m_tai64n *) hc3_entry (hc3_body_m_tai64n x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_initiation_any.
  - (* m_create_initiation *) hc3_entry (hc3_body_m_create_initiation_consume_initiation_any x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSkinit_consume_initiation_any.
  - (* m_consume_initiation_1 *) hc3_entry (hc3_body_m_consume_initiation_1 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_CONSTRUCTION WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_IDENTIFIER) hc3_cs_CSkci_consume_initiation_any.
  - (* m_consume_initiation_2 *) hc3_entry (hc3_body_m_consume_initiation_2 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSkci_consume_initiation_any.
  - (* setup_device *) hc3_entry (hc3_body_setup_device x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_initiation_any.
  - (* setup_peer *) hc3_entry (hc3_body_setup_peer x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_initiation_any.
  - (* m_precomputed *) hc3_entry (hc3_body_m_precomputed x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSki_consume_initiation_any.
  - (* hs_take *) hc3_entry (hc3_body_hs_take x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSkh_consume_initiation_any.
  - (* hs_same *) hc3_entry (hc3_body_hs_same x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSkh_consume_initiation_any.
  - (* draw_hs_state *) hc3_entry (hc3_body_draw_hs_state x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_initiation_any.
  - (* init_img *) hc3_entry (hc3_body_init_img x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSmi_consume_initiation_any.
  - (* fill_init *) hc3_entry (hc3_body_fill_init x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSmi_consume_initiation_any.
  - (* draw_real_clock *) hc3_entry (hc3_body_draw_real_clock x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_initiation_any.
  - (* m_ts_newer *) hc3_entry (hc3_body_m_ts_newer x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_initiation_any.
  - (* m_not_flood *) hc3_entry (hc3_body_m_not_flood x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_initiation_any.
  - (* m_last_consumption *) hc3_entry (hc3_body_m_last_consumption x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_initiation_any.
  - (* hs_randomize *) hc3_entry (hc3_body_hs_randomize x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_initiation_any.
Qed.

Lemma hc3_piece_consume_response_any: piece_ok [u_h_consume_response_any] (hc_imports3s x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
  (hc_G3_consume_response_any x25519 aead_enc aead_dec).
Proof.
  rewrite hc3_G3_consume_response_any_eq. split.
  { apply compute_list_norepet_e. reflexivity. }
  repeat apply Forall_cons; try apply Forall_nil.
  - (* check_failed *) hc3_entry (hc3_body_check_failed x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_response_any.
  - (* bytes_eq *) hc3_entry (hc3_body_bytes_eq x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_response_any.
  - (* bytes_zero *) hc3_entry (hc3_body_bytes_zero x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_response_any.
  - (* bytes_copy *) hc3_entry (hc3_body_bytes_copy x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_response_any.
  - (* bytes_set *) hc3_entry (hc3_body_bytes_set x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_response_any.
  - (* draw_steps *) hc3_entry (hc3_body_draw_steps x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_response_any.
  - (* draw_u64 *) hc3_entry (hc3_body_draw_u64 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_response_any.
  - (* draw_boottime *) hc3_entry (hc3_body_draw_boottime x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_response_any.
  - (* le32_store *) hc3_entry (hc3_body_le32_store x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_response_any.
  - (* m_hash2 *) hc3_entry (hc3_body_m_hash2 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_response_any.
  - (* m_hmac *) hc3_entry (hc3_body_m_hmac x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_response_any.
  - (* m_kdf *) hc3_entry (hc3_body_m_kdf x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_response_any.
  - (* m_dh *) hc3_entry (hc3_body_m_dh x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_response_any.
  - (* m_clamp *) hc3_entry (hc3_body_m_clamp x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_response_any.
  - (* m_identity_of *) hc3_entry (hc3_body_m_identity_of_consume_response_any x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSki_consume_response_any.
  - (* m_mix_hash *) hc3_entry (hc3_body_m_mix_hash x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_consume_response_any.
  - (* m_mix_ck *) hc3_entry (hc3_body_m_mix_ck x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_consume_response_any.
  - (* m_mix_psk *) hc3_entry (hc3_body_m_mix_psk x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_consume_response_any.
  - (* m_encrypt_and_hash *) hc3_entry (hc3_body_m_encrypt_and_hash x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_consume_response_any.
  - (* m_decrypt_and_hash *) hc3_entry (hc3_body_m_decrypt_and_hash x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_consume_response_any.
  - (* m_create_response *) hc3_entry (hc3_body_m_create_response_consume_response_any x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSkresp_consume_response_any.
  - (* m_consume_response *) hc3_entry (hc3_body_m_consume_response x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSks_consume_response_any.
  - (* setup_device *) hc3_entry (hc3_body_setup_device x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_response_any.
  - (* setup_peer *) hc3_entry (hc3_body_setup_peer x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_response_any.
  - (* hs_take *) hc3_entry (hc3_body_hs_take x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSkh_consume_response_any.
  - (* hs_same *) hc3_entry (hc3_body_hs_same x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSkh_consume_response_any.
  - (* draw_hs_state *) hc3_entry (hc3_body_draw_hs_state x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_response_any.
  - (* resp_img *) hc3_entry (hc3_body_resp_img x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSmr_consume_response_any.
  - (* fill_resp *) hc3_entry (hc3_body_fill_resp x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSmr_consume_response_any.
  - (* hs_randomize *) hc3_entry (hc3_body_hs_randomize x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_consume_response_any.
Qed.

Lemma hc3_piece_cookie_reply: piece_ok [u_h_cookie_reply] (hc_imports3s x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
  (hc_G3_cookie_reply x25519 aead_enc aead_dec).
Proof.
  rewrite hc3_G3_cookie_reply_eq. split.
  { apply compute_list_norepet_e. reflexivity. }
  repeat apply Forall_cons; try apply Forall_nil.
  - (* check_failed *) hc3_entry (hc3_body_check_failed x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_reply.
  - (* bytes_eq *) hc3_entry (hc3_body_bytes_eq x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_reply.
  - (* bytes_zero *) hc3_entry (hc3_body_bytes_zero x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_reply.
  - (* bytes_copy *) hc3_entry (hc3_body_bytes_copy x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_reply.
  - (* bytes_set *) hc3_entry (hc3_body_bytes_set x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_reply.
  - (* draw_size *) hc3_entry (hc3_body_draw_size x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_reply.
  - (* draw_steps *) hc3_entry (hc3_body_draw_steps x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_reply.
  - (* draw_u64 *) hc3_entry (hc3_body_draw_u64 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_reply.
  - (* draw_boottime *) hc3_entry (hc3_body_draw_boottime x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_reply.
  - (* le32_store *) hc3_entry (hc3_body_le32_store x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_reply.
  - (* m_hash2 *) hc3_entry (hc3_body_m_hash2 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_reply.
  - (* m_dh *) hc3_entry (hc3_body_m_dh x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_reply.
  - (* m_clamp *) hc3_entry (hc3_body_m_clamp x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_reply.
  - (* m_identity_of *) hc3_entry (hc3_body_m_identity_of_cookie_reply x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSki_cookie_reply.
  - (* m_label_key *) hc3_entry (hc3_body_m_label_key x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_reply.
  - (* m_mac *) hc3_entry (hc3_body_m_mac x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_reply.
  - (* setup_device *) hc3_entry (hc3_body_setup_device x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_reply.
  - (* setup_peer *) hc3_entry (hc3_body_setup_peer x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSk_cookie_reply.
  - (* hs_take *) hc3_entry (hc3_body_hs_take x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSkh_cookie_reply.
  - (* hs_same *) hc3_entry (hc3_body_hs_same x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSkh_cookie_reply.
  - (* ck_take *) hc3_entry (hc3_body_ck_take x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_CSkck_cookie_reply.
  - (* ck_same *) hc3_entry (hc3_body_ck_same x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_KCS_cookie_reply.
  - (* cookie_img *) hc3_entry (hc3_body_cookie_img x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_KCS_cookie_reply.
  - (* fill_cookie_msg *) hc3_entry (hc3_body_fill_cookie_msg x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc3_cs_KCS_cookie_reply.
Qed.

End Pieces.
Theorem hc_pieces3 :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  piece_ok [u_h_keypairs] (hc_imports3s x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
    (hc_G3_keypairs x25519 aead_enc aead_dec) /\
  piece_ok [u_h_create_any] (hc_imports3s x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
    (hc_G3_create_any x25519 aead_enc aead_dec) /\
  piece_ok [u_h_handshake] (hc_imports3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
    (hc_G3_handshake x25519 aead_enc aead_dec) /\
  piece_ok [u_h_replay] (hc_imports3s x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
    (hc_G3_replay x25519 aead_enc aead_dec) /\
  piece_ok [u_h_cookie_mac] (hc_imports3s x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
    (hc_G3_cookie_mac x25519 aead_enc aead_dec) /\
  piece_ok [u_h_consume_initiation_any] (hc_imports3s x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
    (hc_G3_consume_initiation_any x25519 aead_enc aead_dec) /\
  piece_ok [u_h_consume_response_any] (hc_imports3s x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
    (hc_G3_consume_response_any x25519 aead_enc aead_dec) /\
  piece_ok [u_h_cookie_reply] (hc_imports3s x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
    (hc_G3_cookie_reply x25519 aead_enc aead_dec).
Proof.
  intros x25519 aead_enc aead_dec xaead_enc xaead_dec CSw X A XA.
  exact (conj (hc3_piece_keypairs x25519 aead_enc aead_dec xaead_enc xaead_dec CSw X A XA)
        (conj (hc3_piece_create_any x25519 aead_enc aead_dec xaead_enc xaead_dec CSw X A XA)
        (conj (hc3_piece_handshake x25519 aead_enc aead_dec xaead_enc xaead_dec CSw X A XA)
        (conj (hc3_piece_replay x25519 aead_enc aead_dec xaead_enc xaead_dec CSw X A XA)
        (conj (hc3_piece_cookie_mac x25519 aead_enc aead_dec xaead_enc xaead_dec CSw X A XA)
        (conj (hc3_piece_consume_initiation_any x25519 aead_enc aead_dec xaead_enc xaead_dec CSw X A XA)
        (conj (hc3_piece_consume_response_any x25519 aead_enc aead_dec xaead_enc xaead_dec CSw X A XA)
              (hc3_piece_cookie_reply x25519 aead_enc aead_dec xaead_enc xaead_dec CSw X A XA)))))))).
Qed.
