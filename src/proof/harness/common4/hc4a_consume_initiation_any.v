(* the common.h piece of law consume_initiation_any from the four body-group statements
   (hc4_pieces_of's conjunct), hc_bodies3.v's method: explicit list, one hc3_lift entry per function. *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import QuickProof.Env.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common.hc3_lift.
Require Import WgNoise.proof.harness.common.hc3_xcs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4_stmt.
Require Import WgNoise.proof.harness.common4.hc4_body_stmts.
Require Import WgNoise.proof.harness.common4.hc4a_lib.

Require Import WgNoise.proof.harness.common.hc3_body_loops WgNoise.proof.harness.common.hc3_body_draws
  WgNoise.proof.harness.common.hc3_body_sym WgNoise.proof.harness.common.hc3_body_kdf
  WgNoise.proof.harness.common.hc3_body_mix WgNoise.proof.harness.common.hc3_body_ident
  WgNoise.proof.harness.common.hc3_body_init WgNoise.proof.harness.common.hc3_body_cinit
  WgNoise.proof.harness.common.hc3_body_resp WgNoise.proof.harness.common.hc3_body_setup
  WgNoise.proof.harness.common.hc3_body_table WgNoise.proof.harness.common.hc3_body_snap
  WgNoise.proof.harness.common.hc3_body_msg WgNoise.proof.harness.common.hc3_body_ck.
Require Import WgNoise.proof.harness.common4.hc4a_lawb_ident WgNoise.proof.harness.common4.hc4a_lawb_init
  WgNoise.proof.harness.common4.hc4a_lawb_resp WgNoise.proof.harness.common4.hc4a_ck WgNoise.proof.harness.common4.hc4a_msg.

Lemma hc4a_cs_CS4_consume_initiation_any: cspecs_sub CS4 (u_cs u_h4_consume_initiation_any).
Proof. hc4a_cssub. Qed.

Lemma hc4a_cs_CS4s_consume_initiation_any: cspecs_sub CS4s (u_cs u_h4_consume_initiation_any).
Proof. hc4a_cssub. Qed.

Lemma hc4a_cs_CSk_consume_initiation_any: cspecs_sub CSk (u_cs u_h4_consume_initiation_any).
Proof. hc4a_cssub. Qed.

Lemma hc4a_cs_CSkci_consume_initiation_any: cspecs_sub CSkci (u_cs u_h4_consume_initiation_any).
Proof. hc4a_cssub. Qed.

Lemma hc4a_cs_CSkck_consume_initiation_any: cspecs_sub CSkck (u_cs u_h4_consume_initiation_any).
Proof. hc4a_cssub. Qed.

Lemma hc4a_cs_CSkh_consume_initiation_any: cspecs_sub CSkh (u_cs u_h4_consume_initiation_any).
Proof. hc4a_cssub. Qed.

Lemma hc4a_cs_CSki_consume_initiation_any: cspecs_sub CSki (u_cs u_h4_consume_initiation_any).
Proof. hc4a_cssub. Qed.

Lemma hc4a_cs_CSkinit_consume_initiation_any: cspecs_sub CSkinit (u_cs u_h4_consume_initiation_any).
Proof. hc4a_cssub. Qed.

Lemma hc4a_cs_CSks_consume_initiation_any: cspecs_sub CSks (u_cs u_h4_consume_initiation_any).
Proof. hc4a_cssub. Qed.

Lemma hc4a_cs_CSmi_consume_initiation_any: cspecs_sub CSmi (u_cs u_h4_consume_initiation_any).
Proof. hc4a_cssub. Qed.

Lemma hc4a_G_consume_initiation_any_eq x25519 aead_enc aead_dec CSw: hc4_G_consume_initiation_any x25519 aead_enc aead_dec CSw =
  [(check_failed_spec);
   (bytes_eq_spec);
   (bytes_zero_spec);
   (bytes_copy_spec);
   (bytes_set_spec);
   (draw_steps_spec);
   (draw_u64_spec);
   (draw_boottime_spec);
   (le32_store_spec);
   (m_hash2_spec);
   (m_hmac_spec);
   (m_kdf_spec);
   (m_dh_spec x25519);
   (m_clamp_spec);
   (m_identity_of_spec x25519 WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_BASEPOINT);
   (m_start_spec WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_CONSTRUCTION WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_IDENTIFIER);
   (m_mix_hash_spec);
   (m_mix_ck_spec);
   (m_mix_key_spec);
   (m_encrypt_and_hash_spec aead_enc);
   (m_decrypt_and_hash_spec aead_dec);
   (m_tai64n_spec);
   (m_create_initiation_spec x25519 aead_enc WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_BASEPOINT WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_CONSTRUCTION WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_IDENTIFIER);
   (m_consume_initiation_1_spec x25519 aead_dec WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_CONSTRUCTION WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_IDENTIFIER);
   (m_consume_initiation_2_spec aead_dec);
   (setup_device4_spec x25519);
   (setup_peer_spec x25519);
   (m_precomputed_spec x25519);
   (hs_take4_spec);
   (hs_same4_spec CSw);
   (ck_take_spec);
   (ck_same_spec);
   (pr_take4_spec);
   (pr_same_but_cookie4_spec CSw);
   (pr_same4_spec CSw);
   (draw_hs_state_spec);
   (init_img_spec);
   (fill_init_spec);
   (draw_real_clock4_spec);
   (m_ts_newer_spec);
   (m_not_flood_spec);
   (m_last_consumption_spec);
   (hs_randomize4_spec);
   (draw_peer_refs4_spec);
   (hnodes_snap4_spec CSw);
   (hnodes_same_except4_spec CSw);
   (hnodes_free4_spec CSw);
   (hnodes_add4_spec x25519 CSw);
   (peer_randomize_rest4_spec);
   (hnodes_pick4_spec CSw);
   (dev_take4_spec);
   (dev_same4_spec CSw);
   (shim_take4_spec);
   (shim_no_warning4_spec);
   (shim_same4_spec);
   (kents_add4_spec CSw);
   (kents_snap4_spec CSw);
   (kent_same_but_next4_spec CSw);
   (kents_same4_spec CSw);
   (kents_free4_spec CSw)].
Proof. reflexivity. Qed.

Lemma hc4a_piece_consume_initiation_any: hc4_bodies_snap_stmt -> hc4_bodies_hs_stmt -> hc4_bodies_hnodes_stmt -> hc4_bodies_kents_stmt ->
  hc4_piece_stmt_consume_initiation_any.
Proof.
  intros [Hpr_take [Hpr_same_but_cookie [Hpr_same [Hdev_take [Hdev_same [Hshim_take [Hshim_no_warning [Hshim_same
          [Hskb_take [Hskb_same [Hreplay_counter_fresh [Hpeer_randomize_rest [Hdraw_peer_refs Hle32_load]]]]]]]]]]]]]
         [Hhs_take [Hhs_same [Hhs_zeroed_from [Hhs_same_but_next [Hhs_randomize [Hsetup_device Hdraw_real_clock]]]]]]
         [Hhnodes_add [Hhnodes_snap [Hhnodes_same_except [Hhnodes_free Hhnodes_pick]]]]
         [Hkents_add [Hkents_snap [Hkent_same_but_next [Hkents_same [Hkents_same_but_next [Hkents_hashed Hkents_free]]]]]].
  intros x25519 aead_enc aead_dec xaead_enc xaead_dec CSw X25519 AEAD XAEAD HCS4.
  rewrite hc4a_G_consume_initiation_any_eq. split.
  { apply compute_list_norepet_e. reflexivity. }
  repeat apply Forall_cons; try apply Forall_nil.
  - (* check_failed *) hc4a_entry (hc3_body_check_failed x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSk_consume_initiation_any.
  - (* bytes_eq *) hc4a_entry (hc3_body_bytes_eq x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSk_consume_initiation_any.
  - (* bytes_zero *) hc4a_entry (hc3_body_bytes_zero x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSk_consume_initiation_any.
  - (* bytes_copy *) hc4a_entry (hc3_body_bytes_copy x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSk_consume_initiation_any.
  - (* bytes_set *) hc4a_entry (hc3_body_bytes_set x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSk_consume_initiation_any.
  - (* draw_steps *) hc4a_entry (hc3_body_draw_steps x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSk_consume_initiation_any.
  - (* draw_u64 *) hc4a_entry (hc3_body_draw_u64 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSk_consume_initiation_any.
  - (* draw_boottime *) hc4a_entry (hc3_body_draw_boottime x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSk_consume_initiation_any.
  - (* le32_store *) hc4a_entry (hc3_body_le32_store x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSk_consume_initiation_any.
  - (* m_hash2 *) hc4a_entry (hc3_body_m_hash2 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSk_consume_initiation_any.
  - (* m_hmac *) hc4a_entry (hc3_body_m_hmac x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSk_consume_initiation_any.
  - (* m_kdf *) hc4a_entry (hc3_body_m_kdf x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSk_consume_initiation_any.
  - (* m_dh *) hc4a_entry (hc3_body_m_dh x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSk_consume_initiation_any.
  - (* m_clamp *) hc4a_entry (hc3_body_m_clamp x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSk_consume_initiation_any.
  - (* m_identity_of *) hc4a_entry (hc3_body_m_identity_of_consume_initiation_any x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSki_consume_initiation_any.
  - (* m_start *) hc4a_entry (hc3_body_m_start_consume_initiation_any x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSks_consume_initiation_any.
  - (* m_mix_hash *) hc4a_entry (hc3_body_m_mix_hash x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSks_consume_initiation_any.
  - (* m_mix_ck *) hc4a_entry (hc3_body_m_mix_ck x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSks_consume_initiation_any.
  - (* m_mix_key *) hc4a_entry (hc3_body_m_mix_key x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSks_consume_initiation_any.
  - (* m_encrypt_and_hash *) hc4a_entry (hc3_body_m_encrypt_and_hash x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSks_consume_initiation_any.
  - (* m_decrypt_and_hash *) hc4a_entry (hc3_body_m_decrypt_and_hash x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSks_consume_initiation_any.
  - (* m_tai64n *) hc4a_entry (hc3_body_m_tai64n x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSk_consume_initiation_any.
  - (* m_create_initiation *) hc4a_entry (hc3_body_m_create_initiation_consume_initiation_any x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSkinit_consume_initiation_any.
  - (* m_consume_initiation_1 *) hc4a_entry (hc3_body_m_consume_initiation_1 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_CONSTRUCTION WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_IDENTIFIER) hc4a_cs_CSkci_consume_initiation_any.
  - (* m_consume_initiation_2 *) hc4a_entry (hc3_body_m_consume_initiation_2 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSkci_consume_initiation_any.
  - (* setup_device *) hc4a_entry (Hsetup_device x25519) hc4a_cs_CSk_consume_initiation_any.
  - (* setup_peer *) hc4a_entry (hc3_body_setup_peer x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSk_consume_initiation_any.
  - (* m_precomputed *) hc4a_entry (hc3_body_m_precomputed x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSki_consume_initiation_any.
  - (* hs_take *) hc4a_entry Hhs_take hc4a_cs_CSkh_consume_initiation_any.
  - (* hs_same *) hc4a_entry (Hhs_same CSw) hc4a_cs_CSkh_consume_initiation_any.
  - (* ck_take *) hc4a_entry (hc3_body_ck_take x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSkck_consume_initiation_any.
  - (* ck_same *) hc4a_entry (hc4a_body_ck_same x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSkck_consume_initiation_any.
  - (* pr_take *) hc4a_entry Hpr_take hc4a_cs_CS4_consume_initiation_any.
  - (* pr_same_but_cookie *) hc4a_entry (Hpr_same_but_cookie CSw) hc4a_cs_CS4_consume_initiation_any.
  - (* pr_same *) hc4a_entry (Hpr_same CSw) hc4a_cs_CS4_consume_initiation_any.
  - (* draw_hs_state *) hc4a_entry (hc3_body_draw_hs_state x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSk_consume_initiation_any.
  - (* init_img *) hc4a_entry (hc3_body_init_img x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSmi_consume_initiation_any.
  - (* fill_init *) hc4a_entry (hc3_body_fill_init x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSmi_consume_initiation_any.
  - (* draw_real_clock *) hc4a_entry Hdraw_real_clock hc4a_cs_CSk_consume_initiation_any.
  - (* m_ts_newer *) hc4a_entry (hc3_body_m_ts_newer x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSk_consume_initiation_any.
  - (* m_not_flood *) hc4a_entry (hc3_body_m_not_flood x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSk_consume_initiation_any.
  - (* m_last_consumption *) hc4a_entry (hc3_body_m_last_consumption x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSk_consume_initiation_any.
  - (* hs_randomize *) hc4a_entry Hhs_randomize hc4a_cs_CSk_consume_initiation_any.
  - (* draw_peer_refs *) hc4a_entry Hdraw_peer_refs hc4a_cs_CSk_consume_initiation_any.
  - (* hnodes_snap *) hc4a_entry (Hhnodes_snap CSw) hc4a_cs_CS4_consume_initiation_any.
  - (* hnodes_same_except *) hc4a_entry (Hhnodes_same_except CSw) hc4a_cs_CS4_consume_initiation_any.
  - (* hnodes_free *) hc4a_entry (Hhnodes_free CSw HCS4) hc4a_cs_CS4_consume_initiation_any.
  - (* hnodes_add *) hc4a_entry (Hhnodes_add x25519 CSw HCS4) hc4a_cs_CS4_consume_initiation_any.
  - (* peer_randomize_rest *) hc4a_entry Hpeer_randomize_rest hc4a_cs_CSk_consume_initiation_any.
  - (* hnodes_pick *) hc4a_entry (Hhnodes_pick CSw) hc4a_cs_CS4_consume_initiation_any.
  - (* dev_take *) hc4a_entry Hdev_take hc4a_cs_CS4_consume_initiation_any.
  - (* dev_same *) hc4a_entry (Hdev_same CSw) hc4a_cs_CS4_consume_initiation_any.
  - (* shim_take *) hc4a_entry Hshim_take hc4a_cs_CS4s_consume_initiation_any.
  - (* shim_no_warning *) hc4a_entry Hshim_no_warning hc4a_cs_CS4s_consume_initiation_any.
  - (* shim_same *) hc4a_entry Hshim_same hc4a_cs_CS4s_consume_initiation_any.
  - (* kents_add *) hc4a_entry (Hkents_add CSw HCS4) hc4a_cs_CS4_consume_initiation_any.
  - (* kents_snap *) hc4a_entry (Hkents_snap CSw) hc4a_cs_CS4_consume_initiation_any.
  - (* kent_same_but_next *) hc4a_entry (Hkent_same_but_next CSw) hc4a_cs_CS4_consume_initiation_any.
  - (* kents_same *) hc4a_entry (Hkents_same CSw) hc4a_cs_CS4_consume_initiation_any.
  - (* kents_free *) hc4a_entry (Hkents_free CSw HCS4) hc4a_cs_CS4_consume_initiation_any.
Qed.
