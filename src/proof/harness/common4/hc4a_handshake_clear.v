(* the common.h piece of law handshake_clear.  Its unit has NO struct
   blake2s_ctx (handshake_clear.c never hashes), so the bodies are taken at the compspecs without it (hc4a_nb_cs.v): the
   v1 bodies ported (hc4a_nb_loops / draws / setup / table / ck), the v2 ones from hc4a_nb_<group>.v. *)

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
Require Import WgNoise.proof.harness.common4.hc4a_nb_cs WgNoise.proof.harness.common4.hc4a_nb_ctx.

Require Import WgNoise.proof.harness.common4.hc4a_nb_loops WgNoise.proof.harness.common4.hc4a_nb_draws
  WgNoise.proof.harness.common4.hc4a_nb_setup WgNoise.proof.harness.common4.hc4a_nb_table WgNoise.proof.harness.common4.hc4a_nb_ck.
Require Import WgNoise.proof.harness.common4.hc4a_nb_snap WgNoise.proof.harness.common4.hc4a_nb_hs
  WgNoise.proof.harness.common4.hc4a_nb_hnodes WgNoise.proof.harness.common4.hc4a_nb_kents.

Lemma hc4a_cs_CS4nb_handshake_clear: cspecs_sub CS4nb (u_cs u_h4_handshake_clear).
Proof. hc4a_cssub. Qed.

Lemma hc4a_cs_CS4snb_handshake_clear: cspecs_sub CS4snb (u_cs u_h4_handshake_clear).
Proof. hc4a_cssub. Qed.

Lemma hc4a_cs_CSkcknb_handshake_clear: cspecs_sub CSkcknb (u_cs u_h4_handshake_clear).
Proof. hc4a_cssub. Qed.

Lemma hc4a_cs_CSkhnb_handshake_clear: cspecs_sub CSkhnb (u_cs u_h4_handshake_clear).
Proof. hc4a_cssub. Qed.

Lemma hc4a_cs_CSknb_handshake_clear: cspecs_sub CSknb (u_cs u_h4_handshake_clear).
Proof. hc4a_cssub. Qed.

Lemma hc4a_G_handshake_clear_eq x25519 aead_enc aead_dec CSw: hc4_G_handshake_clear x25519 aead_enc aead_dec CSw =
  [(check_failed_spec);
   (bytes_eq_spec);
   (bytes_zero_spec);
   (bytes_copy_spec);
   (bytes_set_spec);
   (draw_steps_spec);
   (draw_u64_spec);
   (draw_boottime_spec);
   (setup_device4_spec x25519);
   (setup_peer_spec x25519);
   (table_has_spec);
   (table_len_spec);
   (hs_take4_spec);
   (hs_zeroed_from4_spec CSw);
   (ck_take_spec);
   (ck_same_spec);
   (pr_take4_spec);
   (pr_same_but_cookie4_spec CSw);
   (pr_same4_spec CSw);
   (draw_hs_state_spec);
   (hs_randomize4_spec);
   (draw_peer_refs4_spec);
   (hnodes_snap4_spec CSw);
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
   (kents_same_but_next4_spec CSw);
   (kents_hashed4_spec CSw);
   (kents_free4_spec CSw);
   (hs_same_but_next4_spec CSw)].
Proof. reflexivity. Qed.

Lemma hc4a_piece_handshake_clear: hc4_piece_stmt_handshake_clear.
Proof.
  destruct hc4a_nb_bodies_snap as [Hpr_take [Hpr_same_but_cookie [Hpr_same [Hdev_take [Hdev_same [Hshim_take
    [Hshim_no_warning [Hshim_same [Hpeer_randomize_rest Hdraw_peer_refs]]]]]]]]].
  destruct hc4a_nb_bodies_hs as [Hhs_take [Hhs_zeroed_from [Hhs_same_but_next [Hhs_randomize Hsetup_device]]]].
  destruct hc4a_nb_bodies_hnodes as [Hhnodes_add [Hhnodes_snap [Hhnodes_free Hhnodes_pick]]].
  destruct hc4a_nb_bodies_kents as [Hkents_add [Hkents_snap [Hkent_same_but_next [Hkents_same_but_next
    [Hkents_hashed Hkents_free]]]]].
  intros x25519 aead_enc aead_dec xaead_enc xaead_dec CSw X25519 AEAD XAEAD HCS4.
  rewrite hc4a_G_handshake_clear_eq. split.
  { apply compute_list_norepet_e. reflexivity. }
  repeat apply Forall_cons; try apply Forall_nil.
  - (* check_failed *) hc4a_entry (hc4nb_body_check_failed x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSknb_handshake_clear.
  - (* bytes_eq *) hc4a_entry (hc4nb_body_bytes_eq x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSknb_handshake_clear.
  - (* bytes_zero *) hc4a_entry (hc4nb_body_bytes_zero x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSknb_handshake_clear.
  - (* bytes_copy *) hc4a_entry (hc4nb_body_bytes_copy x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSknb_handshake_clear.
  - (* bytes_set *) hc4a_entry (hc4nb_body_bytes_set x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSknb_handshake_clear.
  - (* draw_steps *) hc4a_entry (hc4nb_body_draw_steps x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSknb_handshake_clear.
  - (* draw_u64 *) hc4a_entry (hc4nb_body_draw_u64 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSknb_handshake_clear.
  - (* draw_boottime *) hc4a_entry (hc4nb_body_draw_boottime x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSknb_handshake_clear.
  - (* setup_device *) hc4a_entry (Hsetup_device x25519) hc4a_cs_CSknb_handshake_clear.
  - (* setup_peer *) hc4a_entry (hc4nb_body_setup_peer x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSknb_handshake_clear.
  - (* table_has *) hc4a_entry (hc4nb_body_table_has x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSknb_handshake_clear.
  - (* table_len *) hc4a_entry (hc4nb_body_table_len x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSknb_handshake_clear.
  - (* hs_take *) hc4a_entry Hhs_take hc4a_cs_CSkhnb_handshake_clear.
  - (* hs_zeroed_from *) hc4a_entry (Hhs_zeroed_from CSw) hc4a_cs_CSkhnb_handshake_clear.
  - (* ck_take *) hc4a_entry (hc4nb_body_ck_take x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSkcknb_handshake_clear.
  - (* ck_same *) hc4a_entry (hc4nb_body_ck_same x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSkcknb_handshake_clear.
  - (* pr_take *) hc4a_entry Hpr_take hc4a_cs_CS4nb_handshake_clear.
  - (* pr_same_but_cookie *) hc4a_entry (Hpr_same_but_cookie CSw) hc4a_cs_CS4nb_handshake_clear.
  - (* pr_same *) hc4a_entry (Hpr_same CSw) hc4a_cs_CS4nb_handshake_clear.
  - (* draw_hs_state *) hc4a_entry (hc4nb_body_draw_hs_state x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD) hc4a_cs_CSknb_handshake_clear.
  - (* hs_randomize *) hc4a_entry Hhs_randomize hc4a_cs_CSknb_handshake_clear.
  - (* draw_peer_refs *) hc4a_entry Hdraw_peer_refs hc4a_cs_CSknb_handshake_clear.
  - (* hnodes_snap *) hc4a_entry (Hhnodes_snap CSw) hc4a_cs_CS4nb_handshake_clear.
  - (* hnodes_free *) hc4a_entry (Hhnodes_free CSw HCS4) hc4a_cs_CS4nb_handshake_clear.
  - (* hnodes_add *) hc4a_entry (Hhnodes_add x25519 CSw HCS4) hc4a_cs_CS4nb_handshake_clear.
  - (* peer_randomize_rest *) hc4a_entry Hpeer_randomize_rest hc4a_cs_CSknb_handshake_clear.
  - (* hnodes_pick *) hc4a_entry (Hhnodes_pick CSw) hc4a_cs_CS4nb_handshake_clear.
  - (* dev_take *) hc4a_entry Hdev_take hc4a_cs_CS4nb_handshake_clear.
  - (* dev_same *) hc4a_entry (Hdev_same CSw) hc4a_cs_CS4nb_handshake_clear.
  - (* shim_take *) hc4a_entry Hshim_take hc4a_cs_CS4snb_handshake_clear.
  - (* shim_no_warning *) hc4a_entry Hshim_no_warning hc4a_cs_CS4snb_handshake_clear.
  - (* shim_same *) hc4a_entry Hshim_same hc4a_cs_CS4snb_handshake_clear.
  - (* kents_add *) hc4a_entry (Hkents_add CSw HCS4) hc4a_cs_CS4nb_handshake_clear.
  - (* kents_snap *) hc4a_entry (Hkents_snap CSw) hc4a_cs_CS4nb_handshake_clear.
  - (* kent_same_but_next *) hc4a_entry (Hkent_same_but_next CSw) hc4a_cs_CS4nb_handshake_clear.
  - (* kents_same_but_next *) hc4a_entry (Hkents_same_but_next CSw) hc4a_cs_CS4nb_handshake_clear.
  - (* kents_hashed *) hc4a_entry (Hkents_hashed CSw) hc4a_cs_CS4nb_handshake_clear.
  - (* kents_free *) hc4a_entry (Hkents_free CSw HCS4) hc4a_cs_CS4nb_handshake_clear.
  - (* hs_same_but_next *) hc4a_entry (Hhs_same_but_next CSw) hc4a_cs_CSkhnb_handshake_clear.
Qed.
