(* the harness-common pieces: for each protocol law, the common.h functions its
   harness unit contains, with their specifications (hc_specs3.v), proved in the law's harness unit.

   hc_piece3_<law> (hc_bodies3.v): piece_ok [u_h_<law>] (hc_imports3 ...) (hc_G3_<law> ...).
   The law's own piece (main and the harness's local functions) imports hc_G3_<law>. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import QuickProof.Env.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.blake2s.b2s_spec3.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_prog3.
Require Export WgNoise.proof.harness.common.hc_model3.
Require Export WgNoise.proof.harness.common.hc_specs3.
Require WgNoise.contracts.x_consume_initiation_any WgNoise.contracts.x_consume_response_any
        WgNoise.contracts.x_cookie_mac WgNoise.contracts.x_cookie_reply WgNoise.contracts.x_create_any
        WgNoise.contracts.x_handshake WgNoise.contracts.x_keypairs WgNoise.contracts.x_replay.
Require WgNoise.harness.x_consume_initiation_any.code WgNoise.harness.x_consume_response_any.code
        WgNoise.harness.x_cookie_mac.code WgNoise.harness.x_cookie_reply.code WgNoise.harness.x_create_any.code
        WgNoise.harness.x_handshake.code WgNoise.harness.x_keypairs.code WgNoise.harness.x_replay.code.

(* the harness units *)
Definition u_h_consume_initiation_any := mk_unit WgNoise.contracts.x_consume_initiation_any.Harness.CS
  (QPvarspecs WgNoise.contracts.x_consume_initiation_any.Harness.qp) WgNoise.harness.x_consume_initiation_any.code.prog.
Definition u_h_consume_response_any := mk_unit WgNoise.contracts.x_consume_response_any.Harness.CS
  (QPvarspecs WgNoise.contracts.x_consume_response_any.Harness.qp) WgNoise.harness.x_consume_response_any.code.prog.
Definition u_h_cookie_mac := mk_unit WgNoise.contracts.x_cookie_mac.Harness.CS
  (QPvarspecs WgNoise.contracts.x_cookie_mac.Harness.qp) WgNoise.harness.x_cookie_mac.code.prog.
Definition u_h_cookie_reply := mk_unit WgNoise.contracts.x_cookie_reply.Harness.CS
  (QPvarspecs WgNoise.contracts.x_cookie_reply.Harness.qp) WgNoise.harness.x_cookie_reply.code.prog.
Definition u_h_create_any := mk_unit WgNoise.contracts.x_create_any.Harness.CS
  (QPvarspecs WgNoise.contracts.x_create_any.Harness.qp) WgNoise.harness.x_create_any.code.prog.
Definition u_h_handshake := mk_unit WgNoise.contracts.x_handshake.Harness.CS
  (QPvarspecs WgNoise.contracts.x_handshake.Harness.qp) WgNoise.harness.x_handshake.code.prog.
Definition u_h_keypairs := mk_unit WgNoise.contracts.x_keypairs.Harness.CS
  (QPvarspecs WgNoise.contracts.x_keypairs.Harness.qp) WgNoise.harness.x_keypairs.code.prog.
Definition u_h_replay := mk_unit WgNoise.contracts.x_replay.Harness.CS
  (QPvarspecs WgNoise.contracts.x_replay.Harness.qp) WgNoise.harness.x_replay.code.prog.

Module I := WgNoise.harness.x_handshake.code.
Module IK := WgNoise.harness.x_cookie_reply.code.
Module IR := WgNoise.harness.x_consume_response_any.code.

Section HC.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

(* what the common.h functions call: the environment, the lower pieces' interfaces, the protocol piece *)
Definition hc_imports3 (cs: compspecs) : funspecs :=
  env_specs_ns CSw ++
  [@memcpy_spec cs; @memset_spec cs; @memcmp_spec cs; @calloc_spec CSw;
   @memzero_explicit_spec cs; @crypto_memneq_spec cs;
   @curve25519_generic_spec_of cs x25519;
   @chacha20poly1305_encrypt_spec_of cs aead_enc; @chacha20poly1305_decrypt_spec_of3 cs aead_dec;
   @xchacha20poly1305_encrypt_spec_of cs xaead_enc; @xchacha20poly1305_decrypt_spec_of3 cs xaead_dec] ++
  blake2s_G3 ++ prot_G3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw.

(* the laws whose unit has draw_size / draw_steps (every protocol law but handshake) also import nondet_size *)
Definition hc_imports3s (cs: compspecs) : funspecs := hc_imports3 cs ++ [nondet_size_spec].

(* every common.h specification; bp / cons / iden = the law's M_BASEPOINT / M_CONSTRUCTION / M_IDENTIFIER *)
Definition hc_G3_all (bp cons iden: ident) : funspecs :=
  [check_failed_spec; bytes_eq_spec; bytes_zero_spec; bytes_copy_spec; bytes_set_spec;
   draw_size_spec; draw_steps_spec; draw_u64_spec; draw_boottime_spec; le32_store_spec;
   m_hash2_spec; m_hmac_spec; m_kdf_spec; m_dh_spec x25519; m_clamp_spec; m_identity_of_spec x25519 bp;
   m_start_spec cons iden; m_mix_hash_spec; m_mix_ck_spec; m_mix_key_spec; m_mix_psk_spec;
   m_encrypt_and_hash_spec aead_enc; m_decrypt_and_hash_spec aead_dec; m_tai64n_spec;
   m_create_initiation_spec x25519 aead_enc bp cons iden; m_consume_initiation_1_spec x25519 aead_dec cons iden;
   m_consume_initiation_2_spec aead_dec; m_create_response_spec x25519 aead_enc bp;
   m_consume_response_spec x25519 aead_dec; m_transport_spec bp; m_label_key_spec; m_mac_spec;
   setup_device_spec x25519; setup_peer_spec x25519; m_precomputed_spec x25519;
   table_has_spec; table_index_unique_spec; table_len_spec; hs_take_spec; hs_same_spec; hs_zeroed_from_spec;
   draw_hs_state_spec; m_static_public_field_spec; init_img_spec; resp_img_spec; cookie_img_spec;
   fill_init_spec; fill_resp_spec; fill_cookie_msg_spec; draw_real_clock_spec; m_ts_newer_spec;
   m_not_flood_spec; m_last_consumption_spec; hs_randomize_spec; ck_take_spec; ck_same_spec].

(* the specifications of the functions ids, in that order *)
Fixpoint hc_select (ids: list ident) (G: funspecs) : funspecs :=
  match ids with
  | [] => []
  | i :: ids' => match find (fun x => Pos.eqb (fst x) i) G with
                 | Some x => x :: hc_select ids' G
                 | None => hc_select ids' G
                 end
  end.

Definition hc_ids_keypairs : list ident :=
  [I._check_failed; I._bytes_eq; I._bytes_zero; I._bytes_copy; I._bytes_set; IR._draw_steps; I._draw_u64;
   I._draw_boottime; I._m_hash2; I._m_hmac; I._m_kdf; I._m_transport; I._setup_device; I._setup_peer;
   I._table_has; I._table_index_unique; I._table_len; I._hs_take; I._hs_same; I._hs_zeroed_from;
   IR._draw_hs_state].

Definition hc_ids_create_any : list ident :=
  [I._check_failed; I._bytes_eq; I._bytes_zero; I._bytes_copy; I._bytes_set; IR._draw_steps; I._draw_u64;
   I._draw_boottime; I._le32_store; I._m_hash2; I._m_hmac; I._m_kdf; I._m_dh; I._m_clamp; I._m_identity_of;
   I._m_start; I._m_mix_hash; I._m_mix_ck; I._m_mix_key; I._m_mix_psk; I._m_encrypt_and_hash; I._m_tai64n;
   I._setup_device; I._setup_peer; I._m_precomputed; I._table_has; I._table_index_unique; I._table_len;
   I._hs_take; I._hs_same; IR._draw_hs_state; I._init_img; I._resp_img; I._fill_init; I._fill_resp;
   I._draw_real_clock; IR._hs_randomize].

Definition hc_ids_handshake : list ident :=
  [I._check_failed; I._bytes_eq; I._bytes_zero; I._bytes_copy; I._bytes_set; I._draw_u64; I._draw_boottime;
   I._le32_store; I._m_hash2; I._m_hmac; I._m_kdf; I._m_dh; I._m_clamp; I._m_identity_of; I._m_start;
   I._m_mix_hash; I._m_mix_ck; I._m_mix_key; I._m_mix_psk; I._m_encrypt_and_hash; I._m_decrypt_and_hash;
   I._m_tai64n; I._m_create_initiation; I._m_consume_initiation_1; I._m_consume_initiation_2;
   I._m_create_response; I._m_consume_response; I._m_transport; I._m_label_key; I._m_mac; I._setup_device;
   I._setup_peer; I._m_precomputed; I._table_has; I._table_index_unique; I._table_len; I._hs_take;
   I._hs_same; I._hs_zeroed_from; I._m_static_public_field; I._init_img; I._resp_img; I._fill_init;
   I._fill_resp; I._draw_real_clock; I._m_ts_newer; I._m_not_flood; I._m_last_consumption].

Definition hc_ids_replay : list ident :=
  [I._check_failed; I._bytes_eq; I._bytes_zero; I._bytes_copy; I._bytes_set; IR._draw_steps; I._draw_u64;
   I._draw_boottime; I._m_hash2; I._m_hmac; I._m_kdf; I._m_dh; I._m_clamp; I._m_identity_of; I._m_start;
   I._m_mix_hash; I._m_mix_ck; I._m_mix_key; I._m_decrypt_and_hash; I._m_consume_initiation_1;
   I._m_consume_initiation_2; I._setup_device; I._setup_peer; I._m_precomputed; I._hs_take; I._hs_same;
   I._fill_init; I._draw_real_clock; I._m_ts_newer; I._m_not_flood; I._m_last_consumption].

Definition hc_ids_cookie_mac : list ident :=
  [I._check_failed; I._bytes_eq; I._bytes_zero; I._bytes_copy; I._bytes_set; IK._draw_size; I._draw_u64;
   I._draw_boottime; I._m_hash2; I._m_dh; I._m_clamp; I._m_identity_of; I._m_label_key; I._m_mac;
   I._setup_device; I._setup_peer; IK._ck_take].

(* the laws with the harness's peer list (hnodes_*: specifications to come, stage 2) *)
Definition hc_ids_consume_initiation_any : list ident :=
  [I._check_failed; I._bytes_eq; I._bytes_zero; I._bytes_copy; I._bytes_set; IR._draw_steps; I._draw_u64;
   I._draw_boottime; I._le32_store; I._m_hash2; I._m_hmac; I._m_kdf; I._m_dh; I._m_clamp; I._m_identity_of;
   I._m_start; I._m_mix_hash; I._m_mix_ck; I._m_mix_key; I._m_encrypt_and_hash; I._m_decrypt_and_hash;
   I._m_tai64n; I._m_create_initiation; I._m_consume_initiation_1; I._m_consume_initiation_2;
   I._setup_device; I._setup_peer; I._m_precomputed; I._hs_take; I._hs_same; IR._draw_hs_state;
   I._init_img; I._fill_init; I._draw_real_clock; I._m_ts_newer; I._m_not_flood; I._m_last_consumption;
   IR._hs_randomize].

Definition hc_ids_consume_response_any : list ident :=
  [I._check_failed; I._bytes_eq; I._bytes_zero; I._bytes_copy; I._bytes_set; IR._draw_steps; I._draw_u64;
   I._draw_boottime; I._le32_store; I._m_hash2; I._m_hmac; I._m_kdf; I._m_dh; I._m_clamp; I._m_identity_of;
   I._m_mix_hash; I._m_mix_ck; I._m_mix_psk; I._m_encrypt_and_hash; I._m_decrypt_and_hash;
   I._m_create_response; I._m_consume_response; I._setup_device; I._setup_peer; I._hs_take; I._hs_same;
   IR._draw_hs_state; I._resp_img; I._fill_resp; IR._hs_randomize].

Definition hc_ids_cookie_reply : list ident :=
  [I._check_failed; I._bytes_eq; I._bytes_zero; I._bytes_copy; I._bytes_set; IK._draw_size; IR._draw_steps;
   I._draw_u64; I._draw_boottime; I._le32_store; I._m_hash2; I._m_dh; I._m_clamp; I._m_identity_of;
   I._m_label_key; I._m_mac; I._setup_device; I._setup_peer; I._hs_take; I._hs_same; IK._ck_take;
   IK._ck_same; IK._cookie_img; IK._fill_cookie_msg].

Definition hc_G3_keypairs := hc_select hc_ids_keypairs
  (hc_G3_all WgNoise.harness.x_keypairs.code._x_keypairs__M_BASEPOINT xH xH).
Definition hc_G3_create_any := hc_select hc_ids_create_any
  (hc_G3_all WgNoise.harness.x_create_any.code._x_create_any__M_BASEPOINT
     WgNoise.harness.x_create_any.code._x_create_any__M_CONSTRUCTION
     WgNoise.harness.x_create_any.code._x_create_any__M_IDENTIFIER).
Definition hc_G3_handshake := hc_select hc_ids_handshake
  (hc_G3_all WgNoise.harness.x_handshake.code._x_handshake__M_BASEPOINT
     WgNoise.harness.x_handshake.code._x_handshake__M_CONSTRUCTION
     WgNoise.harness.x_handshake.code._x_handshake__M_IDENTIFIER).
Definition hc_G3_replay := hc_select hc_ids_replay
  (hc_G3_all WgNoise.harness.x_replay.code._x_replay__M_BASEPOINT
     WgNoise.harness.x_replay.code._x_replay__M_CONSTRUCTION
     WgNoise.harness.x_replay.code._x_replay__M_IDENTIFIER).
Definition hc_G3_cookie_mac := hc_select hc_ids_cookie_mac
  (hc_G3_all WgNoise.harness.x_cookie_mac.code._x_cookie_mac__M_BASEPOINT xH xH).
Definition hc_G3_consume_initiation_any := hc_select hc_ids_consume_initiation_any
  (hc_G3_all WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_BASEPOINT
     WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_CONSTRUCTION
     WgNoise.harness.x_consume_initiation_any.code._x_consume_initiation_any__M_IDENTIFIER).
Definition hc_G3_consume_response_any := hc_select hc_ids_consume_response_any
  (hc_G3_all WgNoise.harness.x_consume_response_any.code._x_consume_response_any__M_BASEPOINT xH xH).
Definition hc_G3_cookie_reply := hc_select hc_ids_cookie_reply
  (hc_G3_all WgNoise.harness.x_cookie_reply.code._x_cookie_reply__M_BASEPOINT xH xH).

End HC.
