(* hc_pieces3: the function context of each common.h body proof: exactly the specifications of its callees, as they appear in every law's context
   hc_imports3 (u_cs u) ++ hc_G3_<law>, except the compspecs-polymorphic imports (curve25519_generic,
   chacha20poly1305_encrypt / decrypt, nondet_bytes), taken at the body's small compspecs (hc3_cs.v) and
   related to the law's instance by funspec_sub (hc3_xcs.v).

   Body lemma of function X (files hc3_body_*.v):
     @semax_body [] (hc3_G_X ...) CS0 f_X X_spec       (CS0 = the compspecs named below)
   with f_X the Clight of law handshake's unit (draw_steps, draw_hs_state, hs_randomize: consume_response_any's;
   draw_size, ck_take, ck_same, cookie_img, fill_cookie_msg: cookie_reply's).
   The functions that read the renamed constants (m_identity_of, m_start, m_create_initiation,
   m_create_response, m_transport) are proved per law: V0 = the constants they read. *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.blake2s.b2s_spec3.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.

Section Ctx.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variables bp cons iden: ident.

(* CS0 = CSk *)
Definition hc3_G_none : funspecs := [].   (* check_failed bytes_eq bytes_zero bytes_copy bytes_set le32_store
                                             m_clamp m_tai64n table_has table_index_unique table_len m_ts_newer
                                             m_not_flood m_last_consumption *)
Definition hc3_G_draw_size : funspecs := [nondet_size_spec].     (* draw_size, draw_steps *)
Definition hc3_G_draw_u64 : funspecs := [nondet_u32_spec].
Definition hc3_G_draw_boottime : funspecs := [draw_u64_spec].
Definition hc3_G_m_hash2 : funspecs := [blake2s_init_spec; blake2s_update_spec3; blake2s_final_spec].
Definition hc3_G_m_hmac : funspecs := [m_hash2_spec].            (* m_hmac, m_label_key *)
Definition hc3_G_m_kdf : funspecs := [bytes_copy_spec; m_hmac_spec].
Definition hc3_G_m_dh : funspecs := [bytes_zero_spec; @curve25519_generic_spec_of CSk x25519].
Definition hc3_G_m_transport : funspecs := [m_kdf_spec].
Definition hc3_G_m_mac : funspecs := [blake2s_spec3].
Definition hc3_G_setup_device : funspecs :=
  [bytes_set_spec; wg_cookie_checker_init_spec; wg_cookie_checker_precompute_device_keys_spec;
   wg_noise_set_static_identity_private_key_spec x25519].
Definition hc3_G_setup_peer : funspecs :=
  [wg_cookie_checker_precompute_peer_keys_spec; wg_cookie_init_spec; wg_noise_handshake_init_spec x25519].
Definition hc3_G_draw_hs_state : funspecs := [nondet_u8_spec].
Definition hc3_G_draw_real_clock : funspecs := [draw_u64_spec; nondet_u32_spec].
Definition hc3_G_hs_randomize : funspecs :=
  [draw_boottime_spec; draw_hs_state_spec; @asm_env.nondet_bytes_spec CSk; nondet_u32_spec].

(* CS0 = CSkh *)
Definition hc3_G_hs_take : funspecs := [bytes_copy_spec].        (* hs_take; ck_take (CSkck) *)
Definition hc3_G_hs_same : funspecs := [bytes_eq_spec].          (* hs_same; ck_same (cookie_reply's CS) *)
Definition hc3_G_hs_zeroed_from : funspecs := [bytes_eq_spec; bytes_zero_spec].

(* CS0 = CSki *)
Definition hc3_G_m_identity_of : funspecs :=
  [bytes_copy_spec; bytes_zero_spec; m_clamp_spec; m_dh_spec x25519].
Definition hc3_G_m_precomputed : funspecs := [bytes_set_spec; m_dh_spec x25519].
Definition hc3_G_m_static_public_field : funspecs := [bytes_copy_spec; bytes_set_spec; bytes_zero_spec].

(* CS0 = CSks *)
Definition hc3_G_m_start : funspecs := [m_hash2_spec].
Definition hc3_G_m_mix_hash : funspecs := [bytes_copy_spec; m_hash2_spec].
Definition hc3_G_m_mix_ck : funspecs := [bytes_copy_spec; m_kdf_spec].   (* m_mix_ck, m_mix_key *)
Definition hc3_G_m_mix_psk : funspecs := [bytes_copy_spec; m_kdf_spec; m_mix_hash_spec].
Definition hc3_G_m_encrypt_and_hash : funspecs :=
  [@chacha20poly1305_encrypt_spec_of CSks aead_enc; m_mix_hash_spec].
Definition hc3_G_m_decrypt_and_hash : funspecs :=
  [@chacha20poly1305_decrypt_spec_of3 CSks aead_dec; m_mix_hash_spec].
Definition hc3_G_m_consume_response : funspecs :=
  [bytes_copy_spec; m_decrypt_and_hash_spec aead_dec; m_dh_spec x25519; m_mix_ck_spec; m_mix_hash_spec;
   m_mix_psk_spec].

(* CS0 = CSkinit *)
Definition hc3_G_m_create_initiation : funspecs :=
  [bytes_copy_spec; bytes_zero_spec; m_clamp_spec; m_dh_spec x25519; m_encrypt_and_hash_spec aead_enc;
   m_mix_ck_spec; m_mix_hash_spec; m_mix_key_spec; m_start_spec cons iden].
(* CS0 = CSkci *)
Definition hc3_G_m_consume_initiation_1 : funspecs :=
  [m_decrypt_and_hash_spec aead_dec; m_dh_spec x25519; m_mix_ck_spec; m_mix_hash_spec; m_mix_key_spec;
   m_start_spec cons iden].
Definition hc3_G_m_consume_initiation_2 : funspecs :=
  [bytes_zero_spec; m_decrypt_and_hash_spec aead_dec; m_mix_key_spec].
(* CS0 = CSkresp *)
Definition hc3_G_m_create_response : funspecs :=
  [bytes_copy_spec; m_clamp_spec; m_dh_spec x25519; m_encrypt_and_hash_spec aead_enc; m_mix_ck_spec;
   m_mix_hash_spec; m_mix_psk_spec].

(* CS0 = CSmi / CSmr / cookie_reply's CS *)
Definition hc3_G_init_img : funspecs := [bytes_copy_spec; le32_store_spec].  (* init_img resp_img cookie_img *)
Definition hc3_G_fill_init : funspecs := [@asm_env.nondet_bytes_spec CSmi; nondet_u32_spec].
Definition hc3_G_fill_resp : funspecs := [@asm_env.nondet_bytes_spec CSmr; nondet_u32_spec].
Definition hc3_G_fill_cookie_msg : funspecs :=
  [@asm_env.nondet_bytes_spec WgNoise.contracts.x_cookie_reply.Harness.CS; nondet_u32_spec].

End Ctx.

(* the constants read by the law-dependent bodies *)
Definition hc3_V_bp (bp: ident) : varspecs := [(bp, tarray tuchar 32)].
Definition hc3_V_start (cons iden: ident) : varspecs := [(cons, tarray tuchar 37); (iden, tarray tuchar 34)].
