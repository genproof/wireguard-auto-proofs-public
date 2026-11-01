(* law handshake_receive:
   main's specification and context.  main is proved at the world compspecs W_handshake_receive (unit u_hrx5; the
   harness's other functions are the local piece at HRX, hrx5_spec.v).  main's imports are EXACTLY the
   specifications of the functions it calls: the environment, two AEAD primitives, four protocol functions
   (prot_specs4), the common.h functions and ten local functions (hrx5_spec.v, CSw = W).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require WgNoise.proof.protocol.prot_prog3.
Require WgNoise.proof.protocol4.prot_specs4.
Require WgNoise.proof.protocol.prot_dec3.
Require WgNoise.contracts.x_handshake_receive.
Require WgNoise.harness.x_handshake_receive.code.

Module HM5 := WgNoise.harness.x_handshake_receive.code.
Module PS4 := WgNoise.proof.protocol4.prot_specs4.

(* the harness unit, in the world compspecs, with the whole program's varspecs *)
Definition u_hrx5 : unit_ctx := mk_unit W_handshake_receive hrx5_V HM5.prog.

Definition hrx5_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition hrx5_main_spec : ident * funspec :=
  (HM5._main, QPmain_spec_ext' WgNoise.contracts.x_handshake_receive.whole_prog tt hrx5_post).

Section Piece.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Notation W := W_handshake_receive.

(* the harness's constants M_BASEPOINT, M_CONSTRUCTION, M_IDENTIFIER of this unit *)
Notation BP := HM5._x_handshake_receive__M_BASEPOINT.
Notation CO := HM5._x_handshake_receive__M_CONSTRUCTION.
Notation ID := HM5._x_handshake_receive__M_IDENTIFIER.

Definition hrx5_mimports (cs: compspecs) : funspecs :=
  WgNoise.proof.protocol.prot_prog3.env_specs_ns W ++ [nondet_size_spec] ++
  [@xchacha20poly1305_encrypt_spec_of cs xaead_enc;
   @WgNoise.proof.protocol.prot_dec3.xchacha20poly1305_decrypt_spec_of3 cs xaead_dec] ++
  [PS4.wg_noise_init_spec; PS4.wg_index_hashtable_insert_spec; PS4.wg_noise_keypairs_clear_spec W;
   PS4.quickproof_swab16_spec] ++
  (* common.h, unchanged by (hc_specs3.v) *)
  [check_failed_spec; bytes_eq_spec; bytes_copy_spec; bytes_set_spec; draw_size_spec; draw_steps_spec;
   draw_u64_spec; draw_boottime_spec; le32_store_spec; m_identity_of_spec x25519 BP; m_precomputed_spec x25519;
   m_label_key_spec; m_mac_spec; m_consume_initiation_1_spec x25519 aead_dec CO ID;
   m_consume_initiation_2_spec aead_dec; m_consume_response_spec x25519 aead_dec; m_ts_newer_spec;
   m_not_flood_spec; m_last_consumption_spec; table_has_spec; table_len_spec; init_img_spec; resp_img_spec;
   cookie_img_spec; fill_init_spec; fill_resp_spec; fill_cookie_msg_spec] ++
  (* common.h (hc4_specs.v) *)
  [setup_device4_spec x25519; hs_same4_spec W; hs_zeroed_from4_spec W; hs_same_but_next4_spec W;
   hs_randomize4_spec; pr_same_but_cookie4_spec W; pr_same4_spec W; peer_randomize_rest4_spec;
   dev_take4_spec; dev_same4_spec W; shim_take4_spec; shim_same4_spec; shim_no_warning4_spec; skb_take4_spec;
   skb_same4_spec W; hnodes_add4_spec x25519 W; hnodes_snap4_spec W; hnodes_same_except4_spec W;
   hnodes_free4_spec W; hnodes_pick4_spec W; kents_add4_spec W; kents_snap4_spec W; kents_same4_spec W;
   kents_same_but_next4_spec W; kents_hashed4_spec W; kents_free4_spec W; le32_load4_spec] ++
  (* the harness's own functions (hrx5_spec.v) *)
  [hrx5_dispatch_spec x25519 aead_dec xaead_enc xaead_dec W; hrx5_rx_reset_spec; hrx5_rx_only_cookie_spec;
   hrx5_rx_authenticated_spec; hrx5_m_expired_spec; hrx5_m_cookie_spec; hrx5_draw_type_spec;
   hrx5_k_initiation_spec; hrx5_k_response_spec; hrx5_draw_macs_spec].

End Piece.

Definition hrx5_G : funspecs := [hrx5_main_spec].

(* the statement of the main piece (hrx5_piece.v) *)
Definition hrx5_mpiece_stmt : Prop :=
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec,
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  piece_ok [u_hrx5] (hrx5_mimports x25519 aead_dec xaead_enc xaead_dec) hrx5_G.
