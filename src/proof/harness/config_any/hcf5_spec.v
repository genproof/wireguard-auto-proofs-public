(* law config_any: the law's own piece interface.  The law's piece = main (the harness has no other function outside common.h); the common.h
   functions are proved by the common4 piece (hc4_G_config_any: hc4_specs.v / hc_specs3.v), the protocol functions
   by protocol_piece4 (prot_specs4.v).  main's imports are EXACTLY the specifications of the functions it calls (a
   small Delta), in the world compspecs W_config_any (hcf5_world.v). *)
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
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.config_any.hcf5_world.
Require WgNoise.proof.protocol.prot_prog3.
Require WgNoise.contracts.x_config_any.
Require WgNoise.harness.x_config_any.code.

Module HSF5 := WgNoise.harness.x_config_any.code.

(* the varspecs of the WHOLE program (literal): main_pre describes every global (VST's main_pre_InitGpred needs
   each of them in main's glob_types) *)
Definition hcf5_V : varspecs :=
  ltac:(let x := eval vm_compute in (QPvarspecs WgNoise.contracts.x_config_any.whole_prog) in exact x).

(* the harness unit, in the world compspecs, with the whole program's varspecs *)
Definition u_hcf5 : unit_ctx :=
  mk_unit W_config_any hcf5_V WgNoise.harness.x_config_any.code.prog.

Definition hcf5_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition hcf5_main_spec : ident * funspec :=
  (HSF5._main, QPmain_spec_ext' WgNoise.contracts.x_config_any.whole_prog tt hcf5_post).

Section Piece.
Variable x25519: list byte -> list byte -> list byte.

Notation W := W_config_any.
Notation bp := HSF5._x_config_any__M_BASEPOINT.

(* the functions main calls: the environment, eight protocol functions (prot_specs4), the common.h functions *)
Definition hcf5_imports (cs: compspecs) : funspecs :=
  WgNoise.proof.protocol.prot_prog3.env_specs_ns W ++
  [wg_index_hashtable_insert_spec; wg_noise_set_static_identity_private_key_spec x25519;
   wg_noise_precompute_static_static_spec x25519; wg_noise_handshake_init_spec x25519;
   wg_cookie_checker_init_spec; wg_cookie_checker_precompute_device_keys_spec;
   wg_cookie_checker_precompute_peer_keys_spec; wg_cookie_init_spec] ++
  [check_failed_spec; bytes_zero_spec; bytes_copy_spec; bytes_set_spec; draw_u64_spec; draw_boottime_spec;
   m_identity_of_spec x25519 bp; m_label_key_spec; m_precomputed_spec x25519; setup_peer_spec x25519] ++
  [setup_device4_spec x25519; hs_take4_spec; hs_same4_spec W; hs_randomize4_spec; pr_take4_spec; pr_same4_spec W;
   peer_randomize_rest4_spec; dev_take4_spec; dev_same4_spec W; shim_take4_spec; shim_same4_spec;
   kents_add4_spec W; kents_snap4_spec W; kents_same4_spec W; kents_free4_spec W].

End Piece.

Definition hcf5_G : funspecs := [hcf5_main_spec].
