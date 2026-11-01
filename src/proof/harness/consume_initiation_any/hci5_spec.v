(* law consume_initiation_any: the law's own piece
   interface.  The law's piece = main and ts_step (the harness's only
   function outside common.h); the common.h functions are proved by the common4 / common pieces, the protocol functions by protocol_piece4.
   main's imports are EXACTLY the specifications of the functions it calls (a small Delta), in the world
   compspecs W_consume_initiation_any. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_ts.
Require WgNoise.proof.protocol.prot_prog3.
Require WgNoise.contracts.x_consume_initiation_any.
Require WgNoise.harness.x_consume_initiation_any.code.

Module HS5 := WgNoise.harness.x_consume_initiation_any.code.

(* the varspecs of the WHOLE program (literal): main_pre describes every global (VST's main_pre_InitGpred needs
   each of them in main's glob_types) *)
Definition hci5_V : varspecs :=
  ltac:(let x := eval vm_compute in (QPvarspecs WgNoise.contracts.x_consume_initiation_any.whole_prog) in exact x).

(* the harness unit, in the world compspecs, with the whole program's varspecs *)
Definition u_hci5 : unit_ctx :=
  mk_unit W_consume_initiation_any hci5_V WgNoise.harness.x_consume_initiation_any.code.prog.

Definition hci5_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition hci5_main_spec : ident * funspec :=
  (HS5._main, QPmain_spec_ext' WgNoise.contracts.x_consume_initiation_any.whole_prog tt hci5_post).

Section Piece.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Notation W := W_consume_initiation_any.
Notation bp := HS5._x_consume_initiation_any__M_BASEPOINT.
Notation cons := HS5._x_consume_initiation_any__M_CONSTRUCTION.
Notation iden := HS5._x_consume_initiation_any__M_IDENTIFIER.

(* the functions main calls: the environment, four protocol functions (prot_specs4), the common.h functions *)
Definition hci5_imports (cs: compspecs) : funspecs :=
  WgNoise.proof.protocol.prot_prog3.env_specs_ns W ++ [nondet_size_spec] ++
  [wg_noise_init_spec; wg_index_hashtable_insert_spec;
   wg_noise_handshake_consume_initiation_spec x25519 aead_dec; wg_peer_put_spec] ++
  [check_failed_spec; bytes_eq_spec; bytes_copy_spec; draw_steps_spec; draw_boottime_spec;
   m_identity_of_spec x25519 bp; m_tai64n_spec; m_create_initiation_spec x25519 aead_enc bp cons iden;
   m_consume_initiation_1_spec x25519 aead_dec cons iden; m_consume_initiation_2_spec aead_dec;
   m_precomputed_spec x25519; init_img_spec; fill_init_spec; m_ts_newer_spec; m_not_flood_spec;
   m_last_consumption_spec] ++
  [setup_device4_spec x25519; draw_real_clock4_spec; hs_randomize4_spec; pr_same4_spec W;
   peer_randomize_rest4_spec; dev_take4_spec; dev_same4_spec W; shim_take4_spec; shim_same4_spec;
   hnodes_add4_spec x25519 W; hnodes_snap4_spec W; hnodes_same_except4_spec W; hnodes_free4_spec W;
   kents_add4_spec W; kents_snap4_spec W; kents_same4_spec W; kents_free4_spec W].

End Piece.

Definition hci5_G : funspecs := [hci5_ts_step_spec; hci5_main_spec].
