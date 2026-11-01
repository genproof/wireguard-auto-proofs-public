(* law handshake_clear: the law's own piece interface.  The law's piece = main (the harness has no function outside common.h); the
   common.h functions are proved by the common4 piece, the protocol functions by protocol_piece4.  main's imports are EXACTLY
   the specifications of the functions it calls (a small Delta), in the world compspecs W_handshake_clear.
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
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_world.
Require WgNoise.proof.protocol.prot_prog3.
Require WgNoise.contracts.x_handshake_clear.
Require WgNoise.harness.x_handshake_clear.code.

Module HS5 := WgNoise.harness.x_handshake_clear.code.

(* the varspecs of the WHOLE program (literal): main_pre describes every global (VST's main_pre_InitGpred needs
   each of them in main's glob_types) *)
Definition hcl5_V : varspecs :=
  ltac:(let x := eval vm_compute in (QPvarspecs WgNoise.contracts.x_handshake_clear.whole_prog) in exact x).

(* the harness unit, in the world compspecs, with the whole program's varspecs *)
Definition u_hcl5 : unit_ctx :=
  mk_unit W_handshake_clear hcl5_V WgNoise.harness.x_handshake_clear.code.prog.

Definition hcl5_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition hcl5_main_spec : ident * funspec :=
  (HS5._main, QPmain_spec_ext' WgNoise.contracts.x_handshake_clear.whole_prog tt hcl5_post).

Section Piece.
Variable x25519: list byte -> list byte -> list byte.

Notation W := W_handshake_clear.

(* the functions main calls: the environment, two protocol functions (prot_specs4), the common.h functions *)
Definition hcl5_imports (cs: compspecs) : funspecs :=
  WgNoise.proof.protocol.prot_prog3.env_specs_ns W ++
  [wg_index_hashtable_insert_spec; wg_noise_handshake_clear_spec] ++
  [check_failed_spec; draw_steps_spec; draw_boottime_spec; table_has_spec; table_len_spec] ++
  [setup_device4_spec x25519; hs_randomize4_spec; peer_randomize_rest4_spec; hnodes_add4_spec x25519 W;
   hnodes_pick4_spec W; hnodes_snap4_spec W; kents_add4_spec W; kents_snap4_spec W; dev_take4_spec;
   shim_take4_spec; hs_zeroed_from4_spec W; pr_same4_spec W; hs_same_but_next4_spec W;
   kents_same_but_next4_spec W; kents_hashed4_spec W; dev_same4_spec W; shim_same4_spec;
   kents_free4_spec W; hnodes_free4_spec W].

End Piece.

Definition hcl5_G : funspecs := [hcl5_main_spec].
