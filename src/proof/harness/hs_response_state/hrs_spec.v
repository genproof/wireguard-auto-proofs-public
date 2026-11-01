(* The law hs_response_state: the interface of its own piece.

   The harness unit (hs_asm.hs_unit) holds main and the copies of the hs_laws.h helpers this harness has
   (any_u64, any_clocks, new_device, new_peer, new_pair; specifications of hs_specs.v).  main imports the
   functions it calls outside the harness: nondet_u32 and gp_assert (the environment), and noise.c's
   create_initiation, consume_initiation, create_response and consume_response (protocol v5, at the world
   compspecs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require Import WgNoise.proof.harness.hs_common.hs_asm.
Require WgNoise.contracts.hs_response_state.
Require WgNoise.harness.hs_response_state.code.

Module HRS := WgNoise.harness.hs_response_state.code.

Notation hrs_prog := WgNoise.contracts.hs_response_state.whole_prog.
Notation W_hrs := W_hs_response_state.

(* the harness's static functions other than main *)
Definition hrs_Gl (x25519: list byte -> list byte -> list byte) : funspecs :=
  [any_u64_spec; any_clocks_spec; new_device_spec x25519; new_peer_spec x25519; new_pair_spec x25519].

Definition hrs_ids : list ident := ltac:(let l := eval compute in (map fst (hrs_Gl (fun _ _ => nil))) in exact l).

(* main's imports *)
Definition hrs_Il (x25519: list byte -> list byte -> list byte)
    (aead_enc: list byte -> Z -> list byte -> list byte -> list byte)
    (aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte)) (cs: compspecs) : funspecs :=
  [nondet_u32_spec; gp_assert_spec;
   wg_noise_handshake_create_initiation_spec x25519 aead_enc;
   wg_noise_handshake_consume_initiation_spec x25519 aead_dec;
   wg_noise_handshake_create_response_spec x25519 aead_enc;
   wg_noise_handshake_consume_response_spec x25519 aead_dec].

(* the harness unit *)
Definition hrs_unit : unit_ctx := hs_unit W_hrs hrs_prog HRS.prog.

(* main's context *)
Definition hrs_Gmain x25519 aead_enc aead_dec : funspecs :=
  hrs_Il x25519 aead_enc aead_dec W_hrs ++ hs_main_spec hrs_prog :: hrs_Gl x25519.
