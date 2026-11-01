(* The law hs_begin_session_state: the interface of its own piece.

   The harness unit (hs_asm.hs_unit) holds main and the copies of the hs_laws.h helpers this harness has
   (new_device, new_peer, new_pair; specifications of hs_specs.v).  The unit imports the functions they call
   outside the harness: nondet_u8, nondet_u32, nondet_bytes and gp_assert (the environment), and noise.c's
   wg_noise_init, set_static_identity_private_key, handshake_init (new_pair's callees) and begin_session
   (protocol v5, at the world compspecs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.proof.assembly.asm_env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require Import WgNoise.proof.harness.hs_common.hs_asm.
Require WgNoise.contracts.hs_begin_session_state.
Require WgNoise.harness.hs_begin_session_state.code.

Module HBS := WgNoise.harness.hs_begin_session_state.code.

Notation hbs_prog := WgNoise.contracts.hs_begin_session_state.whole_prog.
Notation W_hbs := W_hs_begin_session_state.

(* the harness's static functions other than main *)
Definition hbs_Gl (x25519: list byte -> list byte -> list byte) : funspecs :=
  [new_device_spec x25519; new_peer_spec x25519; new_pair_spec x25519].

Definition hbs_ids : list ident := ltac:(let l := eval compute in (map fst (hbs_Gl (fun _ _ => nil))) in exact l).

(* the unit's imports *)
Definition hbs_Il (x25519: list byte -> list byte -> list byte)
    (aead_enc: list byte -> Z -> list byte -> list byte -> list byte)
    (aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte)) (cs: compspecs) : funspecs :=
  [nondet_u8_spec; nondet_u32_spec; @asm_env.nondet_bytes_spec cs; gp_assert_spec;
   wg_noise_init_spec; wg_noise_set_static_identity_private_key_spec x25519; wg_noise_handshake_init_spec x25519;
   wg_noise_handshake_begin_session_spec cs].

(* the harness unit *)
Definition hbs_unit : unit_ctx := hs_unit W_hbs hbs_prog HBS.prog.

(* main's context *)
Definition hbs_Gmain x25519 aead_enc aead_dec : funspecs :=
  hbs_Il x25519 aead_enc aead_dec W_hbs ++ hs_main_spec hbs_prog :: hbs_Gl x25519.
