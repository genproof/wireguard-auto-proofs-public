(* The law hs_reject_response (harness/hs_reject_response.c): the specifications of its piece.  Its imports are
   the externals it calls (QuickProof.Env's, asm_env's nondet_bytes) and the functions of noise.c that main and
   the helpers of hs_laws.h call (prot_specs5.v); its own functions are main (hs_asm.hs_main_spec) and its copies
   of the helpers of hs_laws.h and hs_unchanged.h (hs_specs.v). *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env.
Require Import WgNoise.proof.protocol5.prot_specs5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require Import WgNoise.proof.harness.hs_common.hs_asm.
Require WgNoise.contracts.hs_reject_response.
Require WgNoise.harness.hs_reject_response.code.

Module R := WgNoise.harness.hs_reject_response.code.

Definition p_rr : QP.program function := WgNoise.contracts.hs_reject_response.whole_prog.

(* the imports: externals and noise.c *)
Definition hrr_Il (x25519: list byte -> list byte -> list byte)
    (aead_enc: list byte -> Z -> list byte -> list byte -> list byte)
    (aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte)) (cs: compspecs) : funspecs :=
  [nondet_u8_spec; nondet_u32_spec; @asm_env.nondet_bytes_spec cs; gp_assert_spec;
   wg_noise_init_spec; wg_noise_set_static_identity_private_key_spec x25519; wg_noise_handshake_init_spec x25519;
   wg_noise_handshake_create_initiation_spec x25519 aead_enc;
   wg_noise_handshake_consume_initiation_spec x25519 aead_dec;
   wg_noise_handshake_create_response_spec x25519 aead_enc;
   wg_noise_handshake_consume_response_spec x25519 aead_dec].

(* the harness's static functions other than main: the helpers *)
Definition hrr_Gl (x25519: list byte -> list byte -> list byte) : funspecs :=
  [any_u64_spec; bytes_eq_spec; any_clocks_spec; new_device_spec x25519; new_peer_spec x25519;
   new_pair_spec x25519; copy_peer_spec; same_peer_spec].

(* main's context *)
Definition hrr_G x25519 aead_enc aead_dec : funspecs :=
  hrr_Il x25519 aead_enc aead_dec W_hs_reject_response ++ hs_main_spec p_rr :: hrr_Gl x25519.
