(* Law hs_reject_initiation: main's specification and the context of its body proof.

   main is proved in the compspecs of its harness, CSh (hs_specs.v), where the helpers of hs_laws.h and
   hs_unchanged.h are proved too, and moved into the law's world like them.  Its context lists exactly the
   functions main calls: the environment (QuickProof.Env's nondet_u8, nondet_u32, gp_assert and asm_env's
   nondet_bytes), create_initiation and consume_initiation of noise.c (prot_specs5.v), and the helpers. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.proof.assembly.asm_env.
Require Import WgNoise.proof.protocol5.prot_specs5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require WgNoise.contracts.hs_reject_initiation.

(* the varspecs of the whole program (literal): main's precondition describes every global *)
Definition hri_V : varspecs :=
  ltac:(let x := eval vm_compute in (QPvarspecs WgNoise.contracts.hs_reject_initiation.whole_prog) in exact x).

Definition hri_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition hri_main_spec : ident * funspec :=
  (H._main, QPmain_spec_ext' WgNoise.contracts.hs_reject_initiation.whole_prog tt hri_post).

Section Ctx.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

Definition hri_G : funspecs :=
  [nondet_u8_spec; nondet_u32_spec; @asm_env.nondet_bytes_spec CSh; gp_assert_spec;
   wg_noise_handshake_create_initiation_spec x25519 aead_enc;
   wg_noise_handshake_consume_initiation_spec x25519 aead_dec;
   any_u64_spec; any_clocks_spec; new_pair_spec x25519; copy_peer_spec; same_peer_spec; hri_main_spec].

End Ctx.
