(* The harness piece's interface for law ae_split_poly1305 (harness/ae_split_poly1305.c), in the law's world
   compspecs W_asp (asp_world.v): the specifications of the harness's own functions (the wg_laws.h helpers upto,
   any_bytes, bytes_eq of wl_spec.v, and main) and what they import: the external world (QuickProof.Env's
   specifications, only the externals the program calls, with gp_assert) and the Poly1305 API main calls, with
   the shared specifications of aead_spec3.v at Poly1305.CS (poly1305_init_spec, poly1305_update_spec3 for any
   chunk, poly1305_final_spec): main converts its two `struct poly1305_desc_ctx` between W_asp and Poly1305.CS. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require QuickProof.Env.
Require WgNoise.proof.assembly.asm_env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Export WgNoise.proof.aead.aead_spec3.
Require Export WgNoise.proof.harness.wg_laws.wl_spec.
Require Export WgNoise.proof.harness.ae_split_poly1305.asp_world.
Require WgNoise.contracts.ae_split_poly1305.
Require WgNoise.harness.ae_split_poly1305.code.

Module ASP := WgNoise.harness.ae_split_poly1305.code.
#[local] Existing Instance W_asp.

(* the varspecs of the whole program (literal) *)
Definition asp_V : varspecs :=
  ltac:(let x := eval vm_compute in (QPvarspecs WgNoise.contracts.ae_split_poly1305.whole_prog) in exact x).

(* the harness unit, in the world compspecs, with the whole program's varspecs *)
Definition u_asp : unit_ctx := mk_unit W_asp asp_V ASP.prog.

(* main: the precondition is fixed (main_pre of the whole program), the postcondition anything *)
Definition asp_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition asp_main_spec : ident * funspec :=
  (ASP._main, QPmain_spec_ext' WgNoise.contracts.ae_split_poly1305.whole_prog tt asp_post).

(* imports: the externals the program calls (malloc for any_bytes, nondet_bytes for the key and any_bytes,
   nondet_size for upto, nondet_u8 for the loop, gp_assert for the check) and the Poly1305 API *)
Definition asp_imports (cs: compspecs) : funspecs :=
  [(_quickproof_malloc, @malloc_spec' W_asp); QuickProof.Env.nondet_u8_spec; QuickProof.Env.nondet_size_spec;
   @asm_env.nondet_bytes_spec W_asp; QuickProof.Env.gp_assert_spec;
   poly1305_init_spec; poly1305_update_spec3; poly1305_final_spec].

Definition asp_G : funspecs :=
  [upto_spec; @any_bytes_spec W_asp; @bytes_eq_spec W_asp; asp_main_spec].

(* the context of every body proof of the harness piece *)
Definition asp_Gprog : funspecs := asp_imports W_asp ++ asp_G.
