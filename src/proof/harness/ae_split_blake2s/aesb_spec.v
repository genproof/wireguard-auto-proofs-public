(* The harness piece's interface for law ae_split_blake2s (harness/ae_split_blake2s.c), in the law's world W_aesb
   (aesb_world.v): the unit, main's specification, the specifications of the wg_laws.h helpers the harness uses
   (upto, any_bytes, bytes_eq: wl_spec.v, at W_aesb) and what main imports: the externals the program has
   (QuickProof.Env's nondet_u8, nondet_size, gp_assert and asm_env's nondet_bytes, quickproof_malloc for
   any_bytes) and the BLAKE2s interface of b2s_spec3.v (at Blake2s.CS: main converts its local
   `struct blake2s_ctx ctx` between W_aesb and Blake2s.CS, which have the same struct).
   The varspecs of the unit are those of the whole program (aesb_V): main's precondition describes every global,
   among them blake2s_sigma, which blake2s_update / blake2s_final need (blake2s_globals). *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.harness.ae_split_blake2s.aesb_world.
Require Export WgNoise.proof.blake2s.b2s_spec3.
Require Import WgNoise.proof.harness.wg_laws.wl_spec.
Require Import QuickProof.Env.
Require WgNoise.contracts.ae_split_blake2s.
Require WgNoise.harness.ae_split_blake2s.code.

#[local] Existing Instance W_aesb.
Local Open Scope Z_scope.

(* the varspecs of the whole program (literal) *)
Definition aesb_V : varspecs :=
  ltac:(let x := eval vm_compute in (QPvarspecs WgNoise.contracts.ae_split_blake2s.whole_prog) in exact x).

(* the harness unit, in the world compspecs, with the whole program's varspecs *)
Definition u_aesb : unit_ctx := mk_unit W_aesb aesb_V WgNoise.harness.ae_split_blake2s.code.prog.

(* main: the precondition is fixed (main_pre of the whole program), the postcondition anything *)
Definition aesb_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition aesb_main_spec : ident * funspec :=
  (WgNoise.harness.ae_split_blake2s.code._main,
   QPmain_spec_ext' WgNoise.contracts.ae_split_blake2s.whole_prog tt aesb_post).

(* the externals of the program and the BLAKE2s functions main calls *)
Definition aesb_imports (cs: compspecs) : funspecs :=
  [(_quickproof_malloc, @malloc_spec' W_aesb); nondet_u8_spec; nondet_size_spec; @asm_env.nondet_bytes_spec W_aesb;
   gp_assert_spec;
   blake2s_init_spec; blake2s_init_key_spec; blake2s_update_spec3; blake2s_final_spec; blake2s_spec3].

(* the harness's functions: the wg_laws.h helpers and main *)
Definition aesb_G : funspecs :=
  [upto_spec; @any_bytes_spec W_aesb; @bytes_eq_spec W_aesb; aesb_main_spec].

(* the context of the body proofs of the harness piece *)
Definition aesb_Gprog : funspecs := aesb_imports W_aesb ++ aesb_G.
