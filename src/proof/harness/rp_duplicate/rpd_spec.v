(* The harness piece's interface for law rp_duplicate (harness/rp_duplicate.c), in the law's world
   W_rp_duplicate (rp_worlds.v): the specifications of the harness's own functions (new_counter, any_u64 of
   wg_laws.h, main) and what they import (the external world and counter_validate's shared specification). *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.harness.rp_common.rp_worlds.
Require Import WgNoise.proof.counter.counter_spec.
Require Import QuickProof.Env.
Require WgNoise.contracts.rp_duplicate.
Require WgNoise.harness.rp_duplicate.code.

#[local] Existing Instance W_rp_duplicate.

(* the harness unit, in the world compspecs *)
Definition u_rpd : unit_ctx :=
  mk_unit W_rp_duplicate (QPvarspecs WgNoise.contracts.rp_duplicate.Harness.qp) WgNoise.harness.rp_duplicate.code.prog.

Definition rpd_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition rpd_main_spec : ident * funspec :=
  (WgNoise.harness.rp_duplicate.code._main,
   QPmain_spec_ext' WgNoise.contracts.rp_duplicate.whole_prog tt rpd_post).

Definition rpd_tnrc := Tstruct WgNoise.harness.rp_duplicate.code._noise_replay_counter noattr.

(* a struct noise_replay_counter with counter top and backtrack bm (the lock is never written) *)
Definition rpd_c (top: Z) (bm: list Z) : reptype rpd_tnrc :=
  (Vlong (Int64.repr top), (Vundef, map (fun w => Vlong (Int64.repr w)) bm)).

(* new_counter(c): a new key's replay counter, all zero *)
Definition rpd_new_counter_spec :=
  DECLARE WgNoise.harness.rp_duplicate.code._new_counter
  WITH sh: share, c: val
  PRE [ tptr rpd_tnrc ]
    PROP (writable_share sh) PARAMS (c) SEP (data_at_ sh rpd_tnrc c)
  POST [ tvoid ]
    PROP () RETURN () SEP (data_at sh rpd_tnrc (rpd_c 0 (Zrepeat 0 128)) c).

(* any_u64(): any 64-bit value *)
Definition rpd_any_u64_spec :=
  DECLARE WgNoise.harness.rp_duplicate.code._any_u64
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tulong ] EX n: Z,
    PROP (0 <= n <= Int64.max_unsigned) RETURN (Vlong (Int64.repr n)) SEP ().

(* the externals of the program (nondet_u8, nondet_u32, gp_assert of QuickProof.Env) and counter_validate's
   specification (at Counter.CS) *)
Definition rpd_imports (cs: compspecs) : funspecs :=
  [nondet_u8_spec; nondet_u32_spec; gp_assert_spec; wg_counter_validate_spec].

Definition rpd_G : funspecs := [rpd_new_counter_spec; rpd_any_u64_spec; rpd_main_spec].
