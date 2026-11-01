(* The harness piece's interface for law rp_limit (harness/rp_limit.c), in the law's world compspecs
   W_rp_limit (rp_worlds.v): the specifications of the harness's own functions upto, any_u64, new_counter
   and main, and what they import: the external world (with gp_assert) and wg_counter_validate's shared
   specification (counter_spec.v, at Counter.CS). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.harness.rp_common.rp_worlds.
Require Import WgNoise.proof.counter.counter_spec.
Require WgNoise.contracts.rp_limit.
Require WgNoise.harness.rp_limit.code.

Module C := WgNoise.harness.rp_limit.code.

#[local] Existing Instance W_rp_limit.

(* the harness unit, in the world compspecs *)
Definition u_rp_limit : unit_ctx :=
  mk_unit W_rp_limit (QPvarspecs WgNoise.contracts.rp_limit.Harness.qp) C.prog.

Definition rp_limit_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition rp_limit_main_spec : ident * funspec :=
  (C._main, QPmain_spec_ext' WgNoise.contracts.rp_limit.whole_prog tt rp_limit_post).

(* upto(max): any value from 0 to max *)
Definition rp_limit_upto_spec :=
  DECLARE C._upto
  WITH max: Z
  PRE [ tulong ] PROP (0 <= max <= Int64.max_unsigned) PARAMS (Vlong (Int64.repr max)) SEP ()
  POST [ tulong ] EX v: Z,
    PROP (0 <= v <= max) RETURN (Vlong (Int64.repr v)) SEP ().

(* any_u64(): any 64-bit value *)
Definition rp_limit_any_u64_spec :=
  DECLARE C._any_u64
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tulong ] EX n: Z,
    PROP (0 <= n <= Int64.max_unsigned) RETURN (Vlong (Int64.repr n)) SEP ().

(* the value of a struct noise_replay_counter with counter top and backtrack bm; the lock is never written *)
Definition rp_tnrc := Tstruct C._noise_replay_counter noattr.
Definition rp_counter_val (top: Z) (bm: list Z) : reptype rp_tnrc :=
  (Vlong (Int64.repr top), (Vundef, map (fun w => Vlong (Int64.repr w)) bm)).

(* new_counter(c): a new key's replay counter, all zero *)
Definition rp_limit_new_counter_spec :=
  DECLARE C._new_counter
  WITH sh: share, c: val
  PRE [ tptr rp_tnrc ] PROP (writable_share sh) PARAMS (c) SEP (data_at_ sh rp_tnrc c)
  POST [ tvoid ]
    PROP () RETURN () SEP (data_at sh rp_tnrc (rp_counter_val 0 (Zrepeat 0 128)) c).

(* the functions of the external world the program calls (QuickProof.Env's specifications, as in
   asm_assert.env_specs_gp) and the counter piece's wg_counter_validate (at Counter.CS) *)
Definition rp_limit_imports (cs: compspecs) : funspecs :=
  [QuickProof.Env.nondet_u8_spec; QuickProof.Env.nondet_u32_spec; QuickProof.Env.nondet_size_spec;
   QuickProof.Env.gp_assert_spec; wg_counter_validate_spec].

Definition rp_limit_G : funspecs :=
  [rp_limit_upto_spec; rp_limit_any_u64_spec; rp_limit_new_counter_spec; rp_limit_main_spec].
