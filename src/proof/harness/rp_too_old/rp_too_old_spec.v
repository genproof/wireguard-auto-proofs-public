(* The harness piece's interface for law rp_too_old (harness/rp_too_old.c), in the law's world compspecs
   W_rp_too_old (rp_worlds.v): the specifications of the harness's own functions upto, any_u64, new_counter
   and main, and what they import (the external world and the counter piece's wg_counter_validate). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.harness.rp_common.rp_worlds.
Require Import WgNoise.proof.counter.counter_spec.
Require WgNoise.contracts.rp_too_old.
Require WgNoise.harness.rp_too_old.code.

Module C := WgNoise.harness.rp_too_old.code.

(* the harness unit, in the world compspecs *)
Definition u_rp_too_old : unit_ctx :=
  mk_unit W_rp_too_old (QPvarspecs WgNoise.contracts.rp_too_old.Harness.qp) C.prog.

Definition rp_too_old_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition rp_too_old_main_spec : ident * funspec :=
  (C._main, QPmain_spec_ext' WgNoise.contracts.rp_too_old.whole_prog tt rp_too_old_post).

(* upto(max): any value from 0 to max *)
Definition rp_too_old_upto_spec :=
  DECLARE C._upto
  WITH m: Z
  PRE [ tulong ] PROP (0 <= m <= Int64.max_unsigned) PARAMS (Vlong (Int64.repr m)) SEP ()
  POST [ tulong ] EX v: Z,
    PROP (0 <= v <= m) RETURN (Vlong (Int64.repr v)) SEP ().

(* any_u64(): any 64-bit value *)
Definition rp_too_old_any_u64_spec :=
  DECLARE C._any_u64
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tulong ] EX n: Z,
    PROP (0 <= n <= Int64.max_unsigned) RETURN (Vlong (Int64.repr n)) SEP ().

(* new_counter(c): counter 0 and an all-zero bitmap; the lock is not written *)
Definition rp_too_old_new_counter_spec :=
  DECLARE C._new_counter
  WITH sh: share, c: val
  PRE [ tptr (Tstruct C._noise_replay_counter noattr) ]
    PROP (writable_share sh) PARAMS (c)
    SEP (@data_at_ W_rp_too_old sh (Tstruct C._noise_replay_counter noattr) c)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (@data_at W_rp_too_old sh (Tstruct C._noise_replay_counter noattr)
           (Vlong (Int64.repr 0), (Vundef, map (fun w => Vlong (Int64.repr w)) (Zrepeat 0 128))) c).

(* the externals the program calls (QuickProof.Env: nondet_u8, nondet_u32, nondet_size and the harness's
   check gp_assert), and the counter piece's wg_counter_validate (at Counter.CS) *)
Definition rp_too_old_imports (cs: compspecs) : funspecs :=
  [QuickProof.Env.nondet_u8_spec; QuickProof.Env.nondet_u32_spec; QuickProof.Env.nondet_size_spec;
   QuickProof.Env.gp_assert_spec; wg_counter_validate_spec].

Definition rp_too_old_G : funspecs :=
  [rp_too_old_upto_spec; rp_too_old_any_u64_spec; rp_too_old_new_counter_spec; rp_too_old_main_spec].
