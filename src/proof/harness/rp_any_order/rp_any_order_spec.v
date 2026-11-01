(* The harness piece's interface for law rp_any_order (harness/rp_any_order.c with wg_laws.h), in the law's world
   compspecs W_rp_any_order (rp_worlds.v): the specifications of the harness's own functions upto, new_counter and
   main, and what they import (the external world and the counter piece's wg_counter_validate, counter_spec.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.harness.rp_common.rp_worlds.
Require Import WgNoise.proof.counter.counter_spec.
Require WgNoise.contracts.rp_any_order.
Require WgNoise.harness.rp_any_order.code.

Module C := WgNoise.harness.rp_any_order.code.

(* the harness unit, in the world compspecs *)
Definition u_rao : unit_ctx :=
  mk_unit W_rp_any_order (QPvarspecs WgNoise.contracts.rp_any_order.Harness.qp) C.prog.

Definition rao_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition rao_main_spec : ident * funspec :=
  (C._main, QPmain_spec_ext' WgNoise.contracts.rp_any_order.whole_prog tt rao_post).

(* upto(max): any value from 0 to max *)
Definition rao_upto_spec :=
  DECLARE C._upto
  WITH max: Z
  PRE [ tulong ] PROP (0 <= max <= Int64.max_unsigned) PARAMS (Vlong (Int64.repr max)) SEP ()
  POST [ tulong ] EX v: Z,
    PROP (0 <= v <= max) RETURN (Vlong (Int64.repr v)) SEP ().

(* the value of the harness's struct noise_replay_counter whose lock is never written *)
Definition rao_cnt (top: Z) (bm: list Z) : @reptype W_rp_any_order (Tstruct C._noise_replay_counter noattr) :=
  (Vlong (Int64.repr top), (Vundef, map (fun w => Vlong (Int64.repr w)) bm)).

(* new_counter(c): a new key's replay counter, all zero but the lock *)
Definition rao_new_counter_spec :=
  DECLARE C._new_counter
  WITH sh: share, c: val
  PRE [ tptr (Tstruct C._noise_replay_counter noattr) ]
    PROP (writable_share sh) PARAMS (c) SEP (@data_at_ W_rp_any_order sh (Tstruct C._noise_replay_counter noattr) c)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (@data_at W_rp_any_order sh (Tstruct C._noise_replay_counter noattr) (rao_cnt 0 (Zrepeat 0 128)) c).

(* the externals the program calls (QuickProof.Env: nondet_u8, nondet_size, the check gp_assert) and the counter
   piece's wg_counter_validate (at Counter.CS) *)
Definition rao_imports (cs: compspecs) : funspecs :=
  [QuickProof.Env.nondet_u8_spec; QuickProof.Env.nondet_size_spec; QuickProof.Env.gp_assert_spec;
   wg_counter_validate_spec].

Definition rao_G : funspecs := [rao_upto_spec; rao_new_counter_spec; rao_main_spec].
