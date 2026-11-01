(* the harness piece's interface for law counter (harness/counter.c), in the world compspecs
   W_counter of wg3_worlds.v.  Same content as the earlier
   counter_harness.v, at W_counter instead of W_cnt. *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.counter.counter_spec.
Require WgNoise.contracts.x_counter.
Require WgNoise.harness.x_counter.code.

(* the harness unit, in the world compspecs *)
Definition u_hcnt3 : unit_ctx :=
  mk_unit W_counter (QPvarspecs WgNoise.contracts.x_counter.Harness.qp) WgNoise.harness.x_counter.code.prog.

Definition hcnt3_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition hcnt3_main_spec : ident * funspec :=
  (WgNoise.harness.x_counter.code._main,
   QPmain_spec_ext' WgNoise.contracts.x_counter.whole_prog tt hcnt3_post).

Definition hcnt3_draw_steps_spec :=
  DECLARE WgNoise.harness.x_counter.code._draw_steps
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tulong ] EX n: Z,
    PROP (0 <= n <= Int64.max_unsigned) RETURN (Vlong (Int64.repr n)) SEP ().

Definition hcnt3_draw_u64_spec :=
  DECLARE WgNoise.harness.x_counter.code._draw_u64
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tulong ] EX n: Z,
    PROP (0 <= n <= Int64.max_unsigned) RETURN (Vlong (Int64.repr n)) SEP ().

(* the external world (at W_counter) and the counter piece's wg_counter_validate (at Counter.CS) *)
Definition hcnt3_imports (cs: compspecs) : funspecs :=
  @asm_env.env_specs W_counter ++ [wg_counter_validate_spec].

Definition hcnt3_G : funspecs := [hcnt3_draw_steps_spec; hcnt3_draw_u64_spec; hcnt3_main_spec].
