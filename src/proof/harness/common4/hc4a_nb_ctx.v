(* the callee contexts of hc4_ctx.v whose compspecs-polymorphic import (nondet_bytes)
   is taken at the body's compspecs, restated at the compspecs without blake2s_ctx (hc4a_nb_cs.v). *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require Import WgNoise.proof.harness.common4.hc4a_nb_cs.

Section Ctx.
Variable x25519: list byte -> list byte -> list byte.
Variable CSw: compspecs.
Definition hc4nb_G_hs_randomize : funspecs :=
  [draw_boottime_spec; draw_hs_state_spec; @asm_env.nondet_bytes_spec CSknb; nondet_u32_spec].
Definition hc4nb_G_peer_randomize_rest : funspecs :=
  [nondet_u8_spec; draw_u64_spec; draw_boottime_spec; @asm_env.nondet_bytes_spec CSknb].
Definition hc4nb_G_hnodes_add : funspecs :=
  [bytes_eq_spec; (_quickproof_malloc, @malloc_spec' CSw); (_quickproof_free, @free_spec' CSw);
   @asm_env.nondet_bytes_spec CS4nb; nondet_u8_spec; setup_peer_spec x25519; draw_peer_refs4_spec].
Definition hc4nb_G_kents_add : funspecs :=
  [draw_steps_spec; (_quickproof_malloc, @malloc_spec' CSw); hnodes_pick4_spec CSw;
   P4.wg_index_hashtable_insert_spec; @asm_env.nondet_bytes_spec CS4nb; draw_boottime_spec; nondet_u8_spec;
   draw_u64_spec; nondet_u32_spec; draw_peer_refs4_spec].
End Ctx.
