(* the function context of each common.h v2 body proof = exactly the
   specifications of its callees, as they appear in every law's context hc4_imports (u_cs u) ++ hc4_G_<law>
   (hc4_prog.v), the compspecs-polymorphic imports (nondet_bytes) at the body's small compspecs (related by
   hc3_xcs.v's hc3_nondet_bytes_xcs); and the globals it reads or writes (V0).

   Body lemma of function X (files hc4_body_*.v):  @semax_body (hc4_V_X) (hc4_G_X ...) CS0 f_X X_spec. *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.prims.prim_api.
Require WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.

Module P4 := WgNoise.proof.protocol4.prot_specs4.

Section Ctx.
Variable x25519: list byte -> list byte -> list byte.
Variable CSw: compspecs.

(* CS0 = CSk *)
Definition hc4_G_setup_device : funspecs :=
  [bytes_set_spec; P4.wg_cookie_checker_init_spec; P4.wg_cookie_checker_precompute_device_keys_spec;
   P4.wg_noise_set_static_identity_private_key_spec x25519].
Definition hc4_G_draw_real_clock : funspecs := [draw_u64_spec; nondet_u32_spec].
Definition hc4_G_hs_randomize : funspecs :=
  [draw_boottime_spec; draw_hs_state_spec; @asm_env.nondet_bytes_spec CSk; nondet_u32_spec].
Definition hc4_G_peer_randomize_rest : funspecs :=
  [nondet_u8_spec; draw_u64_spec; draw_boottime_spec; @asm_env.nondet_bytes_spec CSk].
Definition hc4_G_draw_peer_refs : funspecs := [nondet_u8_spec; nondet_u32_spec].
Definition hc4_G_none : funspecs := [].   (* pr_same_but_cookie, shim_take, shim_no_warning, replay_counter_fresh,
                                             le32_load, kents_hashed *)

(* CS0 = CSkh *)
Definition hc4_G_hs_take : funspecs := [bytes_copy_spec].
Definition hc4_G_hs_same : funspecs := [bytes_eq_spec].   (* hs_same, hs_same_but_next *)
Definition hc4_G_hs_zeroed_from : funspecs := [bytes_eq_spec; bytes_zero_spec].

(* CS0 = CS4 *)
Definition hc4_G_pr_take : funspecs := [ck_take_spec].
Definition hc4_G_pr_same : funspecs := [pr_same_but_cookie4_spec CSw; ck_same_spec].
Definition hc4_G_dev_take : funspecs := [bytes_copy_spec].   (* dev_take, kents_snap; skb_take at CS4skb *)
Definition hc4_G_dev_same : funspecs := [bytes_eq_spec].     (* dev_same, kent_same_but_next; skb_same at CS4skb *)
Definition hc4_G_hnodes_add : funspecs :=
  [bytes_eq_spec; (_quickproof_malloc, @malloc_spec' CSw); (_quickproof_free, @free_spec' CSw);
   @asm_env.nondet_bytes_spec CS4; nondet_u8_spec; setup_peer_spec x25519; draw_peer_refs4_spec].
Definition hc4_G_hnodes_snap : funspecs := [hs_take4_spec; pr_take4_spec].
Definition hc4_G_hnodes_same_except : funspecs := [hs_same4_spec CSw; pr_same4_spec CSw].
Definition hc4_G_free : funspecs := [(_quickproof_free, @free_spec' CSw)].   (* hnodes_free, kents_free *)
Definition hc4_G_hnodes_pick : funspecs := [nondet_size_spec].
Definition hc4_G_kents_add : funspecs :=
  [draw_steps_spec; (_quickproof_malloc, @malloc_spec' CSw); hnodes_pick4_spec CSw;
   P4.wg_index_hashtable_insert_spec; @asm_env.nondet_bytes_spec CS4; draw_boottime_spec; nondet_u8_spec;
   draw_u64_spec; nondet_u32_spec; draw_peer_refs4_spec].
Definition hc4_G_kents_same : funspecs := [kent_same_but_next4_spec CSw].
Definition hc4_G_kents_same_but_next : funspecs := [kent_same_but_next4_spec CSw; table_has_spec].

(* CS0 = CS4s *)
Definition hc4_G_shim_same : funspecs := [shim_no_warning4_spec].
End Ctx.

(* the globals read or written *)
Definition hc4_V_shim : varspecs :=
  [(_wg_shim_allocs, tulong); (_wg_shim_alloc_failures, tulong); (_wg_shim_frees, tulong);
   (_wg_shim_peer_released, tulong); (_wg_shim_refcount_warn, tarray tulong 5)].
Definition hc4_V_warn : varspecs := [(_wg_shim_refcount_warn, tarray tulong 5)].
Definition hc4_V_real_clock : varspecs := [(_wg_shim_real_sec, tlong); (_wg_shim_real_nsec, tlong)].
