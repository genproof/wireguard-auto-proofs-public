(* law keypairs, segment Op0 part A, piece A1: statements 0..5 of the op 0
   branch (a0 / f0 / fr0 = the shim's counters; dead = nondet_u8() % 8 == 0; k = malloc(sizeof(struct mk));
   if (k == NULL) continue). States: hkp5_segOp0_A_defs.v; "Op0 part A". *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.keypairs.hkp5_defs.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_defs.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_A_defs.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

Lemma hkp5_o0A1_tulong_cs {cs1 cs2: compspecs} sh v p :
  @data_at cs1 sh tulong v p = @data_at cs2 sh tulong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible; simpl.
  split; intros (?&?&?&?&?); (repeat split); auto;
    destruct p; try contradiction; unfold align_compatible in *;
    (apply align_compatible_rec_by_value with Mint64; [reflexivity|]);
    apply (align_compatible_rec_by_value_inv _ _ Mint64) in H2; auto.
Qed.

Lemma hkp5_o0A1_shim_fold gv S : shim_ok S ->
  (@data_at Noise.CS Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
   @data_at Noise.CS Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
   @data_at Noise.CS Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
   @data_at Noise.CS Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
   @data_at Noise.CS Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   @data_at Noise.CS Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
   @data_at Noise.CS Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   @data_at Noise.CS Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow))%logic
  |-- shim_core gv S.
Proof. intros H. unfold shim_core. apply andp_right; [apply prop_right; exact H | apply derives_refl]. Qed.

Lemma hkp5_o0A1_bool2val b : bool2val b = Val.of_bool b.
Proof. destruct b; reflexivity. Qed.

Lemma hkp5_o0A_1_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps FR i R :
  hkp5_model_facts -> x25519_props x25519 ->
  semax (hkp5_Delta hkp5_G_Op0) (hkp5_PL0 x25519 F V steps FR i 0) hkp5_o0A_s1
    (overridePost (EX Y: hkp5_dyn, EX dead: bool, EX k: val, hkp5_o0A_K x25519 F V steps FR i Y dead k)
       (loop1_ret_assert (hkp5_Icont x25519 F V steps FR i) R)).
Proof.
  intros HF HX.
  unfold hkp5_PL0, hkp5_Delta.
  Intros Y.
  unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
  cbn [app].
  abbreviate_semax.
  unfold hkp5_o0A_s1.
  (* a0 / f0 / fr0: the shim's counters *)
  unfold shim_state4 at 1, shim_core at 1. Intros. match goal with Hs: shim_ok _ |- _ => rename Hs into HSok end.
  rewrite (@hkp5_o0A1_tulong_cs Noise.CS W_keypairs _ _ (f_gv F _wg_shim_allocs)).
  rewrite (@hkp5_o0A1_tulong_cs Noise.CS W_keypairs _ _ (f_gv F _wg_shim_alloc_failures)).
  rewrite (@hkp5_o0A1_tulong_cs Noise.CS W_keypairs _ _ (f_gv F _wg_shim_frees)).
  change _wg_shim_allocs with KC._wg_shim_allocs.
  change _wg_shim_alloc_failures with KC._wg_shim_alloc_failures.
  change _wg_shim_frees with KC._wg_shim_frees.
  forward. forward. forward.
  rewrite (@hkp5_o0A1_tulong_cs W_keypairs Noise.CS _ _ (f_gv F KC._wg_shim_allocs)).
  rewrite (@hkp5_o0A1_tulong_cs W_keypairs Noise.CS _ _ (f_gv F KC._wg_shim_alloc_failures)).
  rewrite (@hkp5_o0A1_tulong_cs W_keypairs Noise.CS _ _ (f_gv F KC._wg_shim_frees)).
  change KC._wg_shim_allocs with _wg_shim_allocs.
  change KC._wg_shim_alloc_failures with _wg_shim_alloc_failures.
  change KC._wg_shim_frees with _wg_shim_frees.
  sep_apply (hkp5_o0A1_shim_fold (f_gv F) (y_S Y) HSok).
  (* dead = nondet_u8() % 8 == 0 *)
  forward_call tt. Intros u.
  forward.
  { entailer!. match goal with Hc: _ /\ Int.repr 8 = Int.mone |- _ => apply proj2 in Hc;
      apply (f_equal Int.unsigned) in Hc; rewrite Int.unsigned_repr in Hc by rep_lia; discriminate end. }
  set (dead := Int.eq (Int.mods (Int.repr u) (Int.repr 8)) (Int.repr 0)).
  (* k = malloc(sizeof(struct mk)) *)
  forward_call (t_mk5, f_gv F).
  Intros k.
  rewrite hkp5_o0A1_bool2val.
  destruct (eq_dec k nullval) as [Hk | Hk].
  { (* malloc returned NULL: continue *)
    subst k.
    forward_if.
    { forward.
      unfold hkp5_Icont, hkp5_St.
      destruct R as [?r1 ?r2 ?r3 ?r4]. cbn [RA_continue loop1_ret_assert]. Exists Y.
      unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
      cbn [app].
      unfold shim_state4; entailer!. }
    { exfalso. auto. } }
  forward_if.
  { contradiction. }
  forward.
  destruct R as [?r1 ?r2 ?r3 ?r4]. cbn [RA_normal overridePost loop1_ret_assert].
  Exists Y dead k.
  unfold hkp5_o0A_K, hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
  cbn [app].
  unfold shim_state4; entailer!.
Qed.
