(* law config_any: main's phase PA1, statements 0..5: boot clock, raw0, setup_device(&w, &it, &pt, raw0), pub, setup_peer(&p, &w, pub, NULL, 1).
   (states: hcf5_defs.v).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.config_any.hcf5_world.
Require Import WgNoise.proof.harness.config_any.hcf5_cut.
Require Import WgNoise.proof.harness.config_any.hcf5_globals.
Require Import WgNoise.proof.harness.config_any.hcf5_spec.
Require Import WgNoise.proof.harness.config_any.hcf5_defs.
Require Import WgNoise.proof.harness.config_any.hcf5_conv.
Require Import WgNoise.proof.harness.config_any.hcf5_pure.
Require WgNoise.harness.x_config_any.code.

#[local] Existing Instance W_config_any.
Local Open Scope Z_scope.

Module HCFA := WgNoise.harness.x_config_any.code.

#[local] Instance hcf5_pa1_cceN : change_composite_env Noise.CS W_config_any.
Proof. make_cs_preserve Noise.CS W_config_any. Defined.

Lemma hcf5_pa1_tulong_cs sh v p :
  @data_at Noise.CS sh tulong v p = @data_at W_config_any sh tulong v p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W_config_any _ sh tulong v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

Definition hcf5_pa1_rest (gv: globals) (S: shim) : mpred :=
  (@data_at Noise.CS Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
   @data_at Noise.CS Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
   @data_at Noise.CS Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
   @data_at Noise.CS Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   @data_at Noise.CS Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
   @data_at Noise.CS Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   @data_at Noise.CS Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow))%logic.

Lemma hcf5_pa1_core_open gv S :
  shim_core gv S = (!! shim_ok S &&
    (@data_at W_config_any Ews tulong (Vlong (s_boot S)) (gv HCFA._wg_shim_boottime_ns) *
     hcf5_pa1_rest gv S))%logic.
Proof.
  unfold shim_core, hcf5_pa1_rest. rewrite <- hcf5_pa1_tulong_cs. rewrite !sepcon_assoc. reflexivity.
Qed.

(* the shim after the boot clock store *)
Definition hcf5_pa1_S1 (v: int64) : shim :=
  mkShim v Int64.zero Int64.zero zeros32 zeros32 Int.zero Int64.zero Int64.zero Int64.zero false
         Int64.zero false.

#[local] Instance hcf5_pa1_cceH : change_composite_env HCS W_config_any.
Proof. make_cs_preserve HCS W_config_any. Defined.

(* nondet_bytes's result as hbytes *)
Lemma hcf5_pa1_nd sh n bs p : Zlength bs = n -> Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  @data_at W_config_any sh (tarray tuchar n) (map (fun b => Vint (Int.repr b)) bs) p =
  hbytes sh (map Byte.repr bs) p.
Proof.
  intros Hn Hb. subst n. unfold hbytes, bytes. rewrite Zlength_map.
  rewrite (@data_at_change_composite HCS W_config_any _ sh (tarray tuchar (Zlength bs))
             (map Vubyte (map Byte.repr bs)) (map Vubyte (map Byte.repr bs)) (JMeq_refl _))
    by prove_cs_preserve_type.
  f_equal. rewrite map_map. induction Hb; simpl; [reflexivity |]. f_equal; [| assumption].
  unfold Vubyte. rewrite Byte.unsigned_repr by (unfold Byte.max_unsigned in *; simpl in *; lia). reflexivity.
Qed.

Section PA1.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcf5_PA1_ok {Espec: OracleKind} gv L FR :
  hcf5_hyps x25519 ->
  semax (hcf5_Delta x25519) (hcf5_S0 gv L FR) hcf5_PA1
    (overridePost (hcf5_SA1 x25519 gv L FR) (hcf5_R gv)).
Proof.
  intros HH. unfold hcf5_S0, hcf5_Delta, hcf5_R, hcf5_PA1. simplify_func_tycontext.
  abbreviate_semax.
  unfold hcf5_lvars, hcf5_pre; cbn [app].
  rewrite shim_state_ex4. Intros w.
  forward_call tt.
  Intros v.
  unfold shim_state4. rewrite (hcf5_pa1_core_open gv hcf5_shim0). Intros. forward.
  gather_SEP 7 8 9. replace_SEP 0 (shim_state4 gv (hcf5_pa1_S1 v) w).
  1: unfold shim_state4; rewrite hcf5_pa1_core_open; entailer!; apply derives_refl.
  rewrite !hcf5_conv_bytes.
  forward_call (l_raw0 L, 32, Tsh). Intros bs.
  rewrite (hcf5_pa1_nd Tsh 32 bs) by tauto.
  rewrite <- !hcf5_conv_bytes.
  forward_call (gv, hcf5_pa1_S1 v, w, Tsh, l_w L, l_it L, l_pt L, Tsh, l_raw0 L, map Byte.repr bs).
  { rewrite Zlength_map; tauto. }
  Intros sec.
  rewrite !hcf5_conv_bytes.
  forward_call (l_pub L, 32, Tsh). Intros bp.
  rewrite (hcf5_pa1_nd Tsh 32 bp) by tauto.
  set (R := mkRunF (map Byte.repr bs) sec v (map Byte.repr bp)).
  change (setup_dev x25519 (l_w L) (l_it L) (l_pt L) (map Byte.repr bs) sec (s_boot (hcf5_pa1_S1 v)))
    with (hcf5_D0 x25519 R L).
  forward_call (gv, Tsh, l_p L, Tsh, l_w L, hcf5_D0 x25519 R L, nullval, Tsh, l_pub L, r_pub R, nullval, zeros32,
                Int64.repr 1).
  { rewrite if_true by reflexivity. cancel. }
  { simpl; rewrite Zlength_map; tauto. }
  rewrite !if_true by reflexivity.
  change (d_ptab (hcf5_D0 x25519 R L)) with (l_pt L).
  change (setup_peer_val x25519 (hcf5_D0 x25519 R L) (l_w L) (l_p L) nullval (r_pub R) zeros32 (Int64.repr 1))
    with (hcf5_P0 x25519 R L).
  assert_PROP (Zlength w = 5). { unfold shim_state4, refwarn4. entailer!. }
  unfold hcf5_SA1.
  Exists R (shim_draw (hcf5_pa1_S1 v) sec) w.
  unfold hcf5_globs, hcf5_lvars, hcf5_pre; cbn [app].
  entailer!.
  unfold hcf5_run_ok; simpl; rewrite !Zlength_map; tauto.
Qed.

End PA1.
