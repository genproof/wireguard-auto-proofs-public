(* law create_any: Segment A = main's statements 0..7 (boot clock, wg_noise_init, raw / pub / psk, use_psk, setup_device, m_identity_of), from hca5_S0 to hca5_SA.
   (states, conventions), spec-create_any3 (v1 notes of the same segment); v1 proof of the
   segment: (port it: same C where the C did not change). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.create_any.hca3_model.
Require Import WgNoise.proof.harness.create_any.hca5_spec.
Require Import WgNoise.proof.harness.create_any.hca5_defs.
Require Import WgNoise.proof.harness.create_any.hca5_conv.
Require WgNoise.harness.x_create_any.code.
#[local] Existing Instance W_create_any.
Local Open Scope logic.

(* the shim's globals main does not touch in segment A *)
Definition hca5_PA_rest (gv: globals) (S: shim) : mpred :=
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
  @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow).

#[local] Instance hca5_PA_cceN : change_composite_env Noise.CS W_create_any.
Proof. make_cs_preserve Noise.CS W_create_any. Defined.
#[local] Instance hca5_PA_cceH : change_composite_env HCS W_create_any.
Proof. make_cs_preserve HCS W_create_any. Defined.

Lemma hca5_PA_ulong sh (v: val) p : @data_at Noise.CS sh tulong v p = @data_at W_create_any sh tulong v p.
Proof. apply equal_f, (@data_at_change_composite Noise.CS W_create_any _ sh tulong v v); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

Lemma hca5_PA_shim gv S w : shim_state4 gv S w =
  !! shim_ok S &&
  (@data_at W_create_any Ews tulong (Vlong (s_boot S)) (gv HC._wg_shim_boottime_ns) * hca5_PA_rest gv S *
   refwarn4 gv w).
Proof.
  unfold shim_state4, shim_core, hca5_PA_rest. rewrite sepcon_andp_prop'. f_equal.
  rewrite <- !hca5_PA_ulong.
  apply pred_ext; cancel.
Qed.

Definition hca5_PA_boot (S: shim) (v: int64) : shim :=
  mkShim v (s_rsec S) (s_rnsec S) (s_log S) (s_logprev S) (s_u32 S) (s_allocs S) (s_fails S) (s_frees S)
         (s_failnext S) (s_released S) (s_rlallow S).

Lemma hca5_PA_fold gv S w v : shim_ok S ->
  @data_at W_create_any Ews tulong (Vlong v) (gv HC._wg_shim_boottime_ns) * hca5_PA_rest gv S * refwarn4 gv w |--
  shim_state4 gv (hca5_PA_boot S v) w.
Proof.
  intros HS. rewrite hca5_PA_shim. apply andp_right; [apply prop_right; exact HS | apply derives_refl].
Qed.

(* nondet_bytes' result, at the world, is hbytes *)
Lemma hca5_PA_nd sh n (bs: list Z) p :
  Zlength bs = n -> Forall (fun b => 0 <= b <= Byte.max_unsigned)%Z bs ->
  @data_at W_create_any sh (tarray tuchar n) (map (fun b => Vint (Int.repr b)) bs) p =
  hbytes sh (map Byte.repr bs) p.
Proof.
  intros <- Hb. unfold hbytes. rewrite Zlength_map.
  rewrite <- (@data_at_change_composite HCS W_create_any _ sh (tarray tuchar (Zlength bs))
    (map (fun b => Vint (Int.repr b)) bs) (map (fun b => Vint (Int.repr b)) bs));
    [| apply JMeq_refl | prove_cs_preserve_type].
  f_equal. unfold bytes. rewrite map_map. apply map_ext_in. intros b Hin.
  rewrite Forall_forall in Hb. specialize (Hb b Hin).
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

(* use_psk = nondet_u8() & 1 *)
Lemma hca5_PA_and1 u : (0 <= u <= Byte.max_unsigned)%Z ->
  Int.and (Int.repr u) (Int.repr 1) = Int.repr (u mod 2).
Proof.
  intros Hu.
  change (Int.repr 1) with (Int.repr (two_p 1 - 1)). rewrite <- Int.zero_ext_and by lia.
  rewrite <- (Int.repr_unsigned (Int.zero_ext _ _)). rewrite Int.zero_ext_mod by (cbv; intuition congruence).
  rewrite Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma hca5_PA_ok {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_S0 gv L FR w)
    hca5_PA
    (overridePost (hca5_SA x25519 gv L FR w) (hca5_R gv)).
Proof.
  intros HH. unfold hca5_S0, hca5_Delta, hca5_R, hca5_PA. simplify_func_tycontext. abbreviate_semax.
  Intros S.
  unfold hca5_snap0, hca5_scr0, hca5_scr, hca5_lvars; cbn [app].
  rewrite (hca5_PA_shim gv S w). Intros.
  forward_call tt. Intros v.
  forward. (* wg_shim_boottime_ns = ... *)
  sep_apply (hca5_PA_fold gv S w v H).
  forward_call (gv, zeros32, zeros32, Int64.zero).
  rewrite <- !(hca5_conv_bytes Tsh 32 (l_raw L)), <- !(hca5_conv_bytes Tsh 32 (l_pub L)),
    <- !(hca5_conv_bytes Tsh 32 (l_psk L)).
  forward_call (l_raw L, 32, Tsh). Intros bsr.
  forward_call (l_pub L, 32, Tsh). Intros bsp.
  forward_call (l_psk L, 32, Tsh). Intros bsk.
  rewrite (hca5_PA_nd Tsh 32 bsr) by assumption. rewrite (hca5_PA_nd Tsh 32 bsp) by assumption.
  rewrite (hca5_PA_nd Tsh 32 bsk) by assumption.
  forward_call tt. Intros u.
  forward. rewrite (hca5_PA_and1 u) by assumption.
  forward_call (gv, hca5_PA_boot S v, w, Tsh, l_wa L, l_ita L, l_pta L, Tsh, l_raw L, map Byte.repr bsr).
  { rewrite Zlength_map; assumption. }
  Intros sec.
  unfold hca5_consts. repeat flatten_sepcon_in_SEP.
  forward_call (gv, Tsh, l_ia L, Tsh, l_raw L, map Byte.repr bsr).
  { rewrite Zlength_map; assumption. }
  unfold hca5_SA.
  Exists (mkRun5 (map Byte.repr bsr) sec v) (shim_draw (hca5_PA_boot S v) sec) (map Byte.repr bsp)
    (map Byte.repr bsk) (u mod 2).
  unfold hca5_globs, hca5_consts, hca5_snap0, hca5_scr, hca5_lvars, hca5_D, hca5_I; cbn [app r_raw r_sec r_boot].
  change (s_boot (hca5_PA_boot S v)) with v.
  entailer!.
  pose proof (Z.mod_pos_bound u 2 ltac:(lia)).
  unfold hca5_run_ok; cbn [r_raw r_sec r_boot]; rewrite !Zlength_map. repeat split; auto; lia.
Qed.
