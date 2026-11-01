(* law handshake: main's phase P1, segment A = statements 0..9: boot clock, ratelimit_allow, wg_noise_init, raw_a / raw_b, use_psk, psk, allocs0 / frees0 / fails0.
   (section P1). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.handshake.hhs3_spec.
Require Import WgNoise.proof.harness.handshake.hhs3_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_conv.
Require Import WgNoise.proof.harness.handshake.hhs3_p1_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Local Open Scope logic.
(* the shim's globals main does not touch in segment A *)
Definition hhs3_p1_A_rest (gv: globals) (S: shim) : mpred :=
  @data_at Noise.CS Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
  @data_at Noise.CS Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
  @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
  @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
  @data_at Noise.CS Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
  @data_at Noise.CS Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
  @data_at Noise.CS Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
  refwarn gv.

#[local] Instance hhs3_p1_A_cceN : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.
#[local] Instance hhs3_p1_A_cceH : change_composite_env HCS W_handshake.
Proof. make_cs_preserve HCS W_handshake. Defined.

Lemma hhs3_p1_A_ulong sh (v: val) p : @data_at Noise.CS sh tulong v p = @data_at W_handshake sh tulong v p.
Proof. apply equal_f, (@data_at_change_composite Noise.CS W_handshake _ sh tulong v v); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

Lemma hhs3_p1_A_bool sh (v: val) p : @data_at Noise.CS sh tbool v p = @data_at W_handshake sh tbool v p.
Proof. apply equal_f, (@data_at_change_composite Noise.CS W_handshake _ sh tbool v v); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

(* nondet_bytes' result, at the world, is hbytes *)
Lemma hhs3_p1_A_nd sh n (bs: list Z) p :
  Zlength bs = n -> Forall (fun b => 0 <= b <= Byte.max_unsigned)%Z bs ->
  @data_at W_handshake sh (tarray tuchar n) (map (fun b => Vint (Int.repr b)) bs) p =
  hbytes sh (map Byte.repr bs) p.
Proof.
  intros <- Hb. unfold hbytes. rewrite Zlength_map.
  rewrite <- (@data_at_change_composite HCS W_handshake _ sh (tarray tuchar (Zlength bs))
    (map (fun b => Vint (Int.repr b)) bs) (map (fun b => Vint (Int.repr b)) bs));
    [| apply JMeq_refl | prove_cs_preserve_type].
  f_equal. unfold bytes. rewrite map_map. apply map_ext_in. intros b Hin.
  rewrite Forall_forall in Hb. specialize (Hb b Hin).
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma hhs3_p1_A_shim gv S : shim_state gv S =
  !! shim_ok S &&
  (@data_at W_handshake Ews tulong (Vlong (s_boot S)) (gv HC._wg_shim_boottime_ns) *
   @data_at W_handshake Ews tulong (Vlong (s_allocs S)) (gv HC._wg_shim_allocs) *
   @data_at W_handshake Ews tulong (Vlong (s_fails S)) (gv HC._wg_shim_alloc_failures) *
   @data_at W_handshake Ews tulong (Vlong (s_frees S)) (gv HC._wg_shim_frees) *
   @data_at W_handshake Ews tbool (Val.of_bool (s_rlallow S)) (gv HC._wg_shim_ratelimit_allow) *
   hhs3_p1_A_rest gv S).
Proof.
  unfold shim_state, hhs3_p1_A_rest. f_equal.
  rewrite <- !hhs3_p1_A_ulong, <- !hhs3_p1_A_bool.
  apply pred_ext; cancel.
Qed.
Local Open Scope Z_scope.

(* use_psk = nondet_u8() & 1 *)
Lemma hhs3_p1_A_and1 u : 0 <= u <= Byte.max_unsigned ->
  Int.and (Int.repr u) (Int.repr 1) = if Z.odd u then Int.one else Int.zero.
Proof.
  intros Hu.
  change (Int.repr 1) with (Int.repr (two_p 1 - 1)). rewrite <- Int.zero_ext_and by lia.
  rewrite <- (Int.repr_unsigned (Int.zero_ext _ _)). rewrite Int.zero_ext_mod by (cbv; intuition congruence).
  rewrite Int.unsigned_repr by rep_lia. change (two_p 1) with 2.
  rewrite Zmod_odd. destruct (Z.odd u); reflexivity.
Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p1_A_ok {Espec: OracleKind} gv L FR :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_S0 gv L FR) hhs3_p1_A
    (overridePost (hhs3_p1_SA gv L FR) (hhs3_R gv)).
Proof.
  intros HH. unfold hhs3_S0, hhs3_Delta, hhs3_R, hhs3_p1_A. simplify_func_tycontext. abbreviate_semax.
  unfold hhs3_lvars, hhs3_scr_tmp; cbn [app].
  (* the shim's globals stay open during the segment *)
  rewrite (hhs3_p1_A_shim gv hhs3_shim0). Intros.
  forward_call tt. Intros v.
  forward. (* wg_shim_boottime_ns = ... *)
  forward. (* wg_shim_ratelimit_allow = true *)
  forward_call (gv, zeros32, zeros32, Int64.zero).
  rewrite !(hhs3_conv_bytes Tsh 32 (l_rawa L)), !(hhs3_conv_bytes Tsh 32 (l_rawb L)),
    !(hhs3_conv_bytes Tsh 32 (l_psk L)).
  forward_call (l_rawa L, 32, Tsh). Intros bsa.
  forward_call (l_rawb L, 32, Tsh). Intros bsb.
  rewrite (hhs3_p1_A_nd Tsh 32 bsa) by assumption. rewrite (hhs3_p1_A_nd Tsh 32 bsb) by assumption.
  forward_call tt. Intros u.
  forward. rewrite (hhs3_p1_A_and1 u) by assumption.
  apply semax_if_seq. forward_if.
  - forward_call (l_psk L, 32, Tsh). Intros bsp. rewrite (hhs3_p1_A_nd Tsh 32 bsp) by assumption.
    forward. forward. forward.
    unfold hhs3_p1_SA, hhs3_p1_rest, hhs3_globs, hhs3_cnt_temps, hhs3_lvars, hhs3_scr_tmp.
    Exists (map Byte.repr bsa) (map Byte.repr bsb) (map Byte.repr bsp) (Z.odd u)
      (mkShim v Int64.zero Int64.zero zeros32 zeros32 Int.zero Int64.zero Int64.zero Int64.zero false
              Int64.zero true)
      Int64.zero Int64.zero Int64.zero.
    rewrite (hhs3_p1_A_shim gv). cbn [app s_boot s_allocs s_fails s_frees s_rlallow hhs3_shim0 Val.of_bool].
    change (hhs3_p1_A_rest gv hhs3_shim0) with (hhs3_p1_A_rest gv (mkShim v Int64.zero Int64.zero zeros32
      zeros32 Int.zero Int64.zero Int64.zero Int64.zero false Int64.zero true)).
    entailer!.
    rewrite !Zlength_map. refine (conj H1 (conj H3 (conj H7 (conj _ _)))).
    { intros Hu; rewrite Hu in H6; contradiction. }
    repeat split.
  - rewrite <- (hhs3_conv_bytes Tsh 32 (l_psk L)).
    forward_call (Tsh, l_psk L, Byte.zero, 32).
    forward. forward. forward.
    unfold hhs3_p1_SA, hhs3_p1_rest, hhs3_globs, hhs3_cnt_temps, hhs3_lvars, hhs3_scr_tmp.
    Exists (map Byte.repr bsa) (map Byte.repr bsb) (Zrepeat Byte.zero 32) (Z.odd u)
      (mkShim v Int64.zero Int64.zero zeros32 zeros32 Int.zero Int64.zero Int64.zero Int64.zero false
              Int64.zero true)
      Int64.zero Int64.zero Int64.zero.
    rewrite (hhs3_p1_A_shim gv). cbn [app s_boot s_allocs s_fails s_frees s_rlallow hhs3_shim0 Val.of_bool].
    change (hhs3_p1_A_rest gv hhs3_shim0) with (hhs3_p1_A_rest gv (mkShim v Int64.zero Int64.zero zeros32
      zeros32 Int.zero Int64.zero Int64.zero Int64.zero false Int64.zero true)).
    entailer!.
    rewrite !Zlength_map. repeat split; auto.
Qed.

End Seg.
