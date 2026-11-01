(* law handshake: main's phase P2, segment A (statements 37..42): hhs3_S1 x25519 gv L FR -> hhs3_p2_SA x25519 aead_enc gv L FR.
*)
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
Require Import WgNoise.proof.harness.handshake.hhs3_p2_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Local Open Scope logic.
(* the shim's globals main does not read in segment A *)
Definition hhs3_p2_A_rest (gv: globals) (S: shim) : mpred :=
  !! shim_ok S &&
  (@data_at Noise.CS Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
   @data_at Noise.CS Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
   @data_at Noise.CS Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   @data_at Noise.CS Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
   @data_at Noise.CS Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   @data_at Noise.CS Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow) * refwarn gv).

#[local] Instance hhs3_p2_A_cceN : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.

Lemma hhs3_p2_A_long sh (v: val) p : @data_at Noise.CS sh tlong v p = @data_at W_handshake sh tlong v p.
Proof. apply equal_f, (@data_at_change_composite Noise.CS W_handshake _ sh tlong v v); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

Lemma hhs3_p2_A_shim gv S sec nsec : shim_state gv (shim_set_real S sec nsec) =
  @data_at W_handshake Ews tlong (Vlong sec) (gv HC._wg_shim_real_sec) *
  @data_at W_handshake Ews tlong (Vlong nsec) (gv HC._wg_shim_real_nsec) *
  hhs3_p2_A_rest gv S.
Proof.
  unfold shim_state, hhs3_p2_A_rest. cbn [shim_set_real s_boot s_rsec s_rnsec s_log s_logprev s_u32 s_allocs
    s_fails s_frees s_failnext s_released s_rlallow].
  rewrite <- !hhs3_p2_A_long.
  assert (E: shim_ok (shim_set_real S sec nsec) = shim_ok S) by reflexivity. rewrite E.
  apply pred_ext; Intros; entailer!.
Qed.
Local Open Scope Z_scope.

Lemma hhs3_p2_A_log S r : Zlength r = 32 -> s_log (shim_draw S r) = r.
Proof.
  intros Hr. unfold shim_draw; cbn [s_log]. rewrite Hr. change (Z.min 32 32) with 32.
  rewrite sublist_same by auto. rewrite sublist_nil'. 2: reflexivity. apply app_nil_r.
Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p2_A_ok {Espec: OracleKind} gv L FR :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_S1 x25519 gv L FR) hhs3_p2_A
    (overridePost (hhs3_p2_SA x25519 aead_enc gv L FR) (hhs3_R gv)).
Proof.
  intros HH. unfold hhs3_S1, hhs3_Delta, hhs3_R, hhs3_p2_A. simplify_func_tycontext. abbreviate_semax.
  Intros R S m1 m2 a0 f0 l0.
  unfold hhs3_lvars, hhs3_scr_tmp, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
  forward_call (Ews, m1). Intros M0.
  forward_call (Tsh, l_imgb L, Ews, m1, M0).
  forward_call (gv, S). Intros vret. destruct vret as [sec ns]; cbn [fst snd] in *.
  rewrite hhs3_p2_A_shim. Intros.
  forward. forward.
  forward_call (Tsh, l_ts L, sec, Int64.repr ns).
  gather_SEP (data_at _ tlong _ (gv HC._wg_shim_real_sec)) (data_at _ tlong _ (gv HC._wg_shim_real_nsec))
    (hhs3_p2_A_rest gv S).
  rewrite <- hhs3_p2_A_shim.
  assert (HE: t_entry (hhs3_TA0 L) (hs_addr (l_pb L)) = Some (hhs3_EB L)).
  { unfold t_entry, hhs3_TA0; cbn [t_D sfind]. rewrite if_true by auto. reflexivity. }
  assert_PROP (isptr (l_pb L) /\ isptr (l_wa L)) as HPtr by entailer!.
  destruct HPtr as [HPb HPw].
  forward_call (Tsh, l_snap L, Tsh, l_pb L, hhs3_PB0 x25519 R L, Tsh, l_ita L, hhs3_TA0 L, hhs3_EB L).
  { (* hs_take's round-4 side conditions *)
    split; [unfold hhs3_EB; cbn; destruct (l_pb L); try contradiction; discriminate
           | cbn; unfold id_addr; destruct (l_wa L); try contradiction; discriminate]. }
  change (itable Tsh (l_ita L) (hhs3_TA0 L)) with (itable Tsh (d_itab (hhs3_DA x25519 R L)) (hhs3_TA0 L)).
  assert (HP: hs_in_pool (hhs3_TA0 L) (l_pb L)) by (exists (hhs3_EB L); split; [exact HE | reflexivity]).
  forward_call (gv, shim_set_real S sec (Int64.repr ns), Int64.zero, Ews, m1, M0, Tsh, l_pb L,
    hhs3_PB0 x25519 R L, Tsh, l_wa L, hhs3_DA x25519 R L, Tsh, hhs3_TA0 L).
  Intros vret. destruct vret as [r idx]; cbn [fst snd] in *.
  assert (Eci: ci_res x25519 aead_enc (hhs3_DA x25519 R L) (hhs3_PB0 x25519 R L) M0
                 (shim_set_real S sec (Int64.repr ns)) r idx =
               hhs3_ci x25519 aead_enc R L (mkIni M0 sec ns r idx)) by reflexivity.
  rewrite Eci in *.
  destruct (hhs3_ci x25519 aead_enc R L (mkIni M0 sec ns r idx)) as [[ok1 M] Hs] eqn:Eci2.
  cbn [fst snd] in *.
  forward.
  assert (Hid: id_has (d_id (hhs3_DA x25519 R L)) = mi_ok (hhs3_IA x25519 R)) by reflexivity.
  rewrite Hid.
  set (S' := shim_set_real S sec (Int64.repr ns)).
  set (Sf := if mi_ok (hhs3_IA x25519 R) then (if ok1 then shim_u32 (shim_draw S' r) idx else shim_draw S' r)
             else S').
  assert (Hcnt: hhs3_cnt Sf a0 f0 l0).
  { subst Sf S'. destruct (mi_ok (hhs3_IA x25519 R)), ok1; exact H0. }
  assert (Hlog: mi_ok (hhs3_IA x25519 R) = true -> s_log Sf = r).
  { intros Hm. subst Sf. rewrite Hm. destruct ok1; apply hhs3_p2_A_log; auto. }
  assert (Hu32: ok1 = true -> s_u32 Sf = idx).
  { intros Ho. subst Sf. destruct (mi_ok (hhs3_IA x25519 R)) eqn:Hm.
    - rewrite Ho. reflexivity.
    - exfalso. unfold hhs3_ci, create_initiation_model in Eci2. rewrite Hid in Eci2. try rewrite Hm in Eci2. cbn [negb] in Eci2.
      injection Eci2 as E1 _ _. congruence. }
  change (d_itab (hhs3_DA x25519 R L)) with (l_ita L).
  fold Sf.
  unfold hhs3_p2_SA, hhs3_p2_scr, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps, hhs3_lvars.
  Exists R Sf m1 m2 a0 f0 l0 (mkIni M0 sec ns r idx) ok1 M Hs.
  unfold hhs3_ts; cbn [app i_M0 i_sec i_nsec i_r i_idx].
  entailer!.
Qed.

End Seg.
