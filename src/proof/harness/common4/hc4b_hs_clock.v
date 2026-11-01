(* (common4 group hs): body of draw_real_clock (v4 spec: shim_state4, warnings w
   untouched), adapted from hc3b_draws_proofs.v's hc3b_draws_body_draw_real_clock. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require WgNoise.harness.x_handshake.code.

Module FH := WgNoise.harness.x_handshake.code.

#[local] Existing Instance CSk.

Lemma hc4b_hs_clock_tlong_cs {cs1 cs2: compspecs} sh (v: val) p :
  @data_at cs1 sh tlong v p = @data_at cs2 sh tlong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible, size_compatible, align_compatible.
  destruct p; simpl; try tauto.
  split; intros (?&?&?&?&?); repeat split; auto;
    (eapply align_compatible_rec_by_value; [reflexivity|]);
    (eapply align_compatible_rec_by_value_inv in H2; [exact H2 | reflexivity]).
Qed.

Lemma hc4b_hs_clock_body :
  @semax_body hc4_V_real_clock hc4_G_draw_real_clock CSk FH.f_draw_real_clock draw_real_clock4_spec.
Proof.
start_function.
forward_call tt. Intros v.
unfold shim_state4, shim_core. Intros.
change _wg_shim_real_sec with FH._wg_shim_real_sec. change _wg_shim_real_nsec with FH._wg_shim_real_nsec.
rewrite !(@hc4b_hs_clock_tlong_cs Noise.CS CSk).
freeze FR := - (data_at _ _ _ (gv FH._wg_shim_real_sec)) (data_at _ _ _ (gv FH._wg_shim_real_nsec)).
forward.
forward_call tt. Intros ns.
forward.
thaw FR.
assert (Hm: Int.unsigned (Int.modu (Int.repr ns) (Int.repr 1000000000)) = ns mod 1000000000).
{ unfold Int.modu. rewrite (Int.unsigned_repr ns), (Int.unsigned_repr 1000000000) by rep_lia.
  apply Int.unsigned_repr. pose proof (Z.mod_pos_bound ns 1000000000). rep_lia. }
Exists v (Int.unsigned (Int.modu (Int.repr ns) (Int.repr 1000000000))).
unfold shim_state4, shim_core, shim_set_real; simpl s_boot; simpl s_rsec; simpl s_rnsec; simpl s_log; simpl s_logprev;
  simpl s_u32; simpl s_allocs; simpl s_fails; simpl s_frees; simpl s_failnext; simpl s_released; simpl s_rlallow.
rewrite !(@hc4b_hs_clock_tlong_cs Noise.CS CSk).
change _wg_shim_real_sec with FH._wg_shim_real_sec. change _wg_shim_real_nsec with FH._wg_shim_real_nsec.
go_lowerx. rewrite Hm. unfold stackframe_of; simpl. rewrite !sepcon_emp.
pose proof (Z.mod_pos_bound ns 1000000000).
repeat (apply andp_right; [apply prop_right; unfold shim_ok in *; simpl; repeat split; tauto || lia | ]).
cancel.
apply andp_right; [apply prop_right; unfold shim_ok in *; simpl; repeat split; tauto || lia | cancel].
Qed.
