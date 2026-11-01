(* (group snap of common4) child part: the shim snapshot bodies shim_take,
   shim_no_warning, shim_same. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require WgNoise.harness.x_cookie_mac.code WgNoise.harness.x_consume_initiation_any.code WgNoise.harness.x_keypairs.code
        WgNoise.harness.x_handshake.code WgNoise.harness.x_consume_response_any.code
        WgNoise.harness.x_handshake_receive.code.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_model3.

Module HCS4 := WgNoise.harness.x_cookie_mac.code.

(* a scalar data_at does not depend on the compspecs (shim_state is stated at Noise.CS) *)
Lemma hc4bs_data_at_tulong_cs {cs1 cs2: compspecs} sh (v: val) p :
  @data_at cs1 sh tulong v p = @data_at cs2 sh tulong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible, size_compatible, align_compatible.
  destruct p; simpl; try tauto.
  split; intros (?&?&?&?&?); repeat split; auto;
    (eapply align_compatible_rec_by_value; [reflexivity|]);
    (eapply align_compatible_rec_by_value_inv in H2; [exact H2 | reflexivity]).
Qed.

Lemma hc4bs_data_at_warn_cs {cs1 cs2: compspecs} sh (v: list val) p :
  @data_at cs1 sh (tarray tulong 5) v p = @data_at cs2 sh (tarray tulong 5) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible, size_compatible, align_compatible.
  destruct p; simpl; try tauto.
  split; intros (?&?&?&?&?); repeat split; auto;
    (eapply align_compatible_rec_Tarray; intros;
     eapply align_compatible_rec_Tarray_inv in H2; [|eassumption];
     eapply align_compatible_rec_by_value; [reflexivity|];
     eapply align_compatible_rec_by_value_inv in H2; [exact H2 | reflexivity]).
Qed.

Lemma hc4bs_warn_true w0 w :
  (forall j, 0 <= j < 5 -> Znth j w0 = Znth j w) -> warn_eqb w0 w = true.
Proof.
  intros E. unfold warn_eqb. simpl. rewrite !E by lia. rewrite !Int64.eq_true. reflexivity.
Qed.

Lemma hc4bs_warn_false w0 w i :
  0 <= i < 5 -> Znth i w0 <> Znth i w -> warn_eqb w0 w = false.
Proof.
  intros Hi N. unfold warn_eqb. apply Bool.not_true_iff_false. intro T.
  rewrite forallb_forall in T. apply N. apply Int64.same_if_eq. apply T. simpl. lia.
Qed.

Ltac hc4bs_b := unfold bool2val, Int64.cmpu, Val.of_bool; simpl;
  repeat match goal with |- context [Int64.eq ?a ?b] => destruct (Int64.eq a b) end; reflexivity.

Ltac hc4bs_tf := match goal with
  | H: typed_true _ (if ?b then _ else _) |- _ => destruct b; [clear H | inversion H]
  | H: typed_false _ (if ?b then _ else _) |- _ => destruct b; [inversion H | clear H] end.

Section Fold.
#[local] Existing Instance Noise.CS.

(* shim_state4 from its unfolded globals, in the order of shim_core and refwarn4 *)
Lemma hc4bs_fold gv S w : shim_ok S -> Zlength w = 5 ->
  data_at Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
  data_at Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
  data_at Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
  data_at Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
  data_at Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
  data_at Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
  data_at Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
  data_at Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
  data_at Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
  data_at Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
  data_at Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
  data_at Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow) *
  data_at Ews (tarray tulong 5) (map Vlong w) (gv _wg_shim_refcount_warn)
  |-- shim_state4 gv S w.
Proof.
  intros. unfold shim_state4, shim_core, refwarn4. entailer!.
Qed.
End Fold.

Section Bodies.
#[local] Existing Instance CS4s.

#[local] Instance hc4bs_cc : change_composite_env CKS CS4s.
Proof. make_cs_preserve CKS CS4s. Defined.

Lemma hc4bs_take :
  @semax_body hc4_V_shim hc4_G_none CS4s HCS4.f_shim_take shim_take4_spec.
Proof.
  start_function.
  unfold shim_state4, shim_core, refwarn4. Intros.
  rewrite (@data_at__change_composite CKS CS4s _ shs t_shimsnap) by reflexivity.
  rewrite !(@hc4bs_data_at_tulong_cs Noise.CS CS4s). rewrite (@hc4bs_data_at_warn_cs Noise.CS CS4s).
  change HCS4._wg_shim_allocs with _wg_shim_allocs.
  change HCS4._wg_shim_alloc_failures with _wg_shim_alloc_failures.
  change HCS4._wg_shim_frees with _wg_shim_frees.
  change HCS4._wg_shim_peer_released with _wg_shim_peer_released.
  change HCS4._wg_shim_refcount_warn with _wg_shim_refcount_warn.
  freeze FR := (data_at _ _ _ (gv _wg_shim_boottime_ns)) (data_at _ _ _ (gv _wg_shim_real_sec))
    (data_at _ _ _ (gv _wg_shim_real_nsec)) (data_at _ _ _ (gv _wg_shim_random_log))
    (data_at _ _ _ (gv _wg_shim_random_log_prev)) (data_at _ _ _ (gv _wg_shim_random_u32))
    (data_at _ _ _ (gv _wg_shim_fail_next_alloc)) (data_at _ _ _ (gv _wg_shim_ratelimit_allow)).
  forward. forward. forward. forward. forward. forward. forward. forward.
  forward_for_simple_bound 5 (EX i: Z, PROP () LOCAL (gvars gv; temp HCS4._s s)
    SEP (FRZL FR;
         data_at shs t_shimsnap (Vlong (s_allocs S), (Vlong (s_fails S), (Vlong (s_frees S),
           (Vlong (s_released S), sublist 0 i (map Vlong w) ++ Zrepeat Vundef (5 - i))))) s;
         data_at Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs);
         data_at Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures);
         data_at Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees);
         data_at Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released);
         data_at Ews (tarray tulong 5) (map Vlong w) (gv _wg_shim_refcount_warn)))%assert.
  - entailer!.
  - forward. forward. entailer!.
    apply derives_refl'. f_equal. f_equal. f_equal. f_equal. f_equal. list_solve.
  - thaw FR.
    rewrite sublist_same by list_solve. rewrite Z.sub_diag, Zrepeat_0, app_nil_r.
    rewrite <- (@data_at_change_composite CKS CS4s _ shs t_shimsnap (shimsnap_val S w)) by
      (try apply JMeq_refl; reflexivity).
    unfold shim_state4, shim_core, refwarn4.
    rewrite !(@hc4bs_data_at_tulong_cs Noise.CS CS4s). rewrite (@hc4bs_data_at_warn_cs Noise.CS CS4s).
    go_lowerx. unfold stackframe_of; simpl. rewrite !sepcon_emp.
    repeat (apply andp_right; [apply prop_right; auto | ]). cancel.
Qed.

Lemma hc4bs_nowarn :
  @semax_body hc4_V_warn hc4_G_none CS4s HCS4.f_shim_no_warning shim_no_warning4_spec.
Proof.
  start_function.
  unfold shim_state4, refwarn4. Intros.
  erewrite (@data_at_change_composite CKS CS4s _ shs t_shimsnap (shimsnap_val S0 w0) _ (JMeq_refl _))
    by reflexivity.
  rewrite (@hc4bs_data_at_warn_cs Noise.CS CS4s).
  change HCS4._wg_shim_refcount_warn with _wg_shim_refcount_warn.
  freeze FR := (shim_core gv S).
  assert_PROP (Zlength (map Vlong w0) = 5) as Hw0.
  { unfold shimsnap_val. entailer!. simpl in H1. destruct H1 as (_&_&_&_&[? _]). exact H1. }
  rewrite Zlength_map in Hw0.
  unfold shimsnap_val.
  forward_for_simple_bound 5 (EX i: Z,
    PROP (forall j, 0 <= j < i -> Znth j w0 = Znth j w) LOCAL (gvars gv; temp HCS4._s s)
    SEP (FRZL FR;
         data_at shs t_shimsnap (Vlong (s_allocs S0), (Vlong (s_fails S0), (Vlong (s_frees S0),
           (Vlong (s_released S0), map Vlong w0)))) s;
         data_at Ews (tarray tulong 5) (map Vlong w) (gv _wg_shim_refcount_warn)))%assert.
  - entailer!.
  - cbv beta. Intros. forward. forward.
    forward_if.
    + forward.
      rewrite (hc4bs_warn_false w0 w i) by auto.
      thaw FR. unfold shim_state4, refwarn4.
      rewrite (@hc4bs_data_at_warn_cs Noise.CS CS4s).
      erewrite (@data_at_change_composite CKS CS4s _ shs t_shimsnap (shimsnap_val S0 w0) _ (JMeq_refl _))
        by reflexivity.
      unfold shimsnap_val. entailer!.
    + forward. entailer!.
      intros j Hj. destruct (zeq j i); [subst; apply Int64.same_if_eq; auto | apply H1; lia].
  - forward.
    rewrite (hc4bs_warn_true w0 w) by auto.
    thaw FR. unfold shim_state4, refwarn4.
    rewrite (@hc4bs_data_at_warn_cs Noise.CS CS4s).
    erewrite (@data_at_change_composite CKS CS4s _ shs t_shimsnap (shimsnap_val S0 w0) _ (JMeq_refl _))
      by reflexivity.
    unfold shimsnap_val. entailer!.
Qed.

Lemma hc4bs_same :
  @semax_body hc4_V_shim hc4_G_shim_same CS4s HCS4.f_shim_same shim_same4_spec.
Proof.
  start_function.
  unfold shim_state4, shim_core, refwarn4. Intros.
  erewrite (@data_at_change_composite CKS CS4s _ shs t_shimsnap (shimsnap_val S0 w0) _ (JMeq_refl _))
    by reflexivity.
  rewrite !(@hc4bs_data_at_tulong_cs Noise.CS CS4s).
  change HCS4._wg_shim_allocs with _wg_shim_allocs.
  change HCS4._wg_shim_alloc_failures with _wg_shim_alloc_failures.
  change HCS4._wg_shim_frees with _wg_shim_frees.
  change HCS4._wg_shim_peer_released with _wg_shim_peer_released.
  freeze FR := (data_at _ _ _ (gv _wg_shim_boottime_ns)) (data_at _ _ _ (gv _wg_shim_real_sec))
    (data_at _ _ _ (gv _wg_shim_real_nsec)) (data_at _ _ _ (gv _wg_shim_random_log))
    (data_at _ _ _ (gv _wg_shim_random_log_prev)) (data_at _ _ _ (gv _wg_shim_random_u32))
    (data_at _ _ _ (gv _wg_shim_fail_next_alloc)) (data_at _ _ _ (gv _wg_shim_ratelimit_allow))
    (data_at _ _ _ (gv _wg_shim_refcount_warn)).
  unfold shimsnap_val.
  forward. forward.
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    forward_if (PROPx [] (LOCALx [temp HCS4._t'1 (Val.of_bool
      (Int64.eq (s_allocs S0) (s_allocs S) && Int64.eq (s_fails S0) (s_fails S))); gvars gv; temp HCS4._s s]
      (SEPx R))) end.
  { forward. forward. forward. entailer!. rewrite H1. hc4bs_b. }
  { forward. entailer!. rewrite (Int64.eq_false _ _ H1). reflexivity. }
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    forward_if (PROPx [] (LOCALx [temp HCS4._t'2 (Val.of_bool
      (Int64.eq (s_allocs S0) (s_allocs S) && Int64.eq (s_fails S0) (s_fails S) &&
       Int64.eq (s_frees S0) (s_frees S))); gvars gv; temp HCS4._s s]
      (SEPx R))) end.
  { forward. forward. forward. entailer!. hc4bs_tf. hc4bs_b. }
  { forward. entailer!. hc4bs_tf. reflexivity. }
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    forward_if (PROPx [] (LOCALx [temp HCS4._t'3 (Val.of_bool
      (Int64.eq (s_allocs S0) (s_allocs S) && Int64.eq (s_fails S0) (s_fails S) &&
       Int64.eq (s_frees S0) (s_frees S) && Int64.eq (s_released S0) (s_released S))); gvars gv; temp HCS4._s s]
      (SEPx R))) end.
  { forward. forward. forward. entailer!. hc4bs_tf. hc4bs_b. }
  { forward. entailer!. hc4bs_tf. reflexivity. }
  thaw FR.
  rewrite !(@hc4bs_data_at_tulong_cs CS4s Noise.CS).
  match goal with |- semax _ (PROPx _ (LOCALx ?Q _)) _ _ =>
    apply semax_pre with (PROPx [] (LOCALx Q
      (SEPx [@data_at CKS shs t_shimsnap (shimsnap_val S0 w0) s; shim_state4 gv S w]))) end.
  { go_lowerx. sep_apply (hc4bs_fold gv S w H H0).
    erewrite (@data_at_change_composite CKS CS4s _ shs t_shimsnap (shimsnap_val S0 w0) _ (JMeq_refl _))
      by reflexivity.
    unfold shimsnap_val.
    repeat (apply andp_right; [apply prop_right; auto | ]). cancel. }
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    forward_if (PROPx [] (LOCALx [temp HCS4._t'4 (Val.of_bool (shim_eqb S0 w0 S w)); gvars gv;
      temp HCS4._s s] (SEPx R))) end.
  { forward_call (gv, shs, s, S0, w0, S, w).
    forward. unfold shim_eqb. hc4bs_tf. entailer!. destruct (warn_eqb w0 w); reflexivity. }
  { forward. unfold shim_eqb. hc4bs_tf. entailer!. }
  forward. entailer!. destruct (shim_eqb S0 w0 S w); reflexivity.
Qed.

End Bodies.

Theorem hc4b_snap_shim_ok :
  (@semax_body hc4_V_shim hc4_G_none CS4s WgNoise.harness.x_cookie_mac.code.f_shim_take shim_take4_spec) /\
  (@semax_body hc4_V_warn hc4_G_none CS4s WgNoise.harness.x_cookie_mac.code.f_shim_no_warning shim_no_warning4_spec) /\
  (@semax_body hc4_V_shim hc4_G_shim_same CS4s WgNoise.harness.x_cookie_mac.code.f_shim_same shim_same4_spec).
Proof.
  split; [exact hc4bs_take | split; [exact hc4bs_nowarn | exact hc4bs_same]].
Qed.
