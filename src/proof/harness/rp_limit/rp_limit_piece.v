(* The harness piece of law rp_limit (harness/rp_limit.c): upto, any_u64, new_counter and main, proved in
   W_rp_limit against wg_counter_validate's shared specification (counter_spec.v, at Counter.CS) and the
   external world.  Interface: rp_limit_spec.v.

   main: whatever nonces were given to the new counter, the invariant cnt_inv top L bm holds; the last nonce
   n = REJECT_AFTER + upto(U64_MAX - REJECT_AFTER) is at least CNT_R, so cnt_ok top L n is false and
   counter_validate rejects it. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.harness.rp_common.rp_worlds.
Require Import WgNoise.proof.counter.counter_spec.
Require WgNoise.proof.harness.counter.hcnt_defs3.
Require Import WgNoise.proof.harness.rp_limit.rp_limit_spec.
Require WgNoise.contracts.rp_limit.
Require Import WgNoise.harness.rp_limit.code.

#[local] Existing Instance W_rp_limit.

Definition rp_limit_V : varspecs := QPvarspecs WgNoise.contracts.rp_limit.Harness.qp.
Definition rp_limit_Gprog : funspecs := rp_limit_imports W_rp_limit ++ rp_limit_G.

Lemma body_upto : semax_body rp_limit_V rp_limit_Gprog f_upto rp_limit_upto_spec.
Proof.
  start_function.
  forward_call tt. Intros v.
  forward_if (temp _t'2 (Vlong (Int64.repr (Z.min v max)))).
  { forward. entailer!. rewrite Z.min_l by lia. reflexivity. }
  { forward. entailer!. rewrite Z.min_r by lia. reflexivity. }
  forward. Exists (Z.min v max). entailer!.
Qed.

Lemma body_any_u64 : semax_body rp_limit_V rp_limit_Gprog f_any_u64 rp_limit_any_u64_spec.
Proof.
  start_function.
  eapply semax_seq' with (P' := (EX hi:Z, PROP (0 <= hi <= Int.max_unsigned)
                                         LOCAL (temp _high (Vlong (Int64.repr hi))) SEP ())%assert).
  { eapply semax_seq'. forward_call tt. apply ENTAIL_refl. Intros hi. forward. Exists hi. entailer!. }
  abbreviate_semax. Intros hi.
  forward_call tt. Intros lo.
  forward.
  Exists (Int64.unsigned (Int64.or (Int64.shl (Int64.repr hi) (Int64.repr 32)) (Int64.repr lo))).
  entailer!. rewrite Int64.repr_unsigned; auto.
Qed.

Lemma body_new_counter : semax_body rp_limit_V rp_limit_Gprog f_new_counter rp_limit_new_counter_spec.
Proof.
  start_function.
  unfold rp_tnrc. forward.
  forward_for_simple_bound 128 (EX i: Z, PROP ()
    LOCAL (temp _c c)
    SEP (data_at sh (Tstruct _noise_replay_counter noattr)
           (Vlong (Int64.repr 0), (Vundef, Zrepeat (Vlong (Int64.repr 0)) i ++ Zrepeat Vundef (128 - i))) c))%assert.
  - entailer!.
  - forward. rewrite WgNoise.proof.harness.counter.hcnt_defs3.upd_Znth_Zrepeat_step by lia. entailer!.
  - forward.
Qed.

(* main's precondition: keep gvars, forget the globals (main never reads one) and the external state *)
Lemma rp_limit_main_pre {Espec: OracleKind} Delta (prog: QP.program function) (gv: globals) R c Post:
  semax Delta (PROP () LOCAL (gvars gv) SEP (TT) * R)%logic c Post ->
  semax Delta (close_precondition nil (@main_pre unit prog tt gv) * R)%logic c Post.
Proof.
  intros H. eapply semax_pre; [|apply H]; clear H.
  unfold main_pre, PROPx, LOCALx, SEPx, local, lift1.
  intro rho. unfold close_precondition. simpl. unfold_lift. normalize.
  rewrite prop_true_andp; [apply sepcon_derives; auto; apply TT_right | split; auto; hnf; reflexivity].
Qed.

(* the window as counter_validate's specification sees it: the same struct, in Counter.CS *)
#[local] Instance rp_limit_CCE : change_composite_env Counter.CS W_rp_limit.
Proof. make_cs_preserve Counter.CS W_rp_limit. Defined.

Lemma rp_counter_change sh top bm v:
  @data_at W_rp_limit sh rp_tnrc (rp_counter_val top bm) v =
  @data_at Counter.CS sh (Tstruct counter_spec._noise_replay_counter noattr) (cnt_val top Vundef bm) v.
Proof.
  symmetry. unfold rp_tnrc.
  exact (f_equal (fun f => f v) (@data_at_change_composite Counter.CS W_rp_limit rp_limit_CCE sh
    (Tstruct _noise_replay_counter noattr) (cnt_val top Vundef bm) (rp_counter_val top bm) (JMeq_refl _) eq_refl)).
Qed.

Lemma body_main : semax_body rp_limit_V rp_limit_Gprog f_main rp_limit_main_spec.
Proof.
  unfold rp_limit_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  simpl fn_body; simpl fn_params; simpl fn_return.
  change (fun rho => ?A rho * ?B rho)%logic with (A * B)%logic.
  apply rp_limit_main_pre.
  simpl app. simplify_func_tycontext.
  process_stackframe_of.
  abbreviate_semax.
  forward_call (Tsh, v_window).
  forward_loop (EX top: Z, EX L: list Z, EX bm: list Z,
    PROP (cnt_inv top L bm)
    LOCAL (lvar _window rp_tnrc v_window; gvars gv)
    SEP (data_at Tsh rp_tnrc (rp_counter_val top bm) v_window; TT))%assert
  break: (EX top: Z, EX L: list Z, EX bm: list Z,
    PROP (cnt_inv top L bm)
    LOCAL (lvar _window rp_tnrc v_window; gvars gv)
    SEP (data_at Tsh rp_tnrc (rp_counter_val top bm) v_window; TT))%assert.
  { Exists 0 (@nil Z) (Zrepeat 0 128). entailer!. apply WgNoise.proof.harness.counter.hcnt_defs3.cnt_inv_init. }
  { Intros top L bm.
    forward_call tt. Intros b.
    forward_if.
    2:{ forward. Exists top L bm. entailer!. }
    forward_call tt. Intros n.
    rewrite rp_counter_change.
    forward_call (Tsh, v_window, top, L, bm, Vundef, n).
    Intros bm'.
    rewrite <- rp_counter_change.
    Exists (cnt_top' top L n) (cnt_L' top L n) bm'. entailer!. }
  Intros top L bm.
  forward_call (Int64.max_unsigned - CNT_R).
  Intros v.
  forward.
  rewrite rp_counter_change.
  forward_call (Tsh, v_window, top, L, bm, Vundef, CNT_R + v).
  { entailer!. unfold CNT_R, CNT_W. simpl. do 3 f_equal.
    change (Int64.sub (Int64.sub (Int64.not (Int64.repr 0)) (Int64.repr 8128)) (Int64.repr 1))
      with (Int64.repr (Int64.max_unsigned - 8128 - 1)).
    rewrite add64_repr. reflexivity. }
  { unfold CNT_R, CNT_W in *. rep_lia. }
  Intros bm'.
  replace (cnt_ok top L (CNT_R + v)) with false
    by (unfold cnt_ok; replace (CNT_R + v <? CNT_R) with false by (symmetry; apply Z.ltb_ge; lia);
        rewrite andb_false_r, !andb_false_l; reflexivity).
  forward_call (Int.one).
  unfold abbreviate in POSTCONDITION. subst POSTCONDITION. unfold rp_limit_post.
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (TT))%assert
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  abbreviate_semax.
  forward.
  rewrite <- rp_counter_change. sep_apply (data_at_data_at_ Tsh rp_tnrc). cancel.
Qed.

Theorem rp_limit_piece : piece_ok [u_rp_limit] rp_limit_imports rp_limit_G.
Proof.
  split.
  - repeat constructor; simpl; intuition discriminate.
  - repeat constructor; exists u_rp_limit; (split; [left; reflexivity|]).
    + exists f_upto; split; [reflexivity | exact body_upto].
    + exists f_any_u64; split; [reflexivity | exact body_any_u64].
    + exists f_new_counter; split; [reflexivity | exact body_new_counter].
    + exists f_main; split; [reflexivity | exact body_main].
Qed.
