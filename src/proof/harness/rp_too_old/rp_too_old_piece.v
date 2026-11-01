(* The harness piece of law rp_too_old (harness/rp_too_old.c): upto, any_u64, new_counter and main, proved in
   W_rp_too_old against the counter piece's wg_counter_validate_spec (counter_spec.v, at Counter.CS) and the
   external world at W_rp_too_old.  Interface: rp_too_old_spec.v.

   main's loop keeps the counter's model (top, L) of counter_spec.v and the invariant
   newest = 0 \/ newest < top: an accepted nonce is below the new top.  So after the loop, with
   newest > COUNTER_WINDOW_SIZE, every n <= newest - COUNTER_WINDOW_SIZE - 1 has n + 1 + W < top, and cnt_ok
   rejects it. *)
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
Require Import WgNoise.proof.harness.rp_too_old.rp_too_old_spec.
Require WgNoise.contracts.rp_too_old.
Require Import WgNoise.harness.rp_too_old.code.

#[local] Existing Instance W_rp_too_old.

Definition rp_too_old_V : varspecs := QPvarspecs WgNoise.contracts.rp_too_old.Harness.qp.
Definition rp_too_old_Gprog : funspecs := rp_too_old_imports W_rp_too_old ++ rp_too_old_G.

Lemma body_upto : semax_body rp_too_old_V rp_too_old_Gprog f_upto rp_too_old_upto_spec.
Proof.
  start_function.
  forward_call tt. Intros v.
  forward_if (temp _t'2 (Vlong (Int64.repr (Z.min v m)))).
  { forward. entailer!. rewrite Z.min_l by lia. auto. }
  { forward. entailer!. rewrite Z.min_r by lia. auto. }
  forward. Exists (Z.min v m). entailer!.
Qed.

Lemma body_any_u64 : semax_body rp_too_old_V rp_too_old_Gprog f_any_u64 rp_too_old_any_u64_spec.
Proof.
  start_function.
  eapply semax_seq' with (P' := (EX hi: Z, PROP (0 <= hi <= Int.max_unsigned)
                                          LOCAL (temp _high (Vlong (Int64.repr hi))) SEP ())%assert).
  { eapply semax_seq'. forward_call tt. apply ENTAIL_refl. Intros hi. forward. Exists hi. entailer!. }
  abbreviate_semax. Intros hi.
  forward_call tt. Intros lo.
  forward.
  Exists (Int64.unsigned (Int64.or (Int64.shl (Int64.repr hi) (Int64.repr 32)) (Int64.repr lo))).
  entailer!. rewrite Int64.repr_unsigned; auto.
Qed.

Lemma body_new_counter : semax_body rp_too_old_V rp_too_old_Gprog f_new_counter rp_too_old_new_counter_spec.
Proof.
  start_function.
  forward.
  forward_for_simple_bound 128 (EX i: Z, PROP ()
    LOCAL (temp _c c)
    SEP (data_at sh (Tstruct _noise_replay_counter noattr)
           (Vlong (Int64.repr 0), (Vundef, Zrepeat (Vlong (Int64.repr 0)) i ++ Zrepeat Vundef (128 - i))) c))%assert.
  - entailer!.
  - forward.
    rewrite WgNoise.proof.harness.counter.hcnt_defs3.upd_Znth_Zrepeat_step by lia. entailer!.
  - entailer!.
Qed.

Definition tnrc := Tstruct _noise_replay_counter noattr.

(* the harness's struct noise_replay_counter, in W_rp_too_old (the lock is never written) *)
Definition rp_c (top: Z) (bm: list Z) : reptype tnrc :=
  (Vlong (Int64.repr top), (Vundef, map (fun w => Vlong (Int64.repr w)) bm)).

#[local] Instance rp_too_old_CCE : change_composite_env Counter.CS W_rp_too_old.
Proof. make_cs_preserve Counter.CS W_rp_too_old. Defined.

Lemma rp_c_change sh top bm v:
  @data_at W_rp_too_old sh tnrc (rp_c top bm) v =
  @data_at Counter.CS sh (Tstruct counter_spec._noise_replay_counter noattr) (cnt_val top Vundef bm) v.
Proof.
  symmetry. unfold tnrc.
  exact (f_equal (fun f => f v) (@data_at_change_composite Counter.CS W_rp_too_old rp_too_old_CCE sh
    (Tstruct _noise_replay_counter noattr) (cnt_val top Vundef bm) (rp_c top bm) (JMeq_refl _) eq_refl)).
Qed.

(* the loop invariant is kept by one call of counter_validate on nonce, and the update of newest *)
Lemma rp_too_old_step top L nonce newest:
  0 <= nonce -> (newest = 0 \/ newest < top) ->
  let newest' := if (cnt_ok top L nonce && (newest <? nonce))%bool then nonce else newest in
  newest' = 0 \/ newest' < cnt_top' top L nonce.
Proof.
  intros Hn Hinv newest'. subst newest'. unfold cnt_top'.
  destruct (cnt_ok top L nonce); simpl; [|auto].
  destruct (Z.ltb_spec newest nonce); lia.
Qed.

(* the final check: a nonce more than W below newest is rejected *)
Lemma rp_too_old_final top L newest n:
  newest < top -> 0 <= n -> n + CNT_W + 1 <= newest -> cnt_ok top L n = false.
Proof.
  intros H1 H2 H3. unfold cnt_ok.
  replace (top <=? n + 1 + CNT_W) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite !andb_false_r, andb_false_l. reflexivity.
Qed.

(* main's precondition: keep gvars, forget the globals (main never reads one) and the external state *)
Lemma rp_too_old_main_pre {Espec: OracleKind} Delta (prog: QP.program function) (gv: globals) R c Post:
  semax Delta (PROP () LOCAL (gvars gv) SEP (TT) * R)%logic c Post ->
  semax Delta (close_precondition nil (@main_pre unit prog tt gv) * R)%logic c Post.
Proof.
  intros H. eapply semax_pre; [|apply H]; clear H.
  unfold main_pre, PROPx, LOCALx, SEPx, local, lift1.
  intro rho. unfold close_precondition. simpl. unfold_lift. normalize.
  rewrite prop_true_andp; [apply sepcon_derives; auto; apply TT_right | split; auto; hnf; reflexivity].
Qed.

Lemma body_main : semax_body rp_too_old_V rp_too_old_Gprog f_main rp_too_old_main_spec.
Proof.
  unfold rp_too_old_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  simpl fn_body; simpl fn_params; simpl fn_return.
  change (fun rho => ?A rho * ?B rho)%logic with (A * B)%logic.
  apply rp_too_old_main_pre.
  simpl app. simplify_func_tycontext.
  process_stackframe_of.
  repeat rewrite <- data_at__offset_zero.
  abbreviate_semax.
  forward_call (Tsh, v_window).
  forward.
  fold (rp_c 0 (Zrepeat 0 128)).
  forward_loop (EX top: Z, EX L: list Z, EX bm: list Z, EX newest: Z,
    PROP (cnt_inv top L bm; 0 <= newest <= Int64.max_unsigned; newest = 0 \/ newest < top)
    LOCAL (temp _newest (Vlong (Int64.repr newest)); lvar _window tnrc v_window; gvars gv)
    SEP (data_at Tsh tnrc (rp_c top bm) v_window; TT))%assert
  break: (EX top: Z, EX L: list Z, EX bm: list Z, EX newest: Z,
    PROP (cnt_inv top L bm; 0 <= newest <= Int64.max_unsigned; newest = 0 \/ newest < top)
    LOCAL (temp _newest (Vlong (Int64.repr newest)); lvar _window tnrc v_window; gvars gv)
    SEP (data_at Tsh tnrc (rp_c top bm) v_window; TT))%assert.
  { Exists 0 (@nil Z) (Zrepeat 0 128) 0. entailer!.
    all: first [apply WgNoise.proof.harness.counter.hcnt_defs3.cnt_inv_init
               | destruct WgNoise.proof.harness.counter.hcnt_defs3.cnt_inv_init; auto]. }
  { Intros top L bm newest.
    forward_call tt. Intros b.
    forward_if.
    2:{ forward. Exists top L bm newest. entailer!. }
    forward_call tt. Intros nonce.
    rewrite rp_c_change.
    forward_call (Tsh, v_window, top, L, bm, Vundef, nonce).
    Intros bm'.
    rewrite <- rp_c_change.
    forward_if (temp _t'4 (Vint (if (cnt_ok top L nonce && (newest <? nonce))%bool then Int.one else Int.zero))).
    { forward. entailer!.
      destruct (cnt_ok top L nonce); [|inv H6]. simpl andb. unfold Int64.cmpu, Int64.ltu.
      rewrite !Int64.unsigned_repr by rep_lia.
      destruct (zlt newest nonce), (Z.ltb_spec newest nonce); try lia; reflexivity. }
    { forward. entailer!. destruct (cnt_ok top L nonce); [inv H6|]. reflexivity. }
    forward_if (temp _newest
      (Vlong (Int64.repr (if (cnt_ok top L nonce && (newest <? nonce))%bool then nonce else newest)))).
    { forward. entailer!. destruct (_ && _)%bool; [reflexivity | contradiction]. }
    { forward. entailer!. destruct (_ && _)%bool; [discriminate | reflexivity]. }
    Exists (cnt_top' top L nonce) (cnt_L' top L nonce) bm'
      (if (cnt_ok top L nonce && (newest <? nonce))%bool then nonce else newest).
    entailer!.
    split; [destruct (_ && _)%bool; lia | apply rp_too_old_step; lia]. }
  Intros top L bm newest.
  unfold abbreviate in POSTCONDITION. subst POSTCONDITION. unfold rp_too_old_post.
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (TT))%assert
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  abbreviate_semax.
  forward_if.
  { forward. sep_apply (data_at_data_at_ Tsh tnrc). cancel. }
  assert (Hlt: 8128 < newest) by (rewrite !Int64.unsigned_repr in H2 by rep_lia; lia).
  assert (Htop: newest < top) by lia.
  forward_call (newest - 8128 - 1).
  Intros u.
  forward.
  rewrite rp_c_change.
  forward_call (Tsh, v_window, top, L, bm, Vundef, newest - 8128 - 1 - u).
  Intros bm'.
  rewrite <- rp_c_change.
  forward_call (Int.one).
  { entailer!. rewrite (rp_too_old_final top L newest) by (unfold CNT_W; lia). reflexivity. }
  forward.
  sep_apply (data_at_data_at_ Tsh tnrc). cancel.
Qed.

Theorem rp_too_old_piece : piece_ok [u_rp_too_old] rp_too_old_imports rp_too_old_G.
Proof.
  split.
  - repeat constructor; simpl; intuition discriminate.
  - repeat constructor; exists u_rp_too_old; (split; [left; reflexivity|]).
    + exists f_upto; split; [reflexivity | exact body_upto].
    + exists f_any_u64; split; [reflexivity | exact body_any_u64].
    + exists f_new_counter; split; [reflexivity | exact body_new_counter].
    + exists f_main; split; [reflexivity | exact body_main].
Qed.
