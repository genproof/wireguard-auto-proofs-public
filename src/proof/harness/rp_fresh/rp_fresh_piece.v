(* Law rp_fresh (harness/rp_fresh.c), the harness piece: the specifications and the bodies of its functions
   new_counter, any_u64 and main, in the law's world W_rp_fresh, against the counter piece's
   wg_counter_validate_spec (src/proof/counter/counter_spec.v, at Counter.CS), the external world at W_rp_fresh
   and the harness's check gp_assert.

   Main's loop keeps the model of the window (counter_spec.v: top, the list L of accepted nonces, the bitmap)
   and the harness's own variables in step: n was never accepted (every nonce given is different from n), and
   either nothing was accepted (accepted_any = 0, top = 0) or top = newest + 1, the newest accepted nonce plus
   one.  At the end, cnt_ok top L n follows from n < R and n + W >= newest. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.counter.counter_spec.
Require Import WgNoise.proof.harness.rp_common.rp_worlds.
Require WgNoise.proof.harness.counter.hcnt_defs3.
Require WgNoise.contracts.rp_fresh.
Require Import WgNoise.harness.rp_fresh.code.

Module D := WgNoise.proof.harness.counter.hcnt_defs3.

#[local] Existing Instance W_rp_fresh.

Definition tnrc := Tstruct _noise_replay_counter noattr.

(* the harness's struct noise_replay_counter, in W_rp_fresh (the lock is never written) *)
Definition rpf_c (top: Z) (bm: list Z) : reptype tnrc :=
  (Vlong (Int64.repr top), (Vundef, map (fun w => Vlong (Int64.repr w)) bm)).

(* the harness unit, in the world compspecs *)
Definition u_rpf : unit_ctx :=
  mk_unit W_rp_fresh (QPvarspecs WgNoise.contracts.rp_fresh.Harness.qp) WgNoise.harness.rp_fresh.code.prog.

Definition rpf_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition rpf_main_spec : ident * funspec :=
  (_main, QPmain_spec_ext' WgNoise.contracts.rp_fresh.whole_prog tt rpf_post).

(* new_counter(c): a new key's replay window, all zero *)
Definition rpf_new_counter_spec :=
  DECLARE _new_counter
  WITH sh: share, c: val
  PRE [ tptr tnrc ]
    PROP (writable_share sh) PARAMS (c) SEP (data_at_ sh tnrc c)
  POST [ tvoid ]
    PROP () RETURN () SEP (data_at sh tnrc (rpf_c 0 (Zrepeat 0 128)) c).

(* any_u64(): any 64-bit value *)
Definition rpf_any_u64_spec :=
  DECLARE _any_u64
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tulong ] EX n: Z,
    PROP (0 <= n <= Int64.max_unsigned) RETURN (Vlong (Int64.repr n)) SEP ().

(* the externals the program calls (QuickProof.Env: nondet_u8, nondet_u32 and the harness's check gp_assert),
   and the counter piece's wg_counter_validate (at Counter.CS) *)
Definition rpf_imports (cs: compspecs) : funspecs :=
  [QuickProof.Env.nondet_u8_spec; QuickProof.Env.nondet_u32_spec; QuickProof.Env.gp_assert_spec;
   wg_counter_validate_spec].

Definition rpf_G : funspecs := [rpf_new_counter_spec; rpf_any_u64_spec; rpf_main_spec].

Definition rpf_V : varspecs := QPvarspecs WgNoise.contracts.rp_fresh.Harness.qp.
Definition rpf_Gprog : funspecs := rpf_imports W_rp_fresh ++ rpf_G.

Lemma body_new_counter : semax_body rpf_V rpf_Gprog f_new_counter rpf_new_counter_spec.
Proof.
  start_function.
  unfold data_at_, field_at_, tnrc. simpl default_val.
  forward.
  forward_for_simple_bound 128 (EX i: Z, PROP ()
    LOCAL (temp _c c)
    SEP (data_at sh (Tstruct _noise_replay_counter noattr)
           (Vlong (Int64.repr 0), (Vundef, Zrepeat (Vlong (Int64.repr 0)) i ++ Zrepeat Vundef (128 - i))) c))%assert.
  - entailer!.
  - forward.
    rewrite D.upd_Znth_Zrepeat_step by lia. entailer!.
  - entailer!.
Qed.

Lemma body_any_u64 : semax_body rpf_V rpf_Gprog f_any_u64 rpf_any_u64_spec.
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

#[local] Instance rpf_CCE : change_composite_env Counter.CS W_rp_fresh.
Proof. make_cs_preserve Counter.CS W_rp_fresh. Defined.

Lemma rpf_c_change sh top bm v:
  @data_at W_rp_fresh sh tnrc (rpf_c top bm) v =
  @data_at Counter.CS sh (Tstruct counter_spec._noise_replay_counter noattr) (cnt_val top Vundef bm) v.
Proof.
  symmetry. unfold tnrc.
  exact (f_equal (fun f => f v) (@data_at_change_composite Counter.CS W_rp_fresh rpf_CCE sh
    (Tstruct _noise_replay_counter noattr) (cnt_val top Vundef bm) (rpf_c top bm) (JMeq_refl _) eq_refl)).
Qed.

(* main's precondition: keep gvars, forget the globals (main never reads one) and the external state *)
Lemma rpf_main_pre {Espec: OracleKind} Delta (prog: QP.program function) (gv: globals) R c Post:
  semax Delta (PROP () LOCAL (gvars gv) SEP (TT) * R)%logic c Post ->
  semax Delta (close_precondition nil (@main_pre unit prog tt gv) * R)%logic c Post.
Proof.
  intros H. eapply semax_pre; [|apply H]; clear H.
  unfold main_pre, PROPx, LOCALx, SEPx, local, lift1.
  intro rho. unfold close_precondition. simpl. unfold_lift. normalize.
  rewrite prop_true_andp; [apply sepcon_derives; auto; apply TT_right | split; auto; hnf; reflexivity].
Qed.

(* the loop invariant's relation between the model (top) and the harness's variables *)
Definition rpf_track (top newest aa: Z) : Prop :=
  (aa = 0 /\ top = 0) \/ (aa = 1 /\ top = newest + 1).

(* one call of the loop: the model after counter_validate on other <> n *)
Lemma rpf_track_step top L newest aa other:
  0 <= other -> rpf_track top newest aa ->
  rpf_track (cnt_top' top L other)
    (if cnt_ok top L other && ((aa =? 0) || (newest <? other)) then other else newest)%bool
    (if cnt_ok top L other then 1 else aa).
Proof.
  intros Ho Ht. unfold cnt_top'. destruct (cnt_ok top L other); simpl; [|exact Ht].
  right. split; [reflexivity|].
  destruct Ht as [[-> ->] | [-> ->]]; simpl; [lia|].
  destruct (Z.ltb_spec newest other); simpl; lia.
Qed.

Lemma rpf_notin_step top L n other:
  other <> n -> ~ In n L -> ~ In n (cnt_L' top L other).
Proof.
  intros Hne Hn. unfold cnt_L'. destruct (cnt_ok top L other); auto.
  intros [E|E]; auto.
Qed.

(* the check: n is accepted *)
Lemma rpf_final top L bm newest aa n:
  cnt_inv top L bm -> ~ In n L -> rpf_track top newest aa ->
  0 <= n < CNT_R -> (aa = 0 \/ newest <= n + CNT_W) ->
  cnt_ok top L n = true.
Proof.
  intros Hinv Hn Ht Hr Hw. pose proof (cnt_top_range _ _ _ Hinv).
  unfold cnt_ok. rewrite !andb_true_iff. repeat split.
  - apply Z.ltb_lt. lia.
  - apply Z.ltb_lt. lia.
  - apply Z.leb_le. unfold CNT_W in *. destruct Ht as [[-> ->]|[-> ->]]; lia.
  - apply negb_true_iff. destruct (existsb (Z.eqb n) L) eqn:E; auto.
    apply existsb_exists in E as [x [Hx E]]. apply Z.eqb_eq in E. subst. contradiction.
Qed.

Lemma body_main : semax_body rpf_V rpf_Gprog f_main rpf_main_spec.
Proof.
  unfold rpf_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  simpl fn_body; simpl fn_params; simpl fn_return.
  change (fun rho => ?A rho * ?B rho)%logic with (A * B)%logic.
  apply rpf_main_pre.
  simpl app. simplify_func_tycontext.
  process_stackframe_of.
  repeat rewrite <- data_at__offset_zero.
  unfold rpf_post.
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (TT))%assert
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  abbreviate_semax.
  forward_call (Tsh, v_window).
  forward_call tt. Intros n.
  forward. forward.
  forward_loop (EX top: Z, EX L: list Z, EX bm: list Z, EX newest: Z, EX aa: Z,
    PROP (cnt_inv top L bm; ~ In n L; 0 <= newest <= Int64.max_unsigned; rpf_track top newest aa)
    LOCAL (temp _n (Vlong (Int64.repr n)); temp _newest (Vlong (Int64.repr newest));
           temp _accepted_any (Vint (Int.repr aa)); lvar _window tnrc v_window; gvars gv)
    SEP (data_at Tsh tnrc (rpf_c top bm) v_window; TT))%assert
  break: (EX top: Z, EX L: list Z, EX bm: list Z, EX newest: Z, EX aa: Z,
    PROP (cnt_inv top L bm; ~ In n L; 0 <= newest <= Int64.max_unsigned; rpf_track top newest aa)
    LOCAL (temp _n (Vlong (Int64.repr n)); temp _newest (Vlong (Int64.repr newest));
           temp _accepted_any (Vint (Int.repr aa)); lvar _window tnrc v_window; gvars gv)
    SEP (data_at Tsh tnrc (rpf_c top bm) v_window; TT))%assert.
  { Exists 0 (@nil Z) (Zrepeat 0 128) 0 0. entailer!.
    split; [apply D.cnt_inv_init | left; auto]. }
  { Intros top L bm newest aa.
    forward_call tt. Intros b.
    forward_if.
    2:{ forward. Exists top L bm newest aa. entailer!. }
    forward_call tt. Intros other.
    forward_if.
    { (* other <> n: counter_validate on other (the call and the cast to bool are stepped separately) *)
      rewrite rpf_c_change.
      eapply semax_seq' with (P' := (EX bm': list Z,
        PROP (cnt_inv (cnt_top' top L other) (cnt_L' top L other) bm')
        LOCAL (temp _accepted (Val.of_bool (cnt_ok top L other)); temp _other (Vlong (Int64.repr other));
               temp _n (Vlong (Int64.repr n)); temp _newest (Vlong (Int64.repr newest));
               temp _accepted_any (Vint (Int.repr aa)); lvar _window tnrc v_window; gvars gv)
        SEP (data_at Tsh tnrc (rpf_c (cnt_top' top L other) bm') v_window; TT))%assert).
      { eapply semax_seq'. forward_call (Tsh, v_window, top, L, bm, Vundef, other). apply ENTAIL_refl.
        abbreviate_semax. Intros bm'. forward.
        Exists bm'. rewrite <- rpf_c_change.
        replace (force_val (sem_cast tbool tbool (Val.of_bool (cnt_ok top L other))))
          with (Val.of_bool (cnt_ok top L other)) by (destruct (cnt_ok top L other); reflexivity).
        entailer!. }
      abbreviate_semax. Intros bm'.
      assert (Hne: other <> n) by (intro; subst; contradiction).
      forward_if (temp _t'5 (Val.of_bool (cnt_ok top L other && ((aa =? 0) || (newest <? other)))%bool)).
      { assert (Hok: cnt_ok top L other = true) by (destruct (cnt_ok top L other); [auto | inv H9]).
        destruct H3 as [[-> Htop]|[-> Htop]].
        - forward_if.
          + forward. entailer!. rewrite Hok. reflexivity.
          + exfalso. auto.
        - forward_if.
          + exfalso. discriminate.
          + forward. forward. entailer!.
            rewrite Hok. simpl. unfold Int64.cmpu. rewrite D.ltu_repr by rep_lia.
            destruct (newest <? other); reflexivity. }
      { assert (Hok: cnt_ok top L other = false) by (destruct (cnt_ok top L other); [inv H9 | auto]).
        forward. entailer!. rewrite Hok. reflexivity. }
      forward_if (temp _newest (Vlong (Int64.repr
        (if (cnt_ok top L other && ((aa =? 0) || (newest <? other)))%bool then other else newest)))).
      { forward. entailer!. destruct (_ && _)%bool; [reflexivity | inv H9]. }
      { forward. entailer!. destruct (_ && _)%bool; [inv H9 | reflexivity]. }
      forward_if (temp _accepted_any (Vint (Int.repr (if cnt_ok top L other then 1 else aa)))).
      { forward. entailer!. destruct (cnt_ok top L other); [reflexivity | inv H9]. }
      { forward. entailer!. destruct (cnt_ok top L other); [inv H9 | reflexivity]. }
      Exists (cnt_top' top L other) (cnt_L' top L other) bm'
        (if (cnt_ok top L other && ((aa =? 0) || (newest <? other)))%bool then other else newest)
        (if cnt_ok top L other then 1 else aa).
      entailer!.
      split3; [apply rpf_notin_step; auto | destruct (_ && _)%bool; lia | apply rpf_track_step; [lia|auto]]. }
    { forward. Exists top L bm newest aa. entailer!. } }
  (* the check *)
  Intros top L bm newest aa.
  forward_if (temp _t'7 (Val.of_bool ((n <? CNT_R) && ((aa =? 0) || (newest <=? n + CNT_W)))%bool)).
  { match type of H4 with _ < Int64.unsigned ?e =>
      let E := fresh in assert (E: Int64.unsigned e = CNT_R) by reflexivity; rewrite E in H4 end.
    rewrite Int64.unsigned_repr in H4 by rep_lia.
    assert (Hlt: (n <? CNT_R) = true) by (apply Z.ltb_lt; lia).
    destruct H3 as [[-> Ht]|[-> Ht]].
    - forward_if.
      + forward. entailer!. rewrite Hlt. reflexivity.
      + exfalso. auto.
    - forward_if.
      + exfalso. discriminate.
      + forward. forward. entailer!.
        rewrite Hlt. simpl. unfold Int64.cmpu.
        rewrite D.ltu_repr by (rewrite D.CNT_R_val in H4; rep_lia).
        unfold CNT_W. destruct (Z.ltb_spec (n + 8128) newest), (Z.leb_spec newest (n + 8128)); try reflexivity; lia. }
  { match type of H4 with _ >= Int64.unsigned ?e =>
      let E := fresh in assert (E: Int64.unsigned e = CNT_R) by reflexivity; rewrite E in H4 end.
    rewrite Int64.unsigned_repr in H4 by rep_lia.
    forward. entailer!. replace (n <? CNT_R) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  forward_if (EX top': Z, EX bm': list Z,
    PROP () LOCAL (lvar _window tnrc v_window; gvars gv)
    SEP (data_at Tsh tnrc (rpf_c top' bm') v_window; TT))%assert.
  { assert (Hc: ((n <? CNT_R) && ((aa =? 0) || (newest <=? n + CNT_W)))%bool = true)
      by (destruct (_ && _)%bool; [auto | inv H4]).
    rewrite andb_true_iff, orb_true_iff, Z.ltb_lt, Z.eqb_eq, Z.leb_le in Hc.
    assert (Hok: cnt_ok top L n = true) by (apply (rpf_final top L bm newest aa n); auto; lia).
    rewrite rpf_c_change.
    eapply semax_seq' with (P' := (EX bm': list Z,
      PROP ()
      LOCAL (temp _accepted__1 (Val.of_bool true); lvar _window tnrc v_window; gvars gv)
      SEP (data_at Tsh tnrc (rpf_c (cnt_top' top L n) bm') v_window; TT))%assert).
    { eapply semax_seq'. forward_call (Tsh, v_window, top, L, bm, Vundef, n). apply ENTAIL_refl.
      abbreviate_semax. Intros bm'. forward.
      Exists bm'. rewrite <- rpf_c_change.
      replace (force_val (sem_cast tbool tbool (Val.of_bool (cnt_ok top L n))))
        with (Val.of_bool (cnt_ok top L n)) by (destruct (cnt_ok top L n); reflexivity).
      rewrite Hok. entailer!. }
    abbreviate_semax. Intros bm'.
    forward_call (Int.one).
    Exists (cnt_top' top L n) bm'. entailer!. }
  { forward. Exists top bm. entailer!. }
  Intros top' bm'.
  forward.
  sep_apply (data_at_data_at_ Tsh tnrc). cancel.
Qed.

Theorem rpf_piece : piece_ok [u_rpf] rpf_imports rpf_G.
Proof.
  split.
  - repeat constructor; simpl; intuition discriminate.
  - repeat constructor; exists u_rpf; (split; [left; reflexivity|]).
    + exists f_new_counter; split; [reflexivity | exact body_new_counter].
    + exists f_any_u64; split; [reflexivity | exact body_any_u64].
    + exists f_main; split; [reflexivity | exact body_main].
Qed.
