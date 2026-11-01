(* The harness piece of law rp_duplicate (harness/rp_duplicate.c): new_counter, any_u64 and main, proved in
   W_rp_duplicate against counter_validate's shared specification (counter_spec.v, at Counter.CS) and the
   external world with gp_assert.  Interface: rpd_spec.v.

   main follows the model of counter_spec.v: the replay window is (top, L, bm) with cnt_inv top L bm, L the
   accepted nonces.  When n is accepted it joins L; L only grows (cnt_L'), so n stays in L through the second
   sequence of nonces, and then cnt_ok top L n is false: the second call with n returns 0. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.harness.rp_common.rp_worlds.
Require Import WgNoise.proof.counter.counter_spec.
Require WgNoise.proof.harness.counter.hcnt_defs3.
Require Import WgNoise.proof.harness.rp_duplicate.rpd_spec.
Require WgNoise.contracts.rp_duplicate.
Require Import WgNoise.harness.rp_duplicate.code.

#[local] Existing Instance W_rp_duplicate.

Definition rpd_V : varspecs := QPvarspecs WgNoise.contracts.rp_duplicate.Harness.qp.
Definition rpd_Gprog : funspecs := rpd_imports W_rp_duplicate ++ rpd_G.

(* the model: an accepted nonce stays accepted, and is then refused *)
Lemma rpd_L'_keeps top L x n: In n L -> In n (cnt_L' top L x).
Proof. intros H. unfold cnt_L'. destruct (cnt_ok top L x); [right|]; auto. Qed.

Lemma rpd_ok_in top L n: cnt_ok top L n = true -> In n (cnt_L' top L n).
Proof. intros H. unfold cnt_L'. rewrite H. left; auto. Qed.

Lemma rpd_refused top L n: In n L -> cnt_ok top L n = false.
Proof.
  intros H. unfold cnt_ok.
  replace (existsb (Z.eqb n) L) with true by (symmetry; apply existsb_exists; exists n; split; auto; apply Z.eqb_refl).
  rewrite andb_false_r. reflexivity.
Qed.

Lemma body_new_counter : semax_body rpd_V rpd_Gprog f_new_counter rpd_new_counter_spec.
Proof.
  start_function.
  forward.
  forward_for_simple_bound 128 (EX i: Z, PROP ()
    LOCAL (temp _c c)
    SEP (data_at sh rpd_tnrc
           (Vlong (Int64.repr 0), (Vundef, Zrepeat (Vlong (Int64.repr 0)) i ++ Zrepeat Vundef (128 - i))) c))%assert.
  - entailer!.
  - forward. rewrite WgNoise.proof.harness.counter.hcnt_defs3.upd_Znth_Zrepeat_step by lia. entailer!.
  - entailer!.
Qed.

Lemma body_any_u64 : semax_body rpd_V rpd_Gprog f_any_u64 rpd_any_u64_spec.
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

#[local] Instance rpd_CCE : change_composite_env Counter.CS W_rp_duplicate.
Proof. make_cs_preserve Counter.CS W_rp_duplicate. Defined.

Lemma rpd_c_change sh top bm v:
  @data_at W_rp_duplicate sh rpd_tnrc (rpd_c top bm) v =
  @data_at Counter.CS sh (Tstruct counter_spec._noise_replay_counter noattr) (cnt_val top Vundef bm) v.
Proof.
  symmetry. unfold rpd_tnrc.
  exact (f_equal (fun f => f v) (@data_at_change_composite Counter.CS W_rp_duplicate rpd_CCE sh
    (Tstruct _noise_replay_counter noattr) (cnt_val top Vundef bm) (rpd_c top bm) (JMeq_refl _) eq_refl)).
Qed.

(* main's precondition: keep gvars, forget the globals (main never reads one) and the external state *)
Lemma rpd_main_pre {Espec: OracleKind} Delta (prog: QP.program function) (gv: globals) R c Post:
  semax Delta (PROP () LOCAL (gvars gv) SEP (TT) * R)%logic c Post ->
  semax Delta (close_precondition nil (@main_pre unit prog tt gv) * R)%logic c Post.
Proof.
  intros H. eapply semax_pre; [|apply H]; clear H.
  unfold main_pre, PROPx, LOCALx, SEPx, local, lift1.
  intro rho. unfold close_precondition. simpl. unfold_lift. normalize.
  rewrite prop_true_andp; [apply sepcon_derives; auto; apply TT_right | split; auto; hnf; reflexivity].
Qed.

Lemma body_main : semax_body rpd_V rpd_Gprog f_main rpd_main_spec.
Proof.
  unfold rpd_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  simpl fn_body; simpl fn_params; simpl fn_return.
  change (fun rho => ?A rho * ?B rho)%logic with (A * B)%logic.
  apply rpd_main_pre.
  simpl app. simplify_func_tycontext.
  process_stackframe_of.
  repeat rewrite <- data_at__offset_zero.
  unfold rpd_post.
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (TT))%assert
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  abbreviate_semax.
  forward_call (Tsh, v_window).
  (* the first sequence of nonces *)
  forward_loop (EX top: Z, EX L: list Z, EX bm: list Z,
    PROP (cnt_inv top L bm)
    LOCAL (lvar _window rpd_tnrc v_window; gvars gv)
    SEP (data_at Tsh rpd_tnrc (rpd_c top bm) v_window; TT))%assert
  break: (EX top: Z, EX L: list Z, EX bm: list Z,
    PROP (cnt_inv top L bm)
    LOCAL (lvar _window rpd_tnrc v_window; gvars gv)
    SEP (data_at Tsh rpd_tnrc (rpd_c top bm) v_window; TT))%assert.
  { Exists 0 (@nil Z) (Zrepeat 0 128). entailer!. apply WgNoise.proof.harness.counter.hcnt_defs3.cnt_inv_init. }
  { Intros top L bm.
    forward_call tt. Intros b.
    forward_if.
    2:{ forward. Exists top L bm. entailer!. }
    forward_call tt. Intros x.
    rewrite rpd_c_change.
    forward_call (Tsh, v_window, top, L, bm, Vundef, x).
    Intros bm'. rewrite <- rpd_c_change.
    Exists (cnt_top' top L x) (cnt_L' top L x) bm'. entailer!. }
  (* n, accepted or not *)
  Intros top L bm.
  forward_call tt. Intros n.
  rewrite rpd_c_change.
  forward_call (Tsh, v_window, top, L, bm, Vundef, n).
  Intros bm1. rewrite <- rpd_c_change.
  destruct (cnt_ok top L n) eqn:Hok.
  2:{ forward_if.
      - forward. entailer!.
      - exfalso. simpl in *. first [discriminate | contradiction | lia]. }
  forward_if.
  { exfalso. simpl in *. first [discriminate | contradiction | lia]. }
  assert (Hin: In n (cnt_L' top L n)) by (apply rpd_ok_in; exact Hok).
  remember (cnt_top' top L n) as top1 eqn:E1. remember (cnt_L' top L n) as L1 eqn:E2.
  clear E1 E2 H top L bm Hok.
  (* the second sequence of nonces: n stays accepted *)
  forward_loop (EX top: Z, EX L: list Z, EX bm: list Z,
    PROP (cnt_inv top L bm; In n L)
    LOCAL (temp _n (Vlong (Int64.repr n)); lvar _window rpd_tnrc v_window; gvars gv)
    SEP (data_at Tsh rpd_tnrc (rpd_c top bm) v_window; TT))%assert
  break: (EX top: Z, EX L: list Z, EX bm: list Z,
    PROP (cnt_inv top L bm; In n L)
    LOCAL (temp _n (Vlong (Int64.repr n)); lvar _window rpd_tnrc v_window; gvars gv)
    SEP (data_at Tsh rpd_tnrc (rpd_c top bm) v_window; TT))%assert.
  { Exists top1 L1 bm1. entailer!. }
  { Intros top L bm.
    forward_call tt. Intros b.
    forward_if.
    2:{ forward. Exists top L bm. entailer!. }
    forward_call tt. Intros x.
    rewrite rpd_c_change.
    forward_call (Tsh, v_window, top, L, bm, Vundef, x).
    Intros bm'. rewrite <- rpd_c_change.
    Exists (cnt_top' top L x) (cnt_L' top L x) bm'. entailer!. apply rpd_L'_keeps; auto. }
  (* n again: refused *)
  Intros top L bm.
  rewrite rpd_c_change.
  forward_call (Tsh, v_window, top, L, bm, Vundef, n).
  Intros bm2. rewrite <- rpd_c_change.
  rewrite (rpd_refused top L n) by auto.
  forward_call (Int.one).
  forward.
  entailer!.
Qed.

Theorem rpd_piece : piece_ok [u_rpd] rpd_imports rpd_G.
Proof.
  split.
  - repeat constructor; simpl; intuition discriminate.
  - repeat constructor; exists u_rpd; (split; [left; reflexivity|]).
    + exists f_new_counter; split; [reflexivity | exact body_new_counter].
    + exists f_any_u64; split; [reflexivity | exact body_any_u64].
    + exists f_main; split; [reflexivity | exact body_main].
Qed.
