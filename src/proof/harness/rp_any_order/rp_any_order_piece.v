(* The harness piece of law rp_any_order (harness/rp_any_order.c): the bodies of upto, new_counter and main, proved
   in W_rp_any_order against the counter piece's wg_counter_validate_spec (counter_spec.v, at Counter.CS) and the
   external world.  Interface: rp_any_order_spec.v.

   Why the law holds, on the model of counter_spec.v (L = the accepted nonces, top = 1 + the largest one):
   after the first loop every accepted nonce is below the start s and top <= s.  In the second loop every
   accepted nonce is below s or is s + o for an offset o already marked in seen[], and top <= s + W + 1.  A
   new offset o is not marked, so s + o is not in L, s + o + 1 + W >= top, and s + o < R: cnt_ok accepts it. *)
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
Module hcnt_defs3 := WgNoise.proof.harness.counter.hcnt_defs3.
Require Import WgNoise.proof.harness.rp_any_order.rp_any_order_spec.
Require WgNoise.contracts.rp_any_order.
Require Import WgNoise.harness.rp_any_order.code.

#[local] Existing Instance W_rp_any_order.

Definition rao_V : varspecs := QPvarspecs WgNoise.contracts.rp_any_order.Harness.qp.
Definition rao_Gprog : funspecs := rao_imports W_rp_any_order ++ rao_G.

Lemma body_upto : semax_body rao_V rao_Gprog f_upto rao_upto_spec.
Proof.
  start_function.
  forward_call tt. Intros v.
  forward_if (temp _t'2 (Vlong (Int64.repr (Z.min v max)))).
  { forward. entailer!. rewrite Z.min_l by lia. reflexivity. }
  { forward. entailer!. rewrite Z.min_r by lia. reflexivity. }
  forward. Exists (Z.min v max). entailer!.
Qed.

Lemma body_new_counter : semax_body rao_V rao_Gprog f_new_counter rao_new_counter_spec.
Proof.
  start_function.
  forward.
  forward_for_simple_bound 128 (EX i: Z, PROP ()
    LOCAL (temp _c c)
    SEP (data_at sh (Tstruct _noise_replay_counter noattr)
           (Vlong (Int64.repr 0), (Vundef, Zrepeat (Vlong (Int64.repr 0)) i ++ Zrepeat Vundef (128 - i))) c))%assert.
  - entailer!.
  - forward. rewrite hcnt_defs3.upd_Znth_Zrepeat_step by lia. entailer!.
  - entailer!.
Qed.

Definition tnrc := Tstruct _noise_replay_counter noattr.

#[local] Instance rao_CCE : change_composite_env Counter.CS W_rp_any_order.
Proof. make_cs_preserve Counter.CS W_rp_any_order. Defined.

Lemma rao_cnt_change sh top bm v:
  @data_at W_rp_any_order sh tnrc (rao_cnt top bm) v =
  @data_at Counter.CS sh (Tstruct counter_spec._noise_replay_counter noattr) (cnt_val top Vundef bm) v.
Proof.
  symmetry. unfold tnrc.
  exact (f_equal (fun f => f v) (@data_at_change_composite Counter.CS W_rp_any_order rao_CCE sh
    (Tstruct _noise_replay_counter noattr) (cnt_val top Vundef bm) (rao_cnt top bm) (JMeq_refl _) eq_refl)).
Qed.

(* The second loop's invariant on the model: every accepted nonce is below the start, or is start + o for an
   offset o marked in seen[] (sn). *)
Definition rao_marked (start: Z) (sn: list Z) (L: list Z) : Prop :=
  forall x, In x L -> x < start \/ (start <= x <= start + CNT_W /\ Znth (x - start) sn <> 0).

(* a new offset of the window is accepted *)
Lemma rao_ok start top L bm sn o:
  0 <= start <= Int64.max_unsigned - 16258 -> cnt_inv top L bm -> top <= start + 8129 ->
  rao_marked start sn L -> 0 <= o <= 8128 -> Znth o sn = 0 -> cnt_ok top L (start + o) = true.
Proof.
  intros Hs Hi Ht Hm Ho Hz. pose proof (cnt_top_range _ _ _ Hi).
  unfold cnt_ok. rewrite !andb_true_iff. unfold CNT_R, CNT_W in *. split; [split; [split|]|].
  - apply Z.ltb_lt. lia.
  - apply Z.ltb_lt. rep_lia.
  - apply Z.leb_le. lia.
  - apply negb_true_iff. apply not_true_iff_false. intros E. apply existsb_exists in E as [x [Hx E]].
    apply Z.eqb_eq in E. subst x. destruct (Hm _ Hx) as [Hx'|[_ Hx']]; [lia|].
    replace (start + o - start) with o in Hx' by lia. contradiction.
Qed.

(* and the invariant holds after it, with the offset marked *)
Lemma rao_marked_step start top L sn o:
  Zlength sn = 8129 -> rao_marked start sn L -> 0 <= o <= 8128 -> cnt_ok top L (start + o) = true ->
  rao_marked start (upd_Znth o sn 1) (cnt_L' top L (start + o)).
Proof.
  unfold rao_marked, CNT_W in *. intros Hl Hm Ho Hok x Hx. unfold cnt_L' in Hx. rewrite Hok in Hx. destruct Hx as [<-|Hx].
  - right. split; [lia|]. replace (start + o - start) with o by lia. rewrite upd_Znth_same by lia. lia.
  - destruct (Hm x Hx) as [H|[H1 H2]]; [left; auto|right; split; auto].
    destruct (Z.eq_dec (x - start) o) as [E|E].
    + rewrite E, upd_Znth_same by lia. lia.
    + rewrite upd_Znth_diff by lia. auto.
Qed.

(* main's precondition: keep gvars, forget the globals (main never reads one) and the external state *)
Lemma rao_main_pre {Espec: OracleKind} Delta (prog: QP.program function) (gv: globals) R c Post:
  semax Delta (PROP () LOCAL (gvars gv) SEP (TT) * R)%logic c Post ->
  semax Delta (close_precondition nil (@main_pre unit prog tt gv) * R)%logic c Post.
Proof.
  intros H. eapply semax_pre; [|apply H]; clear H.
  unfold main_pre, PROPx, LOCALx, SEPx, local, lift1.
  intro rho. unfold close_precondition. simpl. unfold_lift. normalize.
  rewrite prop_true_andp; [apply sepcon_derives; auto; apply TT_right | split; auto; hnf; reflexivity].
Qed.

Lemma body_main : semax_body rao_V rao_Gprog f_main rao_main_spec.
Proof.
  unfold rao_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  simpl fn_body; simpl fn_params; simpl fn_return.
  change (fun rho => ?A rho * ?B rho)%logic with (A * B)%logic.
  apply rao_main_pre.
  simpl app. simplify_func_tycontext.
  process_stackframe_of.
  repeat rewrite <- data_at__offset_zero.
  abbreviate_semax.
  forward_call (Tsh, v_window).
  forward_call (Int64.max_unsigned - 16258).
  Intros start.
  (* the nonces below the start *)
  forward_loop (EX top: Z, EX L: list Z, EX bm: list Z,
    PROP (cnt_inv top L bm; top <= start)
    LOCAL (temp _start (Vlong (Int64.repr start)); lvar _seen (tarray tuchar 8129) v_seen;
           lvar _window tnrc v_window; gvars gv)
    SEP (data_at Tsh tnrc (rao_cnt top bm) v_window; data_at_ Tsh (tarray tuchar 8129) v_seen; TT))%assert
  break: (EX top: Z, EX L: list Z, EX bm: list Z,
    PROP (cnt_inv top L bm; top <= start)
    LOCAL (temp _start (Vlong (Int64.repr start)); lvar _seen (tarray tuchar 8129) v_seen;
           lvar _window tnrc v_window; gvars gv)
    SEP (data_at Tsh tnrc (rao_cnt top bm) v_window; data_at_ Tsh (tarray tuchar 8129) v_seen; TT))%assert.
  { Exists 0 (@nil Z) (Zrepeat 0 128). entailer!. apply hcnt_defs3.cnt_inv_init. }
  { Intros top L bm.
    forward_if (EX b: bool, PROP (b = true -> 0 < start)
      LOCAL (temp _t'2 (Val.of_bool b); temp _start (Vlong (Int64.repr start)); lvar _seen (tarray tuchar 8129) v_seen;
           lvar _window tnrc v_window; gvars gv)
      SEP (data_at Tsh tnrc (rao_cnt top bm) v_window; data_at_ Tsh (tarray tuchar 8129) v_seen; TT))%assert.
    - forward_call tt. Intros b. forward.
      Exists (negb (zeq b 0)). entailer!.
      split; [|destruct (zeq b 0); reflexivity]. intros _. rewrite !Int64.unsigned_repr in H2 by rep_lia. lia.
    - forward. Exists false. entailer!.
    - Intros b. destruct b.
      2:{ forward_if; [contradiction|]. forward. Exists top L bm. entailer!. }
      forward_if; [|exfalso; apply Int.one_not_zero; assumption].
      forward_call (start - 1).
      Intros n.
      rewrite rao_cnt_change.
      forward_call (Tsh, v_window, top, L, bm, Vundef, n).
      Intros bm'.
      rewrite <- rao_cnt_change.
      Exists (cnt_top' top L n) (cnt_L' top L n) bm'. entailer!.
      unfold cnt_top'. destruct (cnt_ok top L n); lia. }
  Intros top L bm.
  (* seen[] := 0 *)
  forward.
  forward_loop (EX i: Z,
    PROP (0 <= i <= 8129)
    LOCAL (temp _i (Vlong (Int64.repr i)); temp _start (Vlong (Int64.repr start));
           lvar _seen (tarray tuchar 8129) v_seen; lvar _window tnrc v_window; gvars gv)
    SEP (data_at Tsh tnrc (rao_cnt top bm) v_window;
         data_at Tsh (tarray tuchar 8129) (Zrepeat (Vint (Int.repr 0)) i ++ Zrepeat Vundef (8129 - i)) v_seen;
         TT))%assert
  continue: (EX i: Z,
    PROP (0 <= i < 8129)
    LOCAL (temp _i (Vlong (Int64.repr i)); temp _start (Vlong (Int64.repr start));
           lvar _seen (tarray tuchar 8129) v_seen; lvar _window tnrc v_window; gvars gv)
    SEP (data_at Tsh tnrc (rao_cnt top bm) v_window;
         data_at Tsh (tarray tuchar 8129) (Zrepeat (Vint (Int.repr 0)) (i + 1) ++ Zrepeat Vundef (8129 - (i + 1)))
           v_seen;
         TT))%assert
  break: (
    PROP ()
    LOCAL (temp _start (Vlong (Int64.repr start));
           lvar _seen (tarray tuchar 8129) v_seen; lvar _window tnrc v_window; gvars gv)
    SEP (data_at Tsh tnrc (rao_cnt top bm) v_window;
         data_at Tsh (tarray tuchar 8129) (map (fun z => Vint (Int.repr z)) (Zrepeat 0 8129)) v_seen;
         TT))%assert.
  { Exists 0. entailer!. }
  { Intros i. forward_if.
    - rewrite !Int64.unsigned_repr in H3 by rep_lia.
      forward. Exists i. change (Int.zero_ext 8 (Int.repr 0)) with (Int.repr 0).
      rewrite hcnt_defs3.upd_Znth_Zrepeat_step by lia. entailer!.
    - rewrite !Int64.unsigned_repr in H3 by rep_lia.
      assert (i = 8129) by lia. subst i.
      forward.
      rewrite Z.sub_diag. change (Zrepeat Vundef 0) with (@nil val). rewrite app_nil_r.
      unfold Zrepeat at 2. rewrite map_repeat. fold (Zrepeat (Vint (Int.repr 0)) 8129).
      go_lower. rewrite !eqb_type_refl. apply andp_right; [apply prop_right; auto | cancel]. }
  { Intros i. forward. Exists (i + 1). entailer!. }
  (* the offsets of the window *)
  assert (Hz: Zlength (Zrepeat 0 8129) = 8129 /\ Forall (fun z => 0 <= z <= 1) (Zrepeat 0 8129) /\
              rao_marked start (Zrepeat 0 8129) L).
  { split3; [reflexivity | apply Forall_forall; intros z Hz; apply repeat_spec in Hz; lia |].
    intros x Hx. left. pose proof (cnt_L_range _ _ _ H0 x Hx). lia. }
  forget (Zrepeat 0 8129) as sn0.
  forward_loop (EX top: Z, EX L: list Z, EX bm: list Z, EX sn: list Z,
    PROP (cnt_inv top L bm; top <= start + 8129; Zlength sn = 8129;
          Forall (fun z => 0 <= z <= 1) sn; rao_marked start sn L)
    LOCAL (temp _start (Vlong (Int64.repr start));
           lvar _seen (tarray tuchar 8129) v_seen; lvar _window tnrc v_window; gvars gv)
    SEP (data_at Tsh tnrc (rao_cnt top bm) v_window;
         data_at Tsh (tarray tuchar 8129) (map (fun z => Vint (Int.repr z)) sn) v_seen; TT))%assert
  break: (EX top: Z, EX bm: list Z, EX sn: list Z,
    PROP ()
    LOCAL (lvar _seen (tarray tuchar 8129) v_seen; lvar _window tnrc v_window; gvars gv)
    SEP (data_at Tsh tnrc (rao_cnt top bm) v_window;
         data_at Tsh (tarray tuchar 8129) (map (fun z => Vint (Int.repr z)) sn) v_seen; TT))%assert.
  { destruct Hz as (Hz1 & Hz2 & Hz3). Exists top L bm sn0. entailer!. }
  { clear dependent top. clear dependent L. clear dependent bm. clear dependent sn0.
    Intros top L bm sn.
    forward_call tt. Intros b.
    forward_if.
    2:{ forward. Exists top bm sn. entailer!. }
    forward_call 8128. Intros o.
    assert (Hzo: 0 <= Znth o sn <= 1) by (rewrite Forall_forall in H3; apply H3, Znth_In; lia).
    forward.
    { entailer!. simpl. rep_lia. }
    forward_if.
    2:{ forward. Exists top L bm sn. entailer!. }
    rename H8 into Hz.
    forward.
    change (Int.zero_ext 8 (Int.repr 1)) with (Int.repr 1).
    rewrite (upd_Znth_map (fun z => Vint (Int.repr z)) o sn 1).
    assert (Hok: cnt_ok top L (start + o) = true) by (apply (rao_ok start top L bm sn o); auto).
    rewrite rao_cnt_change.
    forward_call (Tsh, v_window, top, L, bm, Vundef, start + o).
    Intros bm'.
    rewrite <- rao_cnt_change. rewrite Hok.
    forward_call Int.one.
    Exists (cnt_top' top L (start + o)) (cnt_L' top L (start + o)) bm' (upd_Znth o sn 1).
    entailer!.
    split; [|split; [|split]].
    - unfold cnt_top'. rewrite Hok. lia.
    - rewrite upd_Znth_Zlength; lia.
    - apply Forall_upd_Znth; auto; lia.
    - apply rao_marked_step; auto. }
  Intros top' bm' sn'.
  unfold abbreviate in POSTCONDITION. subst POSTCONDITION. unfold rao_post.
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (TT))%assert
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  abbreviate_semax.
  forward.
  sep_apply (data_at_data_at_ Tsh tnrc). sep_apply (data_at_data_at_ Tsh (tarray tuchar 8129)). cancel.
Qed.

Theorem rao_piece : piece_ok [u_rao] rao_imports rao_G.
Proof.
  split.
  - repeat constructor; simpl; intuition discriminate.
  - repeat constructor; exists u_rao; (split; [left; reflexivity|]).
    + exists f_upto; split; [reflexivity | exact body_upto].
    + exists f_new_counter; split; [reflexivity | exact body_new_counter].
    + exists f_main; split; [reflexivity | exact body_main].
Qed.
