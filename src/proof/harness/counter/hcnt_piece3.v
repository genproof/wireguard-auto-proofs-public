(* the harness piece of law counter (harness/counter.c): draw_steps, draw_u64 and main, proved in
   W_counter against the counter piece's wg_counter_validate_spec (counter_spec.v, at Counter.CS) and the
   external world QuickProof.Env at W_counter.  Interface: hcnt_spec3.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.counter.counter_spec.
Require Import WgNoise.proof.harness.counter.hcnt_spec3.
Require WgNoise.contracts.x_counter.
Require Import WgNoise.harness.x_counter.code.
Require Import WgNoise.proof.harness.counter.hcnt_defs3.

#[local] Existing Instance W_counter.

Definition hcnt3_V : varspecs := QPvarspecs WgNoise.contracts.x_counter.Harness.qp.
Definition hcnt3_Gprog : funspecs := hcnt3_imports W_counter ++ hcnt3_G.

Lemma body_draw_steps3 : semax_body hcnt3_V hcnt3_Gprog f_draw_steps hcnt3_draw_steps_spec.
Proof.
  start_function.
  forward_call tt. Intros n.
  forward_if (temp _t'2 (Vlong (Int64.repr n))).
  { forward. entailer!. }
  { exfalso. unfold Int64.ltu in H0. rewrite (Int64.unsigned_repr n) in H0 by rep_lia.
    change (Int64.unsigned (Int64.repr (-1))) with Int64.max_unsigned in H0.
    if_tac in H0. lia. discriminate. }
  forward. Exists n. entailer!.
Qed.

Lemma body_draw_u643 : semax_body hcnt3_V hcnt3_Gprog f_draw_u64 hcnt3_draw_u64_spec.
Proof.
  start_function.
  eapply semax_seq' with (P' := (EX hi:Z, PROP (0 <= hi <= Int.max_unsigned)
                                         LOCAL (temp _hi (Vlong (Int64.repr hi))) SEP ())%assert).
  { eapply semax_seq'. forward_call tt. apply ENTAIL_refl. Intros hi. forward. Exists hi. entailer!. }
  abbreviate_semax. Intros hi.
  forward_call tt. Intros lo.
  forward.
  Exists (Int64.unsigned (Int64.or (Int64.shl (Int64.repr hi) (Int64.repr 32)) (Int64.repr lo))).
  entailer!. rewrite Int64.repr_unsigned; auto.
Qed.

Definition tnrc := Tstruct _noise_replay_counter noattr.

(* the harness's struct noise_replay_counter c, in W_counter (the lock is never written) *)
Definition hcnt_c (top: Z) (bm: list Z) : reptype tnrc :=
  (Vlong (Int64.repr top), (Vundef, map (fun w => Vlong (Int64.repr w)) bm)).

#[local] Instance hcnt3_CCE : change_composite_env Counter.CS W_counter.
Proof. make_cs_preserve Counter.CS W_counter. Defined.

Lemma hcnt_c_change sh top bm v:
  @data_at W_counter sh tnrc (hcnt_c top bm) v =
  @data_at Counter.CS sh (Tstruct counter_spec._noise_replay_counter noattr) (cnt_val top Vundef bm) v.
Proof.
  symmetry. unfold tnrc.
  exact (f_equal (fun f => f v) (@data_at_change_composite Counter.CS W_counter hcnt3_CCE sh
    (Tstruct _noise_replay_counter noattr) (cnt_val top Vundef bm) (hcnt_c top bm) (JMeq_refl _) eq_refl)).
Qed.

(* main's precondition: keep gvars, forget the globals (main never reads one) and the external state *)
Lemma hcnt3_main_pre {Espec: OracleKind} Delta (prog: QP.program function) (gv: globals) R c Post:
  semax Delta (PROP () LOCAL (gvars gv) SEP (TT) * R)%logic c Post ->
  semax Delta (close_precondition nil (@main_pre unit prog tt gv) * R)%logic c Post.
Proof.
  intros H. eapply semax_pre; [|apply H]; clear H.
  unfold main_pre, PROPx, LOCALx, SEPx, local, lift1.
  intro rho. unfold close_precondition. simpl. unfold_lift. normalize.
  rewrite prop_true_andp; [apply sepcon_derives; auto; apply TT_right | split; auto; hnf; reflexivity].
Qed.

Lemma body_main3 : semax_body hcnt3_V hcnt3_Gprog f_main hcnt3_main_spec.
Proof.
  unfold hcnt3_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  simpl fn_body; simpl fn_params; simpl fn_return.
  change (fun rho => ?A rho * ?B rho)%logic with (A * B)%logic.
  apply hcnt3_main_pre.
  simpl app. simplify_func_tycontext.
  process_stackframe_of.
  repeat rewrite <- data_at__offset_zero.
  abbreviate_semax.
  forward. forward. forward.
  forward_for_simple_bound 128 (EX i: Z, PROP ()
    LOCAL (temp _top (Vlong (Int64.repr 0));
           lvar _set (tptr tacc) v_set; lvar _c (Tstruct _noise_replay_counter noattr) v_c; gvars gv)
    SEP (data_at Tsh (tptr tacc) nullval v_set;
         data_at Tsh (Tstruct _noise_replay_counter noattr)
           (Vlong (Int64.repr 0), (Vundef, Zrepeat (Vlong (Int64.repr 0)) i ++ Zrepeat Vundef (128 - i))) v_c;
         TT))%assert.
  - entailer!.
  - forward.
    rewrite upd_Znth_Zrepeat_step by lia. entailer!.
  - idtac.
  forward_call tt. Intros steps.
  forward.
  sep_apply (create_mem_mgr gv).
  replace (Zrepeat (Vlong (Int64.repr 0)) 128 ++ Zrepeat Vundef (128 - 128))
    with (map (fun w => Vlong (Int64.repr w)) (Zrepeat 0 128)) by reflexivity.
  forward_loop (EX i: Z, EX top: Z, EX L: list Z, EX bm: list Z, EX p: val,
    PROP (0 <= i <= steps; cnt_inv top L bm)
    LOCAL (temp _i (Vlong (Int64.repr i)); temp _steps (Vlong (Int64.repr steps));
           temp _top (Vlong (Int64.repr top));
           lvar _set (tptr tacc) v_set; lvar _c tnrc v_c; gvars gv)
    SEP (mem_mgr gv; data_at Tsh (tptr tacc) p v_set; accs L p; data_at Tsh tnrc (hcnt_c top bm) v_c; TT))%assert
  continue: (EX i: Z, EX top: Z, EX L: list Z, EX bm: list Z, EX p: val,
    PROP (0 <= i < steps; cnt_inv top L bm)
    LOCAL (temp _i (Vlong (Int64.repr i)); temp _steps (Vlong (Int64.repr steps));
           temp _top (Vlong (Int64.repr top));
           lvar _set (tptr tacc) v_set; lvar _c tnrc v_c; gvars gv)
    SEP (mem_mgr gv; data_at Tsh (tptr tacc) p v_set; accs L p; data_at Tsh tnrc (hcnt_c top bm) v_c; TT))%assert
  break: (EX top: Z, EX L: list Z, EX bm: list Z, EX p: val,
    PROP ()
    LOCAL (lvar _set (tptr tacc) v_set; lvar _c tnrc v_c; gvars gv)
    SEP (mem_mgr gv; data_at Tsh (tptr tacc) p v_set; accs L p; data_at Tsh tnrc (hcnt_c top bm) v_c; TT))%assert.
  { Exists 0 0 (@nil Z) (Zrepeat 0 128) nullval. simpl accs. entailer!. apply cnt_inv_init. }
  { Intros i top L bm p.
    forward_if.
    2:{ forward. Exists top L bm p. entailer!. }
    forward_call tt. Intros b.
    eapply semax_seq' with (P' := (EX nv: int64,
      PROP ()
      LOCAL (temp _n (Vlong nv); temp _i (Vlong (Int64.repr i)); temp _steps (Vlong (Int64.repr steps));
             temp _top (Vlong (Int64.repr top));
             lvar _set (tptr tacc) v_set; lvar _c tnrc v_c; gvars gv)
      SEP (mem_mgr gv; data_at Tsh (tptr tacc) p v_set; accs L p; data_at Tsh tnrc (hcnt_c top bm) v_c; TT))%assert).
    { apply (semax_switch_PQR (b mod 5)).
      - reflexivity.
      - entailer!. destruct H10 as [_ H10]. apply (f_equal Int.signed) in H10.
        rewrite Int.signed_repr in H10 by rep_lia. rewrite Int.signed_mone in H10. lia.
      - entailer!. unfold Int.mods. rewrite !Int.signed_repr by rep_lia.
        rewrite Z.rem_mod_nonneg by lia. reflexivity.
      - rewrite Int.unsigned_repr by (pose proof (Z.mod_pos_bound b 5); rep_lia).
        assert (Hb: b mod 5 = 0 \/ b mod 5 = 1 \/ b mod 5 = 2 \/ b mod 5 = 3 \/ b mod 5 = 4)
          by (pose proof (Z.mod_pos_bound b 5); lia).
        destruct Hb as [Hb|[Hb|[Hb|[Hb|Hb]]]]; rewrite Hb; simpl seq_of_labeled_statement.
        4: forward_call tt; Intros x; forward;
          match goal with |- context [temp _n (Vlong ?E)] => Exists E end; entailer!.
        all: forward_call tt; Intros x; forward; forward;
          match goal with |- context [temp _n (Vlong ?E)] => Exists E end; entailer!. }
    abbreviate_semax.
    Intros nv.
    assert (Hn: 0 <= Int64.unsigned nv <= Int64.max_unsigned) by apply Int64.unsigned_range_2.
    rewrite <- (Int64.repr_unsigned nv).
    remember (Int64.unsigned nv) as n eqn:En. clear En nv.
    rewrite hcnt_c_change.
    forward_call (Tsh, v_c, top, L, bm, Vundef, n).
    Intros bm'.
    rewrite <- hcnt_c_change.
    forward. forward.
    forward_loop (EX K: list Z, EX R: list Z, EX a: val,
      PROP (L = K ++ R)
      LOCAL (temp _a a; temp _in (Vint (Int.repr (if existsb (Z.eqb n) K then 1 else 0)));
             temp _r (Val.of_bool (cnt_ok top L n));
             temp _n (Vlong (Int64.repr n)); temp _i (Vlong (Int64.repr i));
             temp _steps (Vlong (Int64.repr steps)); temp _top (Vlong (Int64.repr top));
             lvar _set (tptr tacc) v_set; lvar _c tnrc v_c; gvars gv)
      SEP (data_at Tsh tnrc (hcnt_c (cnt_top' top L n) bm') v_c; mem_mgr gv;
           data_at Tsh (tptr tacc) p v_set; accseg K p a; accs R a; TT))%assert
    continue: (EX K: list Z, EX x: Z, EX R: list Z, EX a: val, EX q: val,
      PROP (L = K ++ x :: R)
      LOCAL (temp _a a; temp _in (Vint (Int.repr (if existsb (Z.eqb n) (K ++ [x]) then 1 else 0)));
             temp _r (Val.of_bool (cnt_ok top L n));
             temp _n (Vlong (Int64.repr n)); temp _i (Vlong (Int64.repr i));
             temp _steps (Vlong (Int64.repr steps)); temp _top (Vlong (Int64.repr top));
             lvar _set (tptr tacc) v_set; lvar _c tnrc v_c; gvars gv)
      SEP (data_at Tsh tnrc (hcnt_c (cnt_top' top L n) bm') v_c; mem_mgr gv;
           data_at Tsh (tptr tacc) p v_set; accseg K p a; malloc_token Ews tacc a;
           data_at Ews tacc (Vlong (Int64.repr x), q) a; accs R q; TT))%assert
    break: (
      PROP ()
      LOCAL (temp _in (Vint (Int.repr (if existsb (Z.eqb n) L then 1 else 0)));
             temp _r (Val.of_bool (cnt_ok top L n));
             temp _n (Vlong (Int64.repr n)); temp _i (Vlong (Int64.repr i));
             temp _steps (Vlong (Int64.repr steps)); temp _top (Vlong (Int64.repr top));
             lvar _set (tptr tacc) v_set; lvar _c tnrc v_c; gvars gv)
      SEP (data_at Tsh tnrc (hcnt_c (cnt_top' top L n) bm') v_c; mem_mgr gv;
           data_at Tsh (tptr tacc) p v_set; accs L p; TT))%assert.
    { Exists (@nil Z) L p. simpl accseg. entailer!. }
    { Intros K R a.
      forward_if.
      2:{ forward. subst a. destruct R as [|x R].
          - rewrite app_nil_r in *. subst L. sep_apply (accseg_accs K [] p nullval). rewrite app_nil_r. entailer!.
          - simpl accs. Intros q. entailer!. }
      destruct R as [|x R]. { simpl accs. Intros. subst a. simpl in *. contradiction. }
      simpl accs. Intros q.
      forward.
      forward_if (EX K: list Z, EX x: Z, EX R: list Z, EX a: val, EX q: val,
      PROP (L = K ++ x :: R)
      LOCAL (temp _a a; temp _in (Vint (Int.repr (if existsb (Z.eqb n) (K ++ [x]) then 1 else 0)));
             temp _r (Val.of_bool (cnt_ok top L n));
             temp _n (Vlong (Int64.repr n)); temp _i (Vlong (Int64.repr i));
             temp _steps (Vlong (Int64.repr steps)); temp _top (Vlong (Int64.repr top));
             lvar _set (tptr tacc) v_set; lvar _c tnrc v_c; gvars gv)
      SEP (data_at Tsh tnrc (hcnt_c (cnt_top' top L n) bm') v_c; mem_mgr gv;
           data_at Tsh (tptr tacc) p v_set; accseg K p a; malloc_token Ews tacc a;
           data_at Ews tacc (Vlong (Int64.repr x), q) a; accs R q; TT))%assert.
      - forward. Exists K x R a q. entailer!.
        assert (Hx: 0 <= x < Int64.max_unsigned - CNT_W - 1)
          by (apply (cnt_L_bound _ _ _ x H1); apply in_or_app; right; left; auto).
        rewrite int64_eq_repr in H7 by (unfold CNT_W in Hx; rep_lia).
        apply Z.eqb_eq in H7. subst x. rewrite existsb_snoc, Z.eqb_refl, orb_true_r. reflexivity.
      - forward. Exists K x R a q. entailer!.
        assert (Hx: 0 <= x < Int64.max_unsigned - CNT_W - 1)
          by (apply (cnt_L_bound _ _ _ x H1); apply in_or_app; right; left; auto).
        assert (n =? x = false) by (apply Z.eqb_neq; congruence).
        rewrite existsb_snoc, H5, orb_false_r. reflexivity. }
    { Intros K x R a q. forward. Exists (K ++ [x]) R q. entailer!.
      - rewrite <- app_assoc. auto.
      - sep_apply (accseg_app K x p a q). entailer!. }
    assert (Htop: 0 <= top <= CNT_R) by apply (cnt_top_range _ _ _ H1).
    forward_if (temp _t'9 (Val.of_bool (n <? CNT_R))).
    { forward. entailer!.
      unfold Int64.cmpu, Int64.ltu. rewrite u64_R. rewrite Int64.unsigned_repr by rep_lia.
      destruct (zlt n CNT_R), (Z.ltb_spec n CNT_R); auto; lia. }
    { exfalso.
      match type of H5 with _ >= Int64.unsigned ?e =>
        let E := fresh in assert (E: Int64.unsigned e = CNT_R + 1) by reflexivity; rewrite E in H5 end.
      rewrite Int64.unsigned_repr in H5 by (rewrite CNT_R_val in *; rep_lia). lia. }
    forward_if (temp _t'10 (Val.of_bool ((n <? CNT_R) && (top <=? n + 1 + CNT_W))%bool)).
    { forward. entailer!.
      destruct (Z.ltb_spec n CNT_R); [|inv H5]. simpl andb. unfold Int64.cmpu.
      rewrite ltu_repr by (rewrite CNT_R_val in *; rep_lia). unfold CNT_W.
      destruct (Z.ltb_spec (n + 1 + 8128) top), (Z.leb_spec top (n + 1 + 8128)); auto; lia. }
    { forward. entailer!. destruct (n <? CNT_R); [inv H5|]. reflexivity. }
    forward_if (temp _t'11 (Val.of_bool (cnt_ok top L n))).
    { forward. entailer!.
      unfold cnt_ok. replace (top <? CNT_R + 1) with true by (symmetry; apply Z.ltb_lt; lia). simpl andb.
      destruct ((n <? CNT_R) && (top <=? n + 1 + CNT_W))%bool; [|inv H5].
      destruct (existsb (Z.eqb n) L); reflexivity. }
    { forward. entailer!.
      unfold cnt_ok. replace (top <? CNT_R + 1) with true by (symmetry; apply Z.ltb_lt; lia). simpl andb.
      destruct ((n <? CNT_R) && (top <=? n + 1 + CNT_W))%bool; [inv H5|]. reflexivity. }
    forward.
    match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
    { apply ENTAIL_refl. }
    { match goal with |- semax _ ?P _ _ => forward_if P end.
      - exfalso. destruct (cnt_ok top L n); simpl in H5; discriminate.
      - forward. entailer!.
      - forward. apply ENTAIL_refl. }
    abbreviate_semax.
    forward_if (EX p': val,
      PROP ()
      LOCAL (temp _n (Vlong (Int64.repr n)); temp _i (Vlong (Int64.repr i));
             temp _steps (Vlong (Int64.repr steps)); temp _top (Vlong (Int64.repr (cnt_top' top L n)));
             lvar _set (tptr tacc) v_set; lvar _c tnrc v_c; gvars gv)
      SEP (data_at Tsh tnrc (hcnt_c (cnt_top' top L n) bm') v_c; mem_mgr gv;
           data_at Tsh (tptr tacc) p' v_set; accs (cnt_L' top L n) p'; TT))%assert.
    { assert (Hok: cnt_ok top L n = true) by (destruct (cnt_ok top L n); [auto | inv H5]).
      forward_call (tacc, gv).
      Intros a.
      if_tac.
      { subst a. forward_if.
        - forward. Exists (cnt_top' top L n) L bm' p. entailer!.
        - exfalso. apply H6. reflexivity. }
      Intros.
      forward_if.
      { exfalso. subst a. apply H6. reflexivity. }
      forward. forward. forward. forward.
      assert (Hnr: n < CNT_R) by (unfold cnt_ok in Hok; rewrite !andb_true_iff in Hok; lia).
      forward_if (temp _top (Vlong (Int64.repr (Z.max top (n + 1))))).
      - forward. entailer!.
        rewrite !Int64.unsigned_repr in H8 by (rewrite CNT_R_val in *; rep_lia).
        rewrite Z.max_r by lia. reflexivity.
      - forward. entailer!.
        rewrite !Int64.unsigned_repr in H8 by (rewrite CNT_R_val in *; rep_lia).
        rewrite Z.max_l by lia. reflexivity.
      - Exists a. unfold cnt_L', cnt_top'. rewrite Hok. simpl accs. Exists p. entailer!. }
    { forward. Exists p. unfold cnt_L', cnt_top'. destruct (cnt_ok top L n); [inv H5|]. entailer!. }
    Intros p'.
    remember (cnt_top' top L n) as top' eqn:Etop'. remember (cnt_L' top L n) as L' eqn:EL'.
    clear Etop' EL' H1 Htop. clear top L bm p.
    unfold hcnt_c.
    match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
    { apply ENTAIL_refl. }
    { forward.
      match goal with |- semax _ ?P _ _ => forward_if P end.
      - exfalso. rewrite Int64.eq_true in H1. discriminate.
      - forward. entailer!.
      - forward. entailer!. }
    abbreviate_semax.
    forward.
    forward_loop (EX K: list Z, EX R: list Z, EX l: val, EX q: val,
      PROP (hcnt_prune top' L' = K ++ hcnt_prune top' R; forall x, In x R -> In x L')
      LOCAL (temp _l l; temp _n (Vlong (Int64.repr n)); temp _i (Vlong (Int64.repr i));
             temp _steps (Vlong (Int64.repr steps)); temp _top (Vlong (Int64.repr top'));
             lvar _set (tptr tacc) v_set; lvar _c tnrc v_c; gvars gv)
      SEP (data_at Tsh tnrc (hcnt_c top' bm') v_c; mem_mgr gv;
           cseg Tsh K v_set l; data_at (csh Tsh K) (tptr tacc) q l; accs R q; TT))%assert
    break: (EX p'': val,
      PROP ()
      LOCAL (temp _n (Vlong (Int64.repr n)); temp _i (Vlong (Int64.repr i));
             temp _steps (Vlong (Int64.repr steps)); temp _top (Vlong (Int64.repr top'));
             lvar _set (tptr tacc) v_set; lvar _c tnrc v_c; gvars gv)
      SEP (data_at Tsh tnrc (hcnt_c top' bm') v_c; mem_mgr gv;
           data_at Tsh (tptr tacc) p'' v_set; accs (hcnt_prune top' L') p''; TT))%assert.
    { Exists (@nil Z) L' v_set p'. simpl cseg. unfold hcnt_c. entailer!. }
    { Intros K R l q.
      assert (Hsh: writable_share (csh Tsh K)) by (destruct K; simpl; auto).
      forward.
      forward_if.
      2:{ forward. assert_PROP (R = []) by (entailer!; tauto). subst q R.
          sep_apply (cseg_close Tsh K [] v_set l nullval). Intros p''. Exists p''.
          rewrite app_nil_r. simpl in H1. rewrite app_nil_r in H1. rewrite H1. entailer!. }
      destruct R as [|x R]. { simpl accs. Intros. subst q. contradiction. }
      simpl accs. Intros q'.
      forward. forward.
      assert (Hx: 0 <= x < top') by (apply (cnt_L_range _ _ _ H4); apply H5; left; auto).
      pose proof (cnt_top_range _ _ _ H4).
      forward_if.
      - rewrite !add64_repr in H8. rewrite !Int64.unsigned_repr in H8 by (rewrite CNT_R_val in *; rep_lia).
        forward. forward. forward.
        forward_call (tacc, q, gv).
        { rewrite if_false by (intro; subst; contradiction). entailer!. }
        Exists K R l q'. entailer!. split.
        + rewrite H1. unfold hcnt_prune. simpl. unfold CNT_W.
          replace (top' <=? x + 1 + 8128) with false by (symmetry; apply Z.leb_gt; lia). auto.
        + intros y Hy. apply H5. right. auto.
      - rewrite !add64_repr in H8. rewrite !Int64.unsigned_repr in H8 by (rewrite CNT_R_val in *; rep_lia).
        forward. forward.
        Exists (K ++ [x]) R (field_address tacc [StructField _next] q) q'. entailer!.
        { split.
          - rewrite H1, <- app_assoc. f_equal. unfold hcnt_prune. simpl. unfold CNT_W.
            replace (top' <=? x + 1 + 8128) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
          - intros y Hy. apply H5. right. auto. }
        { rewrite acc_split.
          replace (csh Tsh (K ++ [x])) with Ews by (destruct K; reflexivity).
          sep_apply (cseg_extend Tsh K v_set l q x). cancel. } }
    Intros p''.
    Exists i top' (hcnt_prune top' L') bm' p''. entailer!. apply cnt_inv_prune3; auto. }
  { Intros i top L bm p. forward. Exists (i + 1) top L bm p. entailer!. }
  Intros top L bm p.
  forward_loop (EX L: list Z, EX p: val,
    PROP ()
    LOCAL (lvar _set (tptr tacc) v_set; lvar _c tnrc v_c; gvars gv)
    SEP (mem_mgr gv; data_at Tsh (tptr tacc) p v_set; accs L p; data_at Tsh tnrc (hcnt_c top bm) v_c; TT))%assert
  break: (
    PROP ()
    LOCAL (lvar _set (tptr tacc) v_set; lvar _c tnrc v_c; gvars gv)
    SEP (mem_mgr gv; data_at Tsh (tptr tacc) nullval v_set; data_at Tsh tnrc (hcnt_c top bm) v_c; TT))%assert.
  { Exists L p. entailer!. }
  { Intros L' p'. forward.
    forward_if.
    2:{ forward. entailer!. }
    destruct L' as [|x L']. { simpl accs. Intros. subst p'. contradiction. }
    simpl accs. Intros q.
    forward. forward. forward.
    forward_call (tacc, p', gv).
    { rewrite if_false by (intro; subst; contradiction). entailer!. }
    forward. Exists L' q. entailer!. }
  unfold abbreviate in POSTCONDITION. subst POSTCONDITION. unfold hcnt3_post.
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (TT))%assert
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  abbreviate_semax.
  forward.
  sep_apply (data_at_data_at_ Tsh tnrc). sep_apply (data_at_data_at_ Tsh (tptr tacc)). cancel.
Qed.

Theorem hcnt_piece3 : piece_ok [u_hcnt3] hcnt3_imports hcnt3_G.
Proof.
  split.
  - repeat constructor; simpl; intuition discriminate.
  - repeat constructor; exists u_hcnt3; (split; [left; reflexivity|]).
    + exists f_draw_steps; split; [reflexivity | exact body_draw_steps3].
    + exists f_draw_u64; split; [reflexivity | exact body_draw_u643].
    + exists f_main; split; [reflexivity | exact body_main3].
Qed.
