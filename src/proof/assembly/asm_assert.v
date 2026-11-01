(* The assembly of asm_lib.v for harnesses that check with gp_assert (and restrict with gp_assume).

   asm_lib.v assembles a law from its pieces when the program's externals are among asm_env.env_specs
   (malloc, free, the nondet_ functions).  The harnesses of the short laws also call gp_assert and gp_assume of the
   external world QuickProof.Env; this file extends the assembly to them, for any program:
   - env_specs_gp = asm_env.env_specs ++ [gp_assert_spec; gp_assume_spec], the externals a body proof may call;
   - asm_check_gp, asm_Gall_gp, asm_harness_safe_gp: asm_check, asm_Gall, asm_harness_safe with these externals.
   Their bodies are QuickProof.EnvBodies.env_body_assert / env_body_assume.  Everything else (vacuous
   specifications, lifting of pieces, compspecs) is asm_lib.v's. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.EnvBodies.
Require Import WgNoise.proof.assembly.asm_env.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.assembly.asm_lib.

Local Notation find_id := initial_world.find_id.

(* ---------------------------------------------------------------------------------------------------- *)
(* 1. The external world with gp_assert and gp_assume.                                                    *)

Definition env_fundef_gp (i: ident) : option (fundef function) :=
  if Pos.eqb i _gp_assert then
    Some (External (EF_external "gp_assert" (mksignature (AST.Xint :: nil) AST.Xvoid cc_default))
            (tint :: nil) tvoid cc_default)
  else if Pos.eqb i _gp_assume then
    Some (External (EF_external "gp_assume" (mksignature (AST.Xint :: nil) AST.Xvoid cc_default))
            (tint :: nil) tvoid cc_default)
  else env_fundef i.

Section Env.
Context {W: compspecs}.

(* the externals the body proofs may call *)
Definition env_specs_gp : funspecs := @asm_env.env_specs W ++ [gp_assert_spec; gp_assume_spec].

Lemma env_SF_gp (V: varspecs) (ge: Genv.t (fundef function) type) (G: funspecs) i fd phi:
  In (i, phi) (@QuickProof.Env.env_specs W) ->
  env_fundef_gp i = Some fd ->
  genv_find_func ge i fd ->
  @SF (@HonestEspec W) W V ge G i fd phi.
Proof.
  intros HIn Hfd GF. unfold env_fundef_gp in Hfd.
  destruct (Pos.eqb i _gp_assert) eqn:Ea; [|destruct (Pos.eqb i _gp_assume) eqn:Eb].
  3: exact (env_SF V ge G i fd phi HIn Hfd GF).
  all: apply Pos.eqb_eq in Ea || apply Pos.eqb_eq in Eb; subst i; inv Hfd.
  all: unfold QuickProof.Env.env_specs in HIn; simpl in HIn.
  all: repeat destruct HIn as [HIn|HIn]; try contradiction;
         try (apply (f_equal fst) in HIn; vm_compute in HIn; discriminate HIn).
  all: inv HIn.
  all: unfold SF, semaxfunc_ExternalInfo, gp_assert_spec, gp_assume_spec, NDmk_funspec.
  all: refine (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj (or_introl eq_refl) (conj _ (conj _ GF))))))).
  all: try first [exact (@env_body_assert W) | exact (@env_body_assume W) | exact env_body_assert | exact env_body_assume].
  all: intros gx ts x ret; destruct ret as [rv|]; apply prop_right; exact I.
Qed.

End Env.

(* ---------------------------------------------------------------------------------------------------- *)
(* 2. The component's funspecs and the checks on the program, with these externals.                      *)

Definition env_ids_gp : list ident := env_ids ++ [_gp_assert; _gp_assume].

Definition asm_E_gp {W: compspecs} (p: QP.program function) : funspecs :=
  filter (fun ix => asm_present_ext p (fst ix)) (@env_specs_gp W).

Definition asm_E_gp_ids (p: QP.program function) : list ident := filter (asm_present_ext p) env_ids_gp.

Definition asm_G0_gp {W: compspecs} (p: QP.program function) (Gr: funspecs) (ids: list ident) : funspecs :=
  @asm_E_gp W p ++ Gr ++ asm_vac p (QP.prog_main p :: ids).

Definition asm_check_gp (W: compspecs) (p: QP.program function) (ids: list ident) : bool :=
  (compute_list_norepet (map fst (QPvarspecs p) ++
                        QP.prog_main p :: asm_E_gp_ids p ++ ids ++ asm_vac_ids p (QP.prog_main p :: ids)) &&
  forallb (fun ix => asm_fun_ok W (snd ix)) (asm_int_funs p) &&
  forallb (asm_is_internal p) (QP.prog_main p :: ids) &&
  forallb (fun i => match Maps.PTree.get i (QP.prog_defs p), env_fundef_gp i with
                    | Some (Gfun (External (EF_external n s) ts t cc)), Some (External (EF_external n' s') ts' t' cc') =>
                        (String.eqb n n' && proj_sumbool (signature_eq s s') &&
                         proj_sumbool (list_eq_dec type_eq ts ts') && proj_sumbool (type_eq t t') &&
                         proj_sumbool (calling_convention_eq cc cc'))%bool
                    | _, _ => false end) (asm_E_gp_ids p) &&
  QPall_initializers_aligned p &&
  forallb not_builtin (Maps.PTree.elements (QP.prog_defs p)))%bool.

Lemma asm_E_gp_ids_eq {W: compspecs} p: map fst (@asm_E_gp W p) = asm_E_gp_ids p.
Proof. unfold asm_E_gp, asm_E_gp_ids. rewrite asm_map_fst_filter. reflexivity. Qed.

Definition asm_Ew_gp {W: compspecs} (p: QP.program function) : funspecs := map (@env_world W) (@asm_E_gp W p).

Definition asm_G0w_gp {W: compspecs} (p: QP.program function) (Gr: funspecs) (ids: list ident) : funspecs :=
  @asm_Ew_gp W p ++ Gr ++ asm_vac p (QP.prog_main p :: ids).

Lemma asm_Ew_gp_fst {W: compspecs} p: map fst (@asm_Ew_gp W p) = map fst (@asm_E_gp W p).
Proof.
  unfold asm_Ew_gp. rewrite map_map. apply map_ext. intros [i s]. unfold env_world.
  destruct (Pos.eqb (fst (i, s)) _nondet_bytes); reflexivity.
Qed.

Lemma asm_Ew_gp_In {W: compspecs} p i phi:
  In (i, phi) (@asm_Ew_gp W p) -> In (i, phi) (@QuickProof.Env.env_specs W).
Proof.
  unfold asm_Ew_gp, asm_E_gp. intros H. apply in_map_iff in H as [[j s] [E H]].
  apply filter_In in H as [H _]. rewrite asm_env_world_eq in E.
  destruct (Pos.eqb j _nondet_bytes) eqn:Ej.
  - apply Pos.eqb_eq in Ej. subst j. rewrite <- E.
    unfold QuickProof.Env.env_specs. do 5 right. left. reflexivity.
  - rewrite <- E. unfold env_specs_gp, asm_env.env_specs in H. simpl in H.
    repeat destruct H as [H|H]; try contradiction; rewrite <- H;
      unfold QuickProof.Env.env_specs; try (repeat first [left; reflexivity | right]; fail).
    apply (f_equal fst) in H. unfold asm_env.nondet_bytes_spec in H. cbn [fst] in H.
    subst j. rewrite Pos.eqb_refl in Ej. discriminate.
Qed.

(* The bodies, proved in (main :: E ++ Gr ++ Gv), hold in the world's list (main :: Ew ++ Gr ++ Gv). *)
Lemma asm_covers_world_gp {W: compspecs} p (P R: funspecs):
  list_norepet (map fst (P ++ @asm_E_gp W p ++ R)) ->
  asm_covers (P ++ @asm_Ew_gp W p ++ R) (P ++ @asm_E_gp W p ++ R).
Proof.
  intros LNR. unfold asm_covers. rewrite Forall_forall. intros [i s] Hin. cbn [fst snd].
  assert (Hf: find_id i (P ++ asm_E_gp p ++ R) = Some s) by (apply initial_world.find_id_i; auto).
  rewrite !asm_find_id_app_eq in Hf |- *. unfold asm_Ew_gp. rewrite asm_find_id_world.
  destruct (find_id i P) as [s0|].
  { injection Hf as <-. exists s0; split; [reflexivity | apply funspec_sub_refl]. }
  destruct (find_id i (asm_E_gp p)) as [s1|] eqn:E1.
  2: { exists s; split; [exact Hf | apply funspec_sub_refl]. }
  injection Hf as <-. eexists; split; [reflexivity |].
  rewrite asm_env_world_eq. destruct (Pos.eqb i _nondet_bytes) eqn:Ej; cbn [snd]; [| apply funspec_sub_refl].
  apply Pos.eqb_eq in Ej. subst i.
  apply asm_find_id_In in E1. unfold asm_E_gp in E1. apply filter_In in E1 as [E1 _].
  unfold env_specs_gp, asm_env.env_specs in E1. simpl in E1.
  repeat destruct E1 as [E1|E1]; try contradiction;
    try (apply (f_equal fst) in E1; simpl in E1; vm_compute in E1; discriminate E1).
  apply (f_equal snd) in E1. unfold asm_env.nondet_bytes_spec in E1. cbn [snd] in E1. subst s1.
  apply asm_env.nondet_bytes_sub.
Qed.

(* ---------------------------------------------------------------------------------------------------- *)
(* 3. harness_safe.                                                                                       *)

Theorem asm_harness_safe_gp (p: QP.program function) (OK: QPprogram_OK p) (W: compspecs)
  (HW: W = compspecs_of_QPcomposite_env (QP.prog_comp_env p) (proj2 OK))
  (CBC: forall H, cenv_built_correctly
                    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) []))
                    (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) = Errors.OK tt)
  (EXT_OK: all_unspecified_OK p)
  (post: (ident -> val) -> environ -> mpred)
  (Gr: funspecs) (ids: list ident)
  (IDS: map fst Gr = ids)
  (CHECK: asm_check_gp W p ids = true)
  (CC: Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) Gr)
  (BODIES: asm_bodies W p ((QP.prog_main p, QPmain_spec_ext' p tt post) :: @asm_G0_gp W p Gr ids)
                          ((QP.prog_main p, QPmain_spec_ext' p tt post) :: Gr)) :
  harness_safe p.
Proof.
  subst W.
  set (W := compspecs_of_QPcomposite_env (QP.prog_comp_env p) (proj2 OK)).
  set (ms := QPmain_spec_ext' p tt post) in *.
  set (main := QP.prog_main p) in *.
  (* the bodies, proved with env_specs_gp, in the world's list: nondet_bytes_sub *)
  assert (BODIESw: asm_bodies W p ((main, ms) :: @asm_G0w_gp W p Gr ids) ((main, ms) :: Gr)).
  { pose proof CHECK as CHK. unfold asm_check_gp in CHK. rewrite !andb_true_iff in CHK.
    destruct CHK as [[[[[LNR0 FOK0] _] _] _] _].
    apply compute_list_norepet_e in LNR0. rewrite forallb_forall in FOK0.
    assert (MO: map fst (@asm_G0_gp W p Gr ids) = asm_E_gp_ids p ++ ids ++ asm_vac_ids p (main :: ids)).
    { unfold asm_G0_gp. rewrite !map_app, asm_E_gp_ids_eq, asm_vac_ids_eq, IDS. reflexivity. }
    assert (MW: map fst (@asm_G0w_gp W p Gr ids) = asm_E_gp_ids p ++ ids ++ asm_vac_ids p (main :: ids)).
    { unfold asm_G0w_gp. rewrite !map_app, asm_Ew_gp_fst, asm_E_gp_ids_eq, asm_vac_ids_eq, IDS. reflexivity. }
    assert (LNRo: list_norepet (map fst (QPvarspecs p) ++ map fst ((main, ms) :: @asm_G0_gp W p Gr ids))).
    { change (map fst ((main, ms) :: @asm_G0_gp W p Gr ids)) with (main :: map fst (@asm_G0_gp W p Gr ids)).
      rewrite MO. exact LNR0. }
    assert (LNRw: list_norepet (map fst (QPvarspecs p) ++ map fst ((main, ms) :: @asm_G0w_gp W p Gr ids))).
    { change (map fst ((main, ms) :: @asm_G0w_gp W p Gr ids)) with (main :: map fst (@asm_G0w_gp W p Gr ids)).
      rewrite MW. exact LNR0. }
    assert (COV: asm_covers ((main, ms) :: @asm_G0w_gp W p Gr ids) ((main, ms) :: @asm_G0_gp W p Gr ids)).
    { apply (asm_covers_world_gp p [(main, ms)] (Gr ++ asm_vac p (main :: ids))).
      apply list_norepet_append_right in LNRo. exact LNRo. }
    unfold asm_bodies in BODIES |- *. rewrite Forall_forall in BODIES |- *. intros ip Hip.
    destruct (BODIES ip Hip) as [f [Hf SB]]. exists f; split; [exact Hf |].
    apply (@asm_body_lift W W (QPvarspecs p) (QPvarspecs p) ((main, ms) :: @asm_G0_gp W p Gr ids)
             ((main, ms) :: @asm_G0w_gp W p Gr ids) f ip (cspecs_sub_refl)); auto.
    - apply asm_int_funs_In in Hf. apply FOK0 in Hf. simpl in Hf. unfold asm_fun_ok in Hf.
      rewrite !andb_true_iff in Hf. destruct Hf as [[[_ P2] _] _]. rewrite forallb_forall in P2.
      apply Forall_forall; intros; apply P2; auto.
    - apply Forall_forall. intros [i t] Hi. apply initial_world.find_id_i; [exact Hi |].
      apply list_norepet_append_left in LNRw. exact LNRw. }
  clear BODIES.
  set (G0 := @asm_G0w_gp W p Gr ids) in *.
  unfold asm_check_gp in CHECK.
  rewrite !andb_true_iff in CHECK.
  destruct CHECK as [[[[[LNR FOK] INT] EXT] ALIGNED] NB].
  apply compute_list_norepet_e in LNR.
  rewrite forallb_forall in FOK, INT, EXT.
  assert (MAPG0: map fst G0 = asm_E_gp_ids p ++ ids ++ asm_vac_ids p (main :: ids)).
  { unfold G0, asm_G0w_gp. rewrite !map_app, asm_Ew_gp_fst, asm_E_gp_ids_eq, asm_vac_ids_eq, IDS. reflexivity. }
  assert (NOMAIN: find_id main G0 = None).
  { apply assoclists.find_id_None_iff. rewrite MAPG0.
    apply list_norepet_app in LNR as [_ [LNR _]]. inv LNR. auto. }
  assert (GM: G_merge [(main, ms)] G0 = (main, ms) :: G0) by (apply asm_G_merge_single; auto).
  set (E := @asm_Ew_gp W p) in *.
  set (GP := fun gv => InitGPred (Vardefs p) gv).
  set (G := G_merge [(main, ms)] G0).
  assert (LNR': list_norepet (map fst (QPvarspecs p) ++ map fst ((main, ms) :: G0))).
  { simpl map. rewrite MAPG0. exact LNR. }
  assert (LNRE: list_norepet (map fst E)).
  { unfold E; rewrite asm_Ew_gp_fst, asm_E_gp_ids_eq.
    apply list_norepet_append_right in LNR. inv LNR.
    apply list_norepet_append_left in H2; auto. }
  assert (F1: forall i, In i (map fst (@nil (ident * funspec))) ->
            exists f ts t cc, Maps.PTree.get i (QP.prog_defs p) = Some (Gfun (External f ts t cc))).
  { intros i H; inv H. }
  assert (F2: list_norepet (map fst (QPvarspecs p) ++ map fst (G ++ nil))).
  { unfold G; rewrite GM, app_nil_r; auto. }
  assert (F4: list_norepet (map fst (@nil (ident * funspec)))) by constructor.
  assert (F5: forall i, In i (map fst E) ->
            exists f ts t cc, Maps.PTree.get i (QP.prog_defs p) = Some (Gfun (External f ts t cc))).
  { intros i H. unfold E in H; rewrite asm_Ew_gp_fst, asm_E_gp_ids_eq in H. unfold asm_E_gp_ids in H.
    apply filter_In in H as [_ H]. unfold asm_present_ext, isSomeGfunExternal in H.
    destruct (Maps.PTree.get i (QP.prog_defs p)) as [[[?|? ? ? ?]|]|]; try discriminate; eauto. }
  assert (INT': forall i, In i (main :: ids) -> In i (map fst (asm_int_funs p))).
  { intros i H. apply INT in H. apply asm_is_internal_e in H as [f H].
    apply asm_int_funs_In in H. apply in_map with (f := fst) in H. exact H. }
  assert (F6: forall i, In i (IntIDs p ++ map fst E) <-> In i (map fst G)).
  { intros i. unfold G; rewrite GM. simpl map. rewrite MAPG0. unfold E; rewrite asm_Ew_gp_fst, asm_E_gp_ids_eq.
    rewrite <- asm_int_funs_IntIDs. unfold asm_vac_ids.
    split; intro H.
    - apply in_app in H as [H|H].
      + destruct (id_in_list i (main :: ids)) eqn:E1.
        * apply id_in_list_true in E1. destruct E1 as [E1|E1]; [left; auto|].
          right; apply in_app; right; apply in_app; left; auto.
        * right; apply in_app; right; apply in_app; right.
          apply in_map_iff in H as [[j f] [Hj H]]; simpl in Hj; subst j.
          apply in_map_iff. exists (i, f); split; auto. apply filter_In; split; auto.
          change (fst (i, f)) with i. rewrite E1; auto.
      + right; apply in_app; left; auto.
    - destruct H as [H|H].
      + apply in_app; left. apply INT'. left; auto.
      + apply in_app in H as [H|H]; [apply in_app; right; auto|].
        apply in_app in H as [H|H]; [apply in_app; left; apply INT'; right; auto|].
        apply in_app; left.
        apply in_map_iff in H as [[j f] [Hj H]]; simpl in Hj; subst j.
        apply filter_In in H as [H _]. apply in_map with (f := fst) in H. exact H. }
  assert (F7: forall i, In i (map fst E) -> find_id i E = find_id i G).
  { intros i H. unfold G; rewrite GM. simpl.
    rewrite if_false.
    2:{ intro; subst i. unfold E in H; rewrite asm_Ew_gp_fst, asm_E_gp_ids_eq in H.
        apply list_norepet_app in LNR as [_ [LNR _]]. inv LNR. apply H2. apply in_app; left; auto. }
    destruct (find_id i E) as [x|] eqn:E1.
    - unfold G0, asm_G0w_gp. symmetry. apply asm_find_id_app_Some. exact E1.
    - apply assoclists.find_id_None_iff in E1. contradiction. }
  assert (F8: forall i phi fd, Maps.PTree.get i (QP.prog_defs p) = Some (Gfun fd) -> find_id i G = Some phi ->
            @SF (@HonestEspec W) W (QPvarspecs p) (QPglobalenv p) (nil ++ G) i fd phi).
  { intros i phi fd Hd Hf. unfold G in *; rewrite GM in *. simpl app.
    assert (GF: genv_find_func (QPglobalenv p) i fd) by (apply QPprogdefs_GFF; auto).
    assert (INL: id_in_list i (map fst ((main, ms) :: G0)) = true).
    { apply assoclists.id_in_list_true_i. apply asm_find_id_In in Hf.
      apply in_map with (f := fst) in Hf; exact Hf. }
    assert (FOKi: forall f, Maps.PTree.get i (QP.prog_defs p) = Some (Gfun (Internal f)) ->
              semax_body_params_ok f = true /\
              Forall (fun it => complete_type (@cenv_cs W) (snd it) = true) (fn_vars f) /\
              @var_sizes_ok W (fn_vars f) /\ fn_callconv f = cc_default).
    { intros f Hf'. apply asm_int_funs_In in Hf'. apply FOK in Hf'. simpl in Hf'.
      unfold asm_fun_ok in Hf'. rewrite !andb_true_iff in Hf'.
      destruct Hf' as [[[P1 P2] P3] P4]. rewrite forallb_forall in P2, P3.
      split3; [auto | apply Forall_forall; intros; apply P2; auto | split].
      - apply Forall_forall; intros x Hx. apply P3 in Hx. apply Z.leb_le in Hx. exact Hx.
      - destruct (calling_convention_eq (fn_callconv f) cc_default); [auto | discriminate]. }
    assert (REAL: forall ph, In (i, ph) ((main, ms) :: Gr) -> callingconvention_of_funspec ph = cc_default ->
              @SF (@HonestEspec W) W (QPvarspecs p) (QPglobalenv p) ((main, ms) :: G0) i fd ph).
    { intros ph Hin Hcc. unfold asm_bodies in BODIESw. rewrite Forall_forall in BODIESw.
      destruct (BODIESw _ Hin) as [f [Hf' SB]]. simpl in Hf'. rewrite Hd in Hf'. inv Hf'.
      rewrite Hd in *. destruct (FOKi f eq_refl) as [P1 [P2 [P3 P4]]].
      apply SF_internal_sound. constructor; auto.
      - rewrite INL, P1; auto.
      - rewrite P4, Hcc; auto. }
    simpl in Hf. if_tac in Hf.
    { subst i. inv Hf. apply REAL; [left; auto | reflexivity]. }
    unfold G0, asm_G0w_gp in Hf. apply asm_find_id_app in Hf as [Hf|[_ Hf]].
    - (* the external world *)
      apply asm_find_id_In in Hf. pose proof Hf as Hi.
      apply in_map with (f := fst) in Hi; simpl in Hi. fold E in Hi.
      unfold E in Hi; rewrite asm_Ew_gp_fst, asm_E_gp_ids_eq in Hi.
      apply asm_Ew_gp_In in Hf.
      apply (env_SF_gp _ _ _ _ _ _ Hf); auto.
      specialize (EXT i Hi). rewrite Hd in EXT.
      destruct fd as [|ef ts t cc]; try discriminate. destruct ef; try discriminate.
      destruct (env_fundef_gp i) as [[|ef' ts' t' cc']|] eqn:EF; try discriminate.
      destruct ef'; try discriminate.
      rewrite !andb_true_iff in EXT. destruct EXT as [[[[N S] L] T] C].
      apply String.eqb_eq in N.
      destruct (signature_eq _ _); [|discriminate]. destruct (list_eq_dec type_eq _ _); [|discriminate].
      destruct (type_eq _ _); [|discriminate]. destruct (calling_convention_eq _ _); [|discriminate].
      subst; reflexivity.
    - apply asm_find_id_app in Hf as [Hf|[_ Hf]].
      + (* the real specifications *)
        apply asm_find_id_In in Hf. apply REAL; [right; auto|].
        rewrite Forall_forall in CC. apply (CC _ Hf).
      + (* the vacuous ones *)
        apply asm_find_id_In in Hf. unfold asm_vac in Hf.
        apply in_map_iff in Hf as [[j f] [Hj Hf]]. inv Hj.
        apply filter_In in Hf as [Hf _]. apply asm_int_funs_In in Hf.
        rewrite Hd in Hf. inv Hf. rewrite Hd in *. destruct (FOKi f eq_refl) as [P1 [P2 [P3 P4]]].
        apply SF_vacuous; auto. rewrite INL, P1; auto. }
  assert (F9: forall i phi, find_id i (@nil (ident * funspec)) = Some phi ->
            exists phi', find_id i G = Some phi' /\ funspec_sub phi' phi) by (intros; discriminate).
  assert (F10: forall gv, globals_ok gv -> InitGPred (Vardefs p) gv |-- GP gv) by (intros; apply derives_refl).
  pose (c := @Build_Component (@HonestEspec W) (QPvarspecs p) E nil p nil GP G OK F1 F2 LNRE F4 F5 F6 F7 F8 F9 F10).
  assert (MAIN': isSome (Maps.PTree.get main (QP.prog_defs p))).
  { destruct (asm_is_internal_e p main (INT main (or_introl eq_refl))) as [f Hf]. rewrite Hf; exact I. }
  exists W, OK, (cenv_built_correctly_e _ _ (CBC _)), G.
  exact (WholeComponent_semax_progConstructive (@HonestEspec W) E p nil GP ms G0 c NOMAIN tt
           (ex_intro _ post eq_refl) MAIN' EXT_OK ALIGNED NB CBC).
Qed.

(* ---------------------------------------------------------------------------------------------------- *)
(* 4. Glue for the law files (as asm_lib.v's).                                                            *)

(* the whole list of funspecs of the component, main first *)
Definition asm_Gall_gp {W: compspecs} (p: QP.program function) (post: (ident -> val) -> environ -> mpred)
    (Gr: funspecs) (ids: list ident) : funspecs :=
  (QP.prog_main p, QPmain_spec_ext' p tt post) :: @asm_G0_gp W p Gr ids.

Lemma asm_Gall_gp_norepet (W: compspecs) p post Gr ids:
  map fst Gr = ids -> asm_check_gp W p ids = true ->
  list_norepet (map fst (QPvarspecs p) ++ map fst (@asm_Gall_gp W p post Gr ids)).
Proof.
  intros IDS CHECK. unfold asm_check_gp in CHECK. rewrite !andb_true_iff in CHECK.
  destruct CHECK as [[[[[LNR _] _] _] _] _]. apply compute_list_norepet_e in LNR.
  unfold asm_Gall_gp, asm_G0_gp. simpl map. rewrite !map_app, asm_E_gp_ids_eq, asm_vac_ids_eq, IDS. exact LNR.
Qed.

Lemma asm_Gall_gp_norepet' (W: compspecs) p post Gr ids:
  map fst Gr = ids -> asm_check_gp W p ids = true -> list_norepet (map fst (@asm_Gall_gp W p post Gr ids)).
Proof. intros; eapply list_norepet_append_right, asm_Gall_gp_norepet; eauto. Qed.

Lemma asm_Gr_gp_incl (W: compspecs) p post Gr ids: incl Gr (@asm_Gall_gp W p post Gr ids).
Proof. intros x H. right. unfold asm_G0_gp. apply in_app; right; apply in_app; left; auto. Qed.

Lemma asm_E_gp_incl (W: compspecs) p post Gr ids i s:
  In (i, s) (@env_specs_gp W) -> asm_present_ext p i = true -> In (i, s) (@asm_Gall_gp W p post Gr ids).
Proof. intros H1 H2. right. unfold asm_G0_gp. apply in_app; left. apply filter_In; auto. Qed.
