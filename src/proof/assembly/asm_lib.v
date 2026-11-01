(* The assembly library: from pieces to harness_safe.

   One whole-program VST Component over the law's whole_prog, turned into harness_safe by VST's
   WholeComponent_semax_progConstructive (floyd/VSU.v), which exposes the compspecs of the component so that
   the external world HonestEspec is taken at the same compspecs, as harness_safe demands.

   Funspecs of the component: (main, main's spec) :: E ++ Gr ++ Gv, where
   - E  = the external world QuickProof.Env (its env_specs at the world compspecs W), for the externals present;
   - Gr = the real specifications of the internal functions the harness reaches (from the pieces);
   - Gv = vacuous specifications (precondition False) of every other internal function (asm_vac).
   Every obligation that depends only on the program (identifiers, types of the locals, signatures of the
   externals, ...) is a boolean check computed once per law (asm_check); the body proofs come from pieces
   (piece_lift), lifted from a unit's compspecs to the world W (cspecs_sub) and from the unit's Imports ++ G to
   the whole list (funspec_sub per import). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.EnvBodies.
Require Import WgNoise.proof.assembly.asm_env.
Require Import WgNoise.proof.common.pieces.

Local Notation find_id := initial_world.find_id.

(* ---------------------------------------------------------------------------------------------------- *)
(* 1. The external world: the fundefs clightgen gives the externals of quickproof.h, and their SF.        *)

Definition env_fundef (i: ident) : option (fundef function) :=
  if Pos.eqb i _nondet_u8 then
    Some (External (EF_external "nondet_u8" (mksignature nil AST.Xint8unsigned cc_default)) nil tuchar cc_default)
  else if Pos.eqb i _nondet_u32 then
    Some (External (EF_external "nondet_u32" (mksignature nil AST.Xint cc_default)) nil tuint cc_default)
  else if Pos.eqb i _nondet_size then
    Some (External (EF_external "nondet_size" (mksignature nil AST.Xlong cc_default)) nil tulong cc_default)
  else if Pos.eqb i _nondet_bytes then
    Some (External (EF_external "nondet_bytes" (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xvoid cc_default))
            (tptr tuchar :: tulong :: nil) tvoid cc_default)
  else if Pos.eqb i _quickproof_malloc then
    Some (External (EF_external "quickproof_malloc" (mksignature (AST.Xlong :: nil) AST.Xptr cc_default))
            (tulong :: nil) (tptr tvoid) cc_default)
  else if Pos.eqb i _quickproof_free then
    Some (External (EF_external "quickproof_free" (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
            (tptr tvoid :: nil) tvoid cc_default)
  else None.

Section Env.
Context {W: compspecs}.

Lemma env_SF (V: varspecs) (ge: Genv.t (fundef function) type) (G: funspecs) i fd phi:
  In (i, phi) (@QuickProof.Env.env_specs W) ->
  env_fundef i = Some fd ->
  genv_find_func ge i fd ->
  @SF (@HonestEspec W) W V ge G i fd phi.
Proof.
  intros HIn Hfd GF.
  unfold QuickProof.Env.env_specs in HIn; simpl in HIn.
  repeat destruct HIn as [HIn|HIn]; try contradiction; inv HIn; inv Hfd.
  all: unfold SF, semaxfunc_ExternalInfo, malloc_spec', free_spec', nondet_u8_spec, nondet_u32_spec,
         nondet_size_spec, QuickProof.Env.nondet_bytes_spec, NDmk_funspec.
  all: refine (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj (or_introl eq_refl) (conj _ (conj _ GF))))))).
  all: try first [exact (@env_body_malloc W) | exact (@env_body_free W) | exact (@env_body_u8 W)
                 | exact (@env_body_u32 W) | exact (@env_body_size W)
                 | exact (@QuickProof.EnvBodies.env_body_bytes W)].
  all: intros gx ts x ret; repeat match goal with x: prod _ _ |- _ => destruct x end.
  all: destruct ret as [rv|].
  all: try (apply prop_right; exact I).
  all: apply andp_left1.
  all: unfold PROPx, LOCALx, SEPx, local, lift1; simpl.
  all: try (destruct x as [t gv]).
  all: Intros y.
  all: unfold liftx, lift, eval_id in *; simpl in *.
  all: repeat match goal with H: (_ /\ _) /\ True |- _ => destruct H as [[? ?] _] end; subst; try contradiction.
  all: try (apply prop_right; simpl; rewrite ?Int.unsigned_repr by rep_lia; rep_lia).
  all: try (apply prop_right; simpl; auto; fail).
  destruct (EqDec_val rv nullval). { apply prop_right; subst; simpl; auto. }
  sep_apply (data_at__local_facts Ews t rv). entailer!.
Qed.

End Env.

(* ---------------------------------------------------------------------------------------------------- *)
(* 2. Vacuous specifications (precondition False) of the internal functions no harness step reaches.     *)

Lemma SF_vacuous {Espec: OracleKind} {cs: compspecs} V ge (G: funspecs) i f:
  (id_in_list i (map fst G) && semax_body_params_ok f)%bool = true ->
  Forall (fun it => complete_type (@cenv_cs cs) (snd it) = true) (fn_vars f) ->
  @var_sizes_ok cs (fn_vars f) ->
  genv_find_func ge i (Internal f) ->
  @SF Espec cs V ge G i (Internal f) (vacuous_funspec (Internal f)).
Proof.
  intros H1 H2 H3 H4.
  red; red. split3; [exact H1 | exact H2 | split3; [exact H3 | reflexivity | split; [ | exact H4]]].
  destruct f; split3; [reflexivity | reflexivity | ].
  intros; apply semax_vacuous.
Qed.

(* ---------------------------------------------------------------------------------------------------- *)
(* 3. Lifting a body proof from a unit (its compspecs, varspecs, Imports ++ G) to the whole program.     *)

Lemma asm_find_id_In {A} i (G: list (ident * A)) s: find_id i G = Some s -> In (i, s) G.
Proof.
  induction G as [|[j t] G IH]; simpl; intros H; [discriminate|].
  if_tac in H; [inv H; auto | auto].
Qed.

Lemma asm_make_tycontext_g V G i:
  Maps.PTree.get i (make_tycontext_g V G) =
  match find_id i G with Some fs => Some (type_of_funspec fs) | None => find_id i V end.
Proof.
  induction G as [|[j fs] G IH]; simpl.
  - apply semax_prog.make_tycontext_g_nilG_find_id.
  - rewrite Maps.PTree.gsspec. if_tac; subst; [rewrite if_true | rewrite if_false]; auto.
Qed.

Lemma asm_funspec_sub_type s' s: funspec_sub s' s -> type_of_funspec s' = type_of_funspec s.
Proof.
  destruct s' as [[? ?] ? ? ? ? ? ?], s as [[? ?] ? ? ? ? ? ?]; simpl; intros [[H1 H2] _]; inv H1; auto.
Qed.

Lemma asm_norepet_V_G (Vw: varspecs) (Gw: funspecs) i t:
  list_norepet (map fst Vw ++ map fst Gw) -> find_id i Vw = Some t -> find_id i Gw = None.
Proof.
  intros LNR H.
  destruct (find_id i Gw) eqn:E; auto.
  apply asm_find_id_In in H, E.
  apply list_norepet_app in LNR as [_ [_ D]].
  exfalso; apply (D i i); auto; apply in_map_iff; eexists; split; eauto; reflexivity.
Qed.

Definition asm_covers (Gw: funspecs) (Gu: funspecs) : Prop :=
  Forall (fun ix => exists s', find_id (fst ix) Gw = Some s' /\ funspec_sub s' (snd ix)) Gu.

Lemma asm_body_lift {csu W: compspecs} (Vu Vw: varspecs) (Gu Gw: funspecs) f ip:
  cspecs_sub csu W ->
  Forall (fun it => complete_type (@cenv_cs csu) (snd it) = true) (fn_vars f) ->
  list_norepet (map fst Vw ++ map fst Gw) ->
  Forall (fun it => find_id (fst it) Vw = Some (snd it)) Vu ->
  asm_covers Gw Gu ->
  @semax_body Vu Gu csu f ip -> @semax_body Vw Gw W f ip.
Proof.
  intros CSUB COMPL LNR HV HG SB; unfold asm_covers in HG.
  apply (@semax_body_cenv_sub csu W CSUB); auto.
  apply (semax_body_subsumption _ _ _ _ _ _ _ SB).
  apply tycontext_sub_i99. split; intro i.
  - rewrite !asm_make_tycontext_g.
    destruct (find_id i Gu) as [s|] eqn:E.
    + apply asm_find_id_In in E.
      rewrite Forall_forall in HG; destruct (HG _ E) as [s' [E' S]]; simpl in E'.
      rewrite E'; simpl; rewrite (asm_funspec_sub_type _ _ S); auto.
    + destruct (find_id i Vu) as [t|] eqn:E2; simpl; auto.
      apply asm_find_id_In in E2.
      rewrite Forall_forall in HV; specialize (HV _ E2); simpl in HV.
      rewrite (asm_norepet_V_G _ _ _ _ LNR HV); auto.
  - rewrite !semax_prog.find_id_maketycontext_s.
    destruct (find_id i Gu) as [s|] eqn:E; simpl; auto.
    apply asm_find_id_In in E.
    rewrite Forall_forall in HG; destruct (HG _ E) as [s' [E' S]]; simpl in E'.
    exists s'; split; [exact E'|]. apply seplog.funspec_sub_sub_si. apply funspec_sub_iff. exact S.
Qed.

Lemma asm_covers_incl (Gw Gp: funspecs):
  list_norepet (map fst Gw) -> incl Gp Gw -> asm_covers Gw Gp.
Proof.
  intros LNR INC. unfold asm_covers. rewrite Forall_forall. intros [i s] H.
  exists s; split; [ | apply funspec_sub_refl].
  apply INC in H. simpl. apply initial_world.find_id_i; auto.
Qed.

Lemma asm_covers_app Gw G1 G2: asm_covers Gw G1 -> asm_covers Gw G2 -> asm_covers Gw (G1 ++ G2).
Proof. unfold asm_covers; intros; apply Forall_app; auto. Qed.

(* the per-unit conditions of lifting a piece's bodies into the whole program p at world W *)
Definition asm_unit_ok (W: compspecs) (p: QP.program function) (Gw: funspecs)
    (Imports: compspecs -> funspecs) (ids: list ident) (u: unit_ctx) : Prop :=
  cspecs_sub (u_cs u) W /\
  Forall (fun it => find_id (fst it) (QPvarspecs p) = Some (snd it)) (u_V u) /\
  asm_covers Gw (Imports (u_cs u)) /\
  (forall i f, In i ids -> find_internal (u_prog u) i = Some f ->
     Maps.PTree.get i (QP.prog_defs p) = Some (Gfun (Internal f)) /\
     Forall (fun it => complete_type (@cenv_cs (u_cs u)) (snd it) = true) (fn_vars f)).

(* every entry of a piece, as a body proof in the whole program *)
Definition asm_bodies (W: compspecs) (p: QP.program function) (Gw: funspecs) (G: funspecs) : Prop :=
  Forall (fun ip => exists f, Maps.PTree.get (fst ip) (QP.prog_defs p) = Some (Gfun (Internal f)) /\
                              @semax_body (QPvarspecs p) Gw W f ip) G.

Lemma asm_piece_lift (W: compspecs) (p: QP.program function) (Gw: funspecs) units Imports Gp:
  piece_ok units Imports Gp ->
  list_norepet (map fst (QPvarspecs p) ++ map fst Gw) ->
  incl Gp Gw ->
  Forall (asm_unit_ok W p Gw Imports (map fst Gp)) units ->
  asm_bodies W p Gw Gp.
Proof.
  intros [_ PK] LNR INC UOK.
  assert (CG: asm_covers Gw Gp) by (apply asm_covers_incl; auto; apply list_norepet_append_right in LNR; auto).
  unfold asm_bodies. rewrite Forall_forall in PK |- *. intros ip Hip.
  destruct (PK ip Hip) as [u [Hu [f [Hf SB]]]].
  rewrite Forall_forall in UOK. destruct (UOK u Hu) as [CS [HV [HI HF]]].
  destruct (HF (fst ip) f) as [Hdef COMPL]; auto.
  { apply in_map; auto. }
  exists f; split; auto.
  exact (asm_body_lift _ _ _ _ f ip CS COMPL LNR HV (asm_covers_app _ _ _ HI CG) SB).
Qed.

(* ---------------------------------------------------------------------------------------------------- *)
(* 3b. Compspecs inclusion and equality by computation (data only: the proof fields are irrelevant).     *)

Lemma asm_sub_option_elements {A} (t t': Maps.PTree.t A):
  Forall (fun ix => Maps.PTree.get (fst ix) t' = Some (snd ix)) (Maps.PTree.elements t) ->
  forall i, tycontext.sub_option (Maps.PTree.get i t) (Maps.PTree.get i t').
Proof.
  intros H i. destruct (Maps.PTree.get i t) as [x|] eqn:E; simpl; auto.
  apply Maps.PTree.elements_correct in E.
  rewrite Forall_forall in H. apply (H _ E).
Qed.

Lemma asm_composite_eq (c1 c2: composite): getCompositeData c1 = getCompositeData c2 -> c1 = c2.
Proof.
  destruct c1, c2; simpl; intros H; inv H. f_equal; apply proof_irr.
Qed.

Lemma asm_cspecs_sub (cs cs': compspecs):
  Forall (fun ix => Maps.PTree.get (fst ix) (Maps.PTree.map1 getCompositeData (@cenv_cs cs')) = Some (snd ix))
         (Maps.PTree.elements (Maps.PTree.map1 getCompositeData (@cenv_cs cs))) ->
  Forall (fun ix => Maps.PTree.get (fst ix) (@ha_env_cs cs') = Some (snd ix)) (Maps.PTree.elements (@ha_env_cs cs)) ->
  Forall (fun ix => Maps.PTree.get (fst ix) (@la_env_cs cs') = Some (snd ix)) (Maps.PTree.elements (@la_env_cs cs)) ->
  cspecs_sub cs cs'.
Proof.
  intros H1 H2 H3. split3.
  - intro i. pose proof (asm_sub_option_elements _ _ H1 i) as S.
    rewrite !Maps.PTree.gmap1 in S.
    destruct (Maps.PTree.get i (@cenv_cs cs)) as [c|]; simpl in *; auto.
    destruct (Maps.PTree.get i (@cenv_cs cs')) as [c'|]; simpl in *; [|discriminate].
    inv S. f_equal. apply asm_composite_eq; auto.
  - intro i; exact (asm_sub_option_elements _ _ H2 i).
  - intro i; exact (asm_sub_option_elements _ _ H3 i).
Qed.

(* A computing compspecs W is the one of p's composite environment *)
Lemma asm_compspecs_eq (W: compspecs) (ce: QP.composite_env) (H: QPcompspecs_OK ce):
  Maps.PTree.map1 getCompositeData (@cenv_cs W) =
    Maps.PTree.map1 getCompositeData (composite_env_of_QPcomposite_env ce (projT1 H)) ->
  @ha_env_cs W = Maps.PTree.map1 QP.co_ha ce ->
  @la_env_cs W = Maps.PTree.map1 QP.co_la ce ->
  W = compspecs_of_QPcomposite_env ce H.
Proof.
  intros E1 E2 E3.
  destruct (QPcompspecs_OK_e ce H) as [F1 [F2 F3]].
  apply compspecs_ext.
  - rewrite F1. apply composite_env_ext; auto.
  - rewrite F2; auto.
  - rewrite F3; auto.
Qed.

(* ---------------------------------------------------------------------------------------------------- *)
(* 4. The whole-program component and harness_safe.                                                       *)

(* the internal functions of p *)
Definition asm_int_funs (p: QP.program function) : list (ident * function) :=
  fold_right (fun (ix: ident * globdef (fundef function) type) acc =>
                match snd ix with Gfun (Internal f) => (fst ix, f) :: acc | _ => acc end)
             nil (Maps.PTree.elements (QP.prog_defs p)).

(* vacuous specifications of the internal functions not in ids *)
Definition asm_vac (p: QP.program function) (ids: list ident) : funspecs :=
  map (fun ix => (fst ix, vacuous_funspec (Internal (snd ix))))
      (filter (fun ix => negb (id_in_list (fst ix) ids)) (asm_int_funs p)).

Definition asm_vac_ids (p: QP.program function) (ids: list ident) : list ident :=
  map fst (filter (fun ix => negb (id_in_list (fst ix) ids)) (asm_int_funs p)).

(* the external world's functions present in p *)
Definition asm_present_ext (p: QP.program function) (i: ident) : bool :=
  isSomeGfunExternal (Maps.PTree.get i (QP.prog_defs p)).

Definition env_ids : list ident :=
  [_quickproof_malloc; _quickproof_free; _nondet_u8; _nondet_u32; _nondet_size; _nondet_bytes].

Definition asm_E {W: compspecs} (p: QP.program function) : funspecs :=
  filter (fun ix => asm_present_ext p (fst ix)) (@asm_env.env_specs W).

Definition asm_E_ids (p: QP.program function) : list ident := filter (asm_present_ext p) env_ids.

(* the funspecs of the component, main excepted *)
Definition asm_G0 {W: compspecs} (p: QP.program function) (Gr: funspecs) (ids: list ident) : funspecs :=
  @asm_E W p ++ Gr ++ asm_vac p (QP.prog_main p :: ids).

(* the checks on the program alone (computed once per law, by vm_compute) *)
Definition asm_fun_ok (W: compspecs) (f: function) : bool :=
  (semax_body_params_ok f &&
  forallb (fun it => complete_type (@cenv_cs W) (snd it)) (fn_vars f) &&
  forallb (fun it => @sizeof W (snd it) <=? Ptrofs.max_unsigned) (fn_vars f) &&
  proj_sumbool (calling_convention_eq (fn_callconv f) cc_default))%bool.

Definition asm_is_internal (p: QP.program function) (i: ident) : bool :=
  match Maps.PTree.get i (QP.prog_defs p) with Some (Gfun (Internal _)) => true | _ => false end.

Definition asm_check (W: compspecs) (p: QP.program function) (ids: list ident) : bool :=
  (compute_list_norepet (map fst (QPvarspecs p) ++
                        QP.prog_main p :: asm_E_ids p ++ ids ++ asm_vac_ids p (QP.prog_main p :: ids)) &&
  forallb (fun ix => asm_fun_ok W (snd ix)) (asm_int_funs p) &&
  forallb (asm_is_internal p) (QP.prog_main p :: ids) &&
  forallb (fun i => match Maps.PTree.get i (QP.prog_defs p), env_fundef i with
                    | Some (Gfun (External (EF_external n s) ts t cc)), Some (External (EF_external n' s') ts' t' cc') =>
                        (String.eqb n n' && proj_sumbool (signature_eq s s') &&
                         proj_sumbool (list_eq_dec type_eq ts ts') && proj_sumbool (type_eq t t') &&
                         proj_sumbool (calling_convention_eq cc cc'))%bool
                    | _, _ => false end) (asm_E_ids p) &&
  QPall_initializers_aligned p &&
  forallb not_builtin (Maps.PTree.elements (QP.prog_defs p)))%bool.

(* helper facts *)
Lemma asm_G_merge_single i s (G: funspecs):
  find_id i G = None -> G_merge [(i, s)] G = (i, s) :: G.
Proof.
  intros H. unfold G_merge, G_merge_aux. simpl. rewrite H. simpl. f_equal.
  induction G as [|[j t] G IH]; simpl in *; auto.
  if_tac in H; [discriminate|]. rewrite if_false by auto. f_equal; auto.
Qed.

Lemma asm_int_funs_In p i f:
  In (i, f) (asm_int_funs p) <-> Maps.PTree.get i (QP.prog_defs p) = Some (Gfun (Internal f)).
Proof.
  unfold asm_int_funs. split; intros H.
  - apply Maps.PTree.elements_complete.
    induction (Maps.PTree.elements (QP.prog_defs p)) as [|[j d] l IH]; simpl in *; [contradiction|].
    destruct d as [[g|]|]; simpl in H; try (right; auto; fail).
    destruct H as [H|H]; [inv H; left; auto | right; auto].
  - apply Maps.PTree.elements_correct in H.
    induction (Maps.PTree.elements (QP.prog_defs p)) as [|[j d] l IH]; simpl in *; [contradiction|].
    destruct H as [H|H]; [inv H; left; auto|].
    destruct d as [[g|]|]; simpl; auto.
Qed.

Lemma asm_int_funs_IntIDs p: map fst (asm_int_funs p) = IntIDs p.
Proof.
  unfold asm_int_funs, IntIDs.
  induction (Maps.PTree.elements (QP.prog_defs p)) as [|[j d] l IH]; simpl; auto.
  destruct d as [[g|]|]; simpl; auto; f_equal; auto.
Qed.

Lemma asm_map_fst_filter {A} (f: ident -> bool) (l: list (ident * A)):
  map fst (filter (fun ix => f (fst ix)) l) = filter f (map fst l).
Proof. induction l as [|[i x] l IH]; simpl; auto. destruct (f i); simpl; f_equal; auto. Qed.

Lemma asm_E_ids_eq {W: compspecs} p: map fst (@asm_E W p) = asm_E_ids p.
Proof. unfold asm_E, asm_E_ids. rewrite asm_map_fst_filter. reflexivity. Qed.

Lemma asm_vac_ids_eq p ids: map fst (asm_vac p ids) = asm_vac_ids p ids.
Proof. unfold asm_vac, asm_vac_ids. rewrite map_map. reflexivity. Qed.

Lemma asm_find_id_app {A} i (l1 l2: list (ident * A)) x:
  find_id i (l1 ++ l2) = Some x ->
  find_id i l1 = Some x \/ (find_id i l1 = None /\ find_id i l2 = Some x).
Proof.
  induction l1 as [|[j y] l1 IH]; simpl; intros H; auto.
  if_tac; auto.
Qed.

Lemma asm_is_internal_e p i:
  asm_is_internal p i = true -> exists f, Maps.PTree.get i (QP.prog_defs p) = Some (Gfun (Internal f)).
Proof.
  unfold asm_is_internal. destruct (Maps.PTree.get i (QP.prog_defs p)) as [[[f|]|]|]; try discriminate; eauto.
Qed.

Lemma asm_find_id_app_Some {A} i (l1 l2: list (ident * A)) x:
  find_id i l1 = Some x -> find_id i (l1 ++ l2) = Some x.
Proof. induction l1 as [|[j y] l1 IH]; simpl; intros H; [discriminate|]. if_tac; auto. Qed.

(* The world's specifications of the externals present in p: those of the external world QuickProof.Env.
   They are env_specs (asm_env.v), with which the bodies are proved, but for nondet_bytes, whose world
   specification also accepts NULL; the bodies are lifted to them with asm_env.nondet_bytes_sub. *)
Definition env_world {W: compspecs} (ix: ident * funspec) : ident * funspec :=
  if Pos.eqb (fst ix) _nondet_bytes then (fst ix, snd (@QuickProof.Env.nondet_bytes_spec W)) else ix.

Definition asm_Ew {W: compspecs} (p: QP.program function) : funspecs := map (@env_world W) (@asm_E W p).

Definition asm_G0w {W: compspecs} (p: QP.program function) (Gr: funspecs) (ids: list ident) : funspecs :=
  @asm_Ew W p ++ Gr ++ asm_vac p (QP.prog_main p :: ids).

Lemma asm_Ew_fst {W: compspecs} p: map fst (@asm_Ew W p) = map fst (@asm_E W p).
Proof.
  unfold asm_Ew. rewrite map_map. apply map_ext. intros [i s]. unfold env_world.
  destruct (Pos.eqb (fst (i, s)) _nondet_bytes); reflexivity.
Qed.

Lemma asm_env_world_eq {W: compspecs} i s:
  @env_world W (i, s) = if Pos.eqb i _nondet_bytes then (i, snd (@QuickProof.Env.nondet_bytes_spec W)) else (i, s).
Proof. reflexivity. Qed.

Lemma asm_Ew_In {W: compspecs} p i phi:
  In (i, phi) (@asm_Ew W p) -> In (i, phi) (@QuickProof.Env.env_specs W).
Proof.
  unfold asm_Ew, asm_E. intros H. apply in_map_iff in H as [[j s] [E H]].
  apply filter_In in H as [H _]. rewrite asm_env_world_eq in E.
  destruct (Pos.eqb j _nondet_bytes) eqn:Ej.
  - apply Pos.eqb_eq in Ej. subst j. rewrite <- E.
    unfold QuickProof.Env.env_specs. do 5 right. left. reflexivity.
  - rewrite <- E. unfold asm_env.env_specs in H.
    repeat destruct H as [H|H]; try contradiction; rewrite <- H;
      unfold QuickProof.Env.env_specs; try (repeat first [left; reflexivity | right]; fail).
    apply (f_equal fst) in H. unfold asm_env.nondet_bytes_spec in H. cbn [fst] in H.
    subst j. rewrite Pos.eqb_refl in Ej. discriminate.
Qed.

Lemma asm_find_id_app_eq {A} i (l1 l2: list (ident * A)):
  find_id i (l1 ++ l2) = match find_id i l1 with Some x => Some x | None => find_id i l2 end.
Proof. induction l1 as [|[j y] l1 IH]; simpl; auto. if_tac; auto. Qed.

Lemma asm_find_id_world {W: compspecs} i (l: funspecs):
  find_id i (map (@env_world W) l) =
  match find_id i l with Some s => Some (snd (@env_world W (i, s))) | None => None end.
Proof.
  induction l as [|[j s] l IH]; [reflexivity |].
  change (map (@env_world W) ((j, s) :: l)) with (@env_world W (j, s) :: map (@env_world W) l).
  rewrite asm_env_world_eq.
  destruct (Pos.eqb j _nondet_bytes) eqn:Ej; cbn [initial_world.find_id];
    destruct (eq_dec i j) as [<-|NE]; cbv beta iota; try exact IH;
    rewrite asm_env_world_eq, Ej; reflexivity.
Qed.

(* The bodies, proved in (main :: E ++ Gr ++ Gv), hold in the world's list (main :: Ew ++ Gr ++ Gv). *)
Lemma asm_covers_world {W: compspecs} p (P R: funspecs):
  list_norepet (map fst (P ++ @asm_E W p ++ R)) ->
  asm_covers (P ++ @asm_Ew W p ++ R) (P ++ @asm_E W p ++ R).
Proof.
  intros LNR. unfold asm_covers. rewrite Forall_forall. intros [i s] Hin. cbn [fst snd].
  assert (Hf: find_id i (P ++ asm_E p ++ R) = Some s) by (apply initial_world.find_id_i; auto).
  rewrite !asm_find_id_app_eq in Hf |- *. unfold asm_Ew. rewrite asm_find_id_world.
  destruct (find_id i P) as [s0|].
  { injection Hf as <-. exists s0; split; [reflexivity | apply funspec_sub_refl]. }
  destruct (find_id i (asm_E p)) as [s1|] eqn:E1.
  2: { exists s; split; [exact Hf | apply funspec_sub_refl]. }
  injection Hf as <-. eexists; split; [reflexivity |].
  rewrite asm_env_world_eq. destruct (Pos.eqb i _nondet_bytes) eqn:Ej; cbn [snd]; [| apply funspec_sub_refl].
  apply Pos.eqb_eq in Ej. subst i.
  apply asm_find_id_In in E1. unfold asm_E in E1. apply filter_In in E1 as [E1 _].
  unfold asm_env.env_specs in E1.
  repeat destruct E1 as [E1|E1]; try contradiction;
    try (apply (f_equal fst) in E1; simpl in E1; vm_compute in E1; discriminate E1).
  apply (f_equal snd) in E1. unfold asm_env.nondet_bytes_spec in E1. cbn [snd] in E1. subst s1.
  apply asm_env.nondet_bytes_sub.
Qed.

Theorem asm_harness_safe (p: QP.program function) (OK: QPprogram_OK p) (W: compspecs)
  (HW: W = compspecs_of_QPcomposite_env (QP.prog_comp_env p) (proj2 OK))
  (CBC: forall H, cenv_built_correctly
                    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) []))
                    (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) = Errors.OK tt)
  (EXT_OK: all_unspecified_OK p)
  (post: (ident -> val) -> environ -> mpred)
  (Gr: funspecs) (ids: list ident)
  (IDS: map fst Gr = ids)
  (CHECK: asm_check W p ids = true)
  (CC: Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) Gr)
  (BODIES: asm_bodies W p ((QP.prog_main p, QPmain_spec_ext' p tt post) :: @asm_G0 W p Gr ids)
                          ((QP.prog_main p, QPmain_spec_ext' p tt post) :: Gr)) :
  harness_safe p.
Proof.
  subst W.
  set (W := compspecs_of_QPcomposite_env (QP.prog_comp_env p) (proj2 OK)).
  set (ms := QPmain_spec_ext' p tt post) in *.
  set (main := QP.prog_main p) in *.
  (* the bodies, proved with env_specs (asm_env.v), in the world's list: nondet_bytes_sub *)
  assert (BODIESw: asm_bodies W p ((main, ms) :: @asm_G0w W p Gr ids) ((main, ms) :: Gr)).
  { pose proof CHECK as CHK. unfold asm_check in CHK. rewrite !andb_true_iff in CHK.
    destruct CHK as [[[[[LNR0 FOK0] _] _] _] _].
    apply compute_list_norepet_e in LNR0. rewrite forallb_forall in FOK0.
    assert (MO: map fst (@asm_G0 W p Gr ids) = asm_E_ids p ++ ids ++ asm_vac_ids p (main :: ids)).
    { unfold asm_G0. rewrite !map_app, asm_E_ids_eq, asm_vac_ids_eq, IDS. reflexivity. }
    assert (MW: map fst (@asm_G0w W p Gr ids) = asm_E_ids p ++ ids ++ asm_vac_ids p (main :: ids)).
    { unfold asm_G0w. rewrite !map_app, asm_Ew_fst, asm_E_ids_eq, asm_vac_ids_eq, IDS. reflexivity. }
    assert (LNRo: list_norepet (map fst (QPvarspecs p) ++ map fst ((main, ms) :: @asm_G0 W p Gr ids))).
    { change (map fst ((main, ms) :: @asm_G0 W p Gr ids)) with (main :: map fst (@asm_G0 W p Gr ids)).
      rewrite MO. exact LNR0. }
    assert (LNRw: list_norepet (map fst (QPvarspecs p) ++ map fst ((main, ms) :: @asm_G0w W p Gr ids))).
    { change (map fst ((main, ms) :: @asm_G0w W p Gr ids)) with (main :: map fst (@asm_G0w W p Gr ids)).
      rewrite MW. exact LNR0. }
    assert (COV: asm_covers ((main, ms) :: @asm_G0w W p Gr ids) ((main, ms) :: @asm_G0 W p Gr ids)).
    { apply (asm_covers_world p [(main, ms)] (Gr ++ asm_vac p (main :: ids))).
      apply list_norepet_append_right in LNRo. exact LNRo. }
    unfold asm_bodies in BODIES |- *. rewrite Forall_forall in BODIES |- *. intros ip Hip.
    destruct (BODIES ip Hip) as [f [Hf SB]]. exists f; split; [exact Hf |].
    apply (@asm_body_lift W W (QPvarspecs p) (QPvarspecs p) ((main, ms) :: @asm_G0 W p Gr ids)
             ((main, ms) :: @asm_G0w W p Gr ids) f ip (cspecs_sub_refl)); auto.
    - apply asm_int_funs_In in Hf. apply FOK0 in Hf. simpl in Hf. unfold asm_fun_ok in Hf.
      rewrite !andb_true_iff in Hf. destruct Hf as [[[_ P2] _] _]. rewrite forallb_forall in P2.
      apply Forall_forall; intros; apply P2; auto.
    - apply Forall_forall. intros [i t] Hi. apply initial_world.find_id_i; [exact Hi |].
      apply list_norepet_append_left in LNRw. exact LNRw. }
  clear BODIES.
  set (G0 := @asm_G0w W p Gr ids) in *.
  unfold asm_check in CHECK.
  rewrite !andb_true_iff in CHECK.
  destruct CHECK as [[[[[LNR FOK] INT] EXT] ALIGNED] NB].
  apply compute_list_norepet_e in LNR.
  rewrite forallb_forall in FOK, INT, EXT.
  assert (MAPG0: map fst G0 = asm_E_ids p ++ ids ++ asm_vac_ids p (main :: ids)).
  { unfold G0, asm_G0w. rewrite !map_app, asm_Ew_fst, asm_E_ids_eq, asm_vac_ids_eq, IDS. reflexivity. }
  assert (NOMAIN: find_id main G0 = None).
  { apply assoclists.find_id_None_iff. rewrite MAPG0.
    apply list_norepet_app in LNR as [_ [LNR _]]. inv LNR. auto. }
  assert (GM: G_merge [(main, ms)] G0 = (main, ms) :: G0) by (apply asm_G_merge_single; auto).
  set (E := @asm_Ew W p) in *.
  set (GP := fun gv => InitGPred (Vardefs p) gv).
  set (G := G_merge [(main, ms)] G0).
  assert (LNR': list_norepet (map fst (QPvarspecs p) ++ map fst ((main, ms) :: G0))).
  { simpl map. rewrite MAPG0. exact LNR. }
  assert (LNRE: list_norepet (map fst E)).
  { unfold E; rewrite asm_Ew_fst, asm_E_ids_eq.
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
  { intros i H. unfold E in H; rewrite asm_Ew_fst, asm_E_ids_eq in H. unfold asm_E_ids in H.
    apply filter_In in H as [_ H]. unfold asm_present_ext, isSomeGfunExternal in H.
    destruct (Maps.PTree.get i (QP.prog_defs p)) as [[[?|? ? ? ?]|]|]; try discriminate; eauto. }
  assert (INT': forall i, In i (main :: ids) -> In i (map fst (asm_int_funs p))).
  { intros i H. apply INT in H. apply asm_is_internal_e in H as [f H].
    apply asm_int_funs_In in H. apply in_map with (f := fst) in H. exact H. }
  assert (F6: forall i, In i (IntIDs p ++ map fst E) <-> In i (map fst G)).
  { intros i. unfold G; rewrite GM. simpl map. rewrite MAPG0. unfold E; rewrite asm_Ew_fst, asm_E_ids_eq.
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
    2:{ intro; subst i. unfold E in H; rewrite asm_Ew_fst, asm_E_ids_eq in H.
        apply list_norepet_app in LNR as [_ [LNR _]]. inv LNR. apply H2. apply in_app; left; auto. }
    destruct (find_id i E) as [x|] eqn:E1.
    - unfold G0, asm_G0w. symmetry. apply asm_find_id_app_Some. exact E1.
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
    unfold G0, asm_G0w in Hf. apply asm_find_id_app in Hf as [Hf|[_ Hf]].
    - (* the external world *)
      apply asm_find_id_In in Hf. pose proof Hf as Hi.
      apply in_map with (f := fst) in Hi; simpl in Hi. fold E in Hi. unfold E in Hi; rewrite asm_Ew_fst, asm_E_ids_eq in Hi.
      apply asm_Ew_In in Hf.
      apply (env_SF _ _ _ _ _ _ Hf); auto.
      specialize (EXT i Hi). rewrite Hd in EXT.
      destruct fd as [|ef ts t cc]; try discriminate. destruct ef; try discriminate.
      destruct (env_fundef i) as [[|ef' ts' t' cc']|] eqn:EF; try discriminate.
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
(* 5. Glue for the law files.                                                                             *)

(* the whole list of funspecs of the component, main first *)
Definition asm_Gall {W: compspecs} (p: QP.program function) (post: (ident -> val) -> environ -> mpred)
    (Gr: funspecs) (ids: list ident) : funspecs :=
  (QP.prog_main p, QPmain_spec_ext' p tt post) :: @asm_G0 W p Gr ids.

Lemma asm_Gall_norepet (W: compspecs) p post Gr ids:
  map fst Gr = ids -> asm_check W p ids = true ->
  list_norepet (map fst (QPvarspecs p) ++ map fst (@asm_Gall W p post Gr ids)).
Proof.
  intros IDS CHECK. unfold asm_check in CHECK. rewrite !andb_true_iff in CHECK.
  destruct CHECK as [[[[[LNR _] _] _] _] _]. apply compute_list_norepet_e in LNR.
  unfold asm_Gall, asm_G0. simpl map. rewrite !map_app, asm_E_ids_eq, asm_vac_ids_eq, IDS. exact LNR.
Qed.

Lemma asm_Gall_norepet' (W: compspecs) p post Gr ids:
  map fst Gr = ids -> asm_check W p ids = true -> list_norepet (map fst (@asm_Gall W p post Gr ids)).
Proof. intros; eapply list_norepet_append_right, asm_Gall_norepet; eauto. Qed.

Lemma asm_Gr_incl (W: compspecs) p post Gr ids: incl Gr (@asm_Gall W p post Gr ids).
Proof. intros x H. right. unfold asm_G0. apply in_app; right; apply in_app; left; auto. Qed.

Lemma asm_E_incl (W: compspecs) p post Gr ids i s:
  In (i, s) (@asm_env.env_specs W) -> asm_present_ext p i = true -> In (i, s) (@asm_Gall W p post Gr ids).
Proof. intros H1 H2. right. unfold asm_G0. apply in_app; left. apply filter_In; auto. Qed.

Lemma asm_bodies_incl W p Gw L1 L2 L:
  asm_bodies W p Gw L1 -> asm_bodies W p Gw L2 -> incl L (L1 ++ L2) -> asm_bodies W p Gw L.
Proof.
  unfold asm_bodies; rewrite !Forall_forall; intros H1 H2 INC x Hx.
  apply INC, in_app in Hx as [Hx|Hx]; auto.
Qed.
