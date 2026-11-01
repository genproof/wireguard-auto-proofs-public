(* The worlds of the five replay-window laws (rp_): for each law, the compspecs of its whole program
   (harness/rp_<law>.c linked with patch/counter_validate.c only), built as the worlds of the x_ laws in
   wg3_worlds.v: W_rp_<law> computes like a unit's compspecs, equals the compspecs of the program's composite
   environment (what harness_safe needs, W_rp_<law>_eq), and includes the harness's and Counter's compspecs
   (world_ok_rp_<law>), so that counter_validate's body proofs in Counter.CS lift into the law. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require WgNoise.contracts.rp_any_order.
Require WgNoise.contracts.rp_duplicate.
Require WgNoise.contracts.rp_fresh.
Require WgNoise.contracts.rp_limit.
Require WgNoise.contracts.rp_too_old.

(* a world of an rp_ law: the program, its composite environment, and the harness's and Counter's compspecs
   included in it *)
Definition rp_world_ok (p: QP.program function) (Hcs: compspecs) (W: compspecs) : Prop :=
  exists OK: QPprogram_OK p,
    W = compspecs_of_QPcomposite_env (QP.prog_comp_env p) (proj2 OK) /\
    build_composite_env
      (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) [])) =
    Errors.OK (composite_env_of_QPcomposite_env (QP.prog_comp_env p) (projT1 (proj2 OK))) /\
    Forall (fun cs => cspecs_sub cs W) [Hcs; Counter.CS].

(* ---------- rp_any_order ---------- *)
Lemma world_OK_H_rp_any_order : QPprogram_OK WgNoise.contracts.rp_any_order.Harness.qp. Proof. prove_unit_OK WgNoise.contracts.rp_any_order.Harness.CS. Qed.
Lemma world_OK_whole_rp_any_order : QPprogram_OK WgNoise.contracts.rp_any_order.whole_prog.
Proof. link_OK WgNoise.contracts.rp_any_order.Harness.qp Counter.qp world_OK_H_rp_any_order world_OK_Counter. Qed.
Definition ce_rp_any_order : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.rp_any_order.whole_prog) in exact x).
Lemma OKce_rp_any_order : QPcompspecs_OK ce_rp_any_order. Proof. exact (proj2 world_OK_whole_rp_any_order). Qed.
Definition W0_rp_any_order : compspecs := compspecs_of_QPcomposite_env ce_rp_any_order OKce_rp_any_order.
Definition cenv_rp_any_order : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_rp_any_order) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_rp_any_order : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_rp_any_order) in exact x).
Definition la_rp_any_order : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_rp_any_order) in exact x).
Lemma cenv_rp_any_order_eq : cenv_rp_any_order = @cenv_cs W0_rp_any_order.
Proof. unfold W0_rp_any_order; destruct (QPcompspecs_OK_e _ OKce_rp_any_order) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_rp_any_order_eq : ha_rp_any_order = @ha_env_cs W0_rp_any_order.
Proof. unfold W0_rp_any_order; destruct (QPcompspecs_OK_e _ OKce_rp_any_order) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_rp_any_order_eq : la_rp_any_order = @la_env_cs W0_rp_any_order.
Proof. unfold W0_rp_any_order; destruct (QPcompspecs_OK_e _ OKce_rp_any_order) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_rp_any_order : composite_env_consistent cenv_rp_any_order.
Proof. rewrite cenv_rp_any_order_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_rp_any_order : composite_env_legal_fieldlist cenv_rp_any_order.
Proof. rewrite cenv_rp_any_order_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_rp_any_order : composite_env_complete_legal_cosu_type cenv_rp_any_order.
Proof. rewrite cenv_rp_any_order_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_rp_any_order : hardware_alignof_env_consistent cenv_rp_any_order ha_rp_any_order.
Proof. rewrite cenv_rp_any_order_eq, ha_rp_any_order_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_rp_any_order : hardware_alignof_env_complete cenv_rp_any_order ha_rp_any_order.
Proof. rewrite cenv_rp_any_order_eq, ha_rp_any_order_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_rp_any_order : legal_alignas_env_consistent cenv_rp_any_order ha_rp_any_order la_rp_any_order.
Proof. rewrite cenv_rp_any_order_eq, ha_rp_any_order_eq, la_rp_any_order_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_rp_any_order : legal_alignas_env_complete cenv_rp_any_order la_rp_any_order.
Proof. rewrite cenv_rp_any_order_eq, la_rp_any_order_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_rp_any_order : legal_alignas_env_sound cenv_rp_any_order ha_rp_any_order la_rp_any_order.
Proof. rewrite cenv_rp_any_order_eq, ha_rp_any_order_eq, la_rp_any_order_eq; apply la_env_cs_sound. Qed.
Definition W_rp_any_order : compspecs :=
  {| cenv_cs := cenv_rp_any_order; cenv_consistent := cenv_consistent_rp_any_order; cenv_legal_fieldlist := cenv_legal_fieldlist_rp_any_order;
     cenv_legal_su := cenv_legal_su_rp_any_order; ha_env_cs := ha_rp_any_order; ha_env_cs_consistent := ha_env_consistent_rp_any_order;
     ha_env_cs_complete := ha_env_complete_rp_any_order; la_env_cs := la_rp_any_order; la_env_cs_consistent := la_env_consistent_rp_any_order;
     la_env_cs_complete := la_env_complete_rp_any_order; la_env_cs_sound := la_env_sound_rp_any_order |}.
Lemma W_rp_any_order_eq : W_rp_any_order = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.rp_any_order.whole_prog) (proj2 world_OK_whole_rp_any_order).
Proof.
transitivity W0_rp_any_order.
- apply compspecs_ext; [apply cenv_rp_any_order_eq | apply ha_rp_any_order_eq | apply la_rp_any_order_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.
Lemma world_ok_rp_any_order : rp_world_ok WgNoise.contracts.rp_any_order.whole_prog WgNoise.contracts.rp_any_order.Harness.CS W_rp_any_order.
Proof.
exists world_OK_whole_rp_any_order.
split; [apply W_rp_any_order_eq | split].
- apply cenv_built_correctly_e; vm_refl.
- rewrite W_rp_any_order_eq; repeat constructor; apply world_cspecs_sub; vm_refl.
Qed.

(* ---------- rp_duplicate ---------- *)
Lemma world_OK_H_rp_duplicate : QPprogram_OK WgNoise.contracts.rp_duplicate.Harness.qp. Proof. prove_unit_OK WgNoise.contracts.rp_duplicate.Harness.CS. Qed.
Lemma world_OK_whole_rp_duplicate : QPprogram_OK WgNoise.contracts.rp_duplicate.whole_prog.
Proof. link_OK WgNoise.contracts.rp_duplicate.Harness.qp Counter.qp world_OK_H_rp_duplicate world_OK_Counter. Qed.
Definition ce_rp_duplicate : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.rp_duplicate.whole_prog) in exact x).
Lemma OKce_rp_duplicate : QPcompspecs_OK ce_rp_duplicate. Proof. exact (proj2 world_OK_whole_rp_duplicate). Qed.
Definition W0_rp_duplicate : compspecs := compspecs_of_QPcomposite_env ce_rp_duplicate OKce_rp_duplicate.
Definition cenv_rp_duplicate : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_rp_duplicate) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_rp_duplicate : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_rp_duplicate) in exact x).
Definition la_rp_duplicate : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_rp_duplicate) in exact x).
Lemma cenv_rp_duplicate_eq : cenv_rp_duplicate = @cenv_cs W0_rp_duplicate.
Proof. unfold W0_rp_duplicate; destruct (QPcompspecs_OK_e _ OKce_rp_duplicate) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_rp_duplicate_eq : ha_rp_duplicate = @ha_env_cs W0_rp_duplicate.
Proof. unfold W0_rp_duplicate; destruct (QPcompspecs_OK_e _ OKce_rp_duplicate) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_rp_duplicate_eq : la_rp_duplicate = @la_env_cs W0_rp_duplicate.
Proof. unfold W0_rp_duplicate; destruct (QPcompspecs_OK_e _ OKce_rp_duplicate) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_rp_duplicate : composite_env_consistent cenv_rp_duplicate.
Proof. rewrite cenv_rp_duplicate_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_rp_duplicate : composite_env_legal_fieldlist cenv_rp_duplicate.
Proof. rewrite cenv_rp_duplicate_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_rp_duplicate : composite_env_complete_legal_cosu_type cenv_rp_duplicate.
Proof. rewrite cenv_rp_duplicate_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_rp_duplicate : hardware_alignof_env_consistent cenv_rp_duplicate ha_rp_duplicate.
Proof. rewrite cenv_rp_duplicate_eq, ha_rp_duplicate_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_rp_duplicate : hardware_alignof_env_complete cenv_rp_duplicate ha_rp_duplicate.
Proof. rewrite cenv_rp_duplicate_eq, ha_rp_duplicate_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_rp_duplicate : legal_alignas_env_consistent cenv_rp_duplicate ha_rp_duplicate la_rp_duplicate.
Proof. rewrite cenv_rp_duplicate_eq, ha_rp_duplicate_eq, la_rp_duplicate_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_rp_duplicate : legal_alignas_env_complete cenv_rp_duplicate la_rp_duplicate.
Proof. rewrite cenv_rp_duplicate_eq, la_rp_duplicate_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_rp_duplicate : legal_alignas_env_sound cenv_rp_duplicate ha_rp_duplicate la_rp_duplicate.
Proof. rewrite cenv_rp_duplicate_eq, ha_rp_duplicate_eq, la_rp_duplicate_eq; apply la_env_cs_sound. Qed.
Definition W_rp_duplicate : compspecs :=
  {| cenv_cs := cenv_rp_duplicate; cenv_consistent := cenv_consistent_rp_duplicate; cenv_legal_fieldlist := cenv_legal_fieldlist_rp_duplicate;
     cenv_legal_su := cenv_legal_su_rp_duplicate; ha_env_cs := ha_rp_duplicate; ha_env_cs_consistent := ha_env_consistent_rp_duplicate;
     ha_env_cs_complete := ha_env_complete_rp_duplicate; la_env_cs := la_rp_duplicate; la_env_cs_consistent := la_env_consistent_rp_duplicate;
     la_env_cs_complete := la_env_complete_rp_duplicate; la_env_cs_sound := la_env_sound_rp_duplicate |}.
Lemma W_rp_duplicate_eq : W_rp_duplicate = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.rp_duplicate.whole_prog) (proj2 world_OK_whole_rp_duplicate).
Proof.
transitivity W0_rp_duplicate.
- apply compspecs_ext; [apply cenv_rp_duplicate_eq | apply ha_rp_duplicate_eq | apply la_rp_duplicate_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.
Lemma world_ok_rp_duplicate : rp_world_ok WgNoise.contracts.rp_duplicate.whole_prog WgNoise.contracts.rp_duplicate.Harness.CS W_rp_duplicate.
Proof.
exists world_OK_whole_rp_duplicate.
split; [apply W_rp_duplicate_eq | split].
- apply cenv_built_correctly_e; vm_refl.
- rewrite W_rp_duplicate_eq; repeat constructor; apply world_cspecs_sub; vm_refl.
Qed.

(* ---------- rp_fresh ---------- *)
Lemma world_OK_H_rp_fresh : QPprogram_OK WgNoise.contracts.rp_fresh.Harness.qp. Proof. prove_unit_OK WgNoise.contracts.rp_fresh.Harness.CS. Qed.
Lemma world_OK_whole_rp_fresh : QPprogram_OK WgNoise.contracts.rp_fresh.whole_prog.
Proof. link_OK WgNoise.contracts.rp_fresh.Harness.qp Counter.qp world_OK_H_rp_fresh world_OK_Counter. Qed.
Definition ce_rp_fresh : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.rp_fresh.whole_prog) in exact x).
Lemma OKce_rp_fresh : QPcompspecs_OK ce_rp_fresh. Proof. exact (proj2 world_OK_whole_rp_fresh). Qed.
Definition W0_rp_fresh : compspecs := compspecs_of_QPcomposite_env ce_rp_fresh OKce_rp_fresh.
Definition cenv_rp_fresh : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_rp_fresh) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_rp_fresh : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_rp_fresh) in exact x).
Definition la_rp_fresh : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_rp_fresh) in exact x).
Lemma cenv_rp_fresh_eq : cenv_rp_fresh = @cenv_cs W0_rp_fresh.
Proof. unfold W0_rp_fresh; destruct (QPcompspecs_OK_e _ OKce_rp_fresh) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_rp_fresh_eq : ha_rp_fresh = @ha_env_cs W0_rp_fresh.
Proof. unfold W0_rp_fresh; destruct (QPcompspecs_OK_e _ OKce_rp_fresh) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_rp_fresh_eq : la_rp_fresh = @la_env_cs W0_rp_fresh.
Proof. unfold W0_rp_fresh; destruct (QPcompspecs_OK_e _ OKce_rp_fresh) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_rp_fresh : composite_env_consistent cenv_rp_fresh.
Proof. rewrite cenv_rp_fresh_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_rp_fresh : composite_env_legal_fieldlist cenv_rp_fresh.
Proof. rewrite cenv_rp_fresh_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_rp_fresh : composite_env_complete_legal_cosu_type cenv_rp_fresh.
Proof. rewrite cenv_rp_fresh_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_rp_fresh : hardware_alignof_env_consistent cenv_rp_fresh ha_rp_fresh.
Proof. rewrite cenv_rp_fresh_eq, ha_rp_fresh_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_rp_fresh : hardware_alignof_env_complete cenv_rp_fresh ha_rp_fresh.
Proof. rewrite cenv_rp_fresh_eq, ha_rp_fresh_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_rp_fresh : legal_alignas_env_consistent cenv_rp_fresh ha_rp_fresh la_rp_fresh.
Proof. rewrite cenv_rp_fresh_eq, ha_rp_fresh_eq, la_rp_fresh_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_rp_fresh : legal_alignas_env_complete cenv_rp_fresh la_rp_fresh.
Proof. rewrite cenv_rp_fresh_eq, la_rp_fresh_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_rp_fresh : legal_alignas_env_sound cenv_rp_fresh ha_rp_fresh la_rp_fresh.
Proof. rewrite cenv_rp_fresh_eq, ha_rp_fresh_eq, la_rp_fresh_eq; apply la_env_cs_sound. Qed.
Definition W_rp_fresh : compspecs :=
  {| cenv_cs := cenv_rp_fresh; cenv_consistent := cenv_consistent_rp_fresh; cenv_legal_fieldlist := cenv_legal_fieldlist_rp_fresh;
     cenv_legal_su := cenv_legal_su_rp_fresh; ha_env_cs := ha_rp_fresh; ha_env_cs_consistent := ha_env_consistent_rp_fresh;
     ha_env_cs_complete := ha_env_complete_rp_fresh; la_env_cs := la_rp_fresh; la_env_cs_consistent := la_env_consistent_rp_fresh;
     la_env_cs_complete := la_env_complete_rp_fresh; la_env_cs_sound := la_env_sound_rp_fresh |}.
Lemma W_rp_fresh_eq : W_rp_fresh = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.rp_fresh.whole_prog) (proj2 world_OK_whole_rp_fresh).
Proof.
transitivity W0_rp_fresh.
- apply compspecs_ext; [apply cenv_rp_fresh_eq | apply ha_rp_fresh_eq | apply la_rp_fresh_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.
Lemma world_ok_rp_fresh : rp_world_ok WgNoise.contracts.rp_fresh.whole_prog WgNoise.contracts.rp_fresh.Harness.CS W_rp_fresh.
Proof.
exists world_OK_whole_rp_fresh.
split; [apply W_rp_fresh_eq | split].
- apply cenv_built_correctly_e; vm_refl.
- rewrite W_rp_fresh_eq; repeat constructor; apply world_cspecs_sub; vm_refl.
Qed.

(* ---------- rp_limit ---------- *)
Lemma world_OK_H_rp_limit : QPprogram_OK WgNoise.contracts.rp_limit.Harness.qp. Proof. prove_unit_OK WgNoise.contracts.rp_limit.Harness.CS. Qed.
Lemma world_OK_whole_rp_limit : QPprogram_OK WgNoise.contracts.rp_limit.whole_prog.
Proof. link_OK WgNoise.contracts.rp_limit.Harness.qp Counter.qp world_OK_H_rp_limit world_OK_Counter. Qed.
Definition ce_rp_limit : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.rp_limit.whole_prog) in exact x).
Lemma OKce_rp_limit : QPcompspecs_OK ce_rp_limit. Proof. exact (proj2 world_OK_whole_rp_limit). Qed.
Definition W0_rp_limit : compspecs := compspecs_of_QPcomposite_env ce_rp_limit OKce_rp_limit.
Definition cenv_rp_limit : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_rp_limit) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_rp_limit : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_rp_limit) in exact x).
Definition la_rp_limit : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_rp_limit) in exact x).
Lemma cenv_rp_limit_eq : cenv_rp_limit = @cenv_cs W0_rp_limit.
Proof. unfold W0_rp_limit; destruct (QPcompspecs_OK_e _ OKce_rp_limit) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_rp_limit_eq : ha_rp_limit = @ha_env_cs W0_rp_limit.
Proof. unfold W0_rp_limit; destruct (QPcompspecs_OK_e _ OKce_rp_limit) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_rp_limit_eq : la_rp_limit = @la_env_cs W0_rp_limit.
Proof. unfold W0_rp_limit; destruct (QPcompspecs_OK_e _ OKce_rp_limit) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_rp_limit : composite_env_consistent cenv_rp_limit.
Proof. rewrite cenv_rp_limit_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_rp_limit : composite_env_legal_fieldlist cenv_rp_limit.
Proof. rewrite cenv_rp_limit_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_rp_limit : composite_env_complete_legal_cosu_type cenv_rp_limit.
Proof. rewrite cenv_rp_limit_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_rp_limit : hardware_alignof_env_consistent cenv_rp_limit ha_rp_limit.
Proof. rewrite cenv_rp_limit_eq, ha_rp_limit_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_rp_limit : hardware_alignof_env_complete cenv_rp_limit ha_rp_limit.
Proof. rewrite cenv_rp_limit_eq, ha_rp_limit_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_rp_limit : legal_alignas_env_consistent cenv_rp_limit ha_rp_limit la_rp_limit.
Proof. rewrite cenv_rp_limit_eq, ha_rp_limit_eq, la_rp_limit_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_rp_limit : legal_alignas_env_complete cenv_rp_limit la_rp_limit.
Proof. rewrite cenv_rp_limit_eq, la_rp_limit_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_rp_limit : legal_alignas_env_sound cenv_rp_limit ha_rp_limit la_rp_limit.
Proof. rewrite cenv_rp_limit_eq, ha_rp_limit_eq, la_rp_limit_eq; apply la_env_cs_sound. Qed.
Definition W_rp_limit : compspecs :=
  {| cenv_cs := cenv_rp_limit; cenv_consistent := cenv_consistent_rp_limit; cenv_legal_fieldlist := cenv_legal_fieldlist_rp_limit;
     cenv_legal_su := cenv_legal_su_rp_limit; ha_env_cs := ha_rp_limit; ha_env_cs_consistent := ha_env_consistent_rp_limit;
     ha_env_cs_complete := ha_env_complete_rp_limit; la_env_cs := la_rp_limit; la_env_cs_consistent := la_env_consistent_rp_limit;
     la_env_cs_complete := la_env_complete_rp_limit; la_env_cs_sound := la_env_sound_rp_limit |}.
Lemma W_rp_limit_eq : W_rp_limit = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.rp_limit.whole_prog) (proj2 world_OK_whole_rp_limit).
Proof.
transitivity W0_rp_limit.
- apply compspecs_ext; [apply cenv_rp_limit_eq | apply ha_rp_limit_eq | apply la_rp_limit_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.
Lemma world_ok_rp_limit : rp_world_ok WgNoise.contracts.rp_limit.whole_prog WgNoise.contracts.rp_limit.Harness.CS W_rp_limit.
Proof.
exists world_OK_whole_rp_limit.
split; [apply W_rp_limit_eq | split].
- apply cenv_built_correctly_e; vm_refl.
- rewrite W_rp_limit_eq; repeat constructor; apply world_cspecs_sub; vm_refl.
Qed.

(* ---------- rp_too_old ---------- *)
Lemma world_OK_H_rp_too_old : QPprogram_OK WgNoise.contracts.rp_too_old.Harness.qp. Proof. prove_unit_OK WgNoise.contracts.rp_too_old.Harness.CS. Qed.
Lemma world_OK_whole_rp_too_old : QPprogram_OK WgNoise.contracts.rp_too_old.whole_prog.
Proof. link_OK WgNoise.contracts.rp_too_old.Harness.qp Counter.qp world_OK_H_rp_too_old world_OK_Counter. Qed.
Definition ce_rp_too_old : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.rp_too_old.whole_prog) in exact x).
Lemma OKce_rp_too_old : QPcompspecs_OK ce_rp_too_old. Proof. exact (proj2 world_OK_whole_rp_too_old). Qed.
Definition W0_rp_too_old : compspecs := compspecs_of_QPcomposite_env ce_rp_too_old OKce_rp_too_old.
Definition cenv_rp_too_old : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_rp_too_old) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_rp_too_old : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_rp_too_old) in exact x).
Definition la_rp_too_old : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_rp_too_old) in exact x).
Lemma cenv_rp_too_old_eq : cenv_rp_too_old = @cenv_cs W0_rp_too_old.
Proof. unfold W0_rp_too_old; destruct (QPcompspecs_OK_e _ OKce_rp_too_old) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_rp_too_old_eq : ha_rp_too_old = @ha_env_cs W0_rp_too_old.
Proof. unfold W0_rp_too_old; destruct (QPcompspecs_OK_e _ OKce_rp_too_old) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_rp_too_old_eq : la_rp_too_old = @la_env_cs W0_rp_too_old.
Proof. unfold W0_rp_too_old; destruct (QPcompspecs_OK_e _ OKce_rp_too_old) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_rp_too_old : composite_env_consistent cenv_rp_too_old.
Proof. rewrite cenv_rp_too_old_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_rp_too_old : composite_env_legal_fieldlist cenv_rp_too_old.
Proof. rewrite cenv_rp_too_old_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_rp_too_old : composite_env_complete_legal_cosu_type cenv_rp_too_old.
Proof. rewrite cenv_rp_too_old_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_rp_too_old : hardware_alignof_env_consistent cenv_rp_too_old ha_rp_too_old.
Proof. rewrite cenv_rp_too_old_eq, ha_rp_too_old_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_rp_too_old : hardware_alignof_env_complete cenv_rp_too_old ha_rp_too_old.
Proof. rewrite cenv_rp_too_old_eq, ha_rp_too_old_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_rp_too_old : legal_alignas_env_consistent cenv_rp_too_old ha_rp_too_old la_rp_too_old.
Proof. rewrite cenv_rp_too_old_eq, ha_rp_too_old_eq, la_rp_too_old_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_rp_too_old : legal_alignas_env_complete cenv_rp_too_old la_rp_too_old.
Proof. rewrite cenv_rp_too_old_eq, la_rp_too_old_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_rp_too_old : legal_alignas_env_sound cenv_rp_too_old ha_rp_too_old la_rp_too_old.
Proof. rewrite cenv_rp_too_old_eq, ha_rp_too_old_eq, la_rp_too_old_eq; apply la_env_cs_sound. Qed.
Definition W_rp_too_old : compspecs :=
  {| cenv_cs := cenv_rp_too_old; cenv_consistent := cenv_consistent_rp_too_old; cenv_legal_fieldlist := cenv_legal_fieldlist_rp_too_old;
     cenv_legal_su := cenv_legal_su_rp_too_old; ha_env_cs := ha_rp_too_old; ha_env_cs_consistent := ha_env_consistent_rp_too_old;
     ha_env_cs_complete := ha_env_complete_rp_too_old; la_env_cs := la_rp_too_old; la_env_cs_consistent := la_env_consistent_rp_too_old;
     la_env_cs_complete := la_env_complete_rp_too_old; la_env_cs_sound := la_env_sound_rp_too_old |}.
Lemma W_rp_too_old_eq : W_rp_too_old = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.rp_too_old.whole_prog) (proj2 world_OK_whole_rp_too_old).
Proof.
transitivity W0_rp_too_old.
- apply compspecs_ext; [apply cenv_rp_too_old_eq | apply ha_rp_too_old_eq | apply la_rp_too_old_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.
Lemma world_ok_rp_too_old : rp_world_ok WgNoise.contracts.rp_too_old.whole_prog WgNoise.contracts.rp_too_old.Harness.CS W_rp_too_old.
Proof.
exists world_OK_whole_rp_too_old.
split; [apply W_rp_too_old_eq | split].
- apply cenv_built_correctly_e; vm_refl.
- rewrite W_rp_too_old_eq; repeat constructor; apply world_cspecs_sub; vm_refl.
Qed.
