(* The world of law ae_split_poly1305: the compspecs of its whole program (harness/ae_split_poly1305.c linked with
   poly1305.c, poly1305-donna32.c and libc.c), built as the worlds of the x_ laws in wg3_worlds.v: W_asp computes
   like a unit's compspecs, equals the compspecs of the program's composite environment (what harness_safe needs,
   W_asp_eq), and includes the harness's and the three units' compspecs (world_ok_asp), so that bodies proved in
   those units lift into the law. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require WgNoise.contracts.ae_split_poly1305.

(* the program, its composite environment, and the compspecs of the harness and of its units included in it *)
Definition asp_world_ok (p: QP.program function) (W: compspecs) : Prop :=
  exists OK: QPprogram_OK p,
    W = compspecs_of_QPcomposite_env (QP.prog_comp_env p) (proj2 OK) /\
    build_composite_env
      (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) [])) =
    Errors.OK (composite_env_of_QPcomposite_env (QP.prog_comp_env p) (projT1 (proj2 OK))) /\
    Forall (fun cs => cspecs_sub cs W) [WgNoise.contracts.ae_split_poly1305.Harness.CS; Poly1305.CS; Poly1305Donna32.CS; Libc.CS].

Lemma world_OK_H_asp : QPprogram_OK WgNoise.contracts.ae_split_poly1305.Harness.qp. Proof. prove_unit_OK WgNoise.contracts.ae_split_poly1305.Harness.CS. Qed.
Lemma world_OK_link_Donna32_asp : QPprogram_OK WgNoise.contracts.ae_split_poly1305.link_Poly1305Donna32.
Proof. link_OK Poly1305Donna32.qp Poly1305.qp world_OK_Poly1305Donna32 world_OK_Poly1305. Qed.
Lemma world_OK_link_Libc_asp : QPprogram_OK WgNoise.contracts.ae_split_poly1305.link_Libc.
Proof. link_OK Libc.qp WgNoise.contracts.ae_split_poly1305.link_Poly1305Donna32 world_OK_Libc world_OK_link_Donna32_asp. Qed.
Lemma world_OK_whole_asp : QPprogram_OK WgNoise.contracts.ae_split_poly1305.whole_prog.
Proof. link_OK WgNoise.contracts.ae_split_poly1305.Harness.qp WgNoise.contracts.ae_split_poly1305.link_Libc world_OK_H_asp world_OK_link_Libc_asp. Qed.
Definition ce_asp : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.ae_split_poly1305.whole_prog) in exact x).
Lemma OKce_asp : QPcompspecs_OK ce_asp. Proof. exact (proj2 world_OK_whole_asp). Qed.
Definition W0_asp : compspecs := compspecs_of_QPcomposite_env ce_asp OKce_asp.
Definition cenv_asp : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_asp) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_asp : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_asp) in exact x).
Definition la_asp : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_asp) in exact x).
Lemma cenv_asp_eq : cenv_asp = @cenv_cs W0_asp.
Proof. unfold W0_asp; destruct (QPcompspecs_OK_e _ OKce_asp) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_asp_eq : ha_asp = @ha_env_cs W0_asp.
Proof. unfold W0_asp; destruct (QPcompspecs_OK_e _ OKce_asp) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_asp_eq : la_asp = @la_env_cs W0_asp.
Proof. unfold W0_asp; destruct (QPcompspecs_OK_e _ OKce_asp) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_asp : composite_env_consistent cenv_asp.
Proof. rewrite cenv_asp_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_asp : composite_env_legal_fieldlist cenv_asp.
Proof. rewrite cenv_asp_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_asp : composite_env_complete_legal_cosu_type cenv_asp.
Proof. rewrite cenv_asp_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_asp : hardware_alignof_env_consistent cenv_asp ha_asp.
Proof. rewrite cenv_asp_eq, ha_asp_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_asp : hardware_alignof_env_complete cenv_asp ha_asp.
Proof. rewrite cenv_asp_eq, ha_asp_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_asp : legal_alignas_env_consistent cenv_asp ha_asp la_asp.
Proof. rewrite cenv_asp_eq, ha_asp_eq, la_asp_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_asp : legal_alignas_env_complete cenv_asp la_asp.
Proof. rewrite cenv_asp_eq, la_asp_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_asp : legal_alignas_env_sound cenv_asp ha_asp la_asp.
Proof. rewrite cenv_asp_eq, ha_asp_eq, la_asp_eq; apply la_env_cs_sound. Qed.
Definition W_asp : compspecs :=
  {| cenv_cs := cenv_asp; cenv_consistent := cenv_consistent_asp; cenv_legal_fieldlist := cenv_legal_fieldlist_asp;
     cenv_legal_su := cenv_legal_su_asp; ha_env_cs := ha_asp; ha_env_cs_consistent := ha_env_consistent_asp;
     ha_env_cs_complete := ha_env_complete_asp; la_env_cs := la_asp; la_env_cs_consistent := la_env_consistent_asp;
     la_env_cs_complete := la_env_complete_asp; la_env_cs_sound := la_env_sound_asp |}.
Lemma W_asp_eq : W_asp = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.ae_split_poly1305.whole_prog) (proj2 world_OK_whole_asp).
Proof.
transitivity W0_asp.
- apply compspecs_ext; [apply cenv_asp_eq | apply ha_asp_eq | apply la_asp_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.
Lemma world_ok_asp : asp_world_ok WgNoise.contracts.ae_split_poly1305.whole_prog W_asp.
Proof.
exists world_OK_whole_asp.
split; [apply W_asp_eq | split].
- apply cenv_built_correctly_e; vm_refl.
- rewrite W_asp_eq; repeat constructor; apply world_cspecs_sub; vm_refl.
Qed.
