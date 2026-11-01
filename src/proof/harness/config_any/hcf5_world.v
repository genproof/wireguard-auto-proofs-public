(* law config_any: the world compspecs W_config_any of the whole program.  The contract links the same 14 units in the same order as the other protocol laws, so the chain up to
   link_Malloc is wg3_worlds.v's (proved on counter's copy).
   - W_config_any: the literal compspecs of the whole program (computes like a unit's compspecs);
   - W_config_any_eq: W = compspecs_of_QPcomposite_env (QP.prog_comp_env whole_prog) (proj2 OK)
     (what asm_lib.asm_harness_safe needs);
   - world_ok_config_any: wg3_worlds.world_ok (the harness's and every unit's compspecs are included);
   - hcf5_cs4_sub: cspecs_sub CS4 W (common4's body compspecs, hc4_piece_stmt's hypothesis), and CS4s. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require WgNoise.contracts.x_config_any.

Lemma world_OK_H_config_any : QPprogram_OK WgNoise.contracts.x_config_any.Harness.qp.
Proof. prove_unit_OK WgNoise.contracts.x_config_any.Harness.CS. Qed.
Lemma world_OK_whole_config_any : QPprogram_OK WgNoise.contracts.x_config_any.whole_prog.
Proof. link_OK WgNoise.contracts.x_config_any.Harness.qp WgNoise.contracts.x_counter.link_Malloc world_OK_H_config_any world_OK_link_Malloc. Qed.
Definition ce_config_any : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.x_config_any.whole_prog) in exact x).
Lemma OKce_config_any : QPcompspecs_OK ce_config_any. Proof. exact (proj2 world_OK_whole_config_any). Qed.
Definition W0_config_any : compspecs := compspecs_of_QPcomposite_env ce_config_any OKce_config_any.
Definition cenv_config_any : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_config_any) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_config_any : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_config_any) in exact x).
Definition la_config_any : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_config_any) in exact x).
Lemma cenv_config_any_eq : cenv_config_any = @cenv_cs W0_config_any.
Proof. unfold W0_config_any; destruct (QPcompspecs_OK_e _ OKce_config_any) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_config_any_eq : ha_config_any = @ha_env_cs W0_config_any.
Proof. unfold W0_config_any; destruct (QPcompspecs_OK_e _ OKce_config_any) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_config_any_eq : la_config_any = @la_env_cs W0_config_any.
Proof. unfold W0_config_any; destruct (QPcompspecs_OK_e _ OKce_config_any) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_config_any : composite_env_consistent cenv_config_any.
Proof. rewrite cenv_config_any_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_config_any : composite_env_legal_fieldlist cenv_config_any.
Proof. rewrite cenv_config_any_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_config_any : composite_env_complete_legal_cosu_type cenv_config_any.
Proof. rewrite cenv_config_any_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_config_any : hardware_alignof_env_consistent cenv_config_any ha_config_any.
Proof. rewrite cenv_config_any_eq, ha_config_any_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_config_any : hardware_alignof_env_complete cenv_config_any ha_config_any.
Proof. rewrite cenv_config_any_eq, ha_config_any_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_config_any : legal_alignas_env_consistent cenv_config_any ha_config_any la_config_any.
Proof. rewrite cenv_config_any_eq, ha_config_any_eq, la_config_any_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_config_any : legal_alignas_env_complete cenv_config_any la_config_any.
Proof. rewrite cenv_config_any_eq, la_config_any_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_config_any : legal_alignas_env_sound cenv_config_any ha_config_any la_config_any.
Proof. rewrite cenv_config_any_eq, ha_config_any_eq, la_config_any_eq; apply la_env_cs_sound. Qed.

Definition W_config_any : compspecs :=
  {| cenv_cs := cenv_config_any; cenv_consistent := cenv_consistent_config_any; cenv_legal_fieldlist := cenv_legal_fieldlist_config_any;
     cenv_legal_su := cenv_legal_su_config_any; ha_env_cs := ha_config_any; ha_env_cs_consistent := ha_env_consistent_config_any;
     ha_env_cs_complete := ha_env_complete_config_any; la_env_cs := la_config_any; la_env_cs_consistent := la_env_consistent_config_any;
     la_env_cs_complete := la_env_complete_config_any; la_env_cs_sound := la_env_sound_config_any |}.

Lemma W_config_any_eq : W_config_any = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.x_config_any.whole_prog) (proj2 world_OK_whole_config_any).
Proof.
transitivity W0_config_any.
- apply compspecs_ext; [apply cenv_config_any_eq | apply ha_config_any_eq | apply la_config_any_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.

Lemma world_ok_config_any : world_ok WgNoise.contracts.x_config_any.whole_prog WgNoise.contracts.x_config_any.Harness.CS W_config_any.
Proof.
exists world_OK_whole_config_any.
split; [apply W_config_any_eq | split].
- apply cenv_built_correctly_e; vm_refl.
- rewrite W_config_any_eq; repeat constructor; apply world_cspecs_sub; vm_refl.
Qed.

(* common4's body compspecs are included in the world *)
Lemma hcf5_cs4_sub : cspecs_sub CS4 W_config_any.
Proof. rewrite W_config_any_eq; apply world_cspecs_sub; vm_refl. Qed.
Lemma hcf5_cs4s_sub : cspecs_sub CS4s W_config_any.
Proof. rewrite W_config_any_eq; apply world_cspecs_sub; vm_refl. Qed.
