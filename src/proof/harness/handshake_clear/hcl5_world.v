(* law handshake_clear: the world compspecs W_handshake_clear of the whole program.  The contract links the same 14 units in the same order as the other protocol laws, so the chain up to
   link_Malloc is wg3_worlds.v's (proved on counter's copy).
   - W_handshake_clear: the literal compspecs of the whole program (computes like a unit's compspecs);
   - W_handshake_clear_eq: W = compspecs_of_QPcomposite_env (QP.prog_comp_env whole_prog) (proj2 OK)
     (what asm_lib.asm_harness_safe needs);
   - world_ok_handshake_clear: wg3_worlds.world_ok (the harness's and every unit's compspecs are included);
   - hcl5_cs4_sub: cspecs_sub CS4 W (common4's body compspecs, hc4_piece_stmt's hypothesis), and CS4s. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require WgNoise.contracts.x_handshake_clear.

Lemma world_OK_H_handshake_clear : QPprogram_OK WgNoise.contracts.x_handshake_clear.Harness.qp.
Proof. prove_unit_OK WgNoise.contracts.x_handshake_clear.Harness.CS. Qed.
Lemma world_OK_whole_handshake_clear : QPprogram_OK WgNoise.contracts.x_handshake_clear.whole_prog.
Proof. link_OK WgNoise.contracts.x_handshake_clear.Harness.qp WgNoise.contracts.x_counter.link_Malloc world_OK_H_handshake_clear world_OK_link_Malloc. Qed.
Definition ce_handshake_clear : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.x_handshake_clear.whole_prog) in exact x).
Lemma OKce_handshake_clear : QPcompspecs_OK ce_handshake_clear. Proof. exact (proj2 world_OK_whole_handshake_clear). Qed.
Definition W0_handshake_clear : compspecs := compspecs_of_QPcomposite_env ce_handshake_clear OKce_handshake_clear.
Definition cenv_handshake_clear : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_handshake_clear) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_handshake_clear : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_handshake_clear) in exact x).
Definition la_handshake_clear : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_handshake_clear) in exact x).
Lemma cenv_handshake_clear_eq : cenv_handshake_clear = @cenv_cs W0_handshake_clear.
Proof. unfold W0_handshake_clear; destruct (QPcompspecs_OK_e _ OKce_handshake_clear) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_handshake_clear_eq : ha_handshake_clear = @ha_env_cs W0_handshake_clear.
Proof. unfold W0_handshake_clear; destruct (QPcompspecs_OK_e _ OKce_handshake_clear) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_handshake_clear_eq : la_handshake_clear = @la_env_cs W0_handshake_clear.
Proof. unfold W0_handshake_clear; destruct (QPcompspecs_OK_e _ OKce_handshake_clear) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_handshake_clear : composite_env_consistent cenv_handshake_clear.
Proof. rewrite cenv_handshake_clear_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_handshake_clear : composite_env_legal_fieldlist cenv_handshake_clear.
Proof. rewrite cenv_handshake_clear_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_handshake_clear : composite_env_complete_legal_cosu_type cenv_handshake_clear.
Proof. rewrite cenv_handshake_clear_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_handshake_clear : hardware_alignof_env_consistent cenv_handshake_clear ha_handshake_clear.
Proof. rewrite cenv_handshake_clear_eq, ha_handshake_clear_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_handshake_clear : hardware_alignof_env_complete cenv_handshake_clear ha_handshake_clear.
Proof. rewrite cenv_handshake_clear_eq, ha_handshake_clear_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_handshake_clear : legal_alignas_env_consistent cenv_handshake_clear ha_handshake_clear la_handshake_clear.
Proof. rewrite cenv_handshake_clear_eq, ha_handshake_clear_eq, la_handshake_clear_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_handshake_clear : legal_alignas_env_complete cenv_handshake_clear la_handshake_clear.
Proof. rewrite cenv_handshake_clear_eq, la_handshake_clear_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_handshake_clear : legal_alignas_env_sound cenv_handshake_clear ha_handshake_clear la_handshake_clear.
Proof. rewrite cenv_handshake_clear_eq, ha_handshake_clear_eq, la_handshake_clear_eq; apply la_env_cs_sound. Qed.

Definition W_handshake_clear : compspecs :=
  {| cenv_cs := cenv_handshake_clear; cenv_consistent := cenv_consistent_handshake_clear; cenv_legal_fieldlist := cenv_legal_fieldlist_handshake_clear;
     cenv_legal_su := cenv_legal_su_handshake_clear; ha_env_cs := ha_handshake_clear; ha_env_cs_consistent := ha_env_consistent_handshake_clear;
     ha_env_cs_complete := ha_env_complete_handshake_clear; la_env_cs := la_handshake_clear; la_env_cs_consistent := la_env_consistent_handshake_clear;
     la_env_cs_complete := la_env_complete_handshake_clear; la_env_cs_sound := la_env_sound_handshake_clear |}.

Lemma W_handshake_clear_eq : W_handshake_clear = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.x_handshake_clear.whole_prog) (proj2 world_OK_whole_handshake_clear).
Proof.
transitivity W0_handshake_clear.
- apply compspecs_ext; [apply cenv_handshake_clear_eq | apply ha_handshake_clear_eq | apply la_handshake_clear_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.

Lemma world_ok_handshake_clear : world_ok WgNoise.contracts.x_handshake_clear.whole_prog WgNoise.contracts.x_handshake_clear.Harness.CS W_handshake_clear.
Proof.
exists world_OK_whole_handshake_clear.
split; [apply W_handshake_clear_eq | split].
- apply cenv_built_correctly_e; vm_refl.
- rewrite W_handshake_clear_eq; repeat constructor; apply world_cspecs_sub; vm_refl.
Qed.

(* common4's body compspecs are included in the world *)
Lemma hcl5_cs4_sub : cspecs_sub CS4 W_handshake_clear.
Proof. rewrite W_handshake_clear_eq; apply world_cspecs_sub; vm_refl. Qed.
Lemma hcl5_cs4s_sub : cspecs_sub CS4s W_handshake_clear.
Proof. rewrite W_handshake_clear_eq; apply world_cspecs_sub; vm_refl. Qed.
