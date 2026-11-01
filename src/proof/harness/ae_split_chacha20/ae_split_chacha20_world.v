(* The world of law ae_split_chacha20: the compspecs of its whole program (harness/ae_split_chacha20.c linked
   with lib/crypto/chacha.c, lib/crypto/chacha-block-generic.c, patch/wg_shim.c and quickproof/libc/libc.c),
   built as the worlds of the x_ laws in wg3_worlds.v: W_ae_split_chacha20 computes like a unit's compspecs,
   equals the compspecs of the program's composite environment (what harness_safe needs, W_ae_split_chacha20_eq),
   and includes the compspecs of the harness and of the four units (world_ok_ae_split_chacha20), so that body
   proofs in a unit's compspecs lift into the law. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require WgNoise.contracts.ae_split_chacha20.

(* the world of the law: the program, its composite environment, and the compspecs of the harness and of the
   linked units included in it *)
Definition sc_world_ok (p: QP.program function) (Hcs: compspecs) (W: compspecs) : Prop :=
  exists OK: QPprogram_OK p,
    W = compspecs_of_QPcomposite_env (QP.prog_comp_env p) (proj2 OK) /\
    build_composite_env
      (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) [])) =
    Errors.OK (composite_env_of_QPcomposite_env (QP.prog_comp_env p) (projT1 (proj2 OK))) /\
    Forall (fun cs => cspecs_sub cs W) [Hcs; Chacha.CS; ChachaBlock.CS; Shim.CS; Libc.CS].

Lemma world_OK_H_ae_split_chacha20 : QPprogram_OK WgNoise.contracts.ae_split_chacha20.Harness.qp.
Proof. prove_unit_OK WgNoise.contracts.ae_split_chacha20.Harness.CS. Qed.
Lemma world_OK_sc_link_ChachaBlock : QPprogram_OK WgNoise.contracts.ae_split_chacha20.link_ChachaBlock.
Proof. link_OK ChachaBlock.qp Chacha.qp world_OK_ChachaBlock world_OK_Chacha. Qed.
Lemma world_OK_sc_link_Shim : QPprogram_OK WgNoise.contracts.ae_split_chacha20.link_Shim.
Proof. link_OK Shim.qp WgNoise.contracts.ae_split_chacha20.link_ChachaBlock world_OK_Shim world_OK_sc_link_ChachaBlock. Qed.
Lemma world_OK_sc_link_Libc : QPprogram_OK WgNoise.contracts.ae_split_chacha20.link_Libc.
Proof. link_OK Libc.qp WgNoise.contracts.ae_split_chacha20.link_Shim world_OK_Libc world_OK_sc_link_Shim. Qed.
Lemma world_OK_whole_ae_split_chacha20 : QPprogram_OK WgNoise.contracts.ae_split_chacha20.whole_prog.
Proof. link_OK WgNoise.contracts.ae_split_chacha20.Harness.qp WgNoise.contracts.ae_split_chacha20.link_Libc world_OK_H_ae_split_chacha20 world_OK_sc_link_Libc. Qed.
Definition ce_ae_split_chacha20 : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.ae_split_chacha20.whole_prog) in exact x).
Lemma OKce_ae_split_chacha20 : QPcompspecs_OK ce_ae_split_chacha20. Proof. exact (proj2 world_OK_whole_ae_split_chacha20). Qed.
Definition W0_ae_split_chacha20 : compspecs := compspecs_of_QPcomposite_env ce_ae_split_chacha20 OKce_ae_split_chacha20.
Definition cenv_ae_split_chacha20 : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_ae_split_chacha20) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_ae_split_chacha20 : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_ae_split_chacha20) in exact x).
Definition la_ae_split_chacha20 : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_ae_split_chacha20) in exact x).
Lemma cenv_ae_split_chacha20_eq : cenv_ae_split_chacha20 = @cenv_cs W0_ae_split_chacha20.
Proof. unfold W0_ae_split_chacha20; destruct (QPcompspecs_OK_e _ OKce_ae_split_chacha20) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_ae_split_chacha20_eq : ha_ae_split_chacha20 = @ha_env_cs W0_ae_split_chacha20.
Proof. unfold W0_ae_split_chacha20; destruct (QPcompspecs_OK_e _ OKce_ae_split_chacha20) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_ae_split_chacha20_eq : la_ae_split_chacha20 = @la_env_cs W0_ae_split_chacha20.
Proof. unfold W0_ae_split_chacha20; destruct (QPcompspecs_OK_e _ OKce_ae_split_chacha20) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_ae_split_chacha20 : composite_env_consistent cenv_ae_split_chacha20.
Proof. rewrite cenv_ae_split_chacha20_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_ae_split_chacha20 : composite_env_legal_fieldlist cenv_ae_split_chacha20.
Proof. rewrite cenv_ae_split_chacha20_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_ae_split_chacha20 : composite_env_complete_legal_cosu_type cenv_ae_split_chacha20.
Proof. rewrite cenv_ae_split_chacha20_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_ae_split_chacha20 : hardware_alignof_env_consistent cenv_ae_split_chacha20 ha_ae_split_chacha20.
Proof. rewrite cenv_ae_split_chacha20_eq, ha_ae_split_chacha20_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_ae_split_chacha20 : hardware_alignof_env_complete cenv_ae_split_chacha20 ha_ae_split_chacha20.
Proof. rewrite cenv_ae_split_chacha20_eq, ha_ae_split_chacha20_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_ae_split_chacha20 : legal_alignas_env_consistent cenv_ae_split_chacha20 ha_ae_split_chacha20 la_ae_split_chacha20.
Proof. rewrite cenv_ae_split_chacha20_eq, ha_ae_split_chacha20_eq, la_ae_split_chacha20_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_ae_split_chacha20 : legal_alignas_env_complete cenv_ae_split_chacha20 la_ae_split_chacha20.
Proof. rewrite cenv_ae_split_chacha20_eq, la_ae_split_chacha20_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_ae_split_chacha20 : legal_alignas_env_sound cenv_ae_split_chacha20 ha_ae_split_chacha20 la_ae_split_chacha20.
Proof. rewrite cenv_ae_split_chacha20_eq, ha_ae_split_chacha20_eq, la_ae_split_chacha20_eq; apply la_env_cs_sound. Qed.
Definition W_ae_split_chacha20 : compspecs :=
  {| cenv_cs := cenv_ae_split_chacha20; cenv_consistent := cenv_consistent_ae_split_chacha20; cenv_legal_fieldlist := cenv_legal_fieldlist_ae_split_chacha20;
     cenv_legal_su := cenv_legal_su_ae_split_chacha20; ha_env_cs := ha_ae_split_chacha20; ha_env_cs_consistent := ha_env_consistent_ae_split_chacha20;
     ha_env_cs_complete := ha_env_complete_ae_split_chacha20; la_env_cs := la_ae_split_chacha20; la_env_cs_consistent := la_env_consistent_ae_split_chacha20;
     la_env_cs_complete := la_env_complete_ae_split_chacha20; la_env_cs_sound := la_env_sound_ae_split_chacha20 |}.
Lemma W_ae_split_chacha20_eq : W_ae_split_chacha20 = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.ae_split_chacha20.whole_prog) (proj2 world_OK_whole_ae_split_chacha20).
Proof.
transitivity W0_ae_split_chacha20.
- apply compspecs_ext; [apply cenv_ae_split_chacha20_eq | apply ha_ae_split_chacha20_eq | apply la_ae_split_chacha20_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.
Lemma world_ok_ae_split_chacha20 : sc_world_ok WgNoise.contracts.ae_split_chacha20.whole_prog WgNoise.contracts.ae_split_chacha20.Harness.CS W_ae_split_chacha20.
Proof.
exists world_OK_whole_ae_split_chacha20.
split; [apply W_ae_split_chacha20_eq | split].
- apply cenv_built_correctly_e; vm_refl.
- rewrite W_ae_split_chacha20_eq; repeat constructor; apply world_cspecs_sub; vm_refl.
Qed.

