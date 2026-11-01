(* The world of law ae_split_blake2s: the compspecs of its whole program (harness/ae_split_blake2s.c linked with
   lib/crypto/blake2s.c and quickproof/libc/libc.c), built as the worlds of the x_ laws in wg3_worlds.v.
   W_aesb computes like a unit's compspecs, equals the compspecs of the program's composite environment (what
   harness_safe needs, W_aesb_eq), and includes the harness's, Blake2s's and Libc's compspecs (world_ok_aesb), so
   that the bodies proved in those units lift into the law.  The program's only composite is struct blake2s_ctx. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require WgNoise.contracts.ae_split_blake2s.

(* the world of the law: the program, its composite environment, and the compspecs of its three units included
   in it *)
Definition aesb_world_ok (p: QP.program function) (W: compspecs) : Prop :=
  exists OK: QPprogram_OK p,
    W = compspecs_of_QPcomposite_env (QP.prog_comp_env p) (proj2 OK) /\
    build_composite_env
      (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) [])) =
    Errors.OK (composite_env_of_QPcomposite_env (QP.prog_comp_env p) (projT1 (proj2 OK))) /\
    Forall (fun cs => cspecs_sub cs W) [WgNoise.contracts.ae_split_blake2s.Harness.CS; Blake2s.CS; Libc.CS].

Lemma world_OK_H_aesb : QPprogram_OK WgNoise.contracts.ae_split_blake2s.Harness.qp. Proof. prove_unit_OK WgNoise.contracts.ae_split_blake2s.Harness.CS. Qed.
Lemma world_OK_link_Libc_aesb : QPprogram_OK WgNoise.contracts.ae_split_blake2s.link_Libc.
Proof. link_OK Libc.qp Blake2s.qp world_OK_Libc world_OK_Blake2s. Qed.
Lemma world_OK_whole_aesb : QPprogram_OK WgNoise.contracts.ae_split_blake2s.whole_prog.
Proof. link_OK WgNoise.contracts.ae_split_blake2s.Harness.qp WgNoise.contracts.ae_split_blake2s.link_Libc world_OK_H_aesb world_OK_link_Libc_aesb. Qed.
Definition ce_aesb : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.ae_split_blake2s.whole_prog) in exact x).
Lemma OKce_aesb : QPcompspecs_OK ce_aesb. Proof. exact (proj2 world_OK_whole_aesb). Qed.
Definition W0_aesb : compspecs := compspecs_of_QPcomposite_env ce_aesb OKce_aesb.
Definition cenv_aesb : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_aesb) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_aesb : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_aesb) in exact x).
Definition la_aesb : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_aesb) in exact x).
Lemma cenv_aesb_eq : cenv_aesb = @cenv_cs W0_aesb.
Proof. unfold W0_aesb; destruct (QPcompspecs_OK_e _ OKce_aesb) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_aesb_eq : ha_aesb = @ha_env_cs W0_aesb.
Proof. unfold W0_aesb; destruct (QPcompspecs_OK_e _ OKce_aesb) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_aesb_eq : la_aesb = @la_env_cs W0_aesb.
Proof. unfold W0_aesb; destruct (QPcompspecs_OK_e _ OKce_aesb) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_aesb : composite_env_consistent cenv_aesb.
Proof. rewrite cenv_aesb_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_aesb : composite_env_legal_fieldlist cenv_aesb.
Proof. rewrite cenv_aesb_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_aesb : composite_env_complete_legal_cosu_type cenv_aesb.
Proof. rewrite cenv_aesb_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_aesb : hardware_alignof_env_consistent cenv_aesb ha_aesb.
Proof. rewrite cenv_aesb_eq, ha_aesb_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_aesb : hardware_alignof_env_complete cenv_aesb ha_aesb.
Proof. rewrite cenv_aesb_eq, ha_aesb_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_aesb : legal_alignas_env_consistent cenv_aesb ha_aesb la_aesb.
Proof. rewrite cenv_aesb_eq, ha_aesb_eq, la_aesb_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_aesb : legal_alignas_env_complete cenv_aesb la_aesb.
Proof. rewrite cenv_aesb_eq, la_aesb_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_aesb : legal_alignas_env_sound cenv_aesb ha_aesb la_aesb.
Proof. rewrite cenv_aesb_eq, ha_aesb_eq, la_aesb_eq; apply la_env_cs_sound. Qed.
Definition W_aesb : compspecs :=
  {| cenv_cs := cenv_aesb; cenv_consistent := cenv_consistent_aesb; cenv_legal_fieldlist := cenv_legal_fieldlist_aesb;
     cenv_legal_su := cenv_legal_su_aesb; ha_env_cs := ha_aesb; ha_env_cs_consistent := ha_env_consistent_aesb;
     ha_env_cs_complete := ha_env_complete_aesb; la_env_cs := la_aesb; la_env_cs_consistent := la_env_consistent_aesb;
     la_env_cs_complete := la_env_complete_aesb; la_env_cs_sound := la_env_sound_aesb |}.
Lemma W_aesb_eq : W_aesb = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.ae_split_blake2s.whole_prog) (proj2 world_OK_whole_aesb).
Proof.
transitivity W0_aesb.
- apply compspecs_ext; [apply cenv_aesb_eq | apply ha_aesb_eq | apply la_aesb_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.
Lemma world_ok_aesb : aesb_world_ok WgNoise.contracts.ae_split_blake2s.whole_prog W_aesb.
Proof.
exists world_OK_whole_aesb.
split; [apply W_aesb_eq | split].
- apply cenv_built_correctly_e; vm_refl.
- rewrite W_aesb_eq; repeat constructor; apply world_cspecs_sub; vm_refl.
Qed.
