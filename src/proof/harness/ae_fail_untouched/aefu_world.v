(* The world of law ae_fail_untouched: the compspecs of its whole program (harness/ae_fail_untouched.c linked
   with the AEAD units, the shim and the libc), built as wg3_worlds.v builds the worlds of the x_ laws:
   W_ae_fail_untouched computes like a unit's compspecs, is equal to the compspecs harness_safe uses
   (W_ae_fail_untouched_eq), and includes the compspecs of the harness, of every linked unit and of curve25519.c
   (whose copy of the inline crypto_memneq is the proved one, libc_piece.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require WgNoise.contracts.ae_fail_untouched.

Module AF := WgNoise.contracts.ae_fail_untouched.

(* the link steps of the contract, each checked by computation *)
Lemma afw_OK_H : QPprogram_OK AF.Harness.qp. Proof. prove_unit_OK AF.Harness.CS. Qed.
Lemma afw_OK_link_ChachaBlock : QPprogram_OK AF.link_ChachaBlock.
Proof. link_OK ChachaBlock.qp Chacha.qp world_OK_ChachaBlock world_OK_Chacha. Qed.
Lemma afw_OK_link_Poly1305 : QPprogram_OK AF.link_Poly1305.
Proof. link_OK Poly1305.qp AF.link_ChachaBlock world_OK_Poly1305 afw_OK_link_ChachaBlock. Qed.
Lemma afw_OK_link_Poly1305Donna32 : QPprogram_OK AF.link_Poly1305Donna32.
Proof. link_OK Poly1305Donna32.qp AF.link_Poly1305 world_OK_Poly1305Donna32 afw_OK_link_Poly1305. Qed.
Lemma afw_OK_link_Chacha20poly1305 : QPprogram_OK AF.link_Chacha20poly1305.
Proof. link_OK Chacha20poly1305.qp AF.link_Poly1305Donna32 world_OK_Chacha20poly1305 afw_OK_link_Poly1305Donna32. Qed.
Lemma afw_OK_link_Shim : QPprogram_OK AF.link_Shim.
Proof. link_OK Shim.qp AF.link_Chacha20poly1305 world_OK_Shim afw_OK_link_Chacha20poly1305. Qed.
Lemma afw_OK_link_Libc : QPprogram_OK AF.link_Libc.
Proof. link_OK Libc.qp AF.link_Shim world_OK_Libc afw_OK_link_Shim. Qed.
Lemma world_OK_whole_ae_fail_untouched : QPprogram_OK AF.whole_prog.
Proof. link_OK AF.Harness.qp AF.link_Libc afw_OK_H afw_OK_link_Libc. Qed.

Definition ce_ae_fail_untouched : QP.composite_env :=
  ltac:(let x := eval vm_compute in (QP.prog_comp_env AF.whole_prog) in exact x).
Lemma OKce_ae_fail_untouched : QPcompspecs_OK ce_ae_fail_untouched. Proof. exact (proj2 world_OK_whole_ae_fail_untouched). Qed.
Definition W0_ae_fail_untouched : compspecs := compspecs_of_QPcomposite_env ce_ae_fail_untouched OKce_ae_fail_untouched.
Definition cenv_ae_fail_untouched : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_ae_fail_untouched) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_ae_fail_untouched : Maps.PTree.t Z :=
  ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_ae_fail_untouched) in exact x).
Definition la_ae_fail_untouched : Maps.PTree.t legal_alignas_obs :=
  ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_ae_fail_untouched) in exact x).
Lemma cenv_ae_fail_untouched_eq : cenv_ae_fail_untouched = @cenv_cs W0_ae_fail_untouched.
Proof. unfold W0_ae_fail_untouched; destruct (QPcompspecs_OK_e _ OKce_ae_fail_untouched) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_ae_fail_untouched_eq : ha_ae_fail_untouched = @ha_env_cs W0_ae_fail_untouched.
Proof. unfold W0_ae_fail_untouched; destruct (QPcompspecs_OK_e _ OKce_ae_fail_untouched) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_ae_fail_untouched_eq : la_ae_fail_untouched = @la_env_cs W0_ae_fail_untouched.
Proof. unfold W0_ae_fail_untouched; destruct (QPcompspecs_OK_e _ OKce_ae_fail_untouched) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_ae_fail_untouched : composite_env_consistent cenv_ae_fail_untouched.
Proof. rewrite cenv_ae_fail_untouched_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_ae_fail_untouched : composite_env_legal_fieldlist cenv_ae_fail_untouched.
Proof. rewrite cenv_ae_fail_untouched_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_ae_fail_untouched : composite_env_complete_legal_cosu_type cenv_ae_fail_untouched.
Proof. rewrite cenv_ae_fail_untouched_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_ae_fail_untouched : hardware_alignof_env_consistent cenv_ae_fail_untouched ha_ae_fail_untouched.
Proof. rewrite cenv_ae_fail_untouched_eq, ha_ae_fail_untouched_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_ae_fail_untouched : hardware_alignof_env_complete cenv_ae_fail_untouched ha_ae_fail_untouched.
Proof. rewrite cenv_ae_fail_untouched_eq, ha_ae_fail_untouched_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_ae_fail_untouched : legal_alignas_env_consistent cenv_ae_fail_untouched ha_ae_fail_untouched la_ae_fail_untouched.
Proof. rewrite cenv_ae_fail_untouched_eq, ha_ae_fail_untouched_eq, la_ae_fail_untouched_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_ae_fail_untouched : legal_alignas_env_complete cenv_ae_fail_untouched la_ae_fail_untouched.
Proof. rewrite cenv_ae_fail_untouched_eq, la_ae_fail_untouched_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_ae_fail_untouched : legal_alignas_env_sound cenv_ae_fail_untouched ha_ae_fail_untouched la_ae_fail_untouched.
Proof. rewrite cenv_ae_fail_untouched_eq, ha_ae_fail_untouched_eq, la_ae_fail_untouched_eq; apply la_env_cs_sound. Qed.

Definition W_ae_fail_untouched : compspecs :=
  {| cenv_cs := cenv_ae_fail_untouched; cenv_consistent := cenv_consistent_ae_fail_untouched;
     cenv_legal_fieldlist := cenv_legal_fieldlist_ae_fail_untouched; cenv_legal_su := cenv_legal_su_ae_fail_untouched;
     ha_env_cs := ha_ae_fail_untouched; ha_env_cs_consistent := ha_env_consistent_ae_fail_untouched;
     ha_env_cs_complete := ha_env_complete_ae_fail_untouched; la_env_cs := la_ae_fail_untouched;
     la_env_cs_consistent := la_env_consistent_ae_fail_untouched; la_env_cs_complete := la_env_complete_ae_fail_untouched;
     la_env_cs_sound := la_env_sound_ae_fail_untouched |}.

Lemma W_ae_fail_untouched_eq :
  W_ae_fail_untouched = compspecs_of_QPcomposite_env (QP.prog_comp_env AF.whole_prog) (proj2 world_OK_whole_ae_fail_untouched).
Proof.
transitivity W0_ae_fail_untouched.
- apply compspecs_ext; [apply cenv_ae_fail_untouched_eq | apply ha_ae_fail_untouched_eq | apply la_ae_fail_untouched_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.

(* the compspecs of the harness, of the linked units and of curve25519.c, included in the world *)
Definition afw_unit_cs : list compspecs :=
  [AF.Harness.CS; Chacha.CS; ChachaBlock.CS; Poly1305.CS; Poly1305Donna32.CS; Chacha20poly1305.CS;
   Shim.CS; Libc.CS; Curve25519.CS].

Lemma world_ok_ae_fail_untouched : Forall (fun cs => cspecs_sub cs W_ae_fail_untouched) afw_unit_cs.
Proof. rewrite W_ae_fail_untouched_eq; repeat constructor; apply world_cspecs_sub; vm_refl. Qed.
