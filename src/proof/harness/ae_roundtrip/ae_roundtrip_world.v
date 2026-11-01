(* Law ae_roundtrip: the world compspecs W_ae_roundtrip, the compspecs of the whole program's composite
   environment (the one harness_safe asks for), built as wg3_worlds.v builds the x_ laws' worlds so that it
   computes like a unit's compspecs.  The program links the harness with chacha.c, chacha-block-generic.c,
   poly1305.c, poly1305-donna32.c, chacha20poly1305.c, the shim and the libc (no noise.c, cookie.c, blake2s.c,
   curve25519.c): the compspecs of those seven units and of the harness are included in W_ae_roundtrip
   (world_ok_ae_roundtrip), so their body proofs lift into it. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32
        WgNoise.units.Chacha20poly1305 WgNoise.units.Shim WgNoise.units.Libc.
Require WgNoise.contracts.ae_roundtrip.
Require Import WgNoise.proof.common.wg3_worlds.

Module C := WgNoise.contracts.ae_roundtrip.

(* the compspecs of the AEAD program's units *)
Definition aead_prog_unit_cs : list compspecs :=
  [Chacha.CS; ChachaBlock.CS; Poly1305.CS; Poly1305Donna32.CS; Chacha20poly1305.CS; Shim.CS; Libc.CS].

(* the link chain of the contract, step by step *)
Lemma world_OK_H_ae_roundtrip : QPprogram_OK C.Harness.qp. Proof. prove_unit_OK C.Harness.CS. Qed.
Lemma world_OK_ar_ChachaBlock : QPprogram_OK C.link_ChachaBlock.
Proof. link_OK ChachaBlock.qp Chacha.qp world_OK_ChachaBlock world_OK_Chacha. Qed.
Lemma world_OK_ar_Poly1305 : QPprogram_OK C.link_Poly1305.
Proof. link_OK Poly1305.qp C.link_ChachaBlock world_OK_Poly1305 world_OK_ar_ChachaBlock. Qed.
Lemma world_OK_ar_Poly1305Donna32 : QPprogram_OK C.link_Poly1305Donna32.
Proof. link_OK Poly1305Donna32.qp C.link_Poly1305 world_OK_Poly1305Donna32 world_OK_ar_Poly1305. Qed.
Lemma world_OK_ar_Chacha20poly1305 : QPprogram_OK C.link_Chacha20poly1305.
Proof. link_OK Chacha20poly1305.qp C.link_Poly1305Donna32 world_OK_Chacha20poly1305 world_OK_ar_Poly1305Donna32. Qed.
Lemma world_OK_ar_Shim : QPprogram_OK C.link_Shim.
Proof. link_OK Shim.qp C.link_Chacha20poly1305 world_OK_Shim world_OK_ar_Chacha20poly1305. Qed.
Lemma world_OK_ar_Libc : QPprogram_OK C.link_Libc.
Proof. link_OK Libc.qp C.link_Shim world_OK_Libc world_OK_ar_Shim. Qed.
Lemma world_OK_whole_ae_roundtrip : QPprogram_OK C.whole_prog.
Proof. link_OK C.Harness.qp C.link_Libc world_OK_H_ae_roundtrip world_OK_ar_Libc. Qed.

Definition ce_ae_roundtrip : QP.composite_env :=
  ltac:(let x := eval vm_compute in (QP.prog_comp_env C.whole_prog) in exact x).
Lemma OKce_ae_roundtrip : QPcompspecs_OK ce_ae_roundtrip. Proof. exact (proj2 world_OK_whole_ae_roundtrip). Qed.
Definition W0_ae_roundtrip : compspecs := compspecs_of_QPcomposite_env ce_ae_roundtrip OKce_ae_roundtrip.
Definition cenv_ae_roundtrip : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_ae_roundtrip) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_ae_roundtrip : Maps.PTree.t Z :=
  ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_ae_roundtrip) in exact x).
Definition la_ae_roundtrip : Maps.PTree.t legal_alignas_obs :=
  ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_ae_roundtrip) in exact x).
Lemma cenv_ae_roundtrip_eq : cenv_ae_roundtrip = @cenv_cs W0_ae_roundtrip.
Proof. unfold W0_ae_roundtrip; destruct (QPcompspecs_OK_e _ OKce_ae_roundtrip) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_ae_roundtrip_eq : ha_ae_roundtrip = @ha_env_cs W0_ae_roundtrip.
Proof. unfold W0_ae_roundtrip; destruct (QPcompspecs_OK_e _ OKce_ae_roundtrip) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_ae_roundtrip_eq : la_ae_roundtrip = @la_env_cs W0_ae_roundtrip.
Proof. unfold W0_ae_roundtrip; destruct (QPcompspecs_OK_e _ OKce_ae_roundtrip) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_ae_roundtrip : composite_env_consistent cenv_ae_roundtrip.
Proof. rewrite cenv_ae_roundtrip_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_ae_roundtrip : composite_env_legal_fieldlist cenv_ae_roundtrip.
Proof. rewrite cenv_ae_roundtrip_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_ae_roundtrip : composite_env_complete_legal_cosu_type cenv_ae_roundtrip.
Proof. rewrite cenv_ae_roundtrip_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_ae_roundtrip : hardware_alignof_env_consistent cenv_ae_roundtrip ha_ae_roundtrip.
Proof. rewrite cenv_ae_roundtrip_eq, ha_ae_roundtrip_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_ae_roundtrip : hardware_alignof_env_complete cenv_ae_roundtrip ha_ae_roundtrip.
Proof. rewrite cenv_ae_roundtrip_eq, ha_ae_roundtrip_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_ae_roundtrip : legal_alignas_env_consistent cenv_ae_roundtrip ha_ae_roundtrip la_ae_roundtrip.
Proof. rewrite cenv_ae_roundtrip_eq, ha_ae_roundtrip_eq, la_ae_roundtrip_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_ae_roundtrip : legal_alignas_env_complete cenv_ae_roundtrip la_ae_roundtrip.
Proof. rewrite cenv_ae_roundtrip_eq, la_ae_roundtrip_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_ae_roundtrip : legal_alignas_env_sound cenv_ae_roundtrip ha_ae_roundtrip la_ae_roundtrip.
Proof. rewrite cenv_ae_roundtrip_eq, ha_ae_roundtrip_eq, la_ae_roundtrip_eq; apply la_env_cs_sound. Qed.

Definition W_ae_roundtrip : compspecs :=
  {| cenv_cs := cenv_ae_roundtrip; cenv_consistent := cenv_consistent_ae_roundtrip;
     cenv_legal_fieldlist := cenv_legal_fieldlist_ae_roundtrip; cenv_legal_su := cenv_legal_su_ae_roundtrip;
     ha_env_cs := ha_ae_roundtrip; ha_env_cs_consistent := ha_env_consistent_ae_roundtrip;
     ha_env_cs_complete := ha_env_complete_ae_roundtrip; la_env_cs := la_ae_roundtrip;
     la_env_cs_consistent := la_env_consistent_ae_roundtrip; la_env_cs_complete := la_env_complete_ae_roundtrip;
     la_env_cs_sound := la_env_sound_ae_roundtrip |}.

Lemma W_ae_roundtrip_eq :
  W_ae_roundtrip = compspecs_of_QPcomposite_env (QP.prog_comp_env C.whole_prog) (proj2 world_OK_whole_ae_roundtrip).
Proof.
transitivity W0_ae_roundtrip.
- apply compspecs_ext; [apply cenv_ae_roundtrip_eq | apply ha_ae_roundtrip_eq | apply la_ae_roundtrip_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.

Lemma cbc_ae_roundtrip : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env C.whole_prog)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env C.whole_prog) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

(* the harness's and the seven units' compspecs are included in the world *)
Lemma world_ok_ae_roundtrip : Forall (fun cs => cspecs_sub cs W_ae_roundtrip) (C.Harness.CS :: aead_prog_unit_cs).
Proof. rewrite W_ae_roundtrip_eq; repeat constructor; apply world_cspecs_sub; vm_refl. Qed.

Lemma cs_sub_ae_roundtrip cs : In cs (C.Harness.CS :: aead_prog_unit_cs) -> cspecs_sub cs W_ae_roundtrip.
Proof. pose proof world_ok_ae_roundtrip as H. rewrite Forall_forall in H. auto. Qed.
