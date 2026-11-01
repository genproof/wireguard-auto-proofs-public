(* The worlds of the eight hs_ laws: for each law, the compspecs W_hs_<law> of its whole program's composite
   environment (the one harness_safe asks for), built as wg3_worlds.v builds the x_ laws' worlds so that it
   computes like a unit's compspecs.  The hs_ programs link the harness with noise.c, blake2s.c, chacha.c,
   chacha-block-generic.c, poly1305.c, poly1305-donna32.c, chacha20poly1305.c, curve25519.c,
   curve25519-fiat32.c, the shim and the libc (no cookie.c, counter_validate.c, malloc_unit.c), all eight in the
   same order: the link chain is checked once (on hs_response_state's copy, the others' being the same terms).
   world_ok_hs_<law>: the compspecs of the harness, of the helpers' body proofs (CSh) and of the eleven units
   are included in the world, so their body proofs lift into it. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock
        WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305
        WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc.
Require WgNoise.contracts.hs_begin_session_state WgNoise.contracts.hs_matching_keys
        WgNoise.contracts.hs_reject_initiation WgNoise.contracts.hs_reject_response
        WgNoise.contracts.hs_replay_initiation WgNoise.contracts.hs_response_state
        WgNoise.contracts.hs_session_erases WgNoise.contracts.hs_stale_response.
Require Import WgNoise.proof.common.wg3_worlds.

(* the compspecs of the hs_ programs' units, and CSh (hs_specs.v: the compspecs of the helpers' bodies) *)
Definition hs_unit_cs : list compspecs :=
  [WgNoise.contracts.hs_reject_initiation.Harness.CS;
   Noise.CS; Blake2s.CS; Chacha.CS; ChachaBlock.CS; Poly1305.CS; Poly1305Donna32.CS; Chacha20poly1305.CS;
   Curve25519.CS; Curve25519Fiat32.CS; Shim.CS; Libc.CS].

Module RS := WgNoise.contracts.hs_response_state.

(* the link chain, once *)
Lemma world_OK_hs_link_Blake2s : QPprogram_OK RS.link_Blake2s.
Proof. link_OK Blake2s.qp Noise.qp world_OK_Blake2s world_OK_Noise. Qed.
Lemma world_OK_hs_link_Chacha : QPprogram_OK RS.link_Chacha.
Proof. link_OK Chacha.qp RS.link_Blake2s world_OK_Chacha world_OK_hs_link_Blake2s. Qed.
Lemma world_OK_hs_link_ChachaBlock : QPprogram_OK RS.link_ChachaBlock.
Proof. link_OK ChachaBlock.qp RS.link_Chacha world_OK_ChachaBlock world_OK_hs_link_Chacha. Qed.
Lemma world_OK_hs_link_Poly1305 : QPprogram_OK RS.link_Poly1305.
Proof. link_OK Poly1305.qp RS.link_ChachaBlock world_OK_Poly1305 world_OK_hs_link_ChachaBlock. Qed.
Lemma world_OK_hs_link_Poly1305Donna32 : QPprogram_OK RS.link_Poly1305Donna32.
Proof. link_OK Poly1305Donna32.qp RS.link_Poly1305 world_OK_Poly1305Donna32 world_OK_hs_link_Poly1305. Qed.
Lemma world_OK_hs_link_Chacha20poly1305 : QPprogram_OK RS.link_Chacha20poly1305.
Proof. link_OK Chacha20poly1305.qp RS.link_Poly1305Donna32 world_OK_Chacha20poly1305 world_OK_hs_link_Poly1305Donna32. Qed.
Lemma world_OK_hs_link_Curve25519 : QPprogram_OK RS.link_Curve25519.
Proof. link_OK Curve25519.qp RS.link_Chacha20poly1305 world_OK_Curve25519 world_OK_hs_link_Chacha20poly1305. Qed.
Lemma world_OK_hs_link_Curve25519Fiat32 : QPprogram_OK RS.link_Curve25519Fiat32.
Proof. link_OK Curve25519Fiat32.qp RS.link_Curve25519 world_OK_Curve25519Fiat32 world_OK_hs_link_Curve25519. Qed.
Lemma world_OK_hs_link_Shim : QPprogram_OK RS.link_Shim.
Proof. link_OK Shim.qp RS.link_Curve25519Fiat32 world_OK_Shim world_OK_hs_link_Curve25519Fiat32. Qed.
Lemma world_OK_hs_link_Libc : QPprogram_OK RS.link_Libc.
Proof. link_OK Libc.qp RS.link_Shim world_OK_Libc world_OK_hs_link_Shim. Qed.

(* ---------- hs_begin_session_state ---------- *)
Lemma world_OK_H_hs_begin_session_state : QPprogram_OK WgNoise.contracts.hs_begin_session_state.Harness.qp.
Proof. prove_unit_OK WgNoise.contracts.hs_begin_session_state.Harness.CS. Qed.
Lemma world_OK_link_Libc_hs_begin_session_state : QPprogram_OK WgNoise.contracts.hs_begin_session_state.link_Libc.
Proof. exact world_OK_hs_link_Libc. Qed.
Lemma world_OK_whole_hs_begin_session_state : QPprogram_OK WgNoise.contracts.hs_begin_session_state.whole_prog.
Proof. link_OK WgNoise.contracts.hs_begin_session_state.Harness.qp WgNoise.contracts.hs_begin_session_state.link_Libc world_OK_H_hs_begin_session_state world_OK_link_Libc_hs_begin_session_state. Qed.
Definition ce_hs_begin_session_state : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.hs_begin_session_state.whole_prog) in exact x).
Lemma OKce_hs_begin_session_state : QPcompspecs_OK ce_hs_begin_session_state. Proof. exact (proj2 world_OK_whole_hs_begin_session_state). Qed.
Definition W0_hs_begin_session_state : compspecs := compspecs_of_QPcomposite_env ce_hs_begin_session_state OKce_hs_begin_session_state.
Definition cenv_hs_begin_session_state : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_hs_begin_session_state) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_hs_begin_session_state : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_hs_begin_session_state) in exact x).
Definition la_hs_begin_session_state : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_hs_begin_session_state) in exact x).
Lemma cenv_hs_begin_session_state_eq : cenv_hs_begin_session_state = @cenv_cs W0_hs_begin_session_state.
Proof. unfold W0_hs_begin_session_state; destruct (QPcompspecs_OK_e _ OKce_hs_begin_session_state) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_hs_begin_session_state_eq : ha_hs_begin_session_state = @ha_env_cs W0_hs_begin_session_state.
Proof. unfold W0_hs_begin_session_state; destruct (QPcompspecs_OK_e _ OKce_hs_begin_session_state) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_hs_begin_session_state_eq : la_hs_begin_session_state = @la_env_cs W0_hs_begin_session_state.
Proof. unfold W0_hs_begin_session_state; destruct (QPcompspecs_OK_e _ OKce_hs_begin_session_state) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_hs_begin_session_state : composite_env_consistent cenv_hs_begin_session_state.
Proof. rewrite cenv_hs_begin_session_state_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_hs_begin_session_state : composite_env_legal_fieldlist cenv_hs_begin_session_state.
Proof. rewrite cenv_hs_begin_session_state_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_hs_begin_session_state : composite_env_complete_legal_cosu_type cenv_hs_begin_session_state.
Proof. rewrite cenv_hs_begin_session_state_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_hs_begin_session_state : hardware_alignof_env_consistent cenv_hs_begin_session_state ha_hs_begin_session_state.
Proof. rewrite cenv_hs_begin_session_state_eq, ha_hs_begin_session_state_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_hs_begin_session_state : hardware_alignof_env_complete cenv_hs_begin_session_state ha_hs_begin_session_state.
Proof. rewrite cenv_hs_begin_session_state_eq, ha_hs_begin_session_state_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_hs_begin_session_state : legal_alignas_env_consistent cenv_hs_begin_session_state ha_hs_begin_session_state la_hs_begin_session_state.
Proof. rewrite cenv_hs_begin_session_state_eq, ha_hs_begin_session_state_eq, la_hs_begin_session_state_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_hs_begin_session_state : legal_alignas_env_complete cenv_hs_begin_session_state la_hs_begin_session_state.
Proof. rewrite cenv_hs_begin_session_state_eq, la_hs_begin_session_state_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_hs_begin_session_state : legal_alignas_env_sound cenv_hs_begin_session_state ha_hs_begin_session_state la_hs_begin_session_state.
Proof. rewrite cenv_hs_begin_session_state_eq, ha_hs_begin_session_state_eq, la_hs_begin_session_state_eq; apply la_env_cs_sound. Qed.

Definition W_hs_begin_session_state : compspecs :=
  {| cenv_cs := cenv_hs_begin_session_state; cenv_consistent := cenv_consistent_hs_begin_session_state;
     cenv_legal_fieldlist := cenv_legal_fieldlist_hs_begin_session_state; cenv_legal_su := cenv_legal_su_hs_begin_session_state;
     ha_env_cs := ha_hs_begin_session_state; ha_env_cs_consistent := ha_env_consistent_hs_begin_session_state;
     ha_env_cs_complete := ha_env_complete_hs_begin_session_state; la_env_cs := la_hs_begin_session_state;
     la_env_cs_consistent := la_env_consistent_hs_begin_session_state; la_env_cs_complete := la_env_complete_hs_begin_session_state;
     la_env_cs_sound := la_env_sound_hs_begin_session_state |}.

Lemma W_hs_begin_session_state_eq :
  W_hs_begin_session_state = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.hs_begin_session_state.whole_prog)
               (proj2 world_OK_whole_hs_begin_session_state).
Proof.
transitivity W0_hs_begin_session_state.
- apply compspecs_ext; [apply cenv_hs_begin_session_state_eq | apply ha_hs_begin_session_state_eq | apply la_hs_begin_session_state_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.

Lemma cbc_hs_begin_session_state : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env WgNoise.contracts.hs_begin_session_state.whole_prog)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.hs_begin_session_state.whole_prog) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma world_ok_hs_begin_session_state :
  Forall (fun cs => cspecs_sub cs W_hs_begin_session_state) (WgNoise.contracts.hs_begin_session_state.Harness.CS :: hs_unit_cs).
Proof. rewrite W_hs_begin_session_state_eq; repeat constructor; apply world_cspecs_sub; vm_refl. Qed.

(* ---------- hs_matching_keys ---------- *)
Lemma world_OK_H_hs_matching_keys : QPprogram_OK WgNoise.contracts.hs_matching_keys.Harness.qp.
Proof. prove_unit_OK WgNoise.contracts.hs_matching_keys.Harness.CS. Qed.
Lemma world_OK_link_Libc_hs_matching_keys : QPprogram_OK WgNoise.contracts.hs_matching_keys.link_Libc.
Proof. exact world_OK_hs_link_Libc. Qed.
Lemma world_OK_whole_hs_matching_keys : QPprogram_OK WgNoise.contracts.hs_matching_keys.whole_prog.
Proof. link_OK WgNoise.contracts.hs_matching_keys.Harness.qp WgNoise.contracts.hs_matching_keys.link_Libc world_OK_H_hs_matching_keys world_OK_link_Libc_hs_matching_keys. Qed.
Definition ce_hs_matching_keys : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.hs_matching_keys.whole_prog) in exact x).
Lemma OKce_hs_matching_keys : QPcompspecs_OK ce_hs_matching_keys. Proof. exact (proj2 world_OK_whole_hs_matching_keys). Qed.
Definition W0_hs_matching_keys : compspecs := compspecs_of_QPcomposite_env ce_hs_matching_keys OKce_hs_matching_keys.
Definition cenv_hs_matching_keys : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_hs_matching_keys) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_hs_matching_keys : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_hs_matching_keys) in exact x).
Definition la_hs_matching_keys : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_hs_matching_keys) in exact x).
Lemma cenv_hs_matching_keys_eq : cenv_hs_matching_keys = @cenv_cs W0_hs_matching_keys.
Proof. unfold W0_hs_matching_keys; destruct (QPcompspecs_OK_e _ OKce_hs_matching_keys) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_hs_matching_keys_eq : ha_hs_matching_keys = @ha_env_cs W0_hs_matching_keys.
Proof. unfold W0_hs_matching_keys; destruct (QPcompspecs_OK_e _ OKce_hs_matching_keys) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_hs_matching_keys_eq : la_hs_matching_keys = @la_env_cs W0_hs_matching_keys.
Proof. unfold W0_hs_matching_keys; destruct (QPcompspecs_OK_e _ OKce_hs_matching_keys) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_hs_matching_keys : composite_env_consistent cenv_hs_matching_keys.
Proof. rewrite cenv_hs_matching_keys_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_hs_matching_keys : composite_env_legal_fieldlist cenv_hs_matching_keys.
Proof. rewrite cenv_hs_matching_keys_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_hs_matching_keys : composite_env_complete_legal_cosu_type cenv_hs_matching_keys.
Proof. rewrite cenv_hs_matching_keys_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_hs_matching_keys : hardware_alignof_env_consistent cenv_hs_matching_keys ha_hs_matching_keys.
Proof. rewrite cenv_hs_matching_keys_eq, ha_hs_matching_keys_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_hs_matching_keys : hardware_alignof_env_complete cenv_hs_matching_keys ha_hs_matching_keys.
Proof. rewrite cenv_hs_matching_keys_eq, ha_hs_matching_keys_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_hs_matching_keys : legal_alignas_env_consistent cenv_hs_matching_keys ha_hs_matching_keys la_hs_matching_keys.
Proof. rewrite cenv_hs_matching_keys_eq, ha_hs_matching_keys_eq, la_hs_matching_keys_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_hs_matching_keys : legal_alignas_env_complete cenv_hs_matching_keys la_hs_matching_keys.
Proof. rewrite cenv_hs_matching_keys_eq, la_hs_matching_keys_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_hs_matching_keys : legal_alignas_env_sound cenv_hs_matching_keys ha_hs_matching_keys la_hs_matching_keys.
Proof. rewrite cenv_hs_matching_keys_eq, ha_hs_matching_keys_eq, la_hs_matching_keys_eq; apply la_env_cs_sound. Qed.

Definition W_hs_matching_keys : compspecs :=
  {| cenv_cs := cenv_hs_matching_keys; cenv_consistent := cenv_consistent_hs_matching_keys;
     cenv_legal_fieldlist := cenv_legal_fieldlist_hs_matching_keys; cenv_legal_su := cenv_legal_su_hs_matching_keys;
     ha_env_cs := ha_hs_matching_keys; ha_env_cs_consistent := ha_env_consistent_hs_matching_keys;
     ha_env_cs_complete := ha_env_complete_hs_matching_keys; la_env_cs := la_hs_matching_keys;
     la_env_cs_consistent := la_env_consistent_hs_matching_keys; la_env_cs_complete := la_env_complete_hs_matching_keys;
     la_env_cs_sound := la_env_sound_hs_matching_keys |}.

Lemma W_hs_matching_keys_eq :
  W_hs_matching_keys = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.hs_matching_keys.whole_prog)
               (proj2 world_OK_whole_hs_matching_keys).
Proof.
transitivity W0_hs_matching_keys.
- apply compspecs_ext; [apply cenv_hs_matching_keys_eq | apply ha_hs_matching_keys_eq | apply la_hs_matching_keys_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.

Lemma cbc_hs_matching_keys : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env WgNoise.contracts.hs_matching_keys.whole_prog)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.hs_matching_keys.whole_prog) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma world_ok_hs_matching_keys :
  Forall (fun cs => cspecs_sub cs W_hs_matching_keys) (WgNoise.contracts.hs_matching_keys.Harness.CS :: hs_unit_cs).
Proof. rewrite W_hs_matching_keys_eq; repeat constructor; apply world_cspecs_sub; vm_refl. Qed.

(* ---------- hs_reject_initiation ---------- *)
Lemma world_OK_H_hs_reject_initiation : QPprogram_OK WgNoise.contracts.hs_reject_initiation.Harness.qp.
Proof. prove_unit_OK WgNoise.contracts.hs_reject_initiation.Harness.CS. Qed.
Lemma world_OK_link_Libc_hs_reject_initiation : QPprogram_OK WgNoise.contracts.hs_reject_initiation.link_Libc.
Proof. exact world_OK_hs_link_Libc. Qed.
Lemma world_OK_whole_hs_reject_initiation : QPprogram_OK WgNoise.contracts.hs_reject_initiation.whole_prog.
Proof. link_OK WgNoise.contracts.hs_reject_initiation.Harness.qp WgNoise.contracts.hs_reject_initiation.link_Libc world_OK_H_hs_reject_initiation world_OK_link_Libc_hs_reject_initiation. Qed.
Definition ce_hs_reject_initiation : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.hs_reject_initiation.whole_prog) in exact x).
Lemma OKce_hs_reject_initiation : QPcompspecs_OK ce_hs_reject_initiation. Proof. exact (proj2 world_OK_whole_hs_reject_initiation). Qed.
Definition W0_hs_reject_initiation : compspecs := compspecs_of_QPcomposite_env ce_hs_reject_initiation OKce_hs_reject_initiation.
Definition cenv_hs_reject_initiation : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_hs_reject_initiation) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_hs_reject_initiation : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_hs_reject_initiation) in exact x).
Definition la_hs_reject_initiation : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_hs_reject_initiation) in exact x).
Lemma cenv_hs_reject_initiation_eq : cenv_hs_reject_initiation = @cenv_cs W0_hs_reject_initiation.
Proof. unfold W0_hs_reject_initiation; destruct (QPcompspecs_OK_e _ OKce_hs_reject_initiation) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_hs_reject_initiation_eq : ha_hs_reject_initiation = @ha_env_cs W0_hs_reject_initiation.
Proof. unfold W0_hs_reject_initiation; destruct (QPcompspecs_OK_e _ OKce_hs_reject_initiation) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_hs_reject_initiation_eq : la_hs_reject_initiation = @la_env_cs W0_hs_reject_initiation.
Proof. unfold W0_hs_reject_initiation; destruct (QPcompspecs_OK_e _ OKce_hs_reject_initiation) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_hs_reject_initiation : composite_env_consistent cenv_hs_reject_initiation.
Proof. rewrite cenv_hs_reject_initiation_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_hs_reject_initiation : composite_env_legal_fieldlist cenv_hs_reject_initiation.
Proof. rewrite cenv_hs_reject_initiation_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_hs_reject_initiation : composite_env_complete_legal_cosu_type cenv_hs_reject_initiation.
Proof. rewrite cenv_hs_reject_initiation_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_hs_reject_initiation : hardware_alignof_env_consistent cenv_hs_reject_initiation ha_hs_reject_initiation.
Proof. rewrite cenv_hs_reject_initiation_eq, ha_hs_reject_initiation_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_hs_reject_initiation : hardware_alignof_env_complete cenv_hs_reject_initiation ha_hs_reject_initiation.
Proof. rewrite cenv_hs_reject_initiation_eq, ha_hs_reject_initiation_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_hs_reject_initiation : legal_alignas_env_consistent cenv_hs_reject_initiation ha_hs_reject_initiation la_hs_reject_initiation.
Proof. rewrite cenv_hs_reject_initiation_eq, ha_hs_reject_initiation_eq, la_hs_reject_initiation_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_hs_reject_initiation : legal_alignas_env_complete cenv_hs_reject_initiation la_hs_reject_initiation.
Proof. rewrite cenv_hs_reject_initiation_eq, la_hs_reject_initiation_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_hs_reject_initiation : legal_alignas_env_sound cenv_hs_reject_initiation ha_hs_reject_initiation la_hs_reject_initiation.
Proof. rewrite cenv_hs_reject_initiation_eq, ha_hs_reject_initiation_eq, la_hs_reject_initiation_eq; apply la_env_cs_sound. Qed.

Definition W_hs_reject_initiation : compspecs :=
  {| cenv_cs := cenv_hs_reject_initiation; cenv_consistent := cenv_consistent_hs_reject_initiation;
     cenv_legal_fieldlist := cenv_legal_fieldlist_hs_reject_initiation; cenv_legal_su := cenv_legal_su_hs_reject_initiation;
     ha_env_cs := ha_hs_reject_initiation; ha_env_cs_consistent := ha_env_consistent_hs_reject_initiation;
     ha_env_cs_complete := ha_env_complete_hs_reject_initiation; la_env_cs := la_hs_reject_initiation;
     la_env_cs_consistent := la_env_consistent_hs_reject_initiation; la_env_cs_complete := la_env_complete_hs_reject_initiation;
     la_env_cs_sound := la_env_sound_hs_reject_initiation |}.

Lemma W_hs_reject_initiation_eq :
  W_hs_reject_initiation = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.hs_reject_initiation.whole_prog)
               (proj2 world_OK_whole_hs_reject_initiation).
Proof.
transitivity W0_hs_reject_initiation.
- apply compspecs_ext; [apply cenv_hs_reject_initiation_eq | apply ha_hs_reject_initiation_eq | apply la_hs_reject_initiation_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.

Lemma cbc_hs_reject_initiation : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env WgNoise.contracts.hs_reject_initiation.whole_prog)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.hs_reject_initiation.whole_prog) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma world_ok_hs_reject_initiation :
  Forall (fun cs => cspecs_sub cs W_hs_reject_initiation) (WgNoise.contracts.hs_reject_initiation.Harness.CS :: hs_unit_cs).
Proof. rewrite W_hs_reject_initiation_eq; repeat constructor; apply world_cspecs_sub; vm_refl. Qed.

(* ---------- hs_reject_response ---------- *)
Lemma world_OK_H_hs_reject_response : QPprogram_OK WgNoise.contracts.hs_reject_response.Harness.qp.
Proof. prove_unit_OK WgNoise.contracts.hs_reject_response.Harness.CS. Qed.
Lemma world_OK_link_Libc_hs_reject_response : QPprogram_OK WgNoise.contracts.hs_reject_response.link_Libc.
Proof. exact world_OK_hs_link_Libc. Qed.
Lemma world_OK_whole_hs_reject_response : QPprogram_OK WgNoise.contracts.hs_reject_response.whole_prog.
Proof. link_OK WgNoise.contracts.hs_reject_response.Harness.qp WgNoise.contracts.hs_reject_response.link_Libc world_OK_H_hs_reject_response world_OK_link_Libc_hs_reject_response. Qed.
Definition ce_hs_reject_response : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.hs_reject_response.whole_prog) in exact x).
Lemma OKce_hs_reject_response : QPcompspecs_OK ce_hs_reject_response. Proof. exact (proj2 world_OK_whole_hs_reject_response). Qed.
Definition W0_hs_reject_response : compspecs := compspecs_of_QPcomposite_env ce_hs_reject_response OKce_hs_reject_response.
Definition cenv_hs_reject_response : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_hs_reject_response) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_hs_reject_response : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_hs_reject_response) in exact x).
Definition la_hs_reject_response : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_hs_reject_response) in exact x).
Lemma cenv_hs_reject_response_eq : cenv_hs_reject_response = @cenv_cs W0_hs_reject_response.
Proof. unfold W0_hs_reject_response; destruct (QPcompspecs_OK_e _ OKce_hs_reject_response) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_hs_reject_response_eq : ha_hs_reject_response = @ha_env_cs W0_hs_reject_response.
Proof. unfold W0_hs_reject_response; destruct (QPcompspecs_OK_e _ OKce_hs_reject_response) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_hs_reject_response_eq : la_hs_reject_response = @la_env_cs W0_hs_reject_response.
Proof. unfold W0_hs_reject_response; destruct (QPcompspecs_OK_e _ OKce_hs_reject_response) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_hs_reject_response : composite_env_consistent cenv_hs_reject_response.
Proof. rewrite cenv_hs_reject_response_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_hs_reject_response : composite_env_legal_fieldlist cenv_hs_reject_response.
Proof. rewrite cenv_hs_reject_response_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_hs_reject_response : composite_env_complete_legal_cosu_type cenv_hs_reject_response.
Proof. rewrite cenv_hs_reject_response_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_hs_reject_response : hardware_alignof_env_consistent cenv_hs_reject_response ha_hs_reject_response.
Proof. rewrite cenv_hs_reject_response_eq, ha_hs_reject_response_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_hs_reject_response : hardware_alignof_env_complete cenv_hs_reject_response ha_hs_reject_response.
Proof. rewrite cenv_hs_reject_response_eq, ha_hs_reject_response_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_hs_reject_response : legal_alignas_env_consistent cenv_hs_reject_response ha_hs_reject_response la_hs_reject_response.
Proof. rewrite cenv_hs_reject_response_eq, ha_hs_reject_response_eq, la_hs_reject_response_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_hs_reject_response : legal_alignas_env_complete cenv_hs_reject_response la_hs_reject_response.
Proof. rewrite cenv_hs_reject_response_eq, la_hs_reject_response_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_hs_reject_response : legal_alignas_env_sound cenv_hs_reject_response ha_hs_reject_response la_hs_reject_response.
Proof. rewrite cenv_hs_reject_response_eq, ha_hs_reject_response_eq, la_hs_reject_response_eq; apply la_env_cs_sound. Qed.

Definition W_hs_reject_response : compspecs :=
  {| cenv_cs := cenv_hs_reject_response; cenv_consistent := cenv_consistent_hs_reject_response;
     cenv_legal_fieldlist := cenv_legal_fieldlist_hs_reject_response; cenv_legal_su := cenv_legal_su_hs_reject_response;
     ha_env_cs := ha_hs_reject_response; ha_env_cs_consistent := ha_env_consistent_hs_reject_response;
     ha_env_cs_complete := ha_env_complete_hs_reject_response; la_env_cs := la_hs_reject_response;
     la_env_cs_consistent := la_env_consistent_hs_reject_response; la_env_cs_complete := la_env_complete_hs_reject_response;
     la_env_cs_sound := la_env_sound_hs_reject_response |}.

Lemma W_hs_reject_response_eq :
  W_hs_reject_response = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.hs_reject_response.whole_prog)
               (proj2 world_OK_whole_hs_reject_response).
Proof.
transitivity W0_hs_reject_response.
- apply compspecs_ext; [apply cenv_hs_reject_response_eq | apply ha_hs_reject_response_eq | apply la_hs_reject_response_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.

Lemma cbc_hs_reject_response : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env WgNoise.contracts.hs_reject_response.whole_prog)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.hs_reject_response.whole_prog) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma world_ok_hs_reject_response :
  Forall (fun cs => cspecs_sub cs W_hs_reject_response) (WgNoise.contracts.hs_reject_response.Harness.CS :: hs_unit_cs).
Proof. rewrite W_hs_reject_response_eq; repeat constructor; apply world_cspecs_sub; vm_refl. Qed.

(* ---------- hs_replay_initiation ---------- *)
Lemma world_OK_H_hs_replay_initiation : QPprogram_OK WgNoise.contracts.hs_replay_initiation.Harness.qp.
Proof. prove_unit_OK WgNoise.contracts.hs_replay_initiation.Harness.CS. Qed.
Lemma world_OK_link_Libc_hs_replay_initiation : QPprogram_OK WgNoise.contracts.hs_replay_initiation.link_Libc.
Proof. exact world_OK_hs_link_Libc. Qed.
Lemma world_OK_whole_hs_replay_initiation : QPprogram_OK WgNoise.contracts.hs_replay_initiation.whole_prog.
Proof. link_OK WgNoise.contracts.hs_replay_initiation.Harness.qp WgNoise.contracts.hs_replay_initiation.link_Libc world_OK_H_hs_replay_initiation world_OK_link_Libc_hs_replay_initiation. Qed.
Definition ce_hs_replay_initiation : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.hs_replay_initiation.whole_prog) in exact x).
Lemma OKce_hs_replay_initiation : QPcompspecs_OK ce_hs_replay_initiation. Proof. exact (proj2 world_OK_whole_hs_replay_initiation). Qed.
Definition W0_hs_replay_initiation : compspecs := compspecs_of_QPcomposite_env ce_hs_replay_initiation OKce_hs_replay_initiation.
Definition cenv_hs_replay_initiation : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_hs_replay_initiation) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_hs_replay_initiation : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_hs_replay_initiation) in exact x).
Definition la_hs_replay_initiation : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_hs_replay_initiation) in exact x).
Lemma cenv_hs_replay_initiation_eq : cenv_hs_replay_initiation = @cenv_cs W0_hs_replay_initiation.
Proof. unfold W0_hs_replay_initiation; destruct (QPcompspecs_OK_e _ OKce_hs_replay_initiation) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_hs_replay_initiation_eq : ha_hs_replay_initiation = @ha_env_cs W0_hs_replay_initiation.
Proof. unfold W0_hs_replay_initiation; destruct (QPcompspecs_OK_e _ OKce_hs_replay_initiation) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_hs_replay_initiation_eq : la_hs_replay_initiation = @la_env_cs W0_hs_replay_initiation.
Proof. unfold W0_hs_replay_initiation; destruct (QPcompspecs_OK_e _ OKce_hs_replay_initiation) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_hs_replay_initiation : composite_env_consistent cenv_hs_replay_initiation.
Proof. rewrite cenv_hs_replay_initiation_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_hs_replay_initiation : composite_env_legal_fieldlist cenv_hs_replay_initiation.
Proof. rewrite cenv_hs_replay_initiation_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_hs_replay_initiation : composite_env_complete_legal_cosu_type cenv_hs_replay_initiation.
Proof. rewrite cenv_hs_replay_initiation_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_hs_replay_initiation : hardware_alignof_env_consistent cenv_hs_replay_initiation ha_hs_replay_initiation.
Proof. rewrite cenv_hs_replay_initiation_eq, ha_hs_replay_initiation_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_hs_replay_initiation : hardware_alignof_env_complete cenv_hs_replay_initiation ha_hs_replay_initiation.
Proof. rewrite cenv_hs_replay_initiation_eq, ha_hs_replay_initiation_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_hs_replay_initiation : legal_alignas_env_consistent cenv_hs_replay_initiation ha_hs_replay_initiation la_hs_replay_initiation.
Proof. rewrite cenv_hs_replay_initiation_eq, ha_hs_replay_initiation_eq, la_hs_replay_initiation_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_hs_replay_initiation : legal_alignas_env_complete cenv_hs_replay_initiation la_hs_replay_initiation.
Proof. rewrite cenv_hs_replay_initiation_eq, la_hs_replay_initiation_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_hs_replay_initiation : legal_alignas_env_sound cenv_hs_replay_initiation ha_hs_replay_initiation la_hs_replay_initiation.
Proof. rewrite cenv_hs_replay_initiation_eq, ha_hs_replay_initiation_eq, la_hs_replay_initiation_eq; apply la_env_cs_sound. Qed.

Definition W_hs_replay_initiation : compspecs :=
  {| cenv_cs := cenv_hs_replay_initiation; cenv_consistent := cenv_consistent_hs_replay_initiation;
     cenv_legal_fieldlist := cenv_legal_fieldlist_hs_replay_initiation; cenv_legal_su := cenv_legal_su_hs_replay_initiation;
     ha_env_cs := ha_hs_replay_initiation; ha_env_cs_consistent := ha_env_consistent_hs_replay_initiation;
     ha_env_cs_complete := ha_env_complete_hs_replay_initiation; la_env_cs := la_hs_replay_initiation;
     la_env_cs_consistent := la_env_consistent_hs_replay_initiation; la_env_cs_complete := la_env_complete_hs_replay_initiation;
     la_env_cs_sound := la_env_sound_hs_replay_initiation |}.

Lemma W_hs_replay_initiation_eq :
  W_hs_replay_initiation = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.hs_replay_initiation.whole_prog)
               (proj2 world_OK_whole_hs_replay_initiation).
Proof.
transitivity W0_hs_replay_initiation.
- apply compspecs_ext; [apply cenv_hs_replay_initiation_eq | apply ha_hs_replay_initiation_eq | apply la_hs_replay_initiation_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.

Lemma cbc_hs_replay_initiation : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env WgNoise.contracts.hs_replay_initiation.whole_prog)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.hs_replay_initiation.whole_prog) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma world_ok_hs_replay_initiation :
  Forall (fun cs => cspecs_sub cs W_hs_replay_initiation) (WgNoise.contracts.hs_replay_initiation.Harness.CS :: hs_unit_cs).
Proof. rewrite W_hs_replay_initiation_eq; repeat constructor; apply world_cspecs_sub; vm_refl. Qed.

(* ---------- hs_response_state ---------- *)
Lemma world_OK_H_hs_response_state : QPprogram_OK WgNoise.contracts.hs_response_state.Harness.qp.
Proof. prove_unit_OK WgNoise.contracts.hs_response_state.Harness.CS. Qed.
Lemma world_OK_link_Libc_hs_response_state : QPprogram_OK WgNoise.contracts.hs_response_state.link_Libc.
Proof. exact world_OK_hs_link_Libc. Qed.
Lemma world_OK_whole_hs_response_state : QPprogram_OK WgNoise.contracts.hs_response_state.whole_prog.
Proof. link_OK WgNoise.contracts.hs_response_state.Harness.qp WgNoise.contracts.hs_response_state.link_Libc world_OK_H_hs_response_state world_OK_link_Libc_hs_response_state. Qed.
Definition ce_hs_response_state : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.hs_response_state.whole_prog) in exact x).
Lemma OKce_hs_response_state : QPcompspecs_OK ce_hs_response_state. Proof. exact (proj2 world_OK_whole_hs_response_state). Qed.
Definition W0_hs_response_state : compspecs := compspecs_of_QPcomposite_env ce_hs_response_state OKce_hs_response_state.
Definition cenv_hs_response_state : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_hs_response_state) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_hs_response_state : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_hs_response_state) in exact x).
Definition la_hs_response_state : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_hs_response_state) in exact x).
Lemma cenv_hs_response_state_eq : cenv_hs_response_state = @cenv_cs W0_hs_response_state.
Proof. unfold W0_hs_response_state; destruct (QPcompspecs_OK_e _ OKce_hs_response_state) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_hs_response_state_eq : ha_hs_response_state = @ha_env_cs W0_hs_response_state.
Proof. unfold W0_hs_response_state; destruct (QPcompspecs_OK_e _ OKce_hs_response_state) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_hs_response_state_eq : la_hs_response_state = @la_env_cs W0_hs_response_state.
Proof. unfold W0_hs_response_state; destruct (QPcompspecs_OK_e _ OKce_hs_response_state) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_hs_response_state : composite_env_consistent cenv_hs_response_state.
Proof. rewrite cenv_hs_response_state_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_hs_response_state : composite_env_legal_fieldlist cenv_hs_response_state.
Proof. rewrite cenv_hs_response_state_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_hs_response_state : composite_env_complete_legal_cosu_type cenv_hs_response_state.
Proof. rewrite cenv_hs_response_state_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_hs_response_state : hardware_alignof_env_consistent cenv_hs_response_state ha_hs_response_state.
Proof. rewrite cenv_hs_response_state_eq, ha_hs_response_state_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_hs_response_state : hardware_alignof_env_complete cenv_hs_response_state ha_hs_response_state.
Proof. rewrite cenv_hs_response_state_eq, ha_hs_response_state_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_hs_response_state : legal_alignas_env_consistent cenv_hs_response_state ha_hs_response_state la_hs_response_state.
Proof. rewrite cenv_hs_response_state_eq, ha_hs_response_state_eq, la_hs_response_state_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_hs_response_state : legal_alignas_env_complete cenv_hs_response_state la_hs_response_state.
Proof. rewrite cenv_hs_response_state_eq, la_hs_response_state_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_hs_response_state : legal_alignas_env_sound cenv_hs_response_state ha_hs_response_state la_hs_response_state.
Proof. rewrite cenv_hs_response_state_eq, ha_hs_response_state_eq, la_hs_response_state_eq; apply la_env_cs_sound. Qed.

Definition W_hs_response_state : compspecs :=
  {| cenv_cs := cenv_hs_response_state; cenv_consistent := cenv_consistent_hs_response_state;
     cenv_legal_fieldlist := cenv_legal_fieldlist_hs_response_state; cenv_legal_su := cenv_legal_su_hs_response_state;
     ha_env_cs := ha_hs_response_state; ha_env_cs_consistent := ha_env_consistent_hs_response_state;
     ha_env_cs_complete := ha_env_complete_hs_response_state; la_env_cs := la_hs_response_state;
     la_env_cs_consistent := la_env_consistent_hs_response_state; la_env_cs_complete := la_env_complete_hs_response_state;
     la_env_cs_sound := la_env_sound_hs_response_state |}.

Lemma W_hs_response_state_eq :
  W_hs_response_state = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.hs_response_state.whole_prog)
               (proj2 world_OK_whole_hs_response_state).
Proof.
transitivity W0_hs_response_state.
- apply compspecs_ext; [apply cenv_hs_response_state_eq | apply ha_hs_response_state_eq | apply la_hs_response_state_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.

Lemma cbc_hs_response_state : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env WgNoise.contracts.hs_response_state.whole_prog)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.hs_response_state.whole_prog) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma world_ok_hs_response_state :
  Forall (fun cs => cspecs_sub cs W_hs_response_state) (WgNoise.contracts.hs_response_state.Harness.CS :: hs_unit_cs).
Proof. rewrite W_hs_response_state_eq; repeat constructor; apply world_cspecs_sub; vm_refl. Qed.

(* ---------- hs_session_erases ---------- *)
Lemma world_OK_H_hs_session_erases : QPprogram_OK WgNoise.contracts.hs_session_erases.Harness.qp.
Proof. prove_unit_OK WgNoise.contracts.hs_session_erases.Harness.CS. Qed.
Lemma world_OK_link_Libc_hs_session_erases : QPprogram_OK WgNoise.contracts.hs_session_erases.link_Libc.
Proof. exact world_OK_hs_link_Libc. Qed.
Lemma world_OK_whole_hs_session_erases : QPprogram_OK WgNoise.contracts.hs_session_erases.whole_prog.
Proof. link_OK WgNoise.contracts.hs_session_erases.Harness.qp WgNoise.contracts.hs_session_erases.link_Libc world_OK_H_hs_session_erases world_OK_link_Libc_hs_session_erases. Qed.
Definition ce_hs_session_erases : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.hs_session_erases.whole_prog) in exact x).
Lemma OKce_hs_session_erases : QPcompspecs_OK ce_hs_session_erases. Proof. exact (proj2 world_OK_whole_hs_session_erases). Qed.
Definition W0_hs_session_erases : compspecs := compspecs_of_QPcomposite_env ce_hs_session_erases OKce_hs_session_erases.
Definition cenv_hs_session_erases : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_hs_session_erases) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_hs_session_erases : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_hs_session_erases) in exact x).
Definition la_hs_session_erases : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_hs_session_erases) in exact x).
Lemma cenv_hs_session_erases_eq : cenv_hs_session_erases = @cenv_cs W0_hs_session_erases.
Proof. unfold W0_hs_session_erases; destruct (QPcompspecs_OK_e _ OKce_hs_session_erases) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_hs_session_erases_eq : ha_hs_session_erases = @ha_env_cs W0_hs_session_erases.
Proof. unfold W0_hs_session_erases; destruct (QPcompspecs_OK_e _ OKce_hs_session_erases) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_hs_session_erases_eq : la_hs_session_erases = @la_env_cs W0_hs_session_erases.
Proof. unfold W0_hs_session_erases; destruct (QPcompspecs_OK_e _ OKce_hs_session_erases) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_hs_session_erases : composite_env_consistent cenv_hs_session_erases.
Proof. rewrite cenv_hs_session_erases_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_hs_session_erases : composite_env_legal_fieldlist cenv_hs_session_erases.
Proof. rewrite cenv_hs_session_erases_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_hs_session_erases : composite_env_complete_legal_cosu_type cenv_hs_session_erases.
Proof. rewrite cenv_hs_session_erases_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_hs_session_erases : hardware_alignof_env_consistent cenv_hs_session_erases ha_hs_session_erases.
Proof. rewrite cenv_hs_session_erases_eq, ha_hs_session_erases_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_hs_session_erases : hardware_alignof_env_complete cenv_hs_session_erases ha_hs_session_erases.
Proof. rewrite cenv_hs_session_erases_eq, ha_hs_session_erases_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_hs_session_erases : legal_alignas_env_consistent cenv_hs_session_erases ha_hs_session_erases la_hs_session_erases.
Proof. rewrite cenv_hs_session_erases_eq, ha_hs_session_erases_eq, la_hs_session_erases_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_hs_session_erases : legal_alignas_env_complete cenv_hs_session_erases la_hs_session_erases.
Proof. rewrite cenv_hs_session_erases_eq, la_hs_session_erases_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_hs_session_erases : legal_alignas_env_sound cenv_hs_session_erases ha_hs_session_erases la_hs_session_erases.
Proof. rewrite cenv_hs_session_erases_eq, ha_hs_session_erases_eq, la_hs_session_erases_eq; apply la_env_cs_sound. Qed.

Definition W_hs_session_erases : compspecs :=
  {| cenv_cs := cenv_hs_session_erases; cenv_consistent := cenv_consistent_hs_session_erases;
     cenv_legal_fieldlist := cenv_legal_fieldlist_hs_session_erases; cenv_legal_su := cenv_legal_su_hs_session_erases;
     ha_env_cs := ha_hs_session_erases; ha_env_cs_consistent := ha_env_consistent_hs_session_erases;
     ha_env_cs_complete := ha_env_complete_hs_session_erases; la_env_cs := la_hs_session_erases;
     la_env_cs_consistent := la_env_consistent_hs_session_erases; la_env_cs_complete := la_env_complete_hs_session_erases;
     la_env_cs_sound := la_env_sound_hs_session_erases |}.

Lemma W_hs_session_erases_eq :
  W_hs_session_erases = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.hs_session_erases.whole_prog)
               (proj2 world_OK_whole_hs_session_erases).
Proof.
transitivity W0_hs_session_erases.
- apply compspecs_ext; [apply cenv_hs_session_erases_eq | apply ha_hs_session_erases_eq | apply la_hs_session_erases_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.

Lemma cbc_hs_session_erases : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env WgNoise.contracts.hs_session_erases.whole_prog)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.hs_session_erases.whole_prog) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma world_ok_hs_session_erases :
  Forall (fun cs => cspecs_sub cs W_hs_session_erases) (WgNoise.contracts.hs_session_erases.Harness.CS :: hs_unit_cs).
Proof. rewrite W_hs_session_erases_eq; repeat constructor; apply world_cspecs_sub; vm_refl. Qed.

(* ---------- hs_stale_response ---------- *)
Lemma world_OK_H_hs_stale_response : QPprogram_OK WgNoise.contracts.hs_stale_response.Harness.qp.
Proof. prove_unit_OK WgNoise.contracts.hs_stale_response.Harness.CS. Qed.
Lemma world_OK_link_Libc_hs_stale_response : QPprogram_OK WgNoise.contracts.hs_stale_response.link_Libc.
Proof. exact world_OK_hs_link_Libc. Qed.
Lemma world_OK_whole_hs_stale_response : QPprogram_OK WgNoise.contracts.hs_stale_response.whole_prog.
Proof. link_OK WgNoise.contracts.hs_stale_response.Harness.qp WgNoise.contracts.hs_stale_response.link_Libc world_OK_H_hs_stale_response world_OK_link_Libc_hs_stale_response. Qed.
Definition ce_hs_stale_response : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.hs_stale_response.whole_prog) in exact x).
Lemma OKce_hs_stale_response : QPcompspecs_OK ce_hs_stale_response. Proof. exact (proj2 world_OK_whole_hs_stale_response). Qed.
Definition W0_hs_stale_response : compspecs := compspecs_of_QPcomposite_env ce_hs_stale_response OKce_hs_stale_response.
Definition cenv_hs_stale_response : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_hs_stale_response) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_hs_stale_response : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_hs_stale_response) in exact x).
Definition la_hs_stale_response : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_hs_stale_response) in exact x).
Lemma cenv_hs_stale_response_eq : cenv_hs_stale_response = @cenv_cs W0_hs_stale_response.
Proof. unfold W0_hs_stale_response; destruct (QPcompspecs_OK_e _ OKce_hs_stale_response) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_hs_stale_response_eq : ha_hs_stale_response = @ha_env_cs W0_hs_stale_response.
Proof. unfold W0_hs_stale_response; destruct (QPcompspecs_OK_e _ OKce_hs_stale_response) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_hs_stale_response_eq : la_hs_stale_response = @la_env_cs W0_hs_stale_response.
Proof. unfold W0_hs_stale_response; destruct (QPcompspecs_OK_e _ OKce_hs_stale_response) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_hs_stale_response : composite_env_consistent cenv_hs_stale_response.
Proof. rewrite cenv_hs_stale_response_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_hs_stale_response : composite_env_legal_fieldlist cenv_hs_stale_response.
Proof. rewrite cenv_hs_stale_response_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_hs_stale_response : composite_env_complete_legal_cosu_type cenv_hs_stale_response.
Proof. rewrite cenv_hs_stale_response_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_hs_stale_response : hardware_alignof_env_consistent cenv_hs_stale_response ha_hs_stale_response.
Proof. rewrite cenv_hs_stale_response_eq, ha_hs_stale_response_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_hs_stale_response : hardware_alignof_env_complete cenv_hs_stale_response ha_hs_stale_response.
Proof. rewrite cenv_hs_stale_response_eq, ha_hs_stale_response_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_hs_stale_response : legal_alignas_env_consistent cenv_hs_stale_response ha_hs_stale_response la_hs_stale_response.
Proof. rewrite cenv_hs_stale_response_eq, ha_hs_stale_response_eq, la_hs_stale_response_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_hs_stale_response : legal_alignas_env_complete cenv_hs_stale_response la_hs_stale_response.
Proof. rewrite cenv_hs_stale_response_eq, la_hs_stale_response_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_hs_stale_response : legal_alignas_env_sound cenv_hs_stale_response ha_hs_stale_response la_hs_stale_response.
Proof. rewrite cenv_hs_stale_response_eq, ha_hs_stale_response_eq, la_hs_stale_response_eq; apply la_env_cs_sound. Qed.

Definition W_hs_stale_response : compspecs :=
  {| cenv_cs := cenv_hs_stale_response; cenv_consistent := cenv_consistent_hs_stale_response;
     cenv_legal_fieldlist := cenv_legal_fieldlist_hs_stale_response; cenv_legal_su := cenv_legal_su_hs_stale_response;
     ha_env_cs := ha_hs_stale_response; ha_env_cs_consistent := ha_env_consistent_hs_stale_response;
     ha_env_cs_complete := ha_env_complete_hs_stale_response; la_env_cs := la_hs_stale_response;
     la_env_cs_consistent := la_env_consistent_hs_stale_response; la_env_cs_complete := la_env_complete_hs_stale_response;
     la_env_cs_sound := la_env_sound_hs_stale_response |}.

Lemma W_hs_stale_response_eq :
  W_hs_stale_response = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.hs_stale_response.whole_prog)
               (proj2 world_OK_whole_hs_stale_response).
Proof.
transitivity W0_hs_stale_response.
- apply compspecs_ext; [apply cenv_hs_stale_response_eq | apply ha_hs_stale_response_eq | apply la_hs_stale_response_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.

Lemma cbc_hs_stale_response : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env WgNoise.contracts.hs_stale_response.whole_prog)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.hs_stale_response.whole_prog) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma world_ok_hs_stale_response :
  Forall (fun cs => cspecs_sub cs W_hs_stale_response) (WgNoise.contracts.hs_stale_response.Harness.CS :: hs_unit_cs).
Proof. rewrite W_hs_stale_response_eq; repeat constructor; apply world_cspecs_sub; vm_refl. Qed.
