(* the worlds of the 12 laws of suite.
   The worlds: for each law, the compspecs of its whole program.

   harness_safe p asks for semax_prog in the compspecs of p's composite environment; the harness-level proofs
   (main and the harness's own functions) and the specifications that mention malloc tokens are stated in it.
   W_<law> is that compspecs, defined so that it COMPUTES (sizeof, field offsets, data_at of the structs
   reduce as in a unit's compspecs); every unit's compspecs and the harness's are included in it, so that
   body proofs in a unit's compspecs lift (semax_body_cenv_sub).

   W_<law> and world_ok_<law> below are proved (no placeholders). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.contracts.x_consume_initiation_any.
Require WgNoise.contracts.x_consume_response_any.
Require WgNoise.contracts.x_cookie_mac.
Require WgNoise.contracts.x_cookie_reply.
Require WgNoise.contracts.x_counter.
Require WgNoise.contracts.x_create_any.
Require WgNoise.contracts.x_handshake.
Require WgNoise.contracts.x_keypairs.
Require WgNoise.contracts.x_prim_aead.
Require WgNoise.contracts.x_prim_blake2s.
Require WgNoise.contracts.x_prim_poly1305.
Require WgNoise.contracts.x_replay.

Definition all_unit_cs : list compspecs :=
  [Noise.CS; Cookie.CS; Counter.CS; Blake2s.CS; Chacha.CS; ChachaBlock.CS; Poly1305.CS; Poly1305Donna32.CS;
   Chacha20poly1305.CS; Curve25519.CS; Curve25519Fiat32.CS; Shim.CS; Libc.CS; Malloc.CS].

(* W is the compspecs of p's composite environment (the one harness_safe p needs), and includes the harness's
   and every unit's compspecs *)
Definition world_ok (p: QP.program function) (Hcs: compspecs) (W: compspecs) : Prop :=
  exists OK: QPprogram_OK p,
    W = compspecs_of_QPcomposite_env (QP.prog_comp_env p) (proj2 OK) /\
    build_composite_env
      (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) [])) =
    Errors.OK (composite_env_of_QPcomposite_env (QP.prog_comp_env p) (projT1 (proj2 OK))) /\
    Forall (fun cs => cspecs_sub cs W) (Hcs :: all_unit_cs).

(* ---------------------------------------------------------------------------------------------------------
   How the worlds are built.

   1. QPprogram_OK of every unit (as mkComponent does) and of every link step (QPlink_progs_OK; each link is
      checked by vm_compute). The 12 contracts link the units in the same order, so the chain up to
      link_Malloc is proved once (on counter's copy) and every whole_prog is Harness.qp linked with it.
   2. The world's composite environment is rebuilt as a LITERAL composite_env (VST's make_composite_env, then
      hnf; simpl, exactly as make_compspecs does for the units: without the simpl the env stays a chain of
      PTree.set and every VST tactic pays for it), with literal ha/la environments; the compspecs fields are opaque
      lemmas (constants without arguments), transported from the opaque QPcompspecs_OK of the link. So
      W_<law> computes like a unit's compspecs (cbv, simpl, reflexivity on sizeof, field_offset, reptype).
   3. W_<law> is equal (propositionally, by proof irrelevance) to compspecs_of_QPcomposite_env of the
      whole program, which is what harness_safe's semax_prog uses.
   --------------------------------------------------------------------------------------------------------- *)

Ltac vm_refl := match goal with |- _ = ?r => vm_cast_no_check (eq_refl r) end.

Ltac prove_unit_OK cs :=
  split; [apply compute_list_norepet_e; reflexivity
         | apply (@QPcompspecs_OK_i cs); repeat constructor].

Ltac link_OK p1 p2 OK1 OK2 :=
  refine (QPlink_progs_OK p1 p2 _ _ OK1 OK2); vm_refl.

Lemma world_OK_Noise : QPprogram_OK Noise.qp. Proof. prove_unit_OK Noise.CS. Qed.
Lemma world_OK_Cookie : QPprogram_OK Cookie.qp. Proof. prove_unit_OK Cookie.CS. Qed.
Lemma world_OK_Counter : QPprogram_OK Counter.qp. Proof. prove_unit_OK Counter.CS. Qed.
Lemma world_OK_Blake2s : QPprogram_OK Blake2s.qp. Proof. prove_unit_OK Blake2s.CS. Qed.
Lemma world_OK_Chacha : QPprogram_OK Chacha.qp. Proof. prove_unit_OK Chacha.CS. Qed.
Lemma world_OK_ChachaBlock : QPprogram_OK ChachaBlock.qp. Proof. prove_unit_OK ChachaBlock.CS. Qed.
Lemma world_OK_Poly1305 : QPprogram_OK Poly1305.qp. Proof. prove_unit_OK Poly1305.CS. Qed.
Lemma world_OK_Poly1305Donna32 : QPprogram_OK Poly1305Donna32.qp. Proof. prove_unit_OK Poly1305Donna32.CS. Qed.
Lemma world_OK_Chacha20poly1305 : QPprogram_OK Chacha20poly1305.qp. Proof. prove_unit_OK Chacha20poly1305.CS. Qed.
Lemma world_OK_Curve25519 : QPprogram_OK Curve25519.qp. Proof. prove_unit_OK Curve25519.CS. Qed.
Lemma world_OK_Curve25519Fiat32 : QPprogram_OK Curve25519Fiat32.qp. Proof. prove_unit_OK Curve25519Fiat32.CS. Qed.
Lemma world_OK_Shim : QPprogram_OK Shim.qp. Proof. prove_unit_OK Shim.CS. Qed.
Lemma world_OK_Libc : QPprogram_OK Libc.qp. Proof. prove_unit_OK Libc.CS. Qed.
Lemma world_OK_Malloc : QPprogram_OK Malloc.qp. Proof. prove_unit_OK Malloc.CS. Qed.
Lemma world_OK_link_Cookie : QPprogram_OK WgNoise.contracts.x_counter.link_Cookie.
Proof. link_OK Cookie.qp Noise.qp world_OK_Cookie world_OK_Noise. Qed.
Lemma world_OK_link_Counter : QPprogram_OK WgNoise.contracts.x_counter.link_Counter.
Proof. link_OK Counter.qp WgNoise.contracts.x_counter.link_Cookie world_OK_Counter world_OK_link_Cookie. Qed.
Lemma world_OK_link_Blake2s : QPprogram_OK WgNoise.contracts.x_counter.link_Blake2s.
Proof. link_OK Blake2s.qp WgNoise.contracts.x_counter.link_Counter world_OK_Blake2s world_OK_link_Counter. Qed.
Lemma world_OK_link_Chacha : QPprogram_OK WgNoise.contracts.x_counter.link_Chacha.
Proof. link_OK Chacha.qp WgNoise.contracts.x_counter.link_Blake2s world_OK_Chacha world_OK_link_Blake2s. Qed.
Lemma world_OK_link_ChachaBlock : QPprogram_OK WgNoise.contracts.x_counter.link_ChachaBlock.
Proof. link_OK ChachaBlock.qp WgNoise.contracts.x_counter.link_Chacha world_OK_ChachaBlock world_OK_link_Chacha. Qed.
Lemma world_OK_link_Poly1305 : QPprogram_OK WgNoise.contracts.x_counter.link_Poly1305.
Proof. link_OK Poly1305.qp WgNoise.contracts.x_counter.link_ChachaBlock world_OK_Poly1305 world_OK_link_ChachaBlock. Qed.
Lemma world_OK_link_Poly1305Donna32 : QPprogram_OK WgNoise.contracts.x_counter.link_Poly1305Donna32.
Proof. link_OK Poly1305Donna32.qp WgNoise.contracts.x_counter.link_Poly1305 world_OK_Poly1305Donna32 world_OK_link_Poly1305. Qed.
Lemma world_OK_link_Chacha20poly1305 : QPprogram_OK WgNoise.contracts.x_counter.link_Chacha20poly1305.
Proof. link_OK Chacha20poly1305.qp WgNoise.contracts.x_counter.link_Poly1305Donna32 world_OK_Chacha20poly1305 world_OK_link_Poly1305Donna32. Qed.
Lemma world_OK_link_Curve25519 : QPprogram_OK WgNoise.contracts.x_counter.link_Curve25519.
Proof. link_OK Curve25519.qp WgNoise.contracts.x_counter.link_Chacha20poly1305 world_OK_Curve25519 world_OK_link_Chacha20poly1305. Qed.
Lemma world_OK_link_Curve25519Fiat32 : QPprogram_OK WgNoise.contracts.x_counter.link_Curve25519Fiat32.
Proof. link_OK Curve25519Fiat32.qp WgNoise.contracts.x_counter.link_Curve25519 world_OK_Curve25519Fiat32 world_OK_link_Curve25519. Qed.
Lemma world_OK_link_Shim : QPprogram_OK WgNoise.contracts.x_counter.link_Shim.
Proof. link_OK Shim.qp WgNoise.contracts.x_counter.link_Curve25519Fiat32 world_OK_Shim world_OK_link_Curve25519Fiat32. Qed.
Lemma world_OK_link_Libc : QPprogram_OK WgNoise.contracts.x_counter.link_Libc.
Proof. link_OK Libc.qp WgNoise.contracts.x_counter.link_Shim world_OK_Libc world_OK_link_Shim. Qed.
Lemma world_OK_link_Malloc : QPprogram_OK WgNoise.contracts.x_counter.link_Malloc.
Proof. link_OK Malloc.qp WgNoise.contracts.x_counter.link_Libc world_OK_Malloc world_OK_link_Libc. Qed.

Lemma compspecs_of_QPcomposite_env_irr ce (H1 H2: QPcompspecs_OK ce) :
  compspecs_of_QPcomposite_env ce H1 = compspecs_of_QPcomposite_env ce H2.
Proof. f_equal; apply proof_irr. Qed.

Lemma world_cs_eq_QP (cs: compspecs)
  (OK1: QPcompspecs_OK (QPcomposite_env_of_composite_env (@cenv_cs cs) (@ha_env_cs cs) (@la_env_cs cs))) :
  cs = compspecs_of_QPcomposite_env _ OK1.
Proof.
pose proof (PTree_samedom_ha cs). pose proof (PTree_samedom_la cs).
destruct OK1 as [? [? [? [? [? [? ?]]]]]].
apply compspecs_ext; simpl.
- rewrite composite_env_of_QPcomposite_env_of_composite_env; auto.
- unfold QPcomposite_env_of_composite_env.
  rewrite PTree_map1_map3 with (e:=0); auto.
  symmetry; apply PTree_map3_2; auto.
- unfold QPcomposite_env_of_composite_env.
  rewrite PTree_map1_map3 with (e:=false); auto.
  symmetry; apply PTree_map3_3; auto.
Qed.

(* decidable inclusion of QP composite environments *)
Definition QPce_subb (a b : QP.composite_env) : bool :=
  forallb (fun ic => match Maps.PTree.get (fst ic) b with Some d => QPcomposite_eq (snd ic) d | None => false end)
    (Maps.PTree.elements a).

Lemma QPce_subb_e a b : QPce_subb a b = true -> PTree_sub a b.
Proof.
intros H i; unfold sub_option.
destruct (Maps.PTree.get i a) eqn:E; auto.
apply Maps.PTree.elements_correct in E.
unfold QPce_subb in H; rewrite forallb_forall in H.
specialize (H _ E); simpl in H.
destruct (Maps.PTree.get i b); try discriminate.
apply QPcomposite_eq_e in H; subst; auto.
Qed.

Lemma world_cspecs_sub (cs: compspecs) ce (OK: QPcompspecs_OK ce) :
  QPce_subb (QPcomposite_env_of_composite_env (@cenv_cs cs) (@ha_env_cs cs) (@la_env_cs cs)) ce = true ->
  cspecs_sub cs (compspecs_of_QPcomposite_env ce OK).
Proof.
intro H.
pose (OK1 := QPcompspecs_OK_i (PTree_samedom_ha cs) (PTree_samedom_la cs)).
rewrite (world_cs_eq_QP cs OK1) at 1.
apply cspecs_sub_of_QPsub, QPce_subb_e, H.
Qed.

(* ---------- consume_initiation_any ---------- *)
Lemma world_OK_H_consume_initiation_any : QPprogram_OK WgNoise.contracts.x_consume_initiation_any.Harness.qp. Proof. prove_unit_OK WgNoise.contracts.x_consume_initiation_any.Harness.CS. Qed.
Lemma world_OK_whole_consume_initiation_any : QPprogram_OK WgNoise.contracts.x_consume_initiation_any.whole_prog.
Proof. link_OK WgNoise.contracts.x_consume_initiation_any.Harness.qp WgNoise.contracts.x_counter.link_Malloc world_OK_H_consume_initiation_any world_OK_link_Malloc. Qed.
Definition ce_consume_initiation_any : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.x_consume_initiation_any.whole_prog) in exact x).
Lemma OKce_consume_initiation_any : QPcompspecs_OK ce_consume_initiation_any. Proof. exact (proj2 world_OK_whole_consume_initiation_any). Qed.
Definition W0_consume_initiation_any : compspecs := compspecs_of_QPcomposite_env ce_consume_initiation_any OKce_consume_initiation_any.
Definition cenv_consume_initiation_any : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_consume_initiation_any) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_consume_initiation_any : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_consume_initiation_any) in exact x).
Definition la_consume_initiation_any : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_consume_initiation_any) in exact x).
Lemma cenv_consume_initiation_any_eq : cenv_consume_initiation_any = @cenv_cs W0_consume_initiation_any.
Proof. unfold W0_consume_initiation_any; destruct (QPcompspecs_OK_e _ OKce_consume_initiation_any) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_consume_initiation_any_eq : ha_consume_initiation_any = @ha_env_cs W0_consume_initiation_any.
Proof. unfold W0_consume_initiation_any; destruct (QPcompspecs_OK_e _ OKce_consume_initiation_any) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_consume_initiation_any_eq : la_consume_initiation_any = @la_env_cs W0_consume_initiation_any.
Proof. unfold W0_consume_initiation_any; destruct (QPcompspecs_OK_e _ OKce_consume_initiation_any) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_consume_initiation_any : composite_env_consistent cenv_consume_initiation_any.
Proof. rewrite cenv_consume_initiation_any_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_consume_initiation_any : composite_env_legal_fieldlist cenv_consume_initiation_any.
Proof. rewrite cenv_consume_initiation_any_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_consume_initiation_any : composite_env_complete_legal_cosu_type cenv_consume_initiation_any.
Proof. rewrite cenv_consume_initiation_any_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_consume_initiation_any : hardware_alignof_env_consistent cenv_consume_initiation_any ha_consume_initiation_any.
Proof. rewrite cenv_consume_initiation_any_eq, ha_consume_initiation_any_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_consume_initiation_any : hardware_alignof_env_complete cenv_consume_initiation_any ha_consume_initiation_any.
Proof. rewrite cenv_consume_initiation_any_eq, ha_consume_initiation_any_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_consume_initiation_any : legal_alignas_env_consistent cenv_consume_initiation_any ha_consume_initiation_any la_consume_initiation_any.
Proof. rewrite cenv_consume_initiation_any_eq, ha_consume_initiation_any_eq, la_consume_initiation_any_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_consume_initiation_any : legal_alignas_env_complete cenv_consume_initiation_any la_consume_initiation_any.
Proof. rewrite cenv_consume_initiation_any_eq, la_consume_initiation_any_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_consume_initiation_any : legal_alignas_env_sound cenv_consume_initiation_any ha_consume_initiation_any la_consume_initiation_any.
Proof. rewrite cenv_consume_initiation_any_eq, ha_consume_initiation_any_eq, la_consume_initiation_any_eq; apply la_env_cs_sound. Qed.

(* ---------- consume_response_any ---------- *)
Lemma world_OK_H_consume_response_any : QPprogram_OK WgNoise.contracts.x_consume_response_any.Harness.qp. Proof. prove_unit_OK WgNoise.contracts.x_consume_response_any.Harness.CS. Qed.
Lemma world_OK_whole_consume_response_any : QPprogram_OK WgNoise.contracts.x_consume_response_any.whole_prog.
Proof. link_OK WgNoise.contracts.x_consume_response_any.Harness.qp WgNoise.contracts.x_counter.link_Malloc world_OK_H_consume_response_any world_OK_link_Malloc. Qed.
Definition ce_consume_response_any : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.x_consume_response_any.whole_prog) in exact x).
Lemma OKce_consume_response_any : QPcompspecs_OK ce_consume_response_any. Proof. exact (proj2 world_OK_whole_consume_response_any). Qed.
Definition W0_consume_response_any : compspecs := compspecs_of_QPcomposite_env ce_consume_response_any OKce_consume_response_any.
Definition cenv_consume_response_any : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_consume_response_any) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_consume_response_any : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_consume_response_any) in exact x).
Definition la_consume_response_any : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_consume_response_any) in exact x).
Lemma cenv_consume_response_any_eq : cenv_consume_response_any = @cenv_cs W0_consume_response_any.
Proof. unfold W0_consume_response_any; destruct (QPcompspecs_OK_e _ OKce_consume_response_any) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_consume_response_any_eq : ha_consume_response_any = @ha_env_cs W0_consume_response_any.
Proof. unfold W0_consume_response_any; destruct (QPcompspecs_OK_e _ OKce_consume_response_any) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_consume_response_any_eq : la_consume_response_any = @la_env_cs W0_consume_response_any.
Proof. unfold W0_consume_response_any; destruct (QPcompspecs_OK_e _ OKce_consume_response_any) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_consume_response_any : composite_env_consistent cenv_consume_response_any.
Proof. rewrite cenv_consume_response_any_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_consume_response_any : composite_env_legal_fieldlist cenv_consume_response_any.
Proof. rewrite cenv_consume_response_any_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_consume_response_any : composite_env_complete_legal_cosu_type cenv_consume_response_any.
Proof. rewrite cenv_consume_response_any_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_consume_response_any : hardware_alignof_env_consistent cenv_consume_response_any ha_consume_response_any.
Proof. rewrite cenv_consume_response_any_eq, ha_consume_response_any_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_consume_response_any : hardware_alignof_env_complete cenv_consume_response_any ha_consume_response_any.
Proof. rewrite cenv_consume_response_any_eq, ha_consume_response_any_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_consume_response_any : legal_alignas_env_consistent cenv_consume_response_any ha_consume_response_any la_consume_response_any.
Proof. rewrite cenv_consume_response_any_eq, ha_consume_response_any_eq, la_consume_response_any_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_consume_response_any : legal_alignas_env_complete cenv_consume_response_any la_consume_response_any.
Proof. rewrite cenv_consume_response_any_eq, la_consume_response_any_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_consume_response_any : legal_alignas_env_sound cenv_consume_response_any ha_consume_response_any la_consume_response_any.
Proof. rewrite cenv_consume_response_any_eq, ha_consume_response_any_eq, la_consume_response_any_eq; apply la_env_cs_sound. Qed.

(* ---------- cookie_mac ---------- *)
Lemma world_OK_H_cookie_mac : QPprogram_OK WgNoise.contracts.x_cookie_mac.Harness.qp. Proof. prove_unit_OK WgNoise.contracts.x_cookie_mac.Harness.CS. Qed.
Lemma world_OK_whole_cookie_mac : QPprogram_OK WgNoise.contracts.x_cookie_mac.whole_prog.
Proof. link_OK WgNoise.contracts.x_cookie_mac.Harness.qp WgNoise.contracts.x_counter.link_Malloc world_OK_H_cookie_mac world_OK_link_Malloc. Qed.
Definition ce_cookie_mac : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.x_cookie_mac.whole_prog) in exact x).
Lemma OKce_cookie_mac : QPcompspecs_OK ce_cookie_mac. Proof. exact (proj2 world_OK_whole_cookie_mac). Qed.
Definition W0_cookie_mac : compspecs := compspecs_of_QPcomposite_env ce_cookie_mac OKce_cookie_mac.
Definition cenv_cookie_mac : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_cookie_mac) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_cookie_mac : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_cookie_mac) in exact x).
Definition la_cookie_mac : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_cookie_mac) in exact x).
Lemma cenv_cookie_mac_eq : cenv_cookie_mac = @cenv_cs W0_cookie_mac.
Proof. unfold W0_cookie_mac; destruct (QPcompspecs_OK_e _ OKce_cookie_mac) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_cookie_mac_eq : ha_cookie_mac = @ha_env_cs W0_cookie_mac.
Proof. unfold W0_cookie_mac; destruct (QPcompspecs_OK_e _ OKce_cookie_mac) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_cookie_mac_eq : la_cookie_mac = @la_env_cs W0_cookie_mac.
Proof. unfold W0_cookie_mac; destruct (QPcompspecs_OK_e _ OKce_cookie_mac) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_cookie_mac : composite_env_consistent cenv_cookie_mac.
Proof. rewrite cenv_cookie_mac_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_cookie_mac : composite_env_legal_fieldlist cenv_cookie_mac.
Proof. rewrite cenv_cookie_mac_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_cookie_mac : composite_env_complete_legal_cosu_type cenv_cookie_mac.
Proof. rewrite cenv_cookie_mac_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_cookie_mac : hardware_alignof_env_consistent cenv_cookie_mac ha_cookie_mac.
Proof. rewrite cenv_cookie_mac_eq, ha_cookie_mac_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_cookie_mac : hardware_alignof_env_complete cenv_cookie_mac ha_cookie_mac.
Proof. rewrite cenv_cookie_mac_eq, ha_cookie_mac_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_cookie_mac : legal_alignas_env_consistent cenv_cookie_mac ha_cookie_mac la_cookie_mac.
Proof. rewrite cenv_cookie_mac_eq, ha_cookie_mac_eq, la_cookie_mac_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_cookie_mac : legal_alignas_env_complete cenv_cookie_mac la_cookie_mac.
Proof. rewrite cenv_cookie_mac_eq, la_cookie_mac_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_cookie_mac : legal_alignas_env_sound cenv_cookie_mac ha_cookie_mac la_cookie_mac.
Proof. rewrite cenv_cookie_mac_eq, ha_cookie_mac_eq, la_cookie_mac_eq; apply la_env_cs_sound. Qed.

(* ---------- cookie_reply ---------- *)
Lemma world_OK_H_cookie_reply : QPprogram_OK WgNoise.contracts.x_cookie_reply.Harness.qp. Proof. prove_unit_OK WgNoise.contracts.x_cookie_reply.Harness.CS. Qed.
Lemma world_OK_whole_cookie_reply : QPprogram_OK WgNoise.contracts.x_cookie_reply.whole_prog.
Proof. link_OK WgNoise.contracts.x_cookie_reply.Harness.qp WgNoise.contracts.x_counter.link_Malloc world_OK_H_cookie_reply world_OK_link_Malloc. Qed.
Definition ce_cookie_reply : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.x_cookie_reply.whole_prog) in exact x).
Lemma OKce_cookie_reply : QPcompspecs_OK ce_cookie_reply. Proof. exact (proj2 world_OK_whole_cookie_reply). Qed.
Definition W0_cookie_reply : compspecs := compspecs_of_QPcomposite_env ce_cookie_reply OKce_cookie_reply.
Definition cenv_cookie_reply : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_cookie_reply) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_cookie_reply : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_cookie_reply) in exact x).
Definition la_cookie_reply : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_cookie_reply) in exact x).
Lemma cenv_cookie_reply_eq : cenv_cookie_reply = @cenv_cs W0_cookie_reply.
Proof. unfold W0_cookie_reply; destruct (QPcompspecs_OK_e _ OKce_cookie_reply) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_cookie_reply_eq : ha_cookie_reply = @ha_env_cs W0_cookie_reply.
Proof. unfold W0_cookie_reply; destruct (QPcompspecs_OK_e _ OKce_cookie_reply) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_cookie_reply_eq : la_cookie_reply = @la_env_cs W0_cookie_reply.
Proof. unfold W0_cookie_reply; destruct (QPcompspecs_OK_e _ OKce_cookie_reply) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_cookie_reply : composite_env_consistent cenv_cookie_reply.
Proof. rewrite cenv_cookie_reply_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_cookie_reply : composite_env_legal_fieldlist cenv_cookie_reply.
Proof. rewrite cenv_cookie_reply_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_cookie_reply : composite_env_complete_legal_cosu_type cenv_cookie_reply.
Proof. rewrite cenv_cookie_reply_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_cookie_reply : hardware_alignof_env_consistent cenv_cookie_reply ha_cookie_reply.
Proof. rewrite cenv_cookie_reply_eq, ha_cookie_reply_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_cookie_reply : hardware_alignof_env_complete cenv_cookie_reply ha_cookie_reply.
Proof. rewrite cenv_cookie_reply_eq, ha_cookie_reply_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_cookie_reply : legal_alignas_env_consistent cenv_cookie_reply ha_cookie_reply la_cookie_reply.
Proof. rewrite cenv_cookie_reply_eq, ha_cookie_reply_eq, la_cookie_reply_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_cookie_reply : legal_alignas_env_complete cenv_cookie_reply la_cookie_reply.
Proof. rewrite cenv_cookie_reply_eq, la_cookie_reply_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_cookie_reply : legal_alignas_env_sound cenv_cookie_reply ha_cookie_reply la_cookie_reply.
Proof. rewrite cenv_cookie_reply_eq, ha_cookie_reply_eq, la_cookie_reply_eq; apply la_env_cs_sound. Qed.

(* ---------- counter ---------- *)
Lemma world_OK_H_counter : QPprogram_OK WgNoise.contracts.x_counter.Harness.qp. Proof. prove_unit_OK WgNoise.contracts.x_counter.Harness.CS. Qed.
Lemma world_OK_whole_counter : QPprogram_OK WgNoise.contracts.x_counter.whole_prog.
Proof. link_OK WgNoise.contracts.x_counter.Harness.qp WgNoise.contracts.x_counter.link_Malloc world_OK_H_counter world_OK_link_Malloc. Qed.
Definition ce_counter : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.x_counter.whole_prog) in exact x).
Lemma OKce_counter : QPcompspecs_OK ce_counter. Proof. exact (proj2 world_OK_whole_counter). Qed.
Definition W0_counter : compspecs := compspecs_of_QPcomposite_env ce_counter OKce_counter.
Definition cenv_counter : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_counter) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_counter : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_counter) in exact x).
Definition la_counter : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_counter) in exact x).
Lemma cenv_counter_eq : cenv_counter = @cenv_cs W0_counter.
Proof. unfold W0_counter; destruct (QPcompspecs_OK_e _ OKce_counter) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_counter_eq : ha_counter = @ha_env_cs W0_counter.
Proof. unfold W0_counter; destruct (QPcompspecs_OK_e _ OKce_counter) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_counter_eq : la_counter = @la_env_cs W0_counter.
Proof. unfold W0_counter; destruct (QPcompspecs_OK_e _ OKce_counter) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_counter : composite_env_consistent cenv_counter.
Proof. rewrite cenv_counter_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_counter : composite_env_legal_fieldlist cenv_counter.
Proof. rewrite cenv_counter_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_counter : composite_env_complete_legal_cosu_type cenv_counter.
Proof. rewrite cenv_counter_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_counter : hardware_alignof_env_consistent cenv_counter ha_counter.
Proof. rewrite cenv_counter_eq, ha_counter_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_counter : hardware_alignof_env_complete cenv_counter ha_counter.
Proof. rewrite cenv_counter_eq, ha_counter_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_counter : legal_alignas_env_consistent cenv_counter ha_counter la_counter.
Proof. rewrite cenv_counter_eq, ha_counter_eq, la_counter_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_counter : legal_alignas_env_complete cenv_counter la_counter.
Proof. rewrite cenv_counter_eq, la_counter_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_counter : legal_alignas_env_sound cenv_counter ha_counter la_counter.
Proof. rewrite cenv_counter_eq, ha_counter_eq, la_counter_eq; apply la_env_cs_sound. Qed.

(* ---------- create_any ---------- *)
Lemma world_OK_H_create_any : QPprogram_OK WgNoise.contracts.x_create_any.Harness.qp. Proof. prove_unit_OK WgNoise.contracts.x_create_any.Harness.CS. Qed.
Lemma world_OK_whole_create_any : QPprogram_OK WgNoise.contracts.x_create_any.whole_prog.
Proof. link_OK WgNoise.contracts.x_create_any.Harness.qp WgNoise.contracts.x_counter.link_Malloc world_OK_H_create_any world_OK_link_Malloc. Qed.
Definition ce_create_any : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.x_create_any.whole_prog) in exact x).
Lemma OKce_create_any : QPcompspecs_OK ce_create_any. Proof. exact (proj2 world_OK_whole_create_any). Qed.
Definition W0_create_any : compspecs := compspecs_of_QPcomposite_env ce_create_any OKce_create_any.
Definition cenv_create_any : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_create_any) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_create_any : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_create_any) in exact x).
Definition la_create_any : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_create_any) in exact x).
Lemma cenv_create_any_eq : cenv_create_any = @cenv_cs W0_create_any.
Proof. unfold W0_create_any; destruct (QPcompspecs_OK_e _ OKce_create_any) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_create_any_eq : ha_create_any = @ha_env_cs W0_create_any.
Proof. unfold W0_create_any; destruct (QPcompspecs_OK_e _ OKce_create_any) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_create_any_eq : la_create_any = @la_env_cs W0_create_any.
Proof. unfold W0_create_any; destruct (QPcompspecs_OK_e _ OKce_create_any) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_create_any : composite_env_consistent cenv_create_any.
Proof. rewrite cenv_create_any_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_create_any : composite_env_legal_fieldlist cenv_create_any.
Proof. rewrite cenv_create_any_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_create_any : composite_env_complete_legal_cosu_type cenv_create_any.
Proof. rewrite cenv_create_any_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_create_any : hardware_alignof_env_consistent cenv_create_any ha_create_any.
Proof. rewrite cenv_create_any_eq, ha_create_any_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_create_any : hardware_alignof_env_complete cenv_create_any ha_create_any.
Proof. rewrite cenv_create_any_eq, ha_create_any_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_create_any : legal_alignas_env_consistent cenv_create_any ha_create_any la_create_any.
Proof. rewrite cenv_create_any_eq, ha_create_any_eq, la_create_any_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_create_any : legal_alignas_env_complete cenv_create_any la_create_any.
Proof. rewrite cenv_create_any_eq, la_create_any_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_create_any : legal_alignas_env_sound cenv_create_any ha_create_any la_create_any.
Proof. rewrite cenv_create_any_eq, ha_create_any_eq, la_create_any_eq; apply la_env_cs_sound. Qed.

(* ---------- handshake ---------- *)
Lemma world_OK_H_handshake : QPprogram_OK WgNoise.contracts.x_handshake.Harness.qp. Proof. prove_unit_OK WgNoise.contracts.x_handshake.Harness.CS. Qed.
Lemma world_OK_whole_handshake : QPprogram_OK WgNoise.contracts.x_handshake.whole_prog.
Proof. link_OK WgNoise.contracts.x_handshake.Harness.qp WgNoise.contracts.x_counter.link_Malloc world_OK_H_handshake world_OK_link_Malloc. Qed.
Definition ce_handshake : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.x_handshake.whole_prog) in exact x).
Lemma OKce_handshake : QPcompspecs_OK ce_handshake. Proof. exact (proj2 world_OK_whole_handshake). Qed.
Definition W0_handshake : compspecs := compspecs_of_QPcomposite_env ce_handshake OKce_handshake.
Definition cenv_handshake : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_handshake) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_handshake : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_handshake) in exact x).
Definition la_handshake : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_handshake) in exact x).
Lemma cenv_handshake_eq : cenv_handshake = @cenv_cs W0_handshake.
Proof. unfold W0_handshake; destruct (QPcompspecs_OK_e _ OKce_handshake) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_handshake_eq : ha_handshake = @ha_env_cs W0_handshake.
Proof. unfold W0_handshake; destruct (QPcompspecs_OK_e _ OKce_handshake) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_handshake_eq : la_handshake = @la_env_cs W0_handshake.
Proof. unfold W0_handshake; destruct (QPcompspecs_OK_e _ OKce_handshake) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_handshake : composite_env_consistent cenv_handshake.
Proof. rewrite cenv_handshake_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_handshake : composite_env_legal_fieldlist cenv_handshake.
Proof. rewrite cenv_handshake_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_handshake : composite_env_complete_legal_cosu_type cenv_handshake.
Proof. rewrite cenv_handshake_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_handshake : hardware_alignof_env_consistent cenv_handshake ha_handshake.
Proof. rewrite cenv_handshake_eq, ha_handshake_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_handshake : hardware_alignof_env_complete cenv_handshake ha_handshake.
Proof. rewrite cenv_handshake_eq, ha_handshake_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_handshake : legal_alignas_env_consistent cenv_handshake ha_handshake la_handshake.
Proof. rewrite cenv_handshake_eq, ha_handshake_eq, la_handshake_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_handshake : legal_alignas_env_complete cenv_handshake la_handshake.
Proof. rewrite cenv_handshake_eq, la_handshake_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_handshake : legal_alignas_env_sound cenv_handshake ha_handshake la_handshake.
Proof. rewrite cenv_handshake_eq, ha_handshake_eq, la_handshake_eq; apply la_env_cs_sound. Qed.

(* ---------- keypairs ---------- *)
Lemma world_OK_H_keypairs : QPprogram_OK WgNoise.contracts.x_keypairs.Harness.qp. Proof. prove_unit_OK WgNoise.contracts.x_keypairs.Harness.CS. Qed.
Lemma world_OK_whole_keypairs : QPprogram_OK WgNoise.contracts.x_keypairs.whole_prog.
Proof. link_OK WgNoise.contracts.x_keypairs.Harness.qp WgNoise.contracts.x_counter.link_Malloc world_OK_H_keypairs world_OK_link_Malloc. Qed.
Definition ce_keypairs : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.x_keypairs.whole_prog) in exact x).
Lemma OKce_keypairs : QPcompspecs_OK ce_keypairs. Proof. exact (proj2 world_OK_whole_keypairs). Qed.
Definition W0_keypairs : compspecs := compspecs_of_QPcomposite_env ce_keypairs OKce_keypairs.
Definition cenv_keypairs : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_keypairs) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_keypairs : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_keypairs) in exact x).
Definition la_keypairs : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_keypairs) in exact x).
Lemma cenv_keypairs_eq : cenv_keypairs = @cenv_cs W0_keypairs.
Proof. unfold W0_keypairs; destruct (QPcompspecs_OK_e _ OKce_keypairs) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_keypairs_eq : ha_keypairs = @ha_env_cs W0_keypairs.
Proof. unfold W0_keypairs; destruct (QPcompspecs_OK_e _ OKce_keypairs) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_keypairs_eq : la_keypairs = @la_env_cs W0_keypairs.
Proof. unfold W0_keypairs; destruct (QPcompspecs_OK_e _ OKce_keypairs) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_keypairs : composite_env_consistent cenv_keypairs.
Proof. rewrite cenv_keypairs_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_keypairs : composite_env_legal_fieldlist cenv_keypairs.
Proof. rewrite cenv_keypairs_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_keypairs : composite_env_complete_legal_cosu_type cenv_keypairs.
Proof. rewrite cenv_keypairs_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_keypairs : hardware_alignof_env_consistent cenv_keypairs ha_keypairs.
Proof. rewrite cenv_keypairs_eq, ha_keypairs_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_keypairs : hardware_alignof_env_complete cenv_keypairs ha_keypairs.
Proof. rewrite cenv_keypairs_eq, ha_keypairs_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_keypairs : legal_alignas_env_consistent cenv_keypairs ha_keypairs la_keypairs.
Proof. rewrite cenv_keypairs_eq, ha_keypairs_eq, la_keypairs_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_keypairs : legal_alignas_env_complete cenv_keypairs la_keypairs.
Proof. rewrite cenv_keypairs_eq, la_keypairs_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_keypairs : legal_alignas_env_sound cenv_keypairs ha_keypairs la_keypairs.
Proof. rewrite cenv_keypairs_eq, ha_keypairs_eq, la_keypairs_eq; apply la_env_cs_sound. Qed.

(* ---------- prim_aead ---------- *)
Lemma world_OK_H_prim_aead : QPprogram_OK WgNoise.contracts.x_prim_aead.Harness.qp. Proof. prove_unit_OK WgNoise.contracts.x_prim_aead.Harness.CS. Qed.
Lemma world_OK_whole_prim_aead : QPprogram_OK WgNoise.contracts.x_prim_aead.whole_prog.
Proof. link_OK WgNoise.contracts.x_prim_aead.Harness.qp WgNoise.contracts.x_counter.link_Malloc world_OK_H_prim_aead world_OK_link_Malloc. Qed.
Definition ce_prim_aead : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.x_prim_aead.whole_prog) in exact x).
Lemma OKce_prim_aead : QPcompspecs_OK ce_prim_aead. Proof. exact (proj2 world_OK_whole_prim_aead). Qed.
Definition W0_prim_aead : compspecs := compspecs_of_QPcomposite_env ce_prim_aead OKce_prim_aead.
Definition cenv_prim_aead : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_prim_aead) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_prim_aead : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_prim_aead) in exact x).
Definition la_prim_aead : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_prim_aead) in exact x).
Lemma cenv_prim_aead_eq : cenv_prim_aead = @cenv_cs W0_prim_aead.
Proof. unfold W0_prim_aead; destruct (QPcompspecs_OK_e _ OKce_prim_aead) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_prim_aead_eq : ha_prim_aead = @ha_env_cs W0_prim_aead.
Proof. unfold W0_prim_aead; destruct (QPcompspecs_OK_e _ OKce_prim_aead) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_prim_aead_eq : la_prim_aead = @la_env_cs W0_prim_aead.
Proof. unfold W0_prim_aead; destruct (QPcompspecs_OK_e _ OKce_prim_aead) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_prim_aead : composite_env_consistent cenv_prim_aead.
Proof. rewrite cenv_prim_aead_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_prim_aead : composite_env_legal_fieldlist cenv_prim_aead.
Proof. rewrite cenv_prim_aead_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_prim_aead : composite_env_complete_legal_cosu_type cenv_prim_aead.
Proof. rewrite cenv_prim_aead_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_prim_aead : hardware_alignof_env_consistent cenv_prim_aead ha_prim_aead.
Proof. rewrite cenv_prim_aead_eq, ha_prim_aead_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_prim_aead : hardware_alignof_env_complete cenv_prim_aead ha_prim_aead.
Proof. rewrite cenv_prim_aead_eq, ha_prim_aead_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_prim_aead : legal_alignas_env_consistent cenv_prim_aead ha_prim_aead la_prim_aead.
Proof. rewrite cenv_prim_aead_eq, ha_prim_aead_eq, la_prim_aead_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_prim_aead : legal_alignas_env_complete cenv_prim_aead la_prim_aead.
Proof. rewrite cenv_prim_aead_eq, la_prim_aead_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_prim_aead : legal_alignas_env_sound cenv_prim_aead ha_prim_aead la_prim_aead.
Proof. rewrite cenv_prim_aead_eq, ha_prim_aead_eq, la_prim_aead_eq; apply la_env_cs_sound. Qed.

(* ---------- prim_blake2s ---------- *)
Lemma world_OK_H_prim_blake2s : QPprogram_OK WgNoise.contracts.x_prim_blake2s.Harness.qp. Proof. prove_unit_OK WgNoise.contracts.x_prim_blake2s.Harness.CS. Qed.
Lemma world_OK_whole_prim_blake2s : QPprogram_OK WgNoise.contracts.x_prim_blake2s.whole_prog.
Proof. link_OK WgNoise.contracts.x_prim_blake2s.Harness.qp WgNoise.contracts.x_counter.link_Malloc world_OK_H_prim_blake2s world_OK_link_Malloc. Qed.
Definition ce_prim_blake2s : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.x_prim_blake2s.whole_prog) in exact x).
Lemma OKce_prim_blake2s : QPcompspecs_OK ce_prim_blake2s. Proof. exact (proj2 world_OK_whole_prim_blake2s). Qed.
Definition W0_prim_blake2s : compspecs := compspecs_of_QPcomposite_env ce_prim_blake2s OKce_prim_blake2s.
Definition cenv_prim_blake2s : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_prim_blake2s) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_prim_blake2s : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_prim_blake2s) in exact x).
Definition la_prim_blake2s : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_prim_blake2s) in exact x).
Lemma cenv_prim_blake2s_eq : cenv_prim_blake2s = @cenv_cs W0_prim_blake2s.
Proof. unfold W0_prim_blake2s; destruct (QPcompspecs_OK_e _ OKce_prim_blake2s) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_prim_blake2s_eq : ha_prim_blake2s = @ha_env_cs W0_prim_blake2s.
Proof. unfold W0_prim_blake2s; destruct (QPcompspecs_OK_e _ OKce_prim_blake2s) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_prim_blake2s_eq : la_prim_blake2s = @la_env_cs W0_prim_blake2s.
Proof. unfold W0_prim_blake2s; destruct (QPcompspecs_OK_e _ OKce_prim_blake2s) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_prim_blake2s : composite_env_consistent cenv_prim_blake2s.
Proof. rewrite cenv_prim_blake2s_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_prim_blake2s : composite_env_legal_fieldlist cenv_prim_blake2s.
Proof. rewrite cenv_prim_blake2s_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_prim_blake2s : composite_env_complete_legal_cosu_type cenv_prim_blake2s.
Proof. rewrite cenv_prim_blake2s_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_prim_blake2s : hardware_alignof_env_consistent cenv_prim_blake2s ha_prim_blake2s.
Proof. rewrite cenv_prim_blake2s_eq, ha_prim_blake2s_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_prim_blake2s : hardware_alignof_env_complete cenv_prim_blake2s ha_prim_blake2s.
Proof. rewrite cenv_prim_blake2s_eq, ha_prim_blake2s_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_prim_blake2s : legal_alignas_env_consistent cenv_prim_blake2s ha_prim_blake2s la_prim_blake2s.
Proof. rewrite cenv_prim_blake2s_eq, ha_prim_blake2s_eq, la_prim_blake2s_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_prim_blake2s : legal_alignas_env_complete cenv_prim_blake2s la_prim_blake2s.
Proof. rewrite cenv_prim_blake2s_eq, la_prim_blake2s_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_prim_blake2s : legal_alignas_env_sound cenv_prim_blake2s ha_prim_blake2s la_prim_blake2s.
Proof. rewrite cenv_prim_blake2s_eq, ha_prim_blake2s_eq, la_prim_blake2s_eq; apply la_env_cs_sound. Qed.

(* ---------- prim_poly1305 ---------- *)
Lemma world_OK_H_prim_poly1305 : QPprogram_OK WgNoise.contracts.x_prim_poly1305.Harness.qp. Proof. prove_unit_OK WgNoise.contracts.x_prim_poly1305.Harness.CS. Qed.
Lemma world_OK_whole_prim_poly1305 : QPprogram_OK WgNoise.contracts.x_prim_poly1305.whole_prog.
Proof. link_OK WgNoise.contracts.x_prim_poly1305.Harness.qp WgNoise.contracts.x_counter.link_Malloc world_OK_H_prim_poly1305 world_OK_link_Malloc. Qed.
Definition ce_prim_poly1305 : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.x_prim_poly1305.whole_prog) in exact x).
Lemma OKce_prim_poly1305 : QPcompspecs_OK ce_prim_poly1305. Proof. exact (proj2 world_OK_whole_prim_poly1305). Qed.
Definition W0_prim_poly1305 : compspecs := compspecs_of_QPcomposite_env ce_prim_poly1305 OKce_prim_poly1305.
Definition cenv_prim_poly1305 : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_prim_poly1305) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_prim_poly1305 : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_prim_poly1305) in exact x).
Definition la_prim_poly1305 : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_prim_poly1305) in exact x).
Lemma cenv_prim_poly1305_eq : cenv_prim_poly1305 = @cenv_cs W0_prim_poly1305.
Proof. unfold W0_prim_poly1305; destruct (QPcompspecs_OK_e _ OKce_prim_poly1305) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_prim_poly1305_eq : ha_prim_poly1305 = @ha_env_cs W0_prim_poly1305.
Proof. unfold W0_prim_poly1305; destruct (QPcompspecs_OK_e _ OKce_prim_poly1305) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_prim_poly1305_eq : la_prim_poly1305 = @la_env_cs W0_prim_poly1305.
Proof. unfold W0_prim_poly1305; destruct (QPcompspecs_OK_e _ OKce_prim_poly1305) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_prim_poly1305 : composite_env_consistent cenv_prim_poly1305.
Proof. rewrite cenv_prim_poly1305_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_prim_poly1305 : composite_env_legal_fieldlist cenv_prim_poly1305.
Proof. rewrite cenv_prim_poly1305_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_prim_poly1305 : composite_env_complete_legal_cosu_type cenv_prim_poly1305.
Proof. rewrite cenv_prim_poly1305_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_prim_poly1305 : hardware_alignof_env_consistent cenv_prim_poly1305 ha_prim_poly1305.
Proof. rewrite cenv_prim_poly1305_eq, ha_prim_poly1305_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_prim_poly1305 : hardware_alignof_env_complete cenv_prim_poly1305 ha_prim_poly1305.
Proof. rewrite cenv_prim_poly1305_eq, ha_prim_poly1305_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_prim_poly1305 : legal_alignas_env_consistent cenv_prim_poly1305 ha_prim_poly1305 la_prim_poly1305.
Proof. rewrite cenv_prim_poly1305_eq, ha_prim_poly1305_eq, la_prim_poly1305_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_prim_poly1305 : legal_alignas_env_complete cenv_prim_poly1305 la_prim_poly1305.
Proof. rewrite cenv_prim_poly1305_eq, la_prim_poly1305_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_prim_poly1305 : legal_alignas_env_sound cenv_prim_poly1305 ha_prim_poly1305 la_prim_poly1305.
Proof. rewrite cenv_prim_poly1305_eq, ha_prim_poly1305_eq, la_prim_poly1305_eq; apply la_env_cs_sound. Qed.

(* ---------- replay ---------- *)
Lemma world_OK_H_replay : QPprogram_OK WgNoise.contracts.x_replay.Harness.qp. Proof. prove_unit_OK WgNoise.contracts.x_replay.Harness.CS. Qed.
Lemma world_OK_whole_replay : QPprogram_OK WgNoise.contracts.x_replay.whole_prog.
Proof. link_OK WgNoise.contracts.x_replay.Harness.qp WgNoise.contracts.x_counter.link_Malloc world_OK_H_replay world_OK_link_Malloc. Qed.
Definition ce_replay : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.x_replay.whole_prog) in exact x).
Lemma OKce_replay : QPcompspecs_OK ce_replay. Proof. exact (proj2 world_OK_whole_replay). Qed.
Definition W0_replay : compspecs := compspecs_of_QPcomposite_env ce_replay OKce_replay.
Definition cenv_replay : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_replay) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_replay : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_replay) in exact x).
Definition la_replay : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_replay) in exact x).
Lemma cenv_replay_eq : cenv_replay = @cenv_cs W0_replay.
Proof. unfold W0_replay; destruct (QPcompspecs_OK_e _ OKce_replay) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_replay_eq : ha_replay = @ha_env_cs W0_replay.
Proof. unfold W0_replay; destruct (QPcompspecs_OK_e _ OKce_replay) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_replay_eq : la_replay = @la_env_cs W0_replay.
Proof. unfold W0_replay; destruct (QPcompspecs_OK_e _ OKce_replay) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_replay : composite_env_consistent cenv_replay.
Proof. rewrite cenv_replay_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_replay : composite_env_legal_fieldlist cenv_replay.
Proof. rewrite cenv_replay_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_replay : composite_env_complete_legal_cosu_type cenv_replay.
Proof. rewrite cenv_replay_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_replay : hardware_alignof_env_consistent cenv_replay ha_replay.
Proof. rewrite cenv_replay_eq, ha_replay_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_replay : hardware_alignof_env_complete cenv_replay ha_replay.
Proof. rewrite cenv_replay_eq, ha_replay_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_replay : legal_alignas_env_consistent cenv_replay ha_replay la_replay.
Proof. rewrite cenv_replay_eq, ha_replay_eq, la_replay_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_replay : legal_alignas_env_complete cenv_replay la_replay.
Proof. rewrite cenv_replay_eq, la_replay_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_replay : legal_alignas_env_sound cenv_replay ha_replay la_replay.
Proof. rewrite cenv_replay_eq, ha_replay_eq, la_replay_eq; apply la_env_cs_sound. Qed.

(* THE WORLDS *)
Definition W_consume_initiation_any : compspecs :=
  {| cenv_cs := cenv_consume_initiation_any; cenv_consistent := cenv_consistent_consume_initiation_any; cenv_legal_fieldlist := cenv_legal_fieldlist_consume_initiation_any;
     cenv_legal_su := cenv_legal_su_consume_initiation_any; ha_env_cs := ha_consume_initiation_any; ha_env_cs_consistent := ha_env_consistent_consume_initiation_any;
     ha_env_cs_complete := ha_env_complete_consume_initiation_any; la_env_cs := la_consume_initiation_any; la_env_cs_consistent := la_env_consistent_consume_initiation_any;
     la_env_cs_complete := la_env_complete_consume_initiation_any; la_env_cs_sound := la_env_sound_consume_initiation_any |}.
Definition W_consume_response_any : compspecs :=
  {| cenv_cs := cenv_consume_response_any; cenv_consistent := cenv_consistent_consume_response_any; cenv_legal_fieldlist := cenv_legal_fieldlist_consume_response_any;
     cenv_legal_su := cenv_legal_su_consume_response_any; ha_env_cs := ha_consume_response_any; ha_env_cs_consistent := ha_env_consistent_consume_response_any;
     ha_env_cs_complete := ha_env_complete_consume_response_any; la_env_cs := la_consume_response_any; la_env_cs_consistent := la_env_consistent_consume_response_any;
     la_env_cs_complete := la_env_complete_consume_response_any; la_env_cs_sound := la_env_sound_consume_response_any |}.
Definition W_cookie_mac : compspecs :=
  {| cenv_cs := cenv_cookie_mac; cenv_consistent := cenv_consistent_cookie_mac; cenv_legal_fieldlist := cenv_legal_fieldlist_cookie_mac;
     cenv_legal_su := cenv_legal_su_cookie_mac; ha_env_cs := ha_cookie_mac; ha_env_cs_consistent := ha_env_consistent_cookie_mac;
     ha_env_cs_complete := ha_env_complete_cookie_mac; la_env_cs := la_cookie_mac; la_env_cs_consistent := la_env_consistent_cookie_mac;
     la_env_cs_complete := la_env_complete_cookie_mac; la_env_cs_sound := la_env_sound_cookie_mac |}.
Definition W_cookie_reply : compspecs :=
  {| cenv_cs := cenv_cookie_reply; cenv_consistent := cenv_consistent_cookie_reply; cenv_legal_fieldlist := cenv_legal_fieldlist_cookie_reply;
     cenv_legal_su := cenv_legal_su_cookie_reply; ha_env_cs := ha_cookie_reply; ha_env_cs_consistent := ha_env_consistent_cookie_reply;
     ha_env_cs_complete := ha_env_complete_cookie_reply; la_env_cs := la_cookie_reply; la_env_cs_consistent := la_env_consistent_cookie_reply;
     la_env_cs_complete := la_env_complete_cookie_reply; la_env_cs_sound := la_env_sound_cookie_reply |}.
Definition W_counter : compspecs :=
  {| cenv_cs := cenv_counter; cenv_consistent := cenv_consistent_counter; cenv_legal_fieldlist := cenv_legal_fieldlist_counter;
     cenv_legal_su := cenv_legal_su_counter; ha_env_cs := ha_counter; ha_env_cs_consistent := ha_env_consistent_counter;
     ha_env_cs_complete := ha_env_complete_counter; la_env_cs := la_counter; la_env_cs_consistent := la_env_consistent_counter;
     la_env_cs_complete := la_env_complete_counter; la_env_cs_sound := la_env_sound_counter |}.
Definition W_create_any : compspecs :=
  {| cenv_cs := cenv_create_any; cenv_consistent := cenv_consistent_create_any; cenv_legal_fieldlist := cenv_legal_fieldlist_create_any;
     cenv_legal_su := cenv_legal_su_create_any; ha_env_cs := ha_create_any; ha_env_cs_consistent := ha_env_consistent_create_any;
     ha_env_cs_complete := ha_env_complete_create_any; la_env_cs := la_create_any; la_env_cs_consistent := la_env_consistent_create_any;
     la_env_cs_complete := la_env_complete_create_any; la_env_cs_sound := la_env_sound_create_any |}.
Definition W_handshake : compspecs :=
  {| cenv_cs := cenv_handshake; cenv_consistent := cenv_consistent_handshake; cenv_legal_fieldlist := cenv_legal_fieldlist_handshake;
     cenv_legal_su := cenv_legal_su_handshake; ha_env_cs := ha_handshake; ha_env_cs_consistent := ha_env_consistent_handshake;
     ha_env_cs_complete := ha_env_complete_handshake; la_env_cs := la_handshake; la_env_cs_consistent := la_env_consistent_handshake;
     la_env_cs_complete := la_env_complete_handshake; la_env_cs_sound := la_env_sound_handshake |}.
Definition W_keypairs : compspecs :=
  {| cenv_cs := cenv_keypairs; cenv_consistent := cenv_consistent_keypairs; cenv_legal_fieldlist := cenv_legal_fieldlist_keypairs;
     cenv_legal_su := cenv_legal_su_keypairs; ha_env_cs := ha_keypairs; ha_env_cs_consistent := ha_env_consistent_keypairs;
     ha_env_cs_complete := ha_env_complete_keypairs; la_env_cs := la_keypairs; la_env_cs_consistent := la_env_consistent_keypairs;
     la_env_cs_complete := la_env_complete_keypairs; la_env_cs_sound := la_env_sound_keypairs |}.
Definition W_prim_aead : compspecs :=
  {| cenv_cs := cenv_prim_aead; cenv_consistent := cenv_consistent_prim_aead; cenv_legal_fieldlist := cenv_legal_fieldlist_prim_aead;
     cenv_legal_su := cenv_legal_su_prim_aead; ha_env_cs := ha_prim_aead; ha_env_cs_consistent := ha_env_consistent_prim_aead;
     ha_env_cs_complete := ha_env_complete_prim_aead; la_env_cs := la_prim_aead; la_env_cs_consistent := la_env_consistent_prim_aead;
     la_env_cs_complete := la_env_complete_prim_aead; la_env_cs_sound := la_env_sound_prim_aead |}.
Definition W_prim_blake2s : compspecs :=
  {| cenv_cs := cenv_prim_blake2s; cenv_consistent := cenv_consistent_prim_blake2s; cenv_legal_fieldlist := cenv_legal_fieldlist_prim_blake2s;
     cenv_legal_su := cenv_legal_su_prim_blake2s; ha_env_cs := ha_prim_blake2s; ha_env_cs_consistent := ha_env_consistent_prim_blake2s;
     ha_env_cs_complete := ha_env_complete_prim_blake2s; la_env_cs := la_prim_blake2s; la_env_cs_consistent := la_env_consistent_prim_blake2s;
     la_env_cs_complete := la_env_complete_prim_blake2s; la_env_cs_sound := la_env_sound_prim_blake2s |}.
Definition W_prim_poly1305 : compspecs :=
  {| cenv_cs := cenv_prim_poly1305; cenv_consistent := cenv_consistent_prim_poly1305; cenv_legal_fieldlist := cenv_legal_fieldlist_prim_poly1305;
     cenv_legal_su := cenv_legal_su_prim_poly1305; ha_env_cs := ha_prim_poly1305; ha_env_cs_consistent := ha_env_consistent_prim_poly1305;
     ha_env_cs_complete := ha_env_complete_prim_poly1305; la_env_cs := la_prim_poly1305; la_env_cs_consistent := la_env_consistent_prim_poly1305;
     la_env_cs_complete := la_env_complete_prim_poly1305; la_env_cs_sound := la_env_sound_prim_poly1305 |}.
Definition W_replay : compspecs :=
  {| cenv_cs := cenv_replay; cenv_consistent := cenv_consistent_replay; cenv_legal_fieldlist := cenv_legal_fieldlist_replay;
     cenv_legal_su := cenv_legal_su_replay; ha_env_cs := ha_replay; ha_env_cs_consistent := ha_env_consistent_replay;
     ha_env_cs_complete := ha_env_complete_replay; la_env_cs := la_replay; la_env_cs_consistent := la_env_consistent_replay;
     la_env_cs_complete := la_env_complete_replay; la_env_cs_sound := la_env_sound_replay |}.

Lemma W_consume_initiation_any_eq : W_consume_initiation_any = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.x_consume_initiation_any.whole_prog) (proj2 world_OK_whole_consume_initiation_any).
Proof.
transitivity W0_consume_initiation_any.
- apply compspecs_ext; [apply cenv_consume_initiation_any_eq | apply ha_consume_initiation_any_eq | apply la_consume_initiation_any_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.

Lemma world_ok_consume_initiation_any : world_ok WgNoise.contracts.x_consume_initiation_any.whole_prog WgNoise.contracts.x_consume_initiation_any.Harness.CS W_consume_initiation_any.
Proof.
exists world_OK_whole_consume_initiation_any.
split; [apply W_consume_initiation_any_eq | split].
- apply cenv_built_correctly_e; vm_refl.
- rewrite W_consume_initiation_any_eq; repeat constructor; apply world_cspecs_sub; vm_refl.
Qed.

Lemma W_consume_response_any_eq : W_consume_response_any = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.x_consume_response_any.whole_prog) (proj2 world_OK_whole_consume_response_any).
Proof.
transitivity W0_consume_response_any.
- apply compspecs_ext; [apply cenv_consume_response_any_eq | apply ha_consume_response_any_eq | apply la_consume_response_any_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.

Lemma world_ok_consume_response_any : world_ok WgNoise.contracts.x_consume_response_any.whole_prog WgNoise.contracts.x_consume_response_any.Harness.CS W_consume_response_any.
Proof.
exists world_OK_whole_consume_response_any.
split; [apply W_consume_response_any_eq | split].
- apply cenv_built_correctly_e; vm_refl.
- rewrite W_consume_response_any_eq; repeat constructor; apply world_cspecs_sub; vm_refl.
Qed.

Lemma W_cookie_mac_eq : W_cookie_mac = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.x_cookie_mac.whole_prog) (proj2 world_OK_whole_cookie_mac).
Proof.
transitivity W0_cookie_mac.
- apply compspecs_ext; [apply cenv_cookie_mac_eq | apply ha_cookie_mac_eq | apply la_cookie_mac_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.

Lemma world_ok_cookie_mac : world_ok WgNoise.contracts.x_cookie_mac.whole_prog WgNoise.contracts.x_cookie_mac.Harness.CS W_cookie_mac.
Proof.
exists world_OK_whole_cookie_mac.
split; [apply W_cookie_mac_eq | split].
- apply cenv_built_correctly_e; vm_refl.
- rewrite W_cookie_mac_eq; repeat constructor; apply world_cspecs_sub; vm_refl.
Qed.

Lemma W_cookie_reply_eq : W_cookie_reply = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.x_cookie_reply.whole_prog) (proj2 world_OK_whole_cookie_reply).
Proof.
transitivity W0_cookie_reply.
- apply compspecs_ext; [apply cenv_cookie_reply_eq | apply ha_cookie_reply_eq | apply la_cookie_reply_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.

Lemma world_ok_cookie_reply : world_ok WgNoise.contracts.x_cookie_reply.whole_prog WgNoise.contracts.x_cookie_reply.Harness.CS W_cookie_reply.
Proof.
exists world_OK_whole_cookie_reply.
split; [apply W_cookie_reply_eq | split].
- apply cenv_built_correctly_e; vm_refl.
- rewrite W_cookie_reply_eq; repeat constructor; apply world_cspecs_sub; vm_refl.
Qed.

Lemma W_counter_eq : W_counter = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.x_counter.whole_prog) (proj2 world_OK_whole_counter).
Proof.
transitivity W0_counter.
- apply compspecs_ext; [apply cenv_counter_eq | apply ha_counter_eq | apply la_counter_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.

Lemma world_ok_counter : world_ok WgNoise.contracts.x_counter.whole_prog WgNoise.contracts.x_counter.Harness.CS W_counter.
Proof.
exists world_OK_whole_counter.
split; [apply W_counter_eq | split].
- apply cenv_built_correctly_e; vm_refl.
- rewrite W_counter_eq; repeat constructor; apply world_cspecs_sub; vm_refl.
Qed.

Lemma W_create_any_eq : W_create_any = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.x_create_any.whole_prog) (proj2 world_OK_whole_create_any).
Proof.
transitivity W0_create_any.
- apply compspecs_ext; [apply cenv_create_any_eq | apply ha_create_any_eq | apply la_create_any_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.

Lemma world_ok_create_any : world_ok WgNoise.contracts.x_create_any.whole_prog WgNoise.contracts.x_create_any.Harness.CS W_create_any.
Proof.
exists world_OK_whole_create_any.
split; [apply W_create_any_eq | split].
- apply cenv_built_correctly_e; vm_refl.
- rewrite W_create_any_eq; repeat constructor; apply world_cspecs_sub; vm_refl.
Qed.

Lemma W_handshake_eq : W_handshake = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.x_handshake.whole_prog) (proj2 world_OK_whole_handshake).
Proof.
transitivity W0_handshake.
- apply compspecs_ext; [apply cenv_handshake_eq | apply ha_handshake_eq | apply la_handshake_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.

Lemma world_ok_handshake : world_ok WgNoise.contracts.x_handshake.whole_prog WgNoise.contracts.x_handshake.Harness.CS W_handshake.
Proof.
exists world_OK_whole_handshake.
split; [apply W_handshake_eq | split].
- apply cenv_built_correctly_e; vm_refl.
- rewrite W_handshake_eq; repeat constructor; apply world_cspecs_sub; vm_refl.
Qed.

Lemma W_keypairs_eq : W_keypairs = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.x_keypairs.whole_prog) (proj2 world_OK_whole_keypairs).
Proof.
transitivity W0_keypairs.
- apply compspecs_ext; [apply cenv_keypairs_eq | apply ha_keypairs_eq | apply la_keypairs_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.

Lemma world_ok_keypairs : world_ok WgNoise.contracts.x_keypairs.whole_prog WgNoise.contracts.x_keypairs.Harness.CS W_keypairs.
Proof.
exists world_OK_whole_keypairs.
split; [apply W_keypairs_eq | split].
- apply cenv_built_correctly_e; vm_refl.
- rewrite W_keypairs_eq; repeat constructor; apply world_cspecs_sub; vm_refl.
Qed.

Lemma W_prim_aead_eq : W_prim_aead = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.x_prim_aead.whole_prog) (proj2 world_OK_whole_prim_aead).
Proof.
transitivity W0_prim_aead.
- apply compspecs_ext; [apply cenv_prim_aead_eq | apply ha_prim_aead_eq | apply la_prim_aead_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.

Lemma world_ok_prim_aead : world_ok WgNoise.contracts.x_prim_aead.whole_prog WgNoise.contracts.x_prim_aead.Harness.CS W_prim_aead.
Proof.
exists world_OK_whole_prim_aead.
split; [apply W_prim_aead_eq | split].
- apply cenv_built_correctly_e; vm_refl.
- rewrite W_prim_aead_eq; repeat constructor; apply world_cspecs_sub; vm_refl.
Qed.

Lemma W_prim_blake2s_eq : W_prim_blake2s = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.x_prim_blake2s.whole_prog) (proj2 world_OK_whole_prim_blake2s).
Proof.
transitivity W0_prim_blake2s.
- apply compspecs_ext; [apply cenv_prim_blake2s_eq | apply ha_prim_blake2s_eq | apply la_prim_blake2s_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.

Lemma world_ok_prim_blake2s : world_ok WgNoise.contracts.x_prim_blake2s.whole_prog WgNoise.contracts.x_prim_blake2s.Harness.CS W_prim_blake2s.
Proof.
exists world_OK_whole_prim_blake2s.
split; [apply W_prim_blake2s_eq | split].
- apply cenv_built_correctly_e; vm_refl.
- rewrite W_prim_blake2s_eq; repeat constructor; apply world_cspecs_sub; vm_refl.
Qed.

Lemma W_prim_poly1305_eq : W_prim_poly1305 = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.x_prim_poly1305.whole_prog) (proj2 world_OK_whole_prim_poly1305).
Proof.
transitivity W0_prim_poly1305.
- apply compspecs_ext; [apply cenv_prim_poly1305_eq | apply ha_prim_poly1305_eq | apply la_prim_poly1305_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.

Lemma world_ok_prim_poly1305 : world_ok WgNoise.contracts.x_prim_poly1305.whole_prog WgNoise.contracts.x_prim_poly1305.Harness.CS W_prim_poly1305.
Proof.
exists world_OK_whole_prim_poly1305.
split; [apply W_prim_poly1305_eq | split].
- apply cenv_built_correctly_e; vm_refl.
- rewrite W_prim_poly1305_eq; repeat constructor; apply world_cspecs_sub; vm_refl.
Qed.

Lemma W_replay_eq : W_replay = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.x_replay.whole_prog) (proj2 world_OK_whole_replay).
Proof.
transitivity W0_replay.
- apply compspecs_ext; [apply cenv_replay_eq | apply ha_replay_eq | apply la_replay_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.

Lemma world_ok_replay : world_ok WgNoise.contracts.x_replay.whole_prog WgNoise.contracts.x_replay.Harness.CS W_replay.
Proof.
exists world_OK_whole_replay.
split; [apply W_replay_eq | split].
- apply cenv_built_correctly_e; vm_refl.
- rewrite W_replay_eq; repeat constructor; apply world_cspecs_sub; vm_refl.
Qed.

Theorem worlds_ok :
  world_ok WgNoise.contracts.x_consume_initiation_any.whole_prog WgNoise.contracts.x_consume_initiation_any.Harness.CS W_consume_initiation_any /\
  world_ok WgNoise.contracts.x_consume_response_any.whole_prog WgNoise.contracts.x_consume_response_any.Harness.CS W_consume_response_any /\
  world_ok WgNoise.contracts.x_cookie_mac.whole_prog WgNoise.contracts.x_cookie_mac.Harness.CS W_cookie_mac /\
  world_ok WgNoise.contracts.x_cookie_reply.whole_prog WgNoise.contracts.x_cookie_reply.Harness.CS W_cookie_reply /\
  world_ok WgNoise.contracts.x_counter.whole_prog WgNoise.contracts.x_counter.Harness.CS W_counter /\
  world_ok WgNoise.contracts.x_create_any.whole_prog WgNoise.contracts.x_create_any.Harness.CS W_create_any /\
  world_ok WgNoise.contracts.x_handshake.whole_prog WgNoise.contracts.x_handshake.Harness.CS W_handshake /\
  world_ok WgNoise.contracts.x_keypairs.whole_prog WgNoise.contracts.x_keypairs.Harness.CS W_keypairs /\
  world_ok WgNoise.contracts.x_prim_aead.whole_prog WgNoise.contracts.x_prim_aead.Harness.CS W_prim_aead /\
  world_ok WgNoise.contracts.x_prim_blake2s.whole_prog WgNoise.contracts.x_prim_blake2s.Harness.CS W_prim_blake2s /\
  world_ok WgNoise.contracts.x_prim_poly1305.whole_prog WgNoise.contracts.x_prim_poly1305.Harness.CS W_prim_poly1305 /\
  world_ok WgNoise.contracts.x_replay.whole_prog WgNoise.contracts.x_replay.Harness.CS W_replay.
Proof.
exact (conj world_ok_consume_initiation_any (conj world_ok_consume_response_any (conj world_ok_cookie_mac (conj world_ok_cookie_reply (conj world_ok_counter (conj world_ok_create_any (conj world_ok_handshake (conj world_ok_keypairs (conj world_ok_prim_aead (conj world_ok_prim_blake2s (conj world_ok_prim_poly1305 world_ok_replay))))))))))).
Qed.
