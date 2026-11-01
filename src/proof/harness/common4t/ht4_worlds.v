(* the worlds of the transport laws transport_len,
   transport_order, transport_keepalive, shared by the three
   laws (transport_send_nonce has its own, tsn5_world.v).

   The 4 transport contracts link 15 units: the 14 of the other laws + DataHeader (src/units_transport.v), in the
   order Noise, Cookie, Counter, DataHeader, Blake2s, ...; the chain up to link_Malloc is proved once on
   transport_len's copy and every whole_prog is its Harness.qp linked with it.

   - W_<law>: the literal compspecs of the whole program (computes like a unit's compspecs);
   - W_<law>_eq: W_<law> = compspecs_of_QPcomposite_env (QP.prog_comp_env whole_prog) (proj2 world_OK_whole_<law>)
     (what asm_lib.asm_harness_safe needs);
   - world_ok_<law>: ht4_world_ok = wg3_worlds.world_ok with DataHeader.CS among the units' compspecs;
   - ht4_prim_aead_sub_<law>: cspecs_sub W_prim_aead W_<law> (the composite environment of law prim_aead is
     included in each: the common.h function bodies proved at W_prim_aead lift). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.units.DataHeader.
Require Import WgNoise.proof.common.wg3_worlds.
Require WgNoise.contracts.x_transport_len.
Require WgNoise.contracts.x_transport_order.
Require WgNoise.contracts.x_transport_keepalive.

(* W is the compspecs of p's composite environment, and includes the harness's and every unit's compspecs *)
Definition ht4_world_ok (p: QP.program function) (Hcs: compspecs) (W: compspecs) : Prop :=
  exists OK: QPprogram_OK p,
    W = compspecs_of_QPcomposite_env (QP.prog_comp_env p) (proj2 OK) /\
    build_composite_env
      (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) [])) =
    Errors.OK (composite_env_of_QPcomposite_env (QP.prog_comp_env p) (projT1 (proj2 OK))) /\
    Forall (fun cs => cspecs_sub cs W) (Hcs :: DataHeader.CS :: all_unit_cs).

Lemma ht4_OK_DataHeader : QPprogram_OK DataHeader.qp. Proof. prove_unit_OK DataHeader.CS. Qed.
Lemma ht4_OK_link_Cookie : QPprogram_OK WgNoise.contracts.x_transport_len.link_Cookie.
Proof. link_OK Cookie.qp Noise.qp world_OK_Cookie world_OK_Noise. Qed.
Lemma ht4_OK_link_Counter : QPprogram_OK WgNoise.contracts.x_transport_len.link_Counter.
Proof. link_OK Counter.qp WgNoise.contracts.x_transport_len.link_Cookie world_OK_Counter ht4_OK_link_Cookie. Qed.
Lemma ht4_OK_link_DataHeader : QPprogram_OK WgNoise.contracts.x_transport_len.link_DataHeader.
Proof. link_OK DataHeader.qp WgNoise.contracts.x_transport_len.link_Counter ht4_OK_DataHeader ht4_OK_link_Counter. Qed.
Lemma ht4_OK_link_Blake2s : QPprogram_OK WgNoise.contracts.x_transport_len.link_Blake2s.
Proof. link_OK Blake2s.qp WgNoise.contracts.x_transport_len.link_DataHeader world_OK_Blake2s ht4_OK_link_DataHeader. Qed.
Lemma ht4_OK_link_Chacha : QPprogram_OK WgNoise.contracts.x_transport_len.link_Chacha.
Proof. link_OK Chacha.qp WgNoise.contracts.x_transport_len.link_Blake2s world_OK_Chacha ht4_OK_link_Blake2s. Qed.
Lemma ht4_OK_link_ChachaBlock : QPprogram_OK WgNoise.contracts.x_transport_len.link_ChachaBlock.
Proof. link_OK ChachaBlock.qp WgNoise.contracts.x_transport_len.link_Chacha world_OK_ChachaBlock ht4_OK_link_Chacha. Qed.
Lemma ht4_OK_link_Poly1305 : QPprogram_OK WgNoise.contracts.x_transport_len.link_Poly1305.
Proof. link_OK Poly1305.qp WgNoise.contracts.x_transport_len.link_ChachaBlock world_OK_Poly1305 ht4_OK_link_ChachaBlock. Qed.
Lemma ht4_OK_link_Poly1305Donna32 : QPprogram_OK WgNoise.contracts.x_transport_len.link_Poly1305Donna32.
Proof. link_OK Poly1305Donna32.qp WgNoise.contracts.x_transport_len.link_Poly1305 world_OK_Poly1305Donna32 ht4_OK_link_Poly1305. Qed.
Lemma ht4_OK_link_Chacha20poly1305 : QPprogram_OK WgNoise.contracts.x_transport_len.link_Chacha20poly1305.
Proof. link_OK Chacha20poly1305.qp WgNoise.contracts.x_transport_len.link_Poly1305Donna32 world_OK_Chacha20poly1305 ht4_OK_link_Poly1305Donna32. Qed.
Lemma ht4_OK_link_Curve25519 : QPprogram_OK WgNoise.contracts.x_transport_len.link_Curve25519.
Proof. link_OK Curve25519.qp WgNoise.contracts.x_transport_len.link_Chacha20poly1305 world_OK_Curve25519 ht4_OK_link_Chacha20poly1305. Qed.
Lemma ht4_OK_link_Curve25519Fiat32 : QPprogram_OK WgNoise.contracts.x_transport_len.link_Curve25519Fiat32.
Proof. link_OK Curve25519Fiat32.qp WgNoise.contracts.x_transport_len.link_Curve25519 world_OK_Curve25519Fiat32 ht4_OK_link_Curve25519. Qed.
Lemma ht4_OK_link_Shim : QPprogram_OK WgNoise.contracts.x_transport_len.link_Shim.
Proof. link_OK Shim.qp WgNoise.contracts.x_transport_len.link_Curve25519Fiat32 world_OK_Shim ht4_OK_link_Curve25519Fiat32. Qed.
Lemma ht4_OK_link_Libc : QPprogram_OK WgNoise.contracts.x_transport_len.link_Libc.
Proof. link_OK Libc.qp WgNoise.contracts.x_transport_len.link_Shim world_OK_Libc ht4_OK_link_Shim. Qed.
Lemma ht4_OK_link_Malloc : QPprogram_OK WgNoise.contracts.x_transport_len.link_Malloc.
Proof. link_OK Malloc.qp WgNoise.contracts.x_transport_len.link_Libc world_OK_Malloc ht4_OK_link_Libc. Qed.

(* ---------- transport_len ---------- *)
Lemma world_OK_H_transport_len : QPprogram_OK WgNoise.contracts.x_transport_len.Harness.qp. Proof. prove_unit_OK WgNoise.contracts.x_transport_len.Harness.CS. Qed.
Lemma world_OK_whole_transport_len : QPprogram_OK WgNoise.contracts.x_transport_len.whole_prog.
Proof. link_OK WgNoise.contracts.x_transport_len.Harness.qp WgNoise.contracts.x_transport_len.link_Malloc world_OK_H_transport_len ht4_OK_link_Malloc. Qed.
Definition ce_transport_len : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.x_transport_len.whole_prog) in exact x).
Lemma OKce_transport_len : QPcompspecs_OK ce_transport_len. Proof. exact (proj2 world_OK_whole_transport_len). Qed.
Definition W0_transport_len : compspecs := compspecs_of_QPcomposite_env ce_transport_len OKce_transport_len.
Definition cenv_transport_len : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_transport_len) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_transport_len : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_transport_len) in exact x).
Definition la_transport_len : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_transport_len) in exact x).
Lemma cenv_transport_len_eq : cenv_transport_len = @cenv_cs W0_transport_len.
Proof. unfold W0_transport_len; destruct (QPcompspecs_OK_e _ OKce_transport_len) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_transport_len_eq : ha_transport_len = @ha_env_cs W0_transport_len.
Proof. unfold W0_transport_len; destruct (QPcompspecs_OK_e _ OKce_transport_len) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_transport_len_eq : la_transport_len = @la_env_cs W0_transport_len.
Proof. unfold W0_transport_len; destruct (QPcompspecs_OK_e _ OKce_transport_len) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_transport_len : composite_env_consistent cenv_transport_len.
Proof. rewrite cenv_transport_len_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_transport_len : composite_env_legal_fieldlist cenv_transport_len.
Proof. rewrite cenv_transport_len_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_transport_len : composite_env_complete_legal_cosu_type cenv_transport_len.
Proof. rewrite cenv_transport_len_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_transport_len : hardware_alignof_env_consistent cenv_transport_len ha_transport_len.
Proof. rewrite cenv_transport_len_eq, ha_transport_len_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_transport_len : hardware_alignof_env_complete cenv_transport_len ha_transport_len.
Proof. rewrite cenv_transport_len_eq, ha_transport_len_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_transport_len : legal_alignas_env_consistent cenv_transport_len ha_transport_len la_transport_len.
Proof. rewrite cenv_transport_len_eq, ha_transport_len_eq, la_transport_len_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_transport_len : legal_alignas_env_complete cenv_transport_len la_transport_len.
Proof. rewrite cenv_transport_len_eq, la_transport_len_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_transport_len : legal_alignas_env_sound cenv_transport_len ha_transport_len la_transport_len.
Proof. rewrite cenv_transport_len_eq, ha_transport_len_eq, la_transport_len_eq; apply la_env_cs_sound. Qed.
Definition W_transport_len : compspecs :=
  {| cenv_cs := cenv_transport_len; cenv_consistent := cenv_consistent_transport_len; cenv_legal_fieldlist := cenv_legal_fieldlist_transport_len;
     cenv_legal_su := cenv_legal_su_transport_len; ha_env_cs := ha_transport_len; ha_env_cs_consistent := ha_env_consistent_transport_len;
     ha_env_cs_complete := ha_env_complete_transport_len; la_env_cs := la_transport_len; la_env_cs_consistent := la_env_consistent_transport_len;
     la_env_cs_complete := la_env_complete_transport_len; la_env_cs_sound := la_env_sound_transport_len |}.
Lemma W_transport_len_eq : W_transport_len = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.x_transport_len.whole_prog) (proj2 world_OK_whole_transport_len).
Proof.
transitivity W0_transport_len.
- apply compspecs_ext; [apply cenv_transport_len_eq | apply ha_transport_len_eq | apply la_transport_len_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.
Lemma world_ok_transport_len : ht4_world_ok WgNoise.contracts.x_transport_len.whole_prog WgNoise.contracts.x_transport_len.Harness.CS W_transport_len.
Proof.
exists world_OK_whole_transport_len.
split; [apply W_transport_len_eq | split].
- apply cenv_built_correctly_e; vm_refl.
- rewrite W_transport_len_eq; repeat constructor; apply world_cspecs_sub; vm_refl.
Qed.
Lemma ht4_prim_aead_sub_transport_len : cspecs_sub W_prim_aead W_transport_len.
Proof. rewrite W_transport_len_eq; apply world_cspecs_sub; vm_refl. Qed.

(* ---------- transport_order ---------- *)
Lemma world_OK_H_transport_order : QPprogram_OK WgNoise.contracts.x_transport_order.Harness.qp. Proof. prove_unit_OK WgNoise.contracts.x_transport_order.Harness.CS. Qed.
Lemma world_OK_whole_transport_order : QPprogram_OK WgNoise.contracts.x_transport_order.whole_prog.
Proof. link_OK WgNoise.contracts.x_transport_order.Harness.qp WgNoise.contracts.x_transport_len.link_Malloc world_OK_H_transport_order ht4_OK_link_Malloc. Qed.
Definition ce_transport_order : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.x_transport_order.whole_prog) in exact x).
Lemma OKce_transport_order : QPcompspecs_OK ce_transport_order. Proof. exact (proj2 world_OK_whole_transport_order). Qed.
Definition W0_transport_order : compspecs := compspecs_of_QPcomposite_env ce_transport_order OKce_transport_order.
Definition cenv_transport_order : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_transport_order) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_transport_order : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_transport_order) in exact x).
Definition la_transport_order : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_transport_order) in exact x).
Lemma cenv_transport_order_eq : cenv_transport_order = @cenv_cs W0_transport_order.
Proof. unfold W0_transport_order; destruct (QPcompspecs_OK_e _ OKce_transport_order) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_transport_order_eq : ha_transport_order = @ha_env_cs W0_transport_order.
Proof. unfold W0_transport_order; destruct (QPcompspecs_OK_e _ OKce_transport_order) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_transport_order_eq : la_transport_order = @la_env_cs W0_transport_order.
Proof. unfold W0_transport_order; destruct (QPcompspecs_OK_e _ OKce_transport_order) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_transport_order : composite_env_consistent cenv_transport_order.
Proof. rewrite cenv_transport_order_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_transport_order : composite_env_legal_fieldlist cenv_transport_order.
Proof. rewrite cenv_transport_order_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_transport_order : composite_env_complete_legal_cosu_type cenv_transport_order.
Proof. rewrite cenv_transport_order_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_transport_order : hardware_alignof_env_consistent cenv_transport_order ha_transport_order.
Proof. rewrite cenv_transport_order_eq, ha_transport_order_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_transport_order : hardware_alignof_env_complete cenv_transport_order ha_transport_order.
Proof. rewrite cenv_transport_order_eq, ha_transport_order_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_transport_order : legal_alignas_env_consistent cenv_transport_order ha_transport_order la_transport_order.
Proof. rewrite cenv_transport_order_eq, ha_transport_order_eq, la_transport_order_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_transport_order : legal_alignas_env_complete cenv_transport_order la_transport_order.
Proof. rewrite cenv_transport_order_eq, la_transport_order_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_transport_order : legal_alignas_env_sound cenv_transport_order ha_transport_order la_transport_order.
Proof. rewrite cenv_transport_order_eq, ha_transport_order_eq, la_transport_order_eq; apply la_env_cs_sound. Qed.
Definition W_transport_order : compspecs :=
  {| cenv_cs := cenv_transport_order; cenv_consistent := cenv_consistent_transport_order; cenv_legal_fieldlist := cenv_legal_fieldlist_transport_order;
     cenv_legal_su := cenv_legal_su_transport_order; ha_env_cs := ha_transport_order; ha_env_cs_consistent := ha_env_consistent_transport_order;
     ha_env_cs_complete := ha_env_complete_transport_order; la_env_cs := la_transport_order; la_env_cs_consistent := la_env_consistent_transport_order;
     la_env_cs_complete := la_env_complete_transport_order; la_env_cs_sound := la_env_sound_transport_order |}.
Lemma W_transport_order_eq : W_transport_order = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.x_transport_order.whole_prog) (proj2 world_OK_whole_transport_order).
Proof.
transitivity W0_transport_order.
- apply compspecs_ext; [apply cenv_transport_order_eq | apply ha_transport_order_eq | apply la_transport_order_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.
Lemma world_ok_transport_order : ht4_world_ok WgNoise.contracts.x_transport_order.whole_prog WgNoise.contracts.x_transport_order.Harness.CS W_transport_order.
Proof.
exists world_OK_whole_transport_order.
split; [apply W_transport_order_eq | split].
- apply cenv_built_correctly_e; vm_refl.
- rewrite W_transport_order_eq; repeat constructor; apply world_cspecs_sub; vm_refl.
Qed.
Lemma ht4_prim_aead_sub_transport_order : cspecs_sub W_prim_aead W_transport_order.
Proof. rewrite W_transport_order_eq; apply world_cspecs_sub; vm_refl. Qed.

(* ---------- transport_keepalive ---------- *)
Lemma world_OK_H_transport_keepalive : QPprogram_OK WgNoise.contracts.x_transport_keepalive.Harness.qp. Proof. prove_unit_OK WgNoise.contracts.x_transport_keepalive.Harness.CS. Qed.
Lemma world_OK_whole_transport_keepalive : QPprogram_OK WgNoise.contracts.x_transport_keepalive.whole_prog.
Proof. link_OK WgNoise.contracts.x_transport_keepalive.Harness.qp WgNoise.contracts.x_transport_len.link_Malloc world_OK_H_transport_keepalive ht4_OK_link_Malloc. Qed.
Definition ce_transport_keepalive : QP.composite_env := ltac:(let x := eval vm_compute in (QP.prog_comp_env WgNoise.contracts.x_transport_keepalive.whole_prog) in exact x).
Lemma OKce_transport_keepalive : QPcompspecs_OK ce_transport_keepalive. Proof. exact (proj2 world_OK_whole_transport_keepalive). Qed.
Definition W0_transport_keepalive : compspecs := compspecs_of_QPcomposite_env ce_transport_keepalive OKce_transport_keepalive.
Definition cenv_transport_keepalive : composite_env :=
  ltac:(let c := eval vm_compute in (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements ce_transport_keepalive) [])) in
        let e := make_composite_env c in
        match e with Errors.OK ?e => let e := eval hnf in e in let e := eval simpl in e in exact e end).
Definition ha_transport_keepalive : Maps.PTree.t Z := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_ha ce_transport_keepalive) in exact x).
Definition la_transport_keepalive : Maps.PTree.t legal_alignas_obs := ltac:(let x := eval vm_compute in (Maps.PTree.map1 QP.co_la ce_transport_keepalive) in exact x).
Lemma cenv_transport_keepalive_eq : cenv_transport_keepalive = @cenv_cs W0_transport_keepalive.
Proof. unfold W0_transport_keepalive; destruct (QPcompspecs_OK_e _ OKce_transport_keepalive) as [E _]; rewrite E. apply composite_env_ext; vm_refl. Qed.
Lemma ha_transport_keepalive_eq : ha_transport_keepalive = @ha_env_cs W0_transport_keepalive.
Proof. unfold W0_transport_keepalive; destruct (QPcompspecs_OK_e _ OKce_transport_keepalive) as [_ [E _]]; rewrite E. vm_refl. Qed.
Lemma la_transport_keepalive_eq : la_transport_keepalive = @la_env_cs W0_transport_keepalive.
Proof. unfold W0_transport_keepalive; destruct (QPcompspecs_OK_e _ OKce_transport_keepalive) as [_ [_ E]]; rewrite E. vm_refl. Qed.
Lemma cenv_consistent_transport_keepalive : composite_env_consistent cenv_transport_keepalive.
Proof. rewrite cenv_transport_keepalive_eq; apply cenv_consistent. Qed.
Lemma cenv_legal_fieldlist_transport_keepalive : composite_env_legal_fieldlist cenv_transport_keepalive.
Proof. rewrite cenv_transport_keepalive_eq; apply cenv_legal_fieldlist. Qed.
Lemma cenv_legal_su_transport_keepalive : composite_env_complete_legal_cosu_type cenv_transport_keepalive.
Proof. rewrite cenv_transport_keepalive_eq; apply cenv_legal_su. Qed.
Lemma ha_env_consistent_transport_keepalive : hardware_alignof_env_consistent cenv_transport_keepalive ha_transport_keepalive.
Proof. rewrite cenv_transport_keepalive_eq, ha_transport_keepalive_eq; apply ha_env_cs_consistent. Qed.
Lemma ha_env_complete_transport_keepalive : hardware_alignof_env_complete cenv_transport_keepalive ha_transport_keepalive.
Proof. rewrite cenv_transport_keepalive_eq, ha_transport_keepalive_eq; apply ha_env_cs_complete. Qed.
Lemma la_env_consistent_transport_keepalive : legal_alignas_env_consistent cenv_transport_keepalive ha_transport_keepalive la_transport_keepalive.
Proof. rewrite cenv_transport_keepalive_eq, ha_transport_keepalive_eq, la_transport_keepalive_eq; apply la_env_cs_consistent. Qed.
Lemma la_env_complete_transport_keepalive : legal_alignas_env_complete cenv_transport_keepalive la_transport_keepalive.
Proof. rewrite cenv_transport_keepalive_eq, la_transport_keepalive_eq; apply la_env_cs_complete. Qed.
Lemma la_env_sound_transport_keepalive : legal_alignas_env_sound cenv_transport_keepalive ha_transport_keepalive la_transport_keepalive.
Proof. rewrite cenv_transport_keepalive_eq, ha_transport_keepalive_eq, la_transport_keepalive_eq; apply la_env_cs_sound. Qed.
Definition W_transport_keepalive : compspecs :=
  {| cenv_cs := cenv_transport_keepalive; cenv_consistent := cenv_consistent_transport_keepalive; cenv_legal_fieldlist := cenv_legal_fieldlist_transport_keepalive;
     cenv_legal_su := cenv_legal_su_transport_keepalive; ha_env_cs := ha_transport_keepalive; ha_env_cs_consistent := ha_env_consistent_transport_keepalive;
     ha_env_cs_complete := ha_env_complete_transport_keepalive; la_env_cs := la_transport_keepalive; la_env_cs_consistent := la_env_consistent_transport_keepalive;
     la_env_cs_complete := la_env_complete_transport_keepalive; la_env_cs_sound := la_env_sound_transport_keepalive |}.
Lemma W_transport_keepalive_eq : W_transport_keepalive = compspecs_of_QPcomposite_env (QP.prog_comp_env WgNoise.contracts.x_transport_keepalive.whole_prog) (proj2 world_OK_whole_transport_keepalive).
Proof.
transitivity W0_transport_keepalive.
- apply compspecs_ext; [apply cenv_transport_keepalive_eq | apply ha_transport_keepalive_eq | apply la_transport_keepalive_eq].
- apply compspecs_of_QPcomposite_env_irr.
Qed.
Lemma world_ok_transport_keepalive : ht4_world_ok WgNoise.contracts.x_transport_keepalive.whole_prog WgNoise.contracts.x_transport_keepalive.Harness.CS W_transport_keepalive.
Proof.
exists world_OK_whole_transport_keepalive.
split; [apply W_transport_keepalive_eq | split].
- apply cenv_built_correctly_e; vm_refl.
- rewrite W_transport_keepalive_eq; repeat constructor; apply world_cspecs_sub; vm_refl.
Qed.
Lemma ht4_prim_aead_sub_transport_keepalive : cspecs_sub W_prim_aead W_transport_keepalive.
Proof. rewrite W_transport_keepalive_eq; apply world_cspecs_sub; vm_refl. Qed.
