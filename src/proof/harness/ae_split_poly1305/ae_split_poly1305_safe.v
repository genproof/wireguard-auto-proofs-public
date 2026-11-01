(* Law ae_split_poly1305 (harness/ae_split_poly1305.c): the whole program is safe, i.e. its checks hold in every execution, given the
   small shared bodies of wl_kit.v (proved once for all ae_ laws, wl_kit_proof.v, and given in ae_laws_parts.v). *)
Require Import QuickProof.Contract.
Require Import WgNoise.proof.harness.wg_laws.wl_kit.
Require WgNoise.contracts.ae_split_poly1305.

(* The assembly, in the law's world W_asp (asp_world.v), with asm_assert.v's asm_harness_safe_gp, of
   - memcpy and memset (libc_mem_piece.v, at Libc.CS, no context);
   - the inlines get_unaligned_le32 (wl_kit_ok, at W_asp, no context) and poly1305-donna32.c's
     put_unaligned_le32 (p1305_donna_callee.v);
   - poly1305-donna32.c and poly1305.c (p1305_donna_callee.v, p1305_small_callee.v,
     p1305_update_final_callee.v: the specifications of aead_spec3.v, with contexts of their callees only);
   - the harness piece (asp_piece.v: upto, any_bytes, bytes_eq from wl_kit_ok, main).
   Each library body lifts into the whole program by asm_body_lift: its unit's compspecs is included in W_asp and
   its callees' specifications are covered by the program's (memcpy, memset and get_unaligned_le32 through a change
   of compspecs: they touch byte arrays only). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.poly1305.code WgNoise.poly1305_donna32.code WgNoise.chacha20poly1305.code.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.assembly.asm_assert.
Require Import WgNoise.proof.assembly.asm_xcs_aead3.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.libc.libc_mem_piece.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.harness.ae_split_poly1305.asp_spec.
Require Import WgNoise.proof.harness.ae_split_poly1305.asp_piece.
Require WgNoise.proof.aead.p1305_donna_callee WgNoise.proof.aead.p1305_small_callee
        WgNoise.proof.aead.p1305_update_final_callee.

Local Notation p := WgNoise.contracts.ae_split_poly1305.whole_prog.

#[local] Instance asp_cce_libc_poly : change_composite_env Libc.CS Poly1305.CS.
Proof. make_cs_preserve Libc.CS Poly1305.CS. Defined.
#[local] Instance asp_cce_w_poly : change_composite_env W_asp Poly1305.CS.
Proof. make_cs_preserve W_asp Poly1305.CS. Defined.
#[local] Instance asp_cce_w_donna : change_composite_env W_asp Poly1305Donna32.CS.
Proof. make_cs_preserve W_asp Poly1305Donna32.CS. Defined.

(* the specifications of the library functions the program reaches *)
Definition asp_Glib : funspecs :=
  libc_mem_G ++
  [@get_unaligned_le32_spec W_asp; put_unaligned_le32_spec;
   poly1305_core_setkey_spec; poly1305_core_blocks_spec; poly1305_core_emit_spec;
   poly1305_core_init_spec; poly1305_block_init_generic_spec; poly1305_blocks_generic_spec;
   poly1305_emit_generic_spec; poly1305_init_spec; poly1305_update_spec3; poly1305_final_spec].

Definition asp_Gh : funspecs := filter (fun ix => negb (Pos.eqb (fst ix) (QP.prog_main p))) asp_G.

(* the real specifications, main excepted *)
Definition asp_Gr : funspecs := asp_Glib ++ asp_Gh.

Definition asp_ids : list ident := ltac:(let l := eval compute in (map fst asp_Gr) in exact l).

Lemma asp_IDS : map fst asp_Gr = asp_ids.
Proof. reflexivity. Qed.

Lemma asp_check : asm_check_gp W_asp p asp_ids = true.
Proof. vm_compute; reflexivity. Qed.

Local Notation Gw := (@asm_Gall_gp W_asp p asp_post asp_Gr asp_ids).

Lemma asp_norepet : list_norepet (map fst (QPvarspecs p) ++ map fst Gw).
Proof. apply asm_Gall_gp_norepet; [apply asp_IDS | apply asp_check]. Qed.

Lemma asp_norepet' : list_norepet (map fst Gw).
Proof. apply asm_Gall_gp_norepet'; [apply asp_IDS | apply asp_check]. Qed.

Lemma asp_find_Gr i s : In (i, s) asp_Gr -> initial_world.find_id i Gw = Some s.
Proof. intros H. apply initial_world.find_id_i; [| apply asp_norepet']. apply asm_Gr_gp_incl; auto. Qed.

Ltac asp_in := repeat (first [left; reflexivity | right]).

Lemma asp_sub i s : In (i, s) asp_Gr -> exists s', initial_world.find_id i Gw = Some s' /\ funspec_sub s' s.
Proof. intros H. exists s; split; [apply asp_find_Gr; auto | apply funspec_sub_refl]. Qed.

Lemma asp_cs_sub cs : In cs [Poly1305.CS; Poly1305Donna32.CS; Libc.CS] -> cspecs_sub cs W_asp.
Proof.
  destruct world_ok_asp as [_ [_ [_ HF]]]. rewrite Forall_forall in HF. intros H. apply HF. right; auto.
Qed.

(* a body proved in a unit, with a context Gu covered by the program's specifications, in the whole program *)
Lemma asp_lift (csu: compspecs) (Vu: varspecs) (Gu: funspecs) f ip :
  @semax_body Vu Gu csu f ip ->
  cspecs_sub csu W_asp ->
  Maps.PTree.get (fst ip) (QP.prog_defs p) = Some (Gfun (Internal f)) ->
  Forall (fun it => complete_type (@cenv_cs csu) (snd it) = true) (fn_vars f) ->
  Vu = nil ->
  asm_covers Gw Gu ->
  exists f', Maps.PTree.get (fst ip) (QP.prog_defs p) = Some (Gfun (Internal f')) /\
             @semax_body (QPvarspecs p) Gw W_asp f' ip.
Proof.
  intros SB CS DEF COMPL VU COV. subst Vu. exists f; split; auto.
  exact (asm_body_lift nil _ Gu Gw f ip CS COMPL asp_norepet (Forall_nil _) COV SB).
Qed.

(* the callees' specifications at the units' compspecs, covered by the program's *)
Lemma asp_cov_memset : exists s', initial_world.find_id (fst (@memset_spec Poly1305.CS)) Gw = Some s' /\
                                  funspec_sub s' (snd (@memset_spec Poly1305.CS)).
Proof.
  exists (snd (@memset_spec Libc.CS)). split; [apply asp_find_Gr; asp_in | apply xa3_memset_sub].
Qed.
Lemma asp_cov_memcpy : exists s', initial_world.find_id (fst (@memcpy_spec Poly1305.CS)) Gw = Some s' /\
                                  funspec_sub s' (snd (@memcpy_spec Poly1305.CS)).
Proof.
  exists (snd (@memcpy_spec Libc.CS)). split; [apply asp_find_Gr; asp_in | apply xa3_memcpy_sub].
Qed.
Lemma asp_cov_get_poly : exists s', initial_world.find_id (fst (@get_unaligned_le32_spec Poly1305.CS)) Gw = Some s' /\
                                    funspec_sub s' (snd (@get_unaligned_le32_spec Poly1305.CS)).
Proof.
  exists (snd (@get_unaligned_le32_spec W_asp)). split; [apply asp_find_Gr; asp_in | apply xa3_get_unaligned_le32_sub].
Qed.
Lemma asp_cov_get_donna : exists s', initial_world.find_id (fst (@get_unaligned_le32_spec Poly1305Donna32.CS)) Gw = Some s' /\
                                     funspec_sub s' (snd (@get_unaligned_le32_spec Poly1305Donna32.CS)).
Proof.
  exists (snd (@get_unaligned_le32_spec W_asp)). split; [apply asp_find_Gr; asp_in | apply xa3_get_unaligned_le32_sub].
Qed.

Ltac asp_lift_tac CS H :=
  apply (asp_lift _ _ _ _ _ H); [ CS | vm_compute; reflexivity | repeat constructor | reflexivity |].

Ltac asp_sub_tac := apply asp_cs_sub; asp_in.

Lemma asp_cbc : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma asp_ext_ok : all_unspecified_OK p.
Proof. reflexivity. Qed.

Lemma asp_cc : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) asp_Gr.
Proof. repeat constructor. Qed.

Section Assembly.
Variable Hkit: wl_kit_ok.

(* ---------- the library bodies ---------- *)
Lemma asp_bodies_lib : asm_bodies W_asp p Gw asp_Glib.
Proof.
  destruct libc_mem_piece as [_ HL]. unfold libc_mem_G in HL.
  apply Forall_inv in HL as HL1. apply Forall_inv_tail, Forall_inv in HL as HL2.
  destruct HL1 as [u1 [Hu1 [f1 [Hf1 B1]]]]. destruct HL2 as [u2 [Hu2 [f2 [Hf2 B2]]]].
  destruct Hu1 as [<-|[]]. destruct Hu2 as [<-|[]].
  vm_compute in Hf1, Hf2. inv Hf1. inv Hf2.
  pose proof (proj2 (proj2 (proj2 (proj2 (proj2 Hkit)))) W_asp) as G1.
  destruct WgNoise.proof.aead.p1305_donna_callee.p1305_donna_callee_bodies as (D1 & D2 & D3 & D4).
  destruct WgNoise.proof.aead.p1305_small_callee.p1305_small_callee_bodies as (S1 & S2 & S3 & S4 & S5).
  destruct WgNoise.proof.aead.p1305_update_final_callee.p1305_update_final_callee_bodies as (U1 & U2).
  unfold asp_Glib, libc_mem_G. simpl app.
  repeat apply Forall_cons; try apply Forall_nil.
  - asp_lift_tac asp_sub_tac B1. repeat constructor; apply asp_sub; asp_in.
  - asp_lift_tac asp_sub_tac B2. repeat constructor; apply asp_sub; asp_in.
  - asp_lift_tac ltac:(apply cspecs_sub_refl) G1. constructor.
  - asp_lift_tac asp_sub_tac D1. constructor.
  - asp_lift_tac asp_sub_tac D2. constructor; [exact asp_cov_get_donna | constructor].
  - asp_lift_tac asp_sub_tac D3. constructor; [exact asp_cov_get_donna | constructor].
  - asp_lift_tac asp_sub_tac D4. repeat constructor; apply asp_sub; asp_in.
  - asp_lift_tac asp_sub_tac S1. constructor; [exact asp_cov_memset | constructor].
  - asp_lift_tac asp_sub_tac S2. repeat constructor; apply asp_sub; asp_in.
  - asp_lift_tac asp_sub_tac S3. repeat constructor; apply asp_sub; asp_in.
  - asp_lift_tac asp_sub_tac S4. repeat constructor; apply asp_sub; asp_in.
  - asp_lift_tac asp_sub_tac S5. constructor; [exact asp_cov_get_poly | repeat constructor; apply asp_sub; asp_in].
  - asp_lift_tac asp_sub_tac U1. constructor; [exact asp_cov_memcpy | repeat constructor; apply asp_sub; asp_in].
  - asp_lift_tac asp_sub_tac U2. constructor; [exact asp_cov_memset | repeat constructor; apply asp_sub; asp_in].
Qed.

(* ---------- the harness ---------- *)
Lemma asp_bodies_harness : asm_bodies W_asp p Gw asp_G.
Proof.
  apply (asm_piece_lift W_asp p Gw [u_asp] asp_imports asp_G (asp_piece Hkit)).
  - apply asp_norepet.
  - intros x Hx. unfold asp_G in Hx.
    repeat destruct Hx as [<-|Hx]; try contradiction;
      first [ left; reflexivity
            | apply asm_Gr_gp_incl; unfold asp_Gr; apply in_app; right; apply filter_In; split;
                [unfold asp_G; asp_in | reflexivity] ].
  - constructor; [| constructor]. split; [apply cspecs_sub_refl |]. split; [| split].
    + constructor.
    + apply asm_covers_incl; [apply asp_norepet' |].
      intros x Hx. unfold asp_imports in Hx.
      repeat destruct Hx as [<-|Hx]; try contradiction;
        first [ solve [apply asm_Gr_gp_incl; unfold asp_Gr, asp_Glib, libc_mem_G; simpl; asp_in]
              | solve [apply asm_E_gp_incl; [unfold env_specs_gp, asm_env.env_specs; simpl; asp_in | reflexivity]] ].
    + intros i f Hi Hf. vm_compute in Hi.
      repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
        (split; [vm_compute; reflexivity | repeat constructor]).
Qed.

Lemma asp_bodies :
  asm_bodies W_asp p Gw ((QP.prog_main p, QPmain_spec_ext' p tt asp_post) :: asp_Gr).
Proof.
  apply (asm_bodies_incl _ _ _ _ _ _ asp_bodies_lib asp_bodies_harness).
  intros x Hx. apply in_app. destruct Hx as [<-|Hx].
  - right. unfold asp_G. asp_in.
  - unfold asp_Gr in Hx. apply in_app in Hx as [Hx|Hx]; [left; auto |].
    right. apply filter_In in Hx as [Hx _]; auto.
Qed.
End Assembly.

Lemma ae_split_poly1305_safe_kit : wl_kit_ok -> harness_safe WgNoise.contracts.ae_split_poly1305.whole_prog.
Proof.
  intros Hkit.
  exact (asm_harness_safe_gp p world_OK_whole_asp W_asp W_asp_eq asp_cbc asp_ext_ok asp_post
           asp_Gr asp_ids asp_IDS asp_check asp_cc (asp_bodies Hkit)).
Qed.
