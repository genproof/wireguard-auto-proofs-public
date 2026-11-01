(* law transport_order (harness/transport_order.c), the assembly, with asm_lib.asm_harness_safe, from:
   - the libc piece (libc_piece.v), the BLAKE2s piece (hypothesis blake2s3_ok: memzero_explicit,
     get_unaligned_le32, imported by the AEAD units),
   - the CONCRETE AEAD piece aead_piece3b (aead_G3b: any length; aead_model's aead_enc / aead_dec),
   - the counter piece cnt_piece3 (wg_counter_validate),
   - the shared common.h bodies, the NULL-tolerant reference AEAD, the transport.h / harness bodies (ht4o_wm_body_a/c, ht4o_rc_body) and main
     (ht4o_main), each lifted into the whole program by asm_lib.asm_body_lift.
   Every other function of the program (noise.c, cookie.c, the shim, data_header, ...) gets asm_lib's vacuous
   specification. *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.floyd.subsume_funspec.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.common.wg3_iface.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.assembly.asm_xcs_aead3.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.libc.libc_piece.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.blake2s.b2s_spec3.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.aead.aead_bytes.
Require Import WgNoise.proof.aead.aead_spec3b.
Require WgNoise.proof.aead.aead_piece3b.
Require Import WgNoise.proof.counter.counter_spec.
Require WgNoise.proof.counter.cnt_piece3.
Require Import WgNoise.proof.harness.common4t.ht4_worlds.
Require Import WgNoise.proof.harness.common4t.ht4c_spec.
Require Import WgNoise.proof.harness.common4t.ht4r_spec.
Require Import WgNoise.proof.harness.common4t.ht4a_aead.
Require WgNoise.proof.harness.common4t.ht4c_small_body WgNoise.proof.harness.common4t.ht4c_chacha_body
        WgNoise.proof.harness.common4t.ht4c_rp_body WgNoise.proof.harness.common4t.ht4c_rpmul_body
        WgNoise.proof.harness.common4t.ht4c_rpfinal_order WgNoise.proof.harness.common4t.ht4r_piece.
Require WgNoise.proof.harness.prim_aead.haead_piece3.
Require Import WgNoise.proof.harness.transport_order.ht4o_main_defs.
Require WgNoise.proof.harness.transport_order.ht4o_wm_body_a WgNoise.proof.harness.transport_order.ht4o_wm_body_c
        WgNoise.proof.harness.transport_order.ht4o_rc_body WgNoise.proof.harness.transport_order.ht4o_main.
Require WgNoise.contracts.x_transport_order.
Require WgNoise.harness.x_prim_aead.code.

Local Notation p := WgNoise.contracts.x_transport_order.whole_prog.
Local Notation W := W_transport_order.

(* ---------------------------------------------------------------------- *)
(* The specifications                                                      *)
(* ---------------------------------------------------------------------- *)

(* the harness's functions but main: common.h helpers and rp_final, reference AEAD, the
   two draws, the shadow model and the harness's own *)
Definition ht4o_Gh : funspecs :=
  ht4r_Gprog ht4o_mp ++ [ht4_draw_size_spec; ht4_draw_u64_spec] ++ ht4o_wm_G.

Definition ht4o_ids : list ident :=
  ltac:(let l := eval compute in (map fst (libc_G W ++ blake2s_G3 ++ aead_G3b ++ cnt_G ++ ht4o_Gh)) in exact l).

Lemma ht4o_check : asm_check W p ht4o_ids = true.
Proof. vm_compute; reflexivity. Qed.

Lemma ht4o_cbc : forall H, cenv_built_correctly
    (map compdef_of_compenv_element (sort_rank (Maps.PTree.elements (QP.prog_comp_env p)) []))
    (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) = Errors.OK tt.
Proof. intro; reflexivity. Qed.

Lemma ht4o_ext_ok : all_unspecified_OK p.
Proof. reflexivity. Qed.

Lemma ht4o_cs_sub cs : In cs all_unit_cs -> cspecs_sub cs W.
Proof.
  destruct world_ok_transport_order as [_ [_ [_ HF]]]. rewrite Forall_forall in HF. intros H. apply HF.
  right. right. auto.
Qed.

Ltac ht4o_in_cs := unfold all_unit_cs; simpl; repeat first [left; reflexivity | right].

Ltac ht4o_varspecs :=
  apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [<-|Hx]; try contradiction;
  vm_compute; reflexivity.

Ltac ht4o_funs :=
  intros i f Hi Hf; vm_compute in Hi;
  repeat destruct Hi as [<-|Hi]; try contradiction; vm_compute in Hf; inv Hf;
  (split; [vm_compute; reflexivity | repeat constructor]).

Lemma ht4o_cc_h : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) (aead_G3b ++ cnt_G ++ ht4o_Gh).
Proof.
  unfold aead_G3b, cnt_G, ht4o_Gh, ht4r_Gprog, ht4c_G0, ht4c_G1, ht4r_G, ht4o_wm_G. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; reflexivity.
Qed.

(* byte arrays (and u32 arrays) are the same in every compspecs *)
Lemma ht4o_align_tuint_cs (ce1 ce2: composite_env) n z :
  align_compatible_rec ce1 (tarray tuint n) z -> align_compatible_rec ce2 (tarray tuint n) z.
Proof.
  intros H. apply align_compatible_rec_Tarray. intros i Hi.
  eapply align_compatible_rec_Tarray_inv in H; [| exact Hi].
  inv H. econstructor; eauto.
Qed.

Lemma ht4o_minusp_cs {cs1 cs2: compspecs} mp gv : @ht4_minusp cs1 mp gv = @ht4_minusp cs2 mp gv.
Proof.
  unfold ht4_minusp, data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible, align_compatible, size_compatible; simpl.
  split; intros (? & ? & ? & ? & ?); repeat split; auto; destruct (gv mp); auto.
  all: first [ exact (ht4o_align_tuint_cs (@cenv_cs cs1) (@cenv_cs cs2) _ _ ltac:(eassumption))
             | exact (ht4o_align_tuint_cs (@cenv_cs cs2) (@cenv_cs cs1) _ _ ltac:(eassumption)) ].
Qed.

Ltac ht4o_conv c1 c2 :=
  repeat first
    [ rewrite (@aead_data_at_tuchar_cs c1 c2)
    | rewrite (@aead_data_at__tuchar_cs c1 c2)
    | rewrite (@ht4a_prim_bytes c1 c2)
    | rewrite (@ht4a_prim_out c1 c2)
    | rewrite (@ht4a_zero_page c1 c2)
    | rewrite (@ht4o_minusp_cs c1 c2) ].

Ltac ht4o_sub c1 c2 :=
  apply NDsubsume_subsume; [split; reflexivity |];
  split; [split; reflexivity |];
  let x := fresh "x" in let g := fresh "gargs" in
  intros x g; Exists x (@emp mpred _ _); repeat (destruct x as [x ?]); simpl;
  rewrite emp_sepcon; ht4o_conv c1 c2;
  apply andp_right; [apply andp_left2; auto |];
  apply prop_right; let r := fresh "rho" in intros r; rewrite emp_sepcon; apply andp_left2; ht4o_conv c1 c2;
  first [apply derives_refl | auto].

Lemma ht4o_sub_le32 : funspec_sub (snd (@ht4_le32_store_spec W_prim_aead)) (snd (@ht4_le32_store_spec W)).
Proof. ht4o_sub W_prim_aead W. Qed.
Lemma ht4o_sub_le64 : funspec_sub (snd (@ht4_le64_store_spec W_prim_aead)) (snd (@ht4_le64_store_spec W)).
Proof. ht4o_sub W_prim_aead W. Qed.
Lemma ht4o_sub_bytes_eq : funspec_sub (snd (@ht4_bytes_eq_spec W_prim_aead)) (snd (@ht4_bytes_eq_spec W)).
Proof. ht4o_sub W_prim_aead W. Qed.
Lemma ht4o_sub_ref_dec :
  funspec_sub (snd (ref_aead_decrypt_spec_n W_prim_aead ht4o_mp)) (snd (ref_aead_decrypt_spec_n W ht4o_mp)).
Proof. ht4o_sub W_prim_aead W. Qed.
Lemma ht4o_sub_draw_u64 : funspec_sub (snd ht4_draw_u64_spec) (snd haead_spec3.draw_u64_spec).
Proof. apply funspec_sub_refl. Qed.

Section Assembly.
Variable Gb: funspecs.
Variable Hpiece: piece_ok blake2s_units3 blake2s_imports3 Gb.
Variable Hids: map fst Gb = map fst blake2s_G3.
Variable Hcov: asm_covers Gb blake2s_G3.

(* the real specifications, main excepted *)
Definition ht4o_Gr : funspecs := libc_G W ++ Gb ++ aead_G3b ++ cnt_G ++ ht4o_Gh.

Local Notation Gw := (@asm_Gall W p ht4o_post ht4o_Gr ht4o_ids).

Lemma ht4o_IDS : map fst ht4o_Gr = ht4o_ids.
Proof. unfold ht4o_Gr. rewrite !map_app, Hids. reflexivity. Qed.

Lemma ht4o_norepet : list_norepet (map fst (QPvarspecs p) ++ map fst Gw).
Proof. apply asm_Gall_norepet; [apply ht4o_IDS | apply ht4o_check]. Qed.

Lemma ht4o_norepet' : list_norepet (map fst Gw).
Proof. apply asm_Gall_norepet'; [apply ht4o_IDS | apply ht4o_check]. Qed.

Lemma ht4o_find_Gr i s : In (i, s) ht4o_Gr -> initial_world.find_id i Gw = Some s.
Proof. intros H. apply initial_world.find_id_i; [| apply ht4o_norepet']. apply asm_Gr_incl; auto. Qed.

Lemma ht4o_in_libc ix : In ix (libc_G W) -> In ix ht4o_Gr.
Proof. intros H. unfold ht4o_Gr. apply in_app; left; auto. Qed.
Lemma ht4o_in_b2s ix : In ix Gb -> In ix ht4o_Gr.
Proof. intros H. unfold ht4o_Gr. apply in_app; right; apply in_app; left; auto. Qed.
Lemma ht4o_in_aead ix : In ix aead_G3b -> In ix ht4o_Gr.
Proof. intros H. unfold ht4o_Gr. do 2 (apply in_app; right). apply in_app; left; auto. Qed.
Lemma ht4o_in_cnt ix : In ix cnt_G -> In ix ht4o_Gr.
Proof. intros H. unfold ht4o_Gr. do 3 (apply in_app; right). apply in_app; left; auto. Qed.
Lemma ht4o_in_h ix : In ix ht4o_Gh -> In ix ht4o_Gr.
Proof. intros H. unfold ht4o_Gr. do 4 (apply in_app; right). auto. Qed.

(* an entry of Gr covers an import with the same specification *)
Lemma ht4o_cov_in ix : In ix ht4o_Gr -> exists s, initial_world.find_id (fst ix) Gw = Some s /\ funspec_sub s (snd ix).
Proof. intros H. exists (snd ix). split; [apply ht4o_find_Gr; destruct ix; auto | apply funspec_sub_refl]. Qed.

(* an entry of Gr covers an import by a funspec_sub *)
Lemma ht4o_cov_sub i s0 s1 : In (i, s0) ht4o_Gr -> funspec_sub s0 s1 ->
  exists s, initial_world.find_id i Gw = Some s /\ funspec_sub s s1.
Proof. intros H S. exists s0. split; [apply ht4o_find_Gr; auto | exact S]. Qed.

(* an environment entry *)
Lemma ht4o_cov_env i s : In (i, s) (@asm_env.env_specs W) -> asm_present_ext p i = true ->
  exists s', initial_world.find_id i Gw = Some s' /\ funspec_sub s' s.
Proof.
  intros H1 H2. exists s. split; [| apply funspec_sub_refl].
  apply initial_world.find_id_i; [apply asm_E_incl; auto | apply ht4o_norepet'].
Qed.

Ltac ht4o_inl := simpl; repeat first [left; reflexivity | right]; fail.

(* an entry of the BLAKE2s interface: Gb's entry is in Gw and covers it *)
Lemma ht4o_b2s_entry i s0 : In (i, s0) blake2s_G3 ->
  exists s, initial_world.find_id i Gw = Some s /\ funspec_sub s s0.
Proof.
  intros H. unfold asm_covers in Hcov. rewrite Forall_forall in Hcov.
  destruct (Hcov _ H) as [s [Fs Sub]]; simpl in Fs.
  exists s; split; auto. apply ht4o_find_Gr, ht4o_in_b2s. apply initial_world.find_id_e; auto.
Qed.

(* ---------- libc ---------- *)
Lemma ht4o_bodies_libc : asm_bodies W p Gw (libc_G W).
Proof.
  apply (asm_piece_lift W p Gw [u_libc; u_shim; u_curve25519] (libc_imports W) (libc_G W) (libc_piece W)).
  - apply ht4o_norepet.
  - intros x Hx. apply asm_Gr_incl, ht4o_in_libc; auto.
  - assert (CI: forall cs, asm_covers Gw (libc_imports W cs)).
    { intros cs. apply asm_covers_incl; [apply ht4o_norepet' |].
      intros [i s] Hx. destruct Hx as [Hx|[]]. inv Hx. apply asm_E_incl; [left; reflexivity | reflexivity]. }
    constructor; [| constructor; [| constructor; [| constructor]]].
    all: split; [apply ht4o_cs_sub; ht4o_in_cs |]; split; [ht4o_varspecs |]; split; [apply CI | ht4o_funs].
Qed.

(* ---------- BLAKE2s ---------- *)
#[local] Instance ht4o_cce_libc_b2s : change_composite_env Libc.CS Blake2s.CS.
Proof. make_cs_preserve Libc.CS Blake2s.CS. Defined.
#[local] Instance ht4o_cce_libc_cookie : change_composite_env Libc.CS Cookie.CS.
Proof. make_cs_preserve Libc.CS Cookie.CS. Defined.

Lemma ht4o_covers_b2s_imports cs (CCE: change_composite_env Libc.CS cs) :
  asm_covers Gw (blake2s_imports3 cs).
Proof.
  constructor; [| constructor; [| constructor]].
  - exists (snd (@memcpy_spec Libc.CS)). split.
    + apply ht4o_find_Gr, ht4o_in_libc. left; reflexivity.
    + apply (@xa3_memcpy_sub Libc.CS cs CCE).
  - exists (snd (@memset_spec Libc.CS)). split.
    + apply ht4o_find_Gr, ht4o_in_libc. right; left; reflexivity.
    + apply (@xa3_memset_sub Libc.CS cs CCE).
Qed.

Lemma ht4o_bodies_b2s : asm_bodies W p Gw Gb.
Proof.
  apply (asm_piece_lift W p Gw [u_blake2s; u_cookie] blake2s_imports3 Gb Hpiece).
  - apply ht4o_norepet.
  - intros x Hx. apply asm_Gr_incl, ht4o_in_b2s; auto.
  - rewrite Hids.
    constructor; [| constructor; [| constructor]].
    + split; [apply ht4o_cs_sub; ht4o_in_cs |]. split; [ht4o_varspecs |].
      split; [apply (ht4o_covers_b2s_imports Blake2s.CS ht4o_cce_libc_b2s) | ht4o_funs].
    + split; [apply ht4o_cs_sub; ht4o_in_cs |]. split; [ht4o_varspecs |].
      split; [apply (ht4o_covers_b2s_imports Cookie.CS ht4o_cce_libc_cookie) | ht4o_funs].
Qed.

(* ---------- AEAD (the concrete piece) ---------- *)
Ltac ht4o_cce a b := make_cs_preserve a b.
#[local] Instance ht4o_cce_l1 : change_composite_env Libc.CS Chacha.CS. Proof. ht4o_cce Libc.CS Chacha.CS. Defined.
#[local] Instance ht4o_cce_l2 : change_composite_env Libc.CS ChachaBlock.CS. Proof. ht4o_cce Libc.CS ChachaBlock.CS. Defined.
#[local] Instance ht4o_cce_l3 : change_composite_env Libc.CS Poly1305.CS. Proof. ht4o_cce Libc.CS Poly1305.CS. Defined.
#[local] Instance ht4o_cce_l4 : change_composite_env Libc.CS Poly1305Donna32.CS. Proof. ht4o_cce Libc.CS Poly1305Donna32.CS. Defined.
#[local] Instance ht4o_cce_l5 : change_composite_env Libc.CS Chacha20poly1305.CS. Proof. ht4o_cce Libc.CS Chacha20poly1305.CS. Defined.
#[local] Instance ht4o_cce_l6 : change_composite_env Libc.CS Shim.CS. Proof. ht4o_cce Libc.CS Shim.CS. Defined.
#[local] Instance ht4o_cce_b1 : change_composite_env Blake2s.CS Chacha.CS. Proof. ht4o_cce Blake2s.CS Chacha.CS. Defined.
#[local] Instance ht4o_cce_b2 : change_composite_env Blake2s.CS ChachaBlock.CS. Proof. ht4o_cce Blake2s.CS ChachaBlock.CS. Defined.
#[local] Instance ht4o_cce_b3 : change_composite_env Blake2s.CS Poly1305.CS. Proof. ht4o_cce Blake2s.CS Poly1305.CS. Defined.
#[local] Instance ht4o_cce_b4 : change_composite_env Blake2s.CS Poly1305Donna32.CS. Proof. ht4o_cce Blake2s.CS Poly1305Donna32.CS. Defined.
#[local] Instance ht4o_cce_b5 : change_composite_env Blake2s.CS Chacha20poly1305.CS. Proof. ht4o_cce Blake2s.CS Chacha20poly1305.CS. Defined.
#[local] Instance ht4o_cce_b6 : change_composite_env Blake2s.CS Shim.CS. Proof. ht4o_cce Blake2s.CS Shim.CS. Defined.
#[local] Instance ht4o_cce_c1 : change_composite_env Curve25519.CS Chacha.CS. Proof. ht4o_cce Curve25519.CS Chacha.CS. Defined.
#[local] Instance ht4o_cce_c2 : change_composite_env Curve25519.CS ChachaBlock.CS. Proof. ht4o_cce Curve25519.CS ChachaBlock.CS. Defined.
#[local] Instance ht4o_cce_c3 : change_composite_env Curve25519.CS Poly1305.CS. Proof. ht4o_cce Curve25519.CS Poly1305.CS. Defined.
#[local] Instance ht4o_cce_c4 : change_composite_env Curve25519.CS Poly1305Donna32.CS. Proof. ht4o_cce Curve25519.CS Poly1305Donna32.CS. Defined.
#[local] Instance ht4o_cce_c5 : change_composite_env Curve25519.CS Chacha20poly1305.CS. Proof. ht4o_cce Curve25519.CS Chacha20poly1305.CS. Defined.
#[local] Instance ht4o_cce_c6 : change_composite_env Curve25519.CS Shim.CS. Proof. ht4o_cce Curve25519.CS Shim.CS. Defined.

Lemma ht4o_covers_aead_imports cs (C1: change_composite_env Libc.CS cs) (C2: change_composite_env Blake2s.CS cs)
    (C3: change_composite_env Curve25519.CS cs) :
  asm_covers Gw (aead_imports3 cs).
Proof.
  constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]].
  - exists (snd (@memcpy_spec Libc.CS)). split.
    + apply ht4o_find_Gr, ht4o_in_libc. left; reflexivity.
    + apply (@xa3_memcpy_sub Libc.CS cs C1).
  - exists (snd (@memset_spec Libc.CS)). split.
    + apply ht4o_find_Gr, ht4o_in_libc. right; left; reflexivity.
    + apply (@xa3_memset_sub Libc.CS cs C1).
  - destruct (ht4o_b2s_entry _ _ (ltac:(unfold blake2s_G3; simpl; repeat (first [left; reflexivity | right]))
        : In (@memzero_explicit_spec Blake2s.CS) blake2s_G3)) as [s [Fs Sub]].
    exists s; split; [exact Fs |]. eapply funspec_sub_trans; [exact Sub |].
    apply (@xa3_memzero_explicit_sub Blake2s.CS cs C2).
  - destruct (ht4o_b2s_entry _ _ (ltac:(unfold blake2s_G3; simpl; repeat (first [left; reflexivity | right]))
        : In (@get_unaligned_le32_spec Blake2s.CS) blake2s_G3)) as [s [Fs Sub]].
    exists s; split; [exact Fs |]. eapply funspec_sub_trans; [exact Sub |].
    apply (@xa3_get_unaligned_le32_sub Blake2s.CS cs C2).
  - exists (snd (@crypto_memneq_spec Curve25519.CS)). split.
    + apply ht4o_find_Gr, ht4o_in_libc. unfold libc_G; simpl; repeat (first [left; reflexivity | right]).
    + apply (@xa3_crypto_memneq_sub Curve25519.CS cs C3).
Qed.

Lemma ht4o_bodies_aead : asm_bodies W p Gw aead_G3b.
Proof.
  apply (asm_piece_lift W p Gw aead_units3 aead_imports3 aead_G3b (proj1 aead_piece3b.aead_piece3b)).
  - apply ht4o_norepet.
  - intros x Hx. apply asm_Gr_incl, ht4o_in_aead; auto.
  - unfold aead_units3.
    constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]]].
    all: split; [apply ht4o_cs_sub; ht4o_in_cs |]; split; [ht4o_varspecs |].
    all: split; [apply ht4o_covers_aead_imports; typeclasses eauto | ht4o_funs].
Qed.

(* ---------- the counter piece ---------- *)
Lemma ht4o_bodies_cnt : asm_bodies W p Gw cnt_G.
Proof.
  apply (asm_piece_lift W p Gw [u_counter] cnt_imports cnt_G cnt_piece3.cnt_piece3).
  - apply ht4o_norepet.
  - intros x Hx. apply asm_Gr_incl, ht4o_in_cnt; auto.
  - constructor; [| constructor].
    split; [apply ht4o_cs_sub; ht4o_in_cs |]. split; [ht4o_varspecs |].
    split; [constructor | ht4o_funs].
Qed.

(* ---------- the harness's functions ---------- *)

(* one body, proved at compspecs csu with varspecs Vu and context Gu, lifted into the whole program *)
Lemma ht4o_lift (csu: compspecs) (Vu: varspecs) (Gu: funspecs) f ip :
  cspecs_sub csu W ->
  Maps.PTree.get (fst ip) (QP.prog_defs p) = Some (Gfun (Internal f)) ->
  Forall (fun it => complete_type (@cenv_cs csu) (snd it) = true) (fn_vars f) ->
  Forall (fun it => initial_world.find_id (fst it) (QPvarspecs p) = Some (snd it)) Vu ->
  asm_covers Gw Gu ->
  @semax_body Vu Gu csu f ip ->
  exists f', Maps.PTree.get (fst ip) (QP.prog_defs p) = Some (Gfun (Internal f')) /\
             @semax_body (QPvarspecs p) Gw W f' ip.
Proof.
  intros CS D C HV HG SB. exists f. split; auto.
  exact (asm_body_lift Vu (QPvarspecs p) Gu Gw f ip CS C ht4o_norepet HV HG SB).
Qed.

Lemma ht4o_pa_sub : cspecs_sub W_prim_aead W.
Proof. exact ht4_prim_aead_sub_transport_order. Qed.

Lemma ht4o_cov_G1 : asm_covers Gw ht4c_G1.
Proof.
  apply asm_covers_incl; [apply ht4o_norepet' |]. intros x Hx. apply asm_Gr_incl, ht4o_in_h.
  unfold ht4o_Gh, ht4r_Gprog, ht4c_G0. apply in_app; left. apply in_app; left. apply in_app; left. exact Hx.
Qed.

Lemma ht4o_cov_G0mp : asm_covers Gw (ht4c_G0 ht4o_mp).
Proof.
  apply asm_covers_incl; [apply ht4o_norepet' |]. intros x Hx. apply asm_Gr_incl, ht4o_in_h.
  unfold ht4o_Gh, ht4r_Gprog. apply in_app; left. apply in_app; left. exact Hx.
Qed.

Lemma ht4o_cov_Gd : asm_covers Gw ht4c_Gd.
Proof.
  constructor; [| constructor; [| constructor]].
  - apply ht4o_cov_env; [ht4o_inl | reflexivity].
  - apply ht4o_cov_env; [ht4o_inl | reflexivity].
Qed.

Lemma ht4o_cov_mem : asm_covers Gw ht4o_G_mem.
Proof.
  constructor; [| constructor; [| constructor]].
  - apply ht4o_cov_env; [ht4o_inl | reflexivity].
  - apply ht4o_cov_env; [ht4o_inl | reflexivity].
Qed.

Lemma ht4o_cov_draw : asm_covers Gw ht4o_G_draw.
Proof.
  constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]].
  - apply ht4o_cov_env; [ht4o_inl | reflexivity].
  - apply ht4o_cov_env; [ht4o_inl | reflexivity].
  - apply ht4o_cov_env; [ht4o_inl | reflexivity].
  - eapply ht4o_cov_sub; [apply ht4o_in_h; unfold ht4o_Gh; ht4o_inl | exact ht4o_sub_draw_u64].
Qed.

Lemma ht4o_cov_nil : asm_covers Gw [].
Proof. constructor. Qed.

Lemma ht4o_cov_main : asm_covers Gw ht4o_G0.
Proof.
  unfold ht4o_G0.
  repeat apply Forall_cons; try apply Forall_nil; cbv beta.
  all: first
    [ apply ht4o_cov_env; [ht4o_inl | reflexivity]
    | apply ht4o_cov_in; apply ht4o_in_h; unfold ht4o_Gh, ht4o_wm_G; ht4o_inl
    | apply ht4o_cov_in; apply ht4o_in_cnt; unfold cnt_G; ht4o_inl
    | idtac ].
  - eapply ht4o_cov_sub; [apply ht4o_in_h; unfold ht4o_Gh, ht4r_Gprog, ht4c_G0, ht4c_G1; ht4o_inl | exact ht4o_sub_le32].
  - eapply ht4o_cov_sub; [apply ht4o_in_h; unfold ht4o_Gh, ht4r_Gprog, ht4c_G0, ht4c_G1; ht4o_inl | exact ht4o_sub_le64].
  - eapply ht4o_cov_sub; [apply ht4o_in_aead; unfold aead_G3b; ht4o_inl | exact (ht4_encrypt_sub W)].
  - eapply ht4o_cov_sub; [apply ht4o_in_aead; unfold aead_G3b; ht4o_inl | exact (ht4_decrypt_sub W)].
  - eapply ht4o_cov_sub; [apply ht4o_in_h; unfold ht4o_Gh, ht4r_Gprog, ht4r_G; ht4o_inl | exact ht4o_sub_ref_dec].
  - eapply ht4o_cov_sub; [apply ht4o_in_h; unfold ht4o_Gh, ht4r_Gprog, ht4c_G0, ht4c_G1; ht4o_inl | exact ht4o_sub_bytes_eq].
Qed.

Ltac ht4o_one_pa B G :=
  refine (ht4o_lift W_prim_aead [] _ _ _ ht4o_pa_sub _ _ _ _ B);
  [vm_compute; reflexivity | vm_compute; repeat constructor | constructor | exact G].
Ltac ht4o_one_w B G :=
  refine (ht4o_lift W ht4o_V0 _ _ _ (@cspecs_sub_refl W) _ _ _ _ B);
  [vm_compute; reflexivity | vm_compute; repeat constructor | constructor | exact G].

Lemma ht4o_bodies_h1 : asm_bodies W p Gw (ht4c_G0 ht4o_mp).
Proof.
  destruct WgNoise.proof.harness.common4t.ht4c_small_body.ht4c_small_bodies
    as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
  destruct WgNoise.proof.harness.common4t.ht4c_chacha_body.ht4c_chacha_bodies as (C1 & C2 & C3 & C4 & C5).
  destruct WgNoise.proof.harness.common4t.ht4c_rp_body.ht4c_rp_bodies as (R1 & R2 & R3).
  pose proof WgNoise.proof.harness.common4t.ht4c_rpmul_body.ht4cm_rpmul_body as R4.
  pose proof WgNoise.proof.harness.common4t.ht4c_rpfinal_order.ht4co_rp_final_body as R5.
  unfold asm_bodies, ht4c_G0, ht4c_G1.
  repeat apply Forall_cons; try apply Forall_nil.
  - ht4o_one_pa S1 ht4o_cov_G1.
  - ht4o_one_pa S2 ht4o_cov_G1.
  - ht4o_one_pa S3 ht4o_cov_G1.
  - ht4o_one_pa S4 ht4o_cov_G1.
  - ht4o_one_pa S7 ht4o_cov_G1.
  - ht4o_one_pa S8 ht4o_cov_G1.
  - ht4o_one_pa S9 ht4o_cov_G1.
  - ht4o_one_pa C1 ht4o_cov_G1.
  - ht4o_one_pa C2 ht4o_cov_G1.
  - ht4o_one_pa C3 ht4o_cov_G1.
  - ht4o_one_pa C4 ht4o_cov_G1.
  - ht4o_one_pa C5 ht4o_cov_G1.
  - ht4o_one_pa R1 ht4o_cov_G1.
  - ht4o_one_pa R2 ht4o_cov_G1.
  - ht4o_one_pa R4 ht4o_cov_G1.
  - ht4o_one_pa R3 ht4o_cov_G1.
  - refine (ht4o_lift W_prim_aead (ht4c_Vmp ht4o_mp) _ _ _ ht4o_pa_sub _ _ _ _ R5);
      [vm_compute; reflexivity | vm_compute; repeat constructor | ht4o_varspecs | exact ht4o_cov_G0mp].
Qed.

Lemma ht4o_bodies_ref : asm_bodies W p Gw (ht4r_G ht4o_mp).
Proof.
  apply (asm_piece_lift W p Gw [u_ht4r] (fun _ => ht4c_G0 ht4o_mp) (ht4r_G ht4o_mp)
           (WgNoise.proof.harness.common4t.ht4r_piece.ht4r_piece ht4o_mp
              WgNoise.proof.harness.prim_aead.haead_piece3.haead_hyps_ok)).
  - apply ht4o_norepet.
  - intros x Hx. apply asm_Gr_incl, ht4o_in_h. unfold ht4o_Gh, ht4r_Gprog. apply in_app; left; apply in_app; right; auto.
  - constructor; [| constructor].
    split; [exact ht4o_pa_sub |]. split; [constructor |].
    split; [exact ht4o_cov_G0mp | ht4o_funs].
Qed.

Lemma ht4o_bodies_draws : asm_bodies W p Gw [ht4_draw_size_spec; ht4_draw_u64_spec].
Proof.
  destruct WgNoise.proof.harness.common4t.ht4c_small_body.ht4c_small_bodies
    as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
  repeat apply Forall_cons; try apply Forall_nil.
  - ht4o_one_pa S5 ht4o_cov_Gd.
  - ht4o_one_pa S6 ht4o_cov_Gd.
Qed.

Lemma ht4o_bodies_wm : asm_bodies W p Gw ht4o_wm_G.
Proof.
  pose proof WgNoise.proof.harness.transport_order.ht4o_wm_body_a.ht4o_body_wm_init as A0.
  destruct WgNoise.proof.harness.transport_order.ht4o_wm_body_a.ht4o_wm_bodies_a as (A1 & A2).
  pose proof WgNoise.proof.harness.transport_order.ht4o_wm_body_c.ht4o_body_wm_commit as C1.
  pose proof WgNoise.proof.harness.transport_order.ht4o_rc_body.ht4o_body_draw_steps as D0.
  destruct WgNoise.proof.harness.transport_order.ht4o_rc_body.ht4o_rc_bodies as (R1 & R2 & R3 & R4).
  unfold asm_bodies, ht4o_wm_G.
  repeat apply Forall_cons; try apply Forall_nil.
  - ht4o_one_w D0 ht4o_cov_draw.
  - ht4o_one_w R4 ht4o_cov_draw.
  - ht4o_one_w A0 ht4o_cov_nil.
  - ht4o_one_w A1 ht4o_cov_nil.
  - ht4o_one_w C1 ht4o_cov_mem.
  - ht4o_one_w A2 ht4o_cov_mem.
  - ht4o_one_w R1 ht4o_cov_nil.
  - ht4o_one_w R2 ht4o_cov_nil.
  - ht4o_one_w R3 ht4o_cov_nil.
Qed.

Lemma ht4o_bodies_main : asm_bodies W p Gw [(QP.prog_main p, QPmain_spec_ext' p tt ht4o_post)].
Proof.
  apply Forall_cons; [| apply Forall_nil].
  change (QP.prog_main p, QPmain_spec_ext' p tt ht4o_post) with ht4o_main_spec.
  refine (ht4o_lift W ht4o_V _ _ _ (@cspecs_sub_refl W) _ _ _ _
           WgNoise.proof.harness.transport_order.ht4o_main.ht4o_main_body);
    [vm_compute; reflexivity | vm_compute; repeat constructor | ht4o_varspecs | exact ht4o_cov_main].
Qed.

Lemma ht4o_cc : Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) ht4o_Gr.
Proof.
  unfold ht4o_Gr. apply Forall_app; split; [repeat constructor |].
  apply Forall_app; split; [| exact ht4o_cc_h].
  apply (xa3_cc_of_covers Gb blake2s_G3); auto; [apply Hpiece | repeat constructor].
Qed.

Lemma ht4o_bodies :
  asm_bodies W p Gw ((QP.prog_main p, QPmain_spec_ext' p tt ht4o_post) :: ht4o_Gr).
Proof.
  assert (H: asm_bodies W p Gw ([(QP.prog_main p, QPmain_spec_ext' p tt ht4o_post)] ++ libc_G W ++ Gb ++
               aead_G3b ++ cnt_G ++ (ht4c_G0 ht4o_mp ++ ht4r_G ht4o_mp) ++ [ht4_draw_size_spec; ht4_draw_u64_spec] ++
               ht4o_wm_G)).
  { unfold asm_bodies. rewrite !Forall_app.
    split; [exact ht4o_bodies_main |]. split; [exact ht4o_bodies_libc |]. split; [exact ht4o_bodies_b2s |].
    split; [exact ht4o_bodies_aead |]. split; [exact ht4o_bodies_cnt |].
    split; [split; [exact ht4o_bodies_h1 | exact ht4o_bodies_ref] |].
    split; [exact ht4o_bodies_draws | exact ht4o_bodies_wm]. }
  exact H.
Qed.

Lemma ht4o_safe : harness_safe p.
Proof.
  exact (asm_harness_safe p world_OK_whole_transport_order W W_transport_order_eq ht4o_cbc ht4o_ext_ok ht4o_post
           ht4o_Gr ht4o_ids ht4o_IDS ht4o_check ht4o_cc ht4o_bodies).
Qed.

End Assembly.

Theorem ht4o_transport_order_safe : blake2s3_ok -> harness_safe WgNoise.contracts.x_transport_order.whole_prog.
Proof.
  intros [Gb [Hp [Hi Hc]]]. exact (ht4o_safe Gb Hp Hi Hc).
Qed.
