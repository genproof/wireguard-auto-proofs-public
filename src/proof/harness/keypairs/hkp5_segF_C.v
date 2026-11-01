(* law keypairs, segment F piece C: statements 33..37 of main
   (CHECK(check_all); nlive = 0; the CHECK loop over live counting nlive; CHECK(allocs - allocs0 == frees - frees0
   + nlive); CHECK(the warnings 2, 1, 4 == warn0's)), hkp5_segF_defs.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.keypairs.hkp5_segF_defs.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

Lemma hkp5FC_tulong_cs {cs1 cs2: compspecs} sh v p :
  @data_at cs1 sh tulong v p = @data_at cs2 sh tulong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible; simpl.
  split; intros (?&?&?&?&?); (repeat split); auto;
    destruct p; try contradiction; unfold align_compatible in *;
    (apply align_compatible_rec_by_value with Mint64; [reflexivity|]);
    apply (align_compatible_rec_by_value_inv _ _ Mint64) in H2; auto.
Qed.

#[local] Instance hkp5FC_CCE : change_composite_env Noise.CS W_keypairs.
Proof. make_cs_preserve Noise.CS W_keypairs. Defined.

Lemma hkp5FC_warr_cs sh (v: list val) p :
  @data_at Noise.CS sh (tarray tulong 5) v p = @data_at W_keypairs sh (tarray tulong 5) v p.
Proof.
  refine (f_equal (fun f => f p) (@data_at_change_composite Noise.CS W_keypairs hkp5FC_CCE sh (tarray tulong 5) v v
    _ _)); [apply JMeq_refl | reflexivity].
Qed.

Lemma hkp5FC_fold x25519 F V Y (A B: mpred) :
  fold_right_sepcon (hkp5_SEP x25519 F V Y (A * B)) = fold_right_sepcon (hkp5_SEP x25519 F V Y A) * B.
Proof.
  unfold hkp5_SEP. rewrite !app_assoc, !fold_right_sepcon_app. cbn [fold_right_sepcon].
  rewrite !sepcon_emp. symmetry. apply sepcon_assoc.
Qed.

Lemma hkp5FC_SEPx {A0: Type} x25519 F V Y (A B: mpred) :
  @SEPx A0 (hkp5_SEP x25519 F V Y (A * B)) = SEPx [fold_right_sepcon (hkp5_SEP x25519 F V Y A); B].
Proof.
  unfold SEPx. extensionality rho. rewrite hkp5FC_fold. cbn [fold_right_sepcon]. rewrite sepcon_emp.
  reflexivity.
Qed.

(* the live list as a segment (ending in tl) and the rest *)
Fixpoint hkp5FC_seg (ML: list (val * hk5_mk)) (tl: val) : mpred :=
  match ML with
  | [] => emp
  | (m, M) :: ML' => hk5_node m M (match ML' with [] => tl | (a, _) :: _ => a end) * hkp5FC_seg ML' tl
  end.

Lemma hkp5FC_split : forall ML1 ML2,
  hk5_mklist (ML1 ++ ML2) = hkp5FC_seg ML1 (hk5_head ML2) * hk5_mklist ML2.
Proof.
  induction ML1 as [|[a A] ML1 IH]; intros; simpl.
  - rewrite emp_sepcon; auto.
  - rewrite IH, sepcon_assoc.
    replace (hk5_head (ML1 ++ ML2)) with (match ML1 with [] => hk5_head ML2 | (a0, _) :: _ => a0 end);
      [reflexivity|].
    destruct ML1 as [|[b B] ?]; reflexivity.
Qed.

Lemma hkp5FC_seg_snoc : forall ML1 m M tl,
  hkp5FC_seg (ML1 ++ [(m, M)]) tl = hkp5FC_seg ML1 m * hk5_node m M tl.
Proof.
  induction ML1 as [|[a A] ML1 IH]; intros; simpl.
  - rewrite emp_sepcon, sepcon_emp; auto.
  - rewrite IH, sepcon_assoc.
    replace (match ML1 ++ [(m, M)] with [] => tl | (a0, _) :: _ => a0 end)
      with (match ML1 with [] => m | (a0, _) :: _ => a0 end); [reflexivity|].
    destruct ML1 as [|[b B] ?]; reflexivity.
Qed.

Lemma hkp5FC_node_fold : forall m M nx, Zlength (m5_send M) = 32 /\ Zlength (m5_recv M) = 32 ->
  data_at Ews t_mk5 (hk5_mk_val M nx) m * malloc_token Ews t_mk5 m |-- hk5_node m M nx.
Proof.
  intros. unfold hk5_node. entailer!.
Qed.

Lemma hkp5FC_mklist_local_facts : forall ML, hk5_mklist ML |-- !! is_pointer_or_null (hk5_head ML).
Proof.
  intros [|[m M] ML]; simpl hk5_mklist; simpl hk5_head.
  - entailer!.
  - unfold hk5_node. entailer!.
Qed.

Lemma hkp5FC_mklist_valid : forall ML, hk5_mklist ML |-- valid_pointer (hk5_head ML).
Proof.
  intros [|[m M] ML]; simpl hk5_mklist; simpl hk5_head.
  - apply valid_pointer_null.
  - unfold hk5_node. Intros. apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. auto with valid_pointer.
Qed.

Lemma hkp5FC_fold_all ML ML1 ML2 : ML = ML1 ++ ML2 ->
  hkp5FC_seg ML1 (hk5_head ML2) * hk5_mklist ML2 |-- hk5_mklist ML.
Proof. intros ->. rewrite hkp5FC_split. apply derives_refl. Qed.

Lemma hkp5FC_node_fold_h m M nx : m5_hashed M = false -> Zlength (m5_send M) = 32 -> Zlength (m5_recv M) = 32 ->
  data_at Ews t_mk5
    ((m5_kp M, (Vint (m5_refs M), (Vlong (m5_held M), (Val.of_bool false, (Vint (m5_index M),
      (bytes (m5_send M), (bytes (m5_recv M), (Val.of_bool (m5_sv M), (Val.of_bool (m5_rv M),
      (Val.of_bool (m5_init M), (Vint (m5_rindex M), (Vlong (m5_birth M), (Vlong (m5_id M),
      (Vlong (m5_scnt M), (Vlong (m5_rcnt M), nx))))))))))))))) : reptype t_mk5) m *
  malloc_token Ews t_mk5 m |-- hk5_node m M nx.
Proof.
  intros Hh H1 H2. unfold hk5_node, hk5_mk_val. rewrite Hh. entailer!.
Qed.

(* every live node at the end: saturated and not hashed *)
Lemma hkp5FC_node_facts p OD OH H P KS T m M :
  hk5_rel p OD OH H P KS T -> hkp5F_P2 H -> In (m, M) (h5_ML H) ->
  m5_refs M = REFCOUNT_SATURATED /\ m5_hashed M = false.
Proof.
  intros (Hc & _) ((Hsp & Hsc & Hsn) & Hsat) I.
  destruct Hc as (_ & _ & Hnn & _ & _ & _ & _ & Hh & _).
  split.
  - rewrite Forall_forall in Hsat. exact (Hsat _ I).
  - rewrite Forall_forall in Hh. specialize (Hh _ I). cbn [fst snd] in Hh.
    destruct (m5_hashed M); [|reflexivity].
    exfalso. specialize (Hh eq_refl). unfold hk5_slots in Hh. rewrite Hsp, Hsc, Hsn in Hh.
    assert (m = nullval) by (destruct Hh as [E|[E|[E|[]]]]; auto). subst m.
    apply Hnn. apply (in_map fst) in I. exact I.
Qed.

Lemma hkp5_segF_C_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps (O: hkp5_oth) (FR: mpred) R :
  hkp5_model_facts -> x25519_props x25519 -> hkp5_oth_ok F V O ->
  semax (hkp5_Delta (hkp5_G_F x25519)) (hkp5F_S x25519 F V steps O FR hkp5F_P2) hkp5F_sC
    (overridePost (hkp5F_S x25519 F V steps O FR hkp5F_P2) R).
Proof.
  intros HF HX HO.
  unfold hkp5F_S, hkp5_Delta, hkp5F_sC.
  Intros Y.
  abbreviate_semax.
  pose proof H0 as Hinv.
  destruct H0 as (Hrel & Hwarn & _ & _ & _ & Hfr & Hal & _).
  destruct R as [Rn Rb Rc Rr]. unfold POSTCONDITION, abbreviate. cbn [overridePost]. abbreviate_semax.
  (* CHECK(check_all(&p, &t, &w)) *)
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  + apply ENTAIL_refl.
  + rewrite hkp5FC_SEPx. unfold hkp5_temps, hkp5_lvars; cbn [app]. forward_call (F, V, Y, O).
    forward_if.
    { exfalso. exact (Int.one_not_zero H0). }
    forward. rewrite hkp5FC_SEPx. unfold hkp5_temps, hkp5_lvars; cbn [app]. entailer!.
  + forward. apply ENTAIL_refl.
  + forward.
    unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs; cbn [app].
    set (ML := h5_ML (y_H Y)) in Hal |- *.
    Intros.
    assert_PROP (is_pointer_or_null (hk5_head ML)) as Phd.
    { sep_apply (hkp5FC_mklist_local_facts ML). entailer!. }
    forward.
    match goal with |- semax _ (PROPx _ (LOCALx (?K :: _ :: ?Q) (SEPx ?L))) _ _ =>
    let L' := eval cbn [replace_nth] in (replace_nth 12 L emp) in
    forward_loop (EX ML1: list (val * hk5_mk), EX ML2: list (val * hk5_mk),
        PROPx [ML = ML1 ++ ML2]
        (LOCALx (temp KC._k (hk5_head ML2) :: temp KC._nlive (Vlong (Int64.repr (Zlength ML1))) :: Q)
        (SEPx (hkp5FC_seg ML1 (hk5_head ML2) :: hk5_mklist ML2 ::  L'))))
      continue: (EX ML1: list (val * hk5_mk), EX m: val, EX M: hk5_mk, EX ML2: list (val * hk5_mk),
        PROPx [ML = ML1 ++ (m, M) :: ML2]
        (LOCALx (temp KC._k m :: temp KC._nlive (Vlong (Int64.repr (Zlength ML1 + 1))) :: Q)
        (SEPx (hkp5FC_seg ML1 m :: hk5_node m M (hk5_head ML2) :: hk5_mklist ML2 ::  L'))))
      break: (PROPx [] (LOCALx (temp KC._nlive (Vlong (Int64.repr (Zlength ML))) :: Q) (SEPx L)))
    end.
    * Exists (@nil (val * hk5_mk)) ML. cbn [hkp5FC_seg app]. entailer!.
    * Intros ML1 ML2.
      assert_PROP (is_pointer_or_null (hk5_head ML2)) as Phd2.
      { sep_apply (hkp5FC_mklist_local_facts ML2). entailer!. }
      forward_if.
      { apply denote_tc_test_eq_split; [| apply valid_pointer_null].
        eapply derives_trans with (Q := (hk5_mklist ML2 * TT)%logic); [cancel|].
        apply sepcon_valid_pointer1, hkp5FC_mklist_valid. }
      2: { destruct ML2 as [|[m M] ML2'].
        - forward. sep_apply (hkp5FC_fold_all ML ML1 [] H0). entailer!.
          rewrite H0, app_nil_r. reflexivity.
        - cbn [hk5_mklist hk5_head] in *. unfold hk5_node at 1. Intros.
          assert_PROP (isptr m) as Pm by entailer!. subst m. contradiction. }
      destruct ML2 as [|[m M] ML2']; [cbn [hk5_head] in *; contradiction|].
      cbn [hk5_mklist hk5_head] in *. unfold hk5_node at 1. Intros.
      assert (HmM: In (m, M) (h5_ML (y_H Y))) by (fold ML; rewrite H0; apply in_or_app; right; left; reflexivity).
      destruct (hkp5FC_node_facts _ _ _ _ _ _ _ m M Hrel H1 HmM) as [Hsat Hhash].
      unfold hk5_mk_val at 1. rewrite Hhash.
      match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
      { apply ENTAIL_refl. }
      { forward.
        match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?L))) _ _ =>
          forward_if (PROPx P (LOCALx (temp KC._t'61 (Vint Int.one) :: Q) (SEPx L))) end.
        - forward. forward. entailer!.
        - exfalso. rewrite Hsat in *. match goal with Hc: _ |- _ => apply Hc; unfold REFCOUNT_SATURATED; apply Int.eqm_samerepr; exists 1; reflexivity end.
        - forward_if.
          { exfalso. match goal with Hc: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
          forward. entailer!. }
      { forward. apply ENTAIL_refl. }
      forward.
      sep_apply (hkp5FC_node_fold_h m M (hk5_head ML2') Hhash H3 H4).
      Exists ML1 m M ML2'.
      entailer!.
    * Intros ML1 m M ML2.
      assert_PROP (is_pointer_or_null (hk5_head ML2)) as Phd2.
      { sep_apply (hkp5FC_mklist_local_facts ML2). entailer!. }
      unfold hk5_node at 1. Intros.
      unfold hk5_mk_val at 1.
      forward.
      fold (hk5_mk_val M (hk5_head ML2)).
      sep_apply (hkp5FC_node_fold m M (hk5_head ML2) ltac:(split; assumption)).
      Exists (ML1 ++ [(m, M)]) ML2.
      rewrite hkp5FC_seg_snoc, Zlength_app, Zlength_cons, Zlength_nil, <- app_assoc.
      entailer!.
    * assert (Hacc: Int64.sub (s_allocs (y_S Y)) (v_allocs0 V) =
                    Int64.add (Int64.sub (s_frees (y_S Y)) (v_frees0 V)) (Int64.repr (Zlength ML)))
        by (rewrite Hal, Hfr; reflexivity).
      unfold shim_state4 at 1, shim_core at 1. Intros.
      match goal with Hs: shim_ok _ |- _ => rename Hs into HSok end.
      rewrite (@hkp5FC_tulong_cs Noise.CS W_keypairs _ _ (f_gv F _wg_shim_allocs)).
      rewrite (@hkp5FC_tulong_cs Noise.CS W_keypairs _ _ (f_gv F _wg_shim_frees)).
      change _wg_shim_allocs with KC._wg_shim_allocs. change _wg_shim_frees with KC._wg_shim_frees.
      match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
      { apply ENTAIL_refl. }
      { forward. forward. forward_if.
        - exfalso. match goal with Hc: context [Int64.eq] |- _ =>
            rewrite Hacc, Int64.eq_true in Hc; exact (Int.one_not_zero Hc) end.
        - forward. entailer!. }
      { forward. apply ENTAIL_refl. }
      (* the warnings 2, 1, 4 *)
      destruct Hwarn as (Hl0 & Hlm & Hlw & Hweq & Hm1 & Hm2 & Hm4).
      assert (W2: Znth 2 (y_w Y) = Znth 2 (v_w0 V))
        by (rewrite Hweq by lia; unfold REFCOUNT_ADD_UAF in Hm2; rewrite Hm2, Int64.add_zero; reflexivity).
      assert (W1: Znth 1 (y_w Y) = Znth 1 (v_w0 V))
        by (rewrite Hweq by lia; unfold REFCOUNT_ADD_OVF in Hm1; rewrite Hm1, Int64.add_zero; reflexivity).
      assert (W4: Znth 4 (y_w Y) = Znth 4 (v_w0 V))
        by (rewrite Hweq by lia; unfold REFCOUNT_DEC_LEAK in Hm4; rewrite Hm4, Int64.add_zero; reflexivity).
      unfold refwarn4. Intros.
      rewrite hkp5FC_warr_cs. change _wg_shim_refcount_warn with KC._wg_shim_refcount_warn.
      unfold hk5_warr at 2. Intros.
      assert (E2: Znth 2 (map Vlong (y_w Y)) = Vlong (Znth 2 (v_w0 V))) by (rewrite Znth_map by lia; rewrite W2; reflexivity).
      assert (E1: Znth 1 (map Vlong (y_w Y)) = Vlong (Znth 1 (v_w0 V))) by (rewrite Znth_map by lia; rewrite W1; reflexivity).
      assert (E4: Znth 4 (map Vlong (y_w Y)) = Vlong (Znth 4 (v_w0 V))) by (rewrite Znth_map by lia; rewrite W4; reflexivity).
      assert (F2: Znth 2 (map Vlong (v_w0 V)) = Vlong (Znth 2 (v_w0 V))) by (rewrite Znth_map by lia; reflexivity).
      assert (F1: Znth 1 (map Vlong (v_w0 V)) = Vlong (Znth 1 (v_w0 V))) by (rewrite Znth_map by lia; reflexivity).
      assert (F4: Znth 4 (map Vlong (v_w0 V)) = Vlong (Znth 4 (v_w0 V))) by (rewrite Znth_map by lia; reflexivity).
      match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
      { apply ENTAIL_refl. }
      { forward. forward. rewrite W2.
        match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?L))) _ _ =>
          forward_if (PROPx P (LOCALx (temp KC._t'62 (Vint Int.one) :: Q) (SEPx L))) end.
        - forward. forward. rewrite W1. forward. entailer!. rewrite Int64.eq_true. reflexivity.
        - exfalso. match goal with Hc: _ |- _ => apply Hc; reflexivity end.
        - match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?L))) _ _ =>
            forward_if (PROPx P (LOCALx (temp KC._t'63 (Vint Int.one) :: Q) (SEPx L))) end.
          + forward. forward. rewrite W4. forward. entailer!. rewrite Int64.eq_true. reflexivity.
          + exfalso. match goal with Hc: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hc) end.
          + forward_if.
            * exfalso. match goal with Hc: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hc) end.
            * forward. entailer!. }
      { forward. apply ENTAIL_refl. }
      unfold POSTCONDITION, abbreviate. cbn [RA_normal].
      rewrite (@hkp5FC_tulong_cs W_keypairs Noise.CS _ _ (f_gv F KC._wg_shim_allocs)).
      rewrite (@hkp5FC_tulong_cs W_keypairs Noise.CS _ _ (f_gv F KC._wg_shim_frees)).
      change KC._wg_shim_allocs with _wg_shim_allocs. change KC._wg_shim_frees with _wg_shim_frees.
      rewrite <- (hkp5FC_warr_cs Ews (map Vlong (y_w Y)) (f_gv F KC._wg_shim_refcount_warn)).
      change KC._wg_shim_refcount_warn with _wg_shim_refcount_warn.
      Exists Y.
      unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars; cbn [app].
      unfold ML. unfold shim_state4, shim_core, refwarn4, hk5_warr. entailer!.
Qed.
