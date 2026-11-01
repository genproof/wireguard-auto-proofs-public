(* main of law prim_poly1305, segment E (statements 16..19): the checks that the context is all zero
   (buf, buflen, s, h, key.r, precomputed_s.r). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.harness.prim_poly1305.hp1305_spec3.
Require Import WgNoise.proof.harness.prim_poly1305.hp1305_main_defs3.
Require Import WgNoise.proof.libc.libc_bytes.
Require WgNoise.harness.x_prim_poly1305.code.

#[local] Existing Instance W_prim_poly1305.
Local Open Scope Z_scope.

#[local] Instance hp1305m_segE_CCE : change_composite_env Poly1305.CS W_prim_poly1305.
Proof. make_cs_preserve Poly1305.CS W_prim_poly1305. Defined.

Definition hp1305m_zero : reptype t_hpctx :=
  (Zrepeat (Vubyte Byte.zero) 16,
   (Vint Int.zero,
    (Zrepeat (Vint Int.zero) 4,
     (inl (Zrepeat (Vint Int.zero) 5),
      inr (inl (Zrepeat (Vint Int.zero) 5), inl (Zrepeat (Vint Int.zero) 5)))))).

Lemma hp1305m_segE_buf p :
  data_at Tsh t_hpctx hp1305m_zero p |--
  data_at Tsh (tarray tuchar 16) (map Vubyte (Zrepeat Byte.zero 16)) (field_address t_hpctx (DOT HPC._buf) p) *
  (data_at Tsh (tarray tuchar 16) (map Vubyte (Zrepeat Byte.zero 16)) (field_address t_hpctx (DOT HPC._buf) p) -*
   data_at Tsh t_hpctx hp1305m_zero p).
Proof.
  unfold data_at at 1.
  eapply derives_trans;
    [apply (nested_field_ramif' Tsh t_hpctx nil (DOT HPC._buf) hp1305m_zero (Zrepeat (Vubyte Byte.zero) 16)) |].
  { apply JMeq_refl. }
  { split; [exact I | left; reflexivity]. }
  change ((StructField HPC._buf :: nil) ++ []) with (StructField HPC._buf :: nil).
  rewrite field_at_data_at. apply sepcon_derives; [apply derives_refl |].
  apply (allp_left _ (Zrepeat (Vubyte Byte.zero) 16)). apply (allp_left _ (Zrepeat (Vubyte Byte.zero) 16)).
  rewrite prop_imp by apply JMeq_refl. rewrite field_at_data_at.
  match goal with |- context [upd_reptype ?a ?b ?c ?d] =>
    replace (upd_reptype a b c d) with hp1305m_zero by (vm_compute; reflexivity) end.
  apply derives_refl.
Qed.

(* the tag, hidden from subst (computing it diverges) *)
Definition hp1305m_is_tag (kb mb T: list byte) : Prop := poly1305_tag kb mb = T.

Lemma hp1305m_segE_ok {Espec: OracleKind} gv vd vkey vkey0 vref FR :
  semax hp1305m_Delta (hp1305m_PD gv vd vkey vkey0 vref FR) hp1305m_segE
    (overridePost (hp1305m_PE gv vd vkey vkey0 vref FR) (hp1305m_R gv)).
Proof.
  unfold hp1305m_PD. Intros n kb mb msg copy tag.
  remember (poly1305_tag kb mb) as T eqn:ET.
  assert (HT: hp1305m_is_tag kb mb T) by (subst T; reflexivity). clear ET.
  unfold hp1305m_Delta, hp1305m_segE, hp1305m_R.
  simplify_func_tycontext. abbreviate_semax.
  unfold hp1305m_buf, hp1305m_ranges, hp1305m_tv, hp1305m_lv in *. Intros. simpl app.
  erewrite (@data_at_change_composite Poly1305.CS W_prim_poly1305 hp1305m_segE_CCE Tsh t_p1305_ctx p1305_ctx_zero);
    [| apply JMeq_refl | prove_cs_preserve_type].
  change (@data_at W_prim_poly1305 Tsh t_p1305_ctx p1305_ctx_zero vd) with
    (@data_at W_prim_poly1305 Tsh t_hpctx hp1305m_zero vd).
  (* CHECK(bytes_zero(d.buf, 16) && d.buflen == 0) *)
  match goal with |- semax _ ?P (Ssequence (Sloop _ _) _) _ => apply semax_seq with P end.
  match goal with |- semax _ ?P (Sloop _ _) _ => apply semax_loop with (Q' := P) end.
  { assert_PROP (field_compatible t_hpctx nil vd) as Hfc by entailer!.
    sep_apply (hp1305m_segE_buf vd). Intros.
    forward_call (Tsh, field_address t_hpctx (DOT HPC._buf) vd, Zrepeat Byte.zero 16).
    { entailer!. simpl. rewrite field_compatible_field_address by auto with field_compatible. reflexivity. }
    { rewrite Zlength_Zrepeat by lia. rep_lia. }
    replace (Zlength (Zrepeat Byte.zero 16)) with 16 by reflexivity.
    destruct (list_eq_dec Byte.eq_dec (Zrepeat Byte.zero 16) (Zrepeat Byte.zero 16)) as [_|C];
      [| congruence].
    sep_apply modus_ponens_wand.
    forward_if (temp HPC._t'10 (Vint Int.one)).
    { forward. forward. entailer!. }
    { discriminate. }
    forward_if.
    { discriminate. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  abbreviate_semax.
  (* for (i = 0; i < 4; i++) CHECK(d.s[i] == 0) *)
  match goal with |- semax _ (PROPx ?Pr (LOCALx ?L (SEPx ?S))) _ _ =>
    forward_for_simple_bound 4 (EX i:Z, PROPx Pr (LOCALx L (SEPx S)))%assert end.
  { entailer!. }
  { cbv beta.
    match goal with |- semax _ ?P (Sloop _ _) _ => apply semax_loop with (Q' := P) end.
    { forward.
      { entailer!. unfold hp1305m_zero. simpl. rewrite Znth_Zrepeat by lia. exact I. }
      match goal with |- context [Znth i ?l] =>
        replace (Znth i l) with (Vint Int.zero)
          by (unfold hp1305m_zero; simpl; rewrite Znth_Zrepeat by lia; reflexivity) end.
      forward_if.
      + discriminate.
      + forward. entailer!. }
    { forward. apply ENTAIL_refl. } }
  abbreviate_semax.
  (* for (i = 0; i < 5; i++) CHECK(d.state.h.h[i] == 0 && d.state.core_r.key.r[i] == 0) *)
  drop_LOCAL 0%nat.
  match goal with |- semax _ (PROPx ?Pr (LOCALx ?L (SEPx ?S))) _ _ =>
    forward_for_simple_bound 5 (EX i:Z, PROPx Pr (LOCALx L (SEPx S)))%assert end.
  { entailer!. }
  { cbv beta.
    match goal with |- semax _ ?P (Sloop _ _) _ => apply semax_loop with (Q' := P) end.
    { forward.
      { entailer!. unfold hp1305m_zero. simpl. rewrite Znth_Zrepeat by lia. exact I. }
      match goal with |- context [Znth i ?l] =>
        replace (Znth i l) with (Vint Int.zero)
          by (unfold hp1305m_zero; simpl; rewrite Znth_Zrepeat by lia; reflexivity) end.
      forward_if (temp HPC._t'11 (Vint Int.one)).
      { forward.
        { entailer!. unfold hp1305m_zero. simpl. rewrite Znth_Zrepeat by lia. exact I. }
        match goal with |- context [Znth i ?l] =>
          replace (Znth i l) with (Vint Int.zero)
            by (unfold hp1305m_zero; simpl; rewrite Znth_Zrepeat by lia; reflexivity) end.
        forward. entailer!. }
      { congruence. }
      forward_if.
      + discriminate.
      + forward. entailer!. }
    { forward. apply ENTAIL_refl. } }
  abbreviate_semax.
  (* for (i = 0; i < 4; i++) CHECK(d.state.core_r.precomputed_s.r[i] == 0) *)
  drop_LOCAL 0%nat.
  match goal with |- semax _ (PROPx ?Pr (LOCALx ?L (SEPx ?S))) _ _ =>
    forward_for_simple_bound 4 (EX i:Z, PROPx Pr (LOCALx L (SEPx S)))%assert end.
  { entailer!. }
  { cbv beta.
    match goal with |- semax _ ?P (Sloop _ _) _ => apply semax_loop with (Q' := P) end.
    { forward.
      { entailer!. unfold hp1305m_zero. simpl. rewrite Znth_Zrepeat by lia. exact I. }
      match goal with |- context [Znth i ?l] =>
        replace (Znth i l) with (Vint Int.zero)
          by (unfold hp1305m_zero; simpl; rewrite Znth_Zrepeat by lia; reflexivity) end.
      forward_if.
      + discriminate.
      + forward. entailer!. }
    { forward. apply ENTAIL_refl. } }
  unfold hp1305m_PE. Exists n kb mb msg copy tag.
  unfold hp1305m_buf, hp1305m_ranges, hp1305m_tv, hp1305m_lv. simpl app.
  unfold hp1305m_is_tag in HT. rewrite HT.
  sep_apply (data_at_data_at_ Tsh t_hpctx hp1305m_zero vd). entailer!.
Qed.
