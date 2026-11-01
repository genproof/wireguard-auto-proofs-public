(* struct poly1305_desc_ctx for poly1305_final (aead_poly_final_body3.v): the field decomposition with
   ANY field values, and the all-zero context p1305_ctx_zero from 112 zero bytes (memset(desc, 0, sizeof)). *)
Require Import VST.floyd.proofauto.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.poly1305.code.
Require Import WgNoise.proof.aead.aead_spec.
Require Import WgNoise.proof.aead.aead_poly_small_body.

Local Open Scope Z_scope.

Section PolyFinalCtx.
#[local] Existing Instance Poly1305.CS.

Definition pf3_ctx_val (buf: list val) (bl: val) (s: list val) (st: reptype t_p1305_block_state)
  : reptype t_p1305_ctx := (buf, (bl, (s, st))).

Lemma pf3_ctx_split sh buf bl s st desc :
  data_at sh t_p1305_ctx (pf3_ctx_val buf bl s st) desc =
  (field_at sh t_p1305_ctx (DOT poly1305.code._buf) buf desc *
   field_at sh t_p1305_ctx (DOT poly1305.code._buflen) bl desc *
   field_at sh t_p1305_ctx (DOT poly1305.code._s) s desc *
   spacer sh 36 40 desc *
   field_at sh t_p1305_ctx (DOT poly1305.code._state) st desc)%logic.
Proof.
  unfold_data_at (data_at _ _ _ desc).
  rewrite !sepcon_assoc. reflexivity.
Qed.

Definition pf3_key0 : reptype t_p1305_core_key :=
  (inl (Zrepeat (Vint Int.zero) 5), inl (Zrepeat (Vint Int.zero) 5)).
Definition pf3_bstate0 : reptype t_p1305_block_state := (p1305_h_val [0; 0; 0; 0; 0], inr pf3_key0).

Lemma pf3_ctx_zero_eq :
  p1305_ctx_zero = pf3_ctx_val (Zrepeat (Vubyte Byte.zero) 16) (Vint Int.zero) (Zrepeat (Vint Int.zero) 4) pf3_bstate0.
Proof. reflexivity. Qed.

Definition pf3_bstate_val (h: list Z) (k: reptype t_p1305_core_key) : reptype t_p1305_block_state :=
  (p1305_h_val h, inr k).

Lemma pf3_bstate_split sh h k bp :
  field_compatible t_p1305_block_state [] bp ->
  data_at sh t_p1305_block_state (pf3_bstate_val h k) bp =
  (data_at sh t_p1305_state (p1305_h_val h) bp * data_at sh t_p1305_core_key k (offset_val 24 bp))%logic.
Proof.
  intros FC.
  pose proof (aead_ps_fc_core_r bp FC) as FCU.
  unfold_data_at (data_at _ _ _ bp). unfold pf3_bstate_val. simpl. unfold_field_at 2%nat.
  rewrite !field_at_data_at.
  change (nested_field_type t_p1305_block_state (DOT poly1305.code._h)) with t_p1305_state.
  change (nested_field_type t_p1305_block_state [UnionField poly1305.code._core_r; StructField aead_ps_anon])
    with t_p1305_core_key.
  rewrite !field_address_offset by auto with field_compatible.
  simpl. rewrite isptr_offset_val_zero by auto with field_compatible.
  reflexivity.
Qed.

Lemma pf3_key_zero sh p :
  readable_share sh -> field_compatible t_p1305_core_key [] p ->
  mapsto_zeros 48 sh p |-- data_at sh t_p1305_core_key pf3_key0 p.
Proof.
  intros Hsh FC.
  change 48 with (sizeof t_p1305_core_key).
  eapply derives_trans; [apply mapsto_zero_data_at_zero; auto | ].
  apply derives_refl'. f_equal. apply JMeq_eq.
  eapply JMeq_trans; [apply JMeq_zero_val_zero_val' |]. apply JMeq_refl.
Qed.

Lemma pf3_h_zero sh p :
  readable_share sh -> field_compatible t_p1305_state [] p ->
  mapsto_zeros 24 sh p |-- data_at sh t_p1305_state (p1305_h_val [0; 0; 0; 0; 0]) p.
Proof.
  intros Hsh FC.
  change 24 with (sizeof t_p1305_state).
  eapply derives_trans; [apply mapsto_zero_data_at_zero; auto | ].
  apply derives_refl'. f_equal. apply JMeq_eq.
  eapply JMeq_trans; [apply JMeq_zero_val_zero_val' |]. apply JMeq_refl.
Qed.

Ltac pf3_zero_tac :=
  eapply derives_trans; [apply mapsto_zero_data_at_zero; auto | ];
  apply derives_refl'; f_equal; apply JMeq_eq;
  eapply JMeq_trans; [apply JMeq_zero_val_zero_val' |]; apply JMeq_refl.

Lemma pf3_buf_zero sh p :
  readable_share sh -> field_compatible (tarray tuchar 16) [] p ->
  mapsto_zeros 16 sh p |-- data_at sh (tarray tuchar 16) (Zrepeat (Vubyte Byte.zero) 16) p.
Proof. intros Hsh FC. change 16 with (sizeof (tarray tuchar 16)) at 1. pf3_zero_tac. Qed.

Lemma pf3_s_zero sh p :
  readable_share sh -> field_compatible (tarray tuint 4) [] p ->
  mapsto_zeros 16 sh p |-- data_at sh (tarray tuint 4) (Zrepeat (Vint Int.zero) 4) p.
Proof. intros Hsh FC. change 16 with (sizeof (tarray tuint 4)) at 1. pf3_zero_tac. Qed.

Lemma pf3_uint_zero sh p :
  readable_share sh -> field_compatible tuint [] p ->
  mapsto_zeros 4 sh p |-- data_at sh tuint (Vint Int.zero) p.
Proof. intros Hsh FC. change 4 with (sizeof tuint) at 1. pf3_zero_tac. Qed.

Lemma pf3_ctx_zero sh desc :
  readable_share sh -> field_compatible t_p1305_ctx [] desc ->
  data_at sh (tarray tuchar 112) (Zrepeat (Vubyte Byte.zero) 112) desc |-- data_at sh t_p1305_ctx p1305_ctx_zero desc.
Proof.
  intros Hsh FC.
  pose proof (field_compatible_nested_field t_p1305_ctx (DOT poly1305.code._state) desc
                ltac:(auto with field_compatible)) as FCs.
  simpl in FCs.
  sep_apply (aead_ps_bytes_zeros sh 112 desc Hsh). lia.
  rewrite pf3_ctx_zero_eq, pf3_ctx_split. unfold pf3_bstate0. fold (pf3_bstate_val [0; 0; 0; 0; 0] pf3_key0).
  rewrite !field_at_data_at, !field_compatible_field_address by auto with field_compatible.
  rewrite pf3_bstate_split by auto.
  simpl nested_field_type. simpl nested_field_offset.
  unfold spacer. simpl. unfold at_offset.
  rewrite isptr_offset_val_zero by auto with field_compatible.
  pose proof (field_compatible_nested_field t_p1305_ctx (DOT poly1305.code._buf) desc
                ltac:(auto with field_compatible)) as F1.
  pose proof (field_compatible_nested_field t_p1305_ctx (DOT poly1305.code._buflen) desc
                ltac:(auto with field_compatible)) as F2.
  pose proof (field_compatible_nested_field t_p1305_ctx (DOT poly1305.code._s) desc
                ltac:(auto with field_compatible)) as F3.
  pose proof (field_compatible_nested_field t_p1305_block_state (DOT poly1305.code._h) (offset_val 40 desc)
                ltac:(auto with field_compatible)) as F4.
  pose proof (field_compatible_nested_field _ _ _ (aead_ps_fc_core_r _ FCs)) as F5.
  simpl in F1, F2, F3, F4, F5.
  rewrite isptr_offset_val_zero in F1, F4 by auto with field_compatible.
  rewrite offset_offset_val in F5 |- *. simpl Z.add in F5 |- *.
  destruct desc as [| | | | | b i]; try (destruct FC; contradiction).
  pose proof FC as FC'. destruct FC' as [_ [_ [SC _]]]. simpl in SC.
  pose proof (Ptrofs.unsigned_range i) as Hi.
  rewrite <- (Ptrofs.repr_unsigned i) in F1, F2, F3, F4, F5 |- *.
  remember (Ptrofs.unsigned i) as ofs.
  assert (OV: forall k, 0 <= k <= 112 -> offset_val k (Vptr b (Ptrofs.repr ofs)) = Vptr b (Ptrofs.repr (ofs + k)))
    by (intros; simpl; rewrite Ptrofs.add_unsigned, !Ptrofs.unsigned_repr by rep_lia; reflexivity).
  rewrite !OV in F2, F3, F4, F5 by lia. repeat (rewrite OV by lia).
  change 112 with (16 + (4 + (16 + (4 + (24 + 48))))).
  rewrite (aggregate_pred.mapsto_zeros_split sh b _ 16) by lia.
  rewrite (aggregate_pred.mapsto_zeros_split sh b _ 4) by lia.
  rewrite (aggregate_pred.mapsto_zeros_split sh b _ 16) by lia.
  rewrite (aggregate_pred.mapsto_zeros_split sh b _ 4) by lia.
  rewrite (aggregate_pred.mapsto_zeros_split sh b _ 24) by lia.
  replace (ofs + 16 + 4) with (ofs + 20) by lia.
  replace (ofs + 20 + 16) with (ofs + 36) by lia.
  replace (ofs + 36 + 4) with (ofs + 40) by lia.
  replace (ofs + 40 + 24) with (ofs + 64) by lia.
  rewrite !sepcon_assoc.
  apply sepcon_derives; [apply pf3_buf_zero; auto |].
  apply sepcon_derives; [apply pf3_uint_zero; auto |].
  apply sepcon_derives; [apply pf3_s_zero; auto |].
  apply sepcon_derives; [apply mapsto_zeros_memory_block; auto |].
  apply sepcon_derives; [apply pf3_h_zero; auto | apply pf3_key_zero; auto].
Qed.

End PolyFinalCtx.
