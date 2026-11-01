(* Body proofs of the poly1305.c wrappers and poly1305_init. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.poly1305.code.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.aead.aead_spec.
Require Import WgNoise.proof.aead.aead_cce.
Require Import WgNoise.proof.aead.aead_bytes.
Require Import WgNoise.proof.aead.aead_poly_small_ctx.

Local Open Scope Z_scope.

Section PolySmall.
#[local] Existing Instance Poly1305.CS.

Lemma aead_ps_mapsto_byte_zero sh b ofs :
  readable_share sh -> 0 <= ofs -> ofs + 1 < Ptrofs.modulus ->
  mapsto sh tuchar (Vptr b (Ptrofs.repr ofs)) (Vint Int.zero) |-- mapsto_zeros 1 sh (Vptr b (Ptrofs.repr ofs)).
Proof.
  intros. unfold mapsto, mapsto_zeros. simpl. rewrite if_true by auto.
  rewrite Ptrofs.unsigned_repr by rep_lia.
  apply orp_left; [ | apply derives_extract_prop; intro Hx; discriminate Hx].
  apply andp_left2. apply andp_right; [apply prop_right; lia | ].
  change (predicates_sl.sepcon ?a ?b) with (sepcon a b). change predicates_sl.emp with emp.
  rewrite sepcon_emp. apply derives_refl.
Qed.

Lemma aead_ps_bytes_zeros_nat sh b (n: nat) : forall ofs,
  readable_share sh -> 0 <= ofs -> ofs + Z.of_nat n < Ptrofs.modulus ->
  data_at sh (tarray tuchar (Z.of_nat n)) (Zrepeat (Vubyte Byte.zero) (Z.of_nat n)) (Vptr b (Ptrofs.repr ofs))
  |-- mapsto_zeros (Z.of_nat n) sh (Vptr b (Ptrofs.repr ofs)).
Proof.
induction n; intros ofs Hsh H0 H1.
- simpl. change predicates_sl.emp with emp. rewrite Ptrofs.unsigned_repr by rep_lia. entailer!.
  apply data_at_zero_array_inv; auto.
- rewrite Nat2Z.inj_succ in *. unfold tarray.
  assert_PROP (field_compatible (Tarray tuchar (Z.succ (Z.of_nat n)) noattr) [] (Vptr b (Ptrofs.repr ofs)))
    as FC by entailer!.
  rewrite (split2_data_at_Tarray_tuchar sh (Z.succ (Z.of_nat n)) 1) by (try rewrite Zlength_Zrepeat; lia).
  assert (FC0: field_compatible0 (Tarray tuchar (Z.succ (Z.of_nat n)) noattr) [ArraySubsc 1]
                 (Vptr b (Ptrofs.repr ofs)))
    by (apply field_compatible0_cons; simpl; split; [lia | auto with field_compatible]).
  rewrite field_address0_offset by auto.
  replace (Z.succ (Z.of_nat n)) with (1 + Z.of_nat n) by lia.
  rewrite (aggregate_pred.mapsto_zeros_split sh b ofs 1 (Z.of_nat n)) by lia.
  rewrite sublist_Zrepeat, sublist_Zrepeat by lia.
  replace (1 + Z.of_nat n - 1) with (Z.of_nat n) by lia.
  apply sepcon_derives.
  + rewrite (data_at_singleton_array_eq sh tuchar (Vubyte Byte.zero)) by reflexivity.
    assert_PROP (field_compatible tuchar [] (Vptr b (Ptrofs.repr ofs))) by entailer!.
    rewrite <- (mapsto_data_at' sh tuchar (Vubyte Byte.zero) (Vubyte Byte.zero)) by (auto; reflexivity).
    apply aead_ps_mapsto_byte_zero; auto; lia.
  + replace (offset_val _ _) with (Vptr b (Ptrofs.repr (ofs + 1))).
    * apply IHn; auto; lia.
    * simpl. f_equal. rewrite Ptrofs.add_unsigned, !Ptrofs.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma aead_ps_bytes_zeros sh n p :
  readable_share sh -> 0 <= n ->
  data_at sh (tarray tuchar n) (Zrepeat (Vubyte Byte.zero) n) p |-- mapsto_zeros n sh p.
Proof.
  intros Hsh Hn.
  assert_PROP (field_compatible (tarray tuchar n) [] p) as FC by entailer!.
  destruct p; try (destruct FC; contradiction).
  destruct FC as [_ [_ [SC _]]]. simpl in SC. rewrite Z.max_r in SC by lia.
  rewrite <- (Ptrofs.repr_unsigned i). rewrite <- (Z2Nat.id n) by lia.
  apply aead_ps_bytes_zeros_nat; auto; rewrite ?Z2Nat.id by lia; rep_lia.
Qed.

Lemma aead_ps_state_zero sh p :
  readable_share sh -> field_compatible t_p1305_state [] p ->
  data_at sh (tarray tuchar 24) (Zrepeat (Vubyte Byte.zero) 24) p
  |-- data_at sh t_p1305_state (p1305_h_val [0; 0; 0; 0; 0]) p.
Proof.
  intros Hsh FC.
  sep_apply (aead_ps_bytes_zeros sh 24 p Hsh). lia.
  change 24 with (sizeof t_p1305_state).
  eapply derives_trans; [apply mapsto_zero_data_at_zero; auto | ].
  apply derives_refl'. f_equal. apply JMeq_eq.
  eapply JMeq_trans; [apply JMeq_zero_val_zero_val' |]. apply JMeq_refl.
Qed.

Lemma aead_ps_h_cs sh h p :
  @data_at Poly1305.CS sh t_p1305_state (p1305_h_val h) p =
  @data_at Poly1305Donna32.CS sh t_p1305_state (p1305_h_val h) p.
Proof. apply equal_f, (@data_at_change_composite _ _ cce_poly_donna); [apply JMeq_refl | reflexivity]. Qed.

Lemma aead_ps_key_cs sh r p :
  @data_at Poly1305.CS sh t_p1305_core_key (p1305_key_val r) p =
  @data_at Poly1305Donna32.CS sh t_p1305_core_key (p1305_key_val r) p.
Proof. apply equal_f, (@data_at_change_composite _ _ cce_poly_donna); [apply JMeq_refl | reflexivity]. Qed.

Lemma aead_ps_key__cs sh p :
  @data_at_ Poly1305.CS sh t_p1305_core_key p = @data_at_ Poly1305Donna32.CS sh t_p1305_core_key p.
Proof. apply equal_f, (@data_at__change_composite _ _ cce_poly_donna); reflexivity. Qed.

Lemma aead_ps_words_cs sh (s: list int) p :
  @data_at Poly1305.CS sh (tarray tuint 4) (map Vint s) p =
  @data_at Poly1305Donna32.CS sh (tarray tuint 4) (map Vint s) p.
Proof. apply equal_f, (@data_at_change_composite _ _ cce_poly_donna); [apply JMeq_refl | reflexivity]. Qed.

Lemma aead_ps_prim_bytes_cs sh bs p :
  @prim_bytes Poly1305.CS sh bs p = @prim_bytes Poly1305Donna32.CS sh bs p.
Proof. unfold prim_bytes. destruct (Z.eq_dec _ _); auto. apply aead_data_at_tuchar_cs. Qed.

Definition aead_ps_anon : ident := 18727075383868559167%positive.

Lemma aead_ps_fc_core_r bp :
  field_compatible t_p1305_block_state [] bp ->
  field_compatible t_p1305_block_state [UnionField poly1305.code._core_r; StructField aead_ps_anon] bp.
Proof.
  intros FC.
  apply field_compatible_cons; simpl; split; [repeat first [left; reflexivity | right] |].
  apply field_compatible_cons; simpl; split; [repeat first [left; reflexivity | right] | auto].
Qed.

Lemma aead_ps_bstate_split sh h r bp :
  field_compatible t_p1305_block_state [] bp ->
  data_at sh t_p1305_block_state (p1305_bstate_val h r) bp =
  (@data_at Poly1305Donna32.CS sh t_p1305_state (p1305_h_val h) bp *
   @data_at Poly1305Donna32.CS sh t_p1305_core_key (p1305_key_val r) (offset_val 24 bp))%logic.
Proof.
  intros FC.
  pose proof (aead_ps_fc_core_r bp FC) as FCU.
  unfold_data_at (data_at _ _ _ bp). unfold p1305_bstate_val. simpl. unfold_field_at 2%nat.
  rewrite !field_at_data_at.
  change (nested_field_type t_p1305_block_state (DOT poly1305.code._h)) with t_p1305_state.
  change (nested_field_type t_p1305_block_state [UnionField poly1305.code._core_r; StructField aead_ps_anon])
    with t_p1305_core_key.
  rewrite aead_ps_h_cs, aead_ps_key_cs.
  rewrite !field_address_offset by auto with field_compatible.
  simpl. rewrite isptr_offset_val_zero by auto with field_compatible.
  reflexivity.
Qed.

Lemma aead_ps_bstate_split_ sh bp :
  field_compatible t_p1305_block_state [] bp ->
  data_at_ sh t_p1305_block_state bp |--
  (data_at_ sh t_p1305_state bp *
   @data_at_ Poly1305Donna32.CS sh t_p1305_core_key (offset_val 24 bp))%logic.
Proof.
  intros FC.
  pose proof (aead_ps_fc_core_r bp FC) as FCU.
  pose proof (field_compatible_nested_field _ _ _ FCU) as FCk. simpl in FCk.
  rewrite <- aead_ps_key__cs.
  unfold_data_at (data_at_ _ _ bp).
  pose proof (field_compatible_nested_field t_p1305_block_state (DOT poly1305.code._h) bp
                ltac:(auto with field_compatible)) as FCh.
  simpl in FCh. rewrite isptr_offset_val_zero in FCh by auto with field_compatible.
  apply sepcon_derives; (eapply derives_trans; [apply field_at_field_at_ |]);
    rewrite field_at__memory_block; rewrite field_compatible_field_address by auto with field_compatible; simpl.
  - rewrite isptr_offset_val_zero by auto with field_compatible. change 24 with (sizeof t_p1305_state).
    rewrite memory_block_data_at_ by auto. apply derives_refl.
  - change 48 with (sizeof t_p1305_core_key). rewrite memory_block_data_at_ by auto. apply derives_refl.
Qed.

Lemma aead_ps_mb_off sh b ofs k n :
  0 <= ofs -> 0 <= k -> 0 <= n -> ofs + k + n < Ptrofs.modulus ->
  memory_block sh n (offset_val k (Vptr b (Ptrofs.repr ofs))) = memory_block sh n (Vptr b (Ptrofs.repr (ofs + k))).
Proof.
  intros. simpl. rewrite Ptrofs.add_unsigned, !Ptrofs.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma aead_ps_ctx_pre sh desc :
  field_compatible t_p1305_ctx [] desc ->
  data_at_ sh t_p1305_ctx desc |--
  (data_at_ sh (tarray tuchar 16) desc *
   field_at_ sh t_p1305_ctx (DOT poly1305.code._buflen) desc *
   field_at_ sh t_p1305_ctx (DOT poly1305.code._s) desc *
   memory_block sh 4 (offset_val 36 desc) *
   data_at_ sh t_p1305_block_state (offset_val 40 desc))%logic.
Proof.
  intros FC.
  pose proof (field_compatible_nested_field t_p1305_ctx (DOT poly1305.code._state) desc
                ltac:(auto with field_compatible)) as FCs.
  simpl in FCs.
  rewrite data_at__memory_block, prop_true_andp by auto. change (sizeof t_p1305_ctx) with 112.
  rewrite !field_at__memory_block, !field_compatible_field_address by auto with field_compatible.
  simpl.
  rewrite <- (memory_block_data_at__tarray_tuchar_eq sh desc 16) by rep_lia.
  change t_p1305_block_state with (Tstruct poly1305.code._poly1305_block_state noattr).
  rewrite <- (memory_block_data_at_ sh _ (offset_val 40 desc)) by auto.
  simpl sizeof.
  destruct desc; try (destruct FC; contradiction).
  destruct FC as [_ [_ [SC _]]]. simpl in SC.
  rewrite <- (Ptrofs.repr_unsigned i) in *. remember (Ptrofs.unsigned i) as ofs.
  assert (0 <= ofs) by (subst; rep_lia).
  rewrite Ptrofs.unsigned_repr in SC by rep_lia.
  rewrite !aead_ps_mb_off by lia.
  change 112 with (16 + (4 + (16 + (4 + 72)))).
  rewrite (memory_block_split sh b ofs 16) by lia.
  rewrite (memory_block_split sh b (ofs + 16) 4) by lia.
  rewrite (memory_block_split sh b (ofs + 16 + 4) 16) by lia.
  rewrite (memory_block_split sh b (ofs + 16 + 4 + 16) 4) by lia.
  replace (ofs + 16 + 4) with (ofs + 20) by lia.
  replace (ofs + 20 + 16) with (ofs + 36) by lia.
  replace (ofs + 36 + 4) with (ofs + 40) by lia.
  rewrite !sepcon_assoc. apply derives_refl.
Qed.

Lemma aead_ps_init_post sh key desc :
  Zlength key = 32 -> field_compatible t_p1305_ctx [] desc ->
  (data_at sh t_p1305_block_state (p1305_bstate_val [0; 0; 0; 0; 0] (p1305_r key)) (offset_val 40 desc) *
   data_at_ sh (tarray tuchar 16) desc *
   field_at sh t_p1305_ctx (DOT poly1305.code._buflen) (Vint (Int.repr 0)) desc *
   field_at sh t_p1305_ctx (DOT poly1305.code._s) (map Vint (p1305_s_words key)) desc *
   memory_block sh 4 (offset_val 36 desc))%logic
  |-- p1305_state sh key [] desc.
Proof.
  intros HK FC.
  unfold p1305_state. simpl Zlength. simpl sublist.
  Exists [0; 0; 0; 0; 0] (Zrepeat Vundef 16).
  rewrite aead_ps_ctx_split.
  rewrite (field_at_data_at sh t_p1305_ctx (DOT poly1305.code._buf)).
  rewrite (field_at_data_at sh t_p1305_ctx (DOT poly1305.code._state)).
  rewrite !field_compatible_field_address by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  rewrite isptr_offset_val_zero by auto with field_compatible.
  unfold spacer. simpl. unfold at_offset.
  change (Zlength (sublist 0 (Zlength (@nil byte)) (@nil byte))) with 0.
  apply andp_right.
  - apply prop_right. split; [auto |].
    split; [unfold p1305_limbs_ok; simpl; repeat split; try rep_lia; reflexivity |].
    split; reflexivity.
  - cancel.
Qed.

Lemma body_poly1305_core_init :
  @semax_body (QPvarspecs Poly1305.qp) (aead_imports_def Poly1305.CS ++ aead_G_def) Poly1305.CS
    WgNoise.poly1305.code.f_poly1305_core_init poly1305_core_init_spec.
Proof.
  start_function.
  assert_PROP (field_compatible t_p1305_state [] hp) as FC by entailer!.
  rewrite data_at__memory_block. Intros.
  change (sizeof t_p1305_state) with 24.
  rewrite memory_block_data_at__tarray_tuchar_eq by rep_lia.
  forward_call (sh, hp, 0, 24).
  sep_apply (aead_ps_state_zero sh hp); auto.
  entailer!.
Qed.

Lemma body_poly1305_block_init_generic :
  @semax_body (QPvarspecs Poly1305.qp) (aead_imports_def Poly1305.CS ++ aead_G_def) Poly1305.CS
    WgNoise.poly1305.code.f_poly1305_block_init_generic poly1305_block_init_generic_spec.
Proof.
  start_function.
  assert_PROP (field_compatible t_p1305_block_state [] bp) as FC by entailer!.
  pose proof (aead_ps_fc_core_r bp FC) as FCU.
  sep_apply (aead_ps_bstate_split_ sh bp FC).
  forward_call (sh, bp).
  { cancel. }
  rewrite (@aead_data_at_tuchar_cs Poly1305.CS Poly1305Donna32.CS).
  forward_call (sh, offset_val 24 bp, rsh, raw, rk).
  rewrite (aead_ps_bstate_split sh [0; 0; 0; 0; 0] (p1305_r rk) bp FC).
  entailer!.
Qed.

Lemma body_poly1305_blocks_generic :
  @semax_body (QPvarspecs Poly1305.qp) (aead_imports_def Poly1305.CS ++ aead_G_def) Poly1305.CS
    WgNoise.poly1305.code.f_poly1305_blocks_generic poly1305_blocks_generic_spec.
Proof.
  start_function.
  assert_PROP (field_compatible t_p1305_block_state [] bp) as FC by entailer!.
  pose proof (aead_ps_fc_core_r bp FC) as FCU.
  rewrite (aead_ps_bstate_split sh h r bp FC).
  assert (HL: Zlength bs = 16 * (Zlength bs / 16)) by (rewrite (Z_div_mod_eq_full (Zlength bs) 16) at 1; lia).
  pose proof (Zlength_nonneg bs).
  rewrite aead_ps_prim_bytes_cs.
  forward_call (sh, bp, h, sh, offset_val 24 bp, r, msh, src, bs, Zlength bs / 16, hibit).
  { cancel. }
  Intros h'. Exists h'. rewrite (aead_ps_bstate_split sh h' r bp FC), aead_ps_prim_bytes_cs. entailer!.
Qed.

Lemma body_poly1305_emit_generic :
  @semax_body (QPvarspecs Poly1305.qp) (aead_imports_def Poly1305.CS ++ aead_G_def) Poly1305.CS
    WgNoise.poly1305.code.f_poly1305_emit_generic poly1305_emit_generic_spec.
Proof.
  start_function.
  rewrite aead_ps_h_cs, aead_ps_words_cs, (@aead_data_at__tuchar_cs Poly1305.CS Poly1305Donna32.CS).
  forward_call (hsh, hp, h, nsh, np, s, dsh, dst).
  entailer!.
Qed.

Lemma body_poly1305_init :
  @semax_body (QPvarspecs Poly1305.qp) (aead_imports_def Poly1305.CS ++ aead_G_def) Poly1305.CS
    WgNoise.poly1305.code.f_poly1305_init poly1305_init_spec.
Proof.
  start_function.
  assert_PROP (field_compatible t_p1305_ctx [] desc) as FC by entailer!.
  pose proof (field_compatible_nested_field t_p1305_ctx (DOT poly1305.code._state) desc
                ltac:(auto with field_compatible)) as FCs.
  simpl in FCs.
  assert (E: data_at ksh (tarray tuchar 32) (map Vubyte key) kp =
             data_at ksh (tarray tuchar (Zlength key)) (map Vubyte key) kp) by (rewrite H; auto).
  rewrite E.
  sep_apply (aead_ps_ctx_pre sh desc FC).
  flatten_sepcon_in_SEP. flatten_sepcon_in_SEP. flatten_sepcon_in_SEP. flatten_sepcon_in_SEP.
  assert_PROP (isptr kp) as Pkp by entailer!.
  forward_call (ksh, kp, 16, key). forward.
  forward_call (ksh, kp, 20, key). forward.
  forward_call (ksh, kp, 24, key). forward.
  forward_call (ksh, kp, 28, key). forward.
  forward.
  forward_call (sh, offset_val 40 desc, ksh, kp, key).
  rewrite E.
  sep_apply (aead_ps_init_post sh key desc H FC).
  entailer!.
Qed.

End PolySmall.

Theorem aead_poly_small_bodies :
  @semax_body (QPvarspecs Poly1305.qp) (aead_imports_def Poly1305.CS ++ aead_G_def) Poly1305.CS
    WgNoise.poly1305.code.f_poly1305_core_init poly1305_core_init_spec /\
  @semax_body (QPvarspecs Poly1305.qp) (aead_imports_def Poly1305.CS ++ aead_G_def) Poly1305.CS
    WgNoise.poly1305.code.f_poly1305_block_init_generic poly1305_block_init_generic_spec /\
  @semax_body (QPvarspecs Poly1305.qp) (aead_imports_def Poly1305.CS ++ aead_G_def) Poly1305.CS
    WgNoise.poly1305.code.f_poly1305_blocks_generic poly1305_blocks_generic_spec /\
  @semax_body (QPvarspecs Poly1305.qp) (aead_imports_def Poly1305.CS ++ aead_G_def) Poly1305.CS
    WgNoise.poly1305.code.f_poly1305_emit_generic poly1305_emit_generic_spec /\
  @semax_body (QPvarspecs Poly1305.qp) (aead_imports_def Poly1305.CS ++ aead_G_def) Poly1305.CS
    WgNoise.poly1305.code.f_poly1305_init poly1305_init_spec.
Proof.
  split; [| split; [| split; [| split]]].
  - exact body_poly1305_core_init.
  - exact body_poly1305_block_init_generic.
  - exact body_poly1305_blocks_generic.
  - exact body_poly1305_emit_generic.
  - exact body_poly1305_init.
Qed.
