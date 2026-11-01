(* body proof of poly1305_final, against aead_spec3.aead_G3. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.chacha.code WgNoise.chacha_block.code WgNoise.poly1305.code WgNoise.poly1305_donna32.code
        WgNoise.chacha20poly1305.code WgNoise.shim.code.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.common.wg3_iface.
Require Import WgNoise.proof.aead.aead_spec3.
Require Import WgNoise.proof.aead.aead_cce.
Require Import WgNoise.proof.aead.aead_bytes.
Require Import WgNoise.proof.aead.aead_poly_small_ctx.
Require Import WgNoise.proof.aead.aead_poly_small_body.
Require Import WgNoise.proof.aead.aead_poly_final3_model.
Require Import WgNoise.proof.aead.aead_poly_final3_ctx.

Local Open Scope Z_scope.

#[local] Existing Instance Poly1305.CS.

Lemma pf3_fields_bytes sh buf bl (sv: list val) (st: reptype t_p1305_block_state) desc :
  field_compatible t_p1305_ctx [] desc ->
  (field_at sh t_p1305_ctx (DOT poly1305.code._buf) buf desc *
   field_at sh t_p1305_ctx (DOT poly1305.code._buflen) bl desc *
   field_at sh t_p1305_ctx (DOT poly1305.code._s) sv desc *
   spacer sh 36 40 desc *
   field_at sh t_p1305_ctx (DOT poly1305.code._state) st desc)%logic
  |-- data_at_ sh (tarray tuchar 112) desc.
Proof.
  intros FC. rewrite <- pf3_ctx_split. sep_apply data_at_data_at_.
  rewrite data_at__memory_block, prop_true_andp by auto. change (sizeof t_p1305_ctx) with 112.
  rewrite memory_block_data_at__tarray_tuchar_eq by rep_lia. auto.
Qed.

Lemma pf3_final_fold sh h k bufv blv sv desc :
  field_compatible t_p1305_ctx [] desc ->
  (data_at sh t_p1305_state (p1305_h_val h) (offset_val 40 desc) *
   data_at sh (tarray tuint 4) sv (offset_val 20 desc) *
   field_at sh t_p1305_ctx (DOT poly1305.code._buf) bufv desc *
   field_at sh t_p1305_ctx (DOT poly1305.code._buflen) blv desc *
   spacer sh 36 40 desc *
   data_at sh t_p1305_core_key k (offset_val 24 (offset_val 40 desc)))%logic
  |-- data_at_ sh (tarray tuchar 112) desc.
Proof.
  intros FC.
  assert (F5: field_compatible t_p1305_block_state [] (offset_val 40 desc)).
  { pose proof (field_compatible_nested_field t_p1305_ctx (DOT poly1305.code._state) desc
              ltac:(auto with field_compatible)) as X.
    simpl in X. exact X. }
  eapply derives_trans; [| apply (pf3_fields_bytes sh bufv blv sv (pf3_bstate_val h k) desc FC)].
  rewrite (field_at_data_at sh t_p1305_ctx (DOT poly1305.code._state)),
    (field_at_data_at sh t_p1305_ctx (DOT poly1305.code._s)).
  rewrite !field_compatible_field_address by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  rewrite pf3_bstate_split by auto.
  cancel.
Qed.

Theorem aead_poly_final_bodies3 :
  @semax_body (QPvarspecs Poly1305.qp) (aead_imports3 Poly1305.CS ++ aead_G3) Poly1305.CS
    WgNoise.poly1305.code.f_poly1305_final poly1305_final_spec.
Proof.
  start_function.
  unfold p1305_state. Intros h junk.
  set (n := Zlength msg / 16 * 16) in *.
  set (rest := sublist n (Zlength msg) msg) in *.
  assert_PROP (field_compatible t_p1305_ctx [] desc) as FC by entailer!.
  rewrite aead_ps_ctx_split. Intros.
  assert (Hrest: Zlength rest = Zlength msg - n /\ 0 <= Zlength msg - n < 16).
  { pose proof (Zlength_nonneg msg). pose proof (Z.mod_pos_bound (Zlength msg) 16 ltac:(lia)).
    pose proof (Z_div_mod_eq_full (Zlength msg) 16).
    assert (0 <= n <= Zlength msg) by (subst n; lia).
    subst rest. rewrite Zlength_sublist by lia. lia. }
  forward.
  forward_if (EX h': list Z, EX bufv: list val, EX blv: val,
    PROP (p1305_limbs_ok h'; p1305_limbs_val h' mod p1305_p = p1305_acc (p1305_r key) 0 msg)
    LOCAL (temp poly1305.code._desc desc; temp poly1305.code._dst dst)
    SEP (field_at sh t_p1305_ctx (DOT poly1305.code._buf) bufv desc;
         field_at sh t_p1305_ctx (DOT poly1305.code._buflen) blv desc;
         field_at sh t_p1305_ctx (DOT poly1305.code._s) (map Vint (p1305_s_words key)) desc;
         spacer sh 36 40 desc;
         field_at sh t_p1305_ctx (DOT poly1305.code._state) (p1305_bstate_val h' (p1305_r key)) desc;
         data_at_ osh (tarray tuchar 16) dst))%assert.
  - forward. forward. forward.
    destruct Hrest as [Hk Hk'].
    assert (Hb: upd_Znth (Zlength rest) (map Vubyte rest ++ junk) (Vint (Int.zero_ext 8 (Int.repr 1))) =
                map Vubyte (rest ++ [Byte.one]) ++ sublist 1 (Zlength junk) junk).
    { rewrite upd_Znth_app2 by (rewrite Zlength_map; lia). rewrite Zlength_map, Z.sub_diag.
      rewrite map_app. rewrite <- app_assoc. f_equal.
      destruct junk as [| j junk']; [rewrite Zlength_nil in H2; lia |].
      rewrite upd_Znth0, Zlength_cons. simpl. rewrite sublist_1_cons. f_equal. rewrite sublist_same by lia. reflexivity. }
    rewrite Hb, add_repr.
    forward. forward.
    rewrite field_at_data_at, field_compatible_field_address by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset. rewrite isptr_offset_val_zero by auto with field_compatible.
    assert (Hl: Zlength (map Vubyte (rest ++ [Byte.one]) ++ sublist 1 (Zlength junk) junk) = 16).
    { rewrite Zlength_app, Zlength_map, Zlength_app, Zlength_sublist by lia. rewrite Zlength_cons, Zlength_nil. lia. }
    rewrite (split2_data_at_Tarray_tuchar sh 16 (Zlength rest + 1)) by lia.
    assert (F1: field_compatible (tarray tuchar 16) [] desc).
    { pose proof (field_compatible_nested_field t_p1305_ctx (DOT poly1305.code._buf) desc
                ltac:(auto with field_compatible)) as X.
      simpl in X. rewrite isptr_offset_val_zero in X by auto with field_compatible. exact X. }
    rewrite field_address0_offset by auto with field_compatible.
    assert (Hs1: sublist 0 (Zlength rest + 1) (map Vubyte (rest ++ [Byte.one]) ++ sublist 1 (Zlength junk) junk) =
                 map Vubyte (rest ++ [Byte.one])) by list_solve.
    assert (Hs2: sublist (Zlength rest + 1) 16 (map Vubyte (rest ++ [Byte.one]) ++ sublist 1 (Zlength junk) junk) =
                 sublist 1 (Zlength junk) junk) by list_solve.
    rewrite Hs1, Hs2.
    simpl nested_field_offset. replace (0 + 1 * (Zlength rest + 1)) with (Zlength rest + 1) by lia.
    Intros.
    forward_call (sh, offset_val (Zlength rest + 1) desc, 0, 16 - (Zlength rest + 1)).
    set (bs := rest ++ [Byte.one] ++ Zrepeat Byte.zero (15 - Zlength rest)).
    assert (Hbs: Zlength bs = 16) by (subst bs; list_solve).
    gather_SEP 0 1.
    replace_SEP 0 (prim_bytes sh bs desc).
    { unfold prim_bytes. rewrite Hbs. rewrite if_false by lia.
      rewrite (split2_data_at_Tarray_tuchar sh 16 (Zlength rest + 1)) by (rewrite ?Zlength_map; lia).
      rewrite field_address0_offset by auto with field_compatible.
      simpl nested_field_offset. replace (0 + 1 * (Zlength rest + 1)) with (Zlength rest + 1) by lia.
      replace (sublist 0 (Zlength rest + 1) (map Vubyte bs)) with (map Vubyte (rest ++ [Byte.one]))
        by (subst bs; list_solve).
      replace (sublist (Zlength rest + 1) 16 (map Vubyte bs))
        with (Zrepeat (Vubyte (Byte.repr 0)) (16 - (Zlength rest + 1))) by (subst bs; list_solve).
      entailer!. }
    assert (F5: field_compatible t_p1305_block_state [] (offset_val 40 desc)).
    { pose proof (field_compatible_nested_field t_p1305_ctx (DOT poly1305.code._state) desc
                ltac:(auto with field_compatible)) as X.
      simpl in X. exact X. }
    rewrite (field_at_data_at sh t_p1305_ctx (DOT poly1305.code._state)).
    rewrite field_compatible_field_address by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset.
    forward_call (sh, offset_val 40 desc, h, p1305_r key, sh, desc, bs, 0).
    { rewrite Hbs. entailer!. cbv [eval_field typeof]. simpl.
      rewrite isptr_offset_val_zero by auto with field_compatible. reflexivity. }
    { split; [apply pf3_r_ok | rewrite Hbs; reflexivity]. }
    Intros h'.
    assert (HM: p1305_limbs_val h' mod p1305_p = p1305_acc (p1305_r key) 0 msg).
    { rewrite H5. unfold bs. rewrite pf3_core_last_mod by lia. rewrite H1.
      pose proof (pf3_acc_split (p1305_r key) msg) as HA. cbv zeta in HA.
      change (Zlength msg / 16 * 16) with n in HA. fold rest in HA.
      rewrite if_true in HA by lia. rewrite HA. reflexivity. }
    Exists h' (map Vubyte bs) (Vint (Int.repr (Zlength rest + 1))).
    unfold prim_bytes. rewrite Hbs, if_false by lia.
    rewrite (field_at_data_at sh t_p1305_ctx (DOT poly1305.code._buf)),
      (field_at_data_at sh t_p1305_ctx (DOT poly1305.code._state)).
    rewrite !field_compatible_field_address by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset. rewrite isptr_offset_val_zero by auto with field_compatible.
    entailer!.
  - forward.
    destruct Hrest as [Hk Hk'].
    assert (Hk0: Zlength rest = 0).
    { apply repr_inj_unsigned in H3; rep_lia. }
    assert (HM: p1305_limbs_val h mod p1305_p = p1305_acc (p1305_r key) 0 msg).
    { rewrite H1.
      pose proof (pf3_acc_split (p1305_r key) msg) as HA. cbv zeta in HA.
      change (Zlength msg / 16 * 16) with n in HA.
      rewrite if_false in HA by lia. rewrite HA. reflexivity. }
    Exists h (map Vubyte rest ++ junk) (Vint (Int.repr (Zlength rest))).
    entailer!.
  - Intros h' bufv blv.
    assert (F5: field_compatible t_p1305_block_state [] (offset_val 40 desc)).
    { pose proof (field_compatible_nested_field t_p1305_ctx (DOT poly1305.code._state) desc
                ltac:(auto with field_compatible)) as X.
      simpl in X. exact X. }
    rewrite (field_at_data_at sh t_p1305_ctx (DOT poly1305.code._state)),
      (field_at_data_at sh t_p1305_ctx (DOT poly1305.code._s)).
    rewrite !field_compatible_field_address by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset.
    change (p1305_bstate_val h' (p1305_r key)) with (pf3_bstate_val h' (p1305_key_val (p1305_r key))).
    rewrite pf3_bstate_split by auto. Intros.
    forward_call (sh, offset_val 40 desc, h', sh, offset_val 20 desc, p1305_s_words key, osh, dst).
    sep_apply (pf3_final_fold sh h' (p1305_key_val (p1305_r key)) bufv blv (map Vint (p1305_s_words key)) desc FC).
    rewrite H4, pf3_s_words by auto.
    change (le_bytes 16 ((p1305_acc (p1305_r key) 0 msg + p1305_s key) mod 2 ^ 128)) with (poly1305_tag key msg).
    remember (poly1305_tag key msg) as tag.
    forward_call (sh, desc, 0, 112).
    sep_apply (pf3_ctx_zero sh desc); auto.
    entailer!.
Qed.
