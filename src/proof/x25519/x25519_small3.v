(* part of x25519_part3: the small functions of curve25519-fiat32.c.
   Specifications: x25519_spec.v, model: x25519_model.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.x25519.x25519_spec.

#[local] Existing Instance Curve25519Fiat32.CS.

Lemma zext8_small3 (v: int) : Int.unsigned v < 256 -> Int.zero_ext 8 v = v.
Proof.
  intros H. rewrite <- (Int.repr_unsigned (Int.zero_ext 8 v)).
  rewrite Int.zero_ext_mod by (cbn; lia).
  change (two_p 8) with 256.
  rewrite Z.mod_small by (pose proof (Int.unsigned_range v); lia).
  apply Int.repr_unsigned.
Qed.

Lemma zext8_and1_3 (x: int) : Int.zero_ext 8 (Int.and x Int.one) = Int.and x Int.one.
Proof.
  apply zext8_small3. rewrite Int.and_commut.
  pose proof (Int.and_le Int.one x). unfold Int.one in *. rewrite Int.unsigned_repr in * by rep_lia. lia.
Qed.

Lemma zext8_shru31_3 (x: int) : Int.zero_ext 8 (Int.shru x (Int.repr 31)) = Int.shru x (Int.repr 31).
Proof.
  apply zext8_small3. rewrite Int.shru_div_two_p.
  rewrite Int.unsigned_repr with (z := 31) by rep_lia.
  pose proof (Int.unsigned_range x).
  change (two_p 31) with 2147483648; change Int.modulus with 4294967296 in *.
  assert (0 <= Int.unsigned x / 2147483648 < 2) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite Int.unsigned_repr by rep_lia. lia.
Qed.

Lemma is_int_Vubyte3 (b: byte) : is_int I8 Unsigned (Vubyte b).
Proof.
  unfold Vubyte; simpl. pose proof (Byte.unsigned_range_2 b).
  rewrite Int.unsigned_repr by rep_lia. rep_lia.
Qed.

Lemma byte_all3 (f: byte -> bool) : forallb f (map Byte.repr (upto 256)) = true -> forall b, f b = true.
Proof.
  intros H b. rewrite forallb_forall in H. apply H.
  rewrite <- (Byte.repr_unsigned b). apply in_map. apply In_upto.
  pose proof (Byte.unsigned_range_2 b). simpl Z.of_nat. rep_lia.
Qed.

Lemma clamp0_val3 (b: byte) :
  Vubyte (Byte.and b (Byte.repr 248)) =
  force_val (sem_cast_i2i I8 Unsigned (force_val (sem_and tuchar tint (Vubyte b) (Vint (Int.repr 248))))).
Proof.
  assert (H: forall b, Int.eq (Int.repr (Byte.unsigned (Byte.and b (Byte.repr 248))))
                         (Int.zero_ext 8 (Int.and (Int.repr (Byte.unsigned b)) (Int.repr 248))) = true)
    by (apply byte_all3; vm_compute; reflexivity).
  specialize (H b). apply Int.same_if_eq in H. unfold Vubyte; simpl. rewrite H. reflexivity.
Qed.

Lemma clamp31_val3 (b: byte) :
  Vubyte (Byte.or (Byte.and b (Byte.repr 127)) (Byte.repr 64)) =
  force_val (sem_cast_i2i I8 Unsigned (force_val (sem_or tint tint
    (force_val (sem_and tuchar tint (Vubyte b) (Vint (Int.repr 127)))) (Vint (Int.repr 64))))).
Proof.
  assert (H: forall b, Int.eq (Int.repr (Byte.unsigned (Byte.or (Byte.and b (Byte.repr 127)) (Byte.repr 64))))
                         (Int.zero_ext 8 (Int.or (Int.and (Int.repr (Byte.unsigned b)) (Int.repr 127))
                                                 (Int.repr 64))) = true)
    by (apply byte_all3; vm_compute; reflexivity).
  specialize (H b). apply Int.same_if_eq in H. unfold Vubyte; simpl. rewrite H. reflexivity.
Qed.

Lemma limbs_fc3 (id: ident) (p: val) :
  (id = F._fe \/ id = F._fe_loose) ->
  field_compatible t_limbs [] p -> field_compatible (Tstruct id noattr) (DOT F._v) p.
Proof.
  intros Hid Hfc. destruct Hid; subst id; destruct Hfc as [Hp [_ [Hsz [Hal _]]]]; destruct p;
    try contradiction; repeat split; auto;
    (match goal with |- legal_field _ _ => simpl; left; reflexivity | |- _ => idtac end);
    unfold align_compatible in *; (eapply align_compatible_rec_Tstruct; [reflexivity | reflexivity | ]);
    intros i0 t z Hft Hfo; simpl in Hft, Hfo; destruct (ident_eq i0 F._v); inv Hft; inv Hfo;
    rewrite Z.add_0_r; exact Hal.
Qed.

Lemma limbs_field_fe3 (sh: share) (v: list val) (p: val) :
  data_at sh t_limbs v p = field_at sh (Tstruct F._fe noattr) (DOT F._v) v p.
Proof.
  rewrite field_at_data_at. unfold field_address.
  destruct (field_compatible_dec (Tstruct F._fe noattr) (DOT F._v) p) as [Hc|Hc].
  - simpl; rewrite isptr_offset_val_zero by (destruct Hc; auto); reflexivity.
  - apply pred_ext.
    + entailer!. exfalso. apply Hc, limbs_fc3; auto.
    + entailer!. match goal with H: field_compatible _ _ Vundef |- _ => destruct H; contradiction end.
Qed.

Lemma limbs_field_fel3 (sh: share) (v: list val) (p: val) :
  data_at sh t_limbs v p = field_at sh (Tstruct F._fe_loose noattr) (DOT F._v) v p.
Proof.
  rewrite field_at_data_at. unfold field_address.
  destruct (field_compatible_dec (Tstruct F._fe_loose noattr) (DOT F._v) p) as [Hc|Hc].
  - simpl; rewrite isptr_offset_val_zero by (destruct Hc; auto); reflexivity.
  - apply pred_ext.
    + entailer!. exfalso. apply Hc, limbs_fc3; auto.
    + entailer!. match goal with H: field_compatible _ _ Vundef |- _ => destruct H; contradiction end.
Qed.

Lemma body3_curve25519_clamp_secret : semax_body x25_V x25_Gprog F.f_curve25519_clamp_secret (@curve25519_clamp_secret_spec Curve25519Fiat32.CS).
Proof.
  start_function.
  forward. 2: forward. { entailer!. apply is_int_Vubyte3. }
  forward. 2: forward.
  { entailer!. rewrite upd_Znth_diff by (rewrite ?Zlength_map; lia). rewrite Znth_map by lia. apply is_int_Vubyte3. }
  entailer!. apply derives_refl'. f_equal. unfold clamp. rewrite <- !upd_Znth_map.
  rewrite upd_Znth_diff by (rewrite ?Zlength_map; lia). rewrite !Znth_map by lia.
  rewrite <- clamp0_val3, <- clamp31_val3. reflexivity.
Qed.

Lemma body3_addcarryx_u25 : semax_body x25_V x25_Gprog F.f_addcarryx_u25 addcarryx_u25_spec.
Proof.
  start_function.
  forward. forward. forward. entailer!. unfold addcarryx_m; simpl. rewrite zext8_and1_3. reflexivity.
Qed.

Lemma body3_addcarryx_u26 : semax_body x25_V x25_Gprog F.f_addcarryx_u26 addcarryx_u26_spec.
Proof.
  start_function.
  forward. forward. forward. entailer!. unfold addcarryx_m; simpl. rewrite zext8_and1_3. reflexivity.
Qed.

Lemma body3_subborrow_u25 : semax_body x25_V x25_Gprog F.f_subborrow_u25 subborrow_u25_spec.
Proof.
  start_function.
  forward. forward. forward. entailer!. unfold subborrow_m; simpl. rewrite zext8_shru31_3. reflexivity.
Qed.

Lemma body3_subborrow_u26 : semax_body x25_V x25_Gprog F.f_subborrow_u26 subborrow_u26_spec.
Proof.
  start_function.
  forward. forward. forward. entailer!. unfold subborrow_m; simpl. rewrite zext8_shru31_3. reflexivity.
Qed.

Lemma body3_cmovznz32 : semax_body x25_V x25_Gprog F.f_cmovznz32 cmovznz32_spec.
Proof.
  start_function.
  forward. 2: forward. { entailer!. destruct (Int.eq t Int.zero); simpl; rep_lia. }
  entailer!. unfold cmovznz32_m. destruct (Int.eq t Int.zero) eqn:E; reflexivity.
Qed.

Lemma body3_fe_copy : semax_body x25_V x25_Gprog F.f_fe_copy fe_copy_spec.
Proof.
  start_function.
  rewrite data_at__eq. rewrite !limbs_field_fe3.
  forward_for_simple_bound 10 (EX i:Z, PROP () LOCAL (temp F._h h; temp F._f fp)
    SEP (field_at osh (Tstruct F._fe noattr) (DOT F._v) (sublist 0 i (map Vint f) ++ Zrepeat Vundef (10 - i)) h;
         field_at fsh (Tstruct F._fe noattr) (DOT F._v) (map Vint f) fp))%assert.
  { entailer!. }
  { forward. forward. entailer!. apply derives_refl'. f_equal. list_solve. }
  rewrite <- !limbs_field_fe3. entailer!. apply derives_refl'. f_equal. list_solve.
Qed.

Lemma body3_fe_copy_lt : semax_body x25_V x25_Gprog F.f_fe_copy_lt fe_copy_lt_spec.
Proof.
  start_function.
  rewrite data_at__eq. rewrite (limbs_field_fel3 osh _ h), (limbs_field_fe3 fsh _ fp).
  forward_for_simple_bound 10 (EX i:Z, PROP () LOCAL (temp F._h h; temp F._f fp)
    SEP (field_at osh (Tstruct F._fe_loose noattr) (DOT F._v) (sublist 0 i (map Vint f) ++ Zrepeat Vundef (10 - i)) h;
         field_at fsh (Tstruct F._fe noattr) (DOT F._v) (map Vint f) fp))%assert.
  { entailer!. }
  { forward. forward. entailer!. apply derives_refl'. f_equal. list_solve. }
  rewrite <- limbs_field_fel3, <- limbs_field_fe3. entailer!. apply derives_refl'. f_equal. list_solve.
Qed.

Lemma body3_fe_0 : semax_body x25_V x25_Gprog F.f_fe_0 fe_0_spec.
Proof.
  start_function.
  rewrite data_at__eq. rewrite limbs_field_fe3.
  forward_for_simple_bound 10 (EX i:Z, PROP () LOCAL (temp F._h h)
    SEP (field_at osh (Tstruct F._fe noattr) (DOT F._v) (Zrepeat (Vint Int.zero) i ++ Zrepeat Vundef (10 - i)) h))%assert.
  { entailer!. }
  { forward. entailer!. apply derives_refl'. f_equal. list_solve. }
  rewrite <- limbs_field_fe3. entailer!.
Qed.

Lemma body3_fe_1 : semax_body x25_V x25_Gprog F.f_fe_1 fe_1_spec.
Proof.
  start_function.
  rewrite data_at__eq. rewrite limbs_field_fe3.
  forward_for_simple_bound 10 (EX i:Z, PROP () LOCAL (temp F._h h)
    SEP (field_at osh (Tstruct F._fe noattr) (DOT F._v) (Zrepeat (Vint Int.zero) i ++ Zrepeat Vundef (10 - i)) h))%assert.
  { entailer!. }
  { forward. entailer!. apply derives_refl'. f_equal. list_solve. }
  forward.
  rewrite <- limbs_field_fe3. entailer!.
Qed.

Lemma body3_fe_add_impl : semax_body x25_V x25_Gprog F.f_fe_add_impl fe_add_impl_spec.
Proof.
  start_function.
  do 20 forward.
  do 10 forward.
  entailer!.
Qed.

Lemma body3_fe_sub_impl : semax_body x25_V x25_Gprog F.f_fe_sub_impl fe_sub_impl_spec.
Proof.
  start_function.
  do 20 forward.
  do 10 forward.
  entailer!.
Qed.

Lemma body3_fe_cswap : semax_body x25_V x25_Gprog F.f_fe_cswap fe_cswap_spec.
Proof.
  start_function.
  forward.
  rewrite (limbs_field_fe3 sh1 _ fp), (limbs_field_fe3 sh2 _ gp).
  remember (fst (fe_cswap_m f g b)) as fs eqn:Efs. remember (snd (fe_cswap_m f g b)) as gs eqn:Egs.
  assert (Hfs: Zlength fs = 10) by (subst; reflexivity).
  assert (Hgs: Zlength gs = 10) by (subst; reflexivity).
  assert (Hfz: forall j, 0 <= j < 10 ->
    Znth j fs = Int.xor (Znth j f) (Int.and (Int.xor (Znth j f) (Znth j g)) (Int.sub (Int.repr 0) b))).
  { intros j Hj. subst fs. unfold fe_cswap_m. cbn [fst].
    rewrite Znth_map by (rewrite Zlength_upto; simpl; lia). rewrite Znth_upto by (simpl; lia). reflexivity. }
  assert (Hgz: forall j, 0 <= j < 10 ->
    Znth j gs = Int.xor (Znth j g) (Int.and (Int.xor (Znth j f) (Znth j g)) (Int.sub (Int.repr 0) b))).
  { intros j Hj. subst gs. unfold fe_cswap_m. cbn [snd].
    rewrite Znth_map by (rewrite Zlength_upto; simpl; lia). rewrite Znth_upto by (simpl; lia). reflexivity. }
  forward_for_simple_bound 10 (EX i:Z, PROP () LOCAL (temp F._b (Vint (Int.sub (Int.repr 0) b)); temp F._f fp; temp F._g gp)
    SEP (field_at sh1 (Tstruct F._fe noattr) (DOT F._v) (sublist 0 i (map Vint fs) ++ sublist i 10 (map Vint f)) fp;
         field_at sh2 (Tstruct F._fe noattr) (DOT F._v) (sublist 0 i (map Vint gs) ++ sublist i 10 (map Vint g)) gp))%assert.
  { entailer!. rewrite !sublist_nil, !app_nil_l, !sublist_same by (rewrite ?Zlength_map; lia). cancel. }
  { forward. { entailer!. autorewrite with sublist. exact I. }
    autorewrite with sublist.
    forward. { entailer!. autorewrite with sublist. exact I. }
    autorewrite with sublist.
    forward. forward.
    forward. { entailer!. autorewrite with sublist. exact I. }
    autorewrite with sublist.
    forward.
    forward. { entailer!. autorewrite with sublist. exact I. }
    autorewrite with sublist.
    forward.
    entailer!.
    pose proof (Hfz i H1); pose proof (Hgz i H1).
    apply sepcon_derives; apply derives_refl'; f_equal; list_simplify; assert (i0 = i) by lia; subst i0; congruence. }
  rewrite <- !limbs_field_fe3. entailer!.
  apply sepcon_derives; apply derives_refl'; f_equal; list_solve.
Qed.

Theorem x25519_small3 :
  semax_body x25_V x25_Gprog F.f_curve25519_clamp_secret (@curve25519_clamp_secret_spec Curve25519Fiat32.CS) /\
  semax_body x25_V x25_Gprog F.f_addcarryx_u25 addcarryx_u25_spec /\
  semax_body x25_V x25_Gprog F.f_addcarryx_u26 addcarryx_u26_spec /\
  semax_body x25_V x25_Gprog F.f_subborrow_u25 subborrow_u25_spec /\
  semax_body x25_V x25_Gprog F.f_subborrow_u26 subborrow_u26_spec /\
  semax_body x25_V x25_Gprog F.f_cmovznz32 cmovznz32_spec /\
  semax_body x25_V x25_Gprog F.f_fe_copy fe_copy_spec /\
  semax_body x25_V x25_Gprog F.f_fe_copy_lt fe_copy_lt_spec /\
  semax_body x25_V x25_Gprog F.f_fe_0 fe_0_spec /\
  semax_body x25_V x25_Gprog F.f_fe_1 fe_1_spec /\
  semax_body x25_V x25_Gprog F.f_fe_add_impl fe_add_impl_spec /\
  semax_body x25_V x25_Gprog F.f_fe_sub_impl fe_sub_impl_spec /\
  semax_body x25_V x25_Gprog F.f_fe_cswap fe_cswap_spec.
Proof.
  exact (conj body3_curve25519_clamp_secret (conj body3_addcarryx_u25 (conj body3_addcarryx_u26 (conj body3_subborrow_u25 (conj body3_subborrow_u26 (conj body3_cmovznz32 (conj body3_fe_copy (conj body3_fe_copy_lt (conj body3_fe_0 (conj body3_fe_1 (conj body3_fe_add_impl (conj body3_fe_sub_impl (body3_fe_cswap))))))))))))).
Qed.
