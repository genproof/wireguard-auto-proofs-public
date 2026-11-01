(* law prim_aead: the small common.h helpers. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.harness.prim_aead.haead_spec3.
Require Import WgNoise.proof.harness.prim_aead.haead_lemmas3.
Require WgNoise.harness.x_prim_aead.code.

#[local] Existing Instance W_prim_aead.
Local Open Scope Z_scope.

Module C := WgNoise.harness.x_prim_aead.code.

(* ---------------------------------------------------------------------- *)
(* arithmetic                                                              *)
(* ---------------------------------------------------------------------- *)

Lemma haead_small_is_int_Vubyte: forall b, is_int I8 Unsigned (Vubyte b).
Proof.
  intros. unfold Vubyte; simpl. pose proof (Byte.unsigned_range_2 b).
  rewrite Int.unsigned_repr by rep_lia. rep_lia.
Qed.

Lemma haead_small_lor_add a b k : 0 <= k -> 0 <= a < 2 ^ k ->
  Z.lor a (Z.shiftl b k) = a + Z.shiftl b k.
Proof.
  intros Hk Ha.
  assert (Z.land a (Z.shiftl b k) = 0).
  { apply Z.bits_inj'; intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases n k).
    - rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
    - rewrite <- (Z.mod_small a (2 ^ k)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite Z.add_nocarry_lxor by auto. rewrite Z.lxor_lor by auto. reflexivity.
Qed.

Lemma haead_small_or_shl a b k : 0 <= k < 32 -> 0 <= a < 2 ^ k -> 0 <= b -> a + b * 2 ^ k <= Int.max_unsigned ->
  Int.or (Int.repr a) (Int.shl (Int.repr b) (Int.repr k)) = Int.repr (a + b * 2 ^ k).
Proof.
  intros Hk Ha Hb Hs. assert (0 < 2 ^ k) by lia. assert (b <= b * 2 ^ k) by nia.
  unfold Int.or, Int.shl. rewrite !(Int.unsigned_repr a), (Int.unsigned_repr b), (Int.unsigned_repr k) by rep_lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite Int.unsigned_repr by nia.
  rewrite <- Z.shiftl_mul_pow2 by lia. rewrite haead_small_lor_add by lia.
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma haead_small_or_shl64 a b k : 0 <= k < 64 -> 0 <= a < 2 ^ k -> 0 <= b -> a + b * 2 ^ k <= Int64.max_unsigned ->
  Int64.or (Int64.repr a) (Int64.shl (Int64.repr b) (Int64.repr k)) = Int64.repr (a + b * 2 ^ k).
Proof.
  intros Hk Ha Hb Hs. assert (0 < 2 ^ k) by lia. assert (b <= b * 2 ^ k) by nia.
  unfold Int64.or, Int64.shl.
  rewrite !(Int64.unsigned_repr a), (Int64.unsigned_repr b), (Int64.unsigned_repr k) by rep_lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite Int64.unsigned_repr by nia.
  rewrite <- Z.shiftl_mul_pow2 by lia. rewrite haead_small_lor_add by lia.
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma haead_small_le_Z_app a b : le_Z (a ++ b) = le_Z a + 2 ^ (8 * Zlength a) * le_Z b.
Proof.
  induction a as [|x a IH]; simpl app; simpl le_Z.
  - rewrite Zlength_nil. simpl. lia.
  - rewrite IH, Zlength_cons. replace (8 * Z.succ (Zlength a)) with (8 + 8 * Zlength a) by lia.
    rewrite Z.pow_add_r by (pose proof (Zlength_nonneg a); lia). change (2 ^ 8) with 256. ring.
Qed.

Lemma haead_small_le_Z_range bs : 0 <= le_Z bs < 2 ^ (8 * Zlength bs).
Proof.
  induction bs as [|x bs IH]; simpl le_Z.
  - rewrite Zlength_nil. simpl. lia.
  - rewrite Zlength_cons. replace (8 * Z.succ (Zlength bs)) with (8 + 8 * Zlength bs) by lia.
    rewrite Z.pow_add_r by (pose proof (Zlength_nonneg bs); lia). change (2 ^ 8) with 256.
    pose proof (Byte.unsigned_range_2 x). change Byte.max_unsigned with 255 in *. lia.
Qed.

Lemma haead_small_le32_at bs i : 0 <= i -> i + 4 <= Zlength bs ->
  Int.unsigned (le32_at bs i) = le_Z (sublist i (i + 4) bs).
Proof.
  intros. rewrite !(sublist_next _ (i + 4)) by lia. rewrite sublist_nil' by lia. simpl le_Z.
  unfold le32_at, le32_of.
  pose proof (Byte.unsigned_range_2 (Znth i bs)). pose proof (Byte.unsigned_range_2 (Znth (i + 1) bs)).
  pose proof (Byte.unsigned_range_2 (Znth (i + 2) bs)). pose proof (Byte.unsigned_range_2 (Znth (i + 3) bs)).
  change Byte.max_unsigned with 255 in *.
  rewrite haead_small_or_shl by (change (2 ^ 8) with 256; rep_lia).
  rewrite haead_small_or_shl by (change (2 ^ 8) with 256; change (2 ^ 16) with 65536; rep_lia).
  rewrite haead_small_or_shl by (change (2 ^ 8) with 256; change (2 ^ 16) with 65536;
                                 change (2 ^ 24) with 16777216; rep_lia).
  change (2 ^ 8) with 256; change (2 ^ 16) with 65536; change (2 ^ 24) with 16777216.
  rewrite Int.unsigned_repr by rep_lia. replace (i + 1 + 1) with (i + 2) by lia.
  replace (i + 2 + 1) with (i + 3) by lia. ring.
Qed.

Lemma haead_small_byte_shiftr z k : 0 <= k <= 24 ->
  Byte.repr (Z.shiftr (Int.unsigned (Int.repr z)) k) = Byte.repr (Z.shiftr z k).
Proof.
  intros Hk. apply Byte.same_bits_eq; intros j Hj. change Byte.zwordsize with 8 in Hj.
  rewrite !Byte.testbit_repr by (change Byte.zwordsize with 8; lia).
  rewrite !Z.shiftr_spec by lia.
  change (Z.testbit (Int.unsigned (Int.repr z)) (j + k)) with (Int.testbit (Int.repr z) (j + k)).
  rewrite Int.testbit_repr by (change Int.zwordsize with 32; lia). reflexivity.
Qed.

Lemma haead_small_zext8 x : Vint (Int.zero_ext 8 x) = Vubyte (Byte.repr (Int.unsigned x)).
Proof.
  unfold Vubyte. f_equal. apply Int.same_bits_eq; intros j Hj.
  rewrite Int.bits_zero_ext by lia. rewrite Int.testbit_repr by auto.
  destruct (zlt j 8).
  - change (Z.testbit (Byte.unsigned (Byte.repr (Int.unsigned x))) j) with (Byte.testbit (Byte.repr (Int.unsigned x)) j).
    rewrite Byte.testbit_repr by (change Byte.zwordsize with 8; lia). reflexivity.
  - symmetry. apply Byte.bits_above. change Byte.zwordsize with 8; lia.
Qed.

Lemma haead_small_unsigned_shru x k : 0 <= k < 32 ->
  Int.unsigned (Int.shru x (Int.repr k)) = Z.shiftr (Int.unsigned x) k.
Proof.
  intros. unfold Int.shru. rewrite (Int.unsigned_repr k) by rep_lia. apply Int.unsigned_repr.
  pose proof (Int.unsigned_range_2 x). assert (1 <= 2 ^ k) by (pose proof (Z.pow_pos_nonneg 2 k); lia).
  split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by lia.
  apply Z.div_le_upper_bound; nia.
Qed.

Lemma haead_small_shru x k : 0 <= k < 32 -> Int.shru x (Int.repr k) = Int.repr (Z.shiftr (Int.unsigned x) k).
Proof. intros. unfold Int.shru. rewrite Int.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma haead_small_shiftr_div z k : 0 <= k -> Z.shiftr z k / 256 = Z.shiftr z (k + 8).
Proof.
  intros. rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia.
  rewrite Z.pow_add_r by lia. reflexivity.
Qed.

Lemma haead_small_le_bytes_S n z k : 0 <= k ->
  le_bytes (S n) (Z.shiftr z k) = Byte.repr (Z.shiftr z k) :: le_bytes n (Z.shiftr z (k + 8)).
Proof. intros. cbn [le_bytes]. rewrite haead_small_shiftr_div by lia. reflexivity. Qed.

Lemma haead_small_byte_shiftr0 z : Byte.repr (Int.unsigned (Int.repr z)) = Byte.repr (Z.shiftr z 0).
Proof. rewrite <- (Z.shiftr_0_r (Int.unsigned (Int.repr z))). apply haead_small_byte_shiftr. lia. Qed.

Lemma haead_small_le64_bytes v : 0 <= v <= Int64.max_unsigned ->
  le32_bytes (Int.repr (Int64.unsigned (Int64.repr v))) ++
  le32_bytes (Int.repr (Int64.unsigned (Int64.shru (Int64.repr v) (Int64.repr 32)))) = le64_bytes v.
Proof.
  intros Hv. unfold Int64.shru. rewrite !(Int64.unsigned_repr v), (Int64.unsigned_repr 32) by rep_lia.
  assert (0 <= Z.shiftr v 32 <= Int64.max_unsigned).
  { split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by lia.
    apply Z.div_le_upper_bound; lia. }
  rewrite Int64.unsigned_repr by lia.
  unfold le32_bytes, le64_bytes.
  transitivity (le_bytes 8 (Z.shiftr v 0)); [|rewrite Z.shiftr_0_r; reflexivity].
  rewrite !haead_small_le_bytes_S by lia. simpl Z.add. cbn [le_bytes].
  rewrite !haead_small_byte_shiftr by lia. rewrite !haead_small_byte_shiftr0.
  rewrite !Z.shiftr_shiftr by lia. reflexivity.
Qed.

Lemma haead_small_le32_bytes_length w : Zlength (le32_bytes w) = 4.
Proof. reflexivity. Qed.

Lemma haead_small_splice_length i l c : 0 <= i -> i + Zlength l <= Zlength c ->
  Zlength (haead_splice i l c) = Zlength c.
Proof. intros. unfold haead_splice. list_solve. Qed.

Lemma haead_small_splice_twice i l1 l2 c : 0 <= i -> i + Zlength l1 + Zlength l2 <= Zlength c ->
  haead_splice (i + Zlength l1) l2 (haead_splice i l1 c) = haead_splice i (l1 ++ l2) c.
Proof. intros. unfold haead_splice. list_solve. Qed.

(* ---------------------------------------------------------------------- *)
(* bodies                                                                  *)
(* ---------------------------------------------------------------------- *)

Lemma haead_small_body_check_failed :
  semax_body haead_V haead_Gprog C.f_check_failed check_failed_spec.
Proof.
  start_function. contradiction.
Qed.

Lemma haead_small_body_bytes_eq :
  semax_body haead_V haead_Gprog C.f_bytes_eq bytes_eq_spec.
Proof.
  start_function.
  forward_for_simple_bound (Zlength la) (EX i:Z,
    PROP (sublist 0 i la = sublist 0 i lb)
    LOCAL (temp C._a a; temp C._b b; temp C._n (Vlong (Int64.repr (Zlength la))))
    SEP (data_at sha (tarray tuchar (Zlength la)) (map Vubyte la) a;
         data_at shb (tarray tuchar (Zlength lb)) (map Vubyte lb) b)).
  - entailer!.
  - cbv beta. Intros.
    forward.
    { entailer!. try rewrite Znth_map by lia; apply haead_small_is_int_Vubyte. }
    forward.
    { entailer!. try rewrite Znth_map by lia; apply haead_small_is_int_Vubyte. }
    rewrite !Znth_map by lia.
    forward_if (PROP (Znth i la = Znth i lb)
      LOCAL (temp C._i (Vlong (Int64.repr i));
             temp C._a a; temp C._b b; temp C._n (Vlong (Int64.repr (Zlength la))))
      SEP (data_at sha (tarray tuchar (Zlength la)) (map Vubyte la) a;
           data_at shb (tarray tuchar (Zlength lb)) (map Vubyte lb) b)).
    + forward.
      destruct (list_eq_dec Byte.eq_dec la lb); [subst; contradiction|].
      entailer!.
    + forward. entailer!.
      rewrite <- (Byte.repr_unsigned (Znth i la)), <- (Byte.repr_unsigned (Znth i lb)). f_equal. assumption.
    + Intros. entailer!.
      rewrite (sublist_split 0 i (i+1) la), (sublist_split 0 i (i+1) lb), !sublist_len_1 by lia. congruence.
  - forward.
    match goal with H: sublist 0 _ la = sublist 0 _ lb |- _ =>
      rewrite !sublist_same in H by lia; subst la end.
    destruct (list_eq_dec Byte.eq_dec lb lb); [|contradiction].
    entailer!.
Qed.

Lemma haead_small_body_bytes_copy :
  semax_body haead_V haead_Gprog C.f_bytes_copy bytes_copy_spec.
Proof.
  start_function.
  forward_for_simple_bound (Zlength bs) (EX i:Z,
    PROP ()
    LOCAL (temp C._d d; temp C._s s; temp C._n (Vlong (Int64.repr (Zlength bs))))
    SEP (data_at dsh (tarray tuchar (Zlength bs)) (map Vubyte (sublist 0 i bs) ++ Zrepeat Vundef (Zlength bs - i)) d;
         data_at ssh (tarray tuchar (Zlength bs)) (map Vubyte bs) s)).
  - entailer!. simpl app. apply derives_refl.
  - forward.
    { entailer!. try rewrite Znth_map by lia; apply haead_small_is_int_Vubyte. }
    forward. entailer!. apply derives_refl'. f_equal. list_solve.
  - entailer!. apply derives_refl'. f_equal. list_solve.
Qed.

Lemma haead_small_body_bytes_set :
  semax_body haead_V haead_Gprog C.f_bytes_set bytes_set_spec.
Proof.
  start_function.
  forward_for_simple_bound n (EX i:Z,
    PROP ()
    LOCAL (temp C._d d; temp C._v (Vint (Int.repr v)); temp C._n (Vlong (Int64.repr n)))
    SEP (data_at sh (tarray tuchar n) (Zrepeat (Vubyte (Byte.repr v)) i ++ Zrepeat Vundef (n - i)) d)).
  - entailer!. simpl app. apply derives_refl.
  - forward. entailer!. apply derives_refl'. f_equal.
    unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. list_solve.
  - entailer!. apply derives_refl'. f_equal. list_solve.
Qed.

Lemma haead_small_body_draw_size :
  semax_body haead_V haead_Gprog C.f_draw_size draw_size_spec.
Proof.
  start_function.
  forward_call tt.
  Intros n.
  forward_if (PROP () LOCAL (temp C._t'2 (Vlong (Int64.repr n))) SEP ()).
  - forward. entailer!.
  - exfalso. revert H0. unfold Int64.ltu.
    change (Int64.unsigned (Int64.repr (-1))) with Int64.max_unsigned.
    rewrite Int64.unsigned_repr by rep_lia.
    destruct (zlt _ _); [rep_lia|discriminate].
  - forward. Exists n. entailer!.
Qed.

Lemma haead_small_body_draw_u64 :
  semax_body haead_V haead_Gprog C.f_draw_u64 draw_u64_spec.
Proof.
  start_function.
  (* forward_call would fuse the call with the (non-neutral) cast hi = (u64)t'1: split the sequence *)
  apply semax_seq' with
    (P' := EX a: Z, PROP (0 <= a <= Int.max_unsigned) LOCAL (temp C._hi (Vlong (Int64.repr a))) SEP ()).
  { eapply semax_seq'. forward_call tt. apply andp_left2, derives_refl. Intros a. forward. Exists a. entailer!. }
  abbreviate_semax. Intros a.
  forward_call tt.
  Intros b.
  forward.
  Exists (b + a * 2 ^ 32). entailer!.
  f_equal. rewrite Int64.or_commut. apply haead_small_or_shl64; change (2 ^ 32) with 4294967296; rep_lia.
Qed.

Lemma haead_small_body_le32_load :
  semax_body haead_V haead_Gprog C.f_le32_load le32_load_spec.
Proof.
  start_function.
  assert_PROP (field_compatible (tarray tuchar (Zlength bs)) [] p) by entailer!.
  rewrite (split2_data_at_Tarray_tuchar sh (Zlength bs) i) by (rewrite ?Zlength_map; lia).
  change (Tarray tuchar (Zlength bs) noattr) with (tarray tuchar (Zlength bs)).
  rewrite arr_field_address0 by (auto; lia). simpl sizeof. rewrite Z.mul_1_l.
  rewrite !sublist_map. Intros.
  forward; [entailer!; try rewrite Znth_map by list_solve; apply haead_small_is_int_Vubyte|].
  forward; [entailer!; try rewrite Znth_map by list_solve; apply haead_small_is_int_Vubyte|].
  forward; [entailer!; try rewrite Znth_map by list_solve; apply haead_small_is_int_Vubyte|].
  forward; [entailer!; try rewrite Znth_map by list_solve; apply haead_small_is_int_Vubyte|].
  rewrite !Znth_map by list_solve. rewrite !Znth_sublist by list_solve.
  forward.
  apply andp_right.
  - apply prop_right. unfold le32_at, le32_of, Vubyte. simpl. rewrite !(Z.add_comm _ i). reflexivity.
  - rewrite (split2_data_at_Tarray_tuchar sh (Zlength bs) i) by list_solve.
    change (Tarray tuchar (Zlength bs) noattr) with (tarray tuchar (Zlength bs)).
    rewrite arr_field_address0 by (auto; lia). simpl sizeof. rewrite Z.mul_1_l, !sublist_map. cancel.
Qed.

Lemma haead_small_body_le32_store :
  semax_body haead_V haead_Gprog C.f_le32_store le32_store_spec.
Proof.
  start_function.
  assert_PROP (field_compatible (tarray tuchar (Zlength contents)) [] p) by entailer!.
  rewrite (split2_data_at_Tarray_tuchar sh (Zlength contents) i) by lia.
  change (Tarray tuchar (Zlength contents) noattr) with (tarray tuchar (Zlength contents)).
  rewrite arr_field_address0 by (auto; lia). simpl sizeof. rewrite Z.mul_1_l.
  Intros. forward. forward. forward. forward.
  rewrite !Int.zero_ext_idem by lia. rewrite !haead_small_zext8. rewrite !haead_small_unsigned_shru by lia.
  entailer!.
  assert (Zlength (haead_splice i (le32_bytes v) contents) = Zlength contents)
    by (unfold haead_splice, le32_bytes; list_solve).
  rewrite (split2_data_at_Tarray_tuchar sh (Zlength contents) i (haead_splice i (le32_bytes v) contents)) by lia.
  change (Tarray tuchar (Zlength contents) noattr) with (tarray tuchar (Zlength contents)).
  rewrite arr_field_address0 by (auto; lia). simpl sizeof. rewrite Z.mul_1_l.
  apply sepcon_derives; apply derives_refl'; f_equal; unfold haead_splice, le32_bytes; list_solve.
Qed.

Lemma haead_small_body_le64_store :
  semax_body haead_V haead_Gprog C.f_le64_store le64_store_spec.
Proof.
  start_function.
  assert_PROP (isptr p) by entailer!.
  forward_call (sh, p, i, contents, Int.repr (Int64.unsigned (Int64.repr v))).
  rewrite <- (haead_small_splice_length i (le32_bytes (Int.repr (Int64.unsigned (Int64.repr v)))) contents)
    by (try rewrite haead_small_le32_bytes_length; lia).
  (* the second call by hand: forward_call's check of the arguments p + 4, (u32)(v >> 32) diverges *)
  rewrite semax_seq_skip. eapply semax_seq'.
  match goal with |- @semax ?CS _ ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R'))) ?c _ =>
    match c with context [Scall _ (Evar ?id ?ty) ?bl] => exploit (call_setup1_i2 CS Delta P Q R' id ty bl) end end;
  [check_prove_local2ptree
  | apply can_assume_funcptr2;
    [check_function_name | lookup_spec C._le32_store | find_spec_in_globals' | check_type_of_funspec C._le32_store]
  | check_subsumes funspec_sub_refl
  | try reflexivity; (eapply classify_fun_ty_hack; [apply funspec_sub_refl| reflexivity ..])
  | check_typecheck | check_typecheck | check_cast_params | ..].
  let H := fresh "SetupOne" in intro H;
  match goal with |- @semax ?CS _ _ (PROPx ?P (LOCALx ?L (SEPx ?R'))) _ _ =>
    let Frame := fresh "Frame" in evar (Frame: list mpred);
    exploit (call_setup2_i _ _ _ _ _ _ _ _ R' R' _ _ _ _ (@nil Type) _ _ _ _ _ _ _ H
      (sh, p, i + 4, haead_splice i (le32_bytes (Int.repr (Int64.unsigned (Int64.repr v)))) contents,
       Int.repr (Int64.unsigned (Int64.shru (Int64.repr v) (Int64.repr 32)))) Frame); clear H end.
  1: reflexivity.
  1: check_prove_local2ptree.
  1: apply prop_right.
  1: cbn [firstn Datatypes.length typeof]; apply (f_equal2 cons); [| apply (f_equal2 cons); [| reflexivity]].
  2: reflexivity.
  1: destruct p; try contradiction;
     change (eval_binop Oadd (tptr tuchar) tint (offset_val i (Vptr b i0)) (Vint (Int.repr 4)))
       with (offset_val 4 (offset_val i (Vptr b i0)));
     rewrite offset_offset_val; reflexivity.
  1: auto 50 with derives.
  1: check_gvars_spec.
  1: cancel_for_forward_call.
  1: clear_Delta_specs; clear_MORE_POST; forward_call_id00_wow.
  1: split; [lia | rewrite haead_small_splice_length by (try rewrite haead_small_le32_bytes_length; lia); lia].
  after_forward_call.
  rewrite haead_small_splice_length by (try rewrite haead_small_le32_bytes_length; lia).
  replace (i + 4) with (i + Zlength (le32_bytes (Int.repr (Int64.unsigned (Int64.repr v)))))
    by (rewrite haead_small_le32_bytes_length; lia).
  rewrite haead_small_splice_twice by (try rewrite !haead_small_le32_bytes_length; lia).
  rewrite haead_small_le64_bytes by lia.
  entailer!.
Qed.

Lemma haead_small_body_le64_load :
  semax_body haead_V haead_Gprog C.f_le64_load le64_load_spec.
Proof.
  start_function.
  assert_PROP (isptr p) by entailer!.
  forward_call (sh, p, i, bs).
  forward_call (sh, p, i + 4, bs).
  forward.
  apply prop_right. f_equal.
  rewrite !haead_small_le32_at by lia.
  pose proof (haead_small_le_Z_range (sublist i (i + 4) bs)).
  pose proof (haead_small_le_Z_range (sublist (i + 4) (i + 4 + 4) bs)).
  rewrite !Zlength_sublist in * by lia.
  replace (8 * (i + 4 - i)) with 32 in * by lia. replace (8 * (i + 4 + 4 - (i + 4))) with 32 in * by lia.
  change (2 ^ 32) with 4294967296 in *.
  rewrite haead_small_or_shl64 by (change (2 ^ 32) with 4294967296; rep_lia).
  rewrite (sublist_split i (i + 4) (i + 8)) by lia.
  rewrite haead_small_le_Z_app, Zlength_sublist by lia.
  replace (i + 4 + 4) with (i + 8) by lia. replace (8 * (i + 4 - i)) with 32 by lia.
  change (2 ^ 32) with 4294967296. f_equal. ring.
Qed.

Lemma haead_small_bodies3 : haead_hyps ->
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_check_failed check_failed_spec /\
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_bytes_eq bytes_eq_spec /\
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_bytes_copy bytes_copy_spec /\
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_bytes_set bytes_set_spec /\
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_draw_size draw_size_spec /\
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_draw_u64 draw_u64_spec /\
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_le32_store le32_store_spec /\
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_le32_load le32_load_spec /\
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_le64_store le64_store_spec /\
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_le64_load le64_load_spec.
Proof.
  intros _. repeat split.
  - apply haead_small_body_check_failed.
  - apply haead_small_body_bytes_eq.
  - apply haead_small_body_bytes_copy.
  - apply haead_small_body_bytes_set.
  - apply haead_small_body_draw_size.
  - apply haead_small_body_draw_u64.
  - apply haead_small_body_le32_store.
  - apply haead_small_body_le32_load.
  - apply haead_small_body_le64_store.
  - apply haead_small_body_le64_load.
Qed.
