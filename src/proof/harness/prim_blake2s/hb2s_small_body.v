(* bodies of the small common.h functions of law prim_blake2s. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.harness.prim_blake2s.hb2s_spec.
Require WgNoise.harness.x_prim_blake2s.code.

#[local] Existing Instance W_prim_blake2s.
Local Open Scope Z_scope.

Module C := WgNoise.harness.x_prim_blake2s.code.

Lemma hb2s_small_is_int_Vubyte: forall b, is_int I8 Unsigned (Vubyte b).
Proof.
  intros. unfold Vubyte; simpl. pose proof (Byte.unsigned_range_2 b).
  rewrite Int.unsigned_repr by rep_lia. rep_lia.
Qed.

Lemma hb2s_small_body_check_failed :
  semax_body hb2s_V hb2s_Gprog C.f_check_failed check_failed_spec.
Proof.
  start_function. contradiction.
Qed.

Lemma hb2s_small_body_bytes_eq :
  semax_body hb2s_V hb2s_Gprog C.f_bytes_eq bytes_eq_spec.
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
    { entailer!. try rewrite Znth_map by lia; apply hb2s_small_is_int_Vubyte. }
    forward.
    { entailer!. try rewrite Znth_map by lia; apply hb2s_small_is_int_Vubyte. }
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

Lemma hb2s_small_body_bytes_zero :
  semax_body hb2s_V hb2s_Gprog C.f_bytes_zero bytes_zero_spec.
Proof.
  start_function.
  forward_for_simple_bound (Zlength l) (EX i:Z,
    PROP (sublist 0 i l = Zrepeat Byte.zero i)
    LOCAL (temp C._a a; temp C._n (Vlong (Int64.repr (Zlength l))))
    SEP (data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) a)).
  - entailer!.
  - cbv beta. Intros.
    forward.
    { entailer!. try rewrite Znth_map by lia; apply hb2s_small_is_int_Vubyte. }
    rewrite !Znth_map by lia.
    forward_if (PROP (Znth i l = Byte.zero)
      LOCAL (temp C._i (Vlong (Int64.repr i));
             temp C._a a; temp C._n (Vlong (Int64.repr (Zlength l))))
      SEP (data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) a)).
    + forward.
      destruct (list_eq_dec Byte.eq_dec l (Zrepeat Byte.zero (Zlength l))) as [E|]; [|entailer!].
      exfalso. apply H2. rewrite E, Znth_Zrepeat by lia. reflexivity.
    + forward. entailer!.
      rewrite <- (Byte.repr_unsigned (Znth i l)).
      match goal with H: Byte.unsigned _ = _ |- _ => rewrite H end. reflexivity.
    + Intros. entailer!.
      rewrite (sublist_split 0 i (i+1) l), !sublist_len_1, H1, H2 by lia. list_solve.
  - forward.
    match goal with H: sublist 0 _ l = _ |- _ => rewrite !sublist_same in H by lia end.
    destruct (list_eq_dec Byte.eq_dec l (Zrepeat Byte.zero (Zlength l))); [|contradiction].
    entailer!.
Qed.

Lemma hb2s_small_body_bytes_copy :
  semax_body hb2s_V hb2s_Gprog C.f_bytes_copy bytes_copy_spec.
Proof.
  start_function.
  forward_for_simple_bound (Zlength bs) (EX i:Z,
    PROP ()
    LOCAL (temp C._d d; temp C._s s; temp C._n (Vlong (Int64.repr (Zlength bs))))
    SEP (data_at dsh (tarray tuchar (Zlength bs)) (map Vubyte (sublist 0 i bs) ++ Zrepeat Vundef (Zlength bs - i)) d;
         data_at ssh (tarray tuchar (Zlength bs)) (map Vubyte bs) s)).
  - entailer!. simpl app. apply derives_refl.
  - forward.
    { entailer!. try rewrite Znth_map by lia; apply hb2s_small_is_int_Vubyte. }
    forward. entailer!. apply derives_refl'. f_equal. list_solve.
  - entailer!. apply derives_refl'. f_equal. list_solve.
Qed.

Lemma hb2s_small_body_bytes_set :
  semax_body hb2s_V hb2s_Gprog C.f_bytes_set bytes_set_spec.
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

Lemma hb2s_small_body_draw_size :
  semax_body hb2s_V hb2s_Gprog C.f_draw_size draw_size_spec.
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

Lemma hb2s_small_body_le32_load :
  semax_body hb2s_V hb2s_Gprog C.f_le32_load le32_load_spec.
Proof.
  start_function.
  assert_PROP (field_compatible (tarray tuchar (Zlength bs)) [] p) by entailer!.
  rewrite (split2_data_at_Tarray_tuchar sh (Zlength bs) i) by (rewrite ?Zlength_map; lia).
  change (Tarray tuchar (Zlength bs) noattr) with (tarray tuchar (Zlength bs)).
  rewrite arr_field_address0 by (auto; lia). simpl sizeof. rewrite Z.mul_1_l.
  rewrite !sublist_map. Intros.
  forward; [entailer!; try rewrite Znth_map by list_solve; apply hb2s_small_is_int_Vubyte|].
  forward; [entailer!; try rewrite Znth_map by list_solve; apply hb2s_small_is_int_Vubyte|].
  forward; [entailer!; try rewrite Znth_map by list_solve; apply hb2s_small_is_int_Vubyte|].
  forward; [entailer!; try rewrite Znth_map by list_solve; apply hb2s_small_is_int_Vubyte|].
  rewrite !Znth_map by list_solve. rewrite !Znth_sublist by list_solve.
  forward.
  apply andp_right.
  - apply prop_right. unfold le32_at, le32_of, Vubyte. simpl. rewrite !(Z.add_comm _ i). reflexivity.
  - rewrite (split2_data_at_Tarray_tuchar sh (Zlength bs) i) by list_solve.
    change (Tarray tuchar (Zlength bs) noattr) with (tarray tuchar (Zlength bs)).
    rewrite arr_field_address0 by (auto; lia). simpl sizeof. rewrite Z.mul_1_l, !sublist_map. cancel.
Qed.

Lemma hb2s_small_body_rb2s_rotr :
  semax_body hb2s_V hb2s_Gprog C.f_rb2s_rotr rb2s_rotr_spec.
Proof.
  start_function.
  forward.
  { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
  entailer!. f_equal. rewrite Int.or_commut. symmetry. apply Int.or_ror.
  - unfold Int.ltu. rewrite Int.unsigned_repr by rep_lia.
    change (Int.unsigned Int.iwordsize) with 32. destruct (zlt _ _); [reflexivity|lia].
  - unfold Int.ltu. rewrite Int.unsigned_repr by rep_lia.
    change (Int.unsigned Int.iwordsize) with 32. destruct (zlt _ _); [reflexivity|lia].
  - rewrite add_repr. replace (32 - n + n) with 32 by lia. reflexivity.
Qed.

Lemma hb2s_small_bodies :
  semax_body hb2s_V hb2s_Gprog WgNoise.harness.x_prim_blake2s.code.f_check_failed check_failed_spec /\
  semax_body hb2s_V hb2s_Gprog WgNoise.harness.x_prim_blake2s.code.f_bytes_eq bytes_eq_spec /\
  semax_body hb2s_V hb2s_Gprog WgNoise.harness.x_prim_blake2s.code.f_bytes_zero bytes_zero_spec /\
  semax_body hb2s_V hb2s_Gprog WgNoise.harness.x_prim_blake2s.code.f_bytes_copy bytes_copy_spec /\
  semax_body hb2s_V hb2s_Gprog WgNoise.harness.x_prim_blake2s.code.f_bytes_set bytes_set_spec /\
  semax_body hb2s_V hb2s_Gprog WgNoise.harness.x_prim_blake2s.code.f_draw_size draw_size_spec /\
  semax_body hb2s_V hb2s_Gprog WgNoise.harness.x_prim_blake2s.code.f_le32_load le32_load_spec /\
  semax_body hb2s_V hb2s_Gprog WgNoise.harness.x_prim_blake2s.code.f_rb2s_rotr rb2s_rotr_spec.
Proof.
  repeat split.
  - apply hb2s_small_body_check_failed.
  - apply hb2s_small_body_bytes_eq.
  - apply hb2s_small_body_bytes_zero.
  - apply hb2s_small_body_bytes_copy.
  - apply hb2s_small_body_bytes_set.
  - apply hb2s_small_body_draw_size.
  - apply hb2s_small_body_le32_load.
  - apply hb2s_small_body_rb2s_rotr.
Qed.
