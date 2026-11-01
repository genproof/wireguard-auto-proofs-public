(* The piece of the libc and the small shared buffer functions:
   memcpy, memset, memcmp (quickproof/libc/libc.c), calloc, the shim's __crypto_memneq and the inline
   crypto_memneq of crypto/utils.h (identical Clight in noise, cookie, chacha20poly1305, curve25519: the
   copy of curve25519.c is proved).  memmove is never called (vacuous at assembly).
   The specifications are those of src/proof/libc/spec.v and src/proof/prims/prim_api.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import QuickProof.Env.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.prims.prim_api.

Definition libc_imports (CSw: compspecs) (cs: compspecs) : funspecs :=
  [(_quickproof_malloc, @malloc_spec' CSw)].

(* calloc hands out malloc tokens: stated at the world's compspecs CSw *)
Definition libc_G (CSw: compspecs) : funspecs :=
  [@memcpy_spec Libc.CS; @memset_spec Libc.CS; @memcmp_spec Libc.CS; @calloc_spec CSw;
   @__crypto_memneq_spec Shim.CS; @crypto_memneq_spec Curve25519.CS].

Require Import VST.floyd.VSU.
Require Import WgNoise.proof.libc.libc_bytes.

Lemma is_int_Vubyte: forall b, is_int I8 Unsigned (Vubyte b).
Proof.
  intros. unfold Vubyte; simpl. pose proof (Byte.unsigned_range_2 b).
  rewrite Int.unsigned_repr by rep_lia. rep_lia.
Qed.

Lemma zero_ext_8_Vubyte: forall c,
  Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.repr c))) = Vubyte (Byte.repr c).
Proof.
  intros. unfold Vubyte. f_equal. rewrite Int.zero_ext_idem by lia.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 _)).
  rewrite Int.zero_ext_mod by (cbv; intuition congruence).
  rewrite Int.unsigned_repr_eq, Byte.unsigned_repr_eq. f_equal.
  change (two_p 8) with 256. change Int.modulus with (256 * 16777216). change Byte.modulus with 256.
  rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z_mod_plus_full, Z.mod_mod by lia. reflexivity.
Qed.

Lemma memcmp_Z_app: forall l a b, memcmp_Z (l ++ a) (l ++ b) = memcmp_Z a b.
Proof.
  induction l; intros; simpl; auto. destruct (Byte.eq_dec a a); [auto | congruence].
Qed.

Lemma memcmp_Z_refl: forall a, memcmp_Z a a = 0.
Proof.
  induction a; simpl; auto. destruct (Byte.eq_dec a a); [auto | congruence].
Qed.

Lemma memcmp_Z_diff: forall i a b,
  0 <= i < Zlength a -> 0 <= i < Zlength b -> sublist 0 i a = sublist 0 i b -> Znth i a <> Znth i b ->
  memcmp_Z a b = Byte.unsigned (Znth i a) - Byte.unsigned (Znth i b).
Proof.
  intros.
  rewrite <- (sublist_same 0 (Zlength a) a), (sublist_split 0 i (Zlength a)),
    (sublist_next i (Zlength a)) by lia.
  rewrite <- (sublist_same 0 (Zlength b) b), (sublist_split 0 i (Zlength b)),
    (sublist_next i (Zlength b)) by lia.
  rewrite H1, memcmp_Z_app. simpl. destruct (Byte.eq_dec (Znth i a) (Znth i b)); [contradiction | auto].
  rewrite !Znth_app2 by list_solve. rewrite !Zlength_sublist by lia.
  replace (i - (i - 0)) with 0 by lia. rewrite !Znth_0_cons. auto.
Qed.

Section LibcBodies.
Variable CSw: compspecs.
#[local] Existing Instance Libc.CS.

Lemma body_memcpy:
  semax_body (QPvarspecs Libc.qp) (libc_imports CSw Libc.CS ++ libc_G CSw)
    WgNoise.libc.code.f_memcpy (@memcpy_spec Libc.CS).
Proof.
  start_function.
  forward. forward.
  forward_for_simple_bound n (EX i:Z,
    PROP ()
    LOCAL (temp WgNoise.libc.code._d dst; temp WgNoise.libc.code._s src;
           temp WgNoise.libc.code._dest dst; temp WgNoise.libc.code._n (Vlong (Int64.repr n)))
    SEP (data_at dsh (tarray tuchar n) (map Vubyte (sublist 0 i bs) ++ Zrepeat Vundef (n - i)) dst;
         data_at ssh (tarray tuchar n) (map Vubyte bs) src)).
  - entailer!. simpl app. apply derives_refl.
  - forward.
    { entailer!. apply is_int_Vubyte. }
    forward. entailer!. apply derives_refl'. f_equal. list_solve.
  - forward. entailer!. apply derives_refl'. f_equal. list_solve.
Qed.

Lemma body_memset:
  semax_body (QPvarspecs Libc.qp) (libc_imports CSw Libc.CS ++ libc_G CSw)
    WgNoise.libc.code.f_memset (@memset_spec Libc.CS).
Proof.
  start_function.
  forward.
  forward_for_simple_bound n (EX i:Z,
    PROP ()
    LOCAL (temp WgNoise.libc.code._p p; temp WgNoise.libc.code._s p;
           temp WgNoise.libc.code._c (Vint (Int.repr c)); temp WgNoise.libc.code._n (Vlong (Int64.repr n)))
    SEP (data_at sh (tarray tuchar n) (Zrepeat (Vubyte (Byte.repr c)) i ++ Zrepeat Vundef (n - i)) p)).
  - entailer!. simpl app. apply derives_refl.
  - forward. entailer!. apply derives_refl'. f_equal.
    rewrite zero_ext_8_Vubyte. list_solve.
  - forward. entailer!. apply derives_refl'. f_equal. list_solve.
Qed.

Lemma body_memcmp:
  semax_body (QPvarspecs Libc.qp) (libc_imports CSw Libc.CS ++ libc_G CSw)
    WgNoise.libc.code.f_memcmp (@memcmp_spec Libc.CS).
Proof.
  start_function.
  forward. forward.
  forward_for_simple_bound n (EX i:Z,
    PROP (sublist 0 i a = sublist 0 i b)
    LOCAL (temp WgNoise.libc.code._a p1; temp WgNoise.libc.code._b p2;
           temp WgNoise.libc.code._n (Vlong (Int64.repr n)))
    SEP (data_at sh1 (tarray tuchar n) (map Vubyte a) p1; data_at sh2 (tarray tuchar n) (map Vubyte b) p2)).
  - entailer!.
  - cbv beta. Intros.
    forward.
    { entailer!. apply is_int_Vubyte. }
    forward.
    { entailer!. apply is_int_Vubyte. }
    rewrite !Znth_map by lia.
    forward_if (PROP (Znth i a = Znth i b)
      LOCAL (temp WgNoise.libc.code._i (Vlong (Int64.repr i));
             temp WgNoise.libc.code._a p1; temp WgNoise.libc.code._b p2;
             temp WgNoise.libc.code._n (Vlong (Int64.repr n)))
      SEP (data_at sh1 (tarray tuchar n) (map Vubyte a) p1;
           data_at sh2 (tarray tuchar n) (map Vubyte b) p2)).
    + forward. forward. rewrite !Znth_map by lia. forward. entailer!.
      rewrite (memcmp_Z_diff i) by (try lia; auto; congruence). unfold Vubyte. simpl. f_equal.
      apply sub_repr.
    + forward. entailer!.
      rewrite <- (Byte.repr_unsigned (Znth i a)), <- (Byte.repr_unsigned (Znth i b)), H4. auto.
    + Intros. entailer!.
      rewrite (sublist_split 0 i (i+1) a), (sublist_split 0 i (i+1) b), !sublist_len_1 by lia. congruence.
  - forward. entailer!. rewrite !sublist_same in H2 by lia. subst. rewrite memcmp_Z_refl. auto.
Qed.

Lemma body_calloc:
  semax_body (QPvarspecs Libc.qp) (libc_imports CSw Libc.CS ++ libc_G CSw)
    WgNoise.libc.code.f_calloc (@calloc_spec CSw).
Proof.
  start_function.
  forward_if (PROP ()
    LOCAL (temp WgNoise.libc.code._t'1
             (Val.of_bool (negb (Z.eqb size 0) && (Int64.max_unsigned / size <? nmemb)));
           temp WgNoise.libc.code._nmemb (Vlong (Int64.repr nmemb));
           temp WgNoise.libc.code._size (Vlong (Int64.repr size)); gvars gv)
    SEP (mem_mgr gv)).
  - forward. entailer!.
    assert (size <> 0) by (intro; subst; auto). rewrite (proj2 (Z.eqb_neq _ _)) by auto.
    simpl negb. cbv iota. unfold Int64.cmpu, Int64.divu.
    change (Int64.unsigned (Int64.repr (-1))) with Int64.max_unsigned.
    rewrite (Int64.unsigned_repr size) by rep_lia.
    assert (0 <= Int64.max_unsigned / size <= Int64.max_unsigned)
      by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; rep_lia || nia).
    unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
    destruct (zlt _ _), (_ <? _) eqn:?; auto; lia.
  - forward. entailer!.
    assert (size = 0) by (apply repr_inj_unsigned64; auto; rep_lia). subst. reflexivity.
  - remember (andb (negb (size =? 0)) (Int64.max_unsigned / size <? nmemb)) as ovf eqn:Hovf.
    destruct ovf.
    { forward_if (PROP (False) LOCAL () SEP ()).
      + forward. Exists nullval. entailer!.
      + inv H1. }
    forward_if (PROP (size = 0 \/ nmemb <= Int64.max_unsigned / size)
      LOCAL (temp WgNoise.libc.code._nmemb (Vlong (Int64.repr nmemb));
             temp WgNoise.libc.code._size (Vlong (Int64.repr size)); gvars gv)
      SEP (mem_mgr gv)).
    + contradiction.
    + forward. entailer!.
    + Intros.
      assert (Htot: 0 <= nmemb * size <= Int64.max_unsigned).
      { split; [apply Z.mul_nonneg_nonneg; lia |]. destruct (Z.eq_dec size 0); [subst; rep_lia |].
        destruct H1; [lia |].
        assert (0 < size) by lia.
        pose proof (Z.mul_div_le Int64.max_unsigned size ltac:(lia)).
        pose proof (Z.mul_le_mono_nonneg_r nmemb (Int64.max_unsigned / size) size ltac:(lia) H1).
        lia. }
      forward.
      rewrite mul64_repr.
      forward_call (tarray tuchar (nmemb * size), gv).
      { simpl sizeof. rep_lia. }
      Intros p.
      destruct (eq_dec p nullval).
      * subst p.
        forward_if (PROP ()
          LOCAL (temp WgNoise.libc.code._p nullval)
          SEP (mem_mgr gv)).
        { first [contradiction | discriminate | congruence]. }
        { forward. entailer!. }
        forward. Exists nullval. entailer!.
      * rewrite (@data_at__tarray_tuchar_cs CSw Libc.CS).
        forward_if (PROP ()
          LOCAL (temp WgNoise.libc.code._p p)
          SEP (mem_mgr gv; @malloc_token CSw Ews (tarray tuchar (nmemb * size)) p;
               data_at Ews (tarray tuchar (nmemb * size)) (Zrepeat (Vubyte Byte.zero) (nmemb * size)) p)).
        { apply denote_tc_test_eq_split. 2: auto with valid_pointer.
          destruct (zlt 0 (nmemb * size)).
          - apply sepcon_valid_pointer2. apply data_at_valid_ptr; auto. simpl sizeof. rep_lia.
          - apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
            apply malloc_token_valid_pointer. simpl sizeof. rep_lia. }
        { forward_for_simple_bound (nmemb * size) (EX i:Z,
            PROP ()
            LOCAL (temp WgNoise.libc.code._p p;
                   temp WgNoise.libc.code._total (Vlong (Int64.repr (nmemb * size))))
            SEP (mem_mgr gv; @malloc_token CSw Ews (tarray tuchar (nmemb * size)) p;
                 data_at Ews (tarray tuchar (nmemb * size))
                   (Zrepeat (Vubyte Byte.zero) i ++ Zrepeat Vundef (nmemb * size - i)) p)).
          - entailer!. simpl app. apply derives_refl.
          - forward. entailer!. apply derives_refl'. f_equal. list_solve.
          - entailer!. apply derives_refl'. f_equal. list_solve. }
        { first [contradiction | discriminate | congruence]. }
        forward. Exists p. entailer!.
        rewrite if_false by auto. rewrite (@data_at_tarray_tuchar_cs CSw Libc.CS). cancel.
Qed.

End LibcBodies.

Lemma lxor_byte_range: forall a b, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lxor a b < 256.
Proof.
  intros. split; [apply Z.lxor_nonneg; lia |].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [E|E]; [rewrite E; lia |].
  assert (0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
  change 256 with (2 ^ 8). apply Z.log2_lt_pow2; [lia |].
  eapply Z.le_lt_trans; [apply Z.log2_lxor; lia |].
  apply Z.max_lub_lt.
  - destruct (Z.eq_dec a 0); [subst; simpl; lia |]. apply Z.log2_lt_pow2; lia.
  - destruct (Z.eq_dec b 0); [subst; simpl; lia |]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma lor_byte_range: forall a b, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
  intros. split; [apply Z.lor_nonneg; lia |].
  destruct (Z.eq_dec (Z.lor a b) 0) as [E|E]; [rewrite E; lia |].
  assert (0 <= Z.lor a b) by (apply Z.lor_nonneg; lia).
  change 256 with (2 ^ 8). apply Z.log2_lt_pow2; [lia |].
  rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt.
  - destruct (Z.eq_dec a 0); [subst; simpl; lia |]. apply Z.log2_lt_pow2; lia.
  - destruct (Z.eq_dec b 0); [subst; simpl; lia |]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma memneq_Z_range: forall a b, 0 <= memneq_Z a b < 256.
Proof.
  induction a; destruct b; simpl; try lia.
  apply lor_byte_range; auto. apply lxor_byte_range; rep_lia.
Qed.

Lemma memneq_Z_app: forall l1 l2 a b, Zlength l1 = Zlength l2 ->
  memneq_Z (l1 ++ a) (l2 ++ b) = Z.lor (memneq_Z l1 l2) (memneq_Z a b).
Proof.
  induction l1; destruct l2; intros; simpl; auto.
  - rewrite Zlength_nil, Zlength_cons in H. rep_lia.
  - rewrite Zlength_nil, Zlength_cons in H. rep_lia.
  - rewrite !Zlength_cons in H. rewrite IHl1 by lia. apply Z.lor_assoc.
Qed.

Lemma memneq_Z_snoc: forall i a b, 0 <= i < Zlength a -> 0 <= i < Zlength b ->
  memneq_Z (sublist 0 (i + 1) a) (sublist 0 (i + 1) b) =
  Z.lor (memneq_Z (sublist 0 i a) (sublist 0 i b))
        (Z.lxor (Byte.unsigned (Znth i a)) (Byte.unsigned (Znth i b))).
Proof.
  intros. rewrite (sublist_split 0 i (i + 1) a), (sublist_split 0 i (i + 1) b), !sublist_len_1 by lia.
  rewrite memneq_Z_app by list_solve. simpl. rewrite Z.lor_0_r. auto.
Qed.

Section ShimBodies.
Variable CSw: compspecs.
#[local] Existing Instance Shim.CS.

Lemma body___crypto_memneq:
  semax_body (QPvarspecs Shim.qp) (libc_imports CSw Shim.CS ++ libc_G CSw)
    WgNoise.shim.code.f___crypto_memneq (@__crypto_memneq_spec Shim.CS).
Proof.
  start_function.
  forward. forward. forward.
  forward_for_simple_bound n (EX i:Z,
    PROP ()
    LOCAL (temp WgNoise.shim.code._x p1; temp WgNoise.shim.code._y p2;
           temp WgNoise.shim.code._neq (Vlong (Int64.repr (memneq_Z (sublist 0 i a) (sublist 0 i b))));
           temp WgNoise.shim.code._size (Vlong (Int64.repr n)))
    SEP (data_at sh1 (tarray tuchar n) (map Vubyte a) p1; data_at sh2 (tarray tuchar n) (map Vubyte b) p2)).
  - entailer!.
  - forward.
    { entailer!. apply is_int_Vubyte. }
    forward.
    { entailer!. apply is_int_Vubyte. }
    rewrite !Znth_map by lia.
    forward.
    entailer!.
    rewrite memneq_Z_snoc by lia. do 3 f_equal. unfold Int.xor. rewrite !Int.unsigned_repr by rep_lia.
    pose proof (lxor_byte_range (Byte.unsigned (Znth i a)) (Byte.unsigned (Znth i b))
                  ltac:(rep_lia) ltac:(rep_lia)).
    rewrite Int.signed_repr by rep_lia. auto.
  - forward. entailer!. rewrite !sublist_same by lia. auto.
Qed.

End ShimBodies.

Lemma memneq_Z_zero: forall a b, Zlength a = Zlength b -> (memneq_Z a b = 0 <-> a = b).
Proof.
  induction a; destruct b; intros; simpl.
  - tauto.
  - rewrite Zlength_nil, Zlength_cons in H. rep_lia.
  - rewrite Zlength_nil, Zlength_cons in H. rep_lia.
  - rewrite !Zlength_cons in H. rewrite Z.lor_eq_0_iff, Z.lxor_eq_0_iff, IHa by lia.
    split.
    + intros [E1 ->]. f_equal. rewrite <- (Byte.repr_unsigned a), <- (Byte.repr_unsigned i), E1. auto.
    + intros E. inv E. auto.
Qed.

Section Curve25519Bodies.
Variable CSw: compspecs.
#[local] Existing Instance Curve25519.CS.

Lemma body_crypto_memneq:
  semax_body (QPvarspecs Curve25519.qp) (libc_imports CSw Curve25519.CS ++ libc_G CSw)
    WgNoise.curve25519.code.f_crypto_memneq (@crypto_memneq_spec Curve25519.CS).
Proof.
  start_function.
  rewrite (@data_at_tarray_tuchar_cs Curve25519.CS Shim.CS sh1), (@data_at_tarray_tuchar_cs Curve25519.CS Shim.CS sh2).
  forward_call (sh1, sh2, p1, p2, n, a, b).
  rewrite (@data_at_tarray_tuchar_cs Shim.CS Curve25519.CS sh1), (@data_at_tarray_tuchar_cs Shim.CS Curve25519.CS sh2).
  pose proof (memneq_Z_range a b).
  pose proof (memneq_Z_zero a b ltac:(lia)).
  forward_if (PROP ()
    LOCAL (temp WgNoise.curve25519.code._t'2 (Vint (if memneq_bool a b then Int.one else Int.zero)))
    SEP (data_at sh1 (tarray tuchar n) (map Vubyte a) p1; data_at sh2 (tarray tuchar n) (map Vubyte b) p2)).
  - forward. entailer!. unfold memneq_bool.
    destruct (list_eq_dec Byte.eq_dec a b) as [E|E]; auto.
    exfalso. apply H4. rewrite (proj2 H3 E). auto.
  - forward. entailer!.
    assert (memneq_Z a b = 0) by (apply repr_inj_unsigned64; auto; rep_lia).
    unfold memneq_bool. destruct (list_eq_dec Byte.eq_dec a b) as [E|E]; auto.
    exfalso. apply E, H3. auto.
  - forward.
Qed.

End Curve25519Bodies.

Theorem libc_piece : forall CSw: compspecs,
  piece_ok [u_libc; u_shim; u_curve25519] (libc_imports CSw) (libc_G CSw).
Proof.
  intros. split.
  - apply compute_list_norepet_e. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil.
    + exists u_libc. split; [simpl; auto |].
      exists WgNoise.libc.code.f_memcpy. split; [reflexivity | apply body_memcpy].
    + exists u_libc. split; [simpl; auto |].
      exists WgNoise.libc.code.f_memset. split; [reflexivity | apply body_memset].
    + exists u_libc. split; [simpl; auto |].
      exists WgNoise.libc.code.f_memcmp. split; [reflexivity | apply body_memcmp].
    + exists u_libc. split; [simpl; auto |].
      exists WgNoise.libc.code.f_calloc. split; [reflexivity | apply body_calloc].
    + exists u_shim. split; [simpl; auto |].
      exists WgNoise.shim.code.f___crypto_memneq. split; [reflexivity | apply body___crypto_memneq].
    + exists u_curve25519. split; [simpl; auto |].
      exists WgNoise.curve25519.code.f_crypto_memneq. split; [reflexivity | apply body_crypto_memneq].
Qed.
