(* body proof of the small functions, against aead_spec3.aead_G3. *)
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

Local Open Scope Z_scope.

Lemma as3_xor_byte (x y: byte) :
  Int.zero_ext 8 (Int.xor (Int.repr (Byte.unsigned x)) (Int.repr (Byte.unsigned y))) =
  Int.repr (Byte.unsigned (Byte.xor x y)).
Proof.
  apply Int.same_bits_eq; intros j Hj.
  rewrite Int.bits_zero_ext by lia. rewrite !Int.testbit_repr by lia.
  change (Z.testbit (Byte.unsigned (Byte.xor x y)) j) with (Byte.testbit (Byte.xor x y) j).
  destruct (zlt j 8).
  - rewrite Int.bits_xor by lia. rewrite !Int.testbit_repr by lia.
    rewrite Byte.bits_xor by (change Byte.zwordsize with 8; lia). reflexivity.
  - rewrite Byte.bits_above by (change Byte.zwordsize with 8; lia). reflexivity.
Qed.

Lemma as3_xor_app (a1 a2 b1 b2: list byte) :
  length a1 = length b1 -> xor_bytes (a1 ++ a2) (b1 ++ b2) = xor_bytes a1 b1 ++ xor_bytes a2 b2.
Proof.
  revert b1; induction a1; intros [|y b1] Hl; simpl in *; try discriminate; auto.
  unfold xor_bytes in *. simpl. f_equal. apply IHa1. lia.
Qed.

Lemma as3_Zlength_xor_sub (a b: list byte) i :
  0 <= i <= Zlength a -> Zlength a = Zlength b -> Zlength (xor_bytes (sublist 0 i a) (sublist 0 i b)) = i.
Proof.
  intros H1 H2. unfold xor_bytes. rewrite Zlength_map, !Zlength_correct, combine_length.
  rewrite Nat2Z.inj_min, <- !Zlength_correct, !Zlength_sublist by lia. lia.
Qed.

Lemma as3_upd_prefix (l: list val) v k :
  0 < k -> upd_Znth (Zlength l) (l ++ Zrepeat Vundef k) v = (l ++ [v]) ++ Zrepeat Vundef (k - 1).
Proof.
  intros Hk. rewrite upd_Znth_app2 by (rewrite Zlength_Zrepeat; lia). rewrite Z.sub_diag.
  replace (Zrepeat Vundef k) with (Vundef :: Zrepeat Vundef (k - 1)).
  - rewrite upd_Znth0. rewrite <- app_assoc. reflexivity.
  - unfold Zrepeat. replace (Z.to_nat k) with (S (Z.to_nat (k - 1))) by lia. reflexivity.
Qed.

Lemma as3_xor_step (a b: list byte) i :
  0 <= i < Zlength a -> Zlength a = Zlength b ->
  upd_Znth i (map Vubyte (xor_bytes (sublist 0 i a) (sublist 0 i b)) ++ Zrepeat Vundef (Zlength a - i))
    (Vint (Int.zero_ext 8 (Int.xor (Int.repr (Byte.unsigned (Znth i a))) (Int.repr (Byte.unsigned (Znth i b)))))) =
  map Vubyte (xor_bytes (sublist 0 (i + 1) a) (sublist 0 (i + 1) b)) ++ Zrepeat Vundef (Zlength a - (i + 1)).
Proof.
  intros H1 H2. rewrite as3_xor_byte.
  pose proof (as3_upd_prefix (map Vubyte (xor_bytes (sublist 0 i a) (sublist 0 i b)))
                (Vubyte (Byte.xor (Znth i a) (Znth i b))) (Zlength a - i) ltac:(lia)) as E.
  rewrite Zlength_map, as3_Zlength_xor_sub in E by lia.
  change (Vint (Int.repr (Byte.unsigned (Byte.xor (Znth i a) (Znth i b))))) with (Vubyte (Byte.xor (Znth i a) (Znth i b))).
  rewrite E.
  rewrite (sublist_split 0 i (i + 1) a) by lia. rewrite (sublist_split 0 i (i + 1) b) by lia.
  rewrite !sublist_len_1 by lia. rewrite as3_xor_app.
  - rewrite map_app. f_equal. f_equal. lia.
  - rewrite <- !ZtoNat_Zlength, !Zlength_sublist by lia. reflexivity.
Qed.

Section ShimBodies.
#[local] Existing Instance Shim.CS.

Lemma body___crypto_xor3 :
  @semax_body (QPvarspecs Shim.qp) (aead_imports3 Shim.CS ++ aead_G3) Shim.CS
    WgNoise.shim.code.f___crypto_xor __crypto_xor_spec.
Proof.
  start_function.
  forward_for_simple_bound (Zlength a)
    (EX i: Z,
      PROP ()
      LOCAL (temp WgNoise.shim.code._dst dst; temp WgNoise.shim.code._src1 p1;
             temp WgNoise.shim.code._src2 p2; temp WgNoise.shim.code._len (Vint (Int.repr (Zlength a))))
      SEP (data_at dsh (tarray tuchar (Zlength a))
             (map Vubyte (xor_bytes (sublist 0 i a) (sublist 0 i b)) ++ Zrepeat Vundef (Zlength a - i)) dst;
           data_at sh1 (tarray tuchar (Zlength a)) (map Vubyte a) p1;
           data_at sh2 (tarray tuchar (Zlength a)) (map Vubyte b) p2)).
  - entailer!. rewrite data_at__eq. apply derives_refl.
  - forward. { entailer!. pose proof (Byte.unsigned_range_2 (Znth i a)). simpl. rewrite Int.unsigned_repr; rep_lia. }
    forward. { entailer!. rewrite ?Znth_map by lia. pose proof (Byte.unsigned_range_2 (Znth i b)). simpl. rewrite Int.unsigned_repr; rep_lia. }
    rewrite !Znth_map by lia.
    forward.
    entailer!. rewrite as3_xor_step by lia. apply derives_refl.
  - rewrite Z.sub_diag, Zrepeat_0, app_nil_r.
    rewrite (sublist_same 0 (Zlength a) a) by lia. rewrite (sublist_same 0 (Zlength a) b) by lia.
    entailer!.
Qed.

End ShimBodies.

Section ChachaBodies.
#[local] Existing Instance Chacha.CS.

Lemma body_crypto_xor_cpy3 :
  @semax_body (QPvarspecs Chacha.qp) (aead_imports3 Chacha.CS ++ aead_G3) Chacha.CS
    WgNoise.chacha.code.f_crypto_xor_cpy crypto_xor_cpy_spec.
Proof.
  start_function.
  forward_call (dsh, dst, sh1, p1, a, sh2, p2, b).
  { rewrite !(@aead_data_at_tuchar_cs Chacha.CS Shim.CS), (@aead_data_at__tuchar_cs Chacha.CS Shim.CS). cancel. }
  entailer!. rewrite !(@aead_data_at_tuchar_cs Shim.CS Chacha.CS). cancel.
Qed.

End ChachaBodies.

Lemma as3_rol (w: int) s : 0 <= s < 32 ->
  Int.or (Int.shl w (Int.repr (Z.land s 31))) (Int.shru w (Int.repr (Z.land (- s) 31))) = Int.rol w (Int.repr s).
Proof.
  intros Hs. change 31 with (Z.ones 5). rewrite !Z.land_ones by lia. change (2 ^ 5) with 32.
  destruct (Z.eq_dec s 0) as [-> | Hs0].
  - change (0 mod 32) with 0. change (- 0 mod 32) with 0.
    rewrite Int.shl_zero, Int.shru_zero, Int.or_idem, Int.rol_zero. reflexivity.
  - rewrite Z.mod_small by lia.
    replace (- s mod 32) with (32 - s) by (rewrite <- (Z_mod_plus_full (- s) 1 32); rewrite Z.mod_small; lia).
    apply Int.same_bits_eq; intros j Hj. change Int.zwordsize with 32 in *.
    rewrite Int.bits_or, Int.bits_shl, Int.bits_shru, Int.bits_rol by (change Int.zwordsize with 32; lia).
    change Int.zwordsize with 32.
    rewrite !Int.unsigned_repr by rep_lia.
    destruct (zlt j s).
    + rewrite zlt_true by lia. simpl. f_equal.
      rewrite <- (Z_mod_plus_full (j - s) 1 32). rewrite Z.mod_small; lia.
    + rewrite zlt_false by lia. rewrite orb_false_r. f_equal. rewrite Z.mod_small; lia.
Qed.

Lemma as3_split3 {cs: compspecs} sh n i j (v: list val) p :
  0 <= i -> 0 <= j -> i + j <= n -> Zlength v = n -> field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) v p =
  (data_at sh (tarray tuchar i) (sublist 0 i v) p *
   data_at sh (tarray tuchar j) (sublist i (i + j) v) (offset_val i p) *
   data_at sh (tarray tuchar (n - (i + j))) (sublist (i + j) n v) (offset_val (i + j) p))%logic.
Proof.
  intros. unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh n i (i + j)) by lia.
  fold (tarray tuchar n). rewrite !arr_field_address0 by (auto; lia).
  change (sizeof tuchar) with 1. rewrite !Z.mul_1_l. replace (i + j - i) with j by lia. reflexivity.
Qed.

Lemma as3_byte_of (x: int) : Vint (Int.zero_ext 8 x) = Vubyte (Byte.repr (Int.unsigned x)).
Proof.
  unfold Vubyte. f_equal. rewrite <- (Int.repr_unsigned (Int.zero_ext 8 x)).
  rewrite Int.zero_ext_mod by (cbn; lia). rewrite Byte.unsigned_repr_eq. reflexivity.
Qed.

Lemma as3_shru_unsigned (v: int) k : 0 <= k < 32 ->
  Int.unsigned (Int.shru v (Int.repr k)) = Z.shiftr (Int.unsigned v) k.
Proof.
  intros Hk. unfold Int.shru. rewrite (Int.unsigned_repr k) by rep_lia.
  pose proof (Int.unsigned_range_2 v).
  rewrite Z.shiftr_div_pow2 by lia.
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (Int.unsigned v / 2 ^ k <= Int.unsigned v) by (apply Z.div_le_upper_bound; nia).
  assert (0 <= Int.unsigned v / 2 ^ k) by (apply Z.div_pos; lia).
  rewrite Int.unsigned_repr; rep_lia.
Qed.

Lemma as3_upd4 {A} {d: Inhabitant A} (l: list A) a b c e :
  Zlength l = 4 -> upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 l a) b) c) e = [a; b; c; e].
Proof.
  intros Hl. destruct l as [|x0 [|x1 [|x2 [|x3 [|x4 l]]]]];
    try (exfalso; rewrite ?Zlength_cons, ?Zlength_nil in Hl; try pose proof (Zlength_nonneg l); lia).
  reflexivity.
Qed.

Section ChachaBlockBodies.
#[local] Existing Instance ChachaBlock.CS.

Lemma body_rol32_3 :
  @semax_body (QPvarspecs ChachaBlock.qp) (aead_imports3 ChachaBlock.CS ++ aead_G3) ChachaBlock.CS
    WgNoise.chacha_block.code.f_rol32 rol32_spec.
Proof.
  start_function.
  forward.
  - entailer!. change 31 with (Z.ones 5). rewrite !Z.land_ones by lia. change (2 ^ 5) with 32.
    change (Int.unsigned Int.iwordsize) with 32.
    pose proof (Z.mod_pos_bound s 32). pose proof (Z.mod_pos_bound (- s) 32).
    rewrite !Int.unsigned_repr by rep_lia. lia.
  - entailer!. rewrite as3_rol by lia. reflexivity.
Qed.

Lemma body_put_unaligned_le32_3 :
  @semax_body (QPvarspecs ChachaBlock.qp) (aead_imports3 ChachaBlock.CS ++ aead_G3) ChachaBlock.CS
    WgNoise.chacha_block.code.f_put_unaligned_le32 put_unaligned_le32_spec.
Proof.
  start_function.
  assert_PROP (field_compatible (tarray tuchar (Zlength old)) [] p) by entailer!.
  rewrite (as3_split3 sh (Zlength old) i 4 old p) by (auto; lia). Intros.
  forward. forward. forward. forward. forward.
  rewrite !Int.zero_ext_idem by lia. rewrite !as3_byte_of, !as3_shru_unsigned by lia.
  rewrite as3_upd4 by list_solve.
  entailer!.
  rewrite (as3_split3 sh (Zlength old) i 4 _ p) by (auto; list_solve).
  autorewrite with sublist.
  apply sepcon_derives; [apply sepcon_derives; [apply derives_refl | ] | ]; apply derives_refl'; f_equal; list_solve.
Qed.

Lemma body_chacha_zeroize_state3 :
  @semax_body (QPvarspecs ChachaBlock.qp) (aead_imports3 ChachaBlock.CS ++ aead_G3) ChachaBlock.CS
    WgNoise.chacha_block.code.f_chacha_zeroize_state chacha_zeroize_state_spec.
Proof.
  start_function.
  assert_PROP (field_compatible t_chacha_state [] state) as FC by entailer!.
  forward_call (sh, state, 64).
  { rewrite data_at__memory_block, prop_true_andp by auto. change (sizeof t_chacha_state) with 64.
    rewrite memory_block_data_at__tarray_tuchar_eq by rep_lia. cancel. }
  entailer!. sep_apply data_at_data_at_. rewrite <- memory_block_data_at__tarray_tuchar_eq by rep_lia.
  rewrite <- (memory_block_data_at_ sh t_chacha_state state FC). change (sizeof t_chacha_state) with 64. cancel.
Qed.

End ChachaBlockBodies.

Lemma as3_byte_bits a b : (forall j, 0 <= j < 8 -> Z.testbit a j = Z.testbit b j) -> Byte.repr a = Byte.repr b.
Proof.
  intros H. apply Byte.same_bits_eq; intros j Hj. change Byte.zwordsize with 8 in Hj.
  rewrite !Byte.testbit_repr by (change Byte.zwordsize with 8; lia). apply H; lia.
Qed.

Lemma as3_le64 v : 0 <= v -> le64_bytes v = le32_bytes (Int.repr v) ++ le32_bytes (Int.repr (Z.shiftr v 32)).
Proof.
  intros Hv. unfold le64_bytes, le32_bytes. cbn [le_bytes app].
  rewrite !Int.unsigned_repr_eq. change Int.modulus with (2 ^ 32). change 256 with (2 ^ 8).
  repeat (apply (f_equal2 (@cons byte));
    [ apply as3_byte_bits; intros j Hj;
      repeat first [ rewrite Z.shiftr_spec by lia | rewrite Z.div_pow2_bits by lia
                   | rewrite Z.mod_pow2_bits_low by lia ];
      f_equal; lia | ]).
  reflexivity.
Qed.

Lemma as3_loword_shru v : 0 <= v <= Int64.max_unsigned ->
  Int64.loword (Int64.shru (Int64.repr v) (Int64.repr 32)) = Int.repr (Z.shiftr v 32).
Proof.
  intros Hv. unfold Int64.loword, Int64.shru.
  rewrite (Int64.unsigned_repr v), (Int64.unsigned_repr 32) by rep_lia.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (v / 2 ^ 32 <= v) by (apply Z.div_le_upper_bound; lia).
  assert (0 <= v / 2 ^ 32) by (apply Z.div_pos; lia).
  rewrite Int64.unsigned_repr by rep_lia. reflexivity.
Qed.

Section AeadBodies.
#[local] Existing Instance Chacha20poly1305.CS.

(* simpl on Int64.shru' of a symbolic value runs away (check_vl_eq_args of forward_call) *)
Local Arguments Int64.shru : simpl never.
Local Opaque Int64.shru.
Local Arguments le64_bytes : simpl never.
Local Arguments le32_bytes : simpl never.

Lemma body_put_unaligned_le64_3 :
  @semax_body (QPvarspecs Chacha20poly1305.qp) (aead_imports3 Chacha20poly1305.CS ++ aead_G3) Chacha20poly1305.CS
    WgNoise.chacha20poly1305.code.f_put_unaligned_le64 put_unaligned_le64_spec.
Proof.
  start_function.
  assert_PROP (field_compatible (tarray tuchar (Zlength old)) [] p) as FC by entailer!.
  rewrite (as3_split3 sh (Zlength old) i 8 old p) by (auto; lia). Intros.
  assert (Hmid: Zlength (sublist i (i + 8) old) = 8) by list_solve.
  remember (offset_val i p) as q.
  assert (Hq: q = offset_val i p /\ True) by auto. clear Heqq.
  forget (sublist i (i + 8) old) as mid.
  replace (data_at sh (tarray tuchar 8) mid q) with (data_at sh (tarray tuchar (Zlength mid)) mid q)
    by (rewrite Hmid; reflexivity).
  assert_PROP (isptr q) as Pq by entailer!.
  forward_call (Int.repr v, sh, q, 0, mid).
  { entailer!. destruct q; try contradiction. simpl.
    rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. rewrite ?Ptrofs.add_zero. reflexivity. }
  remember (sublist 0 0 mid ++ map Vubyte (le32_bytes (Int.repr v)) ++ sublist (0 + 4) (Zlength mid) mid) as mid1.
  assert (Hl: Zlength mid1 = Zlength mid) by (subst mid1; unfold le32_bytes; list_solve).
  assert (Hm1: mid1 = map Vubyte (le32_bytes (Int.repr v)) ++ sublist 4 8 mid /\ True)
    by (subst mid1; split; auto; rewrite Hmid; list_solve).
  clear Heqmid1. rewrite <- Hl.
  forward_call (Int64.loword (Int64.shru (Int64.repr v) (Int64.repr 32)), sh, q, 4, mid1).
  entailer!.
  destruct Hq as [Hq _]; destruct Hm1 as [Hm1 _]; subst q mid1.
  match goal with |- _ |-- data_at _ _ (?A ++ ?L) _ =>
    replace L with (map Vubyte (le64_bytes v) ++ sublist (i + 8) (Zlength old) old) by reflexivity end.
  rewrite as3_loword_shru by lia. rewrite (as3_le64 v) by lia. rewrite map_app.
  rewrite (as3_split3 sh (Zlength old) i 8 _ p) by (auto; unfold le32_bytes; list_solve).
  unfold le32_bytes.
  autorewrite with sublist.
  replace (Z.succ (Z.succ (Z.succ (Z.succ 0))) + (8 - 4)) with 8 by lia.
  match goal with |- _ |-- _ * data_at _ _ (sublist 0 8 ?M) _ * data_at _ _ (sublist (i + 8) (Zlength old) ?N) _ =>
    replace (sublist 0 8 M) with M by list_solve;
    replace (sublist (i + 8) (Zlength old) N) with (sublist (i + 8) (Zlength old) old) by list_solve end.
  cancel.
Qed.

Lemma body_chacha_init_consts3 :
  @semax_body (QPvarspecs Chacha20poly1305.qp) (aead_imports3 Chacha20poly1305.CS ++ aead_G3) Chacha20poly1305.CS
    WgNoise.chacha20poly1305.code.f_chacha_init_consts chacha_init_consts_spec.
Proof.
  start_function.
  forward. forward. forward. forward.
  entailer!. apply derives_refl'. f_equal. unfold chacha_consts. list_solve.
Qed.

Lemma body_chacha_init3 :
  @semax_body (QPvarspecs Chacha20poly1305.qp) (aead_imports3 Chacha20poly1305.CS ++ aead_G3) Chacha20poly1305.CS
    WgNoise.chacha20poly1305.code.f_chacha_init chacha_init_spec.
Proof.
  start_function.
  rewrite data_at__eq. change (default_val t_chacha_state) with (Zrepeat Vundef 16).
  forward_call (sh, state, Zrepeat Vundef 16).
  forward. forward. forward. forward. forward. forward. forward. forward.
  forward. forward. forward. forward. forward. forward. forward. forward.
  assert_PROP (isptr ivp) as Piv by entailer!. destruct ivp; try contradiction.
  forward_call (ish, Vptr b i, 0, iv).
  forward.
  forward_call (ish, Vptr b i, 4, iv).
  forward.
  forward_call (ish, Vptr b i, 8, iv).
  forward.
  forward_call (ish, Vptr b i, 12, iv).
  forward.
  entailer!. apply derives_refl'. f_equal. unfold chacha_init_st, chacha_consts. list_solve.
Qed.

Lemma body_chacha_load_key3 :
  @semax_body (QPvarspecs Chacha20poly1305.qp) (aead_imports3 Chacha20poly1305.CS ++ aead_G3) Chacha20poly1305.CS
    WgNoise.chacha20poly1305.code.f_chacha_load_key chacha_load_key_spec.
Proof.
  start_function.
  replace (data_at ish (tarray tuchar 32)) with (data_at ish (tarray tuchar (Zlength key))) by (rewrite H; reflexivity).
  assert_PROP (isptr ip) as Pip by entailer!. destruct ip; try contradiction.
  forward_call (ish, Vptr b i, 0, key).
  1: try (entailer!; simpl; rewrite Ptrofs.add_zero; reflexivity).
  forward.
  forward_call (ish, Vptr b i, 4, key).
  forward.
  forward_call (ish, Vptr b i, 8, key).
  forward.
  forward_call (ish, Vptr b i, 12, key).
  forward.
  forward_call (ish, Vptr b i, 16, key).
  forward.
  forward_call (ish, Vptr b i, 20, key).
  forward.
  forward_call (ish, Vptr b i, 24, key).
  forward.
  forward_call (ish, Vptr b i, 28, key).
  forward.
  entailer!.
  rewrite H. apply derives_refl.
Qed.

End AeadBodies.

Theorem aead_small_bodies3 :
  @semax_body (QPvarspecs Shim.qp) (aead_imports3 Shim.CS ++ aead_G3) Shim.CS
    WgNoise.shim.code.f___crypto_xor __crypto_xor_spec /\
  @semax_body (QPvarspecs Chacha.qp) (aead_imports3 Chacha.CS ++ aead_G3) Chacha.CS
    WgNoise.chacha.code.f_crypto_xor_cpy crypto_xor_cpy_spec /\
  @semax_body (QPvarspecs ChachaBlock.qp) (aead_imports3 ChachaBlock.CS ++ aead_G3) ChachaBlock.CS
    WgNoise.chacha_block.code.f_rol32 rol32_spec /\
  @semax_body (QPvarspecs ChachaBlock.qp) (aead_imports3 ChachaBlock.CS ++ aead_G3) ChachaBlock.CS
    WgNoise.chacha_block.code.f_put_unaligned_le32 put_unaligned_le32_spec /\
  @semax_body (QPvarspecs ChachaBlock.qp) (aead_imports3 ChachaBlock.CS ++ aead_G3) ChachaBlock.CS
    WgNoise.chacha_block.code.f_chacha_zeroize_state chacha_zeroize_state_spec /\
  @semax_body (QPvarspecs Chacha20poly1305.qp) (aead_imports3 Chacha20poly1305.CS ++ aead_G3) Chacha20poly1305.CS
    WgNoise.chacha20poly1305.code.f_put_unaligned_le64 put_unaligned_le64_spec /\
  @semax_body (QPvarspecs Chacha20poly1305.qp) (aead_imports3 Chacha20poly1305.CS ++ aead_G3) Chacha20poly1305.CS
    WgNoise.chacha20poly1305.code.f_chacha_init_consts chacha_init_consts_spec /\
  @semax_body (QPvarspecs Chacha20poly1305.qp) (aead_imports3 Chacha20poly1305.CS ++ aead_G3) Chacha20poly1305.CS
    WgNoise.chacha20poly1305.code.f_chacha_init chacha_init_spec /\
  @semax_body (QPvarspecs Chacha20poly1305.qp) (aead_imports3 Chacha20poly1305.CS ++ aead_G3) Chacha20poly1305.CS
    WgNoise.chacha20poly1305.code.f_chacha_load_key chacha_load_key_spec.
Proof.
  exact (conj body___crypto_xor3 (conj body_crypto_xor_cpy3 (conj body_rol32_3 (conj body_put_unaligned_le32_3
          (conj body_chacha_zeroize_state3 (conj body_put_unaligned_le64_3 (conj body_chacha_init_consts3
          (conj body_chacha_init3 body_chacha_load_key3)))))))).
Qed.
