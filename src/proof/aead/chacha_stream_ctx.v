(* The bodies of lib/crypto/chacha.c (crypto_xor_cpy, chacha_crypt_generic, chacha_crypt) and of wg_shim.c's
   __crypto_xor, each with a context of its callees only: the same specifications (aead_spec.v, aead_spec3.v) and
   the same proofs as aead_small_body3.v, aead_chacha_body3.v and aead_chacha_crypt3.v, whose context is the whole
   AEAD piece (with the poly1305 and chacha20poly1305.c functions).  A body moves into a per-law program only if
   every function of its context is in the program: these move into every program that links chacha.c,
   chacha-block-generic.c and wg_shim.c. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.chacha.code WgNoise.chacha_block.code WgNoise.shim.code.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.aead.aead_spec3.
Require Import WgNoise.proof.aead.aead_cce.
Require Import WgNoise.proof.aead.aead_bytes.
Require Import WgNoise.proof.aead.aead_small_body3.
Require Import WgNoise.proof.aead.aead_chacha_body.
Require Import WgNoise.proof.aead.aead_long3_model.
Require Import WgNoise.proof.aead.aead_chacha_body3.

Local Open Scope Z_scope.

Section ShimBodiesCtx.
#[local] Existing Instance Shim.CS.

Lemma body___crypto_xor_ctx :
  @semax_body (QPvarspecs Shim.qp) nil Shim.CS WgNoise.shim.code.f___crypto_xor __crypto_xor_spec.
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

End ShimBodiesCtx.

Section ChachaBodiesCtx.
#[local] Existing Instance Chacha.CS.

Lemma body_crypto_xor_cpy_ctx :
  @semax_body (QPvarspecs Chacha.qp) [__crypto_xor_spec] Chacha.CS
    WgNoise.chacha.code.f_crypto_xor_cpy crypto_xor_cpy_spec.
Proof.
  start_function.
  forward_call (dsh, dst, sh1, p1, a, sh2, p2, b).
  { rewrite !(@aead_data_at_tuchar_cs Chacha.CS Shim.CS), (@aead_data_at__tuchar_cs Chacha.CS Shim.CS). cancel. }
  entailer!. rewrite !(@aead_data_at_tuchar_cs Shim.CS Chacha.CS). cancel.
Qed.

Lemma body_chacha_crypt_generic_ctx :
  @semax_body (QPvarspecs Chacha.qp) [chacha_block_generic_spec; crypto_xor_cpy_spec] Chacha.CS
    WgNoise.chacha.code.f_chacha_crypt_generic chacha_crypt_generic_spec3.
Proof.
  start_function.
  pose proof (Zlength_nonneg m) as Hm0.
  set (nn := Z.to_nat (nr / 2)).
  destruct (Z.eq_dec (Zlength m) 0) as [Hz | Hnz].
  { (* empty message: nothing but the tests; the destination is not touched *)
    unfold prim_bytes. rewrite if_true by auto.
    rewrite (cb3_out_z dsh (Zrepeat Vundef (Zlength m)) dst) by (rewrite Zlength_Zrepeat; lia).
    forward_while (@exp (environ -> mpred) _ unit (fun _ =>
      PROP ()
      LOCAL (lvar WgNoise.chacha.code._stream (tarray tuchar 64) v_stream; temp WgNoise.chacha.code._state state;
             temp WgNoise.chacha.code._dst dst; temp WgNoise.chacha.code._src src;
             temp WgNoise.chacha.code._bytes (Vint (Int.repr (Zlength m)));
             temp WgNoise.chacha.code._nrounds (Vint (Int.repr nr)))
      SEP (data_at_ Tsh (tarray tuchar 64) v_stream; data_at ssh t_chacha_state (map Vint st) state))).
    - Exists tt. entailer!.
    - entailer!.
    - lia.
    - forward_if.
      + rewrite Hz in H2. contradiction.
      + forward.
        apply Zlength_nil_inv in Hz; subst m.
        replace (chacha_advance st (chacha_nblocks (Zlength (@nil byte)))) with st
          by (symmetry; apply chc_advance_0; auto).
        replace (chacha_xor (Z.to_nat (nr / 2)) st []) with (@nil byte) by reflexivity.
        unfold prim_bytes. rewrite if_true by reflexivity.
        rewrite (cb3_out_z dsh (map Vubyte []) dst) by reflexivity.
        entailer!. }
  rewrite (cb3_out_nz dsh (Zrepeat Vundef (Zlength m)) dst) by (rewrite Zlength_Zrepeat; lia).
  rewrite Zlength_Zrepeat by lia. rewrite <- data_at__tarray' by auto.
  assert (EO: prim_out dsh (map Vubyte (chacha_xor nn st m)) dst =
              data_at dsh (tarray tuchar (Zlength m)) (map Vubyte (chacha_xor nn st m)) dst).
  { rewrite cb3_out_nz by (rewrite Zlength_map, lg3_Zlength_chacha_xor; auto).
    rewrite Zlength_map, lg3_Zlength_chacha_xor by auto. reflexivity. }
  unfold POSTCONDITION, abbreviate. fold nn. rewrite EO. clear EO. abbreviate_semax.
  assert_PROP (field_compatible (tarray tuchar (Zlength m)) [] dst) as FCd by entailer!.
  unfold prim_bytes. rewrite if_false by auto.
  assert_PROP (field_compatible (tarray tuchar (Zlength m)) [] src) as FCs by entailer!.
  forward_while (@exp (environ -> mpred) _ Z (fun k =>
    PROP (0 <= k; 64 * k <= Zlength m)
    LOCAL (lvar WgNoise.chacha.code._stream (tarray tuchar 64) v_stream; temp WgNoise.chacha.code._state state;
           temp WgNoise.chacha.code._dst (offset_val (64 * k) dst);
           temp WgNoise.chacha.code._src (offset_val (64 * k) src);
           temp WgNoise.chacha.code._bytes (Vint (Int.repr (Zlength m - 64 * k)));
           temp WgNoise.chacha.code._nrounds (Vint (Int.repr nr)))
    SEP (data_at_ Tsh (tarray tuchar 64) v_stream;
         data_at ssh t_chacha_state (map Vint (chacha_advance st k)) state;
         data_at dsh (tarray tuchar (Zlength m))
           (map Vubyte (chc_done nn st m k) ++ Zrepeat Vundef (Zlength m - 64 * k)) dst;
         data_at msh (tarray tuchar (Zlength m)) (map Vubyte m) src))).
  - Exists 0. entailer!.
    rewrite chc_advance_0 by auto. rewrite data_at__tarray, app_nil_l. cancel.
  - entailer!.
  - forward_call (ssh, state, chacha_advance st k, Tsh, v_stream, nr).
    { rewrite chc_Zlength_advance; auto. }
    fold nn.
    assert (Hd: Zlength (chc_done nn st m k) = 64 * k) by (apply chc_Zlength_done; auto).
    rewrite (chc_split3 dsh (Zlength m) (64 * k) 64 _ dst)
      by (auto; try lia; rewrite Zlength_app, Zlength_map, Zlength_Zrepeat, Hd; lia).
    rewrite (chc_split3 msh (Zlength m) (64 * k) 64 _ src) by (auto; try lia; rewrite Zlength_map; lia).
    replace (sublist 0 (64 * k) (map Vubyte (chc_done nn st m k) ++ Zrepeat Vundef (Zlength m - 64 * k)))
      with (map Vubyte (chc_done nn st m k)) by list_solve.
    replace (sublist (64 * k) (64 * k + 64) (map Vubyte (chc_done nn st m k) ++ Zrepeat Vundef (Zlength m - 64 * k)))
      with (Zrepeat Vundef 64) by list_solve.
    replace (sublist (64 * k + 64) (Zlength m) (map Vubyte (chc_done nn st m k) ++ Zrepeat Vundef (Zlength m - 64 * k)))
      with (Zrepeat Vundef (Zlength m - (64 * k + 64))) by list_solve.
    rewrite (sublist_map _ (64 * k) (64 * k + 64)).
    assert (Ha: Zlength (sublist (64 * k) (64 * k + 64) m) = 64) by (rewrite Zlength_sublist; lia).
    forward_call (dsh, offset_val (64 * k) dst, msh, offset_val (64 * k) src, sublist (64 * k) (64 * k + 64) m,
                  Tsh, v_stream, chacha_block_bytes nn (chacha_advance st k)).
    { rewrite Ha. entailer!. }
    { rewrite Ha, data_at__tarray. cancel. }
    { rewrite Ha, chc_Zlength_block_bytes by (rewrite chc_Zlength_advance; auto). auto. }
    rewrite Ha.
    forward. forward. forward.
    Exists (k + 1).
    assert (Hd1: Zlength (chc_done nn st m (k + 1)) = 64 * (k + 1)) by (apply chc_Zlength_done; auto; lia).
    rewrite (chc_split3 dsh (Zlength m) (64 * k) 64
               (map Vubyte (chc_done nn st m (k + 1)) ++ Zrepeat Vundef (Zlength m - 64 * (k + 1))) dst)
      by (auto; try lia; rewrite Zlength_app, Zlength_map, Zlength_Zrepeat, Hd1; lia).
    rewrite (chc_split3 msh (Zlength m) (64 * k) 64 _ src) by (auto; try lia; rewrite Zlength_map; lia).
    rewrite chc_done_step by lia. rewrite chc_advance_advance by auto.
    assert (Hx: Zlength (xor_bytes (sublist (64 * k) (64 * k + 64) m)
                                   (chacha_block_bytes nn (chacha_advance st k))) = 64)
      by (rewrite chc_Zlength_xor, Ha, chc_Zlength_block_bytes by (rewrite chc_Zlength_advance; auto); lia).
    rewrite (sublist_map _ (64 * k) (64 * k + 64)).
    set (X := xor_bytes _ _) in *.
    replace (sublist 0 (64 * k) (map Vubyte (chc_done nn st m k ++ X) ++ Zrepeat Vundef (Zlength m - 64 * (k + 1))))
      with (map Vubyte (chc_done nn st m k)) by list_solve.
    replace (sublist (64 * k) (64 * k + 64) (map Vubyte (chc_done nn st m k ++ X) ++ Zrepeat Vundef (Zlength m - 64 * (k + 1))))
      with (map Vubyte X) by list_solve.
    replace (sublist (64 * k + 64) (Zlength m) (map Vubyte (chc_done nn st m k ++ X) ++ Zrepeat Vundef (Zlength m - 64 * (k + 1))))
      with (Zrepeat Vundef (Zlength m - (64 * k + 64))) by list_solve.
    clearbody X.
    entailer!.
    replace (64 * (k + 1)) with (64 * k + 64) by lia.
    replace (Zlength m - 64 * k - 64) with (Zlength m - (64 * k + 64)) by lia. auto.
  - assert (Hd: Zlength (chc_done nn st m k) = 64 * k) by (apply chc_Zlength_done; auto).
    forward_if.
    + assert (Hr: Zlength m - 64 * k <> 0) by (intros E; rewrite E in H4; contradiction).
      forward_call (ssh, state, chacha_advance st k, Tsh, v_stream, nr).
      { rewrite chc_Zlength_advance; auto. }
      fold nn.
      set (r := Zlength m - 64 * k) in *.
      set (blk := chacha_block_bytes nn (chacha_advance st k)).
      assert (Hblk: Zlength blk = 64) by (apply chc_Zlength_block_bytes; rewrite chc_Zlength_advance; auto).
      rewrite (chc_split3 dsh (Zlength m) (64 * k) r _ dst)
        by (auto; try lia; rewrite Zlength_app, Zlength_map, Zlength_Zrepeat, Hd; lia).
      rewrite (chc_split3 msh (Zlength m) (64 * k) r _ src) by (auto; try lia; rewrite Zlength_map; lia).
      assert_PROP (field_compatible (tarray tuchar 64) [] v_stream) as FCv by entailer!.
      rewrite (chc_split2 Tsh 64 r _ v_stream) by (auto; try lia; rewrite Zlength_map; lia).
      replace (sublist 0 (64 * k) (map Vubyte (chc_done nn st m k) ++ Zrepeat Vundef r))
        with (map Vubyte (chc_done nn st m k)) by list_solve.
      replace (sublist (64 * k) (64 * k + r) (map Vubyte (chc_done nn st m k) ++ Zrepeat Vundef r))
        with (Zrepeat Vundef r) by list_solve.
      rewrite (sublist_map _ (64 * k) (64 * k + r)), (sublist_map _ 0 r).
      assert (Ha: Zlength (sublist (64 * k) (64 * k + r) m) = r) by (rewrite Zlength_sublist; lia).
      forward_call (dsh, offset_val (64 * k) dst, msh, offset_val (64 * k) src, sublist (64 * k) (64 * k + r) m,
                    Tsh, v_stream, sublist 0 r blk).
      { rewrite Ha. entailer!. }
      { rewrite Ha, data_at__tarray. cancel. }
      { rewrite Ha, Zlength_sublist by lia. lia. }
      rewrite Ha.
      forward.
      fold nn. fold blk.
      replace (64 * k + (Zlength m - 64 * k)) with (Zlength m) by lia.
      rewrite (chc_split2_ Tsh 64 (Zlength m - 64 * k) v_stream) by (auto; lia).
      unfold prim_bytes. rewrite if_false by auto.
      rewrite (chc_split3 msh (Zlength m) (64 * k) (Zlength m - 64 * k) (map Vubyte m) src)
        by (auto; try lia; rewrite Zlength_map; lia).
      rewrite <- (chc_done_tail nn st m k) by (auto; lia). fold blk.
      remember (xor_bytes (sublist (64 * k) (Zlength m) m) (sublist 0 (Zlength m - 64 * k) blk)) as Y eqn:HY.
      assert (Hy: Zlength Y = Zlength m - 64 * k)
        by (subst Y; rewrite chc_Zlength_xor, !Zlength_sublist by lia; lia).
      rewrite (chc_split3 dsh (Zlength m) (64 * k) (Zlength m - 64 * k) _ dst)
        by (auto; try lia; rewrite Zlength_map, Zlength_app, Hd, Hy; lia).
      rewrite chc_advance_advance by auto. rewrite (chc_nblocks_tail k (Zlength m)) by lia.
      replace (64 * k + (Zlength m - 64 * k)) with (Zlength m) by lia.
      rewrite !sublist_nil.
      replace (sublist 0 (64 * k) (map Vubyte (chc_done nn st m k ++ Y)))
        with (map Vubyte (chc_done nn st m k)) by list_solve.
      replace (sublist (64 * k) (Zlength m) (map Vubyte (chc_done nn st m k ++ Y)))
        with (map Vubyte Y) by list_solve.
      rewrite (sublist_map _ (64 * k) (Zlength m) m).
      clearbody blk nn.
      sep_apply (data_at_data_at_ Tsh (tarray tuchar (Zlength m - 64 * k))
                   (map Vubyte (sublist 0 (Zlength m - 64 * k) blk)) v_stream).
      sep_apply (data_at_data_at_ Tsh (tarray tuchar (64 - (Zlength m - 64 * k)))
                   (sublist (Zlength m - 64 * k) 64 (map Vubyte blk)) (offset_val (Zlength m - 64 * k) v_stream)).
      cancel.
    + assert (Hr: Int.unsigned (Int.repr (Zlength m - 64 * k)) = 0) by (rewrite H4; reflexivity).
      rewrite Int.unsigned_repr in Hr by rep_lia.
      forward.
      replace (Zlength m - 64 * k) with 0 by lia.
      change (Zrepeat Vundef 0) with (@nil val). rewrite app_nil_r.
      rewrite chc_done_full by lia.
      replace (chacha_nblocks (Zlength m)) with k by (replace (Zlength m) with (64 * k) by lia;
                                                        symmetry; apply chc_nblocks_full; lia).
      fold nn. entailer!.
      unfold prim_bytes. rewrite if_false by auto. auto.
Qed.

Lemma body_chacha_crypt_ctx :
  @semax_body (QPvarspecs Chacha.qp) [chacha_crypt_generic_spec3] Chacha.CS
    WgNoise.chacha.code.f_chacha_crypt chacha_crypt_spec3.
Proof.
  start_function.
  pose proof (Zlength_nonneg m) as Hm0.
  set (nn := Z.to_nat (nr / 2)).
  destruct (Z.eq_dec (Zlength m) 0) as [Hz | Hnz].
  { (* empty: the loop test fails at once; chacha_crypt_generic(state, dst, src, 0, nrounds) *)
    forward_while (@exp (environ -> mpred) _ unit (fun _ =>
      PROP ()
      LOCAL (temp WgNoise.chacha.code._state state; temp WgNoise.chacha.code._dst dst;
             temp WgNoise.chacha.code._src src;
             temp WgNoise.chacha.code._bytes (Vlong (Int64.repr (Zlength m)));
             temp WgNoise.chacha.code._nrounds (Vint (Int.repr nr)))
      SEP (data_at ssh t_chacha_state (map Vint st) state; prim_out dsh (Zrepeat Vundef (Zlength m)) dst;
           prim_bytes msh m src))).
    - Exists tt. entailer!.
    - entailer!.
    - rewrite Hz in HRE. pose proof (Int.unsigned_range (Int.not (Int.repr 0))). lia.
    - forward_call (ssh, state, st, dsh, dst, msh, src, m, nr).
      { rewrite Hz. go_lower. apply prop_right. reflexivity. }
      entailer!. }
  unfold prim_bytes. rewrite if_false by auto.
  rewrite (cb3_out_nz dsh (Zrepeat Vundef (Zlength m)) dst) by (rewrite Zlength_Zrepeat; lia).
  rewrite Zlength_Zrepeat by lia.
  assert_PROP (field_compatible (tarray tuchar (Zlength m)) [] dst) as FCd by entailer!.
  assert_PROP (field_compatible (tarray tuchar (Zlength m)) [] src) as FCs by entailer!.
  pose proof (proj1 FCd) as Pd. pose proof (proj1 FCs) as Ps.
  set (n := Zlength m) in *.
  forward_while (@exp (environ -> mpred) _ Z (fun k =>
    PROP (0 <= k < n; k mod 64 = 0)
    LOCAL (temp WgNoise.chacha.code._state state;
           temp WgNoise.chacha.code._dst (offset_val k dst); temp WgNoise.chacha.code._src (offset_val k src);
           temp WgNoise.chacha.code._bytes (Vlong (Int64.repr (n - k)));
           temp WgNoise.chacha.code._nrounds (Vint (Int.repr nr)))
    SEP (data_at ssh t_chacha_state (map Vint (chacha_advance st (chacha_nblocks k))) state;
         data_at dsh (tarray tuchar n) (map Vubyte (chacha_xor nn st (sublist 0 k m)) ++ Zrepeat Vundef (n - k)) dst;
         data_at msh (tarray tuchar n) (map Vubyte m) src))).
  - Exists 0. entailer!.
    change (chacha_nblocks 0) with 0. rewrite lg3_advance_0 by auto. rewrite app_nil_l. cancel.
  - entailer!.
  - (* a chunk of l = 2^32 - 64 bytes: more than UINT_MAX bytes remain *)
    assert (Hk: 4294967295 < n - k).
    { unfold Int64.ltu in HRE. change (Int.unsigned (Int.not (Int.repr 0))) with 4294967295 in HRE.
      rewrite !Int64.unsigned_repr in HRE by rep_lia. destruct (zlt _ _); [lia | discriminate]. }
    forward.
    (* the chunk, kept symbolic: a numeral 2^32 - 64 here makes Coq reduce Z.to_nat (chacha_nblocks _) in unary *)
    set (l := Z.min 4294967232 (n - k)).
    assert (Hl: 0 < l /\ k + l < n) by (subst l; lia).
    assert (Hl64: l mod 64 = 0) by (subst l; rewrite Z.min_l by lia; reflexivity).
    assert (Hl32: 0 <= l <= Int.max_unsigned) by (subst l; rep_lia).
    replace (Int.and (Int.not (Int.repr 0)) (Int.not (Int.sub (Int.repr 64) (Int.repr 1)))) with (Int.repr l)
      by (subst l; rewrite Z.min_l by lia; reflexivity).
    set (c := sublist k (k + l) m).
    assert (Hc: Zlength c = l) by (subst c; rewrite Zlength_sublist; lia).
    assert (Hx: Zlength (chacha_xor nn st (sublist 0 k m)) = k)
      by (rewrite lg3_Zlength_chacha_xor, Zlength_sublist; lia).
    rewrite (lg3_split3 dsh n k l _ dst) by (auto; try lia; rewrite Zlength_app, Zlength_map, Zlength_Zrepeat; lia).
    rewrite (lg3_split3 msh n k l _ src) by (auto; try lia; rewrite Zlength_map; lia).
    replace (sublist k (k + l) (map Vubyte (chacha_xor nn st (sublist 0 k m)) ++ Zrepeat Vundef (n - k)))
      with (Zrepeat Vundef l) by list_solve.
    rewrite (sublist_map _ k (k + l)). fold c.
    assert (E: data_at msh (tarray tuchar l) (map Vubyte c) (offset_val k src) = prim_bytes msh c (offset_val k src))
      by (unfold prim_bytes; rewrite if_false by lia; rewrite Hc; auto).
    assert (E2: data_at dsh (tarray tuchar l) (Zrepeat Vundef l) (offset_val k dst) =
                prim_out dsh (Zrepeat Vundef (Zlength c)) (offset_val k dst))
      by (rewrite cb3_out_nz by (rewrite Zlength_Zrepeat; lia); rewrite Zlength_Zrepeat, Hc by lia; auto).
    rewrite E, E2.
    forward_call (ssh, state, chacha_advance st (chacha_nblocks k), dsh, offset_val k dst, msh, offset_val k src, c, nr).
    { go_lower. apply prop_right. simpl. rewrite Hc. reflexivity. }
    { rewrite ?Hc. cancel. }
    { rewrite lg3_Zlength_advance; auto. }
    rewrite Hc. fold nn.
    rewrite cb3_out_nz by (rewrite Zlength_map, lg3_Zlength_chacha_xor by (rewrite lg3_Zlength_advance; auto); lia).
    rewrite Zlength_map, lg3_Zlength_chacha_xor by (rewrite lg3_Zlength_advance; auto).
    forward. forward. forward.
    rewrite Int.unsigned_repr by rep_lia.
    Exists (k + l).
    assert (Hn: chacha_nblocks (k + l) = chacha_nblocks k + chacha_nblocks l).
    { assert (Hq: k = 64 * (k / 64)) by (pose proof (Z.div_mod k 64); lia).
      rewrite Hq, lg3_nblocks_add, lg3_nblocks_full; try lia; apply Z.div_pos; lia. }
    rewrite Hn, <- lg3_advance_advance by auto.
    rewrite (sublist_split 0 k (k + l) m) by lia. fold c.
    rewrite lg3_chacha_xor_app by (auto; rewrite Zlength_sublist by lia; rewrite Z.sub_0_r; auto).
    rewrite Zlength_sublist by lia. rewrite Z.sub_0_r.
    rewrite Hc.
    set (S := chacha_advance (chacha_advance st (chacha_nblocks k)) (chacha_nblocks l)) in *.
    set (X := chacha_xor nn st (sublist 0 k m)) in *.
    set (Y := chacha_xor nn (chacha_advance st (chacha_nblocks k)) c) in *.
    assert (HY: Zlength Y = l) by (subst Y; rewrite lg3_Zlength_chacha_xor by (rewrite lg3_Zlength_advance; auto); auto).
    clearbody S X Y.
    rewrite (lg3_split3 dsh n k l _ dst)
      by (auto; try lia; rewrite Zlength_app, Zlength_map, Zlength_app, Zlength_Zrepeat; lia).
    rewrite (lg3_split3 msh n k l _ src) by (auto; try lia; rewrite Zlength_map; lia).
    rewrite (sublist_map _ k (k + l) m). fold c. rewrite E.
    clear E E2 Hn. clearbody c. subst n.
    replace (sublist k (k + l) (map Vubyte (X ++ Y) ++ Zrepeat Vundef (Zlength m - (k + l))))
      with (map Vubyte Y) by list_solve.
    replace (sublist 0 k (map Vubyte (X ++ Y) ++ Zrepeat Vundef (Zlength m - (k + l))))
      with (sublist 0 k (map Vubyte X ++ Zrepeat Vundef (Zlength m - k))) by list_solve.
    replace (sublist (k + l) (Zlength m) (map Vubyte (X ++ Y) ++ Zrepeat Vundef (Zlength m - (k + l))))
      with (sublist (k + l) (Zlength m) (map Vubyte X ++ Zrepeat Vundef (Zlength m - k))) by list_solve.
    replace (Zlength m - k - l) with (Zlength m - (k + l)) by lia.
    rewrite (cb3_add_ptr_uint dst k l Pd Hl32), (cb3_add_ptr_uint src k l Ps Hl32).
    assert (Hmod: (k + l) mod 64 = 0).
    { match goal with H: k mod 64 = 0 |- _ => rewrite Z.add_mod, H, Hl64 by lia end. reflexivity. }
    entailer!.
    all: try (repeat match goal with |- _ /\ _ => split end;
              first [assumption | lia | (f_equal; f_equal; lia)]).
  - (* the rest: 1 .. UINT_MAX bytes in one call *)
    assert (Hk: n - k <= 4294967295).
    { unfold Int64.ltu in HRE. change (Int.unsigned (Int.not (Int.repr 0))) with 4294967295 in HRE.
      rewrite !Int64.unsigned_repr in HRE by rep_lia. destruct (zlt _ _); [discriminate | lia]. }
    set (r := n - k) in *.
    set (c := sublist k n m).
    assert (Hc: Zlength c = r) by (subst c; rewrite Zlength_sublist; lia).
    assert (Hx: Zlength (chacha_xor nn st (sublist 0 k m)) = k)
      by (rewrite lg3_Zlength_chacha_xor, Zlength_sublist; lia).
    rewrite (lg3_split2 dsh n k _ dst) by (auto; try lia; rewrite Zlength_app, Zlength_map, Zlength_Zrepeat; lia).
    rewrite (lg3_split2 msh n k _ src) by (auto; try lia; rewrite Zlength_map; lia).
    replace (sublist k n (map Vubyte (chacha_xor nn st (sublist 0 k m)) ++ Zrepeat Vundef r))
      with (Zrepeat Vundef r) by list_solve.
    replace (sublist 0 k (map Vubyte (chacha_xor nn st (sublist 0 k m)) ++ Zrepeat Vundef r))
      with (map Vubyte (chacha_xor nn st (sublist 0 k m))) by list_solve.
    rewrite (sublist_map _ k n). fold c.
    assert (E: data_at msh (tarray tuchar (n - k)) (map Vubyte c) (offset_val k src) = prim_bytes msh c (offset_val k src))
      by (unfold prim_bytes; rewrite if_false by lia; rewrite Hc; auto).
    assert (E2: data_at dsh (tarray tuchar (n - k)) (Zrepeat Vundef r) (offset_val k dst) =
                prim_out dsh (Zrepeat Vundef (Zlength c)) (offset_val k dst))
      by (rewrite cb3_out_nz by (rewrite Zlength_Zrepeat; lia); rewrite Zlength_Zrepeat, Hc by lia; auto).
    rewrite E, E2.
    forward_call (ssh, state, chacha_advance st (chacha_nblocks k), dsh, offset_val k dst, msh, offset_val k src, c, nr).
    { go_lower. apply prop_right. simpl. rewrite Hc.
      try rewrite Int64.unsigned_repr by rep_lia. try rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia.
      reflexivity. }
    { rewrite ?Hc. cancel. }
    { rewrite lg3_Zlength_advance; auto. }
    fold nn.
    rewrite cb3_out_nz by (rewrite Zlength_map, lg3_Zlength_chacha_xor by (rewrite lg3_Zlength_advance; auto); lia).
    rewrite Zlength_map, lg3_Zlength_chacha_xor by (rewrite lg3_Zlength_advance; auto).
    rewrite cb3_out_nz by (rewrite Zlength_map, lg3_Zlength_chacha_xor; auto).
    rewrite Zlength_map, lg3_Zlength_chacha_xor by auto.
    assert (Hn: chacha_nblocks n = chacha_nblocks k + chacha_nblocks r).
    { assert (Hq: k = 64 * (k / 64)) by (pose proof (Z.div_mod k 64); lia).
      replace n with (k + r) by lia. rewrite Hq, lg3_nblocks_add, lg3_nblocks_full; try lia; apply Z.div_pos; lia. }
    rewrite Hn, <- lg3_advance_advance by auto.
    assert (Hm: m = sublist 0 k m ++ c) by (subst c; rewrite sublist_rejoin, sublist_same; auto; lia).
    unfold prim_bytes. rewrite !if_false by (try rewrite Hc; lia).
    rewrite (lg3_split2 msh n k (map Vubyte m) src) by (auto; try lia; rewrite Zlength_map; lia).
    rewrite (sublist_map _ k n m). fold c. rewrite Hc.
    assert (Exor: chacha_xor nn st m =
                  chacha_xor nn st (sublist 0 k m) ++ chacha_xor nn (chacha_advance st (chacha_nblocks k)) c).
    { rewrite Hm at 1. rewrite lg3_chacha_xor_app by (auto; rewrite Zlength_sublist by lia; rewrite Z.sub_0_r; auto).
      rewrite Zlength_sublist by lia. rewrite Z.sub_0_r. reflexivity. }
    rewrite Exor. clear Exor Hm.
    set (X := chacha_xor nn st (sublist 0 k m)) in *.
    set (Y := chacha_xor nn (chacha_advance st (chacha_nblocks k)) c) in *.
    assert (HY: Zlength Y = r) by (subst Y; rewrite lg3_Zlength_chacha_xor by (rewrite lg3_Zlength_advance; auto); auto).
    assert (HX: Zlength X = k) by (subst X; rewrite lg3_Zlength_chacha_xor, Zlength_sublist by (auto; lia); lia).
    clearbody X Y.
    change (Zlength m) with n.
    rewrite (lg3_split2 dsh n k (map Vubyte (X ++ Y)) dst) by (auto; try lia; rewrite Zlength_map, Zlength_app; lia).
    replace (sublist 0 k (map Vubyte (X ++ Y))) with (map Vubyte X) by list_solve.
    replace (sublist k n (map Vubyte (X ++ Y))) with (map Vubyte Y) by list_solve.
    change (n - k) with r.
    entailer!.
Qed.

End ChachaBodiesCtx.
