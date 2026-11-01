(* body proofs of chacha_crypt_generic, chacha_crypt and chacha20_crypt against aead_spec3.aead_G3.

   The series patch P23 ("lib/crypto: chacha: Take a size_t length in chacha_crypt()") gave chacha_crypt and
   chacha20_crypt a size_t length; chacha_crypt feeds chacha_crypt_generic (unsigned int) chunks of
   round_down(UINT_MAX, 64) = 2^32 - 64 bytes while more than UINT_MAX bytes remain, then the rest in one call.
   The destination is NULL-tolerant (prim_out: emp when empty), because __chacha20poly1305_decrypt now reaches
   chacha_crypt_generic(state, NULL, src, 0, 20) for an empty plaintext.  The loop follows an earlier proof of
   the P23 helper chacha20_crypt_long (same chunk size); chacha_crypt_generic's nonempty case is the earlier proof
   (aead_chacha_body.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.chacha.code WgNoise.chacha20poly1305.code.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.common.wg3_iface.
Require Import WgNoise.proof.aead.aead_spec3.
Require Import WgNoise.proof.aead.aead_cce.
Require Import WgNoise.proof.aead.aead_bytes.
Require Import WgNoise.proof.aead.aead_chacha_body.
Require Import WgNoise.proof.aead.aead_long3_model.

Local Open Scope Z_scope.

Lemma cb3_prim_bytes_cs {cs1 cs2: compspecs} sh bs p : @prim_bytes cs1 sh bs p = @prim_bytes cs2 sh bs p.
Proof. unfold prim_bytes. if_tac; auto. apply aead_data_at_tuchar_cs. Qed.

Lemma cb3_prim_out_cs {cs1 cs2: compspecs} sh (v: list val) p : @prim_out cs1 sh v p = @prim_out cs2 sh v p.
Proof. unfold prim_out. if_tac; auto. apply aead_data_at_tuchar_cs. Qed.

Lemma cb3_out_nz {cs: compspecs} sh (v: list val) p :
  Zlength v <> 0 -> prim_out sh v p = data_at sh (tarray tuchar (Zlength v)) v p.
Proof. intros H. unfold prim_out. rewrite if_false by auto. reflexivity. Qed.

Lemma cb3_out_z {cs: compspecs} sh (v: list val) p : Zlength v = 0 -> prim_out sh v p = emp.
Proof. intros H. unfold prim_out. rewrite if_true by auto. reflexivity. Qed.

Lemma cb3_add_ptr_uint {cs: compspecs} p k l :
  isptr p -> 0 <= l <= Int.max_unsigned ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tuint (offset_val k p) (Vint (Int.repr l))) =
  offset_val (k + l) p.
Proof.
  intros Hp Hl. destruct p; try contradiction. simpl.
  f_equal. rewrite Ptrofs.add_assoc. f_equal. unfold Ptrofs.of_intu, Ptrofs.of_int.
  rewrite Int.unsigned_repr by auto. rewrite Ptrofs.mul_commut, Ptrofs.mul_one. rewrite Ptrofs.add_unsigned.
  apply Ptrofs.eqm_samerepr. apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym; apply Ptrofs.eqm_unsigned_repr.
Qed.

Section ChachaBodies3.
#[local] Existing Instance Chacha.CS.

(* chacha_crypt_generic: the earlier proof (aead_chacha_body.body_chacha_crypt_generic) with the empty case
   NULL-tolerant *)
Lemma body_chacha_crypt_generic3 :
  @semax_body (QPvarspecs Chacha.qp) (aead_imports3 Chacha.CS ++ aead_G3) Chacha.CS
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

End ChachaBodies3.

Section C20pBodies3.
#[local] Existing Instance Chacha20poly1305.CS.

(* chacha20_crypt(state, dst, src, bytes) = chacha_crypt(state, dst, src, bytes, 20): one call *)
Lemma body_chacha20_crypt3 :
  @semax_body (QPvarspecs Chacha20poly1305.qp) (aead_imports3 Chacha20poly1305.CS ++ aead_G3)
    Chacha20poly1305.CS WgNoise.chacha20poly1305.code.f_chacha20_crypt chacha20_crypt_spec3.
Proof.
  start_function.
  rewrite (@cb3_prim_bytes_cs Chacha20poly1305.CS Chacha.CS).
  rewrite (@cb3_prim_out_cs Chacha20poly1305.CS Chacha.CS).
  forward_call (ssh, state, st, dsh, dst, msh, src, m, 20).
  rewrite (@cb3_prim_bytes_cs Chacha.CS Chacha20poly1305.CS).
  rewrite (@cb3_prim_out_cs Chacha.CS Chacha20poly1305.CS).
  change (Z.to_nat (20 / 2)) with 10%nat.
  entailer!.
Qed.

End C20pBodies3.

