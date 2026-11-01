(* Body proofs of the ChaCha stream functions. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.chacha.code WgNoise.chacha20poly1305.code.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.aead.aead_spec.
Require Import WgNoise.proof.aead.aead_cce.
Require Import WgNoise.proof.aead.aead_bytes.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* model facts                                                             *)
(* ---------------------------------------------------------------------- *)

Lemma chc_Zlength_qround x a b c d : Zlength (chacha_qround x a b c d) = Zlength x.
Proof.
  unfold chacha_qround. rewrite !Zlength_upd_Znth. reflexivity.
Qed.

Lemma chc_Zlength_dround x : Zlength (chacha_dround x) = Zlength x.
Proof.
  unfold chacha_dround. rewrite !chc_Zlength_qround. reflexivity.
Qed.

(* (the kernel compares the arguments of chacha_rounds right to left: never let it compare
   chacha_rounds (S n) x with chacha_rounds n (chacha_dround x), go through the unfolded fix) *)
Lemma chc_Zlength_rounds n x : Zlength (chacha_rounds n x) = Zlength x.
Proof.
  revert x; induction n; intros x; [reflexivity |].
  change (Zlength ((fix rounds (n : nat) (x : list int) {struct n} : list int :=
                      match n with O => x | S k => rounds k (chacha_dround x) end) n (chacha_dround x))
          = Zlength x).
  transitivity (Zlength (chacha_dround x)).
  - exact (IHn (chacha_dround x)).
  - apply chc_Zlength_dround.
Qed.

Lemma chc_Zlength_words_bytes ws : Zlength (words_bytes ws) = 4 * Zlength ws.
Proof.
  unfold words_bytes. induction ws; cbn [map concat]; auto.
  rewrite Zlength_app, IHws, Zlength_cons. unfold le32_bytes. rewrite !Zlength_cons, Zlength_nil. lia.
Qed.

Lemma chc_Zlength_add_words a b : Zlength a = Zlength b -> Zlength (add_words a b) = Zlength a.
Proof.
  intros H. unfold add_words. rewrite Zlength_map. rewrite !Zlength_correct in *.
  rewrite combine_length. lia.
Qed.

Lemma chc_Zlength_block_bytes n st : Zlength st = 16 -> Zlength (chacha_block_bytes n st) = 64.
Proof.
  intros H. unfold chacha_block_bytes, chacha_block_words.
  rewrite chc_Zlength_words_bytes, chc_Zlength_add_words; rewrite ?chc_Zlength_rounds; lia.
Qed.

Lemma chc_Zlength_advance st k : Zlength (chacha_advance st k) = Zlength st.
Proof. unfold chacha_advance. apply Zlength_upd_Znth. Qed.

Lemma chc_advance_0 st : Zlength st = 16 -> chacha_advance st 0 = st.
Proof.
  intros H. unfold chacha_advance. rewrite Int.add_zero. apply upd_Znth_triv; auto; lia.
Qed.

Lemma chc_advance_advance st a b :
  Zlength st = 16 -> chacha_advance (chacha_advance st a) b = chacha_advance st (a + b).
Proof.
  intros H. unfold chacha_advance.
  rewrite upd_Znth_same by lia. rewrite upd_Znth_twice by lia.
  rewrite Int.add_assoc, add_repr. reflexivity.
Qed.

Lemma chc_Zlength_stream n st k :
  Zlength st = 16 -> Zlength (chacha_stream n st k) = 64 * Z.of_nat k.
Proof.
  revert st; induction k; intros st H; cbn [chacha_stream]; auto.
  rewrite Zlength_app, chc_Zlength_block_bytes, IHk by (rewrite ?chc_Zlength_advance; auto). lia.
Qed.

Lemma chc_stream_snoc n st k :
  Zlength st = 16 ->
  chacha_stream n st (S k) = chacha_stream n st k ++ chacha_block_bytes n (chacha_advance st (Z.of_nat k)).
Proof.
  revert st; induction k; intros st H.
  - cbn [chacha_stream Z.of_nat]. rewrite chc_advance_0 by auto. rewrite app_nil_r; auto.
  - change (chacha_stream n st (S (S k))) with
      (chacha_block_bytes n st ++ chacha_stream n (chacha_advance st 1) (S k)).
    rewrite IHk by (rewrite chc_Zlength_advance; auto).
    rewrite chc_advance_advance by auto. rewrite app_assoc. do 2 f_equal. f_equal. lia.
Qed.

Lemma chc_Zlength_xor a b : Zlength (xor_bytes a b) = Z.min (Zlength a) (Zlength b).
Proof.
  unfold xor_bytes. rewrite Zlength_map, !Zlength_correct, combine_length. lia.
Qed.

Lemma chc_xor_app a1 a2 b1 b2 :
  Zlength a1 = Zlength b1 -> xor_bytes (a1 ++ a2) (b1 ++ b2) = xor_bytes a1 b1 ++ xor_bytes a2 b2.
Proof.
  revert b1; induction a1; intros b1 H; destruct b1; simpl; auto;
    rewrite ?Zlength_cons, ?Zlength_nil in H.
  - pose proof (Zlength_nonneg b1); lia.
  - pose proof (Zlength_nonneg a1); lia.
  - unfold xor_bytes in *; simpl. f_equal. apply IHa1. lia.
Qed.

Lemma chc_xor_trunc a b : Zlength a <= Zlength b -> xor_bytes a b = xor_bytes a (sublist 0 (Zlength a) b).
Proof.
  intros H. pose proof (Zlength_nonneg a).
  assert (Hb: b = sublist 0 (Zlength a) b ++ sublist (Zlength a) (Zlength b) b)
    by (rewrite sublist_rejoin, sublist_same; auto; lia).
  rewrite Hb at 1. rewrite <- (app_nil_r a) at 1. rewrite chc_xor_app.
  - change (xor_bytes [] (sublist (Zlength a) (Zlength b) b)) with (@nil byte). apply app_nil_r.
  - rewrite Zlength_sublist; lia.
Qed.

Lemma chc_nblocks_full k : 0 <= k -> chacha_nblocks (64 * k) = k.
Proof.
  intros. unfold chacha_nblocks. symmetry. apply Z.div_unique with 63; lia.
Qed.

Lemma chc_nblocks_tail k len : 0 <= k -> 64 * k < len < 64 * k + 64 -> chacha_nblocks len = k + 1.
Proof.
  intros. unfold chacha_nblocks. symmetry. apply Z.div_unique with (len + 63 - 64 * (k + 1)); lia.
Qed.

(* the keystream XOR of the first k whole blocks *)
Definition chc_done (nn: nat) (st: list int) (m: list byte) (k: Z) : list byte :=
  xor_bytes (sublist 0 (64 * k) m) (chacha_stream nn st (Z.to_nat k)).

Lemma chc_Zlength_done nn st m k :
  Zlength st = 16 -> 0 <= k -> 64 * k <= Zlength m -> Zlength (chc_done nn st m k) = 64 * k.
Proof.
  intros. unfold chc_done. rewrite chc_Zlength_xor, Zlength_sublist, chc_Zlength_stream by lia.
  rewrite Z2Nat.id by lia. lia.
Qed.

Lemma chc_done_step nn st m k :
  Zlength st = 16 -> 0 <= k -> 64 * k + 64 <= Zlength m ->
  chc_done nn st m (k + 1) =
  chc_done nn st m k ++ xor_bytes (sublist (64 * k) (64 * k + 64) m) (chacha_block_bytes nn (chacha_advance st k)).
Proof.
  intros. unfold chc_done. rewrite Z2Nat.inj_add, Nat.add_1_r by lia. rewrite chc_stream_snoc by auto.
  rewrite Z2Nat.id by lia.
  rewrite <- (sublist_rejoin 0 (64 * k) (64 * (k + 1)) m) by lia.
  rewrite chc_xor_app.
  - replace (64 * (k + 1)) with (64 * k + 64) by lia. reflexivity.
  - rewrite Zlength_sublist, chc_Zlength_stream, Z2Nat.id by lia. lia.
Qed.

Lemma chc_done_full nn st m k :
  Zlength st = 16 -> 0 <= k -> Zlength m = 64 * k -> chc_done nn st m k = chacha_xor nn st m.
Proof.
  intros. unfold chc_done, chacha_xor. rewrite sublist_same by lia.
  rewrite H1, chc_nblocks_full by lia. reflexivity.
Qed.

Lemma chc_done_tail nn st m k :
  Zlength st = 16 -> 0 <= k -> 64 * k < Zlength m < 64 * k + 64 ->
  chc_done nn st m k ++
  xor_bytes (sublist (64 * k) (Zlength m) m)
    (sublist 0 (Zlength m - 64 * k) (chacha_block_bytes nn (chacha_advance st k))) =
  chacha_xor nn st m.
Proof.
  intros. unfold chc_done, chacha_xor.
  rewrite (chc_nblocks_tail k) by lia.
  rewrite Z2Nat.inj_add, Nat.add_1_r by lia. rewrite chc_stream_snoc by auto. rewrite Z2Nat.id by lia.
  assert (Hm: m = sublist 0 (64 * k) m ++ sublist (64 * k) (Zlength m) m)
    by (rewrite sublist_rejoin, sublist_same; auto; lia).
  symmetry. rewrite Hm at 1. rewrite chc_xor_app.
  2: rewrite Zlength_sublist, chc_Zlength_stream, Z2Nat.id by lia; lia.
  f_equal. rewrite (chc_xor_trunc (sublist (64 * k) (Zlength m) m)).
  - rewrite Zlength_sublist by lia. reflexivity.
  - rewrite Zlength_sublist, chc_Zlength_block_bytes by (rewrite ?chc_Zlength_advance; lia). lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* byte arrays                                                             *)
(* ---------------------------------------------------------------------- *)

Lemma chc_split3 {cs: compspecs} sh n i j (v: list val) p :
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

Lemma chc_split2 {cs: compspecs} sh n i (v: list val) p :
  0 <= i <= n -> Zlength v = n -> field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) v p =
  (data_at sh (tarray tuchar i) (sublist 0 i v) p *
   data_at sh (tarray tuchar (n - i)) (sublist i n v) (offset_val i p))%logic.
Proof.
  intros. unfold tarray. rewrite (split2_data_at_Tarray_tuchar sh n i) by lia.
  fold (tarray tuchar n). rewrite arr_field_address0 by (auto; lia).
  change (sizeof tuchar) with 1. rewrite Z.mul_1_l. reflexivity.
Qed.

Lemma chc_split2_ {cs: compspecs} sh n i p :
  0 <= i <= n -> field_compatible (tarray tuchar n) [] p ->
  data_at_ sh (tarray tuchar n) p =
  (data_at_ sh (tarray tuchar i) p * data_at_ sh (tarray tuchar (n - i)) (offset_val i p))%logic.
Proof.
  intros. rewrite !data_at__tarray. rewrite (chc_split2 sh n i) by (auto; rewrite Zlength_Zrepeat; lia).
  rewrite !sublist_Zrepeat by lia. f_equal; f_equal; f_equal; lia.
Qed.

Section ChachaBodies.
#[local] Existing Instance Chacha.CS.

Lemma body_chacha_crypt_generic :
  @semax_body (QPvarspecs Chacha.qp) (aead_imports_def Chacha.CS ++ aead_G_def) Chacha.CS
    WgNoise.chacha.code.f_chacha_crypt_generic chacha_crypt_generic_spec.
Proof.
  unfold chacha_crypt_generic_spec, chacha_crypt_spec_for. start_function.
  pose proof (Zlength_nonneg m) as Hm0.
  set (nn := Z.to_nat (nr / 2)).
  assert_PROP (field_compatible (tarray tuchar (Zlength m)) [] dst) as FCd by entailer!.
  destruct (Z.eq_dec (Zlength m) 0) as [Hz | Hnz].
  { (* empty message: nothing but the tests *)
    unfold prim_bytes. rewrite if_true by auto.
    forward_while (@exp (environ -> mpred) _ unit (fun _ =>
      PROP ()
      LOCAL (lvar WgNoise.chacha.code._stream (tarray tuchar 64) v_stream; temp WgNoise.chacha.code._state state;
             temp WgNoise.chacha.code._dst dst; temp WgNoise.chacha.code._src src;
             temp WgNoise.chacha.code._bytes (Vint (Int.repr (Zlength m)));
             temp WgNoise.chacha.code._nrounds (Vint (Int.repr nr)))
      SEP (data_at_ Tsh (tarray tuchar 64) v_stream; data_at ssh t_chacha_state (map Vint st) state;
           data_at_ dsh (tarray tuchar (Zlength m)) dst))).
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
        rewrite data_at__tarray. entailer!. }
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

(* body_chacha_crypt is gone: the series patch P23 gave
   chacha_crypt a loop over chunks of round_down(UINT_MAX, 64) bytes; its body is aead_chacha_body3.v's
   (NULL-tolerant destination, against aead_G3). *)

Lemma body_hchacha_block :
  @semax_body (QPvarspecs Chacha.qp) (aead_imports_def Chacha.CS ++ aead_G_def) Chacha.CS
    WgNoise.chacha.code.f_hchacha_block hchacha_block_spec.
Proof.
  unfold hchacha_block_spec, hchacha_block_spec_for. start_function.
  forward_call (ssh, state, st, osh, out, nr).
  entailer!.
Qed.

End ChachaBodies.

Lemma chc_prim_bytes_cs {cs1 cs2: compspecs} sh bs p : @prim_bytes cs1 sh bs p = @prim_bytes cs2 sh bs p.
Proof. unfold prim_bytes. if_tac; auto. apply aead_data_at_tuchar_cs. Qed.

(* body_chacha20_crypt is aead_chacha_body3.v's (size_t length, NULL-tolerant destination) *)

Theorem aead_chacha_bodies :
  @semax_body (QPvarspecs Chacha.qp) (aead_imports_def Chacha.CS ++ aead_G_def) Chacha.CS
    WgNoise.chacha.code.f_chacha_crypt_generic chacha_crypt_generic_spec /\
  @semax_body (QPvarspecs Chacha.qp) (aead_imports_def Chacha.CS ++ aead_G_def) Chacha.CS
    WgNoise.chacha.code.f_hchacha_block hchacha_block_spec.
Proof.
  exact (conj body_chacha_crypt_generic body_hchacha_block).
Qed.
