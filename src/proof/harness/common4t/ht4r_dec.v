(* the bodies of ref_chacha20_xor and
   ref_aead_decrypt of common.h against the NULL-tolerant specifications of ht4r_spec.v.  Adapted from law
   prim_aead's haead_tag_body3.v (part 3) and haead_ref_body3.v (har_decrypt): dst `prim_out`, src / ad
   `prim_bytes` (emp when empty, any pointer then). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.harness.prim_aead.haead_lemmas3.
Require Import WgNoise.proof.harness.common4t.ht4r_spec.
Require WgNoise.harness.x_prim_aead.code.

#[local] Existing Instance W_prim_aead.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* part 1: ref_chacha20_xor (law prim_aead's haead_tag_body3.v part 3, hax_ -> ht4rd_x_)                *)
(* ====================================================================== *)

Module HDX := WgNoise.harness.x_prim_aead.code.

(* model facts: lengths, the bytes of one block *)
Lemma ht4rd_x_Zlength_qround x a b c d : Zlength (chacha_qround x a b c d) = Zlength x.
Proof. unfold chacha_qround. rewrite !Zlength_upd_Znth. reflexivity. Qed.

Lemma ht4rd_x_Zlength_dround x : Zlength (chacha_dround x) = Zlength x.
Proof. unfold chacha_dround. rewrite !ht4rd_x_Zlength_qround. reflexivity. Qed.

Lemma ht4rd_x_Zlength_rounds n x : Zlength (chacha_rounds n x) = Zlength x.
Proof.
  revert x; induction n; intros x; [reflexivity |].
  change (Zlength ((fix rounds (n : nat) (x : list int) {struct n} : list int :=
                      match n with O => x | S k => rounds k (chacha_dround x) end) n (chacha_dround x))
          = Zlength x).
  transitivity (Zlength (chacha_dround x)).
  - exact (IHn (chacha_dround x)).
  - apply ht4rd_x_Zlength_dround.
Qed.

Lemma ht4rd_x_Zlength_block_bytes n st : Zlength st = 16 -> Zlength (chacha_block_bytes n st) = 64.
Proof.
  intros H. unfold chacha_block_bytes, chacha_block_words.
  assert (Hw: forall ws, Zlength (words_bytes ws) = 4 * Zlength ws).
  { intros ws. unfold words_bytes. induction ws; cbn [map concat]; auto.
    rewrite Zlength_app, IHws, Zlength_cons. unfold le32_bytes. rewrite !Zlength_cons, Zlength_nil. lia. }
  rewrite Hw. unfold add_words. rewrite Zlength_map.
  pose proof (ht4rd_x_Zlength_rounds n st) as Hr. rewrite !Zlength_correct in *.
  rewrite length_combine, Nat2Z.inj_min. rewrite Hr, H. reflexivity.
Qed.

Lemma ht4rd_x_Zlength_st key nonce : Zlength (aead_st key nonce) = 16.
Proof. unfold aead_st, chacha_init_st, le32_words. rewrite !Zlength_app, !Zlength_map. reflexivity. Qed.

Lemma ht4rd_x_xor_Znth a b j : 0 <= j < Zlength a -> 0 <= j < Zlength b ->
  Znth j (xor_bytes a b) = Byte.xor (Znth j a) (Znth j b).
Proof.
  revert b j; induction a as [|x a IH]; intros b j Ha Hb; [rewrite Zlength_nil in Ha; lia |].
  destruct b as [|y b]; [rewrite Zlength_nil in Hb; lia |].
  unfold xor_bytes; cbn [combine map].
  destruct (Z.eq_dec j 0).
  - subst. rewrite !Znth_0_cons. reflexivity.
  - rewrite Zlength_cons in Ha, Hb. rewrite !Znth_pos_cons by lia. apply IH; lia.
Qed.

(* the block b of the keystream, as ref_chacha20_block computes it with ctr = 1 + b *)
Definition ht4rd_x_blk (key: list byte) (nonce b: Z) : list byte :=
  chacha_block_bytes 10 (chacha_advance (aead_st key nonce) (Int.unsigned (Int.repr (1 + b)))).

Lemma ht4rd_x_blk_len key nonce b : Zlength (ht4rd_x_blk key nonce b) = 64.
Proof. unfold ht4rd_x_blk. apply ht4rd_x_Zlength_block_bytes. apply haead_advance_length, ht4rd_x_Zlength_st. Qed.

Lemma ht4rd_x_blk_eq key nonce b :
  ht4rd_x_blk key nonce b = chacha_block_bytes 10 (chacha_advance (chacha_advance (aead_st key nonce) 1) b).
Proof.
  unfold ht4rd_x_blk. f_equal. rewrite haead_advance_add by apply ht4rd_x_Zlength_st. apply haead_advance_repr.
Qed.

Lemma ht4rd_x_xor_len (HH: haead_hyps) key nonce m :
  Zlength (chacha_xor 10 (chacha_advance (aead_st key nonce) 1) m) = Zlength m.
Proof.
  destruct HH as (_ & (_ & HL & _) & _).
  apply HL; try (apply haead_advance_length, ht4rd_x_Zlength_st).
Qed.

Lemma ht4rd_x_block_fact (HH: haead_hyps) key nonce m b j :
  0 <= b -> 64 * b < Zlength m -> 0 <= j < Z.min 64 (Zlength m - 64 * b) ->
  Znth (64 * b + j) (chacha_xor 10 (chacha_advance (aead_st key nonce) 1) m) =
  Byte.xor (Znth (64 * b + j) m) (Znth j (ht4rd_x_blk key nonce b)).
Proof.
  intros Hb Hm Hj.
  pose proof (ht4rd_x_xor_len HH key nonce m) as HX.
  pose proof (ht4rd_x_blk_len key nonce b) as HB.
  destruct HH as (_ & (_ & _ & HF & _) & _).
  pose proof (ht4rd_x_Zlength_st key nonce) as Hst.
  rewrite (ht4rd_x_blk_eq key nonce b).
  pose proof (HF (chacha_advance (aead_st key nonce) 1) m b (haead_advance_length _ _ Hst) Hb Hm) as E.
  assert (HB2: Zlength (chacha_block_bytes 10 (chacha_advance (chacha_advance (aead_st key nonce) 1) b)) = 64)
    by (apply ht4rd_x_Zlength_block_bytes; do 2 apply haead_advance_length; exact Hst).
  clear HF HB.
  replace (64 * b + j) with (j + 64 * b) by lia.
  rewrite <- (Znth_sublist (64 * b) j (Z.min (64 * b + 64) (Zlength m)) (chacha_xor 10 (chacha_advance (aead_st key nonce) 1) m)) by lia.
  rewrite <- (Znth_sublist (64 * b) j (Z.min (64 * b + 64) (Zlength m)) m) by lia.
  rewrite E. apply ht4rd_x_xor_Znth; [rewrite Zlength_sublist by lia; lia | lia].
Qed.

Lemma ht4rd_x_xor_byte a b :
  Vint (Int.zero_ext 8 (Int.xor (Int.repr (Byte.unsigned a)) (Int.repr (Byte.unsigned b)))) = Vubyte (Byte.xor a b).
Proof.
  unfold Vubyte. f_equal. apply Int.same_bits_eq. intros i Hi. rewrite Int.bits_zero_ext by lia. destruct (zlt i 8).
  { rewrite Int.bits_xor by lia. rewrite !Int.testbit_repr by lia.
    change (Z.testbit (Byte.unsigned ?x) i) with (Byte.testbit x i).
    rewrite Byte.bits_xor by (change Byte.zwordsize with 8; lia). reflexivity. }
  { rewrite Int.testbit_repr by lia. change (Z.testbit (Byte.unsigned ?x) i) with (Byte.testbit x i).
    symmetry. apply Byte.bits_above. change Byte.zwordsize with 8; lia. }
Qed.

Lemma ht4rd_x_is_int_Vubyte b : is_int I8 Unsigned (Vubyte b).
Proof.
  unfold Vubyte; simpl. pose proof (Byte.unsigned_range_2 b).
  rewrite Int.unsigned_repr by rep_lia. rep_lia.
Qed.

(* the statements of ref_chacha20_xor: the call, the inner loop (one lemma each: recipe-big-straightline) *)
Definition ht4rd_x_call : statement :=
  ltac:(let b := eval cbv delta [HDX.f_ref_chacha20_xor fn_body] beta iota in (fn_body HDX.f_ref_chacha20_xor) in
        match b with Ssequence _ (Ssequence _ (Swhile _ (Ssequence ?r _))) => exact r end).
Definition ht4rd_x_inner : statement :=
  ltac:(let b := eval cbv delta [HDX.f_ref_chacha20_xor fn_body] beta iota in (fn_body HDX.f_ref_chacha20_xor) in
        match b with Ssequence _ (Ssequence _ (Swhile _ (Ssequence _ (Ssequence ?r _)))) => exact r end).

Definition ht4rd_x_D (mp: ident) : tycontext := func_tycontext HDX.f_ref_chacha20_xor [] (ht4r_Gprog mp) nil.

(* ref_chacha20_block(blk, key, ctr, nonce) *)
Lemma ht4rd_x_call_ok (Espec: OracleKind) (mp: ident) ksh kp key nonce vblk b vpos vdst vsrc vlen Fa Fb :
  readable_share ksh -> Zlength key = 32 -> 0 <= nonce <= Int64.max_unsigned ->
  semax (ht4rd_x_D mp)
    (PROP () LOCAL (temp HDX._pos vpos; temp HDX._ctr (Vint (Int.repr (1 + b))); lvar HDX._blk (tarray tuchar 64) vblk;
      temp HDX._dst vdst; temp HDX._src vsrc; temp HDX._len vlen; temp HDX._key kp;
      temp HDX._nonce (Vlong (Int64.repr nonce)))
    SEP (data_at_ Tsh (tarray tuchar 64) vblk; data_at ksh (tarray tuchar 32) (map Vubyte key) kp; Fa; Fb))
    ht4rd_x_call
    (normal_ret_assert
      (PROP () LOCAL (temp HDX._pos vpos; temp HDX._ctr (Vint (Int.repr (1 + b))); lvar HDX._blk (tarray tuchar 64) vblk;
        temp HDX._dst vdst; temp HDX._src vsrc; temp HDX._len vlen; temp HDX._key kp;
        temp HDX._nonce (Vlong (Int64.repr nonce)))
      SEP (data_at Tsh (tarray tuchar 64)
             (map Vubyte (ht4rd_x_blk key nonce b)) vblk;
           data_at ksh (tarray tuchar 32) (map Vubyte key) kp; Fa; Fb))).
Proof.
  intros SH Hk Hn.
  unfold ht4rd_x_call, ht4rd_x_D. abbreviate_semax.
  forward_call (Tsh, vblk, ksh, kp, key, Int.repr (1 + b), nonce).
  unfold ht4rd_x_blk.
  generalize (chacha_block_bytes 10 (chacha_advance (aead_st key nonce) (Int.unsigned (Int.repr (1 + b))))); intros bl.
  entailer!.
Qed.

Lemma ht4rd_x_cmp1 pos j len n : 0 <= pos < len -> len <= Int64.max_signed -> 0 <= j < 64 ->
  n = Z.min 64 (len - pos) ->
  bool2val (Int64.cmpu Clt (Int64.add (Int64.repr pos) (Int64.repr j)) (Int64.repr len)) =
  Vint (if zlt j n then Int.one else Int.zero).
Proof.
  intros. unfold Int64.cmpu, Int64.ltu. rewrite Int64.add_unsigned.
  rewrite (Int64.unsigned_repr pos), (Int64.unsigned_repr j), (Int64.unsigned_repr (pos + j)),
    (Int64.unsigned_repr len) by rep_lia.
  destruct (zlt (pos + j) len), (zlt j n); try lia; reflexivity.
Qed.

Lemma ht4rd_x_upd_step (X: list byte) k L : 0 <= k < Zlength X -> Zlength X = L ->
  upd_Znth k (map Vubyte (sublist 0 k X) ++ Zrepeat Vundef (L - k)) (Vubyte (Znth k X)) =
  map Vubyte (sublist 0 (k + 1) X) ++ Zrepeat Vundef (L - (k + 1)).
Proof. intros. list_solve. Qed.

(* an equation and the block fact, wrapped so that entailer! leaves them alone *)
Definition ht4rd_x_eq {A} (x y: A) : Prop := x = y.

Definition ht4rd_x_fact (X: list byte) (key: list byte) (nonce: Z) (m: list byte) : Prop :=
  forall b j, 0 <= b -> 64 * b < Zlength m -> 0 <= j < Z.min 64 (Zlength m - 64 * b) ->
    Znth (64 * b + j) X = Byte.xor (Znth (64 * b + j) m) (Znth j (ht4rd_x_blk key nonce b)).

(* the inner loop: dst[pos + i] = src[pos + i] ^ blk[i] for i < n = min 64 (len - pos) *)
Lemma ht4rd_x_inner_ok (Espec: OracleKind) (mp: ident) dsh vdst ssh vsrc m X B pos vblk kp vnonce vctr Fa :
  writable_share dsh -> readable_share ssh -> Zlength m <= Int64.max_signed -> 0 <= pos < Zlength m ->
  Zlength X = Zlength m -> Zlength B = 64 ->
  (forall j, 0 <= j < Z.min 64 (Zlength m - pos) -> Znth (pos + j) X = Byte.xor (Znth (pos + j) m) (Znth j B)) ->
  semax (ht4rd_x_D mp)
    (PROP () LOCAL (temp HDX._pos (Vlong (Int64.repr pos)); temp HDX._ctr vctr; lvar HDX._blk (tarray tuchar 64) vblk;
      temp HDX._dst vdst; temp HDX._src vsrc; temp HDX._len (Vlong (Int64.repr (Zlength m))); temp HDX._key kp;
      temp HDX._nonce vnonce)
    SEP (data_at Tsh (tarray tuchar 64) (map Vubyte B) vblk;
      data_at dsh (tarray tuchar (Zlength m)) (map Vubyte (sublist 0 pos X) ++ Zrepeat Vundef (Zlength m - pos)) vdst;
      data_at ssh (tarray tuchar (Zlength m)) (map Vubyte m) vsrc; Fa))
    ht4rd_x_inner
    (normal_ret_assert
      (PROP () LOCAL (temp HDX._i (Vlong (Int64.repr (Z.min 64 (Zlength m - pos))));
        temp HDX._pos (Vlong (Int64.repr pos)); temp HDX._ctr vctr; lvar HDX._blk (tarray tuchar 64) vblk;
        temp HDX._dst vdst; temp HDX._src vsrc; temp HDX._len (Vlong (Int64.repr (Zlength m))); temp HDX._key kp;
        temp HDX._nonce vnonce)
      SEP (data_at Tsh (tarray tuchar 64) (map Vubyte B) vblk;
        data_at dsh (tarray tuchar (Zlength m))
          (map Vubyte (sublist 0 (pos + Z.min 64 (Zlength m - pos)) X) ++
           Zrepeat Vundef (Zlength m - (pos + Z.min 64 (Zlength m - pos)))) vdst;
        data_at ssh (tarray tuchar (Zlength m)) (map Vubyte m) vsrc; Fa))).
Proof.
  intros SH SH0 Hmax Hp HX HB Hfact.
  unfold ht4rd_x_inner, ht4rd_x_D. abbreviate_semax.
  remember (Z.min 64 (Zlength m - pos)) as n eqn:Hn.
  assert (Hn1: 0 < n <= 64) by lia. assert (Hn2: pos + n <= Zlength m) by lia.
  assert (Hn3: n = 64 \/ pos + n = Zlength m) by lia.
  forward.
  forward_loop (EX j: Z,
      PROP (0 <= j <= n)
      LOCAL (temp HDX._i (Vlong (Int64.repr j));
        temp HDX._pos (Vlong (Int64.repr pos)); temp HDX._ctr vctr; lvar HDX._blk (tarray tuchar 64) vblk;
        temp HDX._dst vdst; temp HDX._src vsrc; temp HDX._len (Vlong (Int64.repr (Zlength m))); temp HDX._key kp;
        temp HDX._nonce vnonce)
      SEP (data_at Tsh (tarray tuchar 64) (map Vubyte B) vblk;
        data_at dsh (tarray tuchar (Zlength m))
          (map Vubyte (sublist 0 (pos + j) X) ++ Zrepeat Vundef (Zlength m - (pos + j))) vdst;
        data_at ssh (tarray tuchar (Zlength m)) (map Vubyte m) vsrc; Fa))%assert
    continue: (EX j: Z,
      PROP (0 <= j < n)
      LOCAL (temp HDX._i (Vlong (Int64.repr j));
        temp HDX._pos (Vlong (Int64.repr pos)); temp HDX._ctr vctr; lvar HDX._blk (tarray tuchar 64) vblk;
        temp HDX._dst vdst; temp HDX._src vsrc; temp HDX._len (Vlong (Int64.repr (Zlength m))); temp HDX._key kp;
        temp HDX._nonce vnonce)
      SEP (data_at Tsh (tarray tuchar 64) (map Vubyte B) vblk;
        data_at dsh (tarray tuchar (Zlength m))
          (map Vubyte (sublist 0 (pos + j + 1) X) ++ Zrepeat Vundef (Zlength m - (pos + j + 1))) vdst;
        data_at ssh (tarray tuchar (Zlength m)) (map Vubyte m) vsrc; Fa))%assert
    break: (PROP () LOCAL (temp HDX._i (Vlong (Int64.repr n));
        temp HDX._pos (Vlong (Int64.repr pos)); temp HDX._ctr vctr; lvar HDX._blk (tarray tuchar 64) vblk;
        temp HDX._dst vdst; temp HDX._src vsrc; temp HDX._len (Vlong (Int64.repr (Zlength m))); temp HDX._key kp;
        temp HDX._nonce vnonce)
      SEP (data_at Tsh (tarray tuchar 64) (map Vubyte B) vblk;
        data_at dsh (tarray tuchar (Zlength m))
          (map Vubyte (sublist 0 (pos + n) X) ++ Zrepeat Vundef (Zlength m - (pos + n))) vdst;
        data_at ssh (tarray tuchar (Zlength m)) (map Vubyte m) vsrc; Fa)).
  - Exists 0. rewrite Z.add_0_r. entailer!.
  - Intros j.
    forward_if (PROP () LOCAL (temp HDX._t'1 (Vint (if zlt j n then Int.one else Int.zero)); temp HDX._i (Vlong (Int64.repr j));
        temp HDX._pos (Vlong (Int64.repr pos)); temp HDX._ctr vctr; lvar HDX._blk (tarray tuchar 64) vblk;
        temp HDX._dst vdst; temp HDX._src vsrc; temp HDX._len (Vlong (Int64.repr (Zlength m))); temp HDX._key kp;
        temp HDX._nonce vnonce)
      SEP (data_at Tsh (tarray tuchar 64) (map Vubyte B) vblk;
        data_at dsh (tarray tuchar (Zlength m))
          (map Vubyte (sublist 0 (pos + j) X) ++ Zrepeat Vundef (Zlength m - (pos + j))) vdst;
        data_at ssh (tarray tuchar (Zlength m)) (map Vubyte m) vsrc; Fa)).
    1: { rewrite !Int64.unsigned_repr in H0 by rep_lia. forward. rewrite (ht4rd_x_cmp1 pos j (Zlength m) n) by (auto; lia). entailer!. }
    1: { rewrite !Int64.unsigned_repr in H0 by rep_lia. forward. destruct (zlt j n); [lia |]. entailer!. }
    forward_if.
    2: { assert (j = n) by (destruct (zlt j n); [discriminate | lia]). subst j. forward. entailer!. }
    assert (Hj: j < n) by (destruct (zlt j n); [lia | exfalso; apply H0; reflexivity]).
    forward.
    1: { entailer!. try rewrite Znth_map by lia. apply ht4rd_x_is_int_Vubyte. }
    rewrite Znth_map by lia.
    forward.
    1: { entailer!. try rewrite Znth_map by lia. apply ht4rd_x_is_int_Vubyte. }
    rewrite Znth_map by lia.
    forward.
    rewrite ht4rd_x_xor_byte, <- Hfact by lia.
    rewrite ht4rd_x_upd_step by lia.
    Exists j. entailer!.
  - Intros j. forward. Exists (j + 1). replace (pos + (j + 1)) with (pos + j + 1) by lia. entailer!.
  - unfold POSTCONDITION, abbreviate. simpl_ret_assert. subst n. apply ENTAIL_refl.
Qed.

(* the NULL-tolerant buffers: prim_out / prim_bytes of a nonempty list are data_at *)
Lemma ht4rd_out_nz sh (v: list val) p : Zlength v <> 0 ->
  prim_out sh v p = data_at sh (tarray tuchar (Zlength v)) v p.
Proof. intros H. unfold prim_out. destruct (Z.eq_dec (Zlength v) 0); [contradiction | reflexivity]. Qed.

Lemma ht4rd_pb_nz sh (bs: list byte) p : Zlength bs <> 0 ->
  prim_bytes sh bs p = data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) p.
Proof. intros H. unfold prim_bytes. destruct (Z.eq_dec (Zlength bs) 0); [contradiction | reflexivity]. Qed.

Lemma ht4rd_pb_nil sh p : prim_bytes sh [] p = emp.
Proof. reflexivity. Qed.

Lemma ht4rd_out_nil sh p : prim_out sh [] p = emp.
Proof. reflexivity. Qed.

Lemma ht4rd_pb_of sh (bs: list byte) p :
  data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) p |-- prim_bytes sh bs p.
Proof.
  unfold prim_bytes. destruct (Z.eq_dec (Zlength bs) 0) as [E | E]; [| apply derives_refl].
  rewrite E. apply Zlength_nil_inv in E. subst bs. apply data_at_zero_array_inv; auto.
Qed.

Lemma ht4rd_pb_to sh (bs: list byte) p : isptr p ->
  prim_bytes sh bs p |-- data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) p.
Proof.
  intros Hp. unfold prim_bytes. destruct (Z.eq_dec (Zlength bs) 0) as [E | E]; [| apply derives_refl].
  rewrite E. apply Zlength_nil_inv in E. subst bs. rewrite data_at_zero_array_eq; auto.
Qed.

Lemma ht4rd_out_undef sh (old: list val) n p : Zlength old = n ->
  prim_out sh old p |-- prim_out sh (Zrepeat Vundef n) p.
Proof.
  intros H. pose proof (Zlength_nonneg old). unfold prim_out. rewrite Zlength_Zrepeat by lia.
  rewrite H. destruct (Z.eq_dec n 0) as [E | E]; [apply derives_refl |].
  apply data_at_data_at_.
Qed.

Lemma ht4rd_xor_body (mp: ident) : haead_hyps ->
  semax_body [] (ht4r_Gprog mp) HDX.f_ref_chacha20_xor ref_chacha20_xor_spec_n.
Proof.
  intros HH. start_function.
  pose proof (ht4rd_x_xor_len HH key nonce m) as HXl.
  pose proof (ht4rd_x_block_fact HH key nonce m) as Hfact.
  remember (chacha_xor 10 (chacha_advance (aead_st key nonce) 1) m) as X eqn:HXe.
  change (ht4rd_x_eq X (chacha_xor 10 (chacha_advance (aead_st key nonce) 1) m)) in HXe.
  change (ht4rd_x_fact X key nonce m) in Hfact. clear HH.
  destruct (Z.eq_dec (Zlength m) 0) as [Hm0 | Hm0].
  { (* empty: the loop exits at once; dst and src are emp *)
    assert (HX0: X = []) by (apply Zlength_nil_inv; lia).
    rewrite Hm0. change (Zrepeat Vundef 0) with (@nil val). rewrite ht4rd_out_nil.
    apply Zlength_nil_inv in Hm0. subst m. rewrite ht4rd_pb_nil.
    forward. forward.
    forward_while (PROP () LOCAL (temp HDX._pos (Vlong (Int64.repr 0)); temp HDX._ctr (Vint (Int.repr 1));
        lvar HDX._blk (tarray tuchar 64) v_blk; temp HDX._dst dst; temp HDX._src src;
        temp HDX._len (Vlong (Int64.repr 0)); temp HDX._key kp; temp HDX._nonce (Vlong (Int64.repr nonce)))
      SEP (data_at_ Tsh (tarray tuchar 64) v_blk; data_at ksh (tarray tuchar 32) (map Vubyte key) kp)).
    - entailer!.
    - entailer!.
    - exfalso. vm_compute in HRE. discriminate.
    - forward. rewrite HX0. entailer!. }
  rewrite (ht4rd_out_nz dsh (Zrepeat Vundef (Zlength m)) dst) by (rewrite Zlength_Zrepeat by list_solve; auto).
  rewrite Zlength_Zrepeat by list_solve. rewrite (ht4rd_pb_nz ssh m src) by auto.
  forward. forward.
  forward_while (EX b: Z,
      PROP (0 <= b)
      LOCAL (temp HDX._pos (Vlong (Int64.repr (Z.min (64 * b) (Zlength m)))); temp HDX._ctr (Vint (Int.repr (1 + b)));
        lvar HDX._blk (tarray tuchar 64) v_blk; temp HDX._dst dst; temp HDX._src src;
        temp HDX._len (Vlong (Int64.repr (Zlength m))); temp HDX._key kp; temp HDX._nonce (Vlong (Int64.repr nonce)))
      SEP (data_at_ Tsh (tarray tuchar 64) v_blk;
        data_at dsh (tarray tuchar (Zlength m))
          (map Vubyte (sublist 0 (Z.min (64 * b) (Zlength m)) X) ++ Zrepeat Vundef (Zlength m - Z.min (64 * b) (Zlength m))) dst;
        data_at ssh (tarray tuchar (Zlength m)) (map Vubyte m) src;
        data_at ksh (tarray tuchar 32) (map Vubyte key) kp))%assert.
  - Exists 0. replace (Z.min (64 * 0) (Zlength m)) with 0 by (pose proof (Zlength_nonneg m); lia).
    rewrite sublist_nil, Z.sub_0_r. entailer!.
  - entailer!.
  - pose proof (Zlength_nonneg m).
    unfold Int64.ltu in HRE. rewrite !Int64.unsigned_repr in HRE by rep_lia. destruct (zlt _ _) in HRE; [| discriminate].
    assert (Hb: 64 * b < Zlength m) by lia.
    replace (Z.min (64 * b) (Zlength m)) with (64 * b) by lia.
    eapply semax_seq'.
    { eapply semax_pre; [| apply (ht4rd_x_call_ok _ mp ksh kp key nonce v_blk b (Vlong (Int64.repr (64 * b)))
         dst src (Vlong (Int64.repr (Zlength m)))
         (data_at dsh (tarray tuchar (Zlength m)) (map Vubyte (sublist 0 (64 * b) X) ++ Zrepeat Vundef (Zlength m - 64 * b)) dst)
         (data_at ssh (tarray tuchar (Zlength m)) (map Vubyte m) src)); auto].
      entailer!. }
    unfold MORE_COMMANDS, abbreviate.
    assert (Hj: forall j, 0 <= j < Z.min 64 (Zlength m - 64 * b) ->
        Znth (64 * b + j) X = Byte.xor (Znth (64 * b + j) m) (Znth j (ht4rd_x_blk key nonce b)))
      by (intros; apply Hfact; auto).
    pose proof (ht4rd_x_blk_len key nonce b) as HBl.
    clear Hfact. generalize dependent (ht4rd_x_blk key nonce b). intros B Hj HBl.
    eapply semax_seq'.
    { eapply semax_pre; [| apply (ht4rd_x_inner_ok _ mp dsh dst ssh src m X B (64 * b) v_blk kp
         (Vlong (Int64.repr nonce)) (Vint (Int.repr (1 + b))) (data_at ksh (tarray tuchar 32) (map Vubyte key) kp));
         [exact SH | exact SH0 | exact H1 | lia | exact HXl | exact HBl | exact Hj]].
      clear Hj. entailer!. }
    clear Hj.
    unfold MORE_COMMANDS, abbreviate.
    forward. forward.
    Exists (b + 1).
    replace (Z.min (64 * (b + 1)) (Zlength m)) with (64 * b + Z.min 64 (Zlength m - 64 * b)) by lia.
    replace (1 + (b + 1)) with (1 + b + 1) by lia.
    entailer!.
  - unfold Int64.ltu in HRE. pose proof (Zlength_nonneg m).
    rewrite !Int64.unsigned_repr in HRE by rep_lia. destruct (zlt _ _) in HRE; [discriminate |].
    replace (Z.min (64 * b) (Zlength m)) with (Zlength m) by lia.
    rewrite sublist_same, Z.sub_diag by lia. change (Zrepeat Vundef 0) with (@nil val). rewrite app_nil_r.
    forward.
  rewrite (ht4rd_out_nz dsh (map Vubyte X) dst) by (rewrite Zlength_map; lia).
  rewrite (ht4rd_pb_nz ssh m src) by auto. rewrite Zlength_map, HXl.
  entailer!.
Qed.

(* ====================================================================== *)
(* part 2: ref_aead_decrypt (law prim_aead's haead_ref_body3.v, har_ -> ht4rd_d_)                     *)
(* ====================================================================== *)

(* splitting a byte array for exact-size callees (as hat_split of haead_tag_body3.v) *)
Lemma ht4rd_d_split sh n n1 n2 (l1 l2: list val) p : Zlength l1 = n1 -> Zlength l2 = n2 -> n = n1 + n2 ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) (l1 ++ l2) p =
  (data_at sh (tarray tuchar n1) l1 p * data_at sh (tarray tuchar n2) l2 (offset_val n1 p))%logic.
Proof.
  intros H1 H2 Hn Hf. subst n1 n2 n.
  rewrite (split2_data_at_Tarray_app (Zlength l1) (Zlength l1 + Zlength l2) sh tuchar l1 l2);
    [| reflexivity | exact (ltac:(lia) : Zlength (A:=val) l2 = Zlength l1 + Zlength l2 - Zlength l1)].
  replace (Zlength l1 + Zlength l2 - Zlength l1) with (Zlength l2) by lia.
  rewrite field_address0_offset.
  2: { pose proof (Zlength_nonneg l1); pose proof (Zlength_nonneg l2). auto with field_compatible. }
  simpl nested_field_offset. f_equal. f_equal. f_equal. simpl. lia.
Qed.

Lemma ht4rd_d_dec_short key nonce a c : Zlength c < 16 -> aead_dec key nonce a c = None.
Proof. intros. unfold aead_dec, aead_dec_st. destruct (Z_lt_dec (Zlength c) 16); [reflexivity | lia]. Qed.

Lemma ht4rd_d_dec_long key nonce a c : 16 <= Zlength c ->
  aead_dec key nonce a c =
  if list_eq_dec Byte.eq_dec (poly1305_tag (aead_otk (aead_st key nonce)) (aead_mac_data a (sublist 0 (Zlength c - 16) c)))
       (sublist (Zlength c - 16) (Zlength c) c)
  then Some (chacha_xor 10 (chacha_advance (aead_st key nonce) 1) (sublist 0 (Zlength c - 16) c)) else None.
Proof. intros. unfold aead_dec, aead_dec_st. destruct (Z_lt_dec (Zlength c) 16); [lia | reflexivity]. Qed.

Lemma ht4rd_d_len_eq sh n (l: list byte) p : Zlength l = n ->
  data_at sh (tarray tuchar n) (map Vubyte l) p = data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p.
Proof. intros; subst; reflexivity. Qed.

Lemma ht4rd_d_split_c sh (c: list byte) n p : 0 <= n <= Zlength c ->
  field_compatible (tarray tuchar (Zlength c)) [] p ->
  data_at sh (tarray tuchar (Zlength c)) (map Vubyte c) p =
  (data_at sh (tarray tuchar (Zlength (sublist 0 n c))) (map Vubyte (sublist 0 n c)) p *
   data_at sh (tarray tuchar (Zlength (sublist n (Zlength c) c))) (map Vubyte (sublist n (Zlength c) c))
     (offset_val n p))%logic.
Proof.
  intros Hn Hf.
  transitivity (data_at sh (tarray tuchar (Zlength c))
    (map Vubyte (sublist 0 n c) ++ map Vubyte (sublist n (Zlength c) c)) p).
  { rewrite <- map_app, sublist_rejoin, sublist_same by lia. reflexivity. }
  replace (offset_val n p) with (offset_val (Zlength (sublist 0 n c)) p) by (f_equal; list_solve).
  apply ht4rd_d_split; [list_solve | list_solve | list_solve | auto].
Qed.

(* an equation entailer! does not substitute (keeps model terms out of the entailments) *)
Definition ht4rd_d_eq {A: Type} (x y: A) : Prop := x = y.

Ltac ht4rd_d_opaque t := with_strategy opaque [aead_dec aead_enc poly1305_tag chacha_xor aead_otk aead_mac_data aead_st ht4rd_d_eq] t.

Ltac ht4rd_d_ent := with_strategy opaque [aead_dec aead_enc poly1305_tag chacha_xor aead_otk aead_mac_data aead_st] entailer!.

Lemma ht4rd_dec_body (mp: ident) (HH: haead_hyps) :
  semax_body [] (ht4r_Gprog mp) HDX.f_ref_aead_decrypt (ref_aead_decrypt_spec_n W_prim_aead mp).
Proof.
  start_function.
  forward_if (PROP (16 <= Zlength c)
    LOCAL (lvar HDX._tag (tarray tuchar 16) v_tag; gvars gv; temp HDX._dst dst; temp HDX._src src;
      temp HDX._len (Vlong (Int64.repr (Zlength c))); temp HDX._ad ad;
      temp HDX._adlen (Vlong (Int64.repr (Zlength a))); temp HDX._nonce (Vlong (Int64.repr nonce));
      temp HDX._key kp)
    SEP (data_at_ Tsh (tarray tuchar 16) v_tag; prim_out dsh old dst;
      prim_bytes ssh c src; prim_bytes ash a ad;
      data_at ksh (tarray tuchar 32) (map Vubyte key) kp; ht4_minusp mp gv)).
  { rewrite !Int64.unsigned_repr in H4 by rep_lia.
    forward. rewrite ht4rd_d_dec_short by lia. ht4rd_d_ent. }
  { rewrite !Int64.unsigned_repr in H4 by rep_lia.
    forward. ht4rd_d_ent. }
  Intros.
  rewrite (ht4rd_pb_nz ssh c src) by lia.
  assert_PROP (field_compatible (tarray tuchar (Zlength c)) [] src) as Hfc by ht4rd_d_ent.
  assert (Hsrc: isptr src) by (destruct Hfc; auto).
  rewrite (ht4rd_d_split_c ssh c (Zlength c - 16)) by (auto; lia).
  flatten_sepcon_in_SEP.
  remember (sublist 0 (Zlength c - 16) c) as ct eqn:Hct.
  remember (sublist (Zlength c - 16) (Zlength c) c) as tg eqn:Htg.
  assert (Hctl: Zlength ct = Zlength c - 16) by (subst ct; list_solve).
  assert (Htgl: Zlength tg = 16) by (subst tg; list_solve).
  change (ht4rd_d_eq ct (sublist 0 (Zlength c - 16) c)) in Hct.
  change (ht4rd_d_eq tg (sublist (Zlength c - 16) (Zlength c) c)) in Htg.
  sep_apply (ht4rd_pb_of ssh ct src).
  forward_call (Tsh, v_tag, ksh, kp, key, nonce, ash, ad, a, ssh, src, ct, gv).
  { rewrite Hctl. ht4rd_d_ent. }
  remember (poly1305_tag (aead_otk (aead_st key nonce)) (aead_mac_data a ct)) as T eqn:HT.
  change (ht4rd_d_eq T (poly1305_tag (aead_otk (aead_st key nonce)) (aead_mac_data a ct))) in HT.
  assert_PROP (Zlength T = 16) as HTl by (ht4rd_d_ent; rewrite Zlength_map in *; auto).
  rewrite (ht4rd_d_len_eq Tsh 16 T) by auto.
  remember (offset_val (Zlength c - 16) src) as q eqn:Hq.
  change (ht4rd_d_eq q (offset_val (Zlength c - 16) src)) in Hq.
  ht4rd_d_opaque ltac:(forward_call (Tsh, v_tag, T, ssh, q, tg)).
  { go_lower; apply prop_right; unfold ht4rd_d_eq in Hq; subst q; rewrite HTl; destruct src; try contradiction; cbn.
    f_equal. f_equal. f_equal. unfold Ptrofs.of_int64, Ptrofs.of_ints.
    rewrite Int64.unsigned_repr by rep_lia. rewrite Int.signed_repr by rep_lia.
    rewrite !(Ptrofs.mul_commut (Ptrofs.repr 1)), !Ptrofs.mul_one.
    rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc. f_equal. rewrite <- Ptrofs.sub_add_opp.
    unfold Ptrofs.sub. rewrite !Ptrofs.unsigned_repr by rep_lia. reflexivity. }
  forward_if (PROP (T = tg)
    LOCAL (lvar HDX._tag (tarray tuchar 16) v_tag; gvars gv; temp HDX._dst dst; temp HDX._src src;
      temp HDX._len (Vlong (Int64.repr (Zlength c))); temp HDX._ad ad;
      temp HDX._adlen (Vlong (Int64.repr (Zlength a))); temp HDX._nonce (Vlong (Int64.repr nonce));
      temp HDX._key kp)
    SEP (data_at Tsh (tarray tuchar (Zlength T)) (map Vubyte T) v_tag;
      data_at ssh (tarray tuchar (Zlength tg)) (map Vubyte tg) q;
      data_at ksh (tarray tuchar 32) (map Vubyte key) kp;
      prim_bytes ash a ad; prim_bytes ssh ct src; ht4_minusp mp gv; prim_out dsh old dst)).
  { destruct (list_eq_dec Byte.eq_dec T tg) as [E | E]; [match goal with Hb: Int.one = Int.zero |- _ => inv Hb end |].
    assert (Hdec: aead_dec key nonce a c = None).
    { rewrite ht4rd_d_dec_long by lia. unfold ht4rd_d_eq in Hct, Htg, HT.
      rewrite <- Hct, <- Htg, <- HT. destruct list_eq_dec; [contradiction | reflexivity]. }
    rewrite HTl. sep_apply (data_at_data_at_ Tsh (tarray tuchar 16) (map Vubyte T) v_tag).
    gather_SEP (prim_bytes ssh _ src) (data_at ssh _ _ q).
    replace_SEP 0 (prim_bytes ssh c src).
    { go_lower. unfold ht4rd_d_eq in Hct, Htg, Hq. rewrite (ht4rd_pb_nz ssh c src) by lia.
      rewrite (ht4rd_d_split_c ssh c (Zlength c - 16)) by (auto; lia).
      rewrite <- Hct, <- Htg, <- Hq. cancel. apply ht4rd_pb_to; auto. }
    clear Hct Htg HT Hq.
    subst POSTCONDITION; unfold abbreviate; rewrite Hdec.
    forward. cancel. }
  { destruct (list_eq_dec Byte.eq_dec T tg) as [E | E]; [| contradiction].
    forward. ht4rd_d_ent. }
  Intros. subst tg.
  assert (Hdec: aead_dec key nonce a c = Some (chacha_xor 10 (chacha_advance (aead_st key nonce) 1) ct)).
  { rewrite ht4rd_d_dec_long by lia. unfold ht4rd_d_eq in Hct, Htg, HT.
    rewrite <- Hct, <- Htg, <- HT. destruct list_eq_dec; [reflexivity | contradiction]. }
  clear HT.
  rewrite HTl. sep_apply (data_at_data_at_ Tsh (tarray tuchar 16) (map Vubyte T) v_tag).
  sep_apply (ht4rd_out_undef dsh old (Zlength ct) dst); [lia |].
  forward_call (dsh, dst, ssh, src, ct, ksh, kp, key, nonce).
  { rewrite Hctl. ht4rd_d_ent. }
  gather_SEP (prim_bytes ssh _ src) (data_at ssh _ _ q).
  replace_SEP 0 (prim_bytes ssh c src).
  { go_lower. unfold ht4rd_d_eq in Hct, Htg, Hq. rewrite (ht4rd_pb_nz ssh c src) by lia.
    rewrite (ht4rd_d_split_c ssh c (Zlength c - 16)) by (auto; lia).
    rewrite <- Hct, <- Htg, <- Hq, HTl. cancel. apply ht4rd_pb_to; auto. }
  clear Hct Htg Hq.
  subst POSTCONDITION; unfold abbreviate; rewrite Hdec.
  forward. cancel.
Qed.

Lemma ht4r_dec_bodies (mp: ident) : haead_hyps ->
  semax_body [] (ht4r_Gprog mp) WgNoise.harness.x_prim_aead.code.f_ref_chacha20_xor ref_chacha20_xor_spec_n /\
  semax_body [] (ht4r_Gprog mp) WgNoise.harness.x_prim_aead.code.f_ref_aead_decrypt
    (ref_aead_decrypt_spec_n W_prim_aead mp).
Proof.
  intros HH. split; [apply ht4rd_xor_body | apply ht4rd_dec_body]; exact HH.
Qed.
