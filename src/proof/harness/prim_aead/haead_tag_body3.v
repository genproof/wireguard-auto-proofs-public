(* law prim_aead: rp_padded, ref_aead_tag, ref_chacha20_xor of common.h. *)
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

(* ====================================================================== *)
(* part 1: rp_padded                                                       *)
(* ====================================================================== *)

Module HAC := WgNoise.harness.x_prim_aead.code.

(* the statements of rp_padded: pos = 0; while; if (one lemma per call, abstract frames: recipe-big-straightline) *)
Definition hat_pad_while : statement :=
  ltac:(let b := eval cbv delta [HAC.f_rp_padded fn_body] beta iota in (fn_body HAC.f_rp_padded) in
        match b with Ssequence _ (Ssequence ?r _) => exact r end).
Definition hat_pad_call1 : statement :=
  ltac:(let b := eval cbv delta [HAC.f_rp_padded fn_body] beta iota in (fn_body HAC.f_rp_padded) in
        match b with Ssequence _ (Ssequence (Swhile _ (Ssequence ?r _)) _) => exact r end).
Definition hat_pad_if : statement :=
  ltac:(let b := eval cbv delta [HAC.f_rp_padded fn_body] beta iota in (fn_body HAC.f_rp_padded) in
        match b with Ssequence _ (Ssequence _ ?r) => exact r end).
Definition hat_pad_set : statement :=
  ltac:(let b := eval cbv delta [HAC.f_rp_padded fn_body] beta iota in (fn_body HAC.f_rp_padded) in
        match b with Ssequence _ (Ssequence _ (Sifthenelse _ (Ssequence ?r _) _)) => exact r end).
Definition hat_pad_copy : statement :=
  ltac:(let b := eval cbv delta [HAC.f_rp_padded fn_body] beta iota in (fn_body HAC.f_rp_padded) in
        match b with Ssequence _ (Ssequence _ (Sifthenelse _ (Ssequence _ (Ssequence ?r _)) _)) => exact r end).
Definition hat_pad_call2 : statement :=
  ltac:(let b := eval cbv delta [HAC.f_rp_padded fn_body] beta iota in (fn_body HAC.f_rp_padded) in
        match b with Ssequence _ (Ssequence _ (Sifthenelse _ (Ssequence _ (Ssequence _ ?r)) _)) => exact r end).

Definition hat_pad_D : tycontext := func_tycontext HAC.f_rp_padded haead_V haead_Gprog nil.

(* the full blocks of rp_padded *)
Definition hat_pad_f (r: list int) (buf: list byte) : list int -> Z -> list int :=
  fun h k => hrp_block r h (sublist (16 * k) (16 * k + 16) buf).

Lemma hat_block_len (HH: haead_hyps) r h m : Zlength h = 17 -> Zlength (hrp_block r h m) = 17.
Proof.
  intros. destruct HH as ((_ & _ & Hm & _) & _). unfold hrp_block. apply Hm; auto.
Qed.

Lemma hat_loop_len (HH: haead_hyps) r buf h k : 0 <= k -> Zlength h = 17 ->
  Zlength (hrp_loop (hat_pad_f r buf) k h) = 17.
Proof.
  intros Hk Hh. pattern k; apply natlike_ind; auto.
  intros x Hx IH. unfold Z.succ. rewrite hrp_loop_succ by lia. unfold hat_pad_f at 1.
  apply hat_block_len; auto.
Qed.

Lemma hat_loop_succ r buf h k : 0 <= k ->
  hrp_loop (hat_pad_f r buf) (k + 1) h = hrp_block r (hrp_loop (hat_pad_f r buf) k h) (sublist (16 * k) (16 * k + 16) buf).
Proof. intros. rewrite hrp_loop_succ by lia. reflexivity. Qed.

Lemma hat_split sh n n1 n2 (l1 l2: list val) p : Zlength l1 = n1 -> Zlength l2 = n2 -> n = n1 + n2 ->
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

(* rp_block(p, in + pos) *)
Lemma hat_pad_call1_ok (Espec: OracleKind) sh p r h s ish ip buf pos vb Fa :
  writable_share sh -> readable_share ish -> 0 <= pos -> pos + 16 <= Zlength buf ->
  Zlength buf <= Int64.max_signed -> Zlength r = 17 -> Zlength h = 17 ->
  semax hat_pad_D
    (PROP () LOCAL (temp HAC._pos (Vlong (Int64.repr pos)); lvar HAC._b (tarray tuchar 16) vb;
      temp HAC._p p; temp HAC._in ip; temp HAC._len (Vlong (Int64.repr (Zlength buf))))
    SEP (Fa; data_at sh t_rpoly (rpoly_val r h s) p;
      data_at ish (tarray tuchar (Zlength buf)) (map Vubyte buf) ip))
    hat_pad_call1
    (normal_ret_assert
      (PROP () LOCAL (temp HAC._pos (Vlong (Int64.repr pos)); lvar HAC._b (tarray tuchar 16) vb;
        temp HAC._p p; temp HAC._in ip; temp HAC._len (Vlong (Int64.repr (Zlength buf))))
      SEP (data_at sh t_rpoly (rpoly_val r (hrp_block r h (sublist pos (pos + 16) buf)) s) p;
        data_at ish (tarray tuchar (Zlength buf)) (map Vubyte buf) ip; Fa))).
Proof.
  intros SH SH0 Hp Hp16 Hmax Hr Hh.
  unfold hat_pad_call1, hat_pad_D. abbreviate_semax.
  forward_call (sh, p, r, h, s, ish, ip, buf, pos).
  { entailer!. }
  entailer!.
Qed.

Lemma hat_sub_repr a b : 0 <= b <= a -> a <= Int64.max_unsigned ->
  Int64.sub (Int64.repr a) (Int64.repr b) = Int64.repr (a - b).
Proof.
  intros. unfold Int64.sub. rewrite (Int64.unsigned_repr a), (Int64.unsigned_repr b) by rep_lia. reflexivity.
Qed.

(* the loop over the full blocks *)
Lemma hat_pad_while_ok (Espec: OracleKind) (HH: haead_hyps) sh p r h s ish ip buf vb vpos :
  writable_share sh -> readable_share ish -> Zlength buf <= Int64.max_signed -> Zlength r = 17 ->
  Zlength h = 17 -> vpos = Vlong (Int64.repr 0) ->
  semax hat_pad_D
    (PROP () LOCAL (temp HAC._pos vpos; lvar HAC._b (tarray tuchar 16) vb;
      temp HAC._p p; temp HAC._in ip; temp HAC._len (Vlong (Int64.repr (Zlength buf))))
    SEP (data_at_ Tsh (tarray tuchar 16) vb; data_at sh t_rpoly (rpoly_val r h s) p;
      data_at ish (tarray tuchar (Zlength buf)) (map Vubyte buf) ip))
    hat_pad_while
    (normal_ret_assert (EX k: Z,
      PROP (0 <= k; 16 * k <= Zlength buf; Zlength buf - 16 * k < 16)
      LOCAL (temp HAC._pos (Vlong (Int64.repr (16 * k))); lvar HAC._b (tarray tuchar 16) vb;
        temp HAC._p p; temp HAC._in ip; temp HAC._len (Vlong (Int64.repr (Zlength buf))))
      SEP (data_at_ Tsh (tarray tuchar 16) vb;
        data_at sh t_rpoly (rpoly_val r (hrp_loop (hat_pad_f r buf) k h) s) p;
        data_at ish (tarray tuchar (Zlength buf)) (map Vubyte buf) ip))%assert).
Proof.
  intros SH SH0 Hmax Hr Hh Hvpos. subst vpos.
  unfold hat_pad_while, hat_pad_D. abbreviate_semax.
  forward_while (EX k: Z,
      PROP (0 <= k; 16 * k <= Zlength buf)
      LOCAL (temp HAC._pos (Vlong (Int64.repr (16 * k))); lvar HAC._b (tarray tuchar 16) vb;
        temp HAC._p p; temp HAC._in ip; temp HAC._len (Vlong (Int64.repr (Zlength buf))))
      SEP (data_at_ Tsh (tarray tuchar 16) vb;
        data_at sh t_rpoly (rpoly_val r (hrp_loop (hat_pad_f r buf) k h) s) p;
        data_at ish (tarray tuchar (Zlength buf)) (map Vubyte buf) ip))%assert.
  { Exists 0. entailer!. }
  { entailer!. }
  { eapply semax_seq'.
    { apply hat_pad_call1_ok; auto; try lia. apply hat_loop_len; auto. }
    unfold MORE_COMMANDS, abbreviate. forward.
    Exists (k + 1). entailer!.
    { f_equal. f_equal. lia. }
    rewrite hat_loop_succ by lia. apply derives_refl. }
  forward. Exists k. entailer!.
Qed.

(* bytes_set(b, 0, 16) *)
Lemma hat_pad_set_ok (Espec: OracleKind) vpos vb p ip vlen Fa Fb :
  semax hat_pad_D
    (PROP () LOCAL (temp HAC._pos vpos; lvar HAC._b (tarray tuchar 16) vb;
      temp HAC._p p; temp HAC._in ip; temp HAC._len vlen)
    SEP (data_at_ Tsh (tarray tuchar 16) vb; Fa; Fb))
    hat_pad_set
    (normal_ret_assert
      (PROP () LOCAL (temp HAC._pos vpos; lvar HAC._b (tarray tuchar 16) vb;
        temp HAC._p p; temp HAC._in ip; temp HAC._len vlen)
      SEP (data_at Tsh (tarray tuchar 16) (Zrepeat (Vubyte (Byte.repr 0)) 16) vb; Fa; Fb))).
Proof.
  unfold hat_pad_set, hat_pad_D. abbreviate_semax.
  forward_call (Tsh, vb, 0, 16).
  entailer!.
Qed.

(* bytes_copy(b, in + pos, len - pos) *)
Lemma hat_pad_copy_ok (Espec: OracleKind) vb p ish ip pos len bs Fa Fb Fc :
  readable_share ish -> 0 <= pos -> len = pos + Zlength bs -> len <= Int64.max_signed ->
  semax hat_pad_D
    (PROP () LOCAL (temp HAC._pos (Vlong (Int64.repr pos)); lvar HAC._b (tarray tuchar 16) vb;
      temp HAC._p p; temp HAC._in ip; temp HAC._len (Vlong (Int64.repr len)))
    SEP (data_at_ Tsh (tarray tuchar (Zlength bs)) vb;
      data_at ish (tarray tuchar (Zlength bs)) (map Vubyte bs) (offset_val pos ip); Fa; Fb; Fc))
    hat_pad_copy
    (normal_ret_assert
      (PROP () LOCAL (temp HAC._pos (Vlong (Int64.repr pos)); lvar HAC._b (tarray tuchar 16) vb;
        temp HAC._p p; temp HAC._in ip; temp HAC._len (Vlong (Int64.repr len)))
      SEP (data_at Tsh (tarray tuchar (Zlength bs)) (map Vubyte bs) vb;
        data_at ish (tarray tuchar (Zlength bs)) (map Vubyte bs) (offset_val pos ip); Fa; Fb; Fc))).
Proof.
  intros SH0 Hp Hl Hmax.
  pose proof (Zlength_nonneg bs).
  unfold hat_pad_copy, hat_pad_D. abbreviate_semax.
  forward_call (Tsh, vb, ish, offset_val pos ip, bs).
  { assert_PROP (isptr (offset_val pos ip)) as Hip by entailer!. destruct ip; try contradiction.
    entailer!. simpl. replace (pos + Zlength bs - pos) with (Zlength bs) by lia.
    unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by rep_lia. rewrite Ptrofs.mul_commut.
    change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.mul_one. reflexivity. }
  entailer!.
Qed.

(* rp_block(p, b) *)
Lemma hat_pad_call2_ok (Espec: OracleKind) sh p r h s vb bl vpos ip vlen Fa Fb :
  writable_share sh -> Zlength r = 17 -> Zlength h = 17 -> Zlength bl = 16 ->
  semax hat_pad_D
    (PROP () LOCAL (temp HAC._pos vpos; lvar HAC._b (tarray tuchar 16) vb;
      temp HAC._p p; temp HAC._in ip; temp HAC._len vlen)
    SEP (data_at Tsh (tarray tuchar (Zlength bl)) (map Vubyte bl) vb; data_at sh t_rpoly (rpoly_val r h s) p;
      Fa; Fb))
    hat_pad_call2
    (normal_ret_assert
      (PROP () LOCAL (temp HAC._pos vpos; lvar HAC._b (tarray tuchar 16) vb;
        temp HAC._p p; temp HAC._in ip; temp HAC._len vlen)
      SEP (data_at sh t_rpoly (rpoly_val r (hrp_block r h bl) s) p;
        data_at Tsh (tarray tuchar (Zlength bl)) (map Vubyte bl) vb; Fa; Fb))).
Proof.
  intros SH Hr Hh Hl.
  unfold hat_pad_call2, hat_pad_D. abbreviate_semax.
  forward_call (sh, p, r, h, s, Tsh, vb, bl, 0).
  rewrite (sublist_same 0 (0 + 16) bl) by lia.
  entailer!.
Qed.

(* the state after the if *)
Definition hat_pad_last (r h1: list int) (buf: list byte) (pos: Z) : list int :=
  if Z.eq_dec (Zlength buf - pos) 0 then h1
  else hrp_block r h1 (sublist pos (Zlength buf) buf ++ Zrepeat Byte.zero (16 - (Zlength buf - pos))).

Lemma hat_padded_eq r h buf k : 0 <= k -> 16 * k <= Zlength buf -> Zlength buf - 16 * k < 16 ->
  haead_padded r h buf = hat_pad_last r (hrp_loop (hat_pad_f r buf) k h) buf (16 * k).
Proof.
  intros. unfold haead_padded.
  assert (E: Zlength buf / 16 = k) by (symmetry; apply Z.div_unique with (r := Zlength buf - 16 * k); lia).
  unfold hat_pad_last, hat_pad_f. cbv zeta. rewrite E. reflexivity.
Qed.

Lemma hat_zrep_split (x: val) n : 0 <= n <= 16 -> Zrepeat x 16 = Zrepeat x n ++ Zrepeat x (16 - n).
Proof. intros. list_solve. Qed.

Lemma hat_buf_split (buf: list byte) pos : 0 <= pos <= Zlength buf ->
  map Vubyte buf = map Vubyte (sublist 0 pos buf) ++ map Vubyte (sublist pos (Zlength buf) buf).
Proof. intros. rewrite <- map_app, <- sublist_split, sublist_same by lia. reflexivity. Qed.

(* the last partial block *)
Lemma hat_pad_if_ok (Espec: OracleKind) (HH: haead_hyps) sh p r h1 s ish ip buf vb pos :
  writable_share sh -> readable_share ish -> Zlength buf <= Int64.max_signed -> Zlength r = 17 ->
  Zlength h1 = 17 -> 0 <= pos <= Zlength buf -> Zlength buf - pos < 16 ->
  semax hat_pad_D
    (PROP () LOCAL (temp HAC._pos (Vlong (Int64.repr pos)); lvar HAC._b (tarray tuchar 16) vb;
      temp HAC._p p; temp HAC._in ip; temp HAC._len (Vlong (Int64.repr (Zlength buf))))
    SEP (data_at_ Tsh (tarray tuchar 16) vb; data_at sh t_rpoly (rpoly_val r h1 s) p;
      data_at ish (tarray tuchar (Zlength buf)) (map Vubyte buf) ip))
    hat_pad_if
    (normal_ret_assert
      (PROP () LOCAL (temp HAC._pos (Vlong (Int64.repr pos)); lvar HAC._b (tarray tuchar 16) vb;
        temp HAC._p p; temp HAC._in ip; temp HAC._len (Vlong (Int64.repr (Zlength buf))))
      SEP (data_at_ Tsh (tarray tuchar 16) vb; data_at sh t_rpoly (rpoly_val r (hat_pad_last r h1 buf pos) s) p;
        data_at ish (tarray tuchar (Zlength buf)) (map Vubyte buf) ip))).
Proof.
  intros SH SH0 Hmax Hr Hh Hp Hlt.
  unfold hat_pad_if, hat_pad_D. abbreviate_semax.
  forward_if (PROP () LOCAL (temp HAC._pos (Vlong (Int64.repr pos)); lvar HAC._b (tarray tuchar 16) vb;
        temp HAC._p p; temp HAC._in ip; temp HAC._len (Vlong (Int64.repr (Zlength buf))))
      SEP (data_at_ Tsh (tarray tuchar 16) vb; data_at sh t_rpoly (rpoly_val r (hat_pad_last r h1 buf pos) s) p;
        data_at ish (tarray tuchar (Zlength buf)) (map Vubyte buf) ip)).
  - rewrite hat_sub_repr, !Int64.unsigned_repr in H by rep_lia.
    eapply semax_seq'; [apply hat_pad_set_ok |]. unfold MORE_COMMANDS, abbreviate.
    assert_PROP (field_compatible (tarray tuchar 16) [] vb) as Fvb by entailer!.
    assert_PROP (field_compatible (tarray tuchar (Zlength buf)) [] ip) as Fip by entailer!.
    rewrite (hat_zrep_split (Vubyte (Byte.repr 0)) (Zlength buf - pos)) by lia.
    rewrite (hat_split Tsh 16 (Zlength buf - pos) (16 - (Zlength buf - pos))) by (auto; try list_solve; lia).
    rewrite (hat_buf_split buf pos) by lia.
    rewrite (hat_split ish (Zlength buf) pos (Zlength buf - pos)) by (auto; try list_solve; lia).
    sep_apply (data_at_data_at_ Tsh (tarray tuchar (Zlength buf - pos))
      (Zrepeat (Vubyte (Byte.repr 0)) (Zlength buf - pos)) vb).
    assert (Hbs: Zlength (sublist pos (Zlength buf) buf) = Zlength buf - pos) by list_solve.
    eapply semax_seq'.
    { eapply semax_pre; [| apply (hat_pad_copy_ok _ vb p ish ip pos (Zlength buf) (sublist pos (Zlength buf) buf)
        (data_at Tsh (tarray tuchar (16 - (Zlength buf - pos))) (Zrepeat (Vubyte (Byte.repr 0)) (16 - (Zlength buf - pos)))
           (offset_val (Zlength buf - pos) vb))
        (data_at sh t_rpoly (rpoly_val r h1 s) p)
        (data_at ish (tarray tuchar pos) (map Vubyte (sublist 0 pos buf)) ip)); auto; lia].
      rewrite Hbs. entailer!. }
    unfold MORE_COMMANDS, abbreviate.
    assert (Hbl: Zlength (sublist pos (Zlength buf) buf ++ Zrepeat Byte.zero (16 - (Zlength buf - pos))) = 16)
      by list_solve.
    assert (Hz: map Vubyte (Zrepeat Byte.zero (16 - (Zlength buf - pos))) =
                Zrepeat (Vubyte (Byte.repr 0)) (16 - (Zlength buf - pos)))
      by (unfold Zrepeat; rewrite map_repeat; reflexivity).
    eapply semax_pre; [| eapply ConseqFacts.semax_post''; [| apply (hat_pad_call2_ok _ sh p r h1 s vb
      (sublist pos (Zlength buf) buf ++ Zrepeat Byte.zero (16 - (Zlength buf - pos)))
      (Vlong (Int64.repr pos)) ip (Vlong (Int64.repr (Zlength buf)))
      (data_at ish (tarray tuchar (Zlength buf)) (map Vubyte buf) ip) emp); auto]].
    { rewrite Hbs, Hbl, map_app, Hz.
      rewrite (hat_split Tsh 16 (Zlength buf - pos) (16 - (Zlength buf - pos))); auto; try list_solve; try lia.
      erewrite (hat_buf_split buf pos) by lia.
      rewrite (hat_split ish (Zlength buf) pos (Zlength buf - pos)); auto; try list_solve; try lia.
      entailer!. }
    unfold POSTCONDITION, abbreviate. simpl_ret_assert.
    unfold hat_pad_last. destruct (Z.eq_dec (Zlength buf - pos) 0); [lia |]. rewrite Hbl.
    entailer!.
  - rewrite hat_sub_repr, !Int64.unsigned_repr in H by rep_lia.
    forward. unfold hat_pad_last. destruct (Z.eq_dec (Zlength buf - pos) 0); [| lia]. entailer!.
Qed.

Lemma haead_tag_padded3 : haead_hyps ->
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_rp_padded rp_padded_spec.
Proof.
  intros HH.
  start_function.
  forward.
  eapply semax_seq'.
  { apply hat_pad_while_ok; auto. }
  Intros k. unfold MORE_COMMANDS, abbreviate.
  eapply ConseqFacts.semax_post''.
  2: { apply hat_pad_if_ok; auto; try lia. apply hat_loop_len; auto. }
  rewrite <- hat_padded_eq by auto.
  unfold POSTCONDITION, abbreviate. simpl_ret_assert. entailer!.
Qed.

(* ====================================================================== *)
(* part 2: ref_aead_tag                                                    *)
(* (helpers of this part go here, between the two banners)                 *)
(* ====================================================================== *)

Lemma htg_le64_len z : Zlength (le64_bytes z) = 8.
Proof. reflexivity. Qed.

Lemma htg_splice1 (l: list byte) : Zlength l = 8 ->
  haead_splice 0 l (Zrepeat Vundef 16) = map Vubyte l ++ Zrepeat Vundef 8.
Proof. intros. unfold haead_splice. list_solve. Qed.

Lemma htg_splice2 (l1 l2: list byte) : Zlength l1 = 8 -> Zlength l2 = 8 ->
  haead_splice 8 l2 (map Vubyte l1 ++ Zrepeat Vundef 8) = map Vubyte (l1 ++ l2).
Proof. intros. unfold haead_splice. list_solve. Qed.

(* model facts kept in the context during the body proof, as opaque predicates over variables: a model term
   in the context costs entailer!/forward_call ~14 s per sentence *)
Definition htg_F (key: list byte) (nonce: Z) (a ct blk: list byte) : Prop :=
  Zlength blk = 64 ->
  hrp_final_out (haead_tag_h blk a ct) (hrp_init_s blk) = poly1305_tag (aead_otk (aead_st key nonce)) (aead_mac_data a ct).
Definition htg_E1 (blk a: list byte) (h1: list int) : Prop := h1 = haead_padded (hrp_init_r blk) hrp_zero17 a.
Definition htg_E2 (blk: list byte) (h1: list int) (ct: list byte) (h2: list int) : Prop :=
  h2 = haead_padded (hrp_init_r blk) h1 ct.
Definition htg_EL (a ct L: list byte) : Prop := L = le64_bytes (Zlength a) ++ le64_bytes (Zlength ct).

Lemma htg_st_len key nonce : Zlength (aead_st key nonce) = 16.
Proof. reflexivity. Qed.

Lemma htg_fin (HH: haead_hyps) key nonce a ct blk :
  blk = chacha_block_bytes 10 (chacha_advance (aead_st key nonce) (Int.unsigned Int.zero)) ->
  htg_F key nonce a ct blk.
Proof.
  intros E. unfold htg_F. intros L. destruct HH as (_ & (_ & _ & _ & _ & Hmac & _) & _).
  rewrite Hmac by lia. subst blk. unfold aead_otk.
  rewrite Int.unsigned_zero, haead_advance_0 by apply htg_st_len. reflexivity.
Qed.

Lemma htg_close key nonce a ct blk h1 h2 L :
  htg_F key nonce a ct blk -> htg_E1 blk a h1 -> htg_E2 blk h1 ct h2 -> htg_EL a ct L -> Zlength blk = 64 ->
  hrp_final_out (hrp_block (hrp_init_r blk) h2 L) (hrp_init_s blk) =
  poly1305_tag (aead_otk (aead_st key nonce)) (aead_mac_data a ct).
Proof.
  unfold htg_F, htg_E1, htg_E2, htg_EL. intros Hfin E1 E2 EL Hbl.
  rewrite <- (Hfin Hbl). unfold haead_tag_h. subst h2 h1 L. reflexivity.
Qed.

Lemma htg_mk1 blk a h1 : h1 = haead_padded (hrp_init_r blk) hrp_zero17 a -> htg_E1 blk a h1.
Proof. exact (fun e => e). Qed.
Lemma htg_mk2 blk h1 ct h2 : h2 = haead_padded (hrp_init_r blk) h1 ct -> htg_E2 blk h1 ct h2.
Proof. exact (fun e => e). Qed.
Lemma htg_mkL a ct L : L = le64_bytes (Zlength a) ++ le64_bytes (Zlength ct) -> htg_EL a ct L.
Proof. exact (fun e => e). Qed.

#[local] Opaque htg_F htg_E1 htg_E2 htg_EL.

Lemma htg_r_len (HH: haead_hyps) blk : Zlength blk = 64 -> Zlength (hrp_init_r blk) = 17.
Proof. intros. destruct HH as ((_ & Hr & _) & _). apply Hr. lia. Qed.

Lemma htg_padded_len (HH: haead_hyps) r h buf : Zlength h = 17 -> Zlength (haead_padded r h buf) = 17.
Proof. intros. destruct HH as (_ & (_ & _ & _ & Hp & _) & _). apply Hp; auto. Qed.

Lemma htg_block_len (HH: haead_hyps) r h m : Zlength h = 17 -> Zlength (hrp_block r h m) = 17.
Proof. intros. destruct HH as ((_ & _ & Hm & _) & _). unfold hrp_block. apply Hm; auto. Qed.

Definition htg_block_stmt : statement :=
  ltac:(let b := eval cbv delta [WgNoise.harness.x_prim_aead.code.f_ref_aead_tag fn_body] beta iota in
          (fn_body WgNoise.harness.x_prim_aead.code.f_ref_aead_tag) in
        match b with Ssequence ?r _ => exact r end).

(* ref_chacha20_block(blk, key, 0, nonce): the block is abstracted, with the fact htg_F *)
Lemma htg_block_call (Espec: OracleKind) (HH: haead_hyps) tag ksh kp key nonce ad a cp ct gv v_p v_blk v_lens
    F1 F2 F3 F4 F5 F6 :
  readable_share ksh -> Zlength key = 32 -> 0 <= nonce <= Int64.max_unsigned ->
  semax (func_tycontext WgNoise.harness.x_prim_aead.code.f_ref_aead_tag haead_V haead_Gprog nil)
    (PROP () LOCAL (lvar WgNoise.harness.x_prim_aead.code._lens (tarray tuchar 16) v_lens;
      lvar WgNoise.harness.x_prim_aead.code._blk (tarray tuchar 64) v_blk;
      lvar WgNoise.harness.x_prim_aead.code._p (Tstruct WgNoise.harness.x_prim_aead.code._rpoly noattr) v_p;
      gvars gv; temp WgNoise.harness.x_prim_aead.code._tag tag; temp WgNoise.harness.x_prim_aead.code._key kp;
      temp WgNoise.harness.x_prim_aead.code._nonce (Vlong (Int64.repr nonce));
      temp WgNoise.harness.x_prim_aead.code._ad ad;
      temp WgNoise.harness.x_prim_aead.code._adlen (Vlong (Int64.repr (Zlength a)));
      temp WgNoise.harness.x_prim_aead.code._ct cp;
      temp WgNoise.harness.x_prim_aead.code._ctlen (Vlong (Int64.repr (Zlength ct))))
     SEP (F1; data_at_ Tsh (tarray tuchar 64) v_blk; F2; F3; data_at ksh (tarray tuchar 32) (map Vubyte key) kp;
      F4; F5; F6))
    htg_block_stmt
    (normal_ret_assert (EX blk: list byte,
      PROP (htg_F key nonce a ct blk; Zlength blk = 64)
      LOCAL (lvar WgNoise.harness.x_prim_aead.code._lens (tarray tuchar 16) v_lens;
        lvar WgNoise.harness.x_prim_aead.code._blk (tarray tuchar 64) v_blk;
        lvar WgNoise.harness.x_prim_aead.code._p (Tstruct WgNoise.harness.x_prim_aead.code._rpoly noattr) v_p;
        gvars gv; temp WgNoise.harness.x_prim_aead.code._tag tag; temp WgNoise.harness.x_prim_aead.code._key kp;
        temp WgNoise.harness.x_prim_aead.code._nonce (Vlong (Int64.repr nonce));
        temp WgNoise.harness.x_prim_aead.code._ad ad;
        temp WgNoise.harness.x_prim_aead.code._adlen (Vlong (Int64.repr (Zlength a)));
        temp WgNoise.harness.x_prim_aead.code._ct cp;
        temp WgNoise.harness.x_prim_aead.code._ctlen (Vlong (Int64.repr (Zlength ct))))
      SEP (data_at Tsh (tarray tuchar (Zlength blk)) (map Vubyte blk) v_blk;
        data_at ksh (tarray tuchar 32) (map Vubyte key) kp; F1; F2; F3; F4; F5; F6))%assert).
Proof.
  intros SH0 H H0.
  unfold htg_block_stmt. abbreviate_semax.
  forward_call (Tsh, v_blk, ksh, kp, key, Int.zero, nonce).
  remember (chacha_block_bytes 10 (chacha_advance (aead_st key nonce) (Int.unsigned Int.zero))) as blk eqn:Eblk.
  pose proof (htg_fin HH key nonce a ct blk Eblk) as Hfin. clear Eblk HH.
  assert_PROP (Zlength (map Vubyte blk) = 64) as Hbl by entailer!. rewrite Zlength_map in Hbl.
  Exists blk. rewrite Hbl. entailer!.
Qed.

(* the locals of ref_aead_tag (no temp changes after the entry) *)
Local Notation htg_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct :=
  [lvar WgNoise.harness.x_prim_aead.code._lens (tarray tuchar 16) v_lens;
   lvar WgNoise.harness.x_prim_aead.code._blk (tarray tuchar 64) v_blk;
   lvar WgNoise.harness.x_prim_aead.code._p (Tstruct WgNoise.harness.x_prim_aead.code._rpoly noattr) v_p;
   gvars gv; temp WgNoise.harness.x_prim_aead.code._tag tag; temp WgNoise.harness.x_prim_aead.code._key kp;
   temp WgNoise.harness.x_prim_aead.code._nonce (Vlong (Int64.repr nonce));
   temp WgNoise.harness.x_prim_aead.code._ad ad;
   temp WgNoise.harness.x_prim_aead.code._adlen (Vlong (Int64.repr (Zlength a)));
   temp WgNoise.harness.x_prim_aead.code._ct cp;
   temp WgNoise.harness.x_prim_aead.code._ctlen (Vlong (Int64.repr (Zlength ct)))].

Local Notation htg_D := (func_tycontext WgNoise.harness.x_prim_aead.code.f_ref_aead_tag haead_V haead_Gprog nil).

Definition htg_s1 : statement :=
  ltac:(let b := eval cbv delta [WgNoise.harness.x_prim_aead.code.f_ref_aead_tag fn_body] beta iota in
          (fn_body WgNoise.harness.x_prim_aead.code.f_ref_aead_tag) in
        match b with Ssequence _ (Ssequence ?r _) => exact r end).
Definition htg_s2 : statement :=
  ltac:(let b := eval cbv delta [WgNoise.harness.x_prim_aead.code.f_ref_aead_tag fn_body] beta iota in
          (fn_body WgNoise.harness.x_prim_aead.code.f_ref_aead_tag) in
        match b with Ssequence _ (Ssequence _ (Ssequence ?r _)) => exact r end).
Definition htg_s3 : statement :=
  ltac:(let b := eval cbv delta [WgNoise.harness.x_prim_aead.code.f_ref_aead_tag fn_body] beta iota in
          (fn_body WgNoise.harness.x_prim_aead.code.f_ref_aead_tag) in
        match b with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence ?r _))) => exact r end).
Definition htg_s4 : statement :=
  ltac:(let b := eval cbv delta [WgNoise.harness.x_prim_aead.code.f_ref_aead_tag fn_body] beta iota in
          (fn_body WgNoise.harness.x_prim_aead.code.f_ref_aead_tag) in
        match b with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence ?r _)))) => exact r end).
Definition htg_s5 : statement :=
  ltac:(let b := eval cbv delta [WgNoise.harness.x_prim_aead.code.f_ref_aead_tag fn_body] beta iota in
          (fn_body WgNoise.harness.x_prim_aead.code.f_ref_aead_tag) in
        match b with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence ?r _))))) => exact r end).
Definition htg_s6 : statement :=
  ltac:(let b := eval cbv delta [WgNoise.harness.x_prim_aead.code.f_ref_aead_tag fn_body] beta iota in
          (fn_body WgNoise.harness.x_prim_aead.code.f_ref_aead_tag) in
        match b with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence ?r _)))))) => exact r end).
Definition htg_s7 : statement :=
  ltac:(let b := eval cbv delta [WgNoise.harness.x_prim_aead.code.f_ref_aead_tag fn_body] beta iota in
          (fn_body WgNoise.harness.x_prim_aead.code.f_ref_aead_tag) in
        match b with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ ?r)))))) => exact r end).

Lemma htg_init_ok (Espec: OracleKind) (v_lens v_blk v_p: val) (gv: globals) (tag kp: val) (nonce: Z) (ad: val) (a: list byte)
    (cp: val) (ct: list byte) (blk: list byte) (F1: mpred) (F2: mpred) (F3: mpred) (F4: mpred) (F5: mpred) (F6: mpred) :
  Zlength blk = 64 ->
  semax htg_D (PROPx [] (LOCALx (htg_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [data_at Tsh (tarray tuchar (Zlength blk)) (map Vubyte blk) v_blk; F1; F2; data_at_ Tsh (Tstruct WgNoise.harness.x_prim_aead.code._rpoly noattr) v_p; F3; F4; F5; F6])))
    htg_s1
    (normal_ret_assert (PROPx [] (LOCALx (htg_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [data_at Tsh t_rpoly (rpoly_val (hrp_init_r blk) hrp_zero17 (hrp_init_s blk)) v_p; data_at Tsh (tarray tuchar (Zlength blk)) (map Vubyte blk) v_blk; F2; F3; F1; F4; F5; F6])))).
Proof.
  intros. unfold htg_s1. abbreviate_semax.
  forward_call (Tsh, v_p, Tsh, v_blk, blk).
  entailer!.
Qed.

Lemma htg_pad_ad_ok (Espec: OracleKind) (v_lens v_blk v_p: val) (gv: globals) (tag kp: val) (nonce: Z) (ad: val) (a: list byte)
    (cp: val) (ct: list byte) (ash: share) (r: list int) (h: list int) (s: list byte) (F1: mpred) (F2: mpred) (F3: mpred) (F4: mpred) (F5: mpred) (F6: mpred) :
  readable_share ash -> Zlength r = 17 -> Zlength h = 17 -> Zlength a <= Int64.max_signed ->
  semax htg_D (PROPx [] (LOCALx (htg_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [data_at Tsh t_rpoly (rpoly_val r h s) v_p; F1; F2; F3; F4; data_at ash (tarray tuchar (Zlength a)) (map Vubyte a) ad; F5; F6])))
    htg_s2
    (normal_ret_assert (PROPx [] (LOCALx (htg_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [data_at Tsh t_rpoly (rpoly_val r (haead_padded r h a) s) v_p; F1; F2; F3; F4; data_at ash (tarray tuchar (Zlength a)) (map Vubyte a) ad; F5; F6])))).
Proof.
  intros. unfold htg_s2. abbreviate_semax.
  forward_call (Tsh, v_p, r, h, s, ash, ad, a).
  entailer!.
Qed.

Lemma htg_pad_ct_ok (Espec: OracleKind) (v_lens v_blk v_p: val) (gv: globals) (tag kp: val) (nonce: Z) (ad: val) (a: list byte)
    (cp: val) (ct: list byte) (csh: share) (r: list int) (h: list int) (s: list byte) (F1: mpred) (F2: mpred) (F3: mpred) (F4: mpred) (F5: mpred) (F6: mpred) :
  readable_share csh -> Zlength r = 17 -> Zlength h = 17 -> Zlength ct <= Int64.max_signed ->
  semax htg_D (PROPx [] (LOCALx (htg_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [data_at Tsh t_rpoly (rpoly_val r h s) v_p; F1; F2; F3; F4; F5; data_at csh (tarray tuchar (Zlength ct)) (map Vubyte ct) cp; F6])))
    htg_s3
    (normal_ret_assert (PROPx [] (LOCALx (htg_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [data_at Tsh t_rpoly (rpoly_val r (haead_padded r h ct) s) v_p; F1; F2; F3; F4; F5; data_at csh (tarray tuchar (Zlength ct)) (map Vubyte ct) cp; F6])))).
Proof.
  intros. unfold htg_s3. abbreviate_semax.
  forward_call (Tsh, v_p, r, h, s, csh, cp, ct).
  entailer!.
Qed.

Lemma htg_le1_ok (Espec: OracleKind) (v_lens v_blk v_p: val) (gv: globals) (tag kp: val) (nonce: Z) (ad: val) (a: list byte)
    (cp: val) (ct: list byte) (F1: mpred) (F2: mpred) (F3: mpred) (F4: mpred) (F5: mpred) (F6: mpred) (F7: mpred) :
  
  Zlength a <= Int64.max_signed ->
  semax htg_D (PROPx [] (LOCALx (htg_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [F1; F2; data_at_ Tsh (tarray tuchar 16) v_lens; F3; F4; F5; F6; F7])))
    htg_s4
    (normal_ret_assert (PROPx [] (LOCALx (htg_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [F1; F2; data_at Tsh (tarray tuchar 16) (map Vubyte (le64_bytes (Zlength a)) ++ Zrepeat Vundef 8) v_lens; F3; F4; F5; F6; F7])))).
Proof.
  intros. unfold htg_s4. abbreviate_semax.
  replace_SEP 2 (data_at Tsh (tarray tuchar (Zlength (Zrepeat Vundef 16))) (Zrepeat Vundef 16) v_lens) by entailer!.
  assert_PROP (isptr v_lens) as Hpl by entailer!.
  forward_call (Tsh, v_lens, 0, Zrepeat Vundef 16, Zlength a).
  { rewrite Zlength_Zrepeat by lia; pose proof (Zlength_nonneg a); repeat split; rep_lia. }
  rewrite htg_splice1 by apply htg_le64_len.
  entailer!.
Qed.

Lemma htg_le2_ok (Espec: OracleKind) (v_lens v_blk v_p: val) (gv: globals) (tag kp: val) (nonce: Z) (ad: val) (a: list byte)
    (cp: val) (ct: list byte) (F1: mpred) (F2: mpred) (F3: mpred) (F4: mpred) (F5: mpred) (F6: mpred) (F7: mpred) :
  
  Zlength ct <= Int64.max_signed ->
  semax htg_D (PROPx [] (LOCALx (htg_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [F1; F2; data_at Tsh (tarray tuchar 16) (map Vubyte (le64_bytes (Zlength a)) ++ Zrepeat Vundef 8) v_lens; F3; F4; F5; F6; F7])))
    htg_s5
    (normal_ret_assert (PROPx [] (LOCALx (htg_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [F1; F2; data_at Tsh (tarray tuchar 16) (map Vubyte (le64_bytes (Zlength a) ++ le64_bytes (Zlength ct))) v_lens; F3; F4; F5; F6; F7])))).
Proof.
  intros. unfold htg_s5. abbreviate_semax.
  replace_SEP 2 (data_at Tsh (tarray tuchar (Zlength (map Vubyte (le64_bytes (Zlength a)) ++ Zrepeat Vundef 8)))
    (map Vubyte (le64_bytes (Zlength a)) ++ Zrepeat Vundef 8) v_lens)
    by (rewrite Zlength_app, Zlength_map, htg_le64_len; entailer!).
  assert_PROP (isptr v_lens) as Hpl by entailer!.
  forward_call (Tsh, v_lens, 8, map Vubyte (le64_bytes (Zlength a)) ++ Zrepeat Vundef 8, Zlength ct).
  rewrite htg_splice2 by apply htg_le64_len.
  rewrite Zlength_app, Zlength_map, htg_le64_len, Zlength_Zrepeat by lia. change (8 + 8) with 16.
  entailer!.
Qed.

Lemma htg_blk_ok (Espec: OracleKind) (v_lens v_blk v_p: val) (gv: globals) (tag kp: val) (nonce: Z) (ad: val) (a: list byte)
    (cp: val) (ct: list byte) (r: list int) (h: list int) (s: list byte) (L: list byte) (F1: mpred) (F2: mpred) (F3: mpred) (F4: mpred) (F5: mpred) (F6: mpred) :
  Zlength r = 17 -> Zlength h = 17 -> Zlength L = 16 ->
  semax htg_D (PROPx [] (LOCALx (htg_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [data_at Tsh t_rpoly (rpoly_val r h s) v_p; F1; data_at Tsh (tarray tuchar 16) (map Vubyte L) v_lens; F2; F3; F4; F5; F6])))
    htg_s6
    (normal_ret_assert (PROPx [] (LOCALx (htg_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [data_at Tsh t_rpoly (rpoly_val r (hrp_block r h L) s) v_p; F1; data_at Tsh (tarray tuchar 16) (map Vubyte L) v_lens; F2; F3; F4; F5; F6])))).
Proof.
  intros. unfold htg_s6. abbreviate_semax.
  match goal with HL: Zlength L = 16 |- _ =>
    replace_SEP 2 (data_at Tsh (tarray tuchar (Zlength L)) (map Vubyte L) v_lens) by (rewrite HL; entailer!);
    forward_call (Tsh, v_p, r, h, s, Tsh, v_lens, L, 0);
    rewrite (sublist_same 0 (0 + 16) L) by lia;
    rewrite HL end.
  entailer!.
Qed.

Lemma htg_final_ok (Espec: OracleKind) (v_lens v_blk v_p: val) (gv: globals) (tag kp: val) (nonce: Z) (ad: val) (a: list byte)
    (cp: val) (ct: list byte) (tsh: share) (r: list int) (h: list int) (s: list byte) (F1: mpred) (F2: mpred) (F3: mpred) (F4: mpred) (F5: mpred) :
  writable_share tsh -> Zlength r = 17 -> Zlength h = 17 ->
  semax htg_D (PROPx [] (LOCALx (htg_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [data_at Tsh t_rpoly (rpoly_val r h s) v_p; F1; F2; data_at_ tsh (tarray tuchar 16) tag; F3; F4; F5; haead_globals gv])))
    htg_s7
    (normal_ret_assert (PROPx [] (LOCALx (htg_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [data_at Tsh t_rpoly (rpoly_val r (hrp_final_h h s) s) v_p; F1; F2; data_at tsh (tarray tuchar 16) (map Vubyte (hrp_final_out h s)) tag; F3; F4; F5; haead_globals gv])))).
Proof.
  intros. unfold htg_s7. abbreviate_semax.
  forward_call (Tsh, v_p, r, h, s, tsh, tag, gv).
  entailer!.
Qed.

Lemma haead_tag_tag3 : haead_hyps ->
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_ref_aead_tag ref_aead_tag_spec.
Proof.
  intros HH.
  start_function.
  eapply semax_seq'.
  { apply htg_block_call; auto. }
  unfold MORE_COMMANDS, abbreviate. Intros blk. rename H3 into Hfin, H4 into Hbl.
  pose proof (htg_r_len HH blk Hbl) as Hr.
  assert (Hz: Zlength hrp_zero17 = 17) by reflexivity.
  pose proof (htg_padded_len HH (hrp_init_r blk) hrp_zero17 a Hz) as Hh1.
  pose proof (htg_padded_len HH (hrp_init_r blk) _ ct Hh1) as Hh2.
  pose proof (htg_block_len HH (hrp_init_r blk) _ (le64_bytes (Zlength a) ++ le64_bytes (Zlength ct)) Hh2) as Hh3.
  assert (HL: Zlength (le64_bytes (Zlength a) ++ le64_bytes (Zlength ct)) = 16)
    by (rewrite Zlength_app, !htg_le64_len; reflexivity).
  eapply semax_seq'. { apply htg_init_ok; auto. }
  eapply semax_seq'. { apply htg_pad_ad_ok; auto. }
  eapply semax_seq'. { apply htg_pad_ct_ok; auto. }
  eapply semax_seq'. { apply htg_le1_ok; auto. }
  eapply semax_seq'. { apply htg_le2_ok; auto. }
  eapply semax_seq'. { apply htg_blk_ok; auto. }
  eapply ConseqFacts.semax_post''.
  2: { apply htg_final_ok; auto. }
  unfold POSTCONDITION, abbreviate. simpl_ret_assert.
  remember (haead_padded (hrp_init_r blk) hrp_zero17 a) as h1 eqn:E1. apply htg_mk1 in E1.
  remember (haead_padded (hrp_init_r blk) h1 ct) as h2 eqn:E2. apply htg_mk2 in E2.
  remember (le64_bytes (Zlength a) ++ le64_bytes (Zlength ct)) as L eqn:EL. apply htg_mkL in EL.
  rewrite (htg_close key nonce a ct blk h1 h2 L Hfin E1 E2 EL Hbl). clear Hfin E1 E2 EL.
  generalize (poly1305_tag (aead_otk (aead_st key nonce)) (aead_mac_data a ct)); intros T.
  generalize (hrp_final_h (hrp_block (hrp_init_r blk) h2 L) (hrp_init_s blk)); intros hf.
  clear Hh3 HH.
  entailer!.
  rewrite Hbl. apply data_at_data_at_.
Qed.

(* ====================================================================== *)
(* part 3: ref_chacha20_xor                                                *)
(* (helpers of this part go here, between the two banners)                 *)
(* ====================================================================== *)

Module HAX := WgNoise.harness.x_prim_aead.code.

(* model facts: lengths, the bytes of one block *)
Lemma hax_Zlength_qround x a b c d : Zlength (chacha_qround x a b c d) = Zlength x.
Proof. unfold chacha_qround. rewrite !Zlength_upd_Znth. reflexivity. Qed.

Lemma hax_Zlength_dround x : Zlength (chacha_dround x) = Zlength x.
Proof. unfold chacha_dround. rewrite !hax_Zlength_qround. reflexivity. Qed.

Lemma hax_Zlength_rounds n x : Zlength (chacha_rounds n x) = Zlength x.
Proof.
  revert x; induction n; intros x; [reflexivity |].
  change (Zlength ((fix rounds (n : nat) (x : list int) {struct n} : list int :=
                      match n with O => x | S k => rounds k (chacha_dround x) end) n (chacha_dround x))
          = Zlength x).
  transitivity (Zlength (chacha_dround x)).
  - exact (IHn (chacha_dround x)).
  - apply hax_Zlength_dround.
Qed.

Lemma hax_Zlength_block_bytes n st : Zlength st = 16 -> Zlength (chacha_block_bytes n st) = 64.
Proof.
  intros H. unfold chacha_block_bytes, chacha_block_words.
  assert (Hw: forall ws, Zlength (words_bytes ws) = 4 * Zlength ws).
  { intros ws. unfold words_bytes. induction ws; cbn [map concat]; auto.
    rewrite Zlength_app, IHws, Zlength_cons. unfold le32_bytes. rewrite !Zlength_cons, Zlength_nil. lia. }
  rewrite Hw. unfold add_words. rewrite Zlength_map.
  pose proof (hax_Zlength_rounds n st) as Hr. rewrite !Zlength_correct in *.
  rewrite length_combine, Nat2Z.inj_min. rewrite Hr, H. reflexivity.
Qed.

Lemma hax_Zlength_st key nonce : Zlength (aead_st key nonce) = 16.
Proof. unfold aead_st, chacha_init_st, le32_words. rewrite !Zlength_app, !Zlength_map. reflexivity. Qed.

Lemma hax_xor_Znth a b j : 0 <= j < Zlength a -> 0 <= j < Zlength b ->
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
Definition hax_blk (key: list byte) (nonce b: Z) : list byte :=
  chacha_block_bytes 10 (chacha_advance (aead_st key nonce) (Int.unsigned (Int.repr (1 + b)))).

Lemma hax_blk_len key nonce b : Zlength (hax_blk key nonce b) = 64.
Proof. unfold hax_blk. apply hax_Zlength_block_bytes. apply haead_advance_length, hax_Zlength_st. Qed.

Lemma hax_blk_eq key nonce b :
  hax_blk key nonce b = chacha_block_bytes 10 (chacha_advance (chacha_advance (aead_st key nonce) 1) b).
Proof.
  unfold hax_blk. f_equal. rewrite haead_advance_add by apply hax_Zlength_st. apply haead_advance_repr.
Qed.

Lemma hax_xor_len (HH: haead_hyps) key nonce m :
  Zlength (chacha_xor 10 (chacha_advance (aead_st key nonce) 1) m) = Zlength m.
Proof.
  destruct HH as (_ & (_ & HL & _) & _).
  apply HL; try (apply haead_advance_length, hax_Zlength_st).
Qed.

Lemma hax_block_fact (HH: haead_hyps) key nonce m b j :
  0 <= b -> 64 * b < Zlength m -> 0 <= j < Z.min 64 (Zlength m - 64 * b) ->
  Znth (64 * b + j) (chacha_xor 10 (chacha_advance (aead_st key nonce) 1) m) =
  Byte.xor (Znth (64 * b + j) m) (Znth j (hax_blk key nonce b)).
Proof.
  intros Hb Hm Hj.
  pose proof (hax_xor_len HH key nonce m) as HX.
  pose proof (hax_blk_len key nonce b) as HB.
  destruct HH as (_ & (_ & _ & HF & _) & _).
  pose proof (hax_Zlength_st key nonce) as Hst.
  rewrite (hax_blk_eq key nonce b).
  pose proof (HF (chacha_advance (aead_st key nonce) 1) m b (haead_advance_length _ _ Hst) Hb Hm) as E.
  assert (HB2: Zlength (chacha_block_bytes 10 (chacha_advance (chacha_advance (aead_st key nonce) 1) b)) = 64)
    by (apply hax_Zlength_block_bytes; do 2 apply haead_advance_length; exact Hst).
  clear HF HB.
  replace (64 * b + j) with (j + 64 * b) by lia.
  rewrite <- (Znth_sublist (64 * b) j (Z.min (64 * b + 64) (Zlength m)) (chacha_xor 10 (chacha_advance (aead_st key nonce) 1) m)) by lia.
  rewrite <- (Znth_sublist (64 * b) j (Z.min (64 * b + 64) (Zlength m)) m) by lia.
  rewrite E. apply hax_xor_Znth; [rewrite Zlength_sublist by lia; lia | lia].
Qed.

Lemma hax_xor_byte a b :
  Vint (Int.zero_ext 8 (Int.xor (Int.repr (Byte.unsigned a)) (Int.repr (Byte.unsigned b)))) = Vubyte (Byte.xor a b).
Proof.
  unfold Vubyte. f_equal. apply Int.same_bits_eq. intros i Hi. rewrite Int.bits_zero_ext by lia. destruct (zlt i 8).
  { rewrite Int.bits_xor by lia. rewrite !Int.testbit_repr by lia.
    change (Z.testbit (Byte.unsigned ?x) i) with (Byte.testbit x i).
    rewrite Byte.bits_xor by (change Byte.zwordsize with 8; lia). reflexivity. }
  { rewrite Int.testbit_repr by lia. change (Z.testbit (Byte.unsigned ?x) i) with (Byte.testbit x i).
    symmetry. apply Byte.bits_above. change Byte.zwordsize with 8; lia. }
Qed.

Lemma hax_is_int_Vubyte b : is_int I8 Unsigned (Vubyte b).
Proof.
  unfold Vubyte; simpl. pose proof (Byte.unsigned_range_2 b).
  rewrite Int.unsigned_repr by rep_lia. rep_lia.
Qed.

(* the statements of ref_chacha20_xor: the call, the inner loop (one lemma each: recipe-big-straightline) *)
Definition hax_call : statement :=
  ltac:(let b := eval cbv delta [HAX.f_ref_chacha20_xor fn_body] beta iota in (fn_body HAX.f_ref_chacha20_xor) in
        match b with Ssequence _ (Ssequence _ (Swhile _ (Ssequence ?r _))) => exact r end).
Definition hax_inner : statement :=
  ltac:(let b := eval cbv delta [HAX.f_ref_chacha20_xor fn_body] beta iota in (fn_body HAX.f_ref_chacha20_xor) in
        match b with Ssequence _ (Ssequence _ (Swhile _ (Ssequence _ (Ssequence ?r _)))) => exact r end).

Definition hax_D : tycontext := func_tycontext HAX.f_ref_chacha20_xor haead_V haead_Gprog nil.

(* ref_chacha20_block(blk, key, ctr, nonce) *)
Lemma hax_call_ok (Espec: OracleKind) ksh kp key nonce vblk b vpos vdst vsrc vlen Fa Fb :
  readable_share ksh -> Zlength key = 32 -> 0 <= nonce <= Int64.max_unsigned ->
  semax hax_D
    (PROP () LOCAL (temp HAX._pos vpos; temp HAX._ctr (Vint (Int.repr (1 + b))); lvar HAX._blk (tarray tuchar 64) vblk;
      temp HAX._dst vdst; temp HAX._src vsrc; temp HAX._len vlen; temp HAX._key kp;
      temp HAX._nonce (Vlong (Int64.repr nonce)))
    SEP (data_at_ Tsh (tarray tuchar 64) vblk; data_at ksh (tarray tuchar 32) (map Vubyte key) kp; Fa; Fb))
    hax_call
    (normal_ret_assert
      (PROP () LOCAL (temp HAX._pos vpos; temp HAX._ctr (Vint (Int.repr (1 + b))); lvar HAX._blk (tarray tuchar 64) vblk;
        temp HAX._dst vdst; temp HAX._src vsrc; temp HAX._len vlen; temp HAX._key kp;
        temp HAX._nonce (Vlong (Int64.repr nonce)))
      SEP (data_at Tsh (tarray tuchar 64)
             (map Vubyte (hax_blk key nonce b)) vblk;
           data_at ksh (tarray tuchar 32) (map Vubyte key) kp; Fa; Fb))).
Proof.
  intros SH Hk Hn.
  unfold hax_call, hax_D. abbreviate_semax.
  forward_call (Tsh, vblk, ksh, kp, key, Int.repr (1 + b), nonce).
  unfold hax_blk.
  generalize (chacha_block_bytes 10 (chacha_advance (aead_st key nonce) (Int.unsigned (Int.repr (1 + b))))); intros bl.
  entailer!.
Qed.

Lemma hax_cmp1 pos j len n : 0 <= pos < len -> len <= Int64.max_signed -> 0 <= j < 64 ->
  n = Z.min 64 (len - pos) ->
  bool2val (Int64.cmpu Clt (Int64.add (Int64.repr pos) (Int64.repr j)) (Int64.repr len)) =
  Vint (if zlt j n then Int.one else Int.zero).
Proof.
  intros. unfold Int64.cmpu, Int64.ltu. rewrite Int64.add_unsigned.
  rewrite (Int64.unsigned_repr pos), (Int64.unsigned_repr j), (Int64.unsigned_repr (pos + j)),
    (Int64.unsigned_repr len) by rep_lia.
  destruct (zlt (pos + j) len), (zlt j n); try lia; reflexivity.
Qed.

Lemma hax_upd_step (X: list byte) k L : 0 <= k < Zlength X -> Zlength X = L ->
  upd_Znth k (map Vubyte (sublist 0 k X) ++ Zrepeat Vundef (L - k)) (Vubyte (Znth k X)) =
  map Vubyte (sublist 0 (k + 1) X) ++ Zrepeat Vundef (L - (k + 1)).
Proof. intros. list_solve. Qed.

(* an equation and the block fact, wrapped so that entailer! leaves them alone *)
Definition hax_eq {A} (x y: A) : Prop := x = y.

Definition hax_fact (X: list byte) (key: list byte) (nonce: Z) (m: list byte) : Prop :=
  forall b j, 0 <= b -> 64 * b < Zlength m -> 0 <= j < Z.min 64 (Zlength m - 64 * b) ->
    Znth (64 * b + j) X = Byte.xor (Znth (64 * b + j) m) (Znth j (hax_blk key nonce b)).

(* the inner loop: dst[pos + i] = src[pos + i] ^ blk[i] for i < n = min 64 (len - pos) *)
Lemma hax_inner_ok (Espec: OracleKind) dsh vdst ssh vsrc m X B pos vblk kp vnonce vctr Fa :
  writable_share dsh -> readable_share ssh -> Zlength m <= Int64.max_signed -> 0 <= pos < Zlength m ->
  Zlength X = Zlength m -> Zlength B = 64 ->
  (forall j, 0 <= j < Z.min 64 (Zlength m - pos) -> Znth (pos + j) X = Byte.xor (Znth (pos + j) m) (Znth j B)) ->
  semax hax_D
    (PROP () LOCAL (temp HAX._pos (Vlong (Int64.repr pos)); temp HAX._ctr vctr; lvar HAX._blk (tarray tuchar 64) vblk;
      temp HAX._dst vdst; temp HAX._src vsrc; temp HAX._len (Vlong (Int64.repr (Zlength m))); temp HAX._key kp;
      temp HAX._nonce vnonce)
    SEP (data_at Tsh (tarray tuchar 64) (map Vubyte B) vblk;
      data_at dsh (tarray tuchar (Zlength m)) (map Vubyte (sublist 0 pos X) ++ Zrepeat Vundef (Zlength m - pos)) vdst;
      data_at ssh (tarray tuchar (Zlength m)) (map Vubyte m) vsrc; Fa))
    hax_inner
    (normal_ret_assert
      (PROP () LOCAL (temp HAX._i (Vlong (Int64.repr (Z.min 64 (Zlength m - pos))));
        temp HAX._pos (Vlong (Int64.repr pos)); temp HAX._ctr vctr; lvar HAX._blk (tarray tuchar 64) vblk;
        temp HAX._dst vdst; temp HAX._src vsrc; temp HAX._len (Vlong (Int64.repr (Zlength m))); temp HAX._key kp;
        temp HAX._nonce vnonce)
      SEP (data_at Tsh (tarray tuchar 64) (map Vubyte B) vblk;
        data_at dsh (tarray tuchar (Zlength m))
          (map Vubyte (sublist 0 (pos + Z.min 64 (Zlength m - pos)) X) ++
           Zrepeat Vundef (Zlength m - (pos + Z.min 64 (Zlength m - pos)))) vdst;
        data_at ssh (tarray tuchar (Zlength m)) (map Vubyte m) vsrc; Fa))).
Proof.
  intros SH SH0 Hmax Hp HX HB Hfact.
  unfold hax_inner, hax_D. abbreviate_semax.
  remember (Z.min 64 (Zlength m - pos)) as n eqn:Hn.
  assert (Hn1: 0 < n <= 64) by lia. assert (Hn2: pos + n <= Zlength m) by lia.
  assert (Hn3: n = 64 \/ pos + n = Zlength m) by lia.
  forward.
  forward_loop (EX j: Z,
      PROP (0 <= j <= n)
      LOCAL (temp HAX._i (Vlong (Int64.repr j));
        temp HAX._pos (Vlong (Int64.repr pos)); temp HAX._ctr vctr; lvar HAX._blk (tarray tuchar 64) vblk;
        temp HAX._dst vdst; temp HAX._src vsrc; temp HAX._len (Vlong (Int64.repr (Zlength m))); temp HAX._key kp;
        temp HAX._nonce vnonce)
      SEP (data_at Tsh (tarray tuchar 64) (map Vubyte B) vblk;
        data_at dsh (tarray tuchar (Zlength m))
          (map Vubyte (sublist 0 (pos + j) X) ++ Zrepeat Vundef (Zlength m - (pos + j))) vdst;
        data_at ssh (tarray tuchar (Zlength m)) (map Vubyte m) vsrc; Fa))%assert
    continue: (EX j: Z,
      PROP (0 <= j < n)
      LOCAL (temp HAX._i (Vlong (Int64.repr j));
        temp HAX._pos (Vlong (Int64.repr pos)); temp HAX._ctr vctr; lvar HAX._blk (tarray tuchar 64) vblk;
        temp HAX._dst vdst; temp HAX._src vsrc; temp HAX._len (Vlong (Int64.repr (Zlength m))); temp HAX._key kp;
        temp HAX._nonce vnonce)
      SEP (data_at Tsh (tarray tuchar 64) (map Vubyte B) vblk;
        data_at dsh (tarray tuchar (Zlength m))
          (map Vubyte (sublist 0 (pos + j + 1) X) ++ Zrepeat Vundef (Zlength m - (pos + j + 1))) vdst;
        data_at ssh (tarray tuchar (Zlength m)) (map Vubyte m) vsrc; Fa))%assert
    break: (PROP () LOCAL (temp HAX._i (Vlong (Int64.repr n));
        temp HAX._pos (Vlong (Int64.repr pos)); temp HAX._ctr vctr; lvar HAX._blk (tarray tuchar 64) vblk;
        temp HAX._dst vdst; temp HAX._src vsrc; temp HAX._len (Vlong (Int64.repr (Zlength m))); temp HAX._key kp;
        temp HAX._nonce vnonce)
      SEP (data_at Tsh (tarray tuchar 64) (map Vubyte B) vblk;
        data_at dsh (tarray tuchar (Zlength m))
          (map Vubyte (sublist 0 (pos + n) X) ++ Zrepeat Vundef (Zlength m - (pos + n))) vdst;
        data_at ssh (tarray tuchar (Zlength m)) (map Vubyte m) vsrc; Fa)).
  - Exists 0. rewrite Z.add_0_r. entailer!.
  - Intros j.
    forward_if (PROP () LOCAL (temp HAX._t'1 (Vint (if zlt j n then Int.one else Int.zero)); temp HAX._i (Vlong (Int64.repr j));
        temp HAX._pos (Vlong (Int64.repr pos)); temp HAX._ctr vctr; lvar HAX._blk (tarray tuchar 64) vblk;
        temp HAX._dst vdst; temp HAX._src vsrc; temp HAX._len (Vlong (Int64.repr (Zlength m))); temp HAX._key kp;
        temp HAX._nonce vnonce)
      SEP (data_at Tsh (tarray tuchar 64) (map Vubyte B) vblk;
        data_at dsh (tarray tuchar (Zlength m))
          (map Vubyte (sublist 0 (pos + j) X) ++ Zrepeat Vundef (Zlength m - (pos + j))) vdst;
        data_at ssh (tarray tuchar (Zlength m)) (map Vubyte m) vsrc; Fa)).
    1: { rewrite !Int64.unsigned_repr in H0 by rep_lia. forward. rewrite (hax_cmp1 pos j (Zlength m) n) by (auto; lia). entailer!. }
    1: { rewrite !Int64.unsigned_repr in H0 by rep_lia. forward. destruct (zlt j n); [lia |]. entailer!. }
    forward_if.
    2: { assert (j = n) by (destruct (zlt j n); [discriminate | lia]). subst j. forward. entailer!. }
    assert (Hj: j < n) by (destruct (zlt j n); [lia | exfalso; apply H0; reflexivity]).
    forward.
    1: { entailer!. try rewrite Znth_map by lia. apply hax_is_int_Vubyte. }
    rewrite Znth_map by lia.
    forward.
    1: { entailer!. try rewrite Znth_map by lia. apply hax_is_int_Vubyte. }
    rewrite Znth_map by lia.
    forward.
    rewrite hax_xor_byte, <- Hfact by lia.
    rewrite hax_upd_step by lia.
    Exists j. entailer!.
  - Intros j. forward. Exists (j + 1). replace (pos + (j + 1)) with (pos + j + 1) by lia. entailer!.
  - unfold POSTCONDITION, abbreviate. simpl_ret_assert. subst n. apply ENTAIL_refl.
Qed.

Lemma haead_tag_xor3 : haead_hyps ->
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_ref_chacha20_xor ref_chacha20_xor_spec.
Proof.
  intros HH. start_function.
  pose proof (hax_xor_len HH key nonce m) as HXl.
  pose proof (hax_block_fact HH key nonce m) as Hfact.
  remember (chacha_xor 10 (chacha_advance (aead_st key nonce) 1) m) as X eqn:HXe.
  change (hax_eq X (chacha_xor 10 (chacha_advance (aead_st key nonce) 1) m)) in HXe.
  change (hax_fact X key nonce m) in Hfact. clear HH.
  forward. forward.
  forward_while (EX b: Z,
      PROP (0 <= b)
      LOCAL (temp HAX._pos (Vlong (Int64.repr (Z.min (64 * b) (Zlength m)))); temp HAX._ctr (Vint (Int.repr (1 + b)));
        lvar HAX._blk (tarray tuchar 64) v_blk; temp HAX._dst dst; temp HAX._src src;
        temp HAX._len (Vlong (Int64.repr (Zlength m))); temp HAX._key kp; temp HAX._nonce (Vlong (Int64.repr nonce)))
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
    { eapply semax_pre; [| apply (hax_call_ok _ ksh kp key nonce v_blk b (Vlong (Int64.repr (64 * b)))
         dst src (Vlong (Int64.repr (Zlength m)))
         (data_at dsh (tarray tuchar (Zlength m)) (map Vubyte (sublist 0 (64 * b) X) ++ Zrepeat Vundef (Zlength m - 64 * b)) dst)
         (data_at ssh (tarray tuchar (Zlength m)) (map Vubyte m) src)); auto].
      entailer!. }
    unfold MORE_COMMANDS, abbreviate.
    assert (Hj: forall j, 0 <= j < Z.min 64 (Zlength m - 64 * b) ->
        Znth (64 * b + j) X = Byte.xor (Znth (64 * b + j) m) (Znth j (hax_blk key nonce b)))
      by (intros; apply Hfact; auto).
    pose proof (hax_blk_len key nonce b) as HBl.
    clear Hfact. generalize dependent (hax_blk key nonce b). intros B Hj HBl.
    eapply semax_seq'.
    { eapply semax_pre; [| apply (hax_inner_ok _ dsh dst ssh src m X B (64 * b) v_blk kp
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
    forward. entailer!.
Qed.

(* ====================================================================== *)
(* the target                                                              *)
(* ====================================================================== *)

Lemma haead_tag_bodies3 : haead_hyps ->
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_rp_padded rp_padded_spec /\
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_ref_aead_tag ref_aead_tag_spec /\
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_ref_chacha20_xor ref_chacha20_xor_spec.
Proof.
  intros H. split; [|split]; [apply haead_tag_padded3 | apply haead_tag_tag3 | apply haead_tag_xor3]; exact H.
Qed.
