(* the bodies of rp_padded and
   ref_aead_tag of common.h against the NULL-tolerant specifications of ht4r_spec.v.  Adapted from law prim_aead's
   haead_tag_body3.v (parts 1 and 2): the input buffers are `prim_bytes` (emp when empty, any pointer then). *)
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
(* part 1: rp_padded                                                       *)
(* ====================================================================== *)

Module H4T := WgNoise.harness.x_prim_aead.code.

(* the static minusp's identifier mp of the law: a section variable (the Delta of the bodies depends on it) *)
Section HT4RT.
Variable mp: ident.

(* the statements of rp_padded: pos = 0; while; if (one lemma per call, abstract frames: recipe-big-straightline) *)
Definition ht4rt_pad_while : statement :=
  ltac:(let b := eval cbv delta [H4T.f_rp_padded fn_body] beta iota in (fn_body H4T.f_rp_padded) in
        match b with Ssequence _ (Ssequence ?r _) => exact r end).
Definition ht4rt_pad_call1 : statement :=
  ltac:(let b := eval cbv delta [H4T.f_rp_padded fn_body] beta iota in (fn_body H4T.f_rp_padded) in
        match b with Ssequence _ (Ssequence (Swhile _ (Ssequence ?r _)) _) => exact r end).
Definition ht4rt_pad_if : statement :=
  ltac:(let b := eval cbv delta [H4T.f_rp_padded fn_body] beta iota in (fn_body H4T.f_rp_padded) in
        match b with Ssequence _ (Ssequence _ ?r) => exact r end).
Definition ht4rt_pad_set : statement :=
  ltac:(let b := eval cbv delta [H4T.f_rp_padded fn_body] beta iota in (fn_body H4T.f_rp_padded) in
        match b with Ssequence _ (Ssequence _ (Sifthenelse _ (Ssequence ?r _) _)) => exact r end).
Definition ht4rt_pad_copy : statement :=
  ltac:(let b := eval cbv delta [H4T.f_rp_padded fn_body] beta iota in (fn_body H4T.f_rp_padded) in
        match b with Ssequence _ (Ssequence _ (Sifthenelse _ (Ssequence _ (Ssequence ?r _)) _)) => exact r end).
Definition ht4rt_pad_call2 : statement :=
  ltac:(let b := eval cbv delta [H4T.f_rp_padded fn_body] beta iota in (fn_body H4T.f_rp_padded) in
        match b with Ssequence _ (Ssequence _ (Sifthenelse _ (Ssequence _ (Ssequence _ ?r)) _)) => exact r end).

Definition ht4rt_pad_D : tycontext := func_tycontext H4T.f_rp_padded [] (ht4r_Gprog mp) nil.

(* the full blocks of rp_padded *)
Definition ht4rt_pad_f (r: list int) (buf: list byte) : list int -> Z -> list int :=
  fun h k => hrp_block r h (sublist (16 * k) (16 * k + 16) buf).

Lemma ht4rt_block_len (HH: haead_hyps) r h m : Zlength h = 17 -> Zlength (hrp_block r h m) = 17.
Proof.
  intros. destruct HH as ((_ & _ & Hm & _) & _). unfold hrp_block. apply Hm; auto.
Qed.

Lemma ht4rt_loop_len (HH: haead_hyps) r buf h k : 0 <= k -> Zlength h = 17 ->
  Zlength (hrp_loop (ht4rt_pad_f r buf) k h) = 17.
Proof.
  intros Hk Hh. pattern k; apply natlike_ind; auto.
  intros x Hx IH. unfold Z.succ. rewrite hrp_loop_succ by lia. unfold ht4rt_pad_f at 1.
  apply ht4rt_block_len; auto.
Qed.

Lemma ht4rt_loop_succ r buf h k : 0 <= k ->
  hrp_loop (ht4rt_pad_f r buf) (k + 1) h = hrp_block r (hrp_loop (ht4rt_pad_f r buf) k h) (sublist (16 * k) (16 * k + 16) buf).
Proof. intros. rewrite hrp_loop_succ by lia. reflexivity. Qed.

Lemma ht4rt_split sh n n1 n2 (l1 l2: list val) p : Zlength l1 = n1 -> Zlength l2 = n2 -> n = n1 + n2 ->
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
Lemma ht4rt_pad_call1_ok (Espec: OracleKind) sh p r h s ish ip buf pos vb Fa :
  writable_share sh -> readable_share ish -> 0 <= pos -> pos + 16 <= Zlength buf ->
  Zlength buf <= Int64.max_signed -> Zlength r = 17 -> Zlength h = 17 ->
  semax ht4rt_pad_D
    (PROP () LOCAL (temp H4T._pos (Vlong (Int64.repr pos)); lvar H4T._b (tarray tuchar 16) vb;
      temp H4T._p p; temp H4T._in ip; temp H4T._len (Vlong (Int64.repr (Zlength buf))))
    SEP (Fa; data_at sh t_rpoly (rpoly_val r h s) p;
      data_at ish (tarray tuchar (Zlength buf)) (map Vubyte buf) ip))
    ht4rt_pad_call1
    (normal_ret_assert
      (PROP () LOCAL (temp H4T._pos (Vlong (Int64.repr pos)); lvar H4T._b (tarray tuchar 16) vb;
        temp H4T._p p; temp H4T._in ip; temp H4T._len (Vlong (Int64.repr (Zlength buf))))
      SEP (data_at sh t_rpoly (rpoly_val r (hrp_block r h (sublist pos (pos + 16) buf)) s) p;
        data_at ish (tarray tuchar (Zlength buf)) (map Vubyte buf) ip; Fa))).
Proof.
  intros SH SH0 Hp Hp16 Hmax Hr Hh.
  unfold ht4rt_pad_call1, ht4rt_pad_D. abbreviate_semax.
  forward_call (sh, p, r, h, s, ish, ip, buf, pos).
  { entailer!. }
  entailer!.
Qed.

Lemma ht4rt_sub_repr a b : 0 <= b <= a -> a <= Int64.max_unsigned ->
  Int64.sub (Int64.repr a) (Int64.repr b) = Int64.repr (a - b).
Proof.
  intros. unfold Int64.sub. rewrite (Int64.unsigned_repr a), (Int64.unsigned_repr b) by rep_lia. reflexivity.
Qed.

(* the loop over the full blocks *)
Lemma ht4rt_pad_while_ok (Espec: OracleKind) (HH: haead_hyps) sh p r h s ish ip buf vb vpos :
  writable_share sh -> readable_share ish -> Zlength buf <= Int64.max_signed -> Zlength r = 17 ->
  Zlength h = 17 -> vpos = Vlong (Int64.repr 0) ->
  semax ht4rt_pad_D
    (PROP () LOCAL (temp H4T._pos vpos; lvar H4T._b (tarray tuchar 16) vb;
      temp H4T._p p; temp H4T._in ip; temp H4T._len (Vlong (Int64.repr (Zlength buf))))
    SEP (data_at_ Tsh (tarray tuchar 16) vb; data_at sh t_rpoly (rpoly_val r h s) p;
      data_at ish (tarray tuchar (Zlength buf)) (map Vubyte buf) ip))
    ht4rt_pad_while
    (normal_ret_assert (EX k: Z,
      PROP (0 <= k; 16 * k <= Zlength buf; Zlength buf - 16 * k < 16)
      LOCAL (temp H4T._pos (Vlong (Int64.repr (16 * k))); lvar H4T._b (tarray tuchar 16) vb;
        temp H4T._p p; temp H4T._in ip; temp H4T._len (Vlong (Int64.repr (Zlength buf))))
      SEP (data_at_ Tsh (tarray tuchar 16) vb;
        data_at sh t_rpoly (rpoly_val r (hrp_loop (ht4rt_pad_f r buf) k h) s) p;
        data_at ish (tarray tuchar (Zlength buf)) (map Vubyte buf) ip))%assert).
Proof.
  intros SH SH0 Hmax Hr Hh Hvpos. subst vpos.
  unfold ht4rt_pad_while, ht4rt_pad_D. abbreviate_semax.
  forward_while (EX k: Z,
      PROP (0 <= k; 16 * k <= Zlength buf)
      LOCAL (temp H4T._pos (Vlong (Int64.repr (16 * k))); lvar H4T._b (tarray tuchar 16) vb;
        temp H4T._p p; temp H4T._in ip; temp H4T._len (Vlong (Int64.repr (Zlength buf))))
      SEP (data_at_ Tsh (tarray tuchar 16) vb;
        data_at sh t_rpoly (rpoly_val r (hrp_loop (ht4rt_pad_f r buf) k h) s) p;
        data_at ish (tarray tuchar (Zlength buf)) (map Vubyte buf) ip))%assert.
  { Exists 0. entailer!. }
  { entailer!. }
  { eapply semax_seq'.
    { apply ht4rt_pad_call1_ok; auto; try lia. apply ht4rt_loop_len; auto. }
    unfold MORE_COMMANDS, abbreviate. forward.
    Exists (k + 1). entailer!.
    { f_equal. f_equal. lia. }
    rewrite ht4rt_loop_succ by lia. apply derives_refl. }
  forward. Exists k. entailer!.
Qed.

(* bytes_set(b, 0, 16) *)
Lemma ht4rt_pad_set_ok (Espec: OracleKind) vpos vb p ip vlen Fa Fb :
  semax ht4rt_pad_D
    (PROP () LOCAL (temp H4T._pos vpos; lvar H4T._b (tarray tuchar 16) vb;
      temp H4T._p p; temp H4T._in ip; temp H4T._len vlen)
    SEP (data_at_ Tsh (tarray tuchar 16) vb; Fa; Fb))
    ht4rt_pad_set
    (normal_ret_assert
      (PROP () LOCAL (temp H4T._pos vpos; lvar H4T._b (tarray tuchar 16) vb;
        temp H4T._p p; temp H4T._in ip; temp H4T._len vlen)
      SEP (data_at Tsh (tarray tuchar 16) (Zrepeat (Vubyte (Byte.repr 0)) 16) vb; Fa; Fb))).
Proof.
  unfold ht4rt_pad_set, ht4rt_pad_D. abbreviate_semax.
  forward_call (Tsh, vb, 0, 16).
  entailer!.
Qed.

(* bytes_copy(b, in + pos, len - pos) *)
Lemma ht4rt_pad_copy_ok (Espec: OracleKind) vb p ish ip pos len bs Fa Fb Fc :
  readable_share ish -> 0 <= pos -> len = pos + Zlength bs -> len <= Int64.max_signed ->
  semax ht4rt_pad_D
    (PROP () LOCAL (temp H4T._pos (Vlong (Int64.repr pos)); lvar H4T._b (tarray tuchar 16) vb;
      temp H4T._p p; temp H4T._in ip; temp H4T._len (Vlong (Int64.repr len)))
    SEP (data_at_ Tsh (tarray tuchar (Zlength bs)) vb;
      data_at ish (tarray tuchar (Zlength bs)) (map Vubyte bs) (offset_val pos ip); Fa; Fb; Fc))
    ht4rt_pad_copy
    (normal_ret_assert
      (PROP () LOCAL (temp H4T._pos (Vlong (Int64.repr pos)); lvar H4T._b (tarray tuchar 16) vb;
        temp H4T._p p; temp H4T._in ip; temp H4T._len (Vlong (Int64.repr len)))
      SEP (data_at Tsh (tarray tuchar (Zlength bs)) (map Vubyte bs) vb;
        data_at ish (tarray tuchar (Zlength bs)) (map Vubyte bs) (offset_val pos ip); Fa; Fb; Fc))).
Proof.
  intros SH0 Hp Hl Hmax.
  pose proof (Zlength_nonneg bs).
  unfold ht4rt_pad_copy, ht4rt_pad_D. abbreviate_semax.
  forward_call (Tsh, vb, ish, offset_val pos ip, bs).
  { assert_PROP (isptr (offset_val pos ip)) as Hip by entailer!. destruct ip; try contradiction.
    entailer!. simpl. replace (pos + Zlength bs - pos) with (Zlength bs) by lia.
    unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by rep_lia. rewrite Ptrofs.mul_commut.
    change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.mul_one. reflexivity. }
  entailer!.
Qed.

(* rp_block(p, b) *)
Lemma ht4rt_pad_call2_ok (Espec: OracleKind) sh p r h s vb bl vpos ip vlen Fa Fb :
  writable_share sh -> Zlength r = 17 -> Zlength h = 17 -> Zlength bl = 16 ->
  semax ht4rt_pad_D
    (PROP () LOCAL (temp H4T._pos vpos; lvar H4T._b (tarray tuchar 16) vb;
      temp H4T._p p; temp H4T._in ip; temp H4T._len vlen)
    SEP (data_at Tsh (tarray tuchar (Zlength bl)) (map Vubyte bl) vb; data_at sh t_rpoly (rpoly_val r h s) p;
      Fa; Fb))
    ht4rt_pad_call2
    (normal_ret_assert
      (PROP () LOCAL (temp H4T._pos vpos; lvar H4T._b (tarray tuchar 16) vb;
        temp H4T._p p; temp H4T._in ip; temp H4T._len vlen)
      SEP (data_at sh t_rpoly (rpoly_val r (hrp_block r h bl) s) p;
        data_at Tsh (tarray tuchar (Zlength bl)) (map Vubyte bl) vb; Fa; Fb))).
Proof.
  intros SH Hr Hh Hl.
  unfold ht4rt_pad_call2, ht4rt_pad_D. abbreviate_semax.
  forward_call (sh, p, r, h, s, Tsh, vb, bl, 0).
  rewrite (sublist_same 0 (0 + 16) bl) by lia.
  entailer!.
Qed.

(* the state after the if *)
Definition ht4rt_pad_last (r h1: list int) (buf: list byte) (pos: Z) : list int :=
  if Z.eq_dec (Zlength buf - pos) 0 then h1
  else hrp_block r h1 (sublist pos (Zlength buf) buf ++ Zrepeat Byte.zero (16 - (Zlength buf - pos))).

Lemma ht4rt_padded_eq r h buf k : 0 <= k -> 16 * k <= Zlength buf -> Zlength buf - 16 * k < 16 ->
  haead_padded r h buf = ht4rt_pad_last r (hrp_loop (ht4rt_pad_f r buf) k h) buf (16 * k).
Proof.
  intros. unfold haead_padded.
  assert (E: Zlength buf / 16 = k) by (symmetry; apply Z.div_unique with (r := Zlength buf - 16 * k); lia).
  unfold ht4rt_pad_last, ht4rt_pad_f. cbv zeta. rewrite E. reflexivity.
Qed.

Lemma ht4rt_zrep_split (x: val) n : 0 <= n <= 16 -> Zrepeat x 16 = Zrepeat x n ++ Zrepeat x (16 - n).
Proof. intros. list_solve. Qed.

Lemma ht4rt_buf_split (buf: list byte) pos : 0 <= pos <= Zlength buf ->
  map Vubyte buf = map Vubyte (sublist 0 pos buf) ++ map Vubyte (sublist pos (Zlength buf) buf).
Proof. intros. rewrite <- map_app, <- sublist_split, sublist_same by lia. reflexivity. Qed.

(* the last partial block *)
Lemma ht4rt_pad_if_ok (Espec: OracleKind) (HH: haead_hyps) sh p r h1 s ish ip buf vb pos :
  writable_share sh -> readable_share ish -> Zlength buf <= Int64.max_signed -> Zlength r = 17 ->
  Zlength h1 = 17 -> 0 <= pos <= Zlength buf -> Zlength buf - pos < 16 ->
  semax ht4rt_pad_D
    (PROP () LOCAL (temp H4T._pos (Vlong (Int64.repr pos)); lvar H4T._b (tarray tuchar 16) vb;
      temp H4T._p p; temp H4T._in ip; temp H4T._len (Vlong (Int64.repr (Zlength buf))))
    SEP (data_at_ Tsh (tarray tuchar 16) vb; data_at sh t_rpoly (rpoly_val r h1 s) p;
      data_at ish (tarray tuchar (Zlength buf)) (map Vubyte buf) ip))
    ht4rt_pad_if
    (normal_ret_assert
      (PROP () LOCAL (temp H4T._pos (Vlong (Int64.repr pos)); lvar H4T._b (tarray tuchar 16) vb;
        temp H4T._p p; temp H4T._in ip; temp H4T._len (Vlong (Int64.repr (Zlength buf))))
      SEP (data_at_ Tsh (tarray tuchar 16) vb; data_at sh t_rpoly (rpoly_val r (ht4rt_pad_last r h1 buf pos) s) p;
        data_at ish (tarray tuchar (Zlength buf)) (map Vubyte buf) ip))).
Proof.
  intros SH SH0 Hmax Hr Hh Hp Hlt.
  unfold ht4rt_pad_if, ht4rt_pad_D. abbreviate_semax.
  forward_if (PROP () LOCAL (temp H4T._pos (Vlong (Int64.repr pos)); lvar H4T._b (tarray tuchar 16) vb;
        temp H4T._p p; temp H4T._in ip; temp H4T._len (Vlong (Int64.repr (Zlength buf))))
      SEP (data_at_ Tsh (tarray tuchar 16) vb; data_at sh t_rpoly (rpoly_val r (ht4rt_pad_last r h1 buf pos) s) p;
        data_at ish (tarray tuchar (Zlength buf)) (map Vubyte buf) ip)).
  - rewrite ht4rt_sub_repr, !Int64.unsigned_repr in H by rep_lia.
    eapply semax_seq'; [apply ht4rt_pad_set_ok |]. unfold MORE_COMMANDS, abbreviate.
    assert_PROP (field_compatible (tarray tuchar 16) [] vb) as Fvb by entailer!.
    assert_PROP (field_compatible (tarray tuchar (Zlength buf)) [] ip) as Fip by entailer!.
    rewrite (ht4rt_zrep_split (Vubyte (Byte.repr 0)) (Zlength buf - pos)) by lia.
    rewrite (ht4rt_split Tsh 16 (Zlength buf - pos) (16 - (Zlength buf - pos))) by (auto; try list_solve; lia).
    rewrite (ht4rt_buf_split buf pos) by lia.
    rewrite (ht4rt_split ish (Zlength buf) pos (Zlength buf - pos)) by (auto; try list_solve; lia).
    sep_apply (data_at_data_at_ Tsh (tarray tuchar (Zlength buf - pos))
      (Zrepeat (Vubyte (Byte.repr 0)) (Zlength buf - pos)) vb).
    assert (Hbs: Zlength (sublist pos (Zlength buf) buf) = Zlength buf - pos) by list_solve.
    eapply semax_seq'.
    { eapply semax_pre; [| apply (ht4rt_pad_copy_ok _ vb p ish ip pos (Zlength buf) (sublist pos (Zlength buf) buf)
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
    eapply semax_pre; [| eapply ConseqFacts.semax_post''; [| apply (ht4rt_pad_call2_ok _ sh p r h1 s vb
      (sublist pos (Zlength buf) buf ++ Zrepeat Byte.zero (16 - (Zlength buf - pos)))
      (Vlong (Int64.repr pos)) ip (Vlong (Int64.repr (Zlength buf)))
      (data_at ish (tarray tuchar (Zlength buf)) (map Vubyte buf) ip) emp); auto]].
    { rewrite Hbs, Hbl, map_app, Hz.
      rewrite (ht4rt_split Tsh 16 (Zlength buf - pos) (16 - (Zlength buf - pos))); auto; try list_solve; try lia.
      erewrite (ht4rt_buf_split buf pos) by lia.
      rewrite (ht4rt_split ish (Zlength buf) pos (Zlength buf - pos)); auto; try list_solve; try lia.
      entailer!. }
    unfold POSTCONDITION, abbreviate. simpl_ret_assert.
    unfold ht4rt_pad_last. destruct (Z.eq_dec (Zlength buf - pos) 0); [lia |]. rewrite Hbl.
    entailer!.
  - rewrite ht4rt_sub_repr, !Int64.unsigned_repr in H by rep_lia.
    forward. unfold ht4rt_pad_last. destruct (Z.eq_dec (Zlength buf - pos) 0); [| lia]. entailer!.
Qed.

Lemma ht4rt_padded_body : haead_hyps ->
  semax_body [] (ht4r_Gprog mp) WgNoise.harness.x_prim_aead.code.f_rp_padded rp_padded_spec_n.
Proof.
  intros HH.
  start_function.
  destruct (Z.eq_dec (Zlength buf) 0) as [Hz | Hnz].
  - (* the empty input: prim_bytes is emp, the pointer anything; neither the loop nor the if runs *)
    assert (Hb: buf = []) by (apply Zlength_nil_inv; exact Hz). subst buf.
    forward.
    forward_while (PROP () LOCAL (temp H4T._pos (Vlong (Int64.repr 0)); lvar H4T._b (tarray tuchar 16) v_b;
       temp H4T._p p; temp H4T._in ip; temp H4T._len (Vlong (Int64.repr 0)))
       SEP (data_at_ Tsh (tarray tuchar 16) v_b; data_at sh t_rpoly (rpoly_val r h s) p; prim_bytes ish [] ip)).
    { entailer!. }
    { entailer!. }
    { exfalso. compute in HRE. congruence. }
    forward_if.
    { exfalso. compute in H2. congruence. }
    forward.
    change (haead_padded r h []) with h.
    entailer!.
  - unfold prim_bytes at 1. rewrite if_false by exact Hnz.
    forward.
    eapply semax_seq'.
    { apply ht4rt_pad_while_ok; auto. }
    Intros k. unfold MORE_COMMANDS, abbreviate.
    eapply ConseqFacts.semax_post''.
    2: { apply ht4rt_pad_if_ok; auto; try lia. apply ht4rt_loop_len; auto. }
    rewrite <- ht4rt_padded_eq by auto.
    unfold POSTCONDITION, abbreviate. simpl_ret_assert. unfold prim_bytes. rewrite if_false by exact Hnz.
    entailer!.
Qed.

(* ====================================================================== *)
(* part 2: ref_aead_tag                                                    *)
(* ====================================================================== *)

Lemma ht4rt_g_le64_len z : Zlength (le64_bytes z) = 8.
Proof. reflexivity. Qed.

Lemma ht4rt_g_splice1 (l: list byte) : Zlength l = 8 ->
  haead_splice 0 l (Zrepeat Vundef 16) = map Vubyte l ++ Zrepeat Vundef 8.
Proof. intros. unfold haead_splice. list_solve. Qed.

Lemma ht4rt_g_splice2 (l1 l2: list byte) : Zlength l1 = 8 -> Zlength l2 = 8 ->
  haead_splice 8 l2 (map Vubyte l1 ++ Zrepeat Vundef 8) = map Vubyte (l1 ++ l2).
Proof. intros. unfold haead_splice. list_solve. Qed.

(* model facts kept in the context during the body proof, as opaque predicates over variables: a model term
   in the context costs entailer!/forward_call ~14 s per sentence *)
Definition ht4rt_g_F (key: list byte) (nonce: Z) (a ct blk: list byte) : Prop :=
  Zlength blk = 64 ->
  hrp_final_out (haead_tag_h blk a ct) (hrp_init_s blk) = poly1305_tag (aead_otk (aead_st key nonce)) (aead_mac_data a ct).
Definition ht4rt_g_E1 (blk a: list byte) (h1: list int) : Prop := h1 = haead_padded (hrp_init_r blk) hrp_zero17 a.
Definition ht4rt_g_E2 (blk: list byte) (h1: list int) (ct: list byte) (h2: list int) : Prop :=
  h2 = haead_padded (hrp_init_r blk) h1 ct.
Definition ht4rt_g_EL (a ct L: list byte) : Prop := L = le64_bytes (Zlength a) ++ le64_bytes (Zlength ct).

Lemma ht4rt_g_st_len key nonce : Zlength (aead_st key nonce) = 16.
Proof. reflexivity. Qed.

Lemma ht4rt_g_fin (HH: haead_hyps) key nonce a ct blk :
  blk = chacha_block_bytes 10 (chacha_advance (aead_st key nonce) (Int.unsigned Int.zero)) ->
  ht4rt_g_F key nonce a ct blk.
Proof.
  intros E. unfold ht4rt_g_F. intros L. destruct HH as (_ & (_ & _ & _ & _ & Hmac & _) & _).
  rewrite Hmac by lia. subst blk. unfold aead_otk.
  rewrite Int.unsigned_zero, haead_advance_0 by apply ht4rt_g_st_len. reflexivity.
Qed.

Lemma ht4rt_g_close key nonce a ct blk h1 h2 L :
  ht4rt_g_F key nonce a ct blk -> ht4rt_g_E1 blk a h1 -> ht4rt_g_E2 blk h1 ct h2 -> ht4rt_g_EL a ct L -> Zlength blk = 64 ->
  hrp_final_out (hrp_block (hrp_init_r blk) h2 L) (hrp_init_s blk) =
  poly1305_tag (aead_otk (aead_st key nonce)) (aead_mac_data a ct).
Proof.
  unfold ht4rt_g_F, ht4rt_g_E1, ht4rt_g_E2, ht4rt_g_EL. intros Hfin E1 E2 EL Hbl.
  rewrite <- (Hfin Hbl). unfold haead_tag_h. subst h2 h1 L. reflexivity.
Qed.

Lemma ht4rt_g_mk1 blk a h1 : h1 = haead_padded (hrp_init_r blk) hrp_zero17 a -> ht4rt_g_E1 blk a h1.
Proof. exact (fun e => e). Qed.
Lemma ht4rt_g_mk2 blk h1 ct h2 : h2 = haead_padded (hrp_init_r blk) h1 ct -> ht4rt_g_E2 blk h1 ct h2.
Proof. exact (fun e => e). Qed.
Lemma ht4rt_g_mkL a ct L : L = le64_bytes (Zlength a) ++ le64_bytes (Zlength ct) -> ht4rt_g_EL a ct L.
Proof. exact (fun e => e). Qed.

#[local] Opaque ht4rt_g_F ht4rt_g_E1 ht4rt_g_E2 ht4rt_g_EL.

Lemma ht4rt_g_r_len (HH: haead_hyps) blk : Zlength blk = 64 -> Zlength (hrp_init_r blk) = 17.
Proof. intros. destruct HH as ((_ & Hr & _) & _). apply Hr. lia. Qed.

Lemma ht4rt_g_padded_len (HH: haead_hyps) r h buf : Zlength h = 17 -> Zlength (haead_padded r h buf) = 17.
Proof. intros. destruct HH as (_ & (_ & _ & _ & Hp & _) & _). apply Hp; auto. Qed.

Lemma ht4rt_g_block_len (HH: haead_hyps) r h m : Zlength h = 17 -> Zlength (hrp_block r h m) = 17.
Proof. intros. destruct HH as ((_ & _ & Hm & _) & _). unfold hrp_block. apply Hm; auto. Qed.

Definition ht4rt_g_block_stmt : statement :=
  ltac:(let b := eval cbv delta [WgNoise.harness.x_prim_aead.code.f_ref_aead_tag fn_body] beta iota in
          (fn_body WgNoise.harness.x_prim_aead.code.f_ref_aead_tag) in
        match b with Ssequence ?r _ => exact r end).

(* ref_chacha20_block(blk, key, 0, nonce): the block is abstracted, with the fact ht4rt_g_F *)
Lemma ht4rt_g_block_call (Espec: OracleKind) (HH: haead_hyps) tag ksh kp key nonce ad a cp ct gv v_p v_blk v_lens
    F1 F2 F3 F4 F5 F6 :
  readable_share ksh -> Zlength key = 32 -> 0 <= nonce <= Int64.max_unsigned ->
  semax (func_tycontext WgNoise.harness.x_prim_aead.code.f_ref_aead_tag [] (ht4r_Gprog mp) nil)
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
    ht4rt_g_block_stmt
    (normal_ret_assert (EX blk: list byte,
      PROP (ht4rt_g_F key nonce a ct blk; Zlength blk = 64)
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
  unfold ht4rt_g_block_stmt. abbreviate_semax.
  forward_call (Tsh, v_blk, ksh, kp, key, Int.zero, nonce).
  remember (chacha_block_bytes 10 (chacha_advance (aead_st key nonce) (Int.unsigned Int.zero))) as blk eqn:Eblk.
  pose proof (ht4rt_g_fin HH key nonce a ct blk Eblk) as Hfin. clear Eblk HH.
  assert_PROP (Zlength (map Vubyte blk) = 64) as Hbl by entailer!. rewrite Zlength_map in Hbl.
  Exists blk. rewrite Hbl. entailer!.
Qed.

(* the locals of ref_aead_tag (no temp changes after the entry) *)
Local Notation ht4rt_g_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct :=
  [lvar WgNoise.harness.x_prim_aead.code._lens (tarray tuchar 16) v_lens;
   lvar WgNoise.harness.x_prim_aead.code._blk (tarray tuchar 64) v_blk;
   lvar WgNoise.harness.x_prim_aead.code._p (Tstruct WgNoise.harness.x_prim_aead.code._rpoly noattr) v_p;
   gvars gv; temp WgNoise.harness.x_prim_aead.code._tag tag; temp WgNoise.harness.x_prim_aead.code._key kp;
   temp WgNoise.harness.x_prim_aead.code._nonce (Vlong (Int64.repr nonce));
   temp WgNoise.harness.x_prim_aead.code._ad ad;
   temp WgNoise.harness.x_prim_aead.code._adlen (Vlong (Int64.repr (Zlength a)));
   temp WgNoise.harness.x_prim_aead.code._ct cp;
   temp WgNoise.harness.x_prim_aead.code._ctlen (Vlong (Int64.repr (Zlength ct)))].

Local Notation ht4rt_g_D := (func_tycontext WgNoise.harness.x_prim_aead.code.f_ref_aead_tag [] (ht4r_Gprog mp) nil).

Definition ht4rt_g_s1 : statement :=
  ltac:(let b := eval cbv delta [WgNoise.harness.x_prim_aead.code.f_ref_aead_tag fn_body] beta iota in
          (fn_body WgNoise.harness.x_prim_aead.code.f_ref_aead_tag) in
        match b with Ssequence _ (Ssequence ?r _) => exact r end).
Definition ht4rt_g_s2 : statement :=
  ltac:(let b := eval cbv delta [WgNoise.harness.x_prim_aead.code.f_ref_aead_tag fn_body] beta iota in
          (fn_body WgNoise.harness.x_prim_aead.code.f_ref_aead_tag) in
        match b with Ssequence _ (Ssequence _ (Ssequence ?r _)) => exact r end).
Definition ht4rt_g_s3 : statement :=
  ltac:(let b := eval cbv delta [WgNoise.harness.x_prim_aead.code.f_ref_aead_tag fn_body] beta iota in
          (fn_body WgNoise.harness.x_prim_aead.code.f_ref_aead_tag) in
        match b with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence ?r _))) => exact r end).
Definition ht4rt_g_s4 : statement :=
  ltac:(let b := eval cbv delta [WgNoise.harness.x_prim_aead.code.f_ref_aead_tag fn_body] beta iota in
          (fn_body WgNoise.harness.x_prim_aead.code.f_ref_aead_tag) in
        match b with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence ?r _)))) => exact r end).
Definition ht4rt_g_s5 : statement :=
  ltac:(let b := eval cbv delta [WgNoise.harness.x_prim_aead.code.f_ref_aead_tag fn_body] beta iota in
          (fn_body WgNoise.harness.x_prim_aead.code.f_ref_aead_tag) in
        match b with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence ?r _))))) => exact r end).
Definition ht4rt_g_s6 : statement :=
  ltac:(let b := eval cbv delta [WgNoise.harness.x_prim_aead.code.f_ref_aead_tag fn_body] beta iota in
          (fn_body WgNoise.harness.x_prim_aead.code.f_ref_aead_tag) in
        match b with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence ?r _)))))) => exact r end).
Definition ht4rt_g_s7 : statement :=
  ltac:(let b := eval cbv delta [WgNoise.harness.x_prim_aead.code.f_ref_aead_tag fn_body] beta iota in
          (fn_body WgNoise.harness.x_prim_aead.code.f_ref_aead_tag) in
        match b with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ ?r)))))) => exact r end).

Lemma ht4rt_g_init_ok (Espec: OracleKind) (v_lens v_blk v_p: val) (gv: globals) (tag kp: val) (nonce: Z) (ad: val) (a: list byte)
    (cp: val) (ct: list byte) (blk: list byte) (F1: mpred) (F2: mpred) (F3: mpred) (F4: mpred) (F5: mpred) (F6: mpred) :
  Zlength blk = 64 ->
  semax ht4rt_g_D (PROPx [] (LOCALx (ht4rt_g_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [data_at Tsh (tarray tuchar (Zlength blk)) (map Vubyte blk) v_blk; F1; F2; data_at_ Tsh (Tstruct WgNoise.harness.x_prim_aead.code._rpoly noattr) v_p; F3; F4; F5; F6])))
    ht4rt_g_s1
    (normal_ret_assert (PROPx [] (LOCALx (ht4rt_g_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [data_at Tsh t_rpoly (rpoly_val (hrp_init_r blk) hrp_zero17 (hrp_init_s blk)) v_p; data_at Tsh (tarray tuchar (Zlength blk)) (map Vubyte blk) v_blk; F2; F3; F1; F4; F5; F6])))).
Proof.
  intros. unfold ht4rt_g_s1. abbreviate_semax.
  forward_call (Tsh, v_p, Tsh, v_blk, blk).
  entailer!.
Qed.

Lemma ht4rt_g_pad_ad_ok (Espec: OracleKind) (v_lens v_blk v_p: val) (gv: globals) (tag kp: val) (nonce: Z) (ad: val) (a: list byte)
    (cp: val) (ct: list byte) (ash: share) (r: list int) (h: list int) (s: list byte) (F1: mpred) (F2: mpred) (F3: mpred) (F4: mpred) (F5: mpred) (F6: mpred) :
  readable_share ash -> Zlength r = 17 -> Zlength h = 17 -> Zlength a <= Int64.max_signed ->
  semax ht4rt_g_D (PROPx [] (LOCALx (ht4rt_g_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [data_at Tsh t_rpoly (rpoly_val r h s) v_p; F1; F2; F3; F4; prim_bytes ash a ad; F5; F6])))
    ht4rt_g_s2
    (normal_ret_assert (PROPx [] (LOCALx (ht4rt_g_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [data_at Tsh t_rpoly (rpoly_val r (haead_padded r h a) s) v_p; F1; F2; F3; F4; prim_bytes ash a ad; F5; F6])))).
Proof.
  intros. unfold ht4rt_g_s2. abbreviate_semax.
  forward_call (Tsh, v_p, r, h, s, ash, ad, a).
  entailer!.
Qed.

Lemma ht4rt_g_pad_ct_ok (Espec: OracleKind) (v_lens v_blk v_p: val) (gv: globals) (tag kp: val) (nonce: Z) (ad: val) (a: list byte)
    (cp: val) (ct: list byte) (csh: share) (r: list int) (h: list int) (s: list byte) (F1: mpred) (F2: mpred) (F3: mpred) (F4: mpred) (F5: mpred) (F6: mpred) :
  readable_share csh -> Zlength r = 17 -> Zlength h = 17 -> Zlength ct <= Int64.max_signed ->
  semax ht4rt_g_D (PROPx [] (LOCALx (ht4rt_g_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [data_at Tsh t_rpoly (rpoly_val r h s) v_p; F1; F2; F3; F4; F5; prim_bytes csh ct cp; F6])))
    ht4rt_g_s3
    (normal_ret_assert (PROPx [] (LOCALx (ht4rt_g_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [data_at Tsh t_rpoly (rpoly_val r (haead_padded r h ct) s) v_p; F1; F2; F3; F4; F5; prim_bytes csh ct cp; F6])))).
Proof.
  intros. unfold ht4rt_g_s3. abbreviate_semax.
  forward_call (Tsh, v_p, r, h, s, csh, cp, ct).
  entailer!.
Qed.

Lemma ht4rt_g_le1_ok (Espec: OracleKind) (v_lens v_blk v_p: val) (gv: globals) (tag kp: val) (nonce: Z) (ad: val) (a: list byte)
    (cp: val) (ct: list byte) (F1: mpred) (F2: mpred) (F3: mpred) (F4: mpred) (F5: mpred) (F6: mpred) (F7: mpred) :
  
  Zlength a <= Int64.max_signed ->
  semax ht4rt_g_D (PROPx [] (LOCALx (ht4rt_g_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [F1; F2; data_at_ Tsh (tarray tuchar 16) v_lens; F3; F4; F5; F6; F7])))
    ht4rt_g_s4
    (normal_ret_assert (PROPx [] (LOCALx (ht4rt_g_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [F1; F2; data_at Tsh (tarray tuchar 16) (map Vubyte (le64_bytes (Zlength a)) ++ Zrepeat Vundef 8) v_lens; F3; F4; F5; F6; F7])))).
Proof.
  intros. unfold ht4rt_g_s4. abbreviate_semax.
  replace_SEP 2 (data_at Tsh (tarray tuchar (Zlength (Zrepeat Vundef 16))) (Zrepeat Vundef 16) v_lens) by entailer!.
  assert_PROP (isptr v_lens) as Hpl by entailer!.
  forward_call (Tsh, v_lens, 0, Zrepeat Vundef 16, Zlength a).
  { rewrite Zlength_Zrepeat by lia; pose proof (Zlength_nonneg a); repeat split; rep_lia. }
  rewrite ht4rt_g_splice1 by apply ht4rt_g_le64_len.
  entailer!.
Qed.

Lemma ht4rt_g_le2_ok (Espec: OracleKind) (v_lens v_blk v_p: val) (gv: globals) (tag kp: val) (nonce: Z) (ad: val) (a: list byte)
    (cp: val) (ct: list byte) (F1: mpred) (F2: mpred) (F3: mpred) (F4: mpred) (F5: mpred) (F6: mpred) (F7: mpred) :
  
  Zlength ct <= Int64.max_signed ->
  semax ht4rt_g_D (PROPx [] (LOCALx (ht4rt_g_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [F1; F2; data_at Tsh (tarray tuchar 16) (map Vubyte (le64_bytes (Zlength a)) ++ Zrepeat Vundef 8) v_lens; F3; F4; F5; F6; F7])))
    ht4rt_g_s5
    (normal_ret_assert (PROPx [] (LOCALx (ht4rt_g_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [F1; F2; data_at Tsh (tarray tuchar 16) (map Vubyte (le64_bytes (Zlength a) ++ le64_bytes (Zlength ct))) v_lens; F3; F4; F5; F6; F7])))).
Proof.
  intros. unfold ht4rt_g_s5. abbreviate_semax.
  replace_SEP 2 (data_at Tsh (tarray tuchar (Zlength (map Vubyte (le64_bytes (Zlength a)) ++ Zrepeat Vundef 8)))
    (map Vubyte (le64_bytes (Zlength a)) ++ Zrepeat Vundef 8) v_lens)
    by (rewrite Zlength_app, Zlength_map, ht4rt_g_le64_len; entailer!).
  assert_PROP (isptr v_lens) as Hpl by entailer!.
  forward_call (Tsh, v_lens, 8, map Vubyte (le64_bytes (Zlength a)) ++ Zrepeat Vundef 8, Zlength ct).
  rewrite ht4rt_g_splice2 by apply ht4rt_g_le64_len.
  rewrite Zlength_app, Zlength_map, ht4rt_g_le64_len, Zlength_Zrepeat by lia. change (8 + 8) with 16.
  entailer!.
Qed.

Lemma ht4rt_g_blk_ok (Espec: OracleKind) (v_lens v_blk v_p: val) (gv: globals) (tag kp: val) (nonce: Z) (ad: val) (a: list byte)
    (cp: val) (ct: list byte) (r: list int) (h: list int) (s: list byte) (L: list byte) (F1: mpred) (F2: mpred) (F3: mpred) (F4: mpred) (F5: mpred) (F6: mpred) :
  Zlength r = 17 -> Zlength h = 17 -> Zlength L = 16 ->
  semax ht4rt_g_D (PROPx [] (LOCALx (ht4rt_g_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [data_at Tsh t_rpoly (rpoly_val r h s) v_p; F1; data_at Tsh (tarray tuchar 16) (map Vubyte L) v_lens; F2; F3; F4; F5; F6])))
    ht4rt_g_s6
    (normal_ret_assert (PROPx [] (LOCALx (ht4rt_g_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [data_at Tsh t_rpoly (rpoly_val r (hrp_block r h L) s) v_p; F1; data_at Tsh (tarray tuchar 16) (map Vubyte L) v_lens; F2; F3; F4; F5; F6])))).
Proof.
  intros. unfold ht4rt_g_s6. abbreviate_semax.
  match goal with HL: Zlength L = 16 |- _ =>
    replace_SEP 2 (data_at Tsh (tarray tuchar (Zlength L)) (map Vubyte L) v_lens) by (rewrite HL; entailer!);
    forward_call (Tsh, v_p, r, h, s, Tsh, v_lens, L, 0);
    rewrite (sublist_same 0 (0 + 16) L) by lia;
    rewrite HL end.
  entailer!.
Qed.

Lemma ht4rt_g_final_ok (Espec: OracleKind) (v_lens v_blk v_p: val) (gv: globals) (tag kp: val) (nonce: Z) (ad: val) (a: list byte)
    (cp: val) (ct: list byte) (tsh: share) (r: list int) (h: list int) (s: list byte) (F1: mpred) (F2: mpred) (F3: mpred) (F4: mpred) (F5: mpred) :
  writable_share tsh -> Zlength r = 17 -> Zlength h = 17 ->
  semax ht4rt_g_D (PROPx [] (LOCALx (ht4rt_g_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [data_at Tsh t_rpoly (rpoly_val r h s) v_p; F1; F2; data_at_ tsh (tarray tuchar 16) tag; F3; F4; F5; ht4_minusp mp gv])))
    ht4rt_g_s7
    (normal_ret_assert (PROPx [] (LOCALx (ht4rt_g_LOC v_lens v_blk v_p gv tag kp nonce ad a cp ct) (SEPx [data_at Tsh t_rpoly (rpoly_val r (hrp_final_h h s) s) v_p; F1; F2; data_at tsh (tarray tuchar 16) (map Vubyte (hrp_final_out h s)) tag; F3; F4; F5; ht4_minusp mp gv])))).
Proof.
  intros. unfold ht4rt_g_s7. abbreviate_semax.
  forward_call (Tsh, v_p, r, h, s, tsh, tag, gv).
  entailer!.
Qed.

Lemma ht4rt_tag_body : haead_hyps ->
  semax_body [] (ht4r_Gprog mp) WgNoise.harness.x_prim_aead.code.f_ref_aead_tag (ref_aead_tag_spec_n mp).
Proof.
  intros HH.
  start_function.
  eapply semax_seq'.
  { apply ht4rt_g_block_call; auto. }
  unfold MORE_COMMANDS, abbreviate. Intros blk. rename H3 into Hfin, H4 into Hbl.
  pose proof (ht4rt_g_r_len HH blk Hbl) as Hr.
  assert (Hz: Zlength hrp_zero17 = 17) by reflexivity.
  pose proof (ht4rt_g_padded_len HH (hrp_init_r blk) hrp_zero17 a Hz) as Hh1.
  pose proof (ht4rt_g_padded_len HH (hrp_init_r blk) _ ct Hh1) as Hh2.
  pose proof (ht4rt_g_block_len HH (hrp_init_r blk) _ (le64_bytes (Zlength a) ++ le64_bytes (Zlength ct)) Hh2) as Hh3.
  assert (HL: Zlength (le64_bytes (Zlength a) ++ le64_bytes (Zlength ct)) = 16)
    by (rewrite Zlength_app, !ht4rt_g_le64_len; reflexivity).
  eapply semax_seq'. { apply ht4rt_g_init_ok; auto. }
  eapply semax_seq'. { apply ht4rt_g_pad_ad_ok; auto. }
  eapply semax_seq'. { apply ht4rt_g_pad_ct_ok; auto. }
  eapply semax_seq'. { apply ht4rt_g_le1_ok; auto. }
  eapply semax_seq'. { apply ht4rt_g_le2_ok; auto. }
  eapply semax_seq'. { apply ht4rt_g_blk_ok; auto. }
  eapply ConseqFacts.semax_post''.
  2: { apply ht4rt_g_final_ok; auto. }
  unfold POSTCONDITION, abbreviate. simpl_ret_assert.
  remember (haead_padded (hrp_init_r blk) hrp_zero17 a) as h1 eqn:E1. apply ht4rt_g_mk1 in E1.
  remember (haead_padded (hrp_init_r blk) h1 ct) as h2 eqn:E2. apply ht4rt_g_mk2 in E2.
  remember (le64_bytes (Zlength a) ++ le64_bytes (Zlength ct)) as L eqn:EL. apply ht4rt_g_mkL in EL.
  rewrite (ht4rt_g_close key nonce a ct blk h1 h2 L Hfin E1 E2 EL Hbl). clear Hfin E1 E2 EL.
  generalize (poly1305_tag (aead_otk (aead_st key nonce)) (aead_mac_data a ct)); intros T.
  generalize (hrp_final_h (hrp_block (hrp_init_r blk) h2 L) (hrp_init_s blk)); intros hf.
  clear Hh3 HH.
  entailer!.
  rewrite Hbl. apply data_at_data_at_.
Qed.

End HT4RT.

Lemma ht4r_tag_bodies (mp: ident) : haead_hyps ->
  semax_body [] (ht4r_Gprog mp) WgNoise.harness.x_prim_aead.code.f_rp_padded rp_padded_spec_n /\
  semax_body [] (ht4r_Gprog mp) WgNoise.harness.x_prim_aead.code.f_ref_aead_tag (ref_aead_tag_spec_n mp).
Proof.
  intros HH. split; [apply ht4rt_padded_body | apply ht4rt_tag_body]; exact HH.
Qed.
