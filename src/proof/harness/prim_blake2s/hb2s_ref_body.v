(* body of the reference ref_blake2s of law prim_blake2s (common.h) against model.v's blake2s. *)
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

(* ---------------------------------------------------------------------- *)
(* Pure facts: the reference's block loop is model.v's b2s_compress_n      *)
(* ---------------------------------------------------------------------- *)

Lemma hb2s_ref_compress_n_snoc: forall n h t f inc d,
  64 * Z.of_nat (S n) <= Zlength d ->
  b2s_compress_n (S n) h t f inc d =
  b2s_compress_block (b2s_compress_n n h t f inc d)
    (sublist (64 * Z.of_nat n) (64 * Z.of_nat n + 64) d) (t + inc * Z.of_nat (S n)) f.
Proof.
  induction n; intros.
  - simpl. f_equal. lia.
  - change (b2s_compress_n (S (S n)) h t f inc d) with
      (b2s_compress_n (S n) (b2s_compress_block h (sublist 0 64 d) (t + inc) f) (t + inc) f inc
         (sublist 64 (Zlength d) d)).
    rewrite IHn by (rewrite Zlength_sublist by lia; lia).
    simpl (b2s_compress_n (S n) h t f inc d).
    f_equal.
    + rewrite sublist_sublist by lia. f_equal; lia.
    + lia.
Qed.

Lemma hb2s_ref_compress_n_prefix: forall n h t f inc d L,
  64 * Z.of_nat n <= L <= Zlength d ->
  b2s_compress_n n h t f inc (sublist 0 L d) = b2s_compress_n n h t f inc d.
Proof.
  induction n; intros; cbn [b2s_compress_n]; [reflexivity|].
  rewrite Zlength_sublist by lia.
  rewrite !sublist_sublist by lia.
  rewrite Nat2Z.inj_succ in H.
  replace (0 + 0) with 0 by lia. replace (64 + 0) with 64 by lia. replace (L - 0 + 0) with L by lia.
  rewrite <- (IHn _ _ _ _ (sublist 64 (Zlength d) d) (L - 64)) by (rewrite Zlength_sublist by lia; lia).
  rewrite sublist_sublist by lia. f_equal. f_equal; lia.
Qed.

(* the parameter word: the three xor-ed fields do not overlap *)
Lemma hb2s_ref_param: forall keylen outlen, 0 <= keylen <= 32 -> 1 <= outlen <= 32 ->
  Int.xor (Int.xor (Int.repr 16842752) (Int.shl (Int.repr keylen) (Int.repr 8))) (Int.repr outlen) =
  Int.repr (16842752 + keylen * 256 + outlen).
Proof.
  intros.
  assert (H1: forallb (fun k => forallb (fun o =>
     Int.eq (Int.xor (Int.xor (Int.repr 16842752) (Int.shl (Int.repr k) (Int.repr 8))) (Int.repr o))
            (Int.repr (16842752 + k * 256 + o))) (map Z.of_nat (seq 1 32))) (map Z.of_nat (seq 0 33)) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H1.
  specialize (H1 keylen). rewrite forallb_forall in H1.
  specialize (H1 ltac:(apply in_map_iff; exists (Z.to_nat keylen); split; [lia | apply in_seq; lia]) outlen
    ltac:(apply in_map_iff; exists (Z.to_nat outlen); split; [lia | apply in_seq; lia])).
  apply Int.same_if_eq in H1. auto.
Qed.

(* the state compressed into the digest (blake2s = b2s_out of it) *)
Definition hb2s_ref_hfin (key: list byte) (outlen: Z) (msg: list byte) : list int :=
  let s := b2s_stream key msg in
  let last := b2s_lastblock s in
  b2s_compress_block (b2s_h_nonfinal (Zlength key) outlen s)
    (last ++ Zrepeat Byte.zero (64 - Zlength last)) (Zlength s) Int.mone.

Lemma hb2s_ref_hfin_out: forall key outlen msg,
  blake2s key outlen msg = b2s_out outlen (hb2s_ref_hfin key outlen msg).
Proof. reflexivity. Qed.

(* the state after the key block (if any), and its counter *)
Definition hb2s_ref_hs (key: list byte) (outlen: Z) (f0: int) : list int :=
  if Zlength key =? 0 then b2s_h0 0 outlen
  else b2s_compress_block (b2s_h0 (Zlength key) outlen) (key ++ Zrepeat Byte.zero (64 - Zlength key)) 64 f0.

Definition hb2s_ref_t0 (key: list byte) : Z := if Zlength key =? 0 then 0 else 64.

(* keyed, empty message: the key block is the last block *)
Lemma hb2s_ref_hfin_key_only: forall key outlen,
  0 < Zlength key <= 32 ->
  hb2s_ref_hfin key outlen [] = hb2s_ref_hs key outlen Int.mone.
Proof.
  intros. unfold hb2s_ref_hfin, hb2s_ref_hs, b2s_stream, b2s_keyblock, b2s_lastblock, b2s_h_nonfinal,
    b2s_nfull, b2s_blocks.
  destruct (Zlength key =? 0) eqn:E; [lia |].
  rewrite app_nil_r.
  assert (Hl: Zlength (key ++ Zrepeat Byte.zero (64 - Zlength key)) = 64) by list_solve.
  rewrite Hl. change ((64 - 1) / 64) with 0. simpl Z.to_nat. cbn [b2s_compress_n].
  change (64 * (if 64 =? 0 then 0 else 0)) with 0.
  rewrite sublist_same by lia. rewrite Hl. f_equal. list_solve.
Qed.

(* the message loop: j full blocks, then the last (partial) block *)
Lemma hb2s_ref_hfin_loop: forall key outlen msg j,
  0 <= Zlength key <= 32 ->
  (Zlength key = 0 \/ 0 < Zlength msg) ->
  0 <= 64 * j <= Zlength msg -> (j = 0 \/ 64 * j < Zlength msg) -> Zlength msg - 64 * j <= 64 ->
  hb2s_ref_hfin key outlen msg =
  b2s_compress_block (b2s_compress_n (Z.to_nat j) (hb2s_ref_hs key outlen Int.zero) (hb2s_ref_t0 key)
                        Int.zero 64 msg)
    (sublist (64 * j) (Zlength msg) msg ++ Zrepeat Byte.zero (64 - (Zlength msg - 64 * j)))
    (hb2s_ref_t0 key + Zlength msg) Int.mone.
Proof.
  intros key outlen msg j Hk Hkm Hj Hj2 Hj3.
  unfold hb2s_ref_hfin, hb2s_ref_hs, hb2s_ref_t0, b2s_stream, b2s_keyblock, b2s_lastblock, b2s_h_nonfinal,
    b2s_nfull, b2s_blocks.
  destruct (Zlength key =? 0) eqn:E.
  - apply Z.eqb_eq in E. rewrite E. rewrite app_nil_l.
    destruct (Zlength msg =? 0) eqn:E2.
    + apply Z.eqb_eq in E2. assert (j = 0) by lia. subst j.
      simpl Z.to_nat. cbn [b2s_compress_n]. rewrite E2. reflexivity.
    + apply Z.eqb_neq in E2.
      assert (Hd: (Zlength msg - 1) / 64 = j) by (symmetry; apply Z.div_unique with (Zlength msg - 1 - 64 * j); lia).
      rewrite Hd. rewrite Zlength_sublist by lia.
      replace ((64 * j - 0) / 64) with j by (rewrite Z.sub_0_r, Z.mul_comm, Z.div_mul; lia).
      rewrite hb2s_ref_compress_n_prefix by lia.
      f_equal. f_equal. f_equal. rewrite Zlength_sublist by lia. lia.
  - apply Z.eqb_neq in E. destruct Hkm as [Hkm | Hkm]; [lia |].
    set (kb := key ++ Zrepeat Byte.zero (64 - Zlength key)).
    assert (Hl: Zlength kb = 64) by (subst kb; list_solve).
    rewrite Zlength_app, Hl.
    replace (64 + Zlength msg =? 0) with false by lia.
    assert (Hd: (64 + Zlength msg - 1) / 64 = j + 1)
      by (symmetry; apply Z.div_unique with (Zlength msg - 1 - 64 * j); lia).
    rewrite Hd.
    rewrite Zlength_sublist by (rewrite ?Zlength_app; lia).
    replace ((64 * (j + 1) - 0) / 64) with (j + 1) by (rewrite Z.sub_0_r, Z.mul_comm, Z.div_mul; lia).
    replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
    cbn [b2s_compress_n].
    rewrite Zlength_sublist by (rewrite ?Zlength_app; lia).
    rewrite !sublist_sublist by (rewrite ?Zlength_app; lia).
    replace (0 + 0) with 0 by lia. replace (0 + 64) with 64 by lia.
    replace (64 * (j + 1) - 0 + 0) with (64 + 64 * j) by lia.
    rewrite sublist_app1 by lia. rewrite sublist_same by lia.
    rewrite sublist_app2 by lia. rewrite Hl.
    replace (64 - 64) with 0 by lia. replace (64 + 64 * j - 64) with (64 * j) by lia.
    rewrite hb2s_ref_compress_n_prefix by lia.
    replace (0 + 64) with 64 by lia.
    rewrite sublist_app2 by lia. rewrite Hl.
    replace (64 * (j + 1) - 64) with (64 * j) by lia. replace (64 + Zlength msg - 64) with (Zlength msg) by lia.
    f_equal. f_equal. f_equal. rewrite Zlength_sublist by lia. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* Byte slices                                                             *)
(* ---------------------------------------------------------------------- *)

Lemma hb2s_ref_slice {cs: compspecs} sh n lo hi (bs: list byte) p:
  0 <= lo <= hi -> hi <= n -> Zlength bs = n ->
  data_at sh (tarray tuchar n) (map Vubyte bs) p |--
  data_at sh (tarray tuchar (Zlength (sublist lo hi bs))) (map Vubyte (sublist lo hi bs)) (offset_val lo p) *
  (data_at sh (tarray tuchar (Zlength (sublist lo hi bs))) (map Vubyte (sublist lo hi bs)) (offset_val lo p)
   -* data_at sh (tarray tuchar n) (map Vubyte bs) p).
Proof.
  intros.
  assert_PROP (field_compatible (tarray tuchar n) [] p) by entailer!.
  rewrite (split3_data_at_Tarray_tuchar sh n lo hi (map Vubyte bs) p) by (try list_solve; lia).
  rewrite Zlength_sublist by lia.
  rewrite field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. replace (0 + 1 * lo) with lo by lia.
  rewrite <- !sublist_map.
  match goal with |- ?A * ?B * ?C |-- _ => apply derives_trans with (B * (A * C))%logic; [cancel |] end.
  apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint. cancel.
Qed.

Lemma hb2s_ref_prefix {cs: compspecs} sh n hi (bs: list byte) p:
  0 <= hi <= n -> Zlength bs = n ->
  data_at sh (tarray tuchar n) (map Vubyte bs) p |--
  data_at sh (tarray tuchar (Zlength (sublist 0 hi bs))) (map Vubyte (sublist 0 hi bs)) p *
  (data_at sh (tarray tuchar (Zlength (sublist 0 hi bs))) (map Vubyte (sublist 0 hi bs)) p
   -* data_at sh (tarray tuchar n) (map Vubyte bs) p).
Proof.
  intros.
  assert_PROP (isptr p) by entailer!.
  rewrite <- (isptr_offset_val_zero p) at 2 3 by auto.
  apply hb2s_ref_slice; lia.
Qed.

Lemma hb2s_ref_resize {cs: compspecs} sh n m p:
  n = m -> data_at_ sh (tarray tuchar n) p |-- data_at_ sh (tarray tuchar m) p.
Proof. intros; subst; auto. Qed.

Lemma hb2s_ref_split {cs: compspecs} sh n n1 (v: list val) p:
  0 <= n1 <= n -> Zlength v = n ->
  data_at sh (tarray tuchar n) v p |--
  data_at_ sh (tarray tuchar n1) p *
  data_at sh (tarray tuchar (n - n1)) (sublist n1 n v) (field_address0 (tarray tuchar n) (SUB n1) p).
Proof.
  intros. unfold tarray. rewrite (split2_data_at_Tarray_tuchar sh n n1 v p) by auto.
  cancel.
Qed.

Lemma hb2s_ref_join {cs: compspecs} sh n n1 (v1 v2: list val) p:
  0 <= n1 <= n -> Zlength v1 = n1 -> Zlength v2 = n - n1 ->
  data_at sh (tarray tuchar n1) v1 p *
  data_at sh (tarray tuchar (n - n1)) v2 (field_address0 (tarray tuchar n) (SUB n1) p) |--
  data_at sh (tarray tuchar n) (v1 ++ v2) p.
Proof.
  intros. unfold tarray. rewrite (split2_data_at_Tarray_tuchar sh n n1 (v1 ++ v2) p) by (try list_solve; lia).
  rewrite sublist_app1 by lia. rewrite sublist_app2 by lia.
  rewrite sublist_same by lia. rewrite sublist_same by lia. replace (n1 - Zlength v1) with 0 by lia.
  apply derives_refl.
Qed.

Lemma hb2s_ref_byte: forall x: int,
  Vint (Int.zero_ext 8 x) = Vubyte (Byte.repr (Int.unsigned x)).
Proof.
  intros. unfold Vubyte. f_equal.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 x)).
  rewrite Int.zero_ext_mod by (cbv; intuition congruence).
  rewrite Byte.unsigned_repr_eq. reflexivity.
Qed.

Lemma hb2s_ref_compress_len: forall h blk t f, Zlength (b2s_compress_block h blk t f) = 8.
Proof. intros. unfold b2s_compress_block, b2s_compress, b2s_feed. rewrite Zlength_map. reflexivity. Qed.

Lemma hb2s_ref_compress_n_len: forall n h t f inc d,
  Zlength h = 8 -> Zlength (b2s_compress_n n h t f inc d) = 8.
Proof. induction n; intros; cbn [b2s_compress_n]; [assumption | apply IHn, hb2s_ref_compress_len]. Qed.

Lemma hb2s_ref_hs_len: forall key outlen f, Zlength (hb2s_ref_hs key outlen f) = 8.
Proof.
  intros. unfold hb2s_ref_hs. destruct (_ =? 0).
  - unfold b2s_h0. rewrite upd_Znth_Zlength by (cbv; intuition congruence). reflexivity.
  - apply hb2s_ref_compress_len.
Qed.

Lemma hb2s_ref_out_len: forall outlen h, 0 <= outlen -> Zlength (b2s_out outlen h) = outlen.
Proof.
  intros. unfold b2s_out. rewrite Zlength_map, Zlength_upto. lia.
Qed.

Lemma hb2s_ref_out_nth: forall outlen h i, 0 <= i < outlen ->
  Znth i (b2s_out outlen h) = Byte.repr (Int.unsigned (Int.shru (Znth (i / 4) h) (Int.repr (8 * (i mod 4))))).
Proof.
  intros. unfold b2s_out. rewrite Znth_map by (rewrite Zlength_upto; lia).
  rewrite Znth_upto by lia. reflexivity.
Qed.

Import WgNoise.harness.x_prim_blake2s.code.

Lemma hb2s_ref_body :
  semax_body hb2s_V hb2s_Gprog WgNoise.harness.x_prim_blake2s.code.f_ref_blake2s ref_blake2s_spec.
Proof.
  start_function.
  unfold hb2s_globals. Intros.
  forward_if (temp _t'1 (Vint (Int.repr (hb2s_ref_t0 (sublist 0 keylen kbuf))))).
  { forward. entailer!. rewrite !Int64.unsigned_repr in H3 by rep_lia.
    unfold hb2s_ref_t0. rewrite Zlength_sublist by lia. destruct (Z.eqb_spec (keylen - 0) 0); auto; lia. }
  { forward. entailer!. rewrite !Int64.unsigned_repr in H3 by rep_lia.
    unfold hb2s_ref_t0. rewrite Zlength_sublist by lia. destruct (Z.eqb_spec (keylen - 0) 0); auto; lia. }
  assert (Ht0: Int.signed (Int.repr (hb2s_ref_t0 (sublist 0 keylen kbuf))) = hb2s_ref_t0 (sublist 0 keylen kbuf))
    by (unfold hb2s_ref_t0; destruct (_ =? 0); reflexivity).
  forward. rewrite Ht0. forward. forward.
  forward_for_simple_bound 8 (EX i: Z,
    PROP () LOCAL (temp _total (Vlong (Int64.repr (hb2s_ref_t0 (sublist 0 keylen kbuf) + Zlength data)));
      temp _done (Vlong (Int64.repr 0)); temp _pos (Vlong (Int64.repr 0));
      lvar _block (tarray tuchar 64) v_block; lvar _h (tarray tuint 8) v_h; gvars gv; temp _out out;
      temp _outlen (Vlong (Int64.repr outlen)); temp _key k; temp _keylen (Vlong (Int64.repr keylen));
      temp _in d; temp _inlen (Vlong (Int64.repr (Zlength data))))
    SEP (data_at_ Tsh (tarray tuchar 64) v_block;
         data_at Tsh (tarray tuint 8) (map Vint (sublist 0 i b2s_IV) ++ Zrepeat Vundef (8 - i)) v_h;
         data_at_ osh (tarray tuchar outlen) out;
         data_at ksh (tarray tuchar (Zlength kbuf)) (map Vubyte kbuf) k;
         data_at dsh (tarray tuchar (Zlength data)) (map Vubyte data) d;
         data_at Ers (tarray tuint 8) (map Vint b2s_IV) (gv HB._RB2S_IV);
         data_at Ers (tarray (tarray tuchar 16) 10) blake2s_sigma_val (gv HB._RB2S_SIGMA))).
  { entailer!. }
  { forward. forward. entailer!. apply derives_refl'. f_equal. list_solve. }
  rewrite (sublist_same 0 8 b2s_IV) by reflexivity. rewrite Z.sub_diag, app_nil_r.
  gather_SEP (data_at Ers (tarray tuint 8) _ _) (data_at Ers (tarray (tarray tuchar 16) 10) _ _).
  fold (hb2s_globals gv).
  assert (HIV: Zlength b2s_IV = 8) by reflexivity.
  forward. forward.
  assert (Hkl: Zlength (sublist 0 keylen kbuf) = keylen) by (rewrite Zlength_sublist; lia).
  replace (upd_Znth 0 _ _) with (map Vint (b2s_h0 keylen outlen)).
  2: { unfold b2s_h0. rewrite upd_Znth_map. f_equal. f_equal.
       rewrite !Int64.Z_mod_modulus_eq, !Z.mod_small by rep_lia. rewrite hb2s_ref_param by lia. reflexivity. }
  forward_if (PROP () LOCAL (temp _done (Vlong (Int64.repr (hb2s_ref_t0 (sublist 0 keylen kbuf))));
      temp _total (Vlong (Int64.repr (hb2s_ref_t0 (sublist 0 keylen kbuf) + Zlength data)));
      temp _pos (Vlong (Int64.repr 0));
      lvar _block (tarray tuchar 64) v_block; lvar _h (tarray tuint 8) v_h; gvars gv; temp _out out;
      temp _outlen (Vlong (Int64.repr outlen)); temp _key k; temp _keylen (Vlong (Int64.repr keylen));
      temp _in d; temp _inlen (Vlong (Int64.repr (Zlength data))))
    SEP (data_at_ Tsh (tarray tuchar 64) v_block;
         data_at Tsh (tarray tuint 8)
           (map Vint (hb2s_ref_hs (sublist 0 keylen kbuf) outlen
              (if Zlength data =? 0 then Int.mone else Int.zero))) v_h;
         data_at_ osh (tarray tuchar outlen) out;
         data_at ksh (tarray tuchar (Zlength kbuf)) (map Vubyte kbuf) k;
         data_at dsh (tarray tuchar (Zlength data)) (map Vubyte data) d;
         hb2s_globals gv)).
  { rewrite !Int64.unsigned_repr in H3 by rep_lia.
    forward_call (Tsh, v_block, 0, 64).
    sep_apply (hb2s_ref_prefix ksh (Zlength kbuf) keylen kbuf k ltac:(lia) eq_refl).
    sep_apply (hb2s_ref_split Tsh 64 (Zlength (sublist 0 keylen kbuf)) (Zrepeat (Vubyte (Byte.repr 0)) 64) v_block
      ltac:(lia) ltac:(list_solve)).
    flatten_sepcon_in_SEP.
    forward_call (Tsh, v_block, ksh, k, sublist 0 keylen kbuf).
    { entailer!. rewrite Hkl. reflexivity. }
    sep_apply (wand_frame_elim
      (data_at ksh (tarray tuchar (Zlength (sublist 0 keylen kbuf))) (map Vubyte (sublist 0 keylen kbuf)) k)
      (data_at ksh (tarray tuchar (Zlength kbuf)) (map Vubyte kbuf) k)).
    sep_apply (hb2s_ref_join Tsh 64 (Zlength (sublist 0 keylen kbuf)) (map Vubyte (sublist 0 keylen kbuf))
      (sublist (Zlength (sublist 0 keylen kbuf)) 64 (Zrepeat (Vubyte (Byte.repr 0)) 64)) v_block
      ltac:(lia) ltac:(list_solve) ltac:(list_solve)).
    replace (map Vubyte (sublist 0 keylen kbuf) ++ _)
      with (map Vubyte (sublist 0 keylen kbuf ++ Zrepeat Byte.zero (64 - Zlength (sublist 0 keylen kbuf))))
      by (rewrite map_app, map_Zrepeat; f_equal; list_solve).
    forward.
    forward_call (Tsh, v_h, b2s_h0 keylen outlen, Tsh, v_block,
      sublist 0 keylen kbuf ++ Zrepeat Byte.zero (64 - Zlength (sublist 0 keylen kbuf)), 64,
      if Zlength data =? 0 then 1 else 0, gv).
    { entailer!. destruct (Z.eqb_spec (Zlength data) 0) as [E|E].
      - rewrite E. reflexivity.
      - unfold Int64.eq. rewrite !Int64.unsigned_repr by rep_lia. rewrite zeq_false by auto. reflexivity. }
    { split; [list_solve | destruct (_ =? 0); rep_lia]. }
    assert (Hf: (if Z.eq_dec (if Zlength data =? 0 then 1 else 0) 0 then Int.zero else Int.mone) =
                (if Zlength data =? 0 then Int.mone else Int.zero)) by (destruct (_ =? 0); reflexivity).
    rewrite Hf.
    entailer!; unfold hb2s_ref_hs, hb2s_ref_t0; rewrite Hkl; destruct (Z.eqb_spec keylen 0); try lia;
      auto; apply derives_refl. }
  { forward. rewrite !Int64.unsigned_repr in H3 by rep_lia. assert (keylen = 0) by lia. subst keylen.
    entailer!; unfold hb2s_ref_hs, hb2s_ref_t0; rewrite Hkl; destruct (Z.eqb_spec 0 0); try lia;
      auto; apply derives_refl. }
  forward_if (temp _t'2 (Vint (Int.repr (if orb (keylen =? 0) (0 <? Zlength data) then 1 else 0)))).
  { forward. entailer!. apply (f_equal Int64.unsigned) in H3.
    rewrite Int64.unsigned_repr in H3 by rep_lia. change (Int64.unsigned Int64.zero) with 0 in H3.
    destruct (Z.eqb_spec keylen 0); [reflexivity | lia]. }
  { forward. entailer!.
    destruct (Z.eqb_spec keylen 0) as [E|E].
    { subst keylen. contradiction H3. reflexivity. }
    simpl orb. unfold bool2val, Int64.cmpu, Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
    destruct (Z.ltb_spec 0 (Zlength data)), (zlt 0 (Zlength data)); try lia; reflexivity. }
  set (key := sublist 0 keylen kbuf) in *.
  set (hfin := hb2s_ref_hfin key outlen data).
  forward_if (PROP () LOCAL (lvar _block (tarray tuchar 64) v_block; lvar _h (tarray tuint 8) v_h; gvars gv;
      temp _out out; temp _outlen (Vlong (Int64.repr outlen)))
    SEP (data_at_ Tsh (tarray tuchar 64) v_block;
         data_at Tsh (tarray tuint 8) (map Vint hfin) v_h;
         data_at_ osh (tarray tuchar outlen) out;
         data_at ksh (tarray tuchar (Zlength kbuf)) (map Vubyte kbuf) k;
         data_at dsh (tarray tuchar (Zlength data)) (map Vubyte data) d;
         hb2s_globals gv)).
  { assert (Hkm: keylen = 0 \/ 0 < Zlength data).
    { destruct (Z.eqb_spec keylen 0); [auto |].
      destruct (Z.ltb_spec 0 (Zlength data)); [auto | simpl in H3'; lia]. }
    assert (Hhs: hb2s_ref_hs key outlen (if Zlength data =? 0 then Int.mone else Int.zero) =
                 hb2s_ref_hs key outlen Int.zero).
    { unfold hb2s_ref_hs. rewrite Hkl. destruct (Z.eqb_spec keylen 0); [reflexivity |].
      destruct (Z.eqb_spec (Zlength data) 0); [lia | reflexivity]. }
    rewrite Hhs.
    set (t0 := hb2s_ref_t0 key) in *.
    assert (Ht0r: t0 = 0 \/ t0 = 64) by (unfold t0, hb2s_ref_t0; destruct (Zlength key =? 0); [left | right]; reflexivity).
    set (hs := hb2s_ref_hs key outlen Int.zero).
    forward_while (EX j: Z, PROP (0 <= 64 * j <= Zlength data; j = 0 \/ 64 * j < Zlength data)
      LOCAL (temp _done (Vlong (Int64.repr (t0 + 64 * j)));
        temp _total (Vlong (Int64.repr (t0 + Zlength data)));
        temp _pos (Vlong (Int64.repr (64 * j))); lvar _block (tarray tuchar 64) v_block;
        lvar _h (tarray tuint 8) v_h; gvars gv; temp _out out;
        temp _outlen (Vlong (Int64.repr outlen)); temp _key k;
        temp _keylen (Vlong (Int64.repr keylen)); temp _in d;
        temp _inlen (Vlong (Int64.repr (Zlength data))))
      SEP (data_at_ Tsh (tarray tuchar 64) v_block;
        data_at Tsh (tarray tuint 8) (map Vint (b2s_compress_n (Z.to_nat j) hs t0 Int.zero 64 data)) v_h;
        data_at_ osh (tarray tuchar outlen) out;
        data_at ksh (tarray tuchar (Zlength kbuf)) (map Vubyte kbuf) k;
        data_at dsh (tarray tuchar (Zlength data)) (map Vubyte data) d;
        hb2s_globals gv)).
    { Exists 0. entailer!. }
    { entailer!. }
    { sep_apply (hb2s_ref_slice dsh (Zlength data) (64 * j) (64 * j + 64) data d ltac:(lia) ltac:(lia) eq_refl).
      flatten_sepcon_in_SEP.
      assert (Hz: Zlength (sublist (64 * j) (64 * j + 64) data) = 64) by (rewrite Zlength_sublist; lia).
      sep_apply (hb2s_ref_resize Tsh 64 (Zlength (sublist (64 * j) (64 * j + 64) data)) v_block (eq_sym Hz)).
      forward_call (Tsh, v_block, dsh, offset_val (64 * j) d, sublist (64 * j) (64 * j + 64) data).
      { entailer!. rewrite Hz. reflexivity. }
      sep_apply (wand_frame_elim
        (data_at dsh (tarray tuchar (Zlength (sublist (64 * j) (64 * j + 64) data)))
           (map Vubyte (sublist (64 * j) (64 * j + 64) data)) (offset_val (64 * j) d))
        (data_at dsh (tarray tuchar (Zlength data)) (map Vubyte data) d)).
      rewrite Hz.
      forward. forward.
      assert (Hhl: Zlength (b2s_compress_n (Z.to_nat j) hs t0 Int.zero 64 data) = 8)
        by (apply hb2s_ref_compress_n_len, hb2s_ref_hs_len).
      forward_call (Tsh, v_h, b2s_compress_n (Z.to_nat j) hs t0 Int.zero 64 data, Tsh, v_block,
        sublist (64 * j) (64 * j + 64) data, t0 + 64 * j + 64, 0, gv).
      Exists (j + 1).
      assert (Hsn: b2s_compress_n (Z.to_nat (j + 1)) hs t0 Int.zero 64 data =
        b2s_compress_block (b2s_compress_n (Z.to_nat j) hs t0 Int.zero 64 data)
          (sublist (64 * j) (64 * j + 64) data) (t0 + 64 * j + 64) Int.zero).
      { replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
        rewrite hb2s_ref_compress_n_snoc by lia.
        rewrite Nat2Z.inj_succ, Z2Nat.id by lia. f_equal. lia. }
      rewrite Hsn. rewrite if_true by reflexivity.
      change (Int.signed (Int.repr 64)) with 64. rewrite !add64_repr.
      replace (t0 + 64 * (j + 1)) with (t0 + 64 * j + 64) by lia.
      replace (64 * (j + 1)) with (64 * j + 64) by lia.
      entailer!. }
    assert (Hzl: Zlength (sublist (64 * j) (Zlength data) data) = Zlength data - 64 * j)
      by (rewrite Zlength_sublist; lia).
    forward_call (Tsh, v_block, 0, 64).
    sep_apply (hb2s_ref_slice dsh (Zlength data) (64 * j) (Zlength data) data d ltac:(lia) ltac:(lia) eq_refl).
    flatten_sepcon_in_SEP.
    sep_apply (hb2s_ref_split Tsh 64 (Zlength (sublist (64 * j) (Zlength data) data))
      (Zrepeat (Vubyte (Byte.repr 0)) 64) v_block ltac:(lia) ltac:(list_solve)).
    flatten_sepcon_in_SEP.
    forward_call (Tsh, v_block, dsh, offset_val (64 * j) d, sublist (64 * j) (Zlength data) data).
    { entailer!. rewrite Hzl. reflexivity. }
    sep_apply (wand_frame_elim
      (data_at dsh (tarray tuchar (Zlength (sublist (64 * j) (Zlength data) data)))
         (map Vubyte (sublist (64 * j) (Zlength data) data)) (offset_val (64 * j) d))
      (data_at dsh (tarray tuchar (Zlength data)) (map Vubyte data) d)).
    sep_apply (hb2s_ref_join Tsh 64 (Zlength (sublist (64 * j) (Zlength data) data))
      (map Vubyte (sublist (64 * j) (Zlength data) data))
      (sublist (Zlength (sublist (64 * j) (Zlength data) data)) 64 (Zrepeat (Vubyte (Byte.repr 0)) 64)) v_block
      ltac:(lia) ltac:(list_solve) ltac:(list_solve)).
    replace (map Vubyte (sublist (64 * j) (Zlength data) data) ++ _)
      with (map Vubyte (sublist (64 * j) (Zlength data) data ++ Zrepeat Byte.zero (64 - (Zlength data - 64 * j))))
      by (rewrite map_app, map_Zrepeat; f_equal; rewrite Hzl; list_solve).
    assert (Hhl: Zlength (b2s_compress_n (Z.to_nat j) hs t0 Int.zero 64 data) = 8)
      by (apply hb2s_ref_compress_n_len, hb2s_ref_hs_len).
    forward_call (Tsh, v_h, b2s_compress_n (Z.to_nat j) hs t0 Int.zero 64 data, Tsh, v_block,
      sublist (64 * j) (Zlength data) data ++ Zrepeat Byte.zero (64 - (Zlength data - 64 * j)),
      t0 + Zlength data, 1, gv).
    { rewrite Zlength_app, Hzl, Zlength_Zrepeat by lia. lia. }
    rewrite if_false by lia.
    entailer!.
    unfold hfin. rewrite (hb2s_ref_hfin_loop key outlen data j) by lia.
    cancel.
  }
  { forward.
    apply (f_equal Int.unsigned) in H3. rewrite Int.unsigned_repr in H3 by (destruct (_ || _)%bool; rep_lia).
    change (Int.unsigned Int.zero) with 0 in H3.
    destruct (Z.eqb_spec keylen 0); [simpl in H3; lia |].
    destruct (Z.ltb_spec 0 (Zlength data)); [simpl in H3; lia |].
    assert (Hd: data = []) by (apply Zlength_nil_inv; list_solve). subst data.
    entailer!. unfold hfin. rewrite hb2s_ref_hfin_key_only by lia. apply derives_refl. }
  assert (Hhl: Zlength hfin = 8) by apply hb2s_ref_compress_len.
  forward_loop (EX i: Z, PROP (0 <= i <= outlen) LOCAL (temp _i (Vint (Int.repr i));
      lvar _block (tarray tuchar 64) v_block; lvar _h (tarray tuint 8) v_h; gvars gv; temp _out out;
      temp _outlen (Vlong (Int64.repr outlen)))
    SEP (data_at_ Tsh (tarray tuchar 64) v_block;
         data_at Tsh (tarray tuint 8) (map Vint hfin) v_h;
         data_at osh (tarray tuchar outlen)
           (map Vubyte (sublist 0 i (b2s_out outlen hfin)) ++ Zrepeat Vundef (outlen - i)) out;
         data_at ksh (tarray tuchar (Zlength kbuf)) (map Vubyte kbuf) k;
         data_at dsh (tarray tuchar (Zlength data)) (map Vubyte data) d;
         hb2s_globals gv))
    continue: (EX i: Z, PROP (0 <= i < outlen) LOCAL (temp _i (Vint (Int.repr i));
      lvar _block (tarray tuchar 64) v_block; lvar _h (tarray tuint 8) v_h; gvars gv; temp _out out;
      temp _outlen (Vlong (Int64.repr outlen)))
    SEP (data_at_ Tsh (tarray tuchar 64) v_block;
         data_at Tsh (tarray tuint 8) (map Vint hfin) v_h;
         data_at osh (tarray tuchar outlen)
           (map Vubyte (sublist 0 (i + 1) (b2s_out outlen hfin)) ++ Zrepeat Vundef (outlen - (i + 1))) out;
         data_at ksh (tarray tuchar (Zlength kbuf)) (map Vubyte kbuf) k;
         data_at dsh (tarray tuchar (Zlength data)) (map Vubyte data) d;
         hb2s_globals gv)).
  { forward. Exists 0. entailer!. simpl app. apply derives_refl. }
  { Intros i. forward_if.
    { rewrite !Int64.unsigned_repr in H4 by rep_lia.
      assert (Hi4: 0 <= i / 4 < 8) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      assert (Hdiv: Int.signed (Int.divs (Int.repr i) (Int.repr 4)) = i / 4).
      { unfold Int.divs. rewrite (Int.signed_repr i), (Int.signed_repr 4) by rep_lia.
        rewrite Z.quot_div_nonneg by lia.
        apply Int.signed_repr. rep_lia. }
      assert (Hmod: Int.mods (Int.repr i) (Int.repr 4) = Int.repr (i mod 4)).
      { unfold Int.mods. rewrite (Int.signed_repr i), (Int.signed_repr 4) by rep_lia.
        rewrite Z.rem_mod_nonneg by lia. reflexivity. }
      forward.
      { entailer!. destruct H18 as [_ H18]. apply (f_equal Int.signed) in H18.
        rewrite Int.signed_repr in H18 by rep_lia. rewrite Int.signed_mone in H18. lia. }
      rewrite Hdiv.
      forward.
      { entailer!. rewrite Hmod, mul_repr.
        assert (0 <= i mod 4 < 4) by (apply Z.mod_pos_bound; lia).
        rewrite Int.unsigned_repr, Int.signed_repr by rep_lia.
        split; [change (Int.unsigned Int.iwordsize) with 32; lia | split; [rep_lia |]].
        intros [_ X]. apply (f_equal Int.signed) in X.
        rewrite Int.signed_repr in X by rep_lia. rewrite Int.signed_mone in X. lia. }
      change (let (q, _) := Z.div_eucl i 4 in q) with (i / 4).
      Exists i. entailer!.
      apply derives_refl'. f_equal.
      rewrite Hmod, mul_repr, Int.zero_ext_idem by lia. rewrite hb2s_ref_byte.
      rewrite <- (hb2s_ref_out_nth outlen hfin i) by lia.
      assert (Hol: Zlength (b2s_out outlen hfin) = outlen) by (apply hb2s_ref_out_len; lia).
      list_solve. }
    { rewrite !Int64.unsigned_repr in H4 by rep_lia. assert (i = outlen) by lia. subst i.
      forward. entailer!.
      rewrite sublist_same by (rewrite ?hb2s_ref_out_len; lia). rewrite Z.sub_diag, app_nil_r.
      unfold hfin. rewrite <- hb2s_ref_hfin_out. cancel. }
  }
  { Intros i. forward. Exists (i + 1). entailer!. }
Qed.
