(* body proof of __chacha20poly1305_decrypt (size_t lengths), against aead_spec3.aead_G3. *)
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
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.aead.aead_out3.
Require WgNoise.proof.aead.aead_long3_model.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* model facts                                                             *)
(* ---------------------------------------------------------------------- *)

Lemma dc3_Zlength_qround x a b c d : Zlength (chacha_qround x a b c d) = Zlength x.
Proof. unfold chacha_qround. rewrite !Zlength_upd_Znth. reflexivity. Qed.

Lemma dc3_Zlength_dround x : Zlength (chacha_dround x) = Zlength x.
Proof. unfold chacha_dround. rewrite !dc3_Zlength_qround. reflexivity. Qed.

(* (never let the kernel compare chacha_rounds (S n) x with chacha_rounds n (chacha_dround x)) *)
Lemma dc3_Zlength_rounds n x : Zlength (chacha_rounds n x) = Zlength x.
Proof.
  revert x; induction n; intros x; [reflexivity |].
  change (Zlength ((fix rounds (n : nat) (x : list int) {struct n} : list int :=
                      match n with O => x | S k => rounds k (chacha_dround x) end) n (chacha_dround x))
          = Zlength x).
  transitivity (Zlength (chacha_dround x)).
  - exact (IHn (chacha_dround x)).
  - apply dc3_Zlength_dround.
Qed.

Lemma dc3_Zlength_words_bytes ws : Zlength (words_bytes ws) = 4 * Zlength ws.
Proof.
  unfold words_bytes. induction ws; cbn [map concat]; auto.
  rewrite Zlength_app, IHws, Zlength_cons. unfold le32_bytes. rewrite !Zlength_cons, Zlength_nil. lia.
Qed.

Lemma dc3_Zlength_add_words a b : Zlength a = Zlength b -> Zlength (add_words a b) = Zlength a.
Proof.
  intros H. unfold add_words. rewrite Zlength_map. rewrite !Zlength_correct in *.
  rewrite combine_length. lia.
Qed.

Lemma dc3_Zlength_block_bytes n st : Zlength st = 16 -> Zlength (chacha_block_bytes n st) = 64.
Proof.
  intros H. unfold chacha_block_bytes, chacha_block_words.
  rewrite dc3_Zlength_words_bytes, dc3_Zlength_add_words; rewrite ?dc3_Zlength_rounds; lia.
Qed.

Lemma dc3_Zlength_advance st k : Zlength (chacha_advance st k) = Zlength st.
Proof. unfold chacha_advance. apply Zlength_upd_Znth. Qed.

Lemma dc3_xor_zeros n b : Zlength b = n -> xor_bytes (Zrepeat Byte.zero n) b = b.
Proof.
  intros <-. induction b; auto.
  rewrite Zlength_cons. unfold Zrepeat. rewrite Z2Nat.inj_succ by (apply Zlength_nonneg).
  simpl. unfold xor_bytes in *. simpl. f_equal.
  - apply Byte.xor_zero_l.
  - unfold Zrepeat in IHb. exact IHb.
Qed.

Lemma dc3_otk_len st : Zlength st = 16 -> Zlength (aead_otk st) = 32.
Proof.
  intros H. unfold aead_otk. rewrite Zlength_sublist; rewrite ?dc3_Zlength_block_bytes; auto; lia.
Qed.

Lemma dc3_xor_app a1 a2 b1 b2 :
  Zlength a1 = Zlength b1 -> xor_bytes (a1 ++ a2) (b1 ++ b2) = xor_bytes a1 b1 ++ xor_bytes a2 b2.
Proof.
  revert b1; induction a1; intros b1 H; destruct b1; simpl; auto;
    rewrite ?Zlength_cons, ?Zlength_nil in H.
  - pose proof (Zlength_nonneg b1); lia.
  - pose proof (Zlength_nonneg a1); lia.
  - unfold xor_bytes in *; simpl. f_equal. apply IHa1. lia.
Qed.

Lemma dc3_xor_trunc a b : Zlength a <= Zlength b -> xor_bytes a b = xor_bytes a (sublist 0 (Zlength a) b).
Proof.
  intros H. pose proof (Zlength_nonneg a).
  assert (Hb: b = sublist 0 (Zlength a) b ++ sublist (Zlength a) (Zlength b) b)
    by (rewrite sublist_rejoin, sublist_same; auto; lia).
  rewrite Hb at 1. rewrite <- (app_nil_r a) at 1. rewrite dc3_xor_app.
  - change (xor_bytes [] (sublist (Zlength a) (Zlength b) b)) with (@nil byte). apply app_nil_r.
  - rewrite Zlength_sublist; lia.
Qed.

Lemma dc3_otk st : Zlength st = 16 -> chacha_xor 10 st (Zrepeat Byte.zero 32) = aead_otk st.
Proof.
  intros H. unfold chacha_xor. change (Z.to_nat (chacha_nblocks (Zlength (Zrepeat Byte.zero 32)))) with 1%nat.
  cbn [chacha_stream]. rewrite app_nil_r.
  pose proof (dc3_Zlength_block_bytes 10 st H) as Hb.
  rewrite dc3_xor_trunc by (rewrite Zlength_Zrepeat, Hb; lia).
  rewrite Zlength_Zrepeat by lia. unfold aead_otk. apply (dc3_xor_zeros 32). rewrite Zlength_sublist; lia.
Qed.

Lemma dc3_and15 n : 0 <= n <= Int64.max_unsigned -> Int64.and (Int64.repr n) (Int64.repr 15) = Int64.repr (n mod 16).
Proof.
  intros H. unfold Int64.and. rewrite !Int64.unsigned_repr by rep_lia.
  change 15 with (Z.ones 4). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma dc3_pad x : Zlength x mod 16 <> 0 -> Zrepeat Byte.zero (16 - Zlength x mod 16) = pad16 x.
Proof.
  intros H. unfold pad16. f_equal. pose proof (Z.mod_pos_bound (Zlength x) 16 ltac:(lia)). rewrite (Z.mod_small (16 - Zlength x mod 16) 16); lia.
Qed.

Lemma dc3_pad0 x : Zlength x mod 16 = 0 -> pad16 x = [].
Proof. intros H. unfold pad16. rewrite H. reflexivity. Qed.

Lemma dc3_mac a ct :
  ((((a ++ pad16 a) ++ ct) ++ pad16 ct) ++ (le64_bytes (Zlength a) ++ le64_bytes (Zlength ct))) = aead_mac_data a ct.
Proof. unfold aead_mac_data. rewrite !app_assoc. reflexivity. Qed.

Lemma dc3_Zlength_le64 z : Zlength (le64_bytes z) = 8.
Proof. reflexivity. Qed.

Lemma dc3_memneq_false x y : memneq_bool x y = false -> x = y.
Proof. unfold memneq_bool. destruct (list_eq_dec Byte.eq_dec x y); congruence. Qed.

Lemma dc3_memneq_true x y : memneq_bool x y = true -> x <> y.
Proof. unfold memneq_bool. destruct (list_eq_dec Byte.eq_dec x y); congruence. Qed.

(* ---------------------------------------------------------------------- *)
(* byte arrays                                                             *)
(* ---------------------------------------------------------------------- *)

Lemma dc3_prim_bytes_cs {cs1 cs2: compspecs} sh bs p : @prim_bytes cs1 sh bs p = @prim_bytes cs2 sh bs p.
Proof. unfold prim_bytes. if_tac; auto. apply aead_data_at_tuchar_cs. Qed.

Lemma dc3_split2 {cs: compspecs} sh n i (v: list val) p :
  0 <= i <= n -> Zlength v = n -> field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) v p =
  (data_at sh (tarray tuchar i) (sublist 0 i v) p *
   data_at sh (tarray tuchar (n - i)) (sublist i n v) (offset_val i p))%logic.
Proof.
  intros. unfold tarray. rewrite (split2_data_at_Tarray_tuchar sh n i) by lia.
  fold (tarray tuchar n). rewrite arr_field_address0 by (auto; lia).
  change (sizeof tuchar) with 1. rewrite Z.mul_1_l. reflexivity.
Qed.

Lemma dc3_resize {cs: compspecs} sh n (l: list val) p :
  Zlength l = n -> data_at sh (tarray tuchar n) l p = data_at sh (tarray tuchar (Zlength l)) l p.
Proof. intros <-. reflexivity. Qed.

(* an equation that entailer! does not substitute *)
Definition dc3_is {A} (x y: A) : Prop := x = y.

Lemma dc3_blk (otk: list byte) x y : Zlength otk = 32 ->
  sublist 0 8 (map Vubyte (le64_bytes x ++ sublist 8 32 otk)) ++ map Vubyte (le64_bytes y) ++
  sublist (8 + 8) (Zlength (map Vubyte (le64_bytes x ++ sublist 8 32 otk))) (map Vubyte (le64_bytes x ++ sublist 8 32 otk)) =
  map Vubyte (le64_bytes x ++ le64_bytes y) ++ map Vubyte (sublist 16 32 otk).
Proof.
  intros H. pose proof (dc3_Zlength_le64 x). pose proof (dc3_Zlength_le64 y). list_solve.
Qed.

Lemma dc3_blk0 (otk: list byte) x : Zlength otk = 32 ->
  sublist 0 0 (map Vubyte otk) ++ map Vubyte (le64_bytes x) ++ sublist (0 + 8) (Zlength (map Vubyte otk)) (map Vubyte otk) =
  map Vubyte (le64_bytes x ++ sublist 8 32 otk).
Proof.
  intros H. pose proof (dc3_Zlength_le64 x). list_solve.
Qed.

Lemma dc3_split16 {cs: compspecs} sh (l1 l2: list val) p :
  Zlength l1 = 16 -> Zlength l2 = 16 -> field_compatible (tarray tuchar 32) [] p ->
  data_at sh (tarray tuchar 32) (l1 ++ l2) p =
  (data_at sh (tarray tuchar 16) l1 p * data_at sh (tarray tuchar 16) l2 (offset_val 16 p))%logic.
Proof.
  intros H1 H2 Hfc. rewrite (dc3_split2 sh 32 16) by (auto; try lia; rewrite Zlength_app; lia).
  rewrite sublist_app1, sublist_same by lia. rewrite sublist_app2 by lia.
  rewrite H1, sublist_same by lia. reflexivity.
Qed.

Lemma dc3_join16_ {cs: compspecs} sh p :
  field_compatible (tarray tuchar 32) [] p ->
  (data_at_ sh (tarray tuchar 16) p * data_at_ sh (tarray tuchar 16) (offset_val 16 p) |--
   data_at_ sh (tarray tuchar 32) p)%logic.
Proof.
  intros Hfc. rewrite !data_at__tarray. change (Zrepeat (default_val tuchar) 32) with
    (Zrepeat (default_val tuchar) 16 ++ Zrepeat (default_val tuchar) 16).
  rewrite dc3_split16 by auto. apply derives_refl.
Qed.

Lemma dc3_prim_bytes_eq {cs: compspecs} sh d p n :
  Zlength d = n -> 0 < n -> prim_bytes sh d p = data_at sh (tarray tuchar n) (map Vubyte d) p.
Proof. intros <- Hn. unfold prim_bytes. rewrite if_false by lia. reflexivity. Qed.

Lemma dc3_Zlength_tag k m : Zlength (poly1305_tag k m) = 16.
Proof. reflexivity. Qed.

Lemma dc3_dec st a c :
  16 <= Zlength c ->
  aead_dec_st st a c =
  if memneq_bool (poly1305_tag (aead_otk st) (aead_mac_data a (sublist 0 (Zlength c - 16) c)))
       (sublist (Zlength c - 16) (Zlength c) c)
  then None else Some (chacha_xor 10 (chacha_advance st 1) (sublist 0 (Zlength c - 16) c)).
Proof.
  intros H. unfold aead_dec_st, memneq_bool. destruct (Z_lt_dec (Zlength c) 16); [lia|].
  destruct (list_eq_dec _ _ _); reflexivity.
Qed.

Section Dec3.
#[local] Existing Instance Chacha20poly1305.CS.

Definition t_dc3_b : type := Tstruct WgNoise.chacha20poly1305.code.__540 noattr.

Lemma dc3_b_fc p : field_compatible t_dc3_b [] p <-> field_compatible (tarray tuchar 32) [] p.
Proof.
  unfold field_compatible; split; intros (? & ? & ? & ? & ?); repeat split; auto.
  all: destruct p; try contradiction; unfold align_compatible in *.
  - apply align_compatible_rec_Tarray. intros. econstructor; [reflexivity|]. simpl. apply Z.divide_1_l.
  - eapply align_compatible_rec_Tstruct. reflexivity. reflexivity.
    intros i0 t z Ht Hz. simpl in Ht. destruct (ident_eq i0 code._block0); [|discriminate].
    inv Ht. vm_compute in Hz. inv Hz. rewrite Z.add_0_r. exact H2.
Qed.

Lemma dc3_b_eq sh p : data_at_ sh (Tstruct WgNoise.chacha20poly1305.code.__540 noattr) p = data_at_ sh (tarray tuchar 32) p.
Proof.
  rewrite !data_at__memory_block. f_equal. f_equal. apply prop_ext, dc3_b_fc.
Qed.

Lemma dc3_ctx_cs sh : @data_at_ Chacha20poly1305.CS sh t_p1305_ctx = @data_at_ Poly1305.CS sh t_p1305_ctx.
Proof. apply data_at__change_composite. reflexivity. Qed.

(* the zero page: its first n bytes as an input buffer *)
Lemma dc3_zp_split gv n :
  0 < n < 64 -> field_compatible (tarray tuchar 64) [] (gv _quickproof_zero_page) ->
  zero_page gv =
  (prim_bytes Ers (Zrepeat Byte.zero n) (gv _quickproof_zero_page) *
   data_at Ers (tarray tuchar (64 - n)) (Zrepeat (Vubyte Byte.zero) (64 - n)) (offset_val n (gv _quickproof_zero_page)))%logic.
Proof.
  intros Hn Hfc. unfold zero_page, prim_bytes. rewrite Zlength_Zrepeat by lia.
  rewrite if_false by lia.
  rewrite (dc3_split2 Ers 64 n) by (rewrite ?Zlength_Zrepeat; auto; lia).
  rewrite !sublist_Zrepeat by lia. rewrite map_Zrepeat. f_equal; f_equal; f_equal; lia.
Qed.

(* the ciphertext and its tag *)
Lemma dc3_c_split sh c p :
  16 <= Zlength c -> field_compatible (tarray tuchar (Zlength c)) [] p ->
  prim_bytes sh c p =
  (prim_bytes sh (sublist 0 (Zlength c - 16) c) p *
   data_at sh (tarray tuchar 16) (map Vubyte (sublist (Zlength c - 16) (Zlength c) c))
     (offset_val (Zlength c - 16) p))%logic.
Proof.
  intros Hc Hfc. unfold prim_bytes. rewrite if_false by lia. rewrite Zlength_sublist by lia.
  rewrite (dc3_split2 sh (Zlength c) (Zlength c - 16)) by (rewrite ?Zlength_map; auto; lia).
  rewrite !sublist_map. replace (Zlength c - (Zlength c - 16)) with 16 by lia.
  if_tac.
  - replace (Zlength c - 16) with 0 by lia. rewrite sublist_nil.
    rewrite data_at_zero_array_eq; [rewrite emp_sepcon; reflexivity | reflexivity | apply Hfc | reflexivity].
  - rewrite Z.sub_0_r. reflexivity.
Qed.

Lemma dc3_c_join sh c ct tag p :
  ct = sublist 0 (Zlength c - 16) c -> tag = sublist (Zlength c - 16) (Zlength c) c ->
  16 <= Zlength c -> field_compatible (tarray tuchar (Zlength c)) [] p ->
  (prim_bytes sh ct p * data_at sh (tarray tuchar 16) (map Vubyte tag) (offset_val (Zlength ct) p))%logic =
  prim_bytes sh c p.
Proof.
  intros -> -> Hc Hfc. rewrite (dc3_c_split sh c p Hc Hfc). rewrite Zlength_sublist by lia.
  rewrite Z.sub_0_r. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* the body in three segments (one proof term for the whole body overflows *)
(* the kernel's stack at Qed): prefix (main theorem), B, C                  *)
(* ---------------------------------------------------------------------- *)

Definition dc3_Delta : tycontext :=
  func_tycontext WgNoise.chacha20poly1305.code.f___chacha20poly1305_decrypt (QPvarspecs Chacha20poly1305.qp)
    (aead_imports3 Chacha20poly1305.CS ++ aead_G3) nil.

Definition dc3_body : statement :=
  Eval cbv delta [WgNoise.chacha20poly1305.code.f___chacha20poly1305_decrypt fn_body] beta iota in
    fn_body WgNoise.chacha20poly1305.code.f___chacha20poly1305_decrypt.

Fixpoint dc3_drop (n: nat) (s: statement) : statement :=
  match n with O => s | S k => match s with Ssequence _ r => dc3_drop k r | _ => Sskip end end.

(* from poly1305_init; from the first put_unaligned_le64 *)
Definition dc3_stB : statement := Eval cbv [dc3_drop dc3_body] in dc3_drop 3 dc3_body.
Definition dc3_stC : statement := Eval cbv [dc3_drop dc3_body] in dc3_drop 9 dc3_body.

Definition dc3_post (dsh: share) (dst: val) (old: list val) (ssh: share) (src: val) (c: list byte)
  (ash: share) (ad: val) (a: list byte) (csh: share) (state: val) (st: list int) (gv: globals) : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tbool
       (PROP ()
        RETURN (Val.of_bool match aead_dec_st st a c with Some _ => true | None => false end)
        SEP (data_at dsh (tarray tuchar (Zlength old))
               match aead_dec_st st a c with Some pt => map Vubyte pt | None => old end dst;
             prim_bytes ssh c src; prim_bytes ash a ad; data_at_ csh t_chacha_state state; zero_page gv)))
    (stackframe_of WgNoise.chacha20poly1305.code.f___chacha20poly1305_decrypt).

Definition dc3_locals (dst src ad state vp vb: val) (c a: list byte) (gv: globals) : list localdef :=
  [temp WgNoise.chacha20poly1305.code._pad0 (gv _quickproof_zero_page);
   lvar WgNoise.chacha20poly1305.code._b (Tstruct WgNoise.chacha20poly1305.code.__540 noattr) vb;
   lvar WgNoise.chacha20poly1305.code._poly1305_state__1
     (Tstruct WgNoise.chacha20poly1305.code._poly1305_desc_ctx noattr) vp;
   gvars gv; temp WgNoise.chacha20poly1305.code._dst dst; temp WgNoise.chacha20poly1305.code._src src;
   temp WgNoise.chacha20poly1305.code._src_len (Vlong (Int64.repr (Zlength c)));
   temp WgNoise.chacha20poly1305.code._ad ad;
   temp WgNoise.chacha20poly1305.code._ad_len (Vlong (Int64.repr (Zlength a)));
   temp WgNoise.chacha20poly1305.code._chacha_state__1 state].

Definition dc3_preB (dsh: share) (dst: val) (old: list val) (ssh: share) (src: val) (c: list byte)
  (ash: share) (ad: val) (a: list byte) (csh: share) (state: val) (st: list int) (gv: globals) (vp vb: val)
  : environ -> mpred :=
  PROPx [] (LOCALx (dc3_locals dst src ad state vp vb c a gv)
  (SEPx [zero_page gv; data_at csh t_chacha_state (map Vint (chacha_advance st 1)) state;
         data_at Tsh (tarray tuchar 32) (map Vubyte (aead_otk st)) vb;
         data_at_ Tsh (Tstruct WgNoise.chacha20poly1305.code._poly1305_desc_ctx noattr) vp;
         data_at dsh (tarray tuchar (Zlength old)) old dst; prim_bytes ssh c src; prim_bytes ash a ad])).

Definition dc3_preC (dsh: share) (dst: val) (old: list val) (ssh: share) (src: val) (c: list byte)
  (ash: share) (ad: val) (a: list byte) (csh: share) (state: val) (st: list int) (gv: globals) (vp vb: val)
  (otk ct tag: list byte) : environ -> mpred :=
  PROPx [] (LOCALx (temp WgNoise.chacha20poly1305.code._dst_len (Vlong (Int64.repr (Zlength ct))) ::
                    dc3_locals dst src ad state vp vb c a gv)
  (SEPx [p1305_state Tsh otk (((a ++ pad16 a) ++ ct) ++ pad16 ct) vp; prim_bytes ssh ct src;
         data_at Tsh (tarray tuchar 32) (map Vubyte otk) vb; zero_page gv;
         data_at csh t_chacha_state (map Vint (chacha_advance st 1)) state;
         data_at dsh (tarray tuchar (Zlength old)) old dst;
         data_at ssh (tarray tuchar 16) (map Vubyte tag) (offset_val (Zlength ct) src);
         prim_bytes ash a ad])).

Definition dc3_stB2 : statement := Eval cbv [dc3_drop dc3_body] in dc3_drop 4 dc3_body.

Definition dc3_preB2 (dsh: share) (dst: val) (old: list val) (ssh: share) (src: val) (c: list byte)
  (ash: share) (ad: val) (a: list byte) (csh: share) (state: val) (st: list int) (gv: globals) (vp vb: val)
  (otk: list byte) : environ -> mpred :=
  PROPx [] (LOCALx (dc3_locals dst src ad state vp vb c a gv)
  (SEPx [p1305_state Tsh otk [] vp; data_at Tsh (tarray tuchar 32) (map Vubyte otk) vb; zero_page gv;
         data_at csh t_chacha_state (map Vint (chacha_advance st 1)) state;
         data_at dsh (tarray tuchar (Zlength old)) old dst; prim_bytes ssh c src; prim_bytes ash a ad])).

(* poly1305_init through a subsumed specification without PROP preconditions: the direct forward_call's
   proof of them (prove_PROP_preconditions, here with the shares Tsh) overflows the kernel's stack at Qed *)
Definition dc3_ctx_ (sh: share) (p: val) : mpred := @data_at_ Chacha20poly1305.CS sh t_p1305_ctx p.
Definition dc3_key (sh: share) (k: list byte) (p: val) : mpred :=
  @data_at Chacha20poly1305.CS sh (tarray tuchar 32) (map Vubyte k) p.
Definition dc3_keyp (sh ksh: share) (k: list byte) (p: val) : mpred :=
  (!! (writable_share sh /\ readable_share ksh /\ Zlength k = 32) && dc3_key ksh k p)%logic.

Lemma dc3_Tsh_w : writable_share Tsh.
Proof. auto with share. Qed.

Lemma dc3_Tsh_r : readable_share Tsh.
Proof. auto with share. Qed.

Lemma dc3_keyp_intro sh ksh k p :
  writable_share sh -> readable_share ksh -> Zlength k = 32 -> dc3_key ksh k p |-- dc3_keyp sh ksh k p.
Proof. intros. unfold dc3_keyp. apply andp_right; auto. apply prop_right; auto. Qed.

Definition dc3_init_spec :=
  DECLARE _poly1305_init
  WITH sh: share, desc: val, ksh: share, kp: val, key: list byte
  PRE [ tptr t_p1305_ctx, tptr tuchar ]
    PROP ()
    PARAMS (desc; kp)
    SEP (dc3_ctx_ sh desc; dc3_keyp sh ksh key kp)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (p1305_state sh key [] desc; dc3_key ksh key kp).

Lemma dc3_init_sub : funspec_sub (snd poly1305_init_spec) (snd dc3_init_spec).
Proof.
  do_funspec_sub.
  destruct w as [[[[sh desc] ksh] kp] key]. Exists (sh, desc, ksh, kp, key) emp. simpl.
  unfold dc3_ctx_, dc3_keyp, dc3_key. rewrite (dc3_ctx_cs sh).
  rewrite (@aead_data_at_tuchar_cs Chacha20poly1305.CS Poly1305.CS ksh 32). Intros. entailer!.
Qed.

Section Dc3Seg.
Context {Espec: OracleKind}.

Lemma dc3_C_ok dsh dst old ssh src c ash ad a csh state st gv v_poly1305_state__1 v_b otk ct tag :
  writable_share dsh -> readable_share ssh -> readable_share ash -> writable_share csh ->
  Zlength c <= Int64.max_unsigned -> Zlength a <= Int64.max_unsigned -> Zlength st = 16 ->
  Zlength old = Z.max 0 (Zlength c - 16) -> Zlength c >= 16 ->
  field_compatible (tarray tuchar (Zlength c)) [] src ->
  Zlength otk = 32 -> dc3_is otk (aead_otk st) -> Zlength ct = Zlength c - 16 ->
  dc3_is ct (sublist 0 (Zlength c - 16) c) -> dc3_is tag (sublist (Zlength c - 16) (Zlength c) c) ->
  semax dc3_Delta (dc3_preC dsh dst old ssh src c ash ad a csh state st gv v_poly1305_state__1 v_b otk ct tag) dc3_stC
    (dc3_post dsh dst old ssh src c ash ad a csh state st gv).
Proof.
  intros SH SH0 SH1 SH2 H H0 H1 H2 H3 Hsrc Hotk Hotk_def Hct Hct_def Htag_def.
  unfold dc3_preC, dc3_locals, dc3_stC, dc3_post.
  unfold dc3_Delta. simplify_func_tycontext. abbreviate_semax.
  change (Tstruct WgNoise.chacha20poly1305.code._poly1305_desc_ctx noattr) with t_p1305_ctx.
  assert_PROP (field_compatible (tarray tuchar 32) [] v_b) as Hb by entailer!.
  rewrite (dc3_resize Tsh 32 (map Vubyte otk) v_b) by (rewrite Zlength_map; auto).
  forward_call (Zlength a, Tsh, v_b, 0, map Vubyte otk).
  { rewrite Zlength_map; lia. }
  rewrite dc3_blk0 by auto.
  replace (Zlength (map Vubyte otk)) with 32 by (rewrite Zlength_map; auto).
  rewrite (dc3_resize Tsh 32 (map Vubyte (le64_bytes (Zlength a) ++ sublist 8 32 otk)) v_b)
    by (rewrite Zlength_map, Zlength_app, dc3_Zlength_le64, Zlength_sublist; lia).
  forward_call (Zlength ct, Tsh, v_b, 8, map Vubyte (le64_bytes (Zlength a) ++ sublist 8 32 otk)).
  { rewrite Zlength_map, Zlength_app, dc3_Zlength_le64, Zlength_sublist; lia. }
  rewrite dc3_blk by auto.
  replace (Zlength (map Vubyte (le64_bytes (Zlength a) ++ sublist 8 32 otk))) with 32
    by (rewrite Zlength_map, Zlength_app, dc3_Zlength_le64, Zlength_sublist; lia).
  rewrite dc3_split16 by (auto; rewrite ?Zlength_map, ?Zlength_app, ?dc3_Zlength_le64, ?Zlength_sublist; lia).
  flatten_sepcon_in_SEP.
  rewrite <- (dc3_prim_bytes_eq Tsh (le64_bytes (Zlength a) ++ le64_bytes (Zlength ct)) v_b 16)
    by (try rewrite Zlength_app, !dc3_Zlength_le64; lia).
  rewrite (@dc3_prim_bytes_cs Chacha20poly1305.CS Poly1305.CS Tsh (le64_bytes (Zlength a) ++ le64_bytes (Zlength ct))).
  forward_call (Tsh, v_poly1305_state__1, otk, (((a ++ pad16 a) ++ ct) ++ pad16 ct), Tsh, v_b,
                le64_bytes (Zlength a) ++ le64_bytes (Zlength ct)).
  { rewrite Zlength_app, !dc3_Zlength_le64; rep_lia. }
  rewrite dc3_mac.
  rewrite (@dc3_prim_bytes_cs Poly1305.CS Chacha20poly1305.CS).
  rewrite (dc3_prim_bytes_eq Tsh _ v_b 16) by (try rewrite Zlength_app, !dc3_Zlength_le64; lia).
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 16) (map Vubyte (le64_bytes (Zlength a) ++ le64_bytes (Zlength ct))) v_b).
  forward_call (Tsh, v_poly1305_state__1, otk, aead_mac_data a ct, Tsh, v_b).
  sep_apply (@data_at_data_at_ Poly1305.CS Tsh t_p1305_ctx p1305_ctx_zero v_poly1305_state__1).
  rewrite <- (dc3_ctx_cs Tsh).
  remember (poly1305_tag otk (aead_mac_data a ct)) as tagc eqn:Etagc.
  assert (Htagc: Zlength tagc = 16) by (subst; apply dc3_Zlength_tag).
  assert (Htagc_def: dc3_is tagc (poly1305_tag otk (aead_mac_data a ct))) by exact Etagc. clear Etagc.
  assert (Htag: Zlength tag = 16) by (rewrite Htag_def, Zlength_sublist; lia).
  forward_call (Tsh, ssh, v_b, offset_val (Zlength ct) src, 16, tagc, tag).
  assert (Hold: Zlength old = Zlength ct) by lia.
  forward_if (PROP () LOCAL (temp code._ret (Vint (if memneq_bool tagc tag then Int.one else Int.zero));
   temp code._dst_len (Vlong (Int64.repr (Zlength ct)));
   temp code._pad0 (gv chacha20poly1305.code._quickproof_zero_page);
   lvar chacha20poly1305.code._b (Tstruct code.__540 noattr) v_b;
   lvar code._poly1305_state__1 t_p1305_ctx v_poly1305_state__1;
   gvars gv; temp chacha20poly1305.code._dst dst;
   temp chacha20poly1305.code._src src;
   temp code._src_len (Vlong (Int64.repr (Zlength c)));
   temp code._ad ad; temp code._ad_len (Vlong (Int64.repr (Zlength a)));
   temp code._chacha_state__1 state)
   SEP (data_at Tsh (tarray tuchar 16) (map Vubyte tagc) v_b;
   data_at ssh (tarray tuchar 16) (map Vubyte tag) (offset_val (Zlength ct) src);
   data_at_ Tsh t_p1305_ctx v_poly1305_state__1;
   data_at Tsh (tarray tuchar 16) (map Vubyte (sublist 16 32 otk)) (offset_val 16 v_b);
   prim_bytes ssh ct src; zero_page gv;
   data_at_ csh t_chacha_state state;
   data_at dsh (tarray tuchar (Zlength old))
     (if memneq_bool tagc tag then old else map Vubyte (chacha_xor 10 (chacha_advance st 1) ct)) dst;
   prim_bytes ash a ad)).
  { destruct (memneq_bool tagc tag) eqn:Hmn; [discriminate|].
    assert_PROP (field_compatible (tarray tuchar (Zlength old)) [] dst) as Hdst by entailer!.
    sep_apply (data_at_data_at_ dsh (tarray tuchar (Zlength old)) old dst). rewrite Hold.
    rewrite Hold in Hdst.
    sep_apply (@out3_intro_ Chacha20poly1305.CS dsh (Zlength ct) dst (Zlength_nonneg ct)).
    forward_call (csh, state, chacha_advance st 1, dsh, dst, ssh, src, ct).
    { rewrite dc3_Zlength_advance; lia. }
    sep_apply (@out3_elim Chacha20poly1305.CS dsh (map Vubyte (chacha_xor 10 (chacha_advance st 1) ct)) (Zlength ct) dst
                 ltac:(rewrite Zlength_map; apply aead_long3_model.lg3_Zlength_chacha_xor; rewrite dc3_Zlength_advance; lia) Hdst).
    entailer!. rewrite Hold. apply derives_refl. }
  { destruct (memneq_bool tagc tag) eqn:Hmn; [| exfalso; apply H4; reflexivity].
    forward. entailer!. }
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 16) (map Vubyte tagc) v_b).
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 16) (map Vubyte (sublist 16 32 otk)) (offset_val 16 v_b)).
  sep_apply (dc3_join16_ Tsh v_b Hb).
  forward_call (Tsh, v_b, 32).
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (Zrepeat (Vubyte Byte.zero) 32) v_b).
  rewrite <- (dc3_b_eq Tsh v_b).
  gather_SEP (prim_bytes ssh ct src) (data_at ssh (tarray tuchar 16) (map Vubyte tag) _).
  rewrite (dc3_c_join ssh c ct tag src) by (auto; lia).
  forward.
  rewrite (dc3_dec st a c) by lia.
  unfold dc3_is in *.
  rewrite <- Hct_def, <- Htag_def, <- Hotk_def, <- Htagc_def.
  destruct (memneq_bool tagc tag); entailer!.
Qed.

Lemma dc3_B2_ok dsh dst old ssh src c ash ad a csh state st gv v_poly1305_state__1 v_b otk :
  writable_share dsh -> readable_share ssh -> readable_share ash -> writable_share csh ->
  Zlength c <= Int64.max_unsigned -> Zlength a <= Int64.max_unsigned -> Zlength st = 16 ->
  Zlength old = Z.max 0 (Zlength c - 16) -> Zlength c >= 16 ->
  Zlength otk = 32 -> dc3_is otk (aead_otk st) ->
  semax dc3_Delta (dc3_preB2 dsh dst old ssh src c ash ad a csh state st gv v_poly1305_state__1 v_b otk) dc3_stB2
    (dc3_post dsh dst old ssh src c ash ad a csh state st gv).
Proof.
  intros SH SH0 SH1 SH2 H H0 H1 H2 H3 Hotk Hotk_def.
  assert (HC: forall otk' ct tag, field_compatible (tarray tuchar (Zlength c)) [] src ->
    Zlength otk' = 32 -> dc3_is otk' (aead_otk st) -> Zlength ct = Zlength c - 16 ->
    dc3_is ct (sublist 0 (Zlength c - 16) c) -> dc3_is tag (sublist (Zlength c - 16) (Zlength c) c) ->
    semax dc3_Delta (dc3_preC dsh dst old ssh src c ash ad a csh state st gv v_poly1305_state__1 v_b otk' ct tag)
      dc3_stC (dc3_post dsh dst old ssh src c ash ad a csh state st gv))
    by (intros; apply dc3_C_ok; auto).
  unfold dc3_preB2, dc3_locals, dc3_stB2, dc3_post.
  unfold dc3_Delta in *. simplify_func_tycontext. abbreviate_semax.
  change (func_tycontext WgNoise.chacha20poly1305.code.f___chacha20poly1305_decrypt (QPvarspecs Chacha20poly1305.qp)
    (aead_imports3 Chacha20poly1305.CS ++ aead_G3) nil) with Delta in HC.
  change (dc3_post dsh dst old ssh src c ash ad a csh state st gv) with POSTCONDITION in HC.
  assert_PROP (field_compatible (tarray tuchar 64) [] (gv _quickproof_zero_page)) as Hzp by (unfold zero_page; entailer!).
  assert_PROP (field_compatible (tarray tuchar (Zlength c)) [] src) as Hsrc
    by (unfold prim_bytes; rewrite if_false by lia; entailer!).
  assert_PROP (field_compatible (tarray tuchar 32) [] v_b) as Hb by entailer!.
  change (Tstruct code._poly1305_desc_ctx noattr) with t_p1305_ctx.
  rewrite (@dc3_prim_bytes_cs Chacha20poly1305.CS Poly1305.CS ash a).
  forward_call (Tsh, v_poly1305_state__1, otk, @nil byte, ash, ad, a).
  rewrite (@dc3_prim_bytes_cs Poly1305.CS Chacha20poly1305.CS ash a).
  rewrite app_nil_l.
  forward_if (PROP () LOCAL (temp code._pad0 (gv chacha20poly1305.code._quickproof_zero_page);
   lvar chacha20poly1305.code._b (Tstruct code.__540 noattr) v_b;
   lvar code._poly1305_state__1 t_p1305_ctx v_poly1305_state__1;
   gvars gv; temp chacha20poly1305.code._dst dst;
   temp chacha20poly1305.code._src src;
   temp code._src_len (Vlong (Int64.repr (Zlength c)));
   temp code._ad ad; temp code._ad_len (Vlong (Int64.repr (Zlength a)));
   temp code._chacha_state__1 state)
   SEP (p1305_state Tsh otk (a ++ pad16 a) v_poly1305_state__1;
   data_at Tsh (tarray tuchar 32) (map Vubyte otk) v_b; zero_page gv;
   data_at csh t_chacha_state (map Vint (chacha_advance st 1)) state;
   data_at dsh (tarray tuchar (Zlength old)) old dst;
   prim_bytes ssh c src; prim_bytes ash a ad)).
  { rewrite dc3_and15 in H4 by rep_lia. clear H4'.
    assert (Hm: Zlength a mod 16 <> 0) by (intro Hx; rewrite Hx in H4; apply H4; reflexivity).
    pose proof (Z.mod_pos_bound (Zlength a) 16 ltac:(lia)).
    rewrite (dc3_zp_split gv (16 - Zlength a mod 16)) by (auto; lia).
    rewrite (@dc3_prim_bytes_cs Chacha20poly1305.CS Poly1305.CS Ers (Zrepeat Byte.zero (16 - Zlength a mod 16))).
    forward_call (Tsh, v_poly1305_state__1, otk, a, Ers, gv _quickproof_zero_page,
                  Zrepeat Byte.zero (16 - Zlength a mod 16)).
    { go_lower. apply prop_right. simpl. rewrite out3_pad_len64 by rep_lia.
      rewrite Zlength_Zrepeat by lia. reflexivity. }
    { cancel. }
    { rewrite Zlength_Zrepeat; rep_lia. }
    rewrite dc3_pad by auto.
    rewrite (@dc3_prim_bytes_cs Poly1305.CS Chacha20poly1305.CS).
    entailer!. rewrite <- dc3_pad by auto. rewrite (dc3_zp_split gv (16 - Zlength a mod 16)) by (auto; lia).
    cancel. }
  { rewrite dc3_and15 in H4 by rep_lia.
    assert (Hm: Zlength a mod 16 = 0).
    { pose proof (Z.mod_pos_bound (Zlength a) 16 ltac:(lia)). apply (f_equal Int64.unsigned) in H4.
      rewrite Int64.unsigned_repr in H4 by rep_lia. exact H4. }
    forward. rewrite dc3_pad0, app_nil_r by auto. entailer!. }
  forward.
  change (Int.signed (Int.repr 16)) with 16.
  assert (Hdl: Int64.sub (Int64.repr (Zlength c)) (Int64.repr 16) = Int64.repr (Zlength c - 16))
    by (unfold Int64.sub; rewrite !Int64.unsigned_repr by rep_lia; reflexivity).
  rewrite Hdl; clear Hdl.
  rewrite (dc3_c_split ssh c src) by (auto; lia). flatten_sepcon_in_SEP.
  remember (sublist 0 (Zlength c - 16) c) as ct eqn:Ect.
  remember (sublist (Zlength c - 16) (Zlength c) c) as tag eqn:Etag.
  assert (Hct: Zlength ct = Zlength c - 16) by (subst; rewrite Zlength_sublist; lia).
  assert (Hct_def: dc3_is ct (sublist 0 (Zlength c - 16) c)) by exact Ect. clear Ect.
  assert (Htag_def: dc3_is tag (sublist (Zlength c - 16) (Zlength c) c)) by exact Etag. clear Etag.
  replace (Zlength c - 16) with (Zlength ct) by lia.
  rewrite (@dc3_prim_bytes_cs Chacha20poly1305.CS Poly1305.CS ssh ct).
  forward_call (Tsh, v_poly1305_state__1, otk, a ++ pad16 a, ssh, src, ct).
  rewrite (@dc3_prim_bytes_cs Poly1305.CS Chacha20poly1305.CS ssh ct).
  forward_if (PROP () LOCAL (temp code._dst_len (Vlong (Int64.repr (Zlength ct)));
   temp code._pad0 (gv chacha20poly1305.code._quickproof_zero_page);
   lvar chacha20poly1305.code._b (Tstruct code.__540 noattr) v_b;
   lvar code._poly1305_state__1 t_p1305_ctx v_poly1305_state__1;
   gvars gv; temp chacha20poly1305.code._dst dst;
   temp chacha20poly1305.code._src src;
   temp code._src_len (Vlong (Int64.repr (Zlength c)));
   temp code._ad ad; temp code._ad_len (Vlong (Int64.repr (Zlength a)));
   temp code._chacha_state__1 state)
   SEP (p1305_state Tsh otk (((a ++ pad16 a) ++ ct) ++ pad16 ct) v_poly1305_state__1;
   prim_bytes ssh ct src;
   data_at Tsh (tarray tuchar 32) (map Vubyte otk) v_b; zero_page gv;
   data_at csh t_chacha_state (map Vint (chacha_advance st 1)) state;
   data_at dsh (tarray tuchar (Zlength old)) old dst;
   data_at ssh (tarray tuchar 16) (map Vubyte tag) (offset_val (Zlength ct) src);
   prim_bytes ash a ad)).
  { rewrite dc3_and15 in H4 by rep_lia. clear H4'.
    assert (Hm: Zlength ct mod 16 <> 0) by (intro Hx; rewrite Hx in H4; apply H4; reflexivity).
    pose proof (Z.mod_pos_bound (Zlength ct) 16 ltac:(lia)).
    rewrite (dc3_zp_split gv (16 - Zlength ct mod 16)) by (auto; lia).
    rewrite (@dc3_prim_bytes_cs Chacha20poly1305.CS Poly1305.CS Ers (Zrepeat Byte.zero (16 - Zlength ct mod 16))).
    forward_call (Tsh, v_poly1305_state__1, otk, (a ++ pad16 a) ++ ct, Ers, gv _quickproof_zero_page,
                  Zrepeat Byte.zero (16 - Zlength ct mod 16)).
    { go_lower. apply prop_right. simpl. rewrite out3_pad_len64 by rep_lia.
      rewrite Zlength_Zrepeat by lia. reflexivity. }
    { cancel. }
    { rewrite Zlength_Zrepeat; rep_lia. }
    rewrite dc3_pad by auto.
    rewrite (@dc3_prim_bytes_cs Poly1305.CS Chacha20poly1305.CS).
    entailer!. rewrite <- dc3_pad by auto. rewrite (dc3_zp_split gv (16 - Zlength ct mod 16)) by (auto; lia).
    cancel. }
  { rewrite dc3_and15 in H4 by rep_lia.
    assert (Hm: Zlength ct mod 16 = 0).
    { pose proof (Z.mod_pos_bound (Zlength ct) 16 ltac:(lia)). apply (f_equal Int64.unsigned) in H4.
      rewrite Int64.unsigned_repr in H4 by rep_lia. exact H4. }
    forward. rewrite (dc3_pad0 ct), app_nil_r by auto. entailer!. }
  unfold MORE_COMMANDS, abbreviate.
  eapply semax_pre; [ | apply (HC otk ct tag Hsrc Hotk Hotk_def Hct eq_refl eq_refl) ].
  unfold dc3_preC, dc3_locals. entailer!.
Qed.

Lemma dc3_B_ok dsh dst old ssh src c ash ad a csh state st gv v_poly1305_state__1 v_b :
  writable_share dsh -> readable_share ssh -> readable_share ash -> writable_share csh ->
  Zlength c <= Int64.max_unsigned -> Zlength a <= Int64.max_unsigned -> Zlength st = 16 ->
  Zlength old = Z.max 0 (Zlength c - 16) -> Zlength c >= 16 ->
  semax dc3_Delta (dc3_preB dsh dst old ssh src c ash ad a csh state st gv v_poly1305_state__1 v_b) dc3_stB
    (dc3_post dsh dst old ssh src c ash ad a csh state st gv).
Proof.
  intros SH SH0 SH1 SH2 H H0 H1 H2 H3.
  assert (HB2: forall otk, Zlength otk = 32 -> dc3_is otk (aead_otk st) ->
    semax dc3_Delta (dc3_preB2 dsh dst old ssh src c ash ad a csh state st gv v_poly1305_state__1 v_b otk)
      dc3_stB2 (dc3_post dsh dst old ssh src c ash ad a csh state st gv))
    by (intros; apply dc3_B2_ok; auto).
  unfold dc3_preB, dc3_locals, dc3_stB, dc3_post.
  unfold dc3_Delta in *. simplify_func_tycontext. abbreviate_semax.
  change (func_tycontext WgNoise.chacha20poly1305.code.f___chacha20poly1305_decrypt (QPvarspecs Chacha20poly1305.qp)
    (aead_imports3 Chacha20poly1305.CS ++ aead_G3) nil) with Delta in HB2.
  change (dc3_post dsh dst old ssh src c ash ad a csh state st gv) with POSTCONDITION in HB2.
  assert (Hotk: Zlength (aead_otk st) = 32) by (apply dc3_otk_len; auto).
  remember (aead_otk st) as otk eqn:E.
  assert (Hotk_def: dc3_is otk (aead_otk st)) by exact E. clear E.
  change (data_at_ Tsh (Tstruct code._poly1305_desc_ctx noattr) v_poly1305_state__1)
    with (dc3_ctx_ Tsh v_poly1305_state__1).
  change (data_at Tsh (tarray tuchar 32) (map Vubyte otk) v_b) with (dc3_key Tsh otk v_b).
  sep_apply (dc3_keyp_intro Tsh Tsh otk v_b dc3_Tsh_w dc3_Tsh_r Hotk).
  forward_call dc3_init_sub (Tsh, v_poly1305_state__1, Tsh, v_b, otk).
  unfold dc3_key.
  unfold MORE_COMMANDS, abbreviate.
  eapply semax_pre; [ | apply (HB2 otk Hotk eq_refl) ].
  unfold dc3_preB2, dc3_locals. entailer!.
Qed.

End Dc3Seg.

Theorem aead_decrypt_bodies3 :
  @semax_body (QPvarspecs Chacha20poly1305.qp) (aead_imports3 Chacha20poly1305.CS ++ aead_G3) Chacha20poly1305.CS
    WgNoise.chacha20poly1305.code.f___chacha20poly1305_decrypt __chacha20poly1305_decrypt_spec3.
Proof.
  start_function.
  assert (HB: Zlength c >= 16 ->
              semax Delta (dc3_preB dsh dst old ssh src c ash ad a csh state st gv v_poly1305_state__1 v_b)
                dc3_stB POSTCONDITION) by (intro; apply dc3_B_ok; auto).
  forward.
  forward_if.
  { forward. assert (Hn: aead_dec_st st a c = None).
    { unfold aead_dec_st. destruct (Z_lt_dec (Zlength c) 16); auto. rewrite !Int64.unsigned_repr in H3 by rep_lia. lia. }
    rewrite Hn. entailer!. }
  rewrite !Int64.unsigned_repr in H3 by rep_lia.
  assert_PROP (field_compatible (tarray tuchar 64) [] (gv _quickproof_zero_page)) as Hzp by (unfold zero_page; entailer!).
  assert_PROP (field_compatible (tarray tuchar (Zlength c)) [] src) as Hsrc
    by (unfold prim_bytes; rewrite if_false by lia; entailer!).
  rewrite (dc3_b_eq Tsh v_b).
  assert_PROP (field_compatible (tarray tuchar 32) [] v_b) as Hb by entailer!.
  rewrite (dc3_zp_split gv 32) by (auto; lia).
  sep_apply (@out3_intro_ Chacha20poly1305.CS Tsh 32 v_b ltac:(lia)).
  forward_call (csh, state, st, Tsh, v_b, Ers, gv _quickproof_zero_page, Zrepeat Byte.zero 32).
  all: try solve [cancel | rewrite ?Zlength_Zrepeat by lia; rep_lia].
  change (chacha_nblocks (Zlength (Zrepeat Byte.zero 32))) with 1.
  change (Zlength (Zrepeat Byte.zero 32)) with 32.
  rewrite (dc3_otk st H1).
  sep_apply (@out3_elim Chacha20poly1305.CS Tsh (map Vubyte (aead_otk st)) 32 v_b
               ltac:(rewrite Zlength_map; apply dc3_otk_len; auto) Hb).
  gather_SEP (prim_bytes Ers (Zrepeat Byte.zero 32) _) (data_at Ers (tarray tuchar (64 - 32)) _ _).
  rewrite <- (dc3_zp_split gv 32) by (auto; lia).
  unfold MORE_COMMANDS, abbreviate.
  eapply semax_pre; [ | exact (HB H3) ].
  unfold dc3_preB, dc3_locals. entailer!.
Qed.

End Dec3.
