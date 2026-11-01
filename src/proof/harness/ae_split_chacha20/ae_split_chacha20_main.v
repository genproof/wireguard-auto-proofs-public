(* main of law ae_split_chacha20 (harness/ae_split_chacha20.c), in W_ae_split_chacha20, against the
   specifications of the functions it calls (asc_main_ctx, ae_split_chacha20_spec.v).

   The law follows from the model (aead_model.v, aead_long3_model.v): the keystream continues across a cut at a
   whole number of blocks.  If |m1| is a multiple of 64, chacha_xor st (m1 ++ m2) = chacha_xor st m1 ++
   chacha_xor (chacha_advance st (chacha_nblocks |m1|)) m2 (lg3_chacha_xor_app), and the state after the two
   pieces is the state after the whole (lg3_advance_advance, lg3_nblocks_add).  So the loop keeps: done bytes
   processed, done a multiple of 64 or done = len, the state of `many` advanced by chacha_nblocks done blocks,
   pieces[0..done) = chacha_xor 10 st m[0..done). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.proof.assembly.asm_env.
Require Import WgNoise.proof.aead.aead_spec3.
Require Import WgNoise.proof.aead.aead_long3_model.
Require Import WgNoise.proof.harness.wg_laws.wl_spec.
Require Import WgNoise.proof.harness.ae_split_chacha20.ae_split_chacha20_world.
Require Import WgNoise.proof.harness.ae_split_chacha20.ae_split_chacha20_spec.
Require WgNoise.contracts.ae_split_chacha20.
Require Import WgNoise.harness.ae_split_chacha20.code.

#[local] Existing Instance W_ae_split_chacha20.
Local Open Scope Z_scope.

(* the specifications of chacha_init and chacha20_crypt are stated at Chacha20poly1305.CS: convert the state
   and byte arrays between it and the law's world around each call *)
#[local] Instance asc_CCE : change_composite_env Chacha20poly1305.CS W_ae_split_chacha20.
Proof. make_cs_preserve Chacha20poly1305.CS W_ae_split_chacha20. Defined.
#[local] Instance asc_CCE' : change_composite_env W_ae_split_chacha20 Chacha20poly1305.CS.
Proof. make_cs_preserve W_ae_split_chacha20 Chacha20poly1305.CS. Defined.

(* main's precondition: keep gvars, forget the globals (main never reads one) and the external state *)
Lemma asc_main_pre {Espec: OracleKind} Delta (prog: QP.program function) (gv: globals) R c Post:
  semax Delta (PROP () LOCAL (gvars gv) SEP (TT) * R)%logic c Post ->
  semax Delta (close_precondition nil (@main_pre unit prog tt gv) * R)%logic c Post.
Proof.
  intros H. eapply semax_pre; [|apply H]; clear H.
  unfold main_pre, PROPx, LOCALx, SEPx, local, lift1.
  intro rho. unfold close_precondition. simpl. unfold_lift. normalize.
  rewrite prop_true_andp; [apply sepcon_derives; auto; apply TT_right | split; auto; hnf; reflexivity].
Qed.

(* a buffer from malloc or any_bytes: NULL, or an object of n bytes *)
Definition asc_buf (p: val) (n: Z) (v: list val) : mpred :=
  if eq_dec p nullval then emp else (malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) v p)%logic.

Lemma asc_buf_valid p n v : asc_buf p n v |-- valid_pointer p.
Proof.
  unfold asc_buf. destruct (eq_dec p nullval).
  - subst. apply valid_pointer_null.
  - destruct (zlt 0 n).
    + apply sepcon_valid_pointer2. apply data_at_valid_ptr; [auto | simpl sizeof; lia].
    + apply sepcon_valid_pointer1. apply malloc_token_valid_pointer. simpl sizeof. lia.
Qed.

#[local] Hint Resolve asc_buf_valid : valid_pointer.

Lemma asc_buf_local p n v : asc_buf p n v |-- !! is_pointer_or_null p.
Proof.
  unfold asc_buf. destruct (eq_dec p nullval).
  - subst. apply prop_right. simpl. auto.
  - entailer!; destruct p; try contradiction; simpl; auto.
Qed.

#[local] Hint Resolve asc_buf_local : saturate_local.

Definition asc_nul (p: val) : bool := if eq_dec p nullval then true else false.

Lemma asc_test_eq p : is_pointer_or_null p ->
  force_val (sem_cast_i2bool (force_val (sem_cmp_pp Ceq p (Vlong (Int64.repr 0))))) =
  Vint (if asc_nul p then Int.one else Int.zero).
Proof.
  intros H. destruct p; simpl in H; try contradiction.
  - subst. reflexivity.
  - unfold asc_nul. rewrite if_false by discriminate. reflexivity.
Qed.

Lemma asc_if_true (b: bool) : (if b then Int.one else Int.repr 0) <> Int.zero -> b = true.
Proof. destruct b; intros H; [reflexivity | contradiction H; reflexivity]. Qed.

Lemma asc_if_false (b: bool) : (if b then Int.one else Int.repr 0) = Int.zero -> b = false.
Proof. destruct b; intros H; [discriminate H | reflexivity]. Qed.

(* the bytes nondet_bytes writes, as bytes *)
Lemma asc_bytes bz : Forall (fun b => 0 <= b <= Byte.max_unsigned) bz ->
  map (fun b => Vint (Int.repr b)) bz = map Vubyte (map Byte.repr bz).
Proof.
  induction 1; simpl; f_equal; auto.
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma asc_Zlength_init_st k iv : Zlength k = 8 -> Zlength (chacha_init_st k iv) = 16.
Proof. intros H. unfold chacha_init_st, chacha_consts. rewrite !Zlength_app, H. reflexivity. Qed.

(* chacha20_crypt's buffers (prim_out, prim_bytes) are nothing when empty: a byte array of n bytes is the
   buffer and, when n = 0, the empty array kept aside (asc_rest) *)
Definition asc_rest (sh: share) (n: Z) (p: val) : mpred :=
  if Z.eq_dec n 0 then data_at sh (tarray tuchar 0) [] p else emp.

Lemma asc_out_split sh (v: list val) p n : Zlength v = n ->
  data_at sh (tarray tuchar n) v p =
  (@prot_dec3.prim_out Chacha20poly1305.CS sh v p * asc_rest sh n p)%logic.
Proof.
  intros <-. unfold prot_dec3.prim_out, asc_rest. destruct (Z.eq_dec (Zlength v) 0) as [E|E].
  - rewrite emp_sepcon. apply Zlength_nil_inv in E. subst v. reflexivity.
  - rewrite sepcon_emp. apply equal_f, (@data_at_change_composite _ _ asc_CCE'); [apply JMeq_refl | reflexivity].
Qed.

Lemma asc_bytes_split sh (m: list byte) p n : Zlength m = n ->
  data_at sh (tarray tuchar n) (map Vubyte m) p =
  (@prim_api.prim_bytes Chacha20poly1305.CS sh m p * asc_rest sh n p)%logic.
Proof.
  intros <-. unfold prim_api.prim_bytes, asc_rest. destruct (Z.eq_dec (Zlength m) 0) as [E|E].
  - rewrite emp_sepcon. apply Zlength_nil_inv in E. subst m. reflexivity.
  - rewrite sepcon_emp.
    apply equal_f, (@data_at_change_composite _ _ asc_CCE'); [apply JMeq_refl | reflexivity].
Qed.

Lemma asc_out_join sh (v: list val) p n : Zlength v = n ->
  (@prot_dec3.prim_out Chacha20poly1305.CS sh v p * asc_rest sh n p)%logic |-- data_at sh (tarray tuchar n) v p.
Proof. intros H. rewrite (asc_out_split sh v p n H). auto. Qed.

Lemma asc_bytes_join sh (m: list byte) p n : Zlength m = n ->
  (@prim_api.prim_bytes Chacha20poly1305.CS sh m p * asc_rest sh n p)%logic |--
  data_at sh (tarray tuchar n) (map Vubyte m) p.
Proof. intros H. rewrite (asc_bytes_split sh m p n H). auto. Qed.

(* a ChaCha state (chacha_init's and chacha20_crypt's view) is main's local struct *)
Lemma asc_state_free sh (l: list int) p :
  @data_at Chacha20poly1305.CS sh t_chacha_state (map Vint l) p |-- data_at_ sh (Tstruct _chacha_state noattr) p.
Proof.
  sep_apply (@data_at_data_at_ Chacha20poly1305.CS sh t_chacha_state (map Vint l) p).
  rewrite (@data_at__change_composite _ _ asc_CCE sh t_chacha_state) by reflexivity.
  unfold t_chacha_state. apply derives_refl.
Qed.

(* one piece of the loop: if done is a multiple of 64, encrypting m[0..done+take) in one go is encrypting
   m[0..done) and then m[done..done+take) from the state advanced by the blocks of the first part, and the state
   after both is the state after the whole *)
Lemma asc_step st (m: list byte) done take :
  Zlength st = 16 -> 0 <= done -> 0 <= take -> done + take <= Zlength m -> done mod 64 = 0 ->
  chacha_xor 10 st (sublist 0 (done + take) m) =
    chacha_xor 10 st (sublist 0 done m) ++
    chacha_xor 10 (chacha_advance st (chacha_nblocks done)) (sublist done (done + take) m) /\
  chacha_advance (chacha_advance st (chacha_nblocks done)) (chacha_nblocks take) =
    chacha_advance st (chacha_nblocks (done + take)).
Proof.
  intros Hst Hd Ht Hle Hm. split.
  - rewrite (sublist_split 0 done (done + take)) by lia.
    rewrite lg3_chacha_xor_app; auto; rewrite Zlength_sublist by lia; [| rewrite Z.sub_0_r; auto].
    rewrite Z.sub_0_r. reflexivity.
  - rewrite lg3_advance_advance by auto. f_equal.
    pose proof (Z.div_mod done 64 ltac:(lia)) as E. rewrite Hm, Z.add_0_r in E.
    rewrite E, lg3_nblocks_add, lg3_nblocks_full; auto; apply Z.div_pos; lia.
Qed.

(* the pieces' buffer, cut at done and done + take *)
Lemma asc_pieces_split sh len done take (A: list byte) p :
  0 <= done -> 0 <= take -> done + take <= len -> Zlength A = done -> field_compatible (tarray tuchar len) [] p ->
  data_at sh (tarray tuchar len) (map Vubyte A ++ Zrepeat Vundef (len - done)) p =
  (data_at sh (tarray tuchar done) (map Vubyte A) p *
   data_at sh (tarray tuchar take) (Zrepeat Vundef take) (offset_val done p) *
   data_at sh (tarray tuchar (len - (done + take))) (Zrepeat Vundef (len - (done + take)))
     (offset_val (done + take) p))%logic.
Proof.
  intros. rewrite (lg3_split3 sh len done take) by (auto; list_solve).
  f_equal; [f_equal |]; f_equal; list_solve.
Qed.

Lemma asc_pieces_join sh len done take (A B: list byte) p :
  0 <= done -> 0 <= take -> done + take <= len -> Zlength A = done -> Zlength B = take ->
  field_compatible (tarray tuchar len) [] p ->
  (data_at sh (tarray tuchar done) (map Vubyte A) p *
   data_at sh (tarray tuchar take) (map Vubyte B) (offset_val done p) *
   data_at sh (tarray tuchar (len - (done + take))) (Zrepeat Vundef (len - (done + take)))
     (offset_val (done + take) p))%logic
  |-- data_at sh (tarray tuchar len) (map Vubyte (A ++ B) ++ Zrepeat Vundef (len - (done + take))) p.
Proof.
  intros. rewrite (lg3_split3 sh len done take) by (auto; list_solve).
  apply derives_refl'. f_equal; [f_equal |]; f_equal; list_solve.
Qed.

(* the message's buffer, cut at done and done + take *)
Lemma asc_msg_split sh len done take (m: list byte) p :
  0 <= done -> 0 <= take -> done + take <= len -> Zlength m = len -> field_compatible (tarray tuchar len) [] p ->
  data_at sh (tarray tuchar len) (map Vubyte m) p =
  (data_at sh (tarray tuchar done) (map Vubyte (sublist 0 done m)) p *
   data_at sh (tarray tuchar take) (map Vubyte (sublist done (done + take) m)) (offset_val done p) *
   data_at sh (tarray tuchar (len - (done + take))) (map Vubyte (sublist (done + take) len m))
     (offset_val (done + take) p))%logic.
Proof.
  intros. rewrite (lg3_split3 sh len done take) by (auto; list_solve).
  rewrite !sublist_map. reflexivity.
Qed.

Lemma body_main_asc : semax_body asc_V asc_main_ctx f_main asc_main_spec.
Proof.
  unfold asc_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  simpl fn_body; simpl fn_params; simpl fn_return.
  change (fun rho => ?A rho * ?B rho)%logic with (A * B)%logic.
  apply asc_main_pre.
  simpl app. simplify_func_tycontext.
  process_stackframe_of.
  repeat rewrite <- data_at__offset_zero.
  unfold asc_post.
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (TT))%assert
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  abbreviate_semax.
  sep_apply (create_mem_mgr gv).
  (* the key *)
  forward_for_simple_bound 8 (EX i: Z, EX ks: list int, PROP (Zlength ks = i)
    LOCAL (lvar _many (Tstruct _chacha_state noattr) v_many; lvar _one (Tstruct _chacha_state noattr) v_one;
           lvar _iv (tarray tuchar 16) v_iv; lvar _key (tarray tuint 8) v_key; gvars gv)
    SEP (data_at_ Tsh (Tstruct _chacha_state noattr) v_many; data_at_ Tsh (Tstruct _chacha_state noattr) v_one;
         data_at_ Tsh (tarray tuchar 16) v_iv;
         data_at Tsh (tarray tuint 8) (map Vint ks ++ Zrepeat Vundef (8 - i)) v_key;
         mem_mgr gv; TT))%assert.
  { Exists (@nil int). entailer!. }
  { forward_call tt. Intros w. forward. Exists (ks ++ [Int.repr w]). entailer!.
    - list_solve.
    - match goal with |- data_at _ _ ?a _ * _ |-- data_at _ _ ?b _ * _ => replace a with b by list_solve end.
      cancel. }
  Intros ks. rewrite Z.sub_diag, Zrepeat_0, app_nil_r.
  (* the block counter and nonce, the message, the two outputs *)
  forward_call (v_iv, 16, Tsh). Intros ivz.
  forward_call (Int64.max_signed). Intros len.
  forward_call (len, gv). Intros vret. destruct vret as [message mb]. simpl fst in *; simpl snd in *.
  forward_call (tarray tuchar len, gv). { simpl sizeof. rewrite Z.max_r by lia. rep_lia. } Intros whole.
  forward_call (tarray tuchar len, gv). { simpl sizeof. rewrite Z.max_r by lia. rep_lia. } Intros pieces.
  change (if eq_dec message nullval then emp else _) with (asc_buf message len (map Vubyte mb)).
  change (if eq_dec whole nullval then emp else _) with (asc_buf whole len (Zrepeat Vundef len)).
  change (if eq_dec pieces nullval then emp else _) with (asc_buf pieces len (Zrepeat Vundef len)).
  forward_if (temp _t'6 (Vint (if orb (asc_nul message) (asc_nul whole) then Int.one else Int.zero))).
  { forward. entailer!. }
  { forward. entailer!. rewrite asc_test_eq by auto. unfold asc_nul at 1. rewrite if_false by auto. reflexivity. }
  forward_if (temp _t'7 (Vint (if orb (orb (asc_nul message) (asc_nul whole)) (asc_nul pieces)
    then Int.one else Int.zero))).
  { forward. match goal with H: (if ?b then Int.one else Int.repr 0) <> Int.zero |- _ =>
      apply asc_if_true in H; rewrite H end. apply ENTAIL_refl. }
  { forward. match goal with H: (if ?b then Int.one else Int.repr 0) = Int.zero |- _ =>
      apply asc_if_false in H; rewrite H end. entailer!. rewrite asc_test_eq by auto. reflexivity. }
  forward_if (orb (orb (asc_nul message) (asc_nul whole)) (asc_nul pieces) = false).
  { forward. sep_apply (data_at_data_at_ Tsh (tarray tuchar 16) (map (fun b : Z => Vint (Int.repr b)) ivz) v_iv).
    sep_apply (data_at_data_at_ Tsh (tarray tuint 8) (map Vint ks) v_key). cancel. }
  { forward. match goal with H: (if ?b then Int.one else Int.repr 0) = Int.zero |- _ =>
      apply asc_if_false in H end. entailer!. }
  Intros.
  match goal with H: orb _ _ = false |- _ => rename H into Hnn end.
  rewrite !orb_false_iff in Hnn. destruct Hnn as [[Hm Hw] Hp].
  unfold asc_nul in Hm, Hw, Hp. unfold asc_buf.
  destruct (eq_dec message nullval); [discriminate |].
  destruct (eq_dec whole nullval); [discriminate |].
  destruct (eq_dec pieces nullval); [discriminate |].
  clear Hm Hw Hp.
  (* in one call *)
  rewrite asc_bytes by auto.
  set (ivb := map Byte.repr ivz).
  assert (Hivb: Zlength ivb = 16) by (unfold ivb; rewrite Zlength_map; auto).
  replace (data_at Tsh (tarray tuchar 16) (map Vubyte ivb) v_iv)
    with (data_at Tsh (tarray tuchar (Zlength ivb)) (map Vubyte ivb) v_iv) by (rewrite Hivb; reflexivity).
  clearbody ivb.
  forward_call (Tsh, v_one, Tsh, v_key, ks, Tsh, v_iv, ivb).
  subst len.
  rewrite (asc_out_split Ews (Zrepeat Vundef (Zlength mb)) whole) by list_solve.
  rewrite (asc_bytes_split Ews mb message) by reflexivity.
  repeat flatten_sepcon_in_SEP.
  forward_call (Tsh, v_one, chacha_init_st ks ivb, Ews, whole, Ews, message, mb).
  { apply asc_Zlength_init_st; auto. }
  assert (Hst: Zlength (chacha_init_st ks ivb) = 16) by (apply asc_Zlength_init_st; auto).
  remember (chacha_init_st ks ivb) as st eqn:Est.
  assert (Hx: Zlength (map Vubyte (chacha_xor 10 st mb)) = Zlength mb)
    by (rewrite Zlength_map; apply lg3_Zlength_chacha_xor; auto).
  sep_apply (asc_out_join Ews (map Vubyte (chacha_xor 10 st mb)) whole (Zlength mb) Hx).
  sep_apply (asc_bytes_join Ews mb message (Zlength mb) eq_refl).
  (* in pieces *)
  forward_call (Tsh, v_many, Tsh, v_key, ks, Tsh, v_iv, ivb).
  rewrite <- Est.
  forward.
  set (len := Zlength mb) in *.
  set (FR := (@data_at Chacha20poly1305.CS Tsh t_chacha_state (map Vint (chacha_advance st (chacha_nblocks len))) v_one *
    mem_mgr gv * malloc_token Ews (tarray tuchar len) pieces * malloc_token Ews (tarray tuchar len) whole *
    malloc_token Ews (tarray tuchar len) message * TT)%logic).
  forward_while (EX done: Z,
    PROP (0 <= done <= len; done mod 64 = 0 \/ done = len)
    LOCAL (temp _done (Vlong (Int64.repr done)); temp _pieces pieces; temp _whole whole;
           temp _message message; temp _len (Vlong (Int64.repr len));
           lvar _many (Tstruct _chacha_state noattr) v_many; lvar _one (Tstruct _chacha_state noattr) v_one;
           lvar _iv (tarray tuchar 16) v_iv; lvar _key (tarray tuint 8) v_key; gvars gv)
    SEP (@data_at Chacha20poly1305.CS Tsh t_chacha_state (map Vint (chacha_advance st (chacha_nblocks done))) v_many;
         data_at Ews (tarray tuchar len)
           (map Vubyte (chacha_xor 10 st (sublist 0 done mb)) ++ Zrepeat Vundef (len - done)) pieces;
         data_at Tsh (tarray tuint 8) (map Vint ks) v_key;
         data_at Tsh (tarray tuchar (Zlength ivb)) (map Vubyte ivb) v_iv;
         data_at Ews (tarray tuchar len) (map Vubyte mb) message;
         data_at Ews (tarray tuchar len) (map Vubyte (chacha_xor 10 st mb)) whole; FR))%assert.
  { Exists 0. unfold FR. entailer!.
    change (chacha_nblocks 0) with 0. rewrite lg3_advance_0 by auto. rewrite app_nil_l. cancel. }
  { entailer!. }
  { assert (Hlt: done < len).
    { unfold Int64.ltu in HRE. rewrite !Int64.unsigned_repr in HRE by rep_lia.
      destruct (zlt done len); [lia | discriminate]. }
    assert (Hd64: done mod 64 = 0) by (destruct H4; [auto | lia]).
    forward.
    rewrite sub64_repr.
    forward_call tt. Intros b.
    forward_if (EX take: Z,
      PROP (0 <= take <= len - done; take = len - done \/ take mod 64 = 0)
      LOCAL (temp _take (Vlong (Int64.repr take)); temp _done (Vlong (Int64.repr done)); temp _pieces pieces;
             temp _whole whole; temp _message message; temp _len (Vlong (Int64.repr len));
             lvar _many (Tstruct _chacha_state noattr) v_many; lvar _one (Tstruct _chacha_state noattr) v_one;
             lvar _iv (tarray tuchar 16) v_iv; lvar _key (tarray tuint 8) v_key; gvars gv)
      SEP (@data_at Chacha20poly1305.CS Tsh t_chacha_state (map Vint (chacha_advance st (chacha_nblocks done))) v_many;
           data_at Ews (tarray tuchar len)
             (map Vubyte (chacha_xor 10 st (sublist 0 done mb)) ++ Zrepeat Vundef (len - done)) pieces;
           data_at Tsh (tarray tuint 8) (map Vint ks) v_key;
           data_at Tsh (tarray tuchar (Zlength ivb)) (map Vubyte ivb) v_iv;
           data_at Ews (tarray tuchar len) (map Vubyte mb) message;
           data_at Ews (tarray tuchar len) (map Vubyte (chacha_xor 10 st mb)) whole; FR))%assert.
    { forward_call ((len - done) / 64).
      { split; [apply Z.div_pos; lia |].
        assert ((len - done) / 64 <= len - done) by (apply Z.div_le_upper_bound; lia). rep_lia. }
      Intros k. forward. Exists (64 * k). entailer!.
      split.
      { assert (64 * ((Zlength mb - done) / 64) <= Zlength mb - done) by (apply Z.mul_div_le; lia). lia. }
      right. rewrite Z.mul_comm. apply Z_mod_mult. }
    { forward. Exists (len - done). entailer!. }
    Intros take.
    assert (HA: Zlength (chacha_xor 10 st (sublist 0 done mb)) = done)
      by (rewrite lg3_Zlength_chacha_xor, Zlength_sublist by (auto; lia); lia).
    assert (HT: Zlength (sublist done (done + take) mb) = take) by (rewrite Zlength_sublist; lia).
    assert_PROP (field_compatible (tarray tuchar len) [] pieces) as Fp by entailer!.
    assert_PROP (field_compatible (tarray tuchar len) [] message) as Fm by entailer!.
    rewrite (asc_pieces_split Ews len done take _ pieces) by (auto; lia).
    rewrite (asc_msg_split Ews len done take mb message) by (auto; lia).
    replace (Zrepeat Vundef take) with (Zrepeat Vundef (Zlength (sublist done (done + take) mb))) by (rewrite HT; auto).
    rewrite (asc_out_split Ews (Zrepeat Vundef (Zlength (sublist done (done + take) mb))) (offset_val done pieces) take)
      by (rewrite Zlength_Zrepeat; lia).
    rewrite (asc_bytes_split Ews (sublist done (done + take) mb) (offset_val done message) take) by auto.
    repeat flatten_sepcon_in_SEP.
    forward_call (Tsh, v_many, chacha_advance st (chacha_nblocks done), Ews, offset_val done pieces,
                  Ews, offset_val done message, sublist done (done + take) mb).
    { rewrite HT. entailer!. }
    { rewrite lg3_Zlength_advance; auto. }
    rewrite HT.
    destruct (asc_step st mb done take) as [Exor Eadv]; auto; try lia.
    rewrite Eadv.
    set (B := chacha_xor 10 (chacha_advance st (chacha_nblocks done)) (sublist done (done + take) mb)).
    assert (HB: Zlength B = take) by (unfold B; rewrite lg3_Zlength_chacha_xor by (rewrite lg3_Zlength_advance; auto); auto).
    assert (HB': Zlength (map Vubyte B) = take) by (rewrite Zlength_map; auto).
    sep_apply (asc_out_join Ews (map Vubyte B) (offset_val done pieces) take HB').
    sep_apply (asc_bytes_join Ews (sublist done (done + take) mb) (offset_val done message) take HT).
    sep_apply (asc_pieces_join Ews len done take (chacha_xor 10 st (sublist 0 done mb)) B pieces); try lia; auto.
    sep_apply (derives_refl' _ _ (eq_sym (asc_msg_split Ews len done take mb message
      ltac:(lia) ltac:(lia) ltac:(lia) eq_refl Fm))).
    unfold B; rewrite <- Exor.
    forward.
    Exists (done + take). entailer!.
    destruct H7 as [E|E]; [right; lia | left; rewrite Z.add_mod, Hd64, E by lia; reflexivity]. }
  (* check *)
  assert (done = len).
  { unfold Int64.ltu in HRE. rewrite !Int64.unsigned_repr in HRE by rep_lia.
    destruct (zlt done len); [discriminate | lia]. }
  subst done. rewrite sublist_same by auto. rewrite Z.sub_diag, Zrepeat_0, app_nil_r.
  replace (data_at Ews (tarray tuchar len) (map Vubyte (chacha_xor 10 st mb)) whole)
    with (data_at Ews (tarray tuchar (Zlength (map Vubyte (chacha_xor 10 st mb))))
            (map Vubyte (chacha_xor 10 st mb)) whole) by (rewrite Hx; reflexivity).
  replace (data_at Ews (tarray tuchar len) (map Vubyte (chacha_xor 10 st mb)) pieces)
    with (data_at Ews (tarray tuchar (Zlength (map Vubyte (chacha_xor 10 st mb))))
            (map Vubyte (chacha_xor 10 st mb)) pieces) by (rewrite Hx; reflexivity).
  forward_call (Ews, whole, map Vubyte (chacha_xor 10 st mb), chacha_xor 10 st mb,
                Ews, pieces, map Vubyte (chacha_xor 10 st mb), chacha_xor 10 st mb, len).
  { rewrite sublist_same by auto. auto. }
  destruct (list_eq_dec Byte.eq_dec (chacha_xor 10 st mb) (chacha_xor 10 st mb)) as [_|C]; [| contradiction C; auto].
  forward_call (Int.one).
  forward.
  unfold FR. rewrite Hivb.
  sep_apply (data_at_data_at_ Tsh (tarray tuint 8) (map Vint ks) v_key).
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 16) (map Vubyte ivb) v_iv).
  sep_apply (asc_state_free Tsh (chacha_advance (chacha_init_st ks ivb) (chacha_nblocks (Zlength mb))) v_one).
  sep_apply (asc_state_free Tsh (chacha_advance (chacha_init_st ks ivb) (chacha_nblocks (Zlength mb))) v_many).
  cancel.
Qed.
