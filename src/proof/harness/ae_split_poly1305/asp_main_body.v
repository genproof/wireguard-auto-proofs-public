(* The body of main of law ae_split_poly1305 against main_spec of the whole program (QPmain_spec_ext'), in the
   world W_asp, with the harness piece's context: the tag of the whole message and the tag of the message handed
   over in any pieces are both poly1305_tag key message (poly1305_update_spec3 appends each piece to the
   context's message), so bytes_eq returns 1 and gp_assert's precondition holds. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.harness.ae_split_poly1305.asp_spec.

#[local] Existing Instance W_asp.
Local Open Scope Z_scope.

(* main's precondition: keep gvars, forget the globals and the external state, and create the memory
   manager (any_bytes allocates) *)
Lemma asp_main_pre {Espec: OracleKind} Delta (prog: QP.program function) (gv: globals) R c Post:
  semax Delta (PROP () LOCAL (gvars gv) SEP (mem_mgr gv; TT) * R)%logic c Post ->
  semax Delta (close_precondition nil (@main_pre unit prog tt gv) * R)%logic c Post.
Proof.
  intros H. eapply semax_pre; [|apply H]; clear H.
  unfold main_pre, PROPx, LOCALx, SEPx, local, lift1.
  intro rho. unfold close_precondition. simpl. unfold_lift. normalize.
  rewrite prop_true_andp; [| split; auto; hnf; reflexivity].
  apply sepcon_derives; auto.
  eapply derives_trans; [| apply sepcon_derives; [apply create_mem_mgr | apply derives_refl]].
  rewrite emp_sepcon. apply TT_right.
Qed.

(* the bytes drawn by nondet_bytes, as bytes *)
Lemma asp_bytes (kz: list Z) : Forall (fun b => 0 <= b <= Byte.max_unsigned) kz ->
  map (fun b => Vint (Int.repr b)) kz = map Vubyte (map Byte.repr kz).
Proof.
  induction 1; simpl; f_equal; auto.
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

(* the context struct poly1305_desc_ctx seen by the Poly1305 functions: the same struct in Poly1305.CS *)
#[local] Instance asp_CCE : change_composite_env W_asp Poly1305.CS.
Proof. make_cs_preserve W_asp Poly1305.CS. Defined.

(* an uninitialised context, in Poly1305.CS and in the world *)
Lemma asp_ctx_W sh v :
  @data_at_ Poly1305.CS sh t_p1305_ctx v = @data_at_ W_asp sh (Tstruct ASP._poly1305_desc_ctx noattr) v.
Proof.
  symmetry. exact (f_equal (fun f => f v)
    (@data_at__change_composite W_asp Poly1305.CS asp_CCE sh (Tstruct ASP._poly1305_desc_ctx noattr) eq_refl)).
Qed.

(* the message buffer without the piece [pos, pos + c) *)
Definition asp_rest (sh: share) (n: Z) (mb: list byte) (pos c: Z) (msg: val) : mpred :=
  !! field_compatible (tarray tuchar n) [] msg &&
  (data_at sh (tarray tuchar pos) (map Vubyte (sublist 0 pos mb)) msg *
   data_at sh (tarray tuchar (n - (pos + c))) (map Vubyte (sublist (pos + c) n mb))
     (field_address0 (tarray tuchar n) (SUB (pos + c)) msg))%logic.

(* the message buffer is the piece [pos, pos + c) handed to poly1305_update (Poly1305's prim_bytes) and the
   rest *)
Lemma asp_chunk_split sh n mb pos c msg :
  0 <= pos -> 0 <= c -> pos + c <= n -> Zlength mb = n ->
  data_at sh (tarray tuchar n) (map Vubyte mb) msg =
  (@WgNoise.proof.prims.prim_api.prim_bytes Poly1305.CS sh (sublist pos (pos + c) mb) (offset_val pos msg) *
   asp_rest sh n mb pos c msg)%logic.
Proof.
  intros Hp Hc Hn Hl. unfold asp_rest, WgNoise.proof.prims.prim_api.prim_bytes.
  rewrite Zlength_sublist by lia.
  destruct (Z.eq_dec (pos + c - pos) 0).
  - assert (c = 0) by lia. subst c. rewrite Z.add_0_r, emp_sepcon.
    apply pred_ext; [assert_PROP (field_compatible (tarray tuchar n) [] msg) by entailer! |];
    rewrite (split2_data_at_Tarray_tuchar sh n pos (map Vubyte mb)) by (rewrite ?Zlength_map; lia);
    rewrite !sublist_map; entailer!.
  - rewrite (@data_at_tarray_tuchar_cs Poly1305.CS W_asp).
    replace (pos + c - pos) with c by lia.
    apply pred_ext; [assert_PROP (field_compatible (tarray tuchar n) [] msg) by entailer! |];
    rewrite (split3_data_at_Tarray_tuchar sh n pos (pos + c) (map Vubyte mb)) by (rewrite ?Zlength_map; lia);
    rewrite !sublist_map; replace (pos + c - pos) with c by lia;
    Intros; saturate_local;
      (rewrite (field_address0_offset (tarray tuchar n) (SUB pos)) by auto with field_compatible;
       simpl nested_field_offset; rewrite Z.mul_1_l, Z.add_0_l; entailer!).
Qed.

(* what any_bytes returns is NULL or a pointer to its object: main can compare it with NULL *)
Lemma asp_mres_valid n bs p :
  (if eq_dec p nullval then emp
   else malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) (map Vubyte bs) p)
  |-- valid_pointer p.
Proof.
  destruct (eq_dec p nullval).
  - subst. apply valid_pointer_null.
  - destruct (zlt 0 n).
    + apply sepcon_valid_pointer2. apply data_at_valid_ptr; [auto | simpl sizeof; lia].
    + apply sepcon_valid_pointer1. apply malloc_token_valid_pointer. simpl sizeof. lia.
Qed.

#[local] Hint Resolve asp_mres_valid : valid_pointer.

Lemma asp_mres_local n bs p :
  (if eq_dec p nullval then emp
   else malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) (map Vubyte bs) p)
  |-- !! is_pointer_or_null p.
Proof.
  destruct (eq_dec p nullval).
  - subst. apply prop_right. simpl. auto.
  - entailer!; destruct p; try contradiction; simpl; auto.
Qed.

#[local] Hint Resolve asp_mres_local : saturate_local.

(* main.  The two contexts are handed to the Poly1305 functions in Poly1305.CS and kept in W_asp (as data_at_)
   when they are not in use; the resources the calls do not touch are frozen around each call: a separation
   goal mixing assertions of the two compspecs makes cancel very slow.  Loop invariant: done bytes handed over,
   the second context holds the message's first done bytes. *)
Lemma asp_main_body : @semax_body asp_V asp_Gprog W_asp ASP.f_main asp_main_spec.
Proof.
  unfold asp_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  simpl fn_body; simpl fn_params; simpl fn_return.
  change (fun rho => ?A rho * ?B rho)%logic with (A * B)%logic.
  apply asp_main_pre.
  simpl app. simplify_func_tycontext.
  process_stackframe_of.
  unfold asp_post.
  replace (fun (_ : environ) => @TT mpred _) with (PROP () LOCAL () SEP (TT))%assert
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  abbreviate_semax.
  forward_call (v_key, 32, Tsh). Intros kz.
  rewrite asp_bytes by auto.
  set (kb := map Byte.repr kz).
  assert (HZ: Zlength kb = 32) by (unfold kb; rewrite Zlength_map; auto).
  clearbody kb.
  forward_call (Int64.max_signed). Intros len.
  forward_call (len, gv). Intros vret. destruct vret as [msg mb]. cbn [fst snd] in H2 |- *. subst len.
  forward_if.
  { forward. sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (map Vubyte kb) v_key). cancel. }
  rewrite if_false by auto. Intros.
  assert_PROP (isptr msg) as Hmsg by (entailer!; destruct msg; try contradiction; simpl; auto).
  erewrite (@data_at__change_composite W_asp Poly1305.CS _ Tsh (Tstruct ASP._poly1305_desc_ctx noattr));
    [| prove_cs_preserve_type].
  forward_call (Tsh, v_one, Tsh, v_key, kb).
  rewrite (asp_chunk_split Ews (Zlength mb) mb 0 (Zlength mb) msg) by lia. Intros.
  rewrite sublist_same, isptr_offset_val_zero by auto.
  forward_call (Tsh, v_one, kb, @nil byte, Ews, msg, mb).
  forward_call (Tsh, v_one, kb, [] ++ mb, Tsh, v_whole).
  rewrite app_nil_l.
  sep_apply (@data_at_data_at_ Poly1305.CS Tsh t_p1305_ctx p1305_ctx_zero v_one).
  rewrite (asp_ctx_W Tsh v_one).
  replace (@prim_api.prim_bytes Poly1305.CS Ews mb msg)
    with (@prim_api.prim_bytes Poly1305.CS Ews (sublist 0 (0 + Zlength mb) mb) (offset_val 0 msg))
    by (rewrite Z.add_0_l, sublist_same, isptr_offset_val_zero by auto; reflexivity).
  gather_SEP (@prim_api.prim_bytes Poly1305.CS _ _ _) (asp_rest _ _ _ _ _ _).
  rewrite <- (asp_chunk_split Ews (Zlength mb) mb 0 (Zlength mb) msg) by lia.
  freeze FR := (data_at_ _ _ v_one) (data_at _ _ _ v_whole) (data_at _ _ _ msg) (malloc_token _ _ msg)
    (mem_mgr gv) (data_at_ _ _ v_pieces).
  forward_call (Tsh, v_many, Tsh, v_key, kb).
  forward.
  thaw FR.
  rewrite !(@data_at_tarray_tuchar_cs Poly1305.CS W_asp).
  forward_loop (EX done: Z,
    PROP (0 <= done <= Zlength mb)
    LOCAL (temp ASP._done (Vlong (Int64.repr done)); temp ASP._message msg;
           temp ASP._len (Vlong (Int64.repr (Zlength mb)));
           lvar ASP._pieces (tarray tuchar 16) v_pieces; lvar ASP._whole (tarray tuchar 16) v_whole;
           lvar ASP._many (Tstruct ASP._poly1305_desc_ctx noattr) v_many;
           lvar ASP._one (Tstruct ASP._poly1305_desc_ctx noattr) v_one;
           lvar ASP._key (tarray tuchar 32) v_key; gvars gv)
    SEP (data_at Ews (tarray tuchar (Zlength mb)) (map Vubyte mb) msg;
         p1305_state Tsh kb (sublist 0 done mb) v_many;
         data_at_ Tsh (Tstruct ASP._poly1305_desc_ctx noattr) v_one;
         data_at Tsh (tarray tuchar 16) (map Vubyte (poly1305_tag kb mb)) v_whole;
         data_at Tsh (tarray tuchar 32) (map Vubyte kb) v_key;
         malloc_token Ews (tarray tuchar (Zlength mb)) msg; mem_mgr gv;
         data_at_ Tsh (tarray tuchar 16) v_pieces; TT))%assert
  break: (PROP ()
    LOCAL (temp ASP._message msg;
           temp ASP._len (Vlong (Int64.repr (Zlength mb)));
           lvar ASP._pieces (tarray tuchar 16) v_pieces; lvar ASP._whole (tarray tuchar 16) v_whole;
           lvar ASP._many (Tstruct ASP._poly1305_desc_ctx noattr) v_many;
           lvar ASP._one (Tstruct ASP._poly1305_desc_ctx noattr) v_one;
           lvar ASP._key (tarray tuchar 32) v_key; gvars gv)
    SEP (p1305_state Tsh kb mb v_many;
         data_at_ Tsh (Tstruct ASP._poly1305_desc_ctx noattr) v_one;
         data_at Tsh (tarray tuchar 16) (map Vubyte (poly1305_tag kb mb)) v_whole;
         data_at Tsh (tarray tuchar 32) (map Vubyte kb) v_key;
         data_at Ews (tarray tuchar (Zlength mb)) (map Vubyte mb) msg;
         malloc_token Ews (tarray tuchar (Zlength mb)) msg; mem_mgr gv;
         data_at_ Tsh (tarray tuchar 16) v_pieces; TT))%assert.
  { Exists 0. rewrite sublist_nil. entailer!. }
  { Intros done.
    forward_if (EX t: int,
      PROP (t = Int.zero -> Zlength mb <= done)
      LOCAL (temp ASP._t'3 (Vint t); temp ASP._done (Vlong (Int64.repr done)); temp ASP._message msg;
             temp ASP._len (Vlong (Int64.repr (Zlength mb)));
             lvar ASP._pieces (tarray tuchar 16) v_pieces; lvar ASP._whole (tarray tuchar 16) v_whole;
             lvar ASP._many (Tstruct ASP._poly1305_desc_ctx noattr) v_many;
             lvar ASP._one (Tstruct ASP._poly1305_desc_ctx noattr) v_one;
             lvar ASP._key (tarray tuchar 32) v_key; gvars gv)
      SEP (data_at Ews (tarray tuchar (Zlength mb)) (map Vubyte mb) msg;
           p1305_state Tsh kb (sublist 0 done mb) v_many;
           data_at_ Tsh (Tstruct ASP._poly1305_desc_ctx noattr) v_one;
           data_at Tsh (tarray tuchar 16) (map Vubyte (poly1305_tag kb mb)) v_whole;
           data_at Tsh (tarray tuchar 32) (map Vubyte kb) v_key;
           malloc_token Ews (tarray tuchar (Zlength mb)) msg; mem_mgr gv;
           data_at_ Tsh (tarray tuchar 16) v_pieces; TT))%assert.
    { forward. Exists Int.one. entailer!. discriminate. }
    { freeze FR := (p1305_state _ _ _ _) (data_at_ _ _ v_one) (data_at _ _ _ v_whole) (data_at _ _ _ v_key)
        (data_at _ _ _ msg) (malloc_token _ _ msg) (mem_mgr gv) (data_at_ _ _ v_pieces).
      forward_call tt. Intros b. forward. thaw FR.
      Exists (if zeq b 0 then Int.zero else Int.one). entailer!.
      all: try (intros; lia). all: destruct (zeq b 0); reflexivity. }
    Intros t.
    forward_if.
    { freeze FR := (p1305_state _ _ _ _) (data_at_ _ _ v_one) (data_at _ _ _ v_whole) (data_at _ _ _ v_key)
        (data_at _ _ _ msg) (malloc_token _ _ msg) (mem_mgr gv) (data_at_ _ _ v_pieces).
      forward_call (Zlength mb - done). Intros take.
      thaw FR.
      rewrite (asp_chunk_split Ews (Zlength mb) mb done take msg) by lia. Intros.
      freeze FR := (data_at_ _ _ v_one) (data_at _ _ _ v_whole) (data_at _ _ _ v_key)
        (asp_rest _ _ _ _ _ _) (malloc_token _ _ msg) (mem_mgr gv) (data_at_ _ _ v_pieces).
      forward_call (Tsh, v_many, kb, sublist 0 done mb, Ews, offset_val done msg, sublist done (done + take) mb).
      { entailer!. rewrite Zlength_sublist by lia. replace (done + take - done) with take by lia.
        destruct v_many; try contradiction; destruct msg; try contradiction; simpl. reflexivity. }
      { rewrite Zlength_sublist by lia. rep_lia. }
      forward. thaw FR.
      Exists (done + take).
      rewrite <- sublist_split by lia.
      gather_SEP (@prim_api.prim_bytes Poly1305.CS _ _ _) (asp_rest _ _ _ _ _ _).
      rewrite <- (asp_chunk_split Ews (Zlength mb) mb done take msg) by lia.
      rewrite add64_repr. entailer!. }
    assert (done = Zlength mb)
      by (match goal with Hz: t = Int.zero -> _, Ht: t = Int.zero |- _ => specialize (Hz Ht) end; lia).
    subst done. rewrite sublist_same by lia.
    forward. entailer!. }
  freeze FR := (data_at _ _ _ msg) (data_at_ _ _ v_one) (data_at _ _ _ v_whole) (data_at _ _ _ v_key)
    (malloc_token _ _ msg) (mem_mgr gv).
  forward_call (Tsh, v_many, kb, mb, Tsh, v_pieces).
  sep_apply (@data_at_data_at_ Poly1305.CS Tsh t_p1305_ctx p1305_ctx_zero v_many).
  rewrite (asp_ctx_W Tsh v_many).
  rewrite !(@data_at_tarray_tuchar_cs Poly1305.CS W_asp).
  thaw FR.
  assert (Htag: Zlength (map Vubyte (poly1305_tag kb mb)) = 16) by (rewrite Zlength_map; reflexivity).
  set (tg := map Vubyte (poly1305_tag kb mb)) in *.
  replace (data_at Tsh (tarray tuchar 16) tg) with (data_at Tsh (tarray tuchar (Zlength tg)) tg)
    by (rewrite Htag; reflexivity).
  freeze FR := (data_at_ _ _ v_many) (data_at _ _ _ msg) (data_at_ _ _ v_one) (data_at _ _ _ v_key)
    (malloc_token _ _ msg) (mem_mgr gv).
  (* both tags are poly1305_tag kb mb: bytes_eq returns 1 *)
  forward_call (Tsh, v_whole, tg, poly1305_tag kb mb, Tsh, v_pieces, tg, poly1305_tag kb mb, 16).
  destruct (list_eq_dec Byte.eq_dec (poly1305_tag kb mb) (poly1305_tag kb mb)) as [_|C];
    [| contradiction C; reflexivity].
  forward_call (Int.one).
  thaw FR. rewrite Htag.
  forward.
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (map Vubyte kb) v_key).
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 16) tg v_whole).
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 16) tg v_pieces).
  cancel.
Qed.
