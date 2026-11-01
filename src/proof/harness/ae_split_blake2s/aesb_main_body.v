(* The body of main of law ae_split_blake2s (harness/ae_split_blake2s.c): the one-shot blake2s() and
   blake2s_init / blake2s_init_key, blake2s_update over any pieces, blake2s_final give the same first out_len
   bytes, so the final gp_assert(bytes_eq(whole, pieces, out_len)) always gets 1. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.harness.ae_split_blake2s.aesb_world.
Require Import WgNoise.proof.harness.ae_split_blake2s.aesb_spec.
Require WgNoise.proof.libc.libc_bytes.
Require WgNoise.proof.harness.prim_blake2s.hb2s_main_defs.
Require WgNoise.contracts.ae_split_blake2s.
Require WgNoise.harness.ae_split_blake2s.code.

#[local] Existing Instance W_aesb.
Local Open Scope Z_scope.

Module AC := WgNoise.harness.ae_split_blake2s.code.

(* The program's only global is blake2s_sigma; main's initial globals are the table blake2s_update and
   blake2s_final read (blake2s_globals), seen as a flat byte array while it is initialised *)
Definition aesb_vardefs_flat :=
  ltac:(let x := eval vm_compute in
    (map WgNoise.proof.harness.prim_blake2s.hb2s_main_defs.hb2s_flat
       (Vardefs WgNoise.contracts.ae_split_blake2s.whole_prog)) in exact x).

Lemma aesb_init_globals gv :
  globals_ok gv ->
  InitGPred (Vardefs WgNoise.contracts.ae_split_blake2s.whole_prog) gv |-- blake2s_globals gv.
Proof.
  intros Hgv.
  change (InitGPred aesb_vardefs_flat gv |-- (fun g => blake2s_globals g)%logic gv).
  eapply InitGPred_process_globvars; auto.
  let Delta := fresh "Delta" in let Delta' := fresh "Delta'" in
  set (Delta' := vardefs_tycontext _);
  set (Delta := @abbreviate tycontext Delta');
  change Delta' with Delta;
  hnf in Delta'; simpl in Delta'; subst Delta'.
  simpl vardefs_to_globvars.
  eapply derives_trans; [process_globals | ].
  clear Delta. apply finish_process_globvars'. unfold fold_right_sepcon at 1.
  simpl readonly2share. rewrite sepcon_emp.
  match goal with |- context [data_at ?sh (tarray tuchar 160) ?l ?p] =>
    replace l with (concat blake2s_sigma_val) by (vm_compute; reflexivity) end.
  change (gv 351097212369991831168331%positive) with (gv _blake2s_sigma).
  unfold blake2s_globals. rewrite <- WgNoise.proof.harness.prim_blake2s.hb2s_main_defs.hb2s_sigma_flat.
  apply derives_refl.
Qed.

(* main's postcondition (TT) weakened to the canonical form forward needs for a return *)
Lemma aesb_post_canon {Espec: OracleKind} {cs: compspecs} Delta P c gv F :
  semax Delta P c (frame_ret_assert (function_body_ret_assert tint (PROP () LOCAL () SEP (TT))) F) ->
  semax Delta P c (frame_ret_assert (function_body_ret_assert tint (aesb_post gv)) F).
Proof.
  intros H. eapply semax_post; [| | | | apply H]; intros; simpl; intros rho; apply andp_left2;
    try apply derives_refl.
  apply sepcon_derives; [| apply derives_refl]. revert rho. apply bind_ret_derives. intros rho. apply TT_right.
Qed.

(* nondet_bytes gives integers in byte range: they are the bytes map Byte.repr bs *)
Lemma aesb_bytes bs : Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  map (fun b => Vint (Int.repr b)) bs = map Vubyte (map Byte.repr bs).
Proof.
  induction 1; simpl; f_equal; auto.
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

(* byte arrays are the same predicate in every compspecs *)
Lemma aesb_cs sh n (v: list val) p :
  data_at sh (tarray tuchar n) v p = @data_at Blake2s.CS sh (tarray tuchar n) v p.
Proof. apply WgNoise.proof.libc.libc_bytes.data_at_tarray_tuchar_cs. Qed.

(* the key pointer main passes to blake2s: the key array, or NULL for the empty key *)
Definition aesb_kptr (keylen: Z) (p: val) : val := if zlt 0 keylen then p else nullval.

(* the key array without its first keylen bytes (all of it for the empty key) *)
Definition aesb_krest (sh: share) (kb: list byte) (keylen: Z) (p: val) : mpred :=
  if zlt 0 keylen
  then data_at sh (tarray tuchar (32 - keylen)) (sublist keylen 32 (map Vubyte kb))
         (field_address0 (tarray tuchar 32) [ArraySubsc keylen] p)
  else data_at sh (tarray tuchar 32) (map Vubyte kb) p.

(* the key array split at keylen: the key as BLAKE2s reads it and the rest *)
Lemma aesb_key sh kb keylen p :
  0 <= keylen <= 32 -> Zlength kb = 32 ->
  data_at sh (tarray tuchar 32) (map Vubyte kb) p =
  (b2s_bytes sh (sublist 0 keylen kb) (aesb_kptr keylen p) * aesb_krest sh kb keylen p)%logic.
Proof.
  intros Hk Hkb. unfold aesb_kptr, aesb_krest. destruct (zlt 0 keylen).
  - rewrite (split2_data_at_Tarray_tuchar sh 32 keylen) by (try lia; rewrite Zlength_map; lia).
    rewrite b2s_bytes_nonempty by (rewrite Zlength_sublist; lia).
    rewrite Zlength_sublist by lia. rewrite Z.sub_0_r, sublist_map.
    f_equal.
  - replace keylen with 0 by lia. rewrite sublist_nil, b2s_bytes_nil, emp_sepcon. reflexivity.
Qed.

(* a byte buffer as the input of blake2s; when it is empty, the buffer itself stays aside *)
Lemma aesb_msg sh l p :
  data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p =
  (b2s_bytes sh l p *
   (if Z.eq_dec (Zlength l) 0 then data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p else emp))%logic.
Proof.
  unfold b2s_bytes. if_tac.
  - rewrite emp_sepcon. reflexivity.
  - rewrite sepcon_emp. apply aesb_cs.
Qed.

(* a 32-byte output array of which the first n bytes are v: the n bytes blake2s / blake2s_final write
   and the rest *)
Lemma aesb_out sh n (v: list val) p :
  0 <= n <= 32 -> Zlength v = n ->
  data_at sh (tarray tuchar 32) (v ++ Zrepeat Vundef (32 - n)) p =
  (@data_at Blake2s.CS sh (tarray tuchar n) v p *
   data_at_ sh (tarray tuchar (32 - n)) (field_address0 (tarray tuchar 32) [ArraySubsc n] p))%logic.
Proof.
  intros Hn Hv.
  rewrite (split2_data_at_Tarray_tuchar sh 32 n) by (try lia; rewrite Zlength_app, Zlength_Zrepeat; lia).
  rewrite sublist_app1, sublist_same by lia. rewrite sublist_app2 by lia.
  rewrite Hv, Z.sub_diag, sublist_same by (rewrite ?Zlength_Zrepeat; lia).
  f_equal.
Qed.

Lemma aesb_out_undef sh n p :
  0 <= n <= 32 ->
  data_at_ sh (tarray tuchar 32) p =
  (@data_at_ Blake2s.CS sh (tarray tuchar n) p *
   data_at_ sh (tarray tuchar (32 - n)) (field_address0 (tarray tuchar 32) [ArraySubsc n] p))%logic.
Proof.
  intros Hn.
  replace (data_at_ sh (tarray tuchar 32) p) with
    (data_at sh (tarray tuchar 32) (Zrepeat Vundef n ++ Zrepeat Vundef (32 - n)) p).
  - rewrite aesb_out by (rewrite ?Zlength_Zrepeat; lia). reflexivity.
  - rewrite Zrepeat_app by lia. replace (n + (32 - n)) with 32 by lia. reflexivity.
Qed.

(* the message buffer without the chunk [pos, pos + c) *)
Definition aesb_rest (sh: share) (n: Z) (mb: list byte) (pos c: Z) (msg: val) : mpred :=
  !! field_compatible (tarray tuchar n) [] msg &&
  (data_at sh (tarray tuchar pos) (map Vubyte (sublist 0 pos mb)) msg *
   data_at sh (tarray tuchar (n - (pos + c))) (map Vubyte (sublist (pos + c) n mb))
     (field_address0 (tarray tuchar n) (SUB (pos + c)) msg))%logic.

(* the message buffer split around the chunk [pos, pos + c) that one blake2s_update reads *)
Lemma aesb_chunk sh n mb pos c msg :
  0 <= pos -> 0 <= c -> pos + c <= n -> Zlength mb = n ->
  data_at sh (tarray tuchar n) (map Vubyte mb) msg =
  (b2s_bytes sh (sublist pos (pos + c) mb) (offset_val pos msg) * aesb_rest sh n mb pos c msg)%logic.
Proof.
  intros Hp Hc Hn Hl. unfold aesb_rest, b2s_bytes.
  rewrite Zlength_sublist by lia.
  destruct (Z.eq_dec (pos + c - pos) 0).
  - assert (c = 0) by lia. subst c. rewrite Z.add_0_r, emp_sepcon.
    apply pred_ext; [assert_PROP (field_compatible (tarray tuchar n) [] msg) by entailer! |];
    rewrite (split2_data_at_Tarray_tuchar sh n pos (map Vubyte mb)) by (rewrite ?Zlength_map; lia);
    rewrite !sublist_map; entailer!.
  - replace (pos + c - pos) with c by lia. rewrite <- (aesb_cs sh c).
    apply pred_ext; [assert_PROP (field_compatible (tarray tuchar n) [] msg) by entailer! |];
    rewrite (split3_data_at_Tarray_tuchar sh n pos (pos + c) (map Vubyte mb)) by (rewrite ?Zlength_map; lia);
    rewrite !sublist_map; replace (pos + c - pos) with c by lia;
    Intros; saturate_local;
      (rewrite (field_address0_offset (tarray tuchar n) (SUB pos)) by auto with field_compatible;
       simpl nested_field_offset; rewrite Z.mul_1_l, Z.add_0_l; entailer!).
Qed.

#[local] Instance aesb_CCE : change_composite_env W_aesb Blake2s.CS.
Proof. make_cs_preserve W_aesb Blake2s.CS. Defined.

Lemma aesb_blake2s_len key outlen msg : 0 <= outlen -> Zlength (blake2s key outlen msg) = outlen.
Proof.
  intros. unfold blake2s, b2s_digest_stream, b2s_out. rewrite Zlength_map, Zlength_correct, upto_length.
  rep_lia.
Qed.

Lemma aesb_main_body :
  semax_body aesb_V aesb_Gprog WgNoise.harness.ae_split_blake2s.code.f_main aesb_main_spec.
Proof.
  unfold aesb_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply (main_pre_InitGpred (blake2s_globals gv));
    [apply aesb_init_globals | reflexivity
    | apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; subst x; vm_compute; exact I | ].
  process_stackframe_of.
  sep_apply (create_mem_mgr gv).
  cbv beta iota delta [fn_body AC.f_main fn_return]. apply aesb_post_canon. abbreviate_semax.
  forward_call (32 - 1). Intros o1. forward.
  forward_call 32. Intros keylen.
  forward_call (v_key, 32, Tsh). Intros kz.
  forward_call Int64.max_signed. Intros len.
  forward_call (len, gv). Intros vm. destruct vm as [message mb]. simpl fst in *; simpl snd in *.
  destruct (eq_dec message nullval) as [En|En].
  { (* any_bytes failed: main returns 0 *)
    subst message. forward_if; [| contradiction].
    forward. sep_apply (data_at_data_at_ Tsh (tarray tuchar 32)). cancel. }
  Intros.
  forward_if; [contradiction |].
  rewrite (aesb_bytes kz) by auto. set (kb := map Byte.repr kz).
  assert (Hkb: Zlength kb = 32) by (subst kb; rewrite Zlength_map; auto).
  clearbody kb. clear dependent kz.
  rewrite Int.signed_repr, add64_repr by rep_lia.
  set (outlen := 1 + o1). assert (Hol: 1 <= outlen <= 32) by lia. clearbody outlen.
  forward_if (temp AC._t'5 (aesb_kptr keylen v_key)).
  { forward. entailer!. unfold aesb_kptr. rewrite if_false; [reflexivity |].
    apply (f_equal Int64.unsigned) in H1. rewrite Int64.unsigned_repr in H1 by rep_lia. simpl in H1. lia. }
  { forward. entailer!. unfold aesb_kptr. rewrite if_true; [reflexivity |].
    assert (keylen <> 0) by (intro; subst; contradiction). lia. }
  (* the one-shot hash into whole *)
  rewrite (aesb_key Tsh kb keylen v_key) by auto.
  subst len. rewrite (aesb_msg Ews mb message).
  rewrite (aesb_out_undef Tsh outlen v_whole) by lia.
  Intros.
  forward_call (Tsh, aesb_kptr keylen v_key, sublist 0 keylen kb, Ews, message, mb, Tsh, v_whole, outlen, gv).
  { entailer!. rewrite Zlength_sublist by lia. rewrite Z.sub_0_r. unfold aesb_kptr.
    destruct message; try contradiction; destruct (zlt 0 keylen); destruct v_key; try contradiction; reflexivity. }
  { rewrite Zlength_sublist by lia. lia. }
  set (B := blake2s (sublist 0 keylen kb) outlen mb).
  assert (HB: Zlength (map Vubyte B) = outlen) by (rewrite Zlength_map; apply aesb_blake2s_len; lia).
  gather_SEP (b2s_bytes Ews _ _) (if Z.eq_dec _ _ then _ else _). rewrite <- aesb_msg.
  gather_SEP (data_at Tsh (tarray tuchar outlen) _ v_whole) (data_at_ Tsh (tarray tuchar (32 - outlen)) _).
  rewrite <- (aesb_out Tsh outlen (map Vubyte B) v_whole) by lia.
  (* the context, seen in Blake2s.CS *)
  erewrite (@data_at__change_composite W_aesb Blake2s.CS _ Tsh (Tstruct AC._blake2s_ctx noattr));
    [| prove_cs_preserve_type].
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
    match S with context C [@data_at_ Blake2s.CS Tsh _ v_ctx] =>
      let S' := context C [blake2s_state Tsh (sublist 0 keylen kb) outlen [] v_ctx] in
      forward_if (PROPx P (LOCALx L (SEPx S'))) end end.
  { (* no key: blake2s_init *)
    apply (f_equal Int64.unsigned) in H1. rewrite Int64.unsigned_repr in H1 by rep_lia. simpl in H1.
    forward_call (Tsh, v_ctx, outlen).
    replace (sublist 0 keylen kb) with (@nil byte) by (rewrite H1; reflexivity).
    entailer!. }
  { (* a key of 1..32 bytes: blake2s_init_key *)
    assert (Hk: keylen <> 0) by (intro E; rewrite E in H1; contradiction).
    unfold aesb_kptr. rewrite if_true by lia.
    forward_call (Tsh, v_ctx, outlen, Tsh, v_key, sublist 0 keylen kb).
    { entailer!. rewrite Zlength_sublist by lia. rewrite Z.sub_0_r. reflexivity. }
    { rewrite Zlength_sublist by lia. lia. }
    unfold aesb_kptr. rewrite if_true by lia. entailer!. }
  (* the pieces: done bytes absorbed *)
  forward.
  match goal with |- semax _ (PROPx ?P (LOCALx (temp ?i ?dv :: ?L) (SEPx ?S))) _ _ =>
    match S with context C [blake2s_state Tsh ?k ?o [] v_ctx] =>
      forward_loop (EX d: Z, PROPx ((0 <= d <= Zlength mb) :: P)
         (LOCALx (temp i (Vlong (Int64.repr d)) :: L)
         (SEPx ltac:(let t := context C [blake2s_state Tsh k o (sublist 0 d mb) v_ctx] in exact t))))
      break: (PROPx P (LOCALx (temp i (Vlong (Int64.repr (Zlength mb))) :: L)
         (SEPx ltac:(let t := context C [blake2s_state Tsh k o mb v_ctx] in exact t))))
    end end.
  { Exists 0. entailer!. }
  { Intros d.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
      forward_if (EX c: bool, PROPx ((d < Zlength mb -> c = true) :: P)
        (LOCALx (temp AC._t'6 (Vint (if c then Int.one else Int.zero)) :: L) (SEPx S))) end.
    { forward. Exists true. entailer!. }
    { forward_call tt. Intros b. forward. Exists (negb (zeq b 0)). entailer!.
      destruct (zeq b 0); reflexivity. }
    Intros c.
    forward_if (c = true).
    { forward. entailer!. destruct c; [reflexivity | contradiction]. }
    { (* the loop ends: all of the message was absorbed *)
      destruct c; [exfalso; apply Int.one_not_zero; exact H4 |].
      assert (d = Zlength mb) by (destruct (zlt d (Zlength mb)) as [Hlt|]; [specialize (H2 Hlt); discriminate | lia]).
      subst d. rewrite (sublist_same 0 (Zlength mb) mb) by lia. forward. entailer!. }
    Intros. subst c.
    forward_call (Zlength mb - d).
    Intros take.
    assert_PROP (isptr message) by entailer!.
    rewrite (aesb_chunk Ews (Zlength mb) mb d take message) by lia. Intros.
    forward_call (Tsh, v_ctx, sublist 0 keylen kb, outlen, sublist 0 d mb, Ews, offset_val d message,
                  sublist d (d + take) mb, gv).
    { entailer!. rewrite Zlength_sublist by lia. replace (d + take - d) with take by lia.
      destruct message; try contradiction; reflexivity. }
    { rewrite Zlength_sublist by lia. lia. }
    forward.
    Exists (d + take).
    rewrite <- sublist_split by lia.
    rewrite (aesb_chunk Ews (Zlength mb) mb d take message) by lia.
    entailer!. }
  (* blake2s_final into pieces: the same digest *)
  rewrite (aesb_out_undef Tsh outlen v_pieces) by lia. Intros.
  forward_call (Tsh, v_ctx, sublist 0 keylen kb, outlen, mb, Tsh, v_pieces, gv).
  change (blake2s (sublist 0 keylen kb) outlen mb) with B.
  gather_SEP (data_at Tsh (tarray tuchar outlen) _ v_pieces) (data_at_ Tsh (tarray tuchar (32 - outlen)) _).
  rewrite <- (aesb_out Tsh outlen (map Vubyte B) v_pieces) by lia.
  set (WB := map Vubyte B ++ Zrepeat Vundef (32 - outlen)).
  assert (HW: Zlength WB = 32) by (subst WB; rewrite Zlength_app, Zlength_Zrepeat; lia).
  assert (EW: forall p, data_at Tsh (tarray tuchar 32) WB p = data_at Tsh (tarray tuchar (Zlength WB)) WB p)
    by (intros; rewrite HW; reflexivity).
  rewrite !EW.
  forward_call (Tsh, v_whole, WB, B, Tsh, v_pieces, WB, B, outlen).
  { assert (sublist 0 outlen WB = map Vubyte B)
      by (subst WB; rewrite sublist_app1, sublist_same by lia; reflexivity).
    repeat split; auto; lia. }
  destruct (list_eq_dec Byte.eq_dec B B) as [_|NE]; [| congruence].
  forward_call Int.one.
  (* return 0: the locals are given back *)
  gather_SEP (b2s_bytes Tsh _ _) (aesb_krest _ _ _ _). rewrite <- aesb_key by auto.
  forward.
  sep_apply (@data_at_data_at_ Blake2s.CS Tsh t_blake2s_ctx b2s_ctx_zero v_ctx).
  rewrite (@data_at__change_composite W_aesb Blake2s.CS _ Tsh (Tstruct AC._blake2s_ctx noattr))
    by prove_cs_preserve_type.
  rewrite HW.
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) WB v_whole).
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) WB v_pieces).
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (map Vubyte kb) v_key).
  unfold t_blake2s_ctx. cancel.
Qed.
