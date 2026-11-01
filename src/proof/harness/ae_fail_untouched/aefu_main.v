(* Law ae_fail_untouched: the body of main (harness/ae_fail_untouched.c) against main's specification, in the
   world.  A failed decryption leaves its output as it was (aefu_decrypt_spec / aefu_xdecrypt_spec: None => old),
   and before holds a copy of the output's bytes (copy_of_spec), so bytes_eq returns 1 and the check holds. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.aead.aead_spec3b.
Require Import WgNoise.proof.harness.wg_laws.wl_spec.
Require Import WgNoise.proof.harness.wg_laws.wl_copy_of.
Require Import WgNoise.proof.harness.ae_fail_untouched.aefu_world.
Require Import WgNoise.proof.harness.ae_fail_untouched.aefu_spec.
Require WgNoise.contracts.ae_fail_untouched.
Require WgNoise.harness.ae_fail_untouched.code.
Require WgNoise.proof.harness.prim_aead.haead_main_body3_defs.
Require WgNoise.proof.aead.aead_models_props3.

#[local] Existing Instance W_ae_fail_untouched.
Module C := WgNoise.harness.ae_fail_untouched.code.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* The initial globals: keep the shim's zero page                          *)
(* ---------------------------------------------------------------------- *)

Definition aefu_keep (x: ident * globdef (fundef function) type) : bool :=
  Pos.eqb (fst x) _quickproof_zero_page.

Definition aefu_vardefs :=
  ltac:(let x := eval vm_compute in
    (filter aefu_keep (Vardefs WgNoise.contracts.ae_fail_untouched.whole_prog)) in exact x).

Lemma aefu_vardefs_eq :
  filter aefu_keep (Vardefs WgNoise.contracts.ae_fail_untouched.whole_prog) = aefu_vardefs.
Proof. vm_compute. reflexivity. Qed.

(* the initial globals of the whole program hold the zero page AEAD reads *)
Lemma aefu_init_globals gv :
  globals_ok gv ->
  InitGPred (Vardefs WgNoise.contracts.ae_fail_untouched.whole_prog) gv |-- (zero_page gv * TT)%logic.
Proof.
  intros Hgv.
  eapply derives_trans; [apply (haead_main_body3_defs.hm3_InitGPred_filter aefu_keep) |].
  rewrite aefu_vardefs_eq. apply sepcon_derives; [| apply derives_refl].
  change (InitGPred aefu_vardefs gv |-- (fun g => zero_page g)%logic gv).
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
  unfold zero_page.
  rewrite zero_val_tarray. replace (zero_val tuchar) with (Vubyte Byte.zero) by (rewrite zero_val_eq; reflexivity).
  match goal with |- data_at _ _ _ (gv ?i) |-- data_at _ _ _ (gv ?j) =>
    replace i with j by reflexivity end.
  apply derives_refl.
Qed.

(* ---------------------------------------------------------------------- *)
(* Byte buffers and the AEAD's views of them                              *)
(* ---------------------------------------------------------------------- *)

(* nondet_bytes gives integers in byte range: they are the bytes map Byte.repr bs *)
Lemma aefu_bytes bs : Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  map (fun b => Vint (Int.repr b)) bs = map Vubyte (map Byte.repr bs).
Proof.
  induction 1; simpl; f_equal; auto.
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

(* a byte buffer is the AEAD's input view (prim_bytes, emp when empty) and, when empty, the rest *)
Lemma aefu_split_bytes sh m p :
  data_at sh (tarray tuchar (Zlength m)) (map Vubyte m) p =
  (prim_bytes sh m p *
   (if Z.eq_dec (Zlength m) 0 then data_at sh (tarray tuchar (Zlength m)) (map Vubyte m) p else emp))%logic.
Proof.
  unfold prim_bytes. destruct (Z.eq_dec (Zlength m) 0).
  - rewrite emp_sepcon. reflexivity.
  - rewrite sepcon_emp. reflexivity.
Qed.

(* the same for the AEAD's output view (prim_out) *)
Lemma aefu_split_out sh (v: list val) p :
  data_at sh (tarray tuchar (Zlength v)) v p =
  (prim_out sh v p *
   (if Z.eq_dec (Zlength v) 0 then data_at sh (tarray tuchar (Zlength v)) v p else emp))%logic.
Proof.
  unfold prim_out. destruct (Z.eq_dec (Zlength v) 0).
  - rewrite emp_sepcon. reflexivity.
  - rewrite sepcon_emp. reflexivity.
Qed.

(* storing a byte value (0..255, as nondet_u8 gives it) into a byte buffer changes one of its bytes *)
Lemma aefu_store_byte bs j v : 0 <= j < Zlength bs -> 0 <= v <= Byte.max_unsigned ->
  upd_Znth j (map Vubyte bs) (Vint (Int.zero_ext 8 (Int.repr v))) = map Vubyte (upd_Znth j bs (Byte.repr v)).
Proof.
  intros Hj Hv. rewrite <- upd_Znth_map. f_equal. unfold Vubyte.
  rewrite Byte.unsigned_repr by rep_lia. f_equal.
  apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. rep_lia.
Qed.

(* main's postcondition (TT) weakened to the canonical form forward needs for a return *)
Lemma aefu_post_canon {Espec: OracleKind} {cs: compspecs} Delta P c gv F :
  semax Delta P c (frame_ret_assert (function_body_ret_assert tint (PROP () LOCAL () SEP (TT))) F) ->
  semax Delta P c (frame_ret_assert (function_body_ret_assert tint (aefu_post gv)) F).
Proof.
  intros H. eapply semax_post; [| | | | apply H]; intros; simpl; intros rho; apply andp_left2;
    try apply derives_refl.
  apply sepcon_derives; [| apply derives_refl]. revert rho. apply bind_ret_derives. intros rho. apply TT_right.
Qed.

(* Main's NULL test: case on each buffer (b = true: the buffer is NULL; otherwise a pointer Vptr) *)
Ltac aefu_case p b :=
  let E := fresh "E" in let PN := fresh "PN" in
  assert_PROP (is_pointer_or_null p) as PN by entailer!;
  destruct (eq_dec p nullval) as [E|E];
  [ pose (b := true); subst p
  | pose (b := false); destruct p; try contradiction;
    try (simpl in PN; subst; exfalso; apply E; reflexivity) ].

(* a branch of one of the ||'s of the NULL test *)
Ltac aefu_branch :=
  first [ contradiction | discriminate | idtac ];
  try (forward; entailer!; subst_any; simpl; auto).

Lemma aefu_main_body :
  semax_body aefu_V aefu_Gmain WgNoise.harness.ae_fail_untouched.code.f_main aefu_main_spec.
Proof.
  unfold aefu_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply (main_pre_InitGpred (zero_page gv * TT)%logic);
    [apply aefu_init_globals | reflexivity
    | apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; subst x; vm_compute; exact I | ].
  process_stackframe_of.
  sep_apply (create_mem_mgr gv).
  cbv beta iota delta [fn_body WgNoise.harness.ae_fail_untouched.code.f_main fn_return].
  apply aefu_post_canon. abbreviate_semax.
  forward_call tt. Intros t1.
  forward.
  forward_call (Int64.max_signed - 16). Intros len.
  forward_call Int64.max_signed. Intros ad_len.
  forward_call (len, gv). Intros vm. destruct vm as [message m]. simpl fst in *; simpl snd in *.
  forward_call (ad_len, gv). Intros va. destruct va as [ad a]. simpl fst in *; simpl snd in *.
  forward_call (tarray tuchar (len + 16), gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros sealed.
  (* the NULL test of message, ad and sealed *)
  aefu_case message bm; aefu_case ad ba; aefu_case sealed bq; Intros.
  all: forward_if (temp C._t'7 (Vint (if orb bm ba then Int.one else Int.zero)));
    [aefu_branch | aefu_branch | ].
  all: forward_if (temp C._t'8 (Vint (if orb bm (orb ba bq) then Int.one else Int.zero)));
    [aefu_branch | aefu_branch | ].
  all: forward_if (bm = false /\ ba = false /\ bq = false);
    [ first [contradiction | discriminate | (forward; cancel)]
    | first [contradiction | discriminate | (forward; entailer!)] | ].
  all: Intros; subst bm ba bq.
  all: try (repeat match goal with H: _ /\ _ |- _ => destruct H end; discriminate).
  subst len ad_len. simpl orb. clear PN PN0 PN1.
  forward_call (v_key, 32, Tsh). Intros kz.
  forward_call (v_xnonce, 24, Tsh). Intros nz.
  forward_call tt. Intros nonce.
  rewrite !aefu_bytes by auto.
  set (k := map Byte.repr kz). set (n := map Byte.repr nz).
  assert (Hk: Zlength k = 32) by (subst k; rewrite Zlength_map; auto).
  assert (Hn: Zlength n = 24) by (subst n; rewrite Zlength_map; auto).
  rewrite (aefu_split_bytes Ews m (Vptr b i)), (aefu_split_bytes Ews a (Vptr b0 i0)). Intros.
  destruct WgNoise.proof.aead.aead_models_props3.aead_models_ok3 as [AP XP].
  (* encrypt with either AEAD: sealed holds some len + 16 bytes; the message is no longer used *)
  match goal with |- semax _ (PROPx _ (LOCALx ?Q _)) _ _ =>
  forward_if (EX bs: list byte,
    PROPx [Zlength bs = Zlength m + 16] (LOCALx Q (SEPx [
      data_at Tsh (tarray tuchar 24) (map Vubyte n) v_xnonce;
      data_at Tsh (tarray tuchar 32) (map Vubyte k) v_key; mem_mgr gv;
      data_at Ews (tarray tuchar (Zlength m + 16)) (map Vubyte bs) (Vptr b1 i1);
      prim_bytes Ews a (Vptr b0 i0); zero_page gv; TT; has_ext tt])))
  end.
  { forward_call (Ews, Vptr b1 i1, Ews, Vptr b i, m, Ews, Vptr b0 i0, a, Tsh, v_xnonce, n, Tsh, v_key, k, gv).
    Exists (xaead_enc k n a m). entailer!. apply (xaead_enc_length _ _ XP). }
  { forward_call (Ews, Vptr b1 i1, Ews, Vptr b i, m, Ews, Vptr b0 i0, a, nonce, Tsh, v_key, k, gv).
    Exists (aead_enc k nonce a m). entailer!. apply (aead_enc_length _ _ AP). }
  Intros bs.
  (* the loop changes any bytes of sealed to any values: it holds some len + 16 bytes *)
  match goal with |- semax _ (PROPx _ (LOCALx ?Q _)) _ _ =>
  pose (Inv := EX bs: list byte,
    PROPx [Zlength bs = Zlength m + 16] (LOCALx Q (SEPx [
      data_at Tsh (tarray tuchar 24) (map Vubyte n) v_xnonce;
      data_at Tsh (tarray tuchar 32) (map Vubyte k) v_key; mem_mgr gv;
      data_at Ews (tarray tuchar (Zlength m + 16)) (map Vubyte bs) (Vptr b1 i1);
      prim_bytes Ews a (Vptr b0 i0); zero_page gv; TT; has_ext tt])))
  end.
  forward_loop Inv break: Inv; subst Inv.
  { Exists bs. entailer!. }
  { clear dependent bs. Intros bs.
    forward_call tt. Intros c.
    forward_if; [| forward; Exists bs; entailer! ].
    forward_call (Zlength m + 16 - 1). Intros j.
    forward_call tt. Intros v.
    forward.
    Exists (upd_Znth j bs (Byte.repr v)). rewrite aefu_store_byte by lia.
    entailer!. rewrite upd_Znth_Zlength by lia. auto. }
  Intros bs'. clear dependent bs.
  (* given: any prefix length; out_len = max(given - 16, 0) *)
  forward_call (Zlength m + 16). Intros g.
  forward_if (temp C._t'14 (Vlong (Int64.repr (Z.max 0 (g - 16)))));
    [ rewrite !Int64.unsigned_repr in * by rep_lia; forward; entailer!; rewrite Z.max_l by lia; reflexivity
    | rewrite !Int64.unsigned_repr in * by rep_lia; forward; entailer!; rewrite Z.max_r by lia; reflexivity | ].
  forward.
  (* ciphertext: the first given bytes of sealed; out: any out_len bytes *)
  rewrite <- H11.
  forward_call (Ews, Vptr b1 i1, bs', g, gv). Intros ct.
  forward_call (Z.max 0 (g - 16), gv). Intros vo. destruct vo as [out o]. simpl fst in *; simpl snd in *.
  match goal with Ho: Zlength o = _ |- _ => rewrite <- Ho end.
  aefu_case ct bc; aefu_case out bo; Intros.
  all: forward_if (temp C._t'17 (Vint (if orb bc bo then Int.one else Int.zero))); [aefu_branch | aefu_branch | ].
  all: forward_if (bc = false /\ bo = false);
    [ first [contradiction | discriminate | (forward; cancel)]
    | first [contradiction | discriminate | (forward; entailer!)] | ].
  all: Intros; subst bc bo.
  all: try (repeat match goal with H: _ /\ _ |- _ => destruct H end; discriminate).
  clear PN PN0.
  (* before: a copy of out *)
  forward_call (Ews, Vptr b3 i3, o, Zlength o, gv). Intros bf.
  rewrite sublist_same by auto.
  aefu_case bf bb; Intros.
  all: forward_if (bb = false);
    [ first [contradiction | discriminate | (forward; cancel)]
    | first [contradiction | discriminate | (forward; entailer!)] | ].
  all: Intros; subst bb.
  all: try discriminate.
  clear PN.
  (* decrypt the prefix with the AEAD chosen: on failure, out is as it was *)
  set (c := sublist 0 g bs').
  assert (Hc: Zlength c = g) by (subst c; rewrite Zlength_sublist by lia; lia).
  assert (Ec: data_at Ews (tarray tuchar g) (map Vubyte c) (Vptr b2 i2) =
              data_at Ews (tarray tuchar (Zlength c)) (map Vubyte c) (Vptr b2 i2)) by (rewrite Hc; reflexivity).
  assert (Eo: data_at Ews (tarray tuchar (Zlength o)) (map Vubyte o) (Vptr b3 i3) =
              data_at Ews (tarray tuchar (Zlength (map Vubyte o))) (map Vubyte o) (Vptr b3 i3))
    by (rewrite Zlength_map; reflexivity).
  assert (Eol: Zlength (map Vubyte o) = Z.max 0 (Zlength c - 16)) by (rewrite Zlength_map, Hc; auto).
  rewrite Ec, Eo, (aefu_split_out Ews (map Vubyte o)), (aefu_split_bytes Ews c). Intros.
  match goal with |- semax _ (PROPx _ (LOCALx ?Q _)) _ _ =>
  forward_if (EX r: bool, EX w: list val,
    PROPx [r = false -> w = map Vubyte o] (LOCALx (temp C._ok (Val.of_bool r) :: Q) (SEPx [
      prim_out Ews w (Vptr b3 i3);
      if Z.eq_dec (Zlength (map Vubyte o)) 0
      then data_at Ews (tarray tuchar (Zlength (map Vubyte o))) (map Vubyte o) (Vptr b3 i3) else emp;
      data_at Ews (tarray tuchar (Zlength o)) (map Vubyte o) (Vptr b4 i4);
      data_at Tsh (tarray tuchar 24) (map Vubyte n) v_xnonce;
      data_at Tsh (tarray tuchar 32) (map Vubyte k) v_key; TT; has_ext tt])))
  end.
  - forward_call (Ews, Vptr b3 i3, map Vubyte o, Ews, Vptr b2 i2, c, Ews, Vptr b0 i0, a, Tsh, v_xnonce, n,
                  Tsh, v_key, k, gv).
    { entailer!. rewrite Hc. reflexivity. }
    forward.
    Exists (match xaead_dec k n a c with Some _ => true | None => false end)
           (match xaead_dec k n a c with Some pt => map Vubyte pt | None => map Vubyte o end).
    entailer!.
    destruct (xaead_dec k n a c); split; try reflexivity; intros; congruence.
  - forward_call (Ews, Vptr b3 i3, map Vubyte o, Ews, Vptr b2 i2, c, Ews, Vptr b0 i0, a, nonce, Tsh, v_key, k, gv).
    { entailer!. rewrite Hc. reflexivity. }
    forward.
    Exists (match aead_dec k nonce a c with Some _ => true | None => false end)
           (match aead_dec k nonce a c with Some pt => map Vubyte pt | None => map Vubyte o end).
    entailer!.
    destruct (aead_dec k nonce a c); split; try reflexivity; intros; congruence.
  - Intros r w.
    (* the check: when the decryption failed, out still holds o, the bytes before holds *)
    forward_if (PROP () LOCAL (lvar C._xnonce (tarray tuchar 24) v_xnonce; lvar C._key (tarray tuchar 32) v_key)
      SEP (data_at Tsh (tarray tuchar 24) (map Vubyte n) v_xnonce;
           data_at Tsh (tarray tuchar 32) (map Vubyte k) v_key; TT)).
    + destruct r; [ discriminate | ].
      match goal with Hw: false = false -> _ |- _ => rewrite Hw by reflexivity end.
      sep_apply (derives_refl' _ _ (eq_sym (aefu_split_out Ews (map Vubyte o) (Vptr b3 i3)))).
      assert (Em: forall p, data_at Ews (tarray tuchar (Zlength o)) (map Vubyte o) p =
                  data_at Ews (tarray tuchar (Zlength (map Vubyte o))) (map Vubyte o) p)
        by (intros; rewrite Zlength_map; reflexivity).
      rewrite !Em.
      forward_call (Ews, Vptr b3 i3, map Vubyte o, o, Ews, Vptr b4 i4, map Vubyte o, o, Zlength o).
      { split; apply sublist_same; rewrite ?Zlength_map; auto. }
      destruct (list_eq_dec Byte.eq_dec o o) as [_|NE]; [| congruence].
      forward_call Int.one.
      entailer!.
    + destruct r; [ | discriminate ].
      forward. entailer!.
    + forward.
      sep_apply (data_at_data_at_ Tsh (tarray tuchar 32)). sep_apply (data_at_data_at_ Tsh (tarray tuchar 24)).
      cancel.
Qed.
