(* Law ae_roundtrip: the body of main (harness/ae_roundtrip.c) against its specification, in the world
   W_ae_roundtrip.  After the inputs are drawn (a failed malloc returns 0), chacha20poly1305_encrypt writes
   aead_enc k nonce ad m into sealed, and chacha20poly1305_decrypt of those |m| + 16 bytes returns true and
   writes m into opened (aead_dec_enc of aead_models_props3.aead_models_ok3): both gp_assert get a nonzero
   argument. *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.aead.aead_spec3.
Require Import WgNoise.proof.harness.wg_laws.wl_spec.
Require Import WgNoise.proof.harness.ae_roundtrip.ae_roundtrip_world.
Require Import WgNoise.proof.harness.ae_roundtrip.ae_roundtrip_spec.
Require WgNoise.contracts.ae_roundtrip.
Require WgNoise.harness.ae_roundtrip.code.
Require WgNoise.proof.aead.aead_models_props3.
Require WgNoise.proof.harness.prim_aead.haead_main_body3_defs.

#[local] Existing Instance W_ae_roundtrip.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* The initial globals: keep the shim's zero page                          *)
(* ---------------------------------------------------------------------- *)

Definition ar_keep (x: ident * globdef (fundef function) type) : bool :=
  Pos.eqb (fst x) _quickproof_zero_page.

Definition ar_vardefs :=
  ltac:(let x := eval vm_compute in
    (filter ar_keep (Vardefs WgNoise.contracts.ae_roundtrip.whole_prog)) in exact x).

Lemma ar_vardefs_eq :
  filter ar_keep (Vardefs WgNoise.contracts.ae_roundtrip.whole_prog) = ar_vardefs.
Proof. vm_compute. reflexivity. Qed.

(* the initial globals of the whole program hold the zero page the AEAD reads *)
Lemma ar_init_globals gv :
  globals_ok gv ->
  InitGPred (Vardefs WgNoise.contracts.ae_roundtrip.whole_prog) gv |-- (zero_page gv * TT)%logic.
Proof.
  intros Hgv.
  eapply derives_trans; [apply (haead_main_body3_defs.hm3_InitGPred_filter ar_keep) |].
  rewrite ar_vardefs_eq. apply sepcon_derives; [| apply derives_refl].
  change (InitGPred ar_vardefs gv |-- (fun g => zero_page g)%logic gv).
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
(* Byte buffers and the AEAD's view of them                                *)
(* ---------------------------------------------------------------------- *)

(* nondet_bytes gives integers in byte range: they are the bytes map Byte.repr bs *)
Lemma ar_bytes bs : Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  map (fun b => Vint (Int.repr b)) bs = map Vubyte (map Byte.repr bs).
Proof.
  induction 1; simpl; f_equal; auto.
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

(* a byte buffer is the AEAD's input view (prim_bytes, emp when empty) and, when empty, the rest *)
Lemma ar_split_bytes sh m p :
  data_at sh (tarray tuchar (Zlength m)) (map Vubyte m) p =
  (prim_bytes sh m p *
   (if Z.eq_dec (Zlength m) 0 then data_at sh (tarray tuchar (Zlength m)) (map Vubyte m) p else emp))%logic.
Proof.
  unfold prim_bytes. destruct (Z.eq_dec (Zlength m) 0).
  - rewrite emp_sepcon. reflexivity.
  - rewrite sepcon_emp. reflexivity.
Qed.

(* main's postcondition (TT) weakened to the canonical form forward needs for a return *)
Lemma ar_post_canon {Espec: OracleKind} {cs: compspecs} Delta P c gv F :
  semax Delta P c (frame_ret_assert (function_body_ret_assert tint (PROP () LOCAL () SEP (TT))) F) ->
  semax Delta P c (frame_ret_assert (function_body_ret_assert tint (ar_post gv)) F).
Proof.
  intros H. eapply semax_post; [| | | | apply H]; intros; simpl; intros rho; apply andp_left2;
    try apply derives_refl.
  apply sepcon_derives; [| apply derives_refl]. revert rho. apply bind_ret_derives. intros rho. apply TT_right.
Qed.

(* Main's NULL test: case on each buffer (b = true: the buffer is NULL; otherwise a pointer Vptr) *)
Ltac ar_case p b :=
  let E := fresh "E" in let PN := fresh "PN" in
  assert_PROP (is_pointer_or_null p) as PN by entailer!;
  destruct (eq_dec p nullval) as [E|E];
  [ pose (b := true); subst p
  | pose (b := false); destruct p; try contradiction;
    try (simpl in PN; subst; exfalso; apply E; reflexivity) ].

(* a branch of one of the ||'s of the NULL test *)
Ltac ar_branch :=
  first [ contradiction | discriminate | idtac ];
  try (forward; entailer!; subst_any; simpl; auto).

Lemma ar_main_body :
  semax_body ar_V ar_Gmain WgNoise.harness.ae_roundtrip.code.f_main ar_main_spec.
Proof.
  unfold ar_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply (main_pre_InitGpred (zero_page gv * TT)%logic);
    [apply ar_init_globals | reflexivity
    | apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; subst x; vm_compute; exact I | ].
  process_stackframe_of.
  sep_apply (create_mem_mgr gv).
  cbv beta iota delta [fn_body WgNoise.harness.ae_roundtrip.code.f_main fn_return]. apply ar_post_canon. abbreviate_semax.
  forward_call (Int64.max_signed - 16). Intros len.
  forward_call Int64.max_signed. Intros ad_len.
  forward_call (len, gv). Intros vm. destruct vm as [message m]. simpl fst in *; simpl snd in *.
  forward_call (ad_len, gv). Intros va. destruct va as [ad a]. simpl fst in *; simpl snd in *.
  forward_call (tarray tuchar (len + 16), gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros sealed.
  forward_call (len, gv). Intros vo. destruct vo as [opened o]. simpl fst in *; simpl snd in *.
  (* the NULL test: in each of the 16 cases the three ||'s give 1 iff some buffer is NULL; then main
     returns 0, otherwise the run goes on with four pointers *)
  ar_case message bm; ar_case ad ba; ar_case sealed bs; ar_case opened bo; Intros.
  all: forward_if (temp WgNoise.harness.ae_roundtrip.code._t'7 (Vint (if orb bm ba then Int.one else Int.zero)));
    [ar_branch | ar_branch | ].
  all: forward_if (temp WgNoise.harness.ae_roundtrip.code._t'8 (Vint (if orb bm (orb ba bs) then Int.one else Int.zero)));
    [ar_branch | ar_branch | ].
  all: forward_if (temp WgNoise.harness.ae_roundtrip.code._t'9 (Vint (if orb bm (orb ba (orb bs bo)) then Int.one else Int.zero)));
    [ar_branch | ar_branch | ].
  all: forward_if (bm = false /\ ba = false /\ bs = false /\ bo = false);
    [ first [contradiction | discriminate | (forward; cancel)]
    | first [contradiction | discriminate | (forward; entailer!)] | ].
  all: Intros; subst bm ba bs bo.
  all: try (repeat match goal with H: _ /\ _ |- _ => destruct H end; discriminate).
  (* all four buffers are non-NULL: draw key and nonce, encrypt, decrypt, check *)
  subst len ad_len. simpl orb. clear PN PN0 PN1 PN2.
  forward_call (v_key, 32, Tsh). Intros kz.
  forward_call. Intros nonce.
  rewrite !ar_bytes by auto.
  set (k := map Byte.repr kz).
  assert (Hk: Zlength k = 32) by (subst k; rewrite Zlength_map; auto).
  rewrite (ar_split_bytes Ews m (Vptr b i)), (ar_split_bytes Ews a (Vptr b0 i0)). Intros.
  forward_call (Ews, Vptr b1 i1, Ews, Vptr b i, m, Ews, Vptr b0 i0, a, nonce, Tsh, v_key, k, gv).
  (* the round trip of the model *)
  destruct WgNoise.proof.aead.aead_models_props3.aead_models_ok3 as [X _].
  set (c := aead_enc k nonce a m).
  assert (Hc: Zlength c = Zlength m + 16) by apply (aead_enc_length _ _ X).
  assert (Hdec: aead_dec k nonce a c = Some m) by apply (aead_dec_enc _ _ X).
  assert (Eo: data_at Ews (tarray tuchar (Zlength m)) (map Vubyte o) (Vptr b2 i2) =
              data_at Ews (tarray tuchar (Zlength (map Vubyte o))) (map Vubyte o) (Vptr b2 i2))
    by (rewrite Zlength_map, H3; reflexivity).
  assert (Ec: data_at Ews (tarray tuchar (Zlength m + 16)) (map Vubyte c) (Vptr b1 i1) =
              data_at Ews (tarray tuchar (Zlength c)) (map Vubyte c) (Vptr b1 i1))
    by (rewrite Hc; reflexivity).
  rewrite Eo, Ec, (ar_split_bytes Ews c). Intros.
  forward_call (Ews, Vptr b2 i2, map Vubyte o, Ews, Vptr b1 i1, c, Ews, Vptr b0 i0, a, nonce,
                Tsh, v_key, k, gv).
  { entailer!. rewrite Hc. reflexivity. }
  { rewrite Zlength_map, H3, Hc. lia. }
  rewrite Hdec. simpl Val.of_bool.
  forward_call Int.one.
  sep_apply (derives_refl' _ _ (eq_sym (ar_split_bytes Ews m (Vptr b i)))).
  assert (Em: Zlength (map Vubyte o) = Zlength (map Vubyte m)) by (rewrite !Zlength_map; auto).
  rewrite Em.
  assert (Em': forall p, data_at Ews (tarray tuchar (Zlength m)) (map Vubyte m) p =
              data_at Ews (tarray tuchar (Zlength (map Vubyte m))) (map Vubyte m) p)
    by (intros; rewrite Zlength_map; reflexivity).
  rewrite !Em'.
  forward_call (Ews, Vptr b2 i2, map Vubyte m, m, Ews, Vptr b i, map Vubyte m, m, Zlength m).
  { rewrite Zlength_map, sublist_same by (rewrite ?Zlength_map; auto). repeat split; lia. }
  destruct (list_eq_dec Byte.eq_dec m m) as [_|NE]; [| congruence].
  forward_call Int.one.
  forward.
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 32)).
  cancel.
Qed.
