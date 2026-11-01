(* law consume_response_any: main's initial globals. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_defs.
Require WgNoise.contracts.x_consume_response_any.

#[local] Existing Instance W_consume_response_any.
Local Open Scope logic.

(* the refcount_t warnings start at zero (the initial global as VST's process_globals gives it, at the world) *)
Lemma hcr5_glob_refwarn4 {cs: compspecs} {CCE: change_composite_env Noise.CS cs} (gv: globals) (i: ident) :
  i = _wg_shim_refcount_warn ->
  @data_at cs Ews (tarray tulong 5) (Zrepeat (Vlong Int64.zero) 5) (gv i) |-- refwarn4 gv hcr5_w0.
Proof.
  intros ->. unfold refwarn4, hcr5_w0.
  rewrite prop_true_andp by reflexivity.
  assert (E: @data_at Noise.CS Ews (tarray tulong 5) (map Vlong (repeat Int64.zero 5)) =
             @data_at cs Ews (tarray tulong 5) (Zrepeat (Vlong Int64.zero) 5)).
  { apply data_at_change_composite; [apply JMeq_refl | reflexivity]. }
  rewrite <- E. apply derives_refl.
Qed.

(* sigma (u8 [10][16]) seen as a flat byte array: globvar2pred ignores gvar_info, and process_globals hangs on
   2-D arrays *)
Definition hcr5_glob_flat (x: ident * globdef (fundef function) type) : ident * globdef (fundef function) type :=
  match x with
  | (i, Gvar v) =>
    match gvar_info v with
    | Tarray (Tarray _ _ _) _ _ =>
        (i, Gvar (mkglobvar (tarray tuchar 160) (gvar_init v) (gvar_readonly v) (gvar_volatile v)))
    | _ => x
    end
  | _ => x
  end.

Definition hcr5_glob_vardefs :=
  ltac:(let x := eval vm_compute in (map hcr5_glob_flat (Vardefs WgNoise.contracts.x_consume_response_any.whole_prog)) in exact x).

Lemma hcr5_glob_InitGPred_flat gv :
  InitGPred (Vardefs WgNoise.contracts.x_consume_response_any.whole_prog) gv = InitGPred hcr5_glob_vardefs gv.
Proof. reflexivity. Qed.

Lemma hcr5_glob_sigma_flat {cs: compspecs} sh p :
  @data_at cs sh (tarray tuchar 160) (concat blake2s_sigma_val) p =
  @data_at cs sh (tarray (tarray tuchar 16) 10) blake2s_sigma_val p.
Proof.
  rewrite (data_at_2darray_concat sh tuchar 10 16); [reflexivity | reflexivity | | reflexivity].
  repeat constructor.
Qed.

(* a 32-byte array initialized by one byte and 31 zero bytes (Init_int8; Init_space 31) *)
Lemma hcr5_glob_pt {cs: compspecs} gv i sh (v: val) :
  globals_ok gv -> readable_share sh ->
  mapsto sh tuchar (gv i) v * mapsto_zeros 31 sh (offset_val 1 (gv i)) |--
  data_at sh (tarray tuchar 32) (v :: Zrepeat (Vint Int.zero) 31) (gv i).
Proof.
  intros Hgv Hsh.
  assert_PROP (isptr (gv i)) by (sep_apply mapsto_local_facts; entailer!).
  destruct (Hgv i) as [[b Hb] | Hu]; [| rewrite Hu in *; contradiction].
  rewrite Hb in *.
  rewrite (split2_data_at_Tarray_app 1 32 sh tuchar [v] (Zrepeat (Vint Int.zero) 31)) by reflexivity.
  rewrite (data_at_singleton_array_eq sh tuchar v [v]) by reflexivity.
  assert (FC: field_compatible (tarray tuchar 32) [] (Vptr b Ptrofs.zero)).
  { apply headptr_field_compatible; [exists b; auto | reflexivity | simpl; auto | simpl; rep_lia | ].
    apply align_compatible_rec_Tarray; intros. eapply align_compatible_rec_by_value; [reflexivity |].
    apply Z.divide_1_l. }
  rewrite field_address0_offset by auto with field_compatible.
  assert (FC1: field_compatible tuchar [] (Vptr b Ptrofs.zero)).
  { apply headptr_field_compatible; [exists b; auto | reflexivity | simpl; auto | simpl; rep_lia | ].
    eapply align_compatible_rec_by_value; [reflexivity |]. apply Z.divide_1_l. }
  rewrite <- (mapsto_data_at' sh tuchar v v) by auto. apply sepcon_derives; [apply derives_refl |].
  unfold data_at, field_at, at_offset. simpl nested_field_type. simpl nested_field_offset.
  change (offset_val 0 (offset_val 1 (Vptr b Ptrofs.zero))) with (Vptr b (Ptrofs.repr 1)).
  change (offset_val 1 (Vptr b Ptrofs.zero)) with (Vptr b (Ptrofs.repr 1)).
  rewrite prop_true_andp.
  2:{ split3; [exact I | reflexivity |]. split3.
      - unfold size_compatible. change (Ptrofs.unsigned (Ptrofs.repr 1)) with 1. simpl. rep_lia.
      - hnf. change (Ptrofs.unsigned (Ptrofs.repr 1)) with 1. constructor. intros.
        eapply align_compatible_rec_by_value; [reflexivity |]. apply Z.divide_1_l.
      - simpl. auto. }
  replace (Zrepeat (Vint Int.zero) 31) with (zero_val (tarray tuchar 31))
    by (rewrite zero_val_tarray; unfold tuchar; rewrite zero_val_Tint; reflexivity).
  apply (mapsto_zeros_data_at_rec_zero_val sh Hsh (tarray tuchar 31) b 1);
    [reflexivity | simpl; rep_lia | | reflexivity].
  constructor. intros. eapply align_compatible_rec_by_value; [reflexivity |]. apply Z.divide_1_l.
Qed.

(* keypair_counter (struct __gp_atomic64_t, initialized by one Init_int64) *)
Lemma hcr5_glob_atomic gv i sh (z: int64) :
  globals_ok gv ->
  mapsto sh tulong (gv i) (Vlong z) |-- @data_at Noise.CS sh t_atomic64 (Vlong z) (gv i).
Proof.
  intros Hgv.
  assert_PROP (isptr (gv i)) by (sep_apply mapsto_local_facts; entailer!).
  destruct (Hgv i) as [[b Hb] | Hu]; [| rewrite Hu in *; contradiction].
  rewrite Hb in *.
  unfold_data_at (data_at _ _ _ _).
  assert (FC: @field_compatible Noise.CS t_atomic64 [] (Vptr b Ptrofs.zero)).
  { apply headptr_field_compatible; [exists b; auto | reflexivity | simpl; auto | simpl; rep_lia | ].
    eapply align_compatible_rec_Tstruct; [reflexivity | reflexivity | ].
    intros i0 t0 z0 H0 H1. simpl in H0, H1. if_tac in H0; [ | discriminate]. inv H0. inv H1.
    eapply align_compatible_rec_by_value; [reflexivity |]. apply Z.divide_0_r. }
  rewrite field_at_data_at. rewrite field_address_offset by auto with field_compatible.
  simpl nested_field_type.
  change (nested_field_offset t_atomic64 (DOT noise.code._counter)) with 0.
  change (offset_val 0 (Vptr b Ptrofs.zero)) with (Vptr b Ptrofs.zero).
  rewrite <- (mapsto_data_at' sh tlong (Vlong z) (Vlong z)); auto.
  2: { apply headptr_field_compatible; [exists b; auto | reflexivity | simpl; auto | simpl; rep_lia | ].
       eapply align_compatible_rec_by_value; [reflexivity |]. apply Z.divide_0_r. }
  apply derives_refl.
Qed.

#[local] Instance hcr5_glob_cceN : change_composite_env Noise.CS W_consume_response_any.
Proof. make_cs_preserve Noise.CS W_consume_response_any. Defined.
#[local] Instance hcr5_glob_cceH : change_composite_env HCS W_consume_response_any.
Proof. make_cs_preserve HCS W_consume_response_any. Defined.
#[local] Instance hcr5_glob_cceB : change_composite_env WgNoise.units.Blake2s.CS W_consume_response_any.
Proof. make_cs_preserve WgNoise.units.Blake2s.CS W_consume_response_any. Defined.

(* one global of the processed list against one of the target: same object, values equal by computation *)
Lemma hcr5_glob_eq sh t t' (v: reptype t) (v': reptype t') p p' :
  t = t' -> JMeq v v' -> p = p' -> data_at sh t v p |-- data_at sh t' v' p'.
Proof. intros -> E ->. apply JMeq_eq in E. subst. apply derives_refl. Qed.

Ltac hcr5_glob_vals :=
  vm_compute;
  repeat match goal with
  | |- ?a = ?a => reflexivity
  | |- cons _ _ = cons _ _ => f_equal
  | |- Vint _ = Vint _ => f_equal; apply Int.mkint_eq; reflexivity
  | |- Vlong _ = Vlong _ => f_equal; apply Int64.mkint_eq; reflexivity
  end.

Ltac hcr5_glob_jmeq :=
  match goal with |- JMeq ?a ?b =>
    let E := fresh in assert (E: a = b) by hcr5_glob_vals; rewrite E; apply JMeq_refl end.

(* turn the processed global at the target's address into the target's form *)
Ltac hcr5_glob_match gv :=
  match goal with |- ?L |-- ?R =>
    match R with context [@data_at W_consume_response_any ?sh' ?t' ?v' (gv ?i')] =>
      lazymatch L with context [@data_at W_consume_response_any sh' t' v' (gv i')] => fail | _ => idtac end;
      let j := eval compute in i' in
      match L with context [@data_at W_consume_response_any ?sh ?t ?v (gv j)] =>
        sep_apply (hcr5_glob_eq sh t t' v v' (gv j) (gv i') eq_refl ltac:(hcr5_glob_jmeq) eq_refl)
      end
    end
  end.

(* the globals of the whole program, as main's precondition gives them (InitGPred, at the world), contain
   the shim's globals (all zero), noise.c's globals (handshake_name, identifier_name: their strings; the
   initial hash, chaining key, keypair_counter, zero_point: zero), the read-only tables of the primitives
   and cookie.c (wg_consts) and the harness's constants; the rest goes to TT *)
Lemma hcr5_init_globals gv :
  globals_ok gv ->
  InitGPred (Vardefs WgNoise.contracts.x_consume_response_any.whole_prog) gv |--
  (shim_state4 gv hcr5_shim0 hcr5_w0 * noise_globals_raw gv zeros32 zeros32 Int64.zero * wg_consts gv *
   hcr5_consts gv * TT)%logic.
Proof.
  intros Hgv. rewrite hcr5_glob_InitGPred_flat.
  change (InitGPred hcr5_glob_vardefs gv |-- (fun g => shim_state4 g hcr5_shim0 hcr5_w0 * noise_globals_raw g zeros32 zeros32 Int64.zero * wg_consts g *
   hcr5_consts g * TT)%logic gv).
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
  repeat match goal with |- context [mapsto_zeros 31 ?sh (offset_val 1 (gv ?i))] =>
    match goal with |- context [mapsto sh tuchar (gv i) ?v] =>
      sep_apply (hcr5_glob_pt gv i sh v Hgv readable_Ers) end end.
  match goal with |- context [mapsto ?sh tulong (gv ?i) (Vlong ?z)] =>
    sep_apply (hcr5_glob_atomic gv i sh z Hgv) end.
  match goal with |- context [data_at ?sh (tarray tuchar 160) ?l ?p] =>
    replace l with (concat blake2s_sigma_val) by (vm_compute; reflexivity) end.
  rewrite hcr5_glob_sigma_flat.
  unfold shim_state4, shim_core, noise_globals_raw, wg_consts, cookie_globals, hcr5_consts, hc_const, blake2s_globals,
    curve25519_globals, zero_page.
  rewrite (prop_true_andp (shim_ok hcr5_shim0)) by (split; reflexivity).
  rewrite (prop_true_andp (Zlength zeros32 = 32 /\ _)) by (split; reflexivity).
  repeat match goal with |- context [@data_at ?cs ?sh ?t ?v] =>
    lazymatch cs with W_consume_response_any => fail | _ => idtac end;
    rewrite (@data_at_change_composite cs W_consume_response_any _ sh t v v (JMeq_refl v)) by prove_cs_preserve_type
  end.
  autorewrite with zero_val.
  replace (zero_val tuchar) with (Vint Int.zero) by (unfold tuchar; rewrite zero_val_Tint; reflexivity).
  repeat hcr5_glob_match gv.
  sep_apply (hcr5_glob_refwarn4 (cs := W_consume_response_any) gv _ eq_refl).
  cancel.
Qed.
