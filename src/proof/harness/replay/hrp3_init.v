(* law replay: the initial globals of main (main_pre's InitGPred of the whole program): the shim's
   (all zero: hrp3_S0), noise.c's (before wg_noise_init), the read-only tables of the primitives and cookie.c
   (wg_consts), the three renamed common.h constants (hrp3_consts); the rest is dropped into TT.
   Worked examples: law prim_aead's hm3_init_globals,
   law prim_blake2s's main.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.protocol.prot_prog3.
Require Import WgNoise.proof.harness.common.hc_prog3.
Require Import WgNoise.proof.harness.replay.hrp3_spec.
Require Import WgNoise.proof.harness.replay.hrp3_model.
Require Import WgNoise.proof.harness.replay.hrp3_defs.
Require WgNoise.contracts.x_replay.
Require WgNoise.harness.x_replay.code.
Require Import WgNoise.proof.protocol.prot3_refwarn.

#[local] Existing Instance W_replay.
Local Open Scope Z_scope.

Definition hrp3i_vardefs :=
  ltac:(let x := eval vm_compute in (Vardefs WgNoise.contracts.x_replay.whole_prog) in exact x).

Lemma hrp3i_vardefs_eq : Vardefs WgNoise.contracts.x_replay.whole_prog = hrp3i_vardefs.
Proof. vm_compute. reflexivity. Qed.

(* blake2s_sigma (u8 [10][16]) seen as a flat byte array (globvar2pred ignores gvar_info) *)
Definition hrp3i_flat (x: ident * globdef (fundef function) type) : ident * globdef (fundef function) type :=
  match x with
  | (i, Gvar v) =>
    if Pos.eqb i WgNoise.blake2s.code._blake2s_sigma
    then (i, Gvar (mkglobvar (tarray tuchar 160) (gvar_init v) (gvar_readonly v) (gvar_volatile v)))
    else x
  | _ => x
  end.

Definition hrp3i_vardefs_flat :=
  ltac:(let x := eval vm_compute in (map hrp3i_flat hrp3i_vardefs) in exact x).

Lemma hrp3i_InitGPred_flat gv : InitGPred hrp3i_vardefs gv = InitGPred hrp3i_vardefs_flat gv.
Proof. reflexivity. Qed.

Lemma hrp3i_sigma_flat {cs: compspecs} sh p :
  @data_at cs sh (tarray tuchar 160) (concat WgNoise.proof.blake2s.spec.blake2s_sigma_val) p =
  @data_at cs sh (tarray (tarray tuchar 16) 10) WgNoise.proof.blake2s.spec.blake2s_sigma_val p.
Proof.
  rewrite (data_at_2darray_concat sh tuchar 10 16); [reflexivity | reflexivity | | reflexivity].
  repeat constructor.
Qed.

(* ---------------------------------------------------------------------- *)
(* Byte arrays and scalars are the same predicates in every compspecs     *)
(* ---------------------------------------------------------------------- *)

Lemma hrp3i_align_bv ce1 ce2 t ch z :
  access_mode t = By_value ch -> align_compatible_rec ce1 t z -> align_compatible_rec ce2 t z.
Proof.
  intros H A. apply (align_compatible_rec_by_value ce2 t ch z H).
  exact (align_compatible_rec_by_value_inv ce1 t ch z H A).
Qed.

Lemma hrp3i_align_tuchar ce n z : align_compatible_rec ce (tarray tuchar n) z.
Proof.
  apply align_compatible_rec_Tarray. intros.
  eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l].
Qed.

Lemma hrp3i_bytes_cs {cs1 cs2: compspecs} sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible, size_compatible, align_compatible.
  destruct p; simpl; try tauto.
  pose proof (hrp3i_align_tuchar (@cenv_cs cs1) n (Ptrofs.unsigned i)).
  pose proof (hrp3i_align_tuchar (@cenv_cs cs2) n (Ptrofs.unsigned i)).
  tauto.
Qed.

Lemma hrp3i_scalar_cs {cs1 cs2: compspecs} sh t ch (v: val) (v1: @reptype cs1 t) (v2: @reptype cs2 t) p :
  access_mode t = By_value ch -> type_is_volatile t = false ->
  (forall cs: compspecs, @sizeof cs t = size_chunk ch) ->
  (forall cs: compspecs, @complete_legal_cosu_type (@cenv_cs cs) t = true) ->
  JMeq v v1 -> JMeq v v2 ->
  @data_at cs1 sh t v1 p = @data_at cs2 sh t v2 p.
Proof.
  intros Hm Hv Hs Hc J1 J2.
  assert (Hbv: type_is_by_value t = true) by (destruct t; inversion Hm; reflexivity).
  assert (Hfc: @field_compatible cs1 t nil p <-> @field_compatible cs2 t nil p).
  { unfold field_compatible, size_compatible, align_compatible.
    rewrite (Hs cs1), (Hs cs2), (Hc cs1), (Hc cs2).
    destruct p; try tauto.
    split; intros (? & ? & ? & ? & ?); (split; [| split; [| split; [| split]]]); auto;
      (match goal with A: align_compatible_rec _ _ _ |- _ => exact (hrp3i_align_bv _ _ t ch _ Hm A) end). }
  apply pred_ext.
  - eapply derives_trans; [apply andp_right; [apply (@data_at_local_facts cs1) | apply derives_refl] |].
    apply derives_extract_prop; intros [Hf _].
    rewrite <- (@mapsto_data_at' cs1 sh t v v1 p) by auto.
    rewrite (@mapsto_data_at' cs2 sh t v v2 p) by (auto; apply Hfc; auto).
    apply derives_refl.
  - eapply derives_trans; [apply andp_right; [apply (@data_at_local_facts cs2) | apply derives_refl] |].
    apply derives_extract_prop; intros [Hf _].
    rewrite <- (@mapsto_data_at' cs2 sh t v v2 p) by auto.
    rewrite (@mapsto_data_at' cs1 sh t v v1 p) by (auto; apply Hfc; auto).
    apply derives_refl.
Qed.

(* a 32-byte array initialised { b, 0... }: process_globals gives its first byte and 31 zero bytes *)
Lemma hrp3i_point {cs: compspecs} sh v p :
  readable_share sh -> headptr p ->
  (mapsto sh tuchar p v * mapsto_zeros 31 sh (offset_val 1 p))%logic
  |-- data_at sh (tarray tuchar 32) (v :: Zrepeat (Vint Int.zero) 31) p.
Proof.
  intros Hsh Hp. destruct Hp as [b ->].
  change (v :: Zrepeat (Vint Int.zero) 31) with ([v] ++ Zrepeat (Vint Int.zero) 31).
  rewrite (split2_data_at_Tarray_app 1 32) by reflexivity.
  rewrite (data_at_singleton_array_eq sh tuchar v) by reflexivity.
  apply sepcon_derives.
  - rewrite (mapsto_data_at' sh tuchar v v); [apply derives_refl | reflexivity | reflexivity | | apply JMeq_refl].
    unfold field_compatible; simpl; repeat split; auto.
    apply align_compatible_rec_by_value with Mint8unsigned; [reflexivity | apply Z.divide_1_l].
  - rewrite field_address0_offset by
      (unfold field_compatible0; simpl; repeat split; auto; try rep_lia; apply hrp3i_align_tuchar).
    simpl offset_val.
    replace (Zrepeat (Vint Int.zero) 31) with (zero_val (tarray tuchar (32 - 1)))
      by (rewrite zero_val_tarray, zero_val_eq; reflexivity).
    apply (mapsto_zero_data_at_zero (tarray tuchar (32 - 1))); auto.
    unfold field_compatible; simpl; repeat split; auto; try rep_lia; apply hrp3i_align_tuchar.
Qed.

(* noise.c's keypair_counter (struct { s64 counter; } = 0): process_globals gives one u64 *)
Lemma hrp3i_atomic sh v p :
  headptr p ->
  mapsto sh tulong p v |-- @data_at Noise.CS sh t_atomic64 v p.
Proof.
  intros Hp. assert (FC: @field_compatible Noise.CS t_atomic64 [] p).
  { apply headptr_field_compatible; auto; try reflexivity; try (simpl; rep_lia).
    eapply align_compatible_rec_Tstruct; [reflexivity | reflexivity |].
    intros i0 t0 z0 H1 H2. simpl in H1. destruct (ident_eq i0 noise.code._counter); [| discriminate].
    subst i0. injection H1 as <-. vm_compute in H2. injection H2 as <-.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_0_r]. }
  unfold_data_at (@data_at Noise.CS _ _ _ _).
  rewrite field_at_data_at. rewrite field_address_offset by auto with field_compatible.
  simpl nested_field_type.
  change (nested_field_offset t_atomic64 (DOT noise.code._counter)) with 0.
  destruct Hp as [b ->]. rewrite isptr_offset_val_zero by exact I.
  rewrite <- (mapsto_data_at' sh tlong v v); [| reflexivity | reflexivity | | apply JMeq_refl].
  - unfold mapsto. simpl. apply derives_refl.
  - destruct FC as (? & ? & ? & ? & ?). repeat split; auto; simpl; try rep_lia.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_0_r].
Qed.

Lemma hrp3i_point_gv {cs: compspecs} gv sh v i :
  globals_ok gv -> readable_share sh ->
  (mapsto sh tuchar (gv i) v * mapsto_zeros 31 sh (offset_val 1 (gv i)))%logic
  |-- data_at sh (tarray tuchar 32) (v :: Zrepeat (Vint Int.zero) 31) (gv i).
Proof.
  intros G Hsh. destruct (G i) as [H | H]; [apply hrp3i_point; auto |].
  rewrite H. unfold mapsto. simpl. rewrite FF_sepcon. apply FF_left.
Qed.

Lemma hrp3i_atomic_gv gv sh v i :
  globals_ok gv -> mapsto sh tulong (gv i) v |-- @data_at Noise.CS sh t_atomic64 v (gv i).
Proof.
  intros G. destruct (G i) as [H | H]; [apply hrp3i_atomic; auto |].
  rewrite H. unfold mapsto. simpl. apply FF_left.
Qed.

(* one global of process_globals' form |-- the same global as the specifications state it *)
Lemma hrp3i_bytes_conv {cs1 cs2: compspecs} sh n1 n2 (v1 v2: list val) p1 p2 :
  n1 = n2 -> v1 = v2 -> p1 = p2 ->
  @data_at cs1 sh (tarray tuchar n1) v1 p1 |-- @data_at cs2 sh (tarray tuchar n2) v2 p2.
Proof. intros <- <- <-. rewrite (@hrp3i_bytes_cs cs1 cs2). apply derives_refl. Qed.

Lemma hrp3i_ulong_conv {cs1 cs2: compspecs} sh (v1 v2: val) p1 p2 :
  v1 = v2 -> p1 = p2 -> @data_at cs1 sh tulong v1 p1 |-- @data_at cs2 sh tulong v2 p2.
Proof.
  intros <- <-. erewrite (@hrp3i_scalar_cs cs1 cs2 sh tulong Mint64 v1 v1 v1);
    try reflexivity; try apply JMeq_refl; apply derives_refl.
Qed.

Lemma hrp3i_long_conv {cs1 cs2: compspecs} sh (v1 v2: val) p1 p2 :
  v1 = v2 -> p1 = p2 -> @data_at cs1 sh tlong v1 p1 |-- @data_at cs2 sh tlong v2 p2.
Proof.
  intros <- <-. erewrite (@hrp3i_scalar_cs cs1 cs2 sh tlong Mint64 v1 v1 v1);
    try reflexivity; try apply JMeq_refl; apply derives_refl.
Qed.

Lemma hrp3i_uint_conv {cs1 cs2: compspecs} sh (v1 v2: val) p1 p2 :
  v1 = v2 -> p1 = p2 -> @data_at cs1 sh tuint v1 p1 |-- @data_at cs2 sh tuint v2 p2.
Proof.
  intros <- <-. erewrite (@hrp3i_scalar_cs cs1 cs2 sh tuint Mint32 v1 v1 v1);
    try reflexivity; try apply JMeq_refl; apply derives_refl.
Qed.

Lemma hrp3i_bool_conv {cs1 cs2: compspecs} sh (v1 v2: val) p1 p2 :
  v1 = v2 -> p1 = p2 -> @data_at cs1 sh tbool v1 p1 |-- @data_at cs2 sh tbool v2 p2.
Proof.
  intros <- <-. erewrite (@hrp3i_scalar_cs cs1 cs2 sh tbool Mbool v1 v1 v1);
    try reflexivity; try apply JMeq_refl; apply derives_refl.
Qed.

Lemma hrp3i_atomic_conv sh (v1 v2: val) p1 p2 :
  v1 = v2 -> p1 = p2 -> @data_at Noise.CS sh t_atomic64 v1 p1 |-- @data_at Noise.CS sh t_atomic64 v2 p2.
Proof. intros <- <-. apply derives_refl. Qed.

(* process_globals' zero values *)
Lemma hrp3i_zv_ulong {cs: compspecs} : @zero_val cs (Tlong Unsigned noattr) = Vlong Int64.zero.
Proof. rewrite zero_val_eq. reflexivity. Qed.
Lemma hrp3i_zv_long {cs: compspecs} : @zero_val cs (Tlong Signed noattr) = Vlong Int64.zero.
Proof. rewrite zero_val_eq. reflexivity. Qed.
Lemma hrp3i_zv_uint {cs: compspecs} : @zero_val cs (Tint I32 Unsigned noattr) = Vint Int.zero.
Proof. rewrite zero_val_eq. reflexivity. Qed.
Lemma hrp3i_zv_bool {cs: compspecs} : @zero_val cs (Tint IBool Unsigned noattr) = Vint Int.zero.
Proof. rewrite zero_val_eq. reflexivity. Qed.
Lemma hrp3i_zv_bytes {cs: compspecs} n : @zero_val cs (tarray tuchar n) = Zrepeat (Vint Int.zero) n.
Proof. rewrite zero_val_tarray, (zero_val_eq tuchar). reflexivity. Qed.

(* two concrete values / lists of values *)
Ltac hrp3i_vals :=
  vm_compute;
  repeat match goal with
  | |- cons _ _ = cons _ _ => f_equal
  | |- Vint _ = Vint _ => f_equal; apply Int.mkint_eq; reflexivity
  | |- Vlong _ = Vlong _ => f_equal; apply Int64.mkint_eq; reflexivity
  end;
  try reflexivity.

Ltac hrp3i_atom :=
  first
  [ apply hrp3i_bytes_conv; [vm_compute; reflexivity | hrp3i_vals | reflexivity]
  | apply hrp3i_ulong_conv; [hrp3i_vals | reflexivity]
  | apply hrp3i_long_conv; [hrp3i_vals | reflexivity]
  | apply hrp3i_uint_conv; [hrp3i_vals | reflexivity]
  | apply hrp3i_bool_conv; [hrp3i_vals | reflexivity]
  | apply hrp3i_atomic_conv; [hrp3i_vals | reflexivity] ].

(* turn the LHS global at the address of some RHS global into that RHS global *)
Ltac hrp3i_step gv :=
  match goal with |- ?L |-- ?R =>
    match R with context [@data_at ?cs2 ?sh ?t2 ?v2 (gv ?i)] =>
      let B := constr:(@data_at cs2 sh t2 v2 (gv i)) in
      lazymatch L with context [B] => fail | _ => idtac end;
      let j := eval vm_compute in i in
      match L with context [@data_at ?cs1 ?sh1 ?t1 ?v1 (gv j)] =>
        let H := fresh "H" in
        assert (H: @data_at cs1 sh1 t1 v1 (gv j) |-- B) by hrp3i_atom;
        sep_apply H; clear H
      end
    end
  end.

#[local] Instance hrp3i_cceN : change_composite_env Noise.CS W_replay.
Proof. make_cs_preserve Noise.CS W_replay. Defined.

Lemma hrp3_init_globals gv :
  globals_ok gv ->
  InitGPred (Vardefs WgNoise.contracts.x_replay.whole_prog) gv
  |-- (shim_state gv hrp3_S0 * noise_globals_raw gv zeros32 zeros32 Int64.zero * wg_consts gv *
       hrp3_consts gv * TT)%logic.
Proof.
  intros Hgv. rewrite hrp3i_vardefs_eq, hrp3i_InitGPred_flat.
  match goal with |- _ |-- ?P => change (InitGPred hrp3i_vardefs_flat gv |-- (fun g => P)%logic gv) end.
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
  do 3 match goal with |- context [mapsto ?sh tuchar (gv ?i) ?v] =>
    sep_apply (hrp3i_point_gv (cs := W_replay) gv sh v i Hgv ltac:(auto)) end.
  match goal with |- context [mapsto ?sh tulong (gv ?i) ?v] => sep_apply (hrp3i_atomic_gv gv sh v i Hgv) end.
  unfold shim_state, noise_globals_raw, wg_consts, cookie_globals, WgNoise.proof.blake2s.spec.blake2s_globals, curve25519_globals,
    zero_page, hrp3_consts, hc_const.
  rewrite !prop_true_andp by (hnf; split; reflexivity).
  rewrite <- (@hrp3i_sigma_flat Blake2s.CS).
  rewrite ?hrp3i_zv_ulong, ?hrp3i_zv_long, ?hrp3i_zv_uint, ?hrp3i_zv_bool, ?hrp3i_zv_bytes.
  do 3 hrp3i_step gv.
  do 3 hrp3i_step gv.
  do 3 hrp3i_step gv.
  do 3 hrp3i_step gv.
  do 3 hrp3i_step gv.
  do 3 hrp3i_step gv.
  do 3 hrp3i_step gv.
  do 3 hrp3i_step gv.
  repeat hrp3i_step gv.
  (* the refcount_t warnings start at zero (refwarn, part of shim_state) *)
  match goal with |- context [@data_at ?cs ?sh (tarray _ 5) ?v (gv ?i)] =>
    sep_apply (@prot3_refwarn_zero cs hrp3i_cceN gv i ltac:(vm_compute; reflexivity)) end.
  cancel.
Qed.
