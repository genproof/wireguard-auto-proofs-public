(* Body proofs of the protocol piece, group shim_small.
   Target: prot_bodies3_shim_small.  Prove each function's body against its specification (prot_specs3.v) in the
   compspecs of its unit, with the context Gprot3 (prot_prog3.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_prog3.
Require Import WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.protocol.prot_body3_shim_rc.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

Section Bodies.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Shim.CS.
Local Open Scope logic.

Definition Gsh := Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS.

(* shim_state in the shim's compspecs (the representation is stated in Noise.CS) *)
Definition shim_state_S (gv: globals) (S: shim) : mpred :=
  !! shim_ok S &&
  (data_at Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
   data_at Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
   data_at Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
   data_at Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
   data_at Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
   data_at Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
   data_at Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   data_at Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
   data_at Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   data_at Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   data_at Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
   data_at Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow) *
   refwarn gv).

Lemma shim_state_S_eq gv S : shim_state gv S = shim_state_S gv S.
Proof.
  unfold shim_state, shim_state_S.
  f_equal.
  repeat match goal with |- sepcon _ _ = sepcon _ _ => f_equal end;
    first [reflexivity | apply data_at_cs_eq; first [apply JMeq_refl | reflexivity]].
Qed.

Lemma calloc_valid_pointer n v p : 0 <= n ->
  @malloc_token CSw Ews (tarray tuchar n) p * @data_at CSw Ews (tarray tuchar n) v p |-- valid_pointer p.
Proof.
  intros. destruct (Z.lt_ge_cases 0 n).
  - apply sepcon_valid_pointer2.
    apply data_at_valid_ptr; [auto | simpl; rewrite Z.max_r by lia; lia].
  - apply sepcon_valid_pointer1.
    apply (@malloc_token_valid_pointer CSw). simpl. rewrite Z.max_r by lia; lia.
Qed.

Lemma map_Vint_bytes (l: list Z) : Forall (fun b => 0 <= b <= Byte.max_unsigned) l ->
  map (fun b => Vint (Int.repr b)) l = bytes (map Byte.repr l).
Proof.
  induction l as [| a l IH]; intros Hl; [reflexivity |].
  inversion Hl; subst. unfold bytes in *; simpl. rewrite IH by auto.
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma is_int_Vubyte' b : is_int I8 Unsigned (Vubyte b).
Proof. unfold Vubyte; simpl. pose proof (Byte.unsigned_range_2 b). rewrite Int.unsigned_repr; rep_lia. Qed.

Lemma andb_ltb_typed_true i a b :
  typed_true tint (if andb (i <? a) (i <? b) then Vtrue else Vfalse) -> i < a /\ i < b.
Proof.
  destruct (Z.ltb_spec i a), (Z.ltb_spec i b); simpl; intros Ht;
    unfold typed_true in Ht; simpl in Ht; try discriminate; lia.
Qed.

Lemma andb_ltb_typed_false i a b :
  typed_false tint (if andb (i <? a) (i <? b) then Vtrue else Vfalse) -> ~ (i < a /\ i < b).
Proof.
  destruct (Z.ltb_spec i a), (Z.ltb_spec i b); simpl; intros Ht;
    unfold typed_false in Ht; simpl in Ht; try discriminate; lia.
Qed.

Lemma tc_val_of_bool b : tc_val tbool (Val.of_bool b).
Proof. destruct b; simpl; auto. Qed.

Lemma ts_N2S sh (v: val * val) p :
  @data_at Noise.CS sh t_timespec v p = @data_at Shim.CS sh t_timespec v p.
Proof. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

Lemma ts__N2S sh p : @data_at_ Noise.CS sh t_timespec p = @data_at_ Shim.CS sh t_timespec p.
Proof. apply data_at__cs_eq; reflexivity. Qed.

Lemma prot3_shim_small_body_ktime_get_coarse_boottime_ns :
  @semax_body (QPvarspecs Shim.qp) Gsh Shim.CS WgNoise.shim.code.f_ktime_get_coarse_boottime_ns ktime_get_coarse_boottime_ns_spec.
Proof.
  start_function.
  rewrite shim_state_S_eq; unfold shim_state_S; Intros.
  forward.
  forward.
  rewrite shim_state_S_eq; unfold shim_state_S; entailer!.
Qed.

Lemma prot3_shim_small_body_ktime_get_real_ts64 :
  @semax_body (QPvarspecs Shim.qp) Gsh Shim.CS WgNoise.shim.code.f_ktime_get_real_ts64 ktime_get_real_ts64_spec.
Proof.
  start_function.
  rewrite shim_state_S_eq; unfold shim_state_S; Intros.
  rewrite ts__N2S.
  forward. forward. forward. forward.
  rewrite shim_state_S_eq, ts_N2S; unfold shim_state_S; entailer!.
Qed.

Lemma prot3_shim_small_body_get_random_bytes :
  @semax_body (QPvarspecs Shim.qp) Gsh Shim.CS WgNoise.shim.code.f_get_random_bytes get_random_bytes_spec.
Proof.
  start_function.
  forward.
  rewrite (@data_at__tarray_tuchar_cs Noise.CS CSw).
  forward_call (buf, n, sh).
  Intros bz.
  rewrite (@data_at_tarray_tuchar_cs CSw Shim.CS).
  rewrite map_Vint_bytes by auto.
  set (bs := map Byte.repr bz).
  assert (Hbs: Zlength bs = n) by (subst bs; rewrite Zlength_map; auto).
  clearbody bs. clear H0 H1.
  rewrite shim_state_S_eq; unfold shim_state_S.
  Intros. match goal with H: shim_ok S |- _ => destruct H as [Hl Hlp] end.
  forward_for_simple_bound 32 (EX i: Z,
    PROP () LOCAL (temp WgNoise.shim.code._b buf; temp WgNoise.shim.code._len (Vlong (Int64.repr n)); gvars gv)
    SEP (data_at sh (tarray tuchar n) (bytes bs) buf;
         data_at Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns);
         data_at Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec);
         data_at Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec);
         data_at Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log);
         data_at Ews (tarray tuchar 32) (bytes (sublist 0 i (s_log S) ++ sublist i 32 (s_logprev S)))
           (gv _wg_shim_random_log_prev);
         data_at Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32);
         data_at Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs);
         data_at Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures);
         data_at Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees);
         data_at Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc);
         data_at Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released);
         data_at Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow); refwarn gv)).
  { entailer!. autorewrite with sublist. apply derives_refl. }
  { unfold bytes. forward.
    { entailer!. try rewrite Znth_map by lia. apply is_int_Vubyte'. }
    try rewrite Znth_map by lia.
    forward.
    entailer!. fold (Vubyte (Znth i (s_log S))). apply derives_refl'. f_equal. unfold bytes. list_solve. }
  rewrite (sublist_same 0 32) by lia. rewrite sublist_nil, app_nil_r. subst n.
  forward.
  forward_loop (EX i: Z,
    PROP (0 <= i <= Z.min (Zlength bs) 32)
    LOCAL (temp WgNoise.shim.code._i (Vlong (Int64.repr i)); temp WgNoise.shim.code._b buf;
           temp WgNoise.shim.code._len (Vlong (Int64.repr (Zlength bs))); gvars gv)
    SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes bs) buf;
         data_at Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns);
         data_at Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec);
         data_at Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec);
         data_at Ews (tarray tuchar 32) (bytes (sublist 0 i bs ++ sublist i 32 (s_log S))) (gv _wg_shim_random_log);
         data_at Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log_prev);
         data_at Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32);
         data_at Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs);
         data_at Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures);
         data_at Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees);
         data_at Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc);
         data_at Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released);
         data_at Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow); refwarn gv))
  continue: (EX i: Z,
    PROP (0 <= i < Z.min (Zlength bs) 32)
    LOCAL (temp WgNoise.shim.code._i (Vlong (Int64.repr i)); temp WgNoise.shim.code._b buf;
           temp WgNoise.shim.code._len (Vlong (Int64.repr (Zlength bs))); gvars gv)
    SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes bs) buf;
         data_at Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns);
         data_at Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec);
         data_at Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec);
         data_at Ews (tarray tuchar 32) (bytes (sublist 0 (i + 1) bs ++ sublist (i + 1) 32 (s_log S)))
           (gv _wg_shim_random_log);
         data_at Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log_prev);
         data_at Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32);
         data_at Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs);
         data_at Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures);
         data_at Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees);
         data_at Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc);
         data_at Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released);
         data_at Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow); refwarn gv)).
  { Exists 0. rewrite sublist_nil, (sublist_same 0 32) by lia. simpl app. entailer!. }
  { Intros i.
    forward_if (PROP ()
      LOCAL (temp WgNoise.shim.code._t'1 (Val.of_bool (andb (i <? Zlength bs) (i <? 32)));
             temp WgNoise.shim.code._i (Vlong (Int64.repr i)); temp WgNoise.shim.code._b buf;
             temp WgNoise.shim.code._len (Vlong (Int64.repr (Zlength bs))); gvars gv)
      SEP (data_at sh (tarray tuchar (Zlength bs)) (bytes bs) buf;
         data_at Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns);
         data_at Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec);
         data_at Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec);
         data_at Ews (tarray tuchar 32) (bytes (sublist 0 i bs ++ sublist i 32 (s_log S))) (gv _wg_shim_random_log);
         data_at Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log_prev);
         data_at Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32);
         data_at Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs);
         data_at Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures);
         data_at Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees);
         data_at Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc);
         data_at Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released);
         data_at Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow); refwarn gv)).
    { forward. entailer!.
      replace (i <? Zlength bs) with true by (symmetry; apply Z.ltb_lt; lia). simpl.
      unfold Int64.cmpu, Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
      destruct (zlt i 32).
      - rewrite (proj2 (Z.ltb_lt _ _) l). reflexivity.
      - rewrite (proj2 (Z.ltb_ge i 32)) by lia. reflexivity. }
    { forward. entailer!.
      replace (i <? Zlength bs) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
    forward_if.
    { apply andb_ltb_typed_true in H1. destruct H1 as [Hia Hib].
      unfold bytes. forward.
      { entailer!. try rewrite Znth_map by lia. apply is_int_Vubyte'. }
      try rewrite Znth_map by lia.
      forward.
      Exists i. entailer!.
      fold (Vubyte (Znth i bs)). apply derives_refl'. f_equal. list_solve. }
    { apply andb_ltb_typed_false in H1.
      assert (Hi: i = Z.min (Zlength bs) 32) by lia.
      forward.
      Exists bs. entailer!.
      rewrite shim_state_S_eq; unfold shim_state_S, shim_draw, shim_ok; simpl.
      unfold bytes_at. rewrite (@data_at_tarray_tuchar_cs Noise.CS Shim.CS).
      match goal with Hz: Zlength (bytes (sublist 0 _ _ ++ _)) = 32 |- _ =>
        unfold bytes in Hz; rewrite Zlength_map in Hz end.
      rewrite prop_true_andp by auto. cancel. } }
  { Intros i. forward. Exists (i + 1). entailer!. }
Qed.

Lemma prot3_shim_small_body_get_random_bytes_wait :
  @semax_body (QPvarspecs Shim.qp) Gsh Shim.CS WgNoise.shim.code.f_get_random_bytes_wait get_random_bytes_wait_spec.
Proof.
  start_function.
  forward_call (gv, S, sh, buf, n).
  Intros bs.
  Exists bs. entailer!.
Qed.

Lemma prot3_shim_small_body_get_random_u32 :
  @semax_body (QPvarspecs Shim.qp) Gsh Shim.CS WgNoise.shim.code.f_get_random_u32 get_random_u32_spec.
Proof.
  start_function.
  forward_call tt.
  Intros n.
  rewrite shim_state_S_eq; unfold shim_state_S; Intros.
  forward. forward. forward.
  Exists (Int.repr n).
  rewrite shim_state_S_eq; unfold shim_state_S, shim_u32, shim_ok in *; simpl; entailer!.
Qed.

Lemma prot3_shim_small_body_kzalloc :
  @semax_body (QPvarspecs Shim.qp) Gsh Shim.CS WgNoise.shim.code.f_kzalloc (kzalloc_spec CSw).
Proof.
  start_function.
  rewrite shim_state_S_eq; unfold shim_state_S; Intros.
  forward. { entailer!. apply tc_val_of_bool. }
  destruct (s_failnext S) eqn:Hf.
  - forward_if.
    + forward. forward. forward. forward.
      Exists nullval.
      rewrite shim_state_S_eq; unfold shim_state_S, shim_alloc_fail, shim_ok in *; simpl.
      entailer!.
    + discriminate.
  - forward_if (PROP () LOCAL (gvars gv; temp WgNoise.shim.code._size (Vlong (Int64.repr n)))
                 SEP (mem_mgr gv; shim_state gv S)).
    { discriminate. }
    { forward. rewrite shim_state_S_eq; unfold shim_state_S. rewrite Hf. entailer!. }
    forward_call (1, n, gv).
    Intros p.
    rewrite shim_state_S_eq; unfold shim_state_S; Intros.
    destruct (eq_dec p nullval) as [Hp | Hp].
    + subst p.
      forward_if (PROP () LOCAL (temp WgNoise.shim.code._p nullval)
                  SEP (mem_mgr gv; shim_state gv (shim_alloc_fail S))).
      { contradiction. }
      { forward. forward.
        rewrite shim_state_S_eq; unfold shim_state_S, shim_alloc_fail, shim_ok in *; simpl.
        rewrite Hf. change (Int64.repr (Int.signed (Int.repr 1))) with Int64.one. go_lowerx. entailer!. }
      forward.
      Exists nullval. entailer!.
      rewrite if_true by auto. cancel.
    + Intros.
      forward_if (PROP () LOCAL (temp WgNoise.shim.code._p p)
                  SEP (mem_mgr gv; shim_state gv (shim_alloc_ok S);
                       @malloc_token CSw Ews (tarray tuchar (1 * n)) p;
                       @data_at CSw Ews (tarray tuchar (1 * n)) (Zrepeat (Vubyte Byte.zero) (1 * n)) p)).
      { apply denote_tc_test_eq_split; [ | auto with valid_pointer].
        do 13 apply sepcon_valid_pointer1. rewrite sepcon_assoc. apply sepcon_valid_pointer2.
        apply calloc_valid_pointer; lia. }
      { forward. forward.
        rewrite shim_state_S_eq; unfold shim_state_S, shim_alloc_ok, shim_ok in *; simpl.
        change (Int64.repr (Int.signed (Int.repr 1))) with Int64.one. go_lowerx. entailer!. }
      { contradiction. }
      forward.
      Exists p. rewrite if_false by auto.
      entailer!.
rewrite if_false by auto. unfold bytes_at, zeros, bytes. rewrite Zlength_Zrepeat by lia.
      unfold Zrepeat at 2. rewrite map_repeat. rewrite (@data_at_tarray_tuchar_cs CSw Noise.CS). cancel.
Qed.

Lemma prot3_shim_small_body_kfree :
  @semax_body (QPvarspecs Shim.qp) Gsh Shim.CS WgNoise.shim.code.f_kfree (kfree_spec CSw).
Proof.
  start_function.
  destruct (eq_dec p nullval) as [Hp | Hp].
  - subst p.
    forward_if.
    + contradiction.
    + forward. entailer!.
  - Intros.
    forward_if.
    { apply denote_tc_test_eq_split; [ | auto with valid_pointer].
      destruct (Z.lt_ge_cases 0 n).
      - apply sepcon_valid_pointer2. unfold data_at_, field_at_.
        apply data_at_valid_ptr; [auto | simpl; rewrite Z.max_r by lia; lia].
      - apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
        apply (@malloc_token_valid_pointer CSw). simpl. rewrite Z.max_r by lia; lia. }
    + rewrite shim_state_S_eq; unfold shim_state_S; Intros.
      forward. forward.
      rewrite (@data_at__tarray_tuchar_cs Noise.CS CSw).
      forward_call (tarray tuchar n, p, gv).
      { rewrite if_false by auto. cancel. }
      entailer!.
      rewrite shim_state_S_eq; unfold shim_state_S, shim_free, shim_ok in *; simpl; entailer!.
    + contradiction.
Qed.

Lemma prot3_shim_small_body_kfree_sensitive :
  @semax_body (QPvarspecs Shim.qp) Gsh Shim.CS WgNoise.shim.code.f_kfree_sensitive (kfree_sensitive_spec CSw).
Proof.
  start_function.
  forward_call (gv, S, p, n).
  entailer!.
Qed.

Lemma refs_N2S sh p r :
  @field_at Noise.CS sh t_peer [StructField I._refcount] (Vint r) p =
  @field_at Shim.CS sh t_peer [StructField I._refcount] (Vint r) p.
Proof. apply field_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

Lemma dev_N2S sh p d :
  @field_at Noise.CS sh t_peer [StructField I._device] d p =
  @field_at Shim.CS sh t_peer [StructField I._device] d p.
Proof. apply field_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

Lemma kref_N2S sh k r : @data_at Noise.CS sh t_kref (Vint r) k = @data_at Shim.CS sh t_kref (Vint r) k.
Proof. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

(* the kref of a peer is one unsigned int, &peer->refcount.refcount is the shim's refcount_t *)
Lemma prot3_shim_small_peer_rc sh p v :
  @field_at Shim.CS sh t_peer [StructField I._refcount] (Vint v) p =
  @data_at Shim.CS sh tuint (Vint v) (field_address t_peer (DOT I._refcount DOT I._refcount) p).
Proof.
  erewrite field_at_Tstruct; [| reflexivity | apply JMeq_refl].
  unfold nested_sfieldlist_at. simpl. unfold withspacer. simpl.
  rewrite field_at_data_at. reflexivity.
Qed.

Lemma prot3_shim_small_fc_rc p : field_compatible t_peer [StructField I._refcount] p ->
  field_compatible t_peer (DOT I._refcount DOT I._refcount) p.
Proof. intros H. apply field_compatible_cons. simpl. split; [left; reflexivity | exact H]. Qed.

Lemma prot3_shim_small_body_wg_peer_get_maybe_zero :
  @semax_body (QPvarspecs Shim.qp) Gsh Shim.CS WgNoise.shim.code.f_wg_peer_get_maybe_zero wg_peer_get_maybe_zero_spec.
Proof.
  start_function.
  destruct (eq_dec p nullval) as [Hp | Hp].
  - subst p.
    forward_if (PROP () LOCAL (temp WgNoise.shim.code._t'1 (Vint Int.one)) SEP (shim_state gv S)).
    + forward. entailer!.
    + contradiction.
    + forward_if.
      { forward. }
      { match goal with H: Int.one = Int.zero |- _ => inversion H end. }
  - unfold peer_refs_rep. rewrite refs_N2S, dev_N2S.
    forward_if (PROP () LOCAL (temp WgNoise.shim.code._t'1 (Vint (if Int.eq r Int.zero then Int.one else Int.zero));
                              temp WgNoise.shim.code._peer p)
                SEP (shim_state gv S;
                     @field_at Shim.CS sh t_peer [StructField I._refcount]
                       (Vint (if Int.eq r Int.zero then r else rc_add1 r)) p;
                     @field_at Shim.CS sh t_peer [StructField I._device] d p)).
    + apply denote_tc_test_eq_split; [ | auto with valid_pointer].
      apply sepcon_valid_pointer2. apply field_at_valid_ptr0; [auto | reflexivity | reflexivity].
    + contradiction.
    + assert_PROP (field_compatible t_peer [StructField I._refcount] p) as FC by entailer!.
      apply prot3_shim_small_fc_rc in FC.
      rewrite prot3_shim_small_peer_rc.
      unfold shim_state. Intros.
      forward_call (gv, sh, field_address t_peer (DOT I._refcount DOT I._refcount) p, r).
      forward.
      rewrite prot3_shim_rc_uint_N2S, <- prot3_shim_small_peer_rc.
      unfold shim_state. entailer!.
      destruct (Int.eq r Int.zero); reflexivity.
    + destruct (Int.eq r Int.zero) eqn:Hr.
      * forward_if.
        { forward. unfold peer_refs_rep. rewrite ?refs_N2S, ?dev_N2S. entailer!. }
        { match goal with H: Int.one = Int.zero |- _ => inversion H end. }
      * forward_if.
        { match goal with H: 0 <> 0 |- _ => contradiction H; reflexivity end. }
        { forward. unfold peer_refs_rep. rewrite ?refs_N2S, ?dev_N2S. entailer!. }
Qed.

Lemma prot3_shim_small_body_wg_peer_put :
  @semax_body (QPvarspecs Shim.qp) Gsh Shim.CS WgNoise.shim.code.f_wg_peer_put wg_peer_put_spec.
Proof.
  start_function.
  destruct (eq_dec p nullval) as [Hp | Hp].
  - subst p.
    forward_if.
    + forward.
    + contradiction.
  - unfold peer_refs_rep. rewrite refs_N2S, dev_N2S. Intros.
    forward_if (PROP () LOCAL (temp WgNoise.shim.code._peer p; gvars gv)
                SEP (shim_state gv S; @field_at Shim.CS sh t_peer [StructField I._refcount] (Vint r) p;
                     @field_at Shim.CS sh t_peer [StructField I._device] d p)).
    + apply denote_tc_test_eq_split; [ | auto with valid_pointer].
      apply sepcon_valid_pointer2. apply field_at_valid_ptr0; [auto | reflexivity | reflexivity].
    + contradiction.
    + forward. entailer!.
    + forward_loop (PROP () LOCAL (temp WgNoise.shim.code._peer p; gvars gv)
                SEP (shim_state gv S; @field_at Shim.CS sh t_peer [StructField I._refcount] (Vint r) p;
                     @field_at Shim.CS sh t_peer [StructField I._device] d p))
      continue: (PROP () LOCAL (temp WgNoise.shim.code._peer p; gvars gv)
                SEP (shim_state gv (if Int.eq (rc_sub1 r) Int.zero then shim_release S else S);
                     @field_at Shim.CS sh t_peer [StructField I._refcount] (Vint (rc_sub1 r)) p;
                     @field_at Shim.CS sh t_peer [StructField I._device] d p)).
      * entailer!.
      * assert_PROP (field_compatible t_peer [StructField I._refcount] p) as FC0 by entailer!.
        pose proof (prot3_shim_small_fc_rc p FC0) as FC.
        rewrite prot3_shim_small_peer_rc.
        unfold shim_state at 1. Intros.
        forward_call (gv, sh, field_address t_peer (DOT I._refcount DOT I._refcount) p, r).
        rewrite prot3_shim_rc_uint_N2S, <- prot3_shim_small_peer_rc.
        forward_if.
        -- forward_call (gv, S, field_address t_peer [StructField I._refcount] p).
           { unfold shim_state. entailer!. }
           change (Int.repr 0) with Int.zero in *.
           destruct (Int.eq (rc_sub1 r) Int.zero); [entailer! | unfold typed_true in *; simpl in *; discriminate].
        -- forward. change (Int.repr 0) with Int.zero in *.
           destruct (Int.eq (rc_sub1 r) Int.zero); [unfold typed_false in *; simpl in *; discriminate |].
           unfold shim_state. entailer!.
      * forward. unfold peer_refs_rep. rewrite ?refs_N2S, ?dev_N2S.
        entailer!.
Qed.

Lemma prot3_shim_small_body_wg_shim_peer_release :
  @semax_body (QPvarspecs Shim.qp) Gsh Shim.CS WgNoise.shim.code.f_wg_shim_peer_release wg_shim_peer_release_spec.
Proof.
  start_function.
  rewrite shim_state_S_eq; unfold shim_state_S; Intros.
  forward. forward.
  rewrite shim_state_S_eq; unfold shim_state_S; entailer!.
Qed.

Lemma prot3_shim_small_body_wg_ratelimiter_allow :
  @semax_body (QPvarspecs Shim.qp) Gsh Shim.CS WgNoise.shim.code.f_wg_ratelimiter_allow wg_ratelimiter_allow_spec.
Proof.
  start_function.
  rewrite shim_state_S_eq; unfold shim_state_S; Intros.
  forward. { entailer!. apply tc_val_of_bool. }
  forward.
  rewrite shim_state_S_eq; unfold shim_state_S; entailer!.
  destruct (s_rlallow S); reflexivity.
Qed.

Lemma prot3_shim_small_body_wg_birthdate_has_expired :
  @semax_body (QPvarspecs Shim.qp) Gsh Shim.CS WgNoise.shim.code.f_wg_birthdate_has_expired wg_birthdate_has_expired_spec.
Proof.
  start_function.
  forward_call (gv, S).
  forward.
  entailer!.
  unfold birthdate_expired, s64_le, NSEC_PER_SEC.
  destruct (Int64.lt _ _); reflexivity.
Qed.

End Bodies.

Theorem prot_bodies3_shim_small :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body (QPvarspecs Shim.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_ktime_get_coarse_boottime_ns ktime_get_coarse_boottime_ns_spec) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_ktime_get_real_ts64 ktime_get_real_ts64_spec) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_get_random_bytes get_random_bytes_spec) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_get_random_bytes_wait get_random_bytes_wait_spec) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_get_random_u32 get_random_u32_spec) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_kzalloc (kzalloc_spec CSw)) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_kfree (kfree_spec CSw)) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_kfree_sensitive (kfree_sensitive_spec CSw)) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_peer_get_maybe_zero wg_peer_get_maybe_zero_spec) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_shim_peer_release wg_shim_peer_release_spec) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_peer_put wg_peer_put_spec) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_ratelimiter_allow wg_ratelimiter_allow_spec) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_birthdate_has_expired wg_birthdate_has_expired_spec).
Proof.
  intros.
  split; [apply prot3_shim_small_body_ktime_get_coarse_boottime_ns |].
  split; [apply prot3_shim_small_body_ktime_get_real_ts64 |].
  split; [apply prot3_shim_small_body_get_random_bytes |].
  split; [apply prot3_shim_small_body_get_random_bytes_wait |].
  split; [apply prot3_shim_small_body_get_random_u32 |].
  split; [apply prot3_shim_small_body_kzalloc |].
  split; [apply prot3_shim_small_body_kfree |].
  split; [apply prot3_shim_small_body_kfree_sensitive |].
  split; [apply prot3_shim_small_body_wg_peer_get_maybe_zero |].
  split; [apply prot3_shim_small_body_wg_shim_peer_release |].
  split; [apply prot3_shim_small_body_wg_peer_put |].
  split; [apply prot3_shim_small_body_wg_ratelimiter_allow |].
  apply prot3_shim_small_body_wg_birthdate_has_expired.
Qed.
