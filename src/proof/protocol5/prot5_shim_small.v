(* The bodies of the shim's small functions (clocks, randomness, allocation, refcount_t, peer references)
   against their v5 specifications (prot_specs5.v: v4's, unchanged), in the context Gprot5 (prot_prog5.v).
   The scripts are those of prot4_shim_rc.v and prot4_shim_small.v, re-run because a body's function context
   is part of its statement; their helper lemmas (shim_state4_S_eq, the compspecs conversions) are reused. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require Import WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.protocol4.prot4_shim_rc.
Require Import WgNoise.proof.protocol4.prot4_shim_small.
Require WgNoise.noise.code WgNoise.shim.code.

Section Bodies.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Shim.CS.
Local Open Scope logic.

Definition Gsh5 := Gprot5 x25519 aead_enc aead_dec CSw Shim.CS.

Lemma prot5_shim_body_warn_saturate :
  @semax_body (QPvarspecs Shim.qp) Gsh5 Shim.CS
    WgNoise.shim.code.f_wg_shim_refcount_warn_saturate wg_shim_refcount_warn_saturate_spec.
Proof.
  start_function.
  rewrite prot4_refwarn4_S_eq, prot4_shim_rc_uint_N2S. unfold prot4_refwarn4_S. Intros.
  forward.
  forward.
  forward.
  rewrite prot4_refwarn4_S_eq, prot4_shim_rc_uint_N2S. unfold prot4_refwarn4_S, warn_bump.
  rewrite prot4_shim_rc_sat_repr.
  entailer!.
  - rewrite upd_Znth_Zlength by lia. auto.
  - first [rewrite upd_Znth_map | rewrite <- upd_Znth_map]; cancel.
Qed.

Lemma prot5_shim_body_neg :
  @semax_body (QPvarspecs Shim.qp) Gsh5 Shim.CS
    WgNoise.shim.code.f_wg_shim_refcount_neg wg_shim_refcount_neg_spec.
Proof.
  start_function.
  forward.
  entailer!.
  unfold rc_neg. rewrite prot4_shim_rc_neg_repr.
  destruct (Int.ltu v (Int.repr 2147483648)); reflexivity.
Qed.

Lemma prot5_shim_body_inc_not_zero :
  @semax_body (QPvarspecs Shim.qp) Gsh5 Shim.CS
    WgNoise.shim.code.f_wg_shim_refcount_inc_not_zero wg_shim_refcount_inc_not_zero_spec.
Proof.
  start_function.
  rewrite prot4_shim_rc_uint_N2S.
  forward.
  forward_if.
  { forward. rewrite prot4_shim_rc_uint_N2S. entailer!. apply derives_refl. }
  forward.
  forward_call v.
  forward_if (PROP () LOCAL (temp WgNoise.shim.code._t'2
                                (Vint (if orb (rc_neg v) (rc_neg (Int.add v Int.one)) then Int.one else Int.zero));
                             temp WgNoise.shim.code._r r; temp WgNoise.shim.code._old (Vint v); gvars gv)
              SEP (@data_at Shim.CS sh tuint (Vint (Int.add v Int.one)) r; refwarn4 gv w)).
  { forward. destruct (rc_neg v) eqn:E; [| unfold typed_true in *; simpl in *; discriminate].
    simpl orb. entailer!. }
  { forward_call (Int.add v Int.one). forward.
    destruct (rc_neg v) eqn:E; [unfold typed_false in *; simpl in *; discriminate |].
    simpl orb. entailer!. destruct (rc_neg (Int.add v Int.one)); reflexivity. }
  forward_if (PROP () LOCAL (temp WgNoise.shim.code._r r; temp WgNoise.shim.code._old (Vint v); gvars gv)
              SEP (@data_at Noise.CS sh tuint (Vint (rc_add1 v)) r; refwarn4 gv (rc_inz_warn v w))).
  { rewrite <- prot4_shim_rc_uint_N2S. forward_call (gv, w, sh, r, Int.add v Int.one, 0).
    unfold rc_add1, rc_inz_warn, REFCOUNT_ADD_NOT_ZERO_OVF. rewrite (Int.eq_false v Int.zero H). destruct (orb (rc_neg v) (rc_neg (Int.add v Int.one))); [entailer! | contradiction]. }
  { forward. rewrite <- prot4_shim_rc_uint_N2S.
    unfold rc_add1, rc_inz_warn. rewrite (Int.eq_false v Int.zero H).
    destruct (orb (rc_neg v) (rc_neg (Int.add v Int.one))); [discriminate | entailer!]. }
  forward.
  rewrite (Int.eq_false v Int.zero H). entailer!.
Qed.



Lemma prot5_shim_body_dec_and_test :
  @semax_body (QPvarspecs Shim.qp) Gsh5 Shim.CS
    WgNoise.shim.code.f_wg_shim_refcount_dec_and_test wg_shim_refcount_dec_and_test_spec.
Proof.
  start_function.
  rewrite prot4_shim_rc_uint_N2S.
  forward.
  forward.
  forward_call v.
  forward_if (PROP () LOCAL (temp WgNoise.shim.code._t'2
                                (Vint (if andb (negb (rc_neg v)) (Int.eq v Int.one) then Int.one else Int.zero));
                             temp WgNoise.shim.code._r r; temp WgNoise.shim.code._old (Vint v); gvars gv)
              SEP (@data_at Shim.CS sh tuint (Vint (Int.sub v Int.one)) r; refwarn4 gv w)).
  { forward. destruct (rc_neg v) eqn:E; [unfold typed_true in *; simpl in *; discriminate |].
    cbn [andb negb]. entailer!. change (Int.repr 1) with Int.one. destruct (Int.eq v Int.one); reflexivity. }
  { forward. destruct (rc_neg v) eqn:E; [| unfold typed_false in *; simpl in *; discriminate].
    cbn [andb negb]. entailer!. }
  forward_if.
  { forward.
    destruct (andb (negb (rc_neg v)) (Int.eq v Int.one)) eqn:E; [| contradiction].
    apply andb_prop in E. destruct E as [_ E]. apply Int.same_if_eq in E. subst v.
    rewrite <- prot4_shim_rc_uint_N2S. unfold rc_sub1, rc_dec_warn. rewrite Int.eq_true. simpl. entailer!. }
  assert (EA: andb (negb (rc_neg v)) (Int.eq v Int.one) = false).
  { destruct (andb (negb (rc_neg v)) (Int.eq v Int.one)); [discriminate | reflexivity]. }
  clear H.
  forward_if (PROP () LOCAL (temp WgNoise.shim.code._t'3
                                (Vint (if orb (Int.eq v Int.zero) (rc_neg v) then Int.one else Int.zero));
                             temp WgNoise.shim.code._r r; temp WgNoise.shim.code._old (Vint v); gvars gv)
              SEP (@data_at Shim.CS sh tuint (Vint (Int.sub v Int.one)) r; refwarn4 gv w)).
  { forward. subst v. entailer!. }
  { forward_call v. forward. rewrite (Int.eq_false v Int.zero H). cbn [orb]. entailer!.
    destruct (rc_neg v); reflexivity. }
  forward_if (PROP () LOCAL ()
              SEP (@data_at Noise.CS sh tuint (Vint (rc_sub1 v)) r; refwarn4 gv (rc_dec_warn v w))).
  { rewrite <- prot4_shim_rc_uint_N2S. forward_call (gv, w, sh, r, Int.sub v Int.one, 3).
    unfold rc_sub1, rc_dec_warn, REFCOUNT_SUB_UAF. rewrite EA. change (Int.repr 0) with Int.zero in H.
    destruct (orb (Int.eq v Int.zero) (rc_neg v)); [entailer! | contradiction]. }
  { forward. rewrite <- prot4_shim_rc_uint_N2S.
    unfold rc_sub1, rc_dec_warn. rewrite EA. change (Int.repr 0) with Int.zero in H.
    destruct (orb (Int.eq v Int.zero) (rc_neg v));
      [exfalso; apply Int.one_not_zero; exact H | entailer!]. }
  forward.
  apply prop_right.
  assert (Int.eq (rc_sub1 v) Int.zero = false) as ->; [| reflexivity].
  unfold rc_sub1. rewrite EA.
  destruct (Int.eq v Int.zero) eqn:E0; [vm_compute; reflexivity |].
  destruct (rc_neg v) eqn:EN; [vm_compute; reflexivity |].
  simpl. apply prot4_shim_rc_sub_one. intros ->. rewrite Int.eq_true in EA. discriminate.
Qed.

Lemma prot5_shim_body_ktime_get_coarse_boottime_ns :
  @semax_body (QPvarspecs Shim.qp) Gsh5 Shim.CS WgNoise.shim.code.f_ktime_get_coarse_boottime_ns ktime_get_coarse_boottime_ns_spec.
Proof.
  start_function.
  rewrite shim_state4_S_eq; unfold shim_state4_S; Intros.
  forward.
  forward.
  rewrite shim_state4_S_eq; unfold shim_state4_S; entailer!.
Qed.

Lemma prot5_shim_body_ktime_get_real_ts64 :
  @semax_body (QPvarspecs Shim.qp) Gsh5 Shim.CS WgNoise.shim.code.f_ktime_get_real_ts64 ktime_get_real_ts64_spec.
Proof.
  start_function.
  rewrite shim_state4_S_eq; unfold shim_state4_S; Intros.
  rewrite ts__N2S.
  forward. forward. forward. forward.
  rewrite shim_state4_S_eq, ts_N2S; unfold shim_state4_S; entailer!.
Qed.

Lemma prot5_shim_body_get_random_bytes :
  @semax_body (QPvarspecs Shim.qp) Gsh5 Shim.CS WgNoise.shim.code.f_get_random_bytes get_random_bytes_spec.
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
  rewrite shim_state4_S_eq; unfold shim_state4_S.
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
         data_at Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow); refwarn4 gv w)).
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
         data_at Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow); refwarn4 gv w))
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
         data_at Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow); refwarn4 gv w)).
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
         data_at Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow); refwarn4 gv w)).
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
      rewrite shim_state4_S_eq; unfold shim_state4_S, shim_draw, shim_ok; simpl.
      unfold bytes_at. rewrite (@data_at_tarray_tuchar_cs Noise.CS Shim.CS).
      match goal with Hz: Zlength (bytes (sublist 0 _ _ ++ _)) = 32 |- _ =>
        unfold bytes in Hz; rewrite Zlength_map in Hz end.
      rewrite prop_true_andp by auto. cancel. } }
  { Intros i. forward. Exists (i + 1). entailer!. }
Qed.

Lemma prot5_shim_body_get_random_bytes_wait :
  @semax_body (QPvarspecs Shim.qp) Gsh5 Shim.CS WgNoise.shim.code.f_get_random_bytes_wait get_random_bytes_wait_spec.
Proof.
  start_function.
  forward_call (gv, S, w, sh, buf, n).
  Intros bs.
  Exists bs. entailer!.
Qed.

Lemma prot5_shim_body_get_random_u32 :
  @semax_body (QPvarspecs Shim.qp) Gsh5 Shim.CS WgNoise.shim.code.f_get_random_u32 get_random_u32_spec.
Proof.
  start_function.
  forward_call tt.
  Intros n.
  rewrite shim_state4_S_eq; unfold shim_state4_S; Intros.
  forward. forward. forward.
  Exists (Int.repr n).
  rewrite shim_state4_S_eq; unfold shim_state4_S, shim_u32, shim_ok in *; simpl; entailer!.
Qed.

Lemma prot5_shim_body_kzalloc :
  @semax_body (QPvarspecs Shim.qp) Gsh5 Shim.CS WgNoise.shim.code.f_kzalloc (kzalloc_spec CSw).
Proof.
  start_function.
  rewrite shim_state4_S_eq; unfold shim_state4_S; Intros.
  forward. { entailer!. apply tc_val_of_bool. }
  destruct (s_failnext S) eqn:Hf.
  - forward_if.
    + forward. forward. forward. forward.
      Exists nullval.
      rewrite shim_state4_S_eq; unfold shim_state4_S, shim_alloc_fail, shim_ok in *; simpl.
      entailer!.
    + discriminate.
  - forward_if (PROP () LOCAL (gvars gv; temp WgNoise.shim.code._size (Vlong (Int64.repr n)))
                 SEP (mem_mgr gv; shim_state4 gv S w)).
    { discriminate. }
    { forward. rewrite shim_state4_S_eq; unfold shim_state4_S. rewrite Hf. entailer!. }
    forward_call (1, n, gv).
    Intros p.
    rewrite shim_state4_S_eq; unfold shim_state4_S; Intros.
    destruct (eq_dec p nullval) as [Hp | Hp].
    + subst p.
      forward_if (PROP () LOCAL (temp WgNoise.shim.code._p nullval)
                  SEP (mem_mgr gv; shim_state4 gv (shim_alloc_fail S) w)).
      { contradiction. }
      { forward. forward.
        rewrite shim_state4_S_eq; unfold shim_state4_S, shim_alloc_fail, shim_ok in *; simpl.
        rewrite Hf. change (Int64.repr (Int.signed (Int.repr 1))) with Int64.one. go_lowerx. entailer!. }
      forward.
      Exists nullval. entailer!.
      rewrite if_true by auto. cancel.
    + Intros.
      forward_if (PROP () LOCAL (temp WgNoise.shim.code._p p)
                  SEP (mem_mgr gv; shim_state4 gv (shim_alloc_ok S) w;
                       @malloc_token CSw Ews (tarray tuchar (1 * n)) p;
                       @data_at CSw Ews (tarray tuchar (1 * n)) (Zrepeat (Vubyte Byte.zero) (1 * n)) p)).
      { apply denote_tc_test_eq_split; [ | auto with valid_pointer].
        do 13 apply sepcon_valid_pointer1. rewrite sepcon_assoc. apply sepcon_valid_pointer2.
        apply calloc_valid_pointer; lia. }
      { forward. forward.
        rewrite shim_state4_S_eq; unfold shim_state4_S, shim_alloc_ok, shim_ok in *; simpl.
        change (Int64.repr (Int.signed (Int.repr 1))) with Int64.one. go_lowerx. entailer!. }
      { contradiction. }
      forward.
      Exists p. rewrite if_false by auto.
      entailer!.
rewrite if_false by auto. unfold bytes_at, zeros, bytes. rewrite Zlength_Zrepeat by lia.
      unfold Zrepeat at 2. rewrite map_repeat. rewrite (@data_at_tarray_tuchar_cs CSw Noise.CS). cancel.
Qed.

Lemma prot5_shim_body_kfree :
  @semax_body (QPvarspecs Shim.qp) Gsh5 Shim.CS WgNoise.shim.code.f_kfree (kfree_spec CSw).
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
    + rewrite shim_state4_S_eq; unfold shim_state4_S; Intros.
      forward. forward.
      rewrite (@data_at__tarray_tuchar_cs Noise.CS CSw).
      forward_call (tarray tuchar n, p, gv).
      { rewrite if_false by auto. cancel. }
      entailer!.
      rewrite shim_state4_S_eq; unfold shim_state4_S, shim_free, shim_ok in *; simpl; entailer!.
    + contradiction.
Qed.

Lemma prot5_shim_body_kfree_sensitive :
  @semax_body (QPvarspecs Shim.qp) Gsh5 Shim.CS WgNoise.shim.code.f_kfree_sensitive (kfree_sensitive_spec CSw).
Proof.
  start_function.
  forward_call (gv, S, w, p, n).
  entailer!.
Qed.



Lemma prot5_shim_body_wg_peer_get_maybe_zero :
  @semax_body (QPvarspecs Shim.qp) Gsh5 Shim.CS WgNoise.shim.code.f_wg_peer_get_maybe_zero wg_peer_get_maybe_zero_spec.
Proof.
  start_function.
  destruct (eq_dec p nullval) as [Hp | Hp].
  - subst p.
    forward_if (PROP () LOCAL (temp WgNoise.shim.code._t'1 (Vint Int.one)) SEP (shim_state4 gv S w)).
    + forward. entailer!.
    + contradiction.
    + forward_if.
      { forward. }
      { match goal with H: Int.one = Int.zero |- _ => inversion H end. }
  - unfold peer_refs_rep. rewrite refs_N2S, dev_N2S.
    forward_if (PROP () LOCAL (temp WgNoise.shim.code._t'1 (Vint (if Int.eq r Int.zero then Int.one else Int.zero));
                              temp WgNoise.shim.code._peer p)
                SEP (shim_state4 gv S (rc_inz_warn r w);
                     @field_at Shim.CS sh t_peer [StructField I._refcount]
                       (Vint (if Int.eq r Int.zero then r else rc_add1 r)) p;
                     @field_at Shim.CS sh t_peer [StructField I._device] d p)).
    + apply denote_tc_test_eq_split; [ | auto with valid_pointer].
      apply sepcon_valid_pointer2. apply field_at_valid_ptr0; [auto | reflexivity | reflexivity].
    + contradiction.
    + assert_PROP (field_compatible t_peer [StructField I._refcount] p) as FC by entailer!.
      apply prot4_shim_small_fc_rc in FC.
      rewrite prot4_shim_small_peer_rc.
      unfold shim_state4. Intros.
      forward_call (gv, w, sh, field_address t_peer (DOT I._refcount DOT I._refcount) p, r).
      forward.
      rewrite prot4_shim_rc_uint_N2S, <- prot4_shim_small_peer_rc.
      unfold shim_state4. entailer!.
      destruct (Int.eq r Int.zero); reflexivity.
    + destruct (Int.eq r Int.zero) eqn:Hr.
      * forward_if.
        { forward. unfold peer_refs_rep. rewrite ?refs_N2S, ?dev_N2S. entailer!. }
        { match goal with H: Int.one = Int.zero |- _ => inversion H end. }
      * forward_if.
        { match goal with H: 0 <> 0 |- _ => contradiction H; reflexivity end. }
        { forward. unfold peer_refs_rep. rewrite ?refs_N2S, ?dev_N2S. entailer!. }
Qed.

Lemma prot5_shim_body_wg_peer_put :
  @semax_body (QPvarspecs Shim.qp) Gsh5 Shim.CS WgNoise.shim.code.f_wg_peer_put wg_peer_put_spec.
Proof.
  start_function.
  destruct (eq_dec p nullval) as [Hp | Hp].
  - subst p.
    forward_if.
    + forward.
    + contradiction.
  - unfold peer_refs_rep. rewrite refs_N2S, dev_N2S. Intros.
    forward_if (PROP () LOCAL (temp WgNoise.shim.code._peer p; gvars gv)
                SEP (shim_state4 gv S w; @field_at Shim.CS sh t_peer [StructField I._refcount] (Vint r) p;
                     @field_at Shim.CS sh t_peer [StructField I._device] d p)).
    + apply denote_tc_test_eq_split; [ | auto with valid_pointer].
      apply sepcon_valid_pointer2. apply field_at_valid_ptr0; [auto | reflexivity | reflexivity].
    + contradiction.
    + forward. entailer!.
    + forward_loop (PROP () LOCAL (temp WgNoise.shim.code._peer p; gvars gv)
                SEP (shim_state4 gv S w; @field_at Shim.CS sh t_peer [StructField I._refcount] (Vint r) p;
                     @field_at Shim.CS sh t_peer [StructField I._device] d p))
      continue: (PROP () LOCAL (temp WgNoise.shim.code._peer p; gvars gv)
                SEP (shim_state4 gv (if Int.eq (rc_sub1 r) Int.zero then shim_release S else S) (rc_dec_warn r w);
                     @field_at Shim.CS sh t_peer [StructField I._refcount] (Vint (rc_sub1 r)) p;
                     @field_at Shim.CS sh t_peer [StructField I._device] d p)).
      * entailer!.
      * assert_PROP (field_compatible t_peer [StructField I._refcount] p) as FC0 by entailer!.
        pose proof (prot4_shim_small_fc_rc p FC0) as FC.
        rewrite prot4_shim_small_peer_rc.
        unfold shim_state4 at 1. Intros.
        forward_call (gv, w, sh, field_address t_peer (DOT I._refcount DOT I._refcount) p, r).
        rewrite prot4_shim_rc_uint_N2S, <- prot4_shim_small_peer_rc.
        forward_if.
        -- forward_call (gv, S, rc_dec_warn r w, field_address t_peer [StructField I._refcount] p).
           { unfold shim_state4. entailer!. }
           change (Int.repr 0) with Int.zero in *.
           destruct (Int.eq (rc_sub1 r) Int.zero); [entailer! | unfold typed_true in *; simpl in *; discriminate].
        -- forward. change (Int.repr 0) with Int.zero in *.
           destruct (Int.eq (rc_sub1 r) Int.zero); [unfold typed_false in *; simpl in *; discriminate |].
           unfold shim_state4. entailer!.
      * forward. unfold peer_refs_rep. rewrite ?refs_N2S, ?dev_N2S.
        entailer!.
Qed.

Lemma prot5_shim_body_wg_shim_peer_release :
  @semax_body (QPvarspecs Shim.qp) Gsh5 Shim.CS WgNoise.shim.code.f_wg_shim_peer_release wg_shim_peer_release_spec.
Proof.
  start_function.
  rewrite shim_state4_S_eq; unfold shim_state4_S; Intros.
  forward. forward.
  rewrite shim_state4_S_eq; unfold shim_state4_S; entailer!.
Qed.



End Bodies.
