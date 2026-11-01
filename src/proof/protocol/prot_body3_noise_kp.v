(* Body proofs of the protocol piece, group noise_kp.
   Target: prot_bodies3_noise_kp.  Prove each function's body against its specification (prot_specs3.v) in the
   compspecs of its unit, with the context Gprot3 (prot_prog3.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_prog3.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.
Require Import VST.msl.iter_sepcon.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.protocol.prot_body3_shim_table1.
Require Import WgNoise.proof.protocol.prot3_noise_kp_lemmas.

Section NoiseKP.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

Definition Gn := Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS.

(* kfree_sensitive's token is at CSw: keep forward_call from converting it *)
Local Ltac change_compspecs cs ::= idtac.

(* container_of: (char * )(k + n) - n = k *)
Lemma prot3_noise_kp_ofs n i :
  0 <= n <= Int64.max_unsigned ->
  Ptrofs.sub (Ptrofs.add i (Ptrofs.repr n)) (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.repr n))) = i.
Proof.
  intros. rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc. unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by lia.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one, Ptrofs.add_neg_zero, Ptrofs.add_zero. reflexivity.
Qed.

Lemma prot3_noise_kp_body_free_rcu :
  @semax_body (QPvarspecs Noise.qp) Gn Noise.CS
    WgNoise.noise.code.f_keypair_free_rcu (keypair_free_rcu_spec CSw).
Proof.
  start_function.
  assert_PROP (isptr k) by entailer!.
  assert (k <> nullval) by (destruct k; try contradiction; discriminate).
  forward_call (gv, S, k, SIZEOF_KEYPAIR).
  { entailer!. destruct k; try contradiction. simpl. rewrite prot3_noise_kp_ofs by rep_lia. reflexivity. }
  { rewrite if_false by auto. cancel. }
  rewrite if_false by auto. entailer!.
Qed.

(* the kref of a keypair is one unsigned int, &keypair->refcount.refcount is the shim's refcount_t *)
Lemma prot3_noise_kp_rc_uint sh k v :
  field_at sh t_kp (DOT I._refcount) (Vint v) k =
  data_at sh tuint (Vint v) (field_address t_kp (DOT I._refcount DOT I._refcount) k).
Proof.
  erewrite field_at_Tstruct; [| reflexivity | apply JMeq_refl].
  unfold nested_sfieldlist_at. simpl. unfold withspacer. simpl.
  rewrite field_at_data_at. reflexivity.
Qed.

Lemma prot3_noise_kp_fc_rc k : field_compatible t_kp [] k ->
  field_compatible t_kp (DOT I._refcount DOT I._refcount) k.
Proof.
  intros H. apply field_compatible_cons. simpl. split; [left; reflexivity |].
  apply field_compatible_cons. simpl. split; [repeat first [left; reflexivity | right] | exact H].
Qed.

Lemma prot3_noise_kp_fold_shim gv S : shim_core gv S * refwarn gv |-- shim_state gv S.
Proof. rewrite shim_state_split. cancel. Qed.

Ltac prot3_noise_kp_vp VP :=
  match goal with
  | |- ?A * ?B |-- valid_pointer _ =>
      first [apply sepcon_valid_pointer2; prot3_noise_kp_vp VP | apply sepcon_valid_pointer1; prot3_noise_kp_vp VP]
  | _ => apply VP
  end.

Lemma prot3_noise_kp_body_get :
  @semax_body (QPvarspecs Noise.qp) Gn Noise.CS
    WgNoise.noise.code.f_wg_noise_keypair_get (wg_noise_keypair_get_spec CSw).
Proof.
  start_function.
  destruct H as [Hk|Hk].
  - subst k.
    forward_if (PROP () LOCAL (temp I._t'1 (Vint Int.one); temp I._keypair nullval)
                SEP (keypairs_rep CSw KS; itable sht tab T; shim_state gv S)).
    { forward. entailer!. }
    { exfalso. apply H; reflexivity. }
    forward_if.
    { forward. }
    { exfalso. apply Int.one_not_zero; auto. }
  - destruct (prot3_noise_kp_afind_in _ _ Hk) as [K HK].
    destruct (prot3_noise_kp_inpool _ _ _ _ H0 Hk) as (E & HE & HEp).
    assert (Hin: In k (saddrs (t_D T))) by (eapply prot3_noise_kp_sfind_saddrs; eauto).
    unfold keypairs_rep. rewrite (prot3_noise_kp_split _ _ _ _ HK).
    change (keypair_item_rep CSw (k, K)) with (keypair_rep CSw k K).
    rewrite (prot3_noise_kp_rc_split CSw k K).
    assert_PROP (field_compatible t_kp [] k) as FC0 by (sep_apply prot3_noise_kp_krest_fc; entailer!).
    pose proof (prot3_noise_kp_fc_rc k FC0) as FC.
    rewrite prot3_noise_kp_rc_uint.
    rewrite (shim_state_split gv S). Intros.
    forward_if (PROP () LOCAL (temp I._t'1 (Val.of_bool (Int.eq (kp_refs K) Int.zero)); temp I._keypair k)
      SEP (shim_core gv S; refwarn gv;
           data_at Ews tuint
             (Vint (if Int.eq (kp_refs K) Int.zero then kp_refs K else rc_add1 (kp_refs K)))
             (field_address t_kp (DOT I._refcount DOT I._refcount) k);
           prot3_noise_kp_krest CSw k K; iter_sepcon (keypair_item_rep CSw) (adel KS k); itable sht tab T)).
    { apply denote_tc_test_eq_split; [|apply valid_pointer_null].
      pose proof (prot3_shim_table1_valid sht tab T k Hin) as VP.
      prot3_noise_kp_vp VP. }
    { exfalso. subst k. destruct FC0 as [Hp _]. contradiction. }
    { forward_call (gv, Ews, field_address t_kp (DOT I._refcount DOT I._refcount) k, kp_refs K).
      forward. destruct (Int.eq (kp_refs K) Int.zero); entailer!. }
    assert (Hnn: k <> nullval) by (intro; subst k; destruct FC0 as [Hp _]; contradiction).
    destruct (Int.eq (kp_refs K) Int.zero) eqn:Hr.
    + forward_if (PROP (False) LOCAL () SEP ()).
      { forward. unfold kp_get. rewrite if_false by auto. rewrite HK, Hr.
        unfold keypairs_rep. rewrite (prot3_noise_kp_split _ _ _ _ HK).
        change (keypair_item_rep CSw (k, K)) with (keypair_rep CSw k K).
        rewrite (prot3_noise_kp_rc_split CSw k K), prot3_noise_kp_rc_uint.
        rewrite (shim_state_split gv S). entailer!. }
      { exfalso. apply Int.one_not_zero; assumption. }
    + forward_if (PROP () LOCAL (temp I._keypair k)
        SEP (shim_core gv S; refwarn gv;
             data_at Ews tuint (Vint (rc_add1 (kp_refs K)))
               (field_address t_kp (DOT I._refcount DOT I._refcount) k);
             prot3_noise_kp_krest CSw k K; iter_sepcon (keypair_item_rep CSw) (adel KS k); itable sht tab T)).
      { exfalso. apply H; reflexivity. }
      { forward. entailer!. }
      forward. unfold kp_get. rewrite if_false by auto. rewrite HK, Hr. cbn [fst snd].
      unfold keypairs_rep. rewrite (prot3_noise_kp_upd _ _ K _ _ HK).
      change (keypair_item_rep CSw (k, kp_set_refs K (rc_add1 (kp_refs K))))
        with (keypair_rep CSw k (kp_set_refs K (rc_add1 (kp_refs K)))).
      rewrite (prot3_noise_kp_rc_split CSw k (kp_set_refs K (rc_add1 (kp_refs K)))), prot3_noise_kp_krest_refs,
        prot3_noise_kp_rc_uint.
      rewrite (shim_state_split gv S). entailer!.
Qed.

Lemma prot3_noise_kp_tfree T k : t_free (t_remove T k) k = t_free T k.
Proof.
  unfold t_free, t_remove; simpl. f_equal.
  apply prot3_shim_table1_vremove_notin, prot3_shim_table1_vremove_notin'.
Qed.

Lemma prot3_noise_kp_body_free_kref :
  @semax_body (QPvarspecs Noise.qp) Gn Noise.CS
    WgNoise.noise.code.f_keypair_free_kref (keypair_free_kref_spec CSw).
Proof.
  start_function.
  assert_PROP (field_compatible t_kp [] k) as FC by (unfold keypair_rep; entailer!).
  assert (Hp: isptr k) by (destruct FC; auto).
  forward.
  match goal with |- context [temp I._keypair ?v] => replace v with k end.
  2:{ destruct k; try contradiction. simpl. rewrite prot3_noise_kp_ofs by rep_lia. reflexivity. }
  rewrite (prot3_noise_kp_open sht (d_itab D) T k Ews E FC H0).
  unfold peer_rep, device_rep. Intros.
  forward.
  match goal with |- context [temp I._t'1 ?v] => replace v with p by (rewrite <- H1; reflexivity) end.
  forward. rewrite H.
  forward.
  { unfold prot3_noise_kp_irest. Intros. entailer!. }
  sep_apply (derives_refl' _ _ (eq_sym (prot3_noise_kp_open sht (d_itab D) T k Ews E FC H0))).
  assert (Hin: In k (saddrs (t_D T))) by (eapply prot3_noise_kp_sfind_saddrs; eauto).
  forward_call (sht, d_itab D, T, k, @None (share * entry)).
  { change (raw_rep k None) with emp. rewrite emp_sepcon. cancel. }
  all: try (change (raw_ok T k None) with (In k (saddrs (t_D T))); exact Hin).
  change (raw_rep k None) with emp.
  assert (HE': sfind (t_D (t_remove T k)) k = Some (Ews, E)) by exact H0.
  sep_apply (prot3_noise_kp_pool_free sht (d_itab D) (t_remove T k) k Ews E HE'
               (prot3_shim_table1_vremove_notin' k (t_L T))).
  rewrite prot3_noise_kp_tfree.
  sep_apply (prot3_noise_kp_whole CSw k K E).
  forward_call (gv, S, k).
  { entailer!. }
  unfold peer_rep, device_rep. rewrite H. entailer!.
Qed.

Lemma prot3_noise_kp_body_put :
  @semax_body (QPvarspecs Noise.qp) Gn Noise.CS
    WgNoise.noise.code.f_wg_noise_keypair_put (wg_noise_keypair_put_spec CSw).
Proof.
  start_function.
  destruct H1 as [Hk|Hk].
  { subst k. forward_if (PROP (False) LOCAL () SEP ()).
    { forward. }
    { exfalso. apply H1; reflexivity. }
    }
  destruct (prot3_noise_kp_afind_in _ _ Hk) as [K HK].
  destruct (prot3_noise_kp_inpool _ _ _ _ H0 Hk) as (E & HE & HEp).
  assert (Hin: In k (saddrs (t_D T))) by (eapply prot3_noise_kp_sfind_saddrs; eauto).
  unfold keypairs_rep. rewrite (prot3_noise_kp_split _ _ _ _ HK).
  change (keypair_item_rep CSw (k, K)) with (keypair_rep CSw k K).
  rewrite prot3_noise_kp_rc_split.
  assert_PROP (field_compatible t_kp [] k) as FC by (sep_apply prot3_noise_kp_krest_fc; entailer!).
  assert (Hnn: k <> nullval) by (intro; subst k; destruct FC; contradiction).
  forward_if (PROP () LOCAL (gvars gv; temp I._keypair k; temp I._unreference_now (Val.of_bool unref))
    SEP (mem_mgr gv; shim_state gv S; field_at Ews t_kp (DOT I._refcount) (Vint (kp_refs K)) k;
         prot3_noise_kp_krest CSw k K; iter_sepcon (keypair_item_rep CSw) (adel KS k);
         peer_rep shp p P; device_rep shd wg D; itable sht (d_itab D) T)).
  { apply denote_tc_test_eq_split; [|apply valid_pointer_null].
    pull_left (itable sht (d_itab D) T). repeat apply sepcon_valid_pointer1.
    apply prot3_shim_table1_valid; auto. }
  { contradiction. }
  { forward. entailer!. }
  forward_if (PROP () LOCAL (gvars gv; temp I._keypair k)
    SEP (mem_mgr gv; shim_state gv S; field_at Ews t_kp (DOT I._refcount) (Vint (kp_refs K)) k;
         prot3_noise_kp_krest CSw k K; iter_sepcon (keypair_item_rep CSw) (adel KS k);
         peer_rep shp p P; device_rep shd wg D;
         itable sht (d_itab D) (if unref then t_remove T k else T))).
  { destruct unref; [| unfold typed_true in H1; simpl in H1; discriminate].
    rewrite (prot3_noise_kp_open sht (d_itab D) T k Ews E FC HE).
    unfold peer_rep, device_rep. Intros.
    forward.
    match goal with |- context [temp I._t'2 ?v] => replace v with p by (rewrite <- HEp; reflexivity) end.
    forward. rewrite H.
    forward.
    { unfold prot3_noise_kp_irest. Intros. entailer!. }
    sep_apply (derives_refl' _ _ (eq_sym (prot3_noise_kp_open sht (d_itab D) T k Ews E FC HE))).
    forward_call (sht, d_itab D, T, k, @None (share * entry)).
    { change (raw_rep k None) with emp. rewrite emp_sepcon. cancel. }
    all: try (change (raw_ok T k None) with (In k (saddrs (t_D T))); eapply prot3_noise_kp_sfind_saddrs; eauto).
    change (raw_rep k None) with emp.
    unfold peer_rep, device_rep. rewrite H. entailer!. }
  { forward. destruct unref; [unfold typed_false in H1; simpl in H1; discriminate|]. entailer!. }
  set (T1 := if unref then t_remove T k else T).
  assert (HE1: sfind (t_D T1) k = Some (Ews, E)) by (subst T1; destruct unref; exact HE).
  set (r' := rc_sub1 (kp_refs K)).
  assert (EW: kp_put k unref (mkKW KS T S) =
     if Int.eq r' Int.zero then mkKW (adel KS k) (t_free T1 k) (shim_free S)
     else mkKW (aupd KS k (kp_set_refs K r')) T1 S).
  { unfold kp_put. rewrite if_false by auto. cbn [kw_KS kw_T kw_S]. rewrite HK. reflexivity. }
  forward_loop (PROP () LOCAL (gvars gv; temp I._keypair k)
    SEP (mem_mgr gv; shim_state gv S; field_at Ews t_kp (DOT I._refcount) (Vint (kp_refs K)) k;
         prot3_noise_kp_krest CSw k K; iter_sepcon (keypair_item_rep CSw) (adel KS k);
         peer_rep shp p P; device_rep shd wg D; itable sht (d_itab D) T1))
    continue: (PROP () LOCAL ()
      SEP (mem_mgr gv; shim_state gv (kw_S (kp_put k unref (mkKW KS T S)));
           keypairs_rep CSw (kw_KS (kp_put k unref (mkKW KS T S)));
           peer_rep shp p P; device_rep shd wg D; itable sht (d_itab D) (kw_T (kp_put k unref (mkKW KS T S)))))
    break: (PROP () LOCAL ()
      SEP (mem_mgr gv; shim_state gv (kw_S (kp_put k unref (mkKW KS T S)));
           keypairs_rep CSw (kw_KS (kp_put k unref (mkKW KS T S)));
           peer_rep shp p P; device_rep shd wg D; itable sht (d_itab D) (kw_T (kp_put k unref (mkKW KS T S))))).
  { entailer!. }
  pose proof (prot3_noise_kp_fc_rc k FC) as FCr.
  rewrite prot3_noise_kp_rc_uint.
  rewrite (shim_state_split gv S). Intros.
  forward_call (gv, Ews, field_address t_kp (DOT I._refcount DOT I._refcount) k, kp_refs K).
  rewrite <- prot3_noise_kp_rc_uint. fold r'.
  sep_apply (prot3_noise_kp_fold_shim gv S).
  forward_if.
  { change (Int.repr 0) with Int.zero in *.
    repeat match goal with Hx: context [rc_sub1 (kp_refs K)] |- _ => fold r' in Hx end. fold r'.
    destruct (Int.eq r' Int.zero) eqn:Hz; [| unfold typed_true in *; simpl in *; discriminate].
    rewrite <- (prot3_noise_kp_krest_refs CSw k K r').
    sep_apply (derives_refl' _ _ (eq_sym (prot3_noise_kp_rc_split CSw k (kp_set_refs K r')))).
    forward_call (gv, S, k, kp_set_refs K r', E, shp, p, P, shd, wg, D, sht, T1).
    rewrite EW. cbn [kw_S kw_KS kw_T].
    unfold keypairs_rep. entailer!. }
  { change (Int.repr 0) with Int.zero in *.
    repeat match goal with Hx: context [rc_sub1 (kp_refs K)] |- _ => fold r' in Hx end. fold r'.
    destruct (Int.eq r' Int.zero) eqn:Hz; [unfold typed_false in *; simpl in *; discriminate |].
    forward. rewrite EW. cbn [kw_S kw_KS kw_T].
    unfold keypairs_rep. rewrite (prot3_noise_kp_upd _ _ K _ _ HK).
    change (keypair_item_rep CSw (k, kp_set_refs K r')) with (keypair_rep CSw k (kp_set_refs K r')).
    rewrite prot3_noise_kp_rc_split, prot3_noise_kp_krest_refs.
    change (kp_refs (kp_set_refs K r')) with r'. entailer!. }
  forward. entailer!.
  unfold POSTCONDITION, abbreviate. simpl RA_normal. unfold stackframe_of; simpl. intro rho.
  unfold PROPx, LOCALx, SEPx, local, lift1, liftx, lift; simpl. rewrite sepcon_emp. entailer!.
Qed.

End NoiseKP.

Theorem prot_bodies3_noise_kp :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body (QPvarspecs Noise.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_keypair_free_rcu (keypair_free_rcu_spec CSw)) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_keypair_free_kref (keypair_free_kref_spec CSw)) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_wg_noise_keypair_put (wg_noise_keypair_put_spec CSw)) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_wg_noise_keypair_get (wg_noise_keypair_get_spec CSw)).
Proof.
  intros. split; [|split; [|split]].
  - apply prot3_noise_kp_body_free_rcu.
  - apply prot3_noise_kp_body_free_kref.
  - apply prot3_noise_kp_body_put.
  - apply prot3_noise_kp_body_get.
Qed.
