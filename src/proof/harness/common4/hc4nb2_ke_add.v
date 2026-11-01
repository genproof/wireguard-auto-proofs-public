(* nb port of the hc4b_ke_add.v. The target closes with
     exact (hc4nb2_ke_add_ok hc4nb2_ke_add_split hc4nb2_ke_add_segC_ok hc4nb2_ke_add_segD_ok). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4a_nb_cs.
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require Import WgNoise.proof.harness.common4.hc4a_nb_ctx.
Require Import WgNoise.proof.harness.common4.hc4nb2_ke_hf.
Require Import WgNoise.proof.harness.common4.hc4nb2_ke_hf2.
Require Import WgNoise.proof.harness.common4.hc4nb2_ke_add_defs.
Require Import WgNoise.proof.harness.common4.hc4nb2_ke_add_lem.
Require WgNoise.harness.x_cookie_mac.code.
Local Open Scope logic.

(* hc4nb2_ke_add_split.v's statement *)
Definition hc4nb2_ke_add_split_P : Prop :=
  forall k: val,
  @data_at_ CS4nb Ews t_kent k |--
  !! (@field_compatible CKS t_kent [] k /\ @field_compatible Noise.CS t_kp [] k /\
      @field_compatible Noise.CS t_entry_s [] k) &&
  (@data_at_ Noise.CS Ews t_entry_s k * hc4nb2_ke_add_body0 k * kent_snap_rep k None *
   @field_at_ CKS Ews t_kent [StructField HC._next] k * kent_pads k).

(* hc4nb2_ke_add_segC.v's statement *)
Definition hc4nb2_ke_add_segC_P : Prop :=
  forall {Espec: OracleKind} (CSw: hc4nb2_ke_add_csw) (l k n i owner tab peers p: val) (fl: int)
    (gv: globals) (FR: mpred) (rest: statement) (R: ret_assert),
  @field_compatible Noise.CS t_kp [] k ->
  (forall K, kd_K_ok K ->
     @semax CS4nb Espec (hc4nb2_ke_add_Delta CSw)
       (PROPx [] (LOCALx (hc4nb2_ke_add_locs l k n i owner tab peers p fl gv) (SEPx [kp_body_rep k K; FR])))
       rest R) ->
  @semax CS4nb Espec (hc4nb2_ke_add_Delta CSw)
    (PROPx [] (LOCALx (hc4nb2_ke_add_locs l k n i owner tab peers p fl gv) (SEPx [hc4nb2_ke_add_body0 k; FR])))
    (hc4nb2_ke_add_sC rest) R.

(* hc4nb2_ke_add_segD.v's statement *)
Definition hc4nb2_ke_add_segD_P : Prop :=
  forall {Espec: OracleKind} (CSw: hc4nb2_ke_add_csw) (l k n i owner tab peers p: val) (fl: int)
    (gv: globals) (sht: share) (T: tstate) (PS: list (val * share * peer)) (K: keypair) (idx: int) (FR: mpred),
  readable_share sht -> peers_wf PS -> NoDup (map peer_addr4 PS) -> In owner (map peer_addr4 PS) ->
  In k (saddrs (t_D T)) -> hc4nb2_ke_add_slots_ok (saddrs (t_D T)) PS ->
  @semax CS4nb Espec (hc4nb2_ke_add_Delta CSw)
    (PROPx [] (LOCALx (hc4nb2_ke_add_locs l k n i owner tab peers p fl gv)
      (SEPx [peers_rep PS; itable sht tab T; FR])))
    hc4nb2_ke_add_sD
    (normal_ret_assert (EX c: Z,
      PROPx [0 <= c <= 3] (LOCALx (hc4nb2_ke_add_locs l k n i owner tab peers p fl gv)
        (SEPx [peers_rep (if negb (Int.eq fl Int.zero) then fill_peers PS (mkKD k owner K idx c) else PS);
               itable sht tab T; FR])))).

(* malloc's preconditions for struct kent at the abstract world CSw *)
Lemma hc4nb2_ke_add_mpre (CSw: compspecs) (HCS: cspecs_sub CS4nb CSw) :
  fold_right_and True [0 <= @sizeof CSw t_kent <= Ptrofs.max_unsigned;
                       @complete_legal_cosu_type (@cenv_cs CSw) t_kent = true;
                       @natural_aligned CSw natural_alignment t_kent = true].
Proof.
  cbn [fold_right_and]. pose proof HCS as [Hce _].
  assert (Hs: @sizeof CSw t_kent = 2392) by (apply (expr_lemmas4.cenv_sub_sizeof Hce); reflexivity).
  rewrite Hs. split; [rep_lia|]. split; [apply (semax.cenv_sub_complete_legal_cosu_type _ _ Hce); reflexivity|].
  split; [apply (hc4nb2_ke_hf_natural_aligned HCS); reflexivity | exact I].
Qed.

(* forward_call of malloc, step by step (fwd_call' with our own argument and precondition proofs) *)
Ltac hc4nb2_ke_add_msetup W VL :=
  prove_call_setup1 funspec_sub_refl;
  [ .. |
    match goal with |- call_setup1 _ _ _ _ _ _ _ _ _ _ _ _ _ ?A _ _ _ _ _ _ -> _ =>
      check_witness_type (@nil Type) A W end;
    let H := fresh "SetupOne" in intro H;
    match goal with |- @semax ?CS _ _ (PROPx ?P (LOCALx ?L (SEPx ?R'))) _ _ =>
      let Frame := fresh "Frame" in evar (Frame: list mpred);
      exploit (call_setup2_i _ _ _ _ _ _ _ _ R' R' _ _ _ _ (@nil Type) _ _ _ _ _ _ _ H W Frame); clear H end;
    simpl functors.MixVariantFunctor._functor;
    [ try_convertPreElim | check_prove_local2ptree | VL | auto 50 with derives | check_gvars_spec
    | cancel_for_forward_call | ] ].

Ltac hc4nb2_ke_add_my tpre :=
  let H := fresh in intro H;
  eapply (semax_call_id1_y_wow H);
  clear H;
  lazymatch goal with Frame := _ : list mpred |- _ => try clear Frame end;
  [ check_result_type | check_result_type
  | apply Coq.Init.Logic.I | apply Coq.Init.Logic.I | reflexivity
  | (clear; let H := fresh in intro H; inversion H)
  | match_postcondition
  | prove_delete_temp
  | prove_delete_temp
  | unify_postcondition_exps
  | tpre ].

Definition hc4nb2_ke_add_go (peers p: val) : bool :=
  if eq_dec peers nullval then (if eq_dec p nullval then false else true) else true.

Lemma hc4nb2_ke_add_sT1 T a E idx : saddrs (t_D (t_insert (t_add T a Ews E) a idx)) = a :: saddrs (t_D T).
Proof. rewrite hc4nb2_ke_add_saddrs_insert. reflexivity. Qed.

Lemma hc4nb2_ke_add_S S KD idx : shim_u32 (kents_S S KD) idx = shim_u32 S idx.
Proof. destruct KD; reflexivity. Qed.

(* the rest of the state while the keypair's fields are drawn and the slot is filled *)
Definition hc4nb2_ke_add_FR (CSw: compspecs) (k: val) (KD: list kdraw) (peers: val) (NS: list hnode4) (gv: globals)
    (S: shim) (w: list int64) : mpred :=
  kent_snap_rep k None * @field_at_ CKS Ews t_kent (DOT HC._next) k * kent_pads k * @malloc_token CSw Ews t_kent k *
  kents_rep CSw (kents_head KD) (map kd_kent KD) * hnodes_rep4 CSw peers NS * shim_state4 gv S w * mem_mgr gv.

Section Main.
Variable CSw: hc4nb2_ke_add_csw.
#[local] Existing Instance CS4nb.

#[local] Instance hc4nb2_ke_add_cce2 : change_composite_env Noise.CS CS4nb.
Proof. make_cs_preserve Noise.CS CS4nb. Defined.
#[local] Instance hc4nb2_ke_add_cce1' : change_composite_env CKS CS4nb.
Proof. make_cs_preserve CKS CS4nb. Defined.

Lemma hc4nb2_ke_add_next_ k : @field_at_ CKS Ews t_kent (DOT HC._next) k = @field_at_ CS4nb Ews t_kent (DOT HC._next) k.
Proof. exact (f_equal (fun f => f k) (@field_at__change_composite CKS CS4nb _ Ews t_kent (DOT HC._next) eq_refl)). Qed.

Lemma hc4nb2_ke_add_next v k : @field_at CS4nb Ews t_kent (DOT HC._next) v k = @field_at CKS Ews t_kent (DOT HC._next) v k.
Proof.
  symmetry. exact (f_equal (fun f => f k)
    (@field_at_change_composite CKS CS4nb _ Ews t_kent (DOT HC._next) v v (JMeq_refl v) eq_refl)).
Qed.

(* the entry of the keypair at k, as a field of struct noise_keypair (kp = &k->kp = k) *)
Lemma hc4nb2_ke_add_e2kp sh v k : @field_compatible CS4nb t_kp [] k ->
  @data_at Noise.CS sh t_entry_s v k = @field_at CS4nb sh t_kp (DOT I._entry) v k.
Proof.
  intros FC. rewrite (@field_at_data_at CS4nb).
  rewrite (@field_address_offset CS4nb) by auto with field_compatible.
  assert (Hp: isptr k) by (destruct FC; auto).
  change (@nested_field_offset CS4nb t_kp (DOT I._entry)) with 0.
  rewrite isptr_offset_val_zero by auto.
  exact (f_equal (fun f => f k)
    (@data_at_change_composite Noise.CS CS4nb _ sh t_entry_s v v (JMeq_refl _) eq_refl)).
Qed.

Lemma hc4nb2_ke_add_e2kp_ sh k : @field_compatible CS4nb t_kp [] k ->
  @data_at_ Noise.CS sh t_entry_s k = @field_at_ CS4nb sh t_kp (DOT I._entry) k.
Proof.
  intros FC. unfold field_at_, data_at_. exact (hc4nb2_ke_add_e2kp sh _ k FC).
Qed.

(* the entry after kents_add's four stores: the raw entry of the insertion *)
Lemma hc4nb2_ke_add_raw owner k : @field_compatible CS4nb t_kp [] k ->
  @field_at CS4nb Ews t_kp (DOT I._entry)
    (owner, (Vlong (Int64.repr (Int.signed (Int.repr 0))), (Vint Int.zero, (Vint (Int.repr 2),
      snd (snd (snd (snd (default_val (nested_field_type t_kp (DOT I._entry)))))))))) k |--
  WgNoise.proof.protocol4.prot_specs4.raw_entry Ews k (mkEntry owner IDX_KEYPAIR Int.zero).
Proof.
  intros FC. unfold WgNoise.proof.protocol4.prot_specs4.raw_entry.
  exact (derives_refl' _ _ (eq_sym (hc4nb2_ke_add_e2kp Ews _ k FC))).
Qed.

Lemma hc4nb2_ke_add_main (HS: hc4nb2_ke_add_split_P) (HC: hc4nb2_ke_add_segC_P) (HD: hc4nb2_ke_add_segD_P)
  (HCS: cspecs_sub CS4nb CSw) :
  @semax_body [] (hc4nb_G_kents_add CSw) CS4nb WgNoise.harness.x_cookie_mac.code.f_kents_add (kents_add4_spec CSw).
Proof.
  start_function.
  forward.
  forward_if (PROP () LOCAL (temp HC._t'1 (Val.of_bool (hc4nb2_ke_add_go peers p)); temp HC._l nullval; gvars gv;
      temp HC._t tab; temp HC._peers peers; temp HC._p p; temp HC._fill (Vint fl))
    SEP (itable sht tab T; hnodes_rep4 CSw peers NS; peers_rep PS; shim_state4 gv S w; mem_mgr gv)).
  { apply denote_tc_test_eq_split; [|apply valid_pointer_null].
    do 3 apply sepcon_valid_pointer1. apply sepcon_valid_pointer2. apply hc4nb2_ke_add_hn_valid. }
  { forward. entailer!. unfold hc4nb2_ke_add_go. rewrite if_false by auto. reflexivity. }
  { pose proof H0 as H0'. unfold kents_owners_ok in H0'. rewrite if_true in H0' by auto. destruct H0' as [HN HPS].
    destruct (eq_dec p nullval) as [Ep|Ep].
    - forward. entailer!.
    - forward.
      { entailer!. apply denote_tc_test_eq_split; [|apply valid_pointer_null].
        do 2 apply sepcon_valid_pointer1. apply (hc4nb2_ke_add_peers_valid PS p); auto. rewrite HPS. left; auto. }
      entailer!. unfold hc4nb2_ke_add_go. rewrite if_true, if_false by auto. destruct p; try contradiction; try reflexivity. simpl in PNp. subst. contradiction. }
  forward_if (EX nn: Z, PROP (0 <= nn <= Int64.max_unsigned; hc4nb2_ke_add_go peers p = false -> nn = 0)
    LOCAL (temp HC._t'2 (Vlong (Int64.repr nn)); temp HC._l nullval; gvars gv;
      temp HC._t tab; temp HC._peers peers; temp HC._p p; temp HC._fill (Vint fl))
    SEP (itable sht tab T; hnodes_rep4 CSw peers NS; peers_rep PS; shim_state4 gv S w; mem_mgr gv)).
  { forward_call tt. Intros nn. forward. Exists nn. entailer!. match goal with E: hc4nb2_ke_add_go _ _ = false, H2: typed_true _ _ |- _ => rewrite E in H2; discriminate H2 end. }
  { forward. Exists 0. entailer!. }
  Intros nn. forward.
  set (fb := negb (Int.eq fl Int.zero)).
  assert_PROP (NoDup (map peer_addr4 PS)) as HND by (sep_apply (hc4nb2_ke_add_peers_nodup PS H); entailer!).
  assert (Hsz: @sizeof CSw t_kent = 2392).
  { destruct HCS as [Hce _]. apply (expr_lemmas4.cenv_sub_sizeof Hce). reflexivity. }
  forward_loop (EX i: Z, EX KD: list kdraw,
      PROP (0 <= i <= nn; kents_draws_ok PS KD; kents_fresh T KD;
            hc4nb2_ke_add_slots_ok (saddrs (t_D (kents_T T KD))) (kents_PS fb PS KD))
      LOCAL (temp HC._i (Vlong (Int64.repr i)); temp HC._l (kents_head KD); temp HC._n (Vlong (Int64.repr nn));
        gvars gv; temp HC._t tab; temp HC._peers peers; temp HC._p p; temp HC._fill (Vint fl))
      SEP (kents_rep CSw (kents_head KD) (map kd_kent KD); itable sht tab (kents_T T KD);
           hnodes_rep4 CSw peers NS; peers_rep (kents_PS fb PS KD); shim_state4 gv (kents_S S KD) w; mem_mgr gv))
    continue: (EX i: Z, EX KD: list kdraw,
      PROP (0 <= i < nn; kents_draws_ok PS KD; kents_fresh T KD;
            hc4nb2_ke_add_slots_ok (saddrs (t_D (kents_T T KD))) (kents_PS fb PS KD))
      LOCAL (temp HC._i (Vlong (Int64.repr i)); temp HC._l (kents_head KD); temp HC._n (Vlong (Int64.repr nn));
        gvars gv; temp HC._t tab; temp HC._peers peers; temp HC._p p; temp HC._fill (Vint fl))
      SEP (kents_rep CSw (kents_head KD) (map kd_kent KD); itable sht tab (kents_T T KD);
           hnodes_rep4 CSw peers NS; peers_rep (kents_PS fb PS KD); shim_state4 gv (kents_S S KD) w; mem_mgr gv))
    break: (EX KD: list kdraw,
      PROP (kents_draws_ok PS KD; kents_fresh T KD)
      LOCAL (temp HC._l (kents_head KD); gvars gv)
      SEP (kents_rep CSw (kents_head KD) (map kd_kent KD); itable sht tab (kents_T T KD);
           hnodes_rep4 CSw peers NS; peers_rep (kents_PS fb PS KD); shim_state4 gv (kents_S S KD) w; mem_mgr gv)).
  { forward. Exists 0 (@nil kdraw). entailer!.
    - split; constructor.
    - simpl. entailer!. }
  { Intros i KD. forward_if.
    2: { forward. Exists KD. entailer!. }
    eapply semax_seq';
      [ hc4nb2_ke_add_msetup (t_kent, gv)
          ltac:(apply prop_right; rewrite Hsz; vm_compute; reflexivity);
        clear_Delta_specs; clear_MORE_POST;
        [ .. | hc4nb2_ke_add_my ltac:(apply (hc4nb2_ke_add_mpre CSw HCS)) ]
      | after_forward_call ].
    Intros k.
    destruct (eq_dec k nullval) as [Ek|Ek].
    { subst k. forward_if.
      { forward. Exists KD. entailer!. }
      { exfalso; auto. } }
    Intros.
    assert_PROP (malloc_compatible (@sizeof CSw t_kent) k) as Hm.
    { sep_apply (@malloc_token_local_facts CSw). entailer!. }
    rewrite Hsz in Hm.
    assert (Hk: isptr k) by (destruct k; try contradiction; exact I).
    sep_apply (derives_refl' _ _ (eq_sym (hc4nb2_ke_hf_data_at__cssub HCS Ews HC._kent noattr k eq_refl eq_refl eq_refl Hm))).
    sep_apply (HS k). Intros.
    freeze FRK := (hc4nb2_ke_add_body0 k) (kent_snap_rep k None) (@field_at_ CKS Ews t_kent _ k) (kent_pads k)
      (@malloc_token CSw Ews t_kent k).
    freeze FRR := (kents_rep _ _ _) (itable _ _ _) (hnodes_rep4 _ _ _) (peers_rep _) (shim_state4 _ _ _) (mem_mgr _).
    forward_if.
    { exfalso; auto. }
    forward.
    match goal with |- context [temp _ (offset_val ?o k)] =>
      replace (offset_val o k) with k by (symmetry; apply isptr_offset_val_zero; auto) end.
    thaw FRR.
    forward_if (EX owner: val, PROP (In owner (map peer_addr4 PS))
      LOCAL (temp HC._t'5 owner; temp HC._kp k; temp HC._k k; temp HC._i (Vlong (Int64.repr i));
        temp HC._l (kents_head KD); temp HC._n (Vlong (Int64.repr nn)); gvars gv; temp HC._t tab;
        temp HC._peers peers; temp HC._p p; temp HC._fill (Vint fl))
      SEP (FRZL FRK; @data_at_ Noise.CS Ews t_entry_s k; kents_rep CSw (kents_head KD) (map kd_kent KD);
           itable sht tab (kents_T T KD); hnodes_rep4 CSw peers NS; peers_rep (kents_PS fb PS KD);
           shim_state4 gv (kents_S S KD) w; mem_mgr gv)).
    { apply denote_tc_test_eq_split; [|apply valid_pointer_null].
      do 5 apply sepcon_valid_pointer1. apply sepcon_valid_pointer2. apply hc4nb2_ke_add_hn_valid. }
    { pose proof H0 as H0'. unfold kents_owners_ok in H0'. rewrite if_false in H0' by auto.
      destruct H0' as (HNN & HPS & _).
      forward_call (peers, NS). Intros j.
      assert (Hin: In (hn_p (Znth j NS)) (map peer_addr4 PS)).
      { unfold hnodes_peers4 in HPS. rewrite <- HPS. apply in_map. apply Znth_In. lia. }
      assert (Hin': In (hn_p (Znth j NS)) (map peer_addr4 (kents_PS fb PS KD))) by (rewrite hc4nb2_ke_add_PS_addrs; auto).
      assert_PROP (isptr (hn_p (Znth j NS))) as Hpp by (sep_apply (hc4nb2_ke_add_peers_ptr _ _ Hin'); entailer!).
      sep_apply (hc4nb2_ke_add_hn_p CSw peers NS j ltac:(lia)). Intros.
      forward.
      forward.
      Exists (hn_p (Znth j NS)). entailer!.
      sep_apply modus_ponens_wand. cancel. }
    { pose proof H0 as H0'. unfold kents_owners_ok in H0'. rewrite if_true in H0' by auto.
      destruct H0' as [HN HPS].
      destruct (eq_dec p nullval) as [Ep|Ep].
      { exfalso. assert (nn = 0); [apply H3; unfold hc4nb2_ke_add_go; rewrite !if_true by auto; reflexivity | lia]. }
      forward. Exists p. entailer!. rewrite HPS. left; auto. }
    Intros owner. forward.
    assert (FCk: @field_compatible CS4nb t_kp [] k).
    { apply (@field_compatible_change_composite Noise.CS CS4nb _ t_kp); [reflexivity | auto]. }
    sep_apply (derives_refl' _ _ (hc4nb2_ke_add_e2kp_ Ews k FCk)).
    forward. forward. forward. forward.
    sep_apply (hc4nb2_ke_add_raw owner k FCk).
    assert_PROP (~ In k (saddrs (t_D (kents_T T KD)))) as Hnk.
    { unfold WgNoise.proof.protocol4.prot_specs4.raw_entry. sep_apply hc4nb2_ke_add_notin. entailer!. }
    forward_call (gv, kents_S S KD, w, sht, tab, kents_T T KD, k, Some (Ews, mkEntry owner IDX_KEYPAIR Int.zero)).
    { simpl. split; auto. }
    Intros idx.
    change (P4.raw_add (kents_T T KD) k (Some (Ews, mkEntry owner IDX_KEYPAIR Int.zero)))
      with (t_add (kents_T T KD) k Ews (mkEntry owner IDX_KEYPAIR Int.zero)) in *.
    rewrite hc4nb2_ke_add_S.
    set (T1 := t_insert (t_add (kents_T T KD) k Ews (mkEntry owner IDX_KEYPAIR Int.zero)) k idx).
    set (PS1 := kents_PS fb PS KD).
    thaw FRK.
    match goal with |- semax _ _ ?c _ =>
      change c with (hc4nb2_ke_add_sC (Ssequence hc4nb2_ke_add_sD hc4nb2_ke_add_sL)) end.
    change Delta with (hc4nb2_ke_add_Delta CSw).
    eapply semax_pre; [| apply (HC Espec CSw (kents_head KD) k (Vlong (Int64.repr nn)) (Vlong (Int64.repr i)) owner tab
       peers p fl gv (peers_rep PS1 * itable sht tab T1 * hc4nb2_ke_add_FR CSw k KD peers NS gv (shim_u32 S idx) w)); auto].
    { unfold hc4nb2_ke_add_locs, hc4nb2_ke_add_FR. entailer!. }
    intros K HK.
    assert (HT1: saddrs (t_D T1) = k :: saddrs (t_D (kents_T T KD))) by apply hc4nb2_ke_add_sT1.
    eapply semax_seq'.
    { eapply semax_pre; [| apply (HD Espec CSw (kents_head KD) k (Vlong (Int64.repr nn)) (Vlong (Int64.repr i)) owner tab
         peers p fl gv sht T1 PS1 K idx (kp_body_rep k K * hc4nb2_ke_add_FR CSw k KD peers NS gv (shim_u32 S idx) w))].
      { apply andp_left2. apply andp_derives; [apply derives_refl|]. apply andp_derives; [apply derives_refl|].
        intro rho. unfold SEPx, fold_right_sepcon. cancel. }
      - apply writable_readable_share; auto.
      - apply hc4nb2_ke_add_PS_wf; auto.
      - unfold PS1. rewrite hc4nb2_ke_add_PS_addrs; auto.
      - unfold PS1. rewrite hc4nb2_ke_add_PS_addrs; auto.
      - rewrite HT1. left; auto.
      - rewrite HT1. eapply hc4nb2_ke_add_slots_mono; [|exact H7]. intros x Hx; right; auto. }
    Intros c.
    change (hc4nb2_ke_add_Delta CSw) with Delta.
    unfold hc4nb2_ke_add_sL, hc4nb2_ke_add_locs, hc4nb2_ke_add_FR. Intros.
    sep_apply (derives_refl' _ _ (hc4nb2_ke_add_next_ k)).
    forward.
    forward.
    set (d := mkKD k owner K idx c).
    assert (Hdraw: kents_draws_ok PS (d :: KD)).
    { destruct H5 as [HF HN]. split.
      - constructor; auto.
      - simpl. constructor; auto. intros Hin. apply Hnk. apply (proj2 (hc4nb2_ke_add_kT_incl T KD)). exact Hin. }
    assert (Hfr: kents_fresh T (d :: KD)) by (split; auto).
    assert (Hsl: hc4nb2_ke_add_slots_ok (saddrs (t_D (kents_T T (d :: KD)))) (kents_PS fb PS (d :: KD))).
    { rewrite hc4nb2_ke_add_saddrs_kT. simpl kents_PS.
      assert (Hm0: hc4nb2_ke_add_slots_ok (kd_addr d :: saddrs (t_D (kents_T T KD))) (kents_PS fb PS KD)).
      { eapply hc4nb2_ke_add_slots_mono; [|exact H7]. intros x Hx; right; auto. }
      destruct fb; auto. apply hc4nb2_ke_add_slots_fill; auto. left; reflexivity. }
    Exists i (d :: KD).
    unfold T1, PS1, fb in *.
    simpl kents_head. simpl kents_PS. simpl kents_S. simpl map. simpl kents_rep.
    entailer!.
    Exists (kents_head KD). unfold kent_cell. simpl ke_addr. simpl ke_K. simpl ke_snap.
    rewrite hc4nb2_ke_add_next. entailer!.
    apply derives_refl. }
  { Intros i KD. forward. Exists (i + 1) KD. entailer!. }
  Intros KD. forward. Exists KD. unfold fb. entailer!.
Qed.
End Main.

Lemma hc4nb2_ke_add_ok (HS: hc4nb2_ke_add_split_P) (HC: hc4nb2_ke_add_segC_P) (HD: hc4nb2_ke_add_segD_P) :
  forall CSw, cspecs_sub CS4nb CSw ->
  @semax_body [] (hc4nb_G_kents_add CSw) CS4nb WgNoise.harness.x_cookie_mac.code.f_kents_add (kents_add4_spec CSw).
Proof.
  intros CSw HCS. exact (hc4nb2_ke_add_main CSw HS HC HD HCS).
Qed.
