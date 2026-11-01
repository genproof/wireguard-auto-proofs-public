(* nb port of the hc4b_ke_hf2.v., (common4 group kents): the bodies of kents_free and kents_hashed. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4a_nb_cs.
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require Import WgNoise.proof.harness.common4.hc4nb2_ke_hf.
Require WgNoise.harness.x_cookie_mac.code WgNoise.harness.x_keypairs.code.
Local Open Scope logic.

Module HKP := WgNoise.harness.x_keypairs.code.

Section Free.
Variable CSw: compspecs.
#[local] Existing Instance CS4nb.

#[local] Instance hc4nb2_ke_hf2_cce1 : change_composite_env CKS CS4nb.
Proof. make_cs_preserve CKS CS4nb. Defined.
#[local] Instance hc4nb2_ke_hf2_cce2 : change_composite_env Noise.CS CS4nb.
Proof. make_cs_preserve Noise.CS CS4nb. Defined.

(* the cell without its list link *)
Definition hc4nb2_ke_hf2_nn (e: kent4) : mpred :=
  !! (@field_compatible CKS t_kent [] (ke_addr e)) &&
  (@malloc_token CSw Ews t_kent (ke_addr e) * kp_body_rep (ke_addr e) (ke_K e) *
   kent_snap_rep (ke_addr e) (ke_snap e) * kent_pads (ke_addr e)).

Lemma hc4nb2_ke_hf2_next_cs v k :
  @field_at CKS Ews t_kent [StructField HC._next] v k = @field_at CS4nb Ews t_kent [StructField HC._next] v k.
Proof.
  exact (f_equal (fun f => f k)
    (@field_at_change_composite CKS CS4nb _ Ews t_kent [StructField HC._next] v v (JMeq_refl v) eq_refl)).
Qed.

Lemma hc4nb2_ke_hf2_split e nx :
  kent_cell CSw e nx = @field_at CS4nb Ews t_kent [StructField HC._next] nx (ke_addr e) * hc4nb2_ke_hf2_nn e.
Proof.
  unfold kent_cell, hc4nb2_ke_hf2_nn. rewrite hc4nb2_ke_hf2_next_cs.
  apply pred_ext; Intros; entailer!.
Qed.

Lemma hc4nb2_ke_hf2_fc e nx :
  kent_cell CSw e nx |-- !! (@field_compatible CS4nb t_kent [] (ke_addr e)).
Proof.
  unfold kent_cell. Intros. apply prop_right.
  apply (@field_compatible_change_composite CKS CS4nb _ t_kent); [reflexivity | auto].
Qed.

Lemma hc4nb2_ke_hf2_whole (H: cspecs_sub CS4nb CSw) e nx :
  kent_cell CSw e nx * @data_at_ Noise.CS Ews t_entry_s (ke_addr e) |--
  @malloc_token CSw Ews t_kent (ke_addr e) * @data_at_ CSw Ews t_kent (ke_addr e).
Proof.
  sep_apply (hc4nb2_ke_hf_whole4 CSw e nx).
  assert_PROP (malloc_compatible (@sizeof CSw t_kent) (ke_addr e)) as Hm.
  { sep_apply (@malloc_token_local_facts CSw). entailer!. }
  assert (Hs: @sizeof CSw t_kent = @sizeof CS4nb t_kent).
  { destruct H as [Hce _]. apply (expr_lemmas4.cenv_sub_sizeof Hce). reflexivity. }
  rewrite Hs in Hm.
  unfold t_kent. rewrite <- (hc4nb2_ke_hf_data_at__cssub H Ews HC._kent noattr (ke_addr e)) by (auto; reflexivity).
  apply derives_refl.
Qed.

Lemma hc4nb2_ke_hf2_nonnull e nx : kent_cell CSw e nx |-- !! (ke_addr e <> nullval).
Proof.
  sep_apply hc4nb2_ke_hf2_fc. Intros. apply prop_right. intros E. rewrite E in H. destruct H; contradiction.
Qed.

Lemma hc4nb2_ke_hf2_rep_ptr l KE : kents_rep CSw l KE |-- !! is_pointer_or_null l.
Proof.
  destruct KE as [|e KE]; simpl kents_rep.
  - Intros. subst. apply prop_right. reflexivity.
  - Intros nx. subst. unfold kent_cell. Intros. apply prop_right.
    destruct H as [H _]. destruct (ke_addr e); try contradiction; exact I.
Qed.

Lemma hc4nb2_ke_hf_free_ok :
  cspecs_sub CS4nb CSw -> @semax_body [] (hc4_G_free CSw) CS4nb WgNoise.harness.x_cookie_mac.code.f_kents_free (kents_free4_spec CSw).
Proof.
  intros HCS. start_function.
  forward_while (EX l': val, EX KE': list kent4,
    PROP () LOCAL (temp HC._l l'; gvars gv)
    SEP (kents_rep CSw l' KE'; iter_sepcon (fun e => @data_at_ Noise.CS Ews t_entry_s (ke_addr e)) KE'; mem_mgr gv)).
  - Exists l KE. entailer!.
  - destruct KE' as [|e KE'']; simpl kents_rep.
    + entailer!.
    + Intros nx. sep_apply hc4nb2_ke_hf2_nonnull. entailer!.
      simpl iter_sepcon. apply denote_tc_test_eq_split; [|apply valid_pointer_null].
      apply sepcon_valid_pointer1. apply sepcon_valid_pointer2. apply sepcon_valid_pointer1.
      apply data_at_valid_ptr; [auto | simpl; lia].
  - destruct KE' as [|e KE'']; simpl kents_rep.
    + Intros. subst. contradiction.
    + Intros nx. subst l'. simpl iter_sepcon.
      rewrite hc4nb2_ke_hf2_split. Intros. forward.
      { sep_apply hc4nb2_ke_hf2_rep_ptr. entailer!. }
      sep_apply (derives_refl' _ _ (eq_sym (hc4nb2_ke_hf2_split e nx))).
      sep_apply (hc4nb2_ke_hf2_whole HCS e nx).
      assert (NN: ke_addr e <> nullval) by (destruct (ke_addr e); try contradiction; discriminate).
      forward_call (t_kent, ke_addr e, gv).
      { rewrite if_false by auto. cancel. }
      forward. Exists (nx, KE''). entailer!. apply derives_refl.
  - destruct KE' as [|e KE'']; simpl kents_rep.
    + Intros. forward. simpl iter_sepcon. entailer!.
    + Intros nx. sep_apply hc4nb2_ke_hf2_nonnull. Intros. congruence.
Qed.

(* ---- kents_hashed ---- *)

(* a list segment of kents from l to l' *)
Fixpoint hc4nb2_ke_hf2_seg (l l': val) (KE: list kent4) : mpred :=
  match KE with
  | [] => !! (l = l') && emp
  | e :: KE' => !! (l = ke_addr e) && EX nx: val, kent_cell CSw e nx * hc4nb2_ke_hf2_seg nx l' KE'
  end.

Lemma hc4nb2_ke_hf2_seg_app l l' KE1 KE2 :
  hc4nb2_ke_hf2_seg l l' KE1 * kents_rep CSw l' KE2 |-- kents_rep CSw l (KE1 ++ KE2).
Proof.
  revert l. induction KE1 as [|e KE1 IH]; intros l; simpl.
  - Intros. subst. cancel.
  - Intros nx. Exists nx. entailer!. apply IH.
Qed.

Lemma hc4nb2_ke_hf2_seg_snoc l KE1 e nx :
  hc4nb2_ke_hf2_seg l (ke_addr e) KE1 * kent_cell CSw e nx |-- hc4nb2_ke_hf2_seg l nx (KE1 ++ [e]).
Proof.
  revert l. induction KE1 as [|e1 KE1 IH]; intros l; simpl.
  - Intros. subst. Exists nx. entailer!.
  - Intros nx1. Exists nx1. entailer!. apply IH.
Qed.

Lemma hc4nb2_ke_hf2_cnt T KE1 e :
  kents_hashed_n T (KE1 ++ [e]) = kents_hashed_n T KE1 + (if vin (ke_addr e) (t_L T) then 1 else 0).
Proof.
  unfold kents_hashed_n. rewrite filter_app, Zlength_app. simpl. destruct (vin (ke_addr e) (t_L T)); reflexivity.
Qed.

Lemma hc4nb2_ke_hf2_cnt_bound T KE : 0 <= kents_hashed_n T KE <= Zlength KE.
Proof.
  unfold kents_hashed_n. split; [apply Zlength_nonneg|].
  rewrite !Zlength_correct. apply Nat2Z.inj_le. apply filter_length_le.
Qed.

Lemma hc4nb2_ke_hf2_split_at {A} (D: list (val * share * A)) a sh E (f: val * share * A -> mpred) :
  sfind D a = Some (sh, E) -> iter_sepcon f D = f (a, sh, E) * iter_sepcon f (sdel D a).
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; reflexivity|].
  rewrite (IH H); simpl. rewrite <- !sepcon_assoc, (sepcon_comm (f _) (f _)). reflexivity.
Qed.

Lemma hc4nb2_ke_hf2_sfind_in {A} (D: list (val * share * A)) a :
  In a (saddrs D) -> exists sh E, sfind D a = Some (sh, E).
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [contradiction|].
  destruct (EqDec_val x a); [eauto|]. destruct H; [congruence|auto].
Qed.

(* the table without the pool item at a *)
Definition hc4nb2_ke_hf2_irest (sht: share) (tab: val) (T: tstate) (a: val) : mpred :=
  !! itable_wf T &&
  (@data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab * iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) a)).

Lemma hc4nb2_ke_hf2_take sht tab T a sh E :
  itable_wf T -> sfind (t_D T) a = Some (sh, E) ->
  itable sht tab T = entry_at sh a E (succ_in (t_L T) a) (vin a (t_L T)) * hc4nb2_ke_hf2_irest sht tab T a.
Proof.
  intros W F. unfold itable, hc4nb2_ke_hf2_irest. rewrite (hc4nb2_ke_hf2_split_at _ _ _ _ _ F).
  unfold pool_item_rep at 1. apply pred_ext; entailer!.
Qed.

Lemma hc4nb2_ke_hf2_sfind_In {A} (D: list (val * share * A)) a sh E :
  sfind D a = Some (sh, E) -> In (a, sh, E) D.
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; auto|auto].
Qed.

Lemma hc4nb2_ke_hf2_valid P sht tab T a :
  In a (saddrs (t_D T)) -> P * itable sht tab T |-- valid_pointer a.
Proof.
  intros Ha. destruct (hc4nb2_ke_hf2_sfind_in _ _ Ha) as (sh & E & F).
  unfold itable. Intros. rewrite (hc4nb2_ke_hf2_split_at _ _ _ _ _ F).
  assert (writable_share sh).
  { destruct H as (_ & _ & _ & HF). apply hc4nb2_ke_hf2_sfind_In in F.
    rewrite Forall_forall in HF. apply (HF _ F). }
  unfold pool_item_rep, entry_at.
  apply sepcon_valid_pointer2. apply sepcon_valid_pointer2. apply sepcon_valid_pointer1.
  apply data_at_valid_ptr; [auto | simpl; lia].
Qed.

(* the entry of a kent's keypair, at the kent's address *)
Lemma hc4nb2_ke_hf2_entry sh l E nx h :
  @field_compatible CS4nb t_kent [] l ->
  entry_at sh l E nx h = @field_at CS4nb sh t_kent [StructField I._entry; StructField HC._kp] (entry_val E nx h) l.
Proof.
  intros FC. unfold entry_at. rewrite (@field_at_data_at CS4nb).
  rewrite (@field_address_offset CS4nb) by auto with field_compatible.
  assert (Hp: isptr l) by (destruct FC; auto).
  change (@nested_field_offset CS4nb t_kent [StructField I._entry; StructField HC._kp]) with 0.
  rewrite isptr_offset_val_zero by auto.
  exact (f_equal (fun f => f l)
    (@data_at_change_composite Noise.CS CS4nb _ sh t_entry_s (entry_val E nx h) (entry_val E nx h) (JMeq_refl _) eq_refl)).
Qed.

Lemma hc4nb2_ke_hf_hashed_ok :
  @semax_body [] hc4_G_none CS4nb WgNoise.harness.x_keypairs.code.f_kents_hashed (kents_hashed4_spec CSw).
Proof.
  start_function.
  assert_PROP (itable_wf T) as W by (unfold itable; entailer!).
  forward.
  forward_loop
    (EX KE1: list kent4, EX KE2: list kent4, EX l': val,
      PROP (KE = KE1 ++ KE2)
      LOCAL (temp HKP._n (Vlong (Int64.repr (kents_hashed_n T KE1))); temp HKP._l l')
      SEP (hc4nb2_ke_hf2_seg l l' KE1; kents_rep CSw l' KE2; itable sht tab T))
  continue:
    (EX KE1: list kent4, EX e: kent4, EX KE2: list kent4, EX nx: val,
      PROP (KE = KE1 ++ e :: KE2)
      LOCAL (temp HKP._n (Vlong (Int64.repr (kents_hashed_n T (KE1 ++ [e])))); temp HKP._l (ke_addr e))
      SEP (hc4nb2_ke_hf2_seg l (ke_addr e) KE1; kent_cell CSw e nx; kents_rep CSw nx KE2; itable sht tab T))
  break:
    (PROP () LOCAL (temp HKP._n (Vlong (Int64.repr (kents_hashed_n T KE))))
     SEP (kents_rep CSw l KE; itable sht tab T)).
  - Exists (@nil kent4) KE l. entailer!. simpl. entailer!.
  - Intros KE1 KE2 l'. subst KE.
    assert_PROP (is_pointer_or_null l') as PN by (sep_apply hc4nb2_ke_hf2_rep_ptr; entailer!).
    forward_if.
    { destruct KE2 as [|e KE2]; simpl kents_rep; Intros.
      - subst. apply denote_tc_test_eq_split; apply valid_pointer_null.
      - subst. apply denote_tc_test_eq_split; [|apply valid_pointer_null].
        apply hc4nb2_ke_hf2_valid.
        match goal with HF: Forall _ (KE1 ++ _) |- _ => rewrite Forall_forall in HF; apply HF end.
        apply in_or_app; right; left; reflexivity. }
    + destruct KE2 as [|e KE2]; simpl kents_rep.
      { Intros. subst. contradiction. }
      Intros nx. subst l'.
      assert_PROP (@field_compatible CS4nb t_kent [] (ke_addr e)) as FC by (sep_apply hc4nb2_ke_hf2_fc; entailer!).
      assert (Hin: In (ke_addr e) (saddrs (t_D T))).
      { match goal with HF: Forall _ (KE1 ++ _) |- _ => rewrite Forall_forall in HF; apply HF end.
        apply in_or_app; right; left; reflexivity. }
      destruct (hc4nb2_ke_hf2_sfind_in _ _ Hin) as (sh & E & F).
      assert (WS: readable_share sh).
      { apply writable_readable_share. destruct W as (_ & _ & _ & HF). pose proof (hc4nb2_ke_hf2_sfind_In _ _ _ _ F) as F'.
        rewrite Forall_forall in HF. apply (HF _ F'). }
      sep_apply (derives_refl' _ _ (hc4nb2_ke_hf2_take sht tab T (ke_addr e) sh E W F)). Intros.
      sep_apply (derives_refl' _ _ (hc4nb2_ke_hf2_entry sh (ke_addr e) E (succ_in (t_L T) (ke_addr e)) (vin (ke_addr e) (t_L T)) FC)).
      forward.
      { entailer!. simpl. destruct (vin (ke_addr e) (t_L T)); simpl; auto. }
      sep_apply (derives_refl' _ _ (eq_sym (hc4nb2_ke_hf2_entry sh (ke_addr e) E (succ_in (t_L T) (ke_addr e)) (vin (ke_addr e) (t_L T)) FC))).
      sep_apply (derives_refl' _ _ (eq_sym (hc4nb2_ke_hf2_take sht tab T (ke_addr e) sh E W F))).
      forward_if (PROP () LOCAL (temp HKP._n (Vlong (Int64.repr (kents_hashed_n T (KE1 ++ [e])))); temp HKP._l (ke_addr e))
                  SEP (hc4nb2_ke_hf2_seg l (ke_addr e) KE1; kent_cell CSw e nx; kents_rep CSw nx KE2; itable sht tab T)).
      * forward. rewrite hc4nb2_ke_hf2_cnt. destruct (vin (ke_addr e) (t_L T)); [|discriminate]. entailer!.
      * forward. rewrite hc4nb2_ke_hf2_cnt. destruct (vin (ke_addr e) (t_L T)); [discriminate|]. entailer!.
      * Exists KE1 e KE2 nx. entailer!.
    + forward. destruct KE2 as [|e KE2]; simpl kents_rep.
      * Intros. subst. rewrite app_nil_r. entailer!.
        pose proof (hc4nb2_ke_hf2_seg_app l nullval KE1 []) as X. rewrite app_nil_r in X.
        eapply derives_trans; [|exact X]. simpl kents_rep. entailer!.
      * Intros nx. sep_apply hc4nb2_ke_hf2_nonnull. Intros. congruence.
  - Intros KE1 e KE2 nx. rewrite hc4nb2_ke_hf2_split. Intros. forward.
    { sep_apply hc4nb2_ke_hf2_rep_ptr. entailer!. }
    sep_apply (derives_refl' _ _ (eq_sym (hc4nb2_ke_hf2_split e nx))).
    sep_apply (hc4nb2_ke_hf2_seg_snoc l KE1 e nx).
    Exists (KE1 ++ [e]) KE2 nx. entailer!. rewrite <- app_assoc. reflexivity.
  - forward.
Qed.

End Free.
