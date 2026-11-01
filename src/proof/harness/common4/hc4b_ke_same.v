(* (common4 group kents): the body of kents_same.
   Proved modulo one hypothesis HV on the lent objects (vobjs_addrs VO has no VKents / VKeypairs address whose
   byte 0 is not owned). *)
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
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require Import WgNoise.proof.harness.common4.hc4b_ke_hf.
Require Import WgNoise.proof.harness.common4.hc4b_ke_hf2.
Require Import WgNoise.proof.harness.common4.hc4b_ke_same_vp.
Require WgNoise.harness.x_cookie_mac.code.
Local Open Scope logic.

Section Same.
Variable CSw: compspecs.
#[local] Existing Instance CS4.

#[local] Instance hc4b_ke_same_cce1 : change_composite_env CKS CS4.
Proof. make_cs_preserve CKS CS4. Defined.

Lemma hc4b_ke_same_next0_cs v k :
  @field_at CKS Ews t_kent [StructField HC._next0] v k = @field_at CS4 Ews t_kent [StructField HC._next0] v k.
Proof.
  exact (f_equal (fun f => f k)
    (@field_at_change_composite CKS CS4 _ Ews t_kent [StructField HC._next0] v v (JMeq_refl v) eq_refl)).
Qed.

(* the snapshot's next0 field out of a kent's cell *)
Lemma hc4b_ke_same_n0 e nx s :
  ke_snap e = Some s ->
  kent_cell CSw e nx |--
  @field_at CS4 Ews t_kent [StructField HC._next0] (ks_next s) (ke_addr e) *
  (@field_at CS4 Ews t_kent [StructField HC._next0] (ks_next s) (ke_addr e) -* kent_cell CSw e nx).
Proof.
  intros Hs. unfold kent_cell at 1. Intros. unfold kent_snap_rep. rewrite Hs.
  rewrite hc4b_ke_same_next0_cs.
  rewrite <- !sepcon_assoc.
  pull_right (@field_at CS4 Ews t_kent [StructField HC._next0] (ks_next s) (ke_addr e)).
  apply sepcon_derives; [|apply derives_refl].
  apply -> wand_sepcon_adjoint. unfold kent_cell, kent_snap_rep. rewrite Hs. rewrite hc4b_ke_same_next0_cs.
  entailer!.
Qed.

Lemma hc4b_ke_same_succ L a : succ_in L a = nullval \/ In (succ_in L a) L.
Proof.
  induction L as [|x L IH]; simpl; [auto|].
  destruct (EqDec_val x a).
  - destruct L as [|y L]; simpl; auto.
  - destruct IH; auto.
Qed.

Lemma hc4b_ke_same_vpx (HV: forall VO x, In x (vobjs_addrs VO) -> In x (hc4b_ke_same_vobjs_vaddrs VO))
  VO sht tab T x P :
  Forall vobj_ok VO -> vp_ok (saddrs (t_D T) ++ vobjs_addrs VO) x ->
  P * vobjs CSw VO * itable sht tab T |-- valid_pointer x.
Proof.
  intros HF Hx. rewrite (sepcon_comm P), sepcon_assoc.
  apply (hc4b_ke_same_vp_ok CSw VO (saddrs (t_D T)) x).
  - auto.
  - destruct Hx as [-> | Hx]; [auto|]. apply in_app_or in Hx. destruct Hx; auto.
  - intros Hin. apply hc4b_ke_hf2_valid; auto.
Qed.

Lemma hc4b_ke_same_nn own T e : Forall (vp_ok own) (kent_ptrs T e) -> Forall (vp_ok own) (kent_ptrs_nn T e).
Proof.
  unfold kent_ptrs, kent_ptrs_nn. destruct (ke_snap e); [|auto].
  intros H. inversion H; subst. match goal with H: Forall _ (_ :: _) |- _ => inversion H; subst end. auto.
Qed.

Lemma hc4b_ke_same_ptrs (P: val -> Prop) T e s : ke_snap e = Some s -> Forall P (kent_ptrs T e) -> P (ks_next s).
Proof.
  intros Hs H. unfold kent_ptrs in H. rewrite Hs in H. rewrite Forall_forall in H. apply H. simpl. tauto.
Qed.

Lemma hc4b_ke_same_cmp a b : is_pointer_or_null a -> is_pointer_or_null b ->
  force_val (sem_cast_i2bool (force_val (sem_cmp_pp Cne a b))) = Vint (if veqb b a then Int.zero else Int.one).
Proof.
  intros Ha Hb. unfold veqb. destruct (eq_dec b a) as [E|NE].
  - subst. destruct a; try contradiction; simpl in Ha; try subst.
    + reflexivity.
    + unfold sem_cmp_pp; simpl. destruct (eq_block b b); [|contradiction].
      rewrite Ptrofs.eq_true. reflexivity.
  - destruct a; try contradiction; destruct b; try contradiction; simpl in Ha, Hb; try subst.
    + exfalso; apply NE; reflexivity.
    + reflexivity.
    + reflexivity.
    + unfold sem_cmp_pp; simpl. destruct (eq_block b0 b); [|reflexivity].
      subst. destruct (Ptrofs.eq i i0) eqn:Q; [|reflexivity].
      apply Ptrofs.same_if_eq in Q. subst. exfalso; apply NE; reflexivity.
Qed.

Lemma hc4b_ke_same_fold l KE1 e nx KE2 :
  hc4b_ke_hf2_seg CSw l (ke_addr e) KE1 * kent_cell CSw e nx * kents_rep CSw nx KE2 |--
  kents_rep CSw l (KE1 ++ e :: KE2).
Proof.
  eapply derives_trans; [|apply (hc4b_ke_hf2_seg_app CSw l (ke_addr e) KE1 (e :: KE2))].
  simpl kents_rep. Exists nx. entailer!.
Qed.

Definition hc4b_ke_same_HV : Prop := forall VO x, In x (vobjs_addrs VO) -> In x (hc4b_ke_same_vobjs_vaddrs VO).

Lemma hc4b_ke_same_ok_HV (HV: hc4b_ke_same_HV) :
  @semax_body [] (hc4_G_kents_same CSw) CS4 WgNoise.harness.x_cookie_mac.code.f_kents_same (kents_same4_spec CSw).
Proof.
  start_function.
  assert_PROP (itable_wf T) as W by (unfold itable; entailer!).
  forward_loop
    (EX KE1: list kent4, EX KE2: list kent4, EX l': val,
      PROP (KE = KE1 ++ KE2; forallb (kent_same T) KE1 = true)
      LOCAL (temp HC._l l')
      SEP (hc4b_ke_hf2_seg CSw l l' KE1; kents_rep CSw l' KE2; vobjs CSw VO; itable sht tab T))
  continue:
    (EX KE1: list kent4, EX e: kent4, EX KE2: list kent4, EX nx: val,
      PROP (KE = KE1 ++ e :: KE2; forallb (kent_same T) (KE1 ++ [e]) = true)
      LOCAL (temp HC._l (ke_addr e))
      SEP (hc4b_ke_hf2_seg CSw l (ke_addr e) KE1; kent_cell CSw e nx; kents_rep CSw nx KE2; vobjs CSw VO;
           itable sht tab T))
  break:
    (PROP (forallb (kent_same T) KE = true) LOCAL ()
     SEP (kents_rep CSw l KE; itable sht tab T; vobjs CSw VO)).
  - Exists (@nil kent4) KE l. entailer!. simpl. entailer!.
  - Intros KE1 KE2 l'. subst KE.
    assert_PROP (is_pointer_or_null l') as PN by (sep_apply hc4b_ke_hf2_rep_ptr; entailer!).
    forward_if.
    { destruct KE2 as [|e KE2]; simpl kents_rep; Intros.
      - subst. apply denote_tc_test_eq_split; apply valid_pointer_null.
      - subst. apply denote_tc_test_eq_split; [|apply valid_pointer_null].
        apply hc4b_ke_hf2_valid.
        match goal with HF: Forall _ (KE1 ++ _) |- _ => rewrite Forall_forall in HF; apply HF end.
        apply in_or_app; right; left; reflexivity. }
    + destruct KE2 as [|e KE2]; simpl kents_rep.
      { Intros. subst. contradiction. }
      Intros nx. subst l'.
      assert (He: In e (KE1 ++ e :: KE2)) by (apply in_or_app; right; left; reflexivity).
      match goal with HF: Forall _ (KE1 ++ _) |- _ =>
        pose proof HF as HF'; rewrite Forall_forall in HF'; destruct (HF' e He) as (Hin & Hsn & Hptrs) end.
      destruct (ke_snap e) as [s|] eqn:Hs; [|contradiction].
      forward_call (e, nx, sht, tab, T, VO).
      { apply hc4b_ke_same_nn; auto. }
      assert_PROP (@field_compatible CS4 t_kent [] (ke_addr e)) as FC by (sep_apply hc4b_ke_hf2_fc; entailer!).
      forward_if (PROP () LOCAL (temp HC._t'2 (Vint (if kent_same T e then Int.zero else Int.one)); temp HC._l (ke_addr e))
                  SEP (kent_cell CSw e nx; itable sht tab T; vobjs CSw VO;
                       hc4b_ke_hf2_seg CSw l (ke_addr e) KE1; kents_rep CSw nx KE2)).
      * forward. entailer!. unfold kent_same. rewrite Hs.
        destruct (kent_eqb_cur T e); [discriminate|reflexivity].
      * assert (Hx1: vp_ok (saddrs (t_D T) ++ vobjs_addrs VO) (ks_next s)) by (exact (hc4b_ke_same_ptrs _ T e s Hs Hptrs)).
        assert (Hx2: vp_ok (saddrs (t_D T) ++ vobjs_addrs VO) (succ_in (t_L T) (ke_addr e))).
        { destruct (hc4b_ke_same_succ (t_L T) (ke_addr e)) as [X | X]; [left; exact X | right].
          apply in_or_app; left. destruct W as (_ & WI & _). apply WI; exact X. }
        assert_PROP (is_pointer_or_null (ks_next s)) as PN1.
        { go_lowerx. eapply derives_trans; [|apply VSU.valid_pointer_is_null_or_ptr].
          eapply derives_trans; [|apply (hc4b_ke_same_vpx HV VO sht tab T (ks_next s)
            (kent_cell CSw e nx * hc4b_ke_hf2_seg CSw l (ke_addr e) KE1 * kents_rep CSw nx KE2) H Hx1)].
          cancel. }
        assert_PROP (is_pointer_or_null (succ_in (t_L T) (ke_addr e))) as PN2.
        { go_lowerx. eapply derives_trans; [|apply VSU.valid_pointer_is_null_or_ptr].
          eapply derives_trans; [|apply (hc4b_ke_same_vpx HV VO sht tab T (succ_in (t_L T) (ke_addr e))
            (kent_cell CSw e nx * hc4b_ke_hf2_seg CSw l (ke_addr e) KE1 * kents_rep CSw nx KE2) H Hx2)].
          cancel. }
        destruct (hc4b_ke_hf2_sfind_in _ _ Hin) as (sh & E & F).
        assert (WS: readable_share sh).
        { apply writable_readable_share. destruct W as (_ & _ & _ & HW). pose proof (hc4b_ke_hf2_sfind_In _ _ _ _ F) as F'.
          rewrite Forall_forall in HW. apply (HW _ F'). }
        sep_apply (derives_refl' _ _ (hc4b_ke_hf2_take sht tab T (ke_addr e) sh E W F)). Intros.
        sep_apply (derives_refl' _ _ (hc4b_ke_hf2_entry sh (ke_addr e) E (succ_in (t_L T) (ke_addr e)) (vin (ke_addr e) (t_L T)) FC)).
        forward.
        sep_apply (derives_refl' _ _ (eq_sym (hc4b_ke_hf2_entry sh (ke_addr e) E (succ_in (t_L T) (ke_addr e)) (vin (ke_addr e) (t_L T)) FC))).
        sep_apply (derives_refl' _ _ (eq_sym (hc4b_ke_hf2_take sht tab T (ke_addr e) sh E W F))).
        sep_apply (hc4b_ke_same_n0 e nx s Hs). Intros.
        forward.
        sep_apply (wand_frame_elim (@field_at CS4 Ews t_kent [StructField HC._next0] (ks_next s) (ke_addr e)) (kent_cell CSw e nx)).
        unfold entry_val. forward.
        { entailer!. apply denote_tc_test_eq_split.
          - eapply derives_trans; [|apply (hc4b_ke_same_vpx HV VO sht tab T (succ_in (t_L T) (ke_addr e))
              (kent_cell CSw e nx * hc4b_ke_hf2_seg CSw l (ke_addr e) KE1 * kents_rep CSw nx KE2) H Hx2)].
            cancel.
          - eapply derives_trans; [|apply (hc4b_ke_same_vpx HV VO sht tab T (ks_next s)
              (kent_cell CSw e nx * hc4b_ke_hf2_seg CSw l (ke_addr e) KE1 * kents_rep CSw nx KE2) H Hx1)].
            cancel. }
        entailer!. rewrite hc4b_ke_same_cmp by auto. unfold kent_same. rewrite Hs.
        destruct (kent_eqb_cur T e); [reflexivity|]. exfalso; apply H3; reflexivity.
      * forward_if (PROP (kent_same T e = true) LOCAL (temp HC._l (ke_addr e))
                    SEP (kent_cell CSw e nx; itable sht tab T; vobjs CSw VO;
                         hc4b_ke_hf2_seg CSw l (ke_addr e) KE1; kents_rep CSw nx KE2)).
        -- forward.
           assert (Hk: kent_same T e = false).
           { destruct (kent_same T e); [|reflexivity].
             match goal with X: _ <> _ |- _ => exfalso; apply X; reflexivity end. }
           rewrite forallb_app. simpl. rewrite Hk, andb_false_r.
           entailer!. sep_apply (hc4b_ke_same_fold l KE1 e nx KE2). cancel.
        -- forward.
           assert (Hk: kent_same T e = true).
           { destruct (kent_same T e); [reflexivity|].
             match goal with X: Int.one = _ |- _ => discriminate X end. }
           entailer!.
        -- Exists KE1 e KE2 nx. entailer!. rewrite forallb_app, H2. simpl.
           match goal with X: kent_same T e = true |- _ => rewrite X end. reflexivity.
    + forward. destruct KE2 as [|e KE2]; simpl kents_rep.
      * Intros. subst. rewrite app_nil_r. entailer!.
        pose proof (hc4b_ke_hf2_seg_app CSw l nullval KE1 []) as X. rewrite app_nil_r in X.
        eapply derives_trans; [|exact X]. simpl kents_rep. entailer!.
      * Intros nx. sep_apply hc4b_ke_hf2_nonnull. Intros. congruence.
  - Intros KE1 e KE2 nx. rewrite hc4b_ke_hf2_split. Intros. forward.
    { sep_apply hc4b_ke_hf2_rep_ptr. entailer!. }
    sep_apply (derives_refl' _ _ (eq_sym (hc4b_ke_hf2_split CSw e nx))).
    sep_apply (hc4b_ke_hf2_seg_snoc CSw l KE1 e nx).
    Exists (KE1 ++ [e]) KE2 nx. entailer!. rewrite <- app_assoc. reflexivity.
  - forward. entailer!. rewrite H1. reflexivity.
Qed.

End Same.
