(* (common4 group kents): the body of kents_same_but_next. *)
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
Require WgNoise.harness.x_cookie_mac.code WgNoise.harness.x_keypairs.code.
Local Open Scope logic.

Module HKP := WgNoise.harness.x_keypairs.code.

Section SBN.
Variable CSw: compspecs.
#[local] Existing Instance CS4.

(* the cell without its snapshot field hashed0 *)
Definition hc4b_ke_sbn_nh (e: kent4) (s: ksnap) (nx: val) : mpred :=
  let k := ke_addr e in let E := ks_E s in let K := ks_K s in
  !! (@field_compatible CKS t_kent [] k) &&
  (@malloc_token CSw Ews t_kent k * kp_body_rep k (ke_K e) *
   (@field_at CKS Ews t_kent [StructField HC._peer0] (e_peer E) k *
    @field_at CKS Ews t_kent [StructField HC._next0] (ks_next s) k *
    @field_at CKS Ews t_kent [StructField HC._type0] (Vint (e_type E)) k *
    @field_at CKS Ews t_kent [StructField HC._index0] (Vint (e_index E)) k *
    @field_at CKS Ews t_kent [StructField HC._skey0] (bytes (sk_key (kp_send K))) k *
    @field_at CKS Ews t_kent [StructField HC._rkey0] (bytes (sk_key (kp_recv K))) k *
    @field_at CKS Ews t_kent [StructField HC._sbirth0] (Vlong (sk_birth (kp_send K))) k *
    @field_at CKS Ews t_kent [StructField HC._rbirth0] (Vlong (sk_birth (kp_recv K))) k *
    @field_at CKS Ews t_kent [StructField HC._svalid0] (Val.of_bool (sk_valid (kp_send K))) k *
    @field_at CKS Ews t_kent [StructField HC._rvalid0] (Val.of_bool (sk_valid (kp_recv K))) k *
    @field_at CKS Ews t_kent [StructField HC._scnt0] (Vlong (kp_scounter K)) k *
    @field_at CKS Ews t_kent [StructField HC._rcnt0] (Vlong (kp_rcounter K)) k *
    @field_at CKS Ews t_kent [StructField HC._bt0] (map Vlong (kp_backtrack K)) k *
    @field_at CKS Ews t_kent [StructField HC._remote_index0] (Vint (kp_rindex K)) k *
    @field_at CKS Ews t_kent [StructField HC._initiator0] (Val.of_bool (kp_init K)) k *
    @field_at CKS Ews t_kent [StructField HC._refs0] (Vint (kp_refs K)) k *
    @field_at CKS Ews t_kent [StructField HC._id0] (Vlong (kp_id K)) k) *
   @field_at CKS Ews t_kent [StructField HC._next] nx k * kent_pads k).

#[local] Instance hc4b_ke_sbn_cce1 : change_composite_env CKS CS4.
Proof. make_cs_preserve CKS CS4. Defined.

Lemma hc4b_ke_sbn_h_cs v k :
  @field_at CKS Ews t_kent [StructField HC._hashed0] v k = @field_at CS4 Ews t_kent [StructField HC._hashed0] v k.
Proof.
  exact (f_equal (fun f => f k)
    (@field_at_change_composite CKS CS4 _ Ews t_kent [StructField HC._hashed0] v v (JMeq_refl v) eq_refl)).
Qed.

Lemma hc4b_ke_sbn_split e s nx :
  ke_snap e = Some s ->
  kent_cell CSw e nx =
  @field_at CS4 Ews t_kent [StructField HC._hashed0] (Val.of_bool (ks_hashed s)) (ke_addr e) * hc4b_ke_sbn_nh e s nx.
Proof.
  intros Hs. unfold kent_cell, hc4b_ke_sbn_nh. rewrite Hs. unfold kent_snap_rep. rewrite hc4b_ke_sbn_h_cs.
  apply pred_ext; Intros; entailer!.
Qed.

Lemma hc4b_ke_sbn_fc e s nx :
  hc4b_ke_sbn_nh e s nx |-- !! (@field_compatible CS4 t_kent [] (ke_addr e)).
Proof.
  unfold hc4b_ke_sbn_nh. Intros. apply prop_right.
  apply (@field_compatible_change_composite CKS CS4 _ t_kent); [reflexivity | auto].
Qed.

Lemma hc4b_ke_sbn_ok :
  @semax_body [] (hc4_G_kents_same_but_next CSw) CS4 WgNoise.harness.x_keypairs.code.f_kents_same_but_next
    (kents_same_but_next4_spec CSw).
Proof.
  start_function.
  assert_PROP (itable_wf T) as W by (unfold itable; entailer!).
  forward_loop
    (EX KE1: list kent4, EX KE2: list kent4, EX l': val,
      PROP (KE = KE1 ++ KE2; forallb (kent_same_bn T) KE1 = true)
      LOCAL (temp HKP._l l'; temp HKP._t tab)
      SEP (hc4b_ke_hf2_seg CSw l l' KE1; kents_rep CSw l' KE2; itable sht tab T; vobjs CSw VO))
  continue:
    (EX KE1: list kent4, EX e: kent4, EX KE2: list kent4, EX nx: val,
      PROP (KE = KE1 ++ e :: KE2; forallb (kent_same_bn T) (KE1 ++ [e]) = true)
      LOCAL (temp HKP._l (ke_addr e); temp HKP._t tab)
      SEP (hc4b_ke_hf2_seg CSw l (ke_addr e) KE1; kent_cell CSw e nx; kents_rep CSw nx KE2; itable sht tab T;
           vobjs CSw VO))
  break:
    (PROP (forallb (kent_same_bn T) KE = true) LOCAL ()
     SEP (kents_rep CSw l KE; itable sht tab T; vobjs CSw VO)).
  - Exists (@nil kent4) KE l. entailer!. simpl. entailer!.
  - Intros KE1 KE2 l'. subst KE.
    assert_PROP (is_pointer_or_null l') as PN by (sep_apply hc4b_ke_hf2_rep_ptr; entailer!).
    forward_if.
    { destruct KE2 as [|e KE2]; simpl kents_rep; Intros.
      - subst. apply denote_tc_test_eq_split; apply valid_pointer_null.
      - subst. apply denote_tc_test_eq_split; [|apply valid_pointer_null].
        apply sepcon_valid_pointer1. apply hc4b_ke_hf2_valid.
        match goal with HF: Forall _ (KE1 ++ _) |- _ => rewrite Forall_forall in HF; apply HF end.
        apply in_or_app; right; left; reflexivity. }
    + destruct KE2 as [|e KE2]; simpl kents_rep.
      { Intros. subst. contradiction. }
      Intros nx. subst l'.
      assert (He: In e (KE1 ++ e :: KE2)) by (apply in_or_app; right; left; reflexivity).
      assert (HE := proj1 (Forall_forall _ _) H0 e He). destruct HE as (Hin & Hsn & Hvp).
      forward_call (e, nx, sht, tab, T, VO).
      destruct (ke_snap e) as [s|] eqn:Hs; [clear Hsn|congruence].
      forward_if (PROP () LOCAL (temp HKP._t'2 (Vint (if kent_same_bn T e then Int.zero else Int.one));
                  temp HKP._l (ke_addr e); temp HKP._t tab)
                  SEP (kent_cell CSw e nx; itable sht tab T; vobjs CSw VO;
                       hc4b_ke_hf2_seg CSw l (ke_addr e) KE1; kents_rep CSw nx KE2)).
      * forward. unfold kent_same_bn. rewrite Hs. destruct (kent_eqb_cur T e); [discriminate|]. entailer!.
      * rewrite (hc4b_ke_sbn_split e s nx Hs). Intros.
        assert_PROP (@field_compatible CS4 t_kent [] (ke_addr e)) as FC by (sep_apply hc4b_ke_sbn_fc; entailer!).
        forward.
        { entailer!. destruct (ks_hashed s); simpl; auto. }
        sep_apply (derives_refl' _ _ (eq_sym (hc4b_ke_sbn_split e s nx Hs))).
        forward_if (PROP () LOCAL (temp HKP._t'2 (Vint (if kent_same_bn T e then Int.zero else Int.one));
                  temp HKP._l (ke_addr e); temp HKP._t tab)
                  SEP (kent_cell CSw e nx; itable sht tab T; vobjs CSw VO;
                       hc4b_ke_hf2_seg CSw l (ke_addr e) KE1; kents_rep CSw nx KE2)).
        -- forward_call (sht, tab, T, ke_addr e).
           forward. forward.
           unfold kent_same_bn. rewrite Hs. destruct (kent_eqb_cur T e); [|contradiction H3; reflexivity].
           destruct (ks_hashed s); [|discriminate]. simpl orb. destruct (vin (ke_addr e) (t_L T)); entailer!.
        -- forward.
           unfold kent_same_bn. rewrite Hs. destruct (kent_eqb_cur T e); [|contradiction H3; reflexivity].
           destruct (ks_hashed s); [discriminate|]. simpl orb. entailer!.
      * forward_if.
        -- forward.
           destruct (kent_same_bn T e) eqn:Hb; [contradiction H3; reflexivity|].
           rewrite forallb_app, H2. simpl forallb. rewrite Hb. simpl andb.
           assert (F: kent_cell CSw e nx * kents_rep CSw nx KE2 |-- kents_rep CSw (ke_addr e) (e :: KE2))
             by (simpl kents_rep; Exists nx; entailer!).
           sep_apply F. sep_apply (hc4b_ke_hf2_seg_app CSw l (ke_addr e) KE1 (e :: KE2)). entailer!.
        -- forward.
           destruct (kent_same_bn T e) eqn:Hb; [|discriminate].
           Exists KE1 e KE2 nx. entailer!. rewrite forallb_app, H2. simpl. rewrite Hb. reflexivity.
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
  - forward. rewrite H1. entailer!.
Qed.

End SBN.
