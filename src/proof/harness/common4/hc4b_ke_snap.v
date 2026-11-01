(* (common4 group kents): the body of kents_snap *)
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
Require Import WgNoise.proof.harness.common4.hc4b_ke_snap1.
Require Import WgNoise.proof.harness.common4.hc4b_ke_snap2.
Require WgNoise.harness.x_cookie_mac.code.
Local Open Scope logic.

Lemma hc4b_ke_snap_pool_ptrs L (D: list (val * share * entry)) :
  iter_sepcon (pool_item_rep L) D |-- !! Forall isptr (saddrs D).
Proof.
  induction D as [|[[x sh] e] D IH]; simpl.
  - entailer!.
  - assert_PROP (Forall isptr (saddrs D)) as HF by (sep_apply IH; entailer!).
    unfold pool_item_rep at 1, entry_at.
    assert_PROP (isptr x) as Hx by (entailer!; match goal with Hc: field_compatible _ _ x |- _ => destruct Hc; auto end).
    entailer!.
Qed.

Lemma hc4b_ke_snap_succ L a : succ_in L a = nullval \/ In (succ_in L a) L.
Proof.
  induction L as [|x L IH]; simpl; [auto|].
  destruct (EqDec_val x a); [|destruct IH; auto].
  destruct L as [|y L]; simpl; auto.
Qed.

Lemma hc4b_ke_snap_succ_ptr T a :
  itable_wf T -> Forall isptr (saddrs (t_D T)) -> is_pointer_or_null (succ_in (t_L T) a).
Proof.
  intros (_ & HI & _) HF. destruct (hc4b_ke_snap_succ (t_L T) a) as [-> | Hin]; [simpl; auto|].
  apply HI in Hin. rewrite Forall_forall in HF. apply HF in Hin. destruct (succ_in _ _); try contradiction; exact I.
Qed.

Lemma hc4b_ke_snap_ted T a sh E : sfind (t_D T) a = Some (sh, E) -> t_entry_d T a = E.
Proof. intros F. unfold t_entry_d, t_entry. rewrite F. reflexivity. Qed.

Lemma hc4b_ke_snap_map_app T KE1 e : map (kent_snapped T) (KE1 ++ [e]) = map (kent_snapped T) KE1 ++ [kent_snapped T e].
Proof. rewrite map_app. reflexivity. Qed.

Section Body.
Variable CSw: compspecs.
#[local] Existing Instance CS4.

Lemma hc4b_ke_snap_ok :
  @semax_body [] hc4_G_dev_take CS4 WgNoise.harness.x_cookie_mac.code.f_kents_snap (kents_snap4_spec CSw).
Proof.
  start_function.
  assert_PROP (itable_wf T) as W by (unfold itable; entailer!).
  assert_PROP (Forall isptr (saddrs (t_D T))) as PP.
  { unfold itable. Intros. sep_apply hc4b_ke_snap_pool_ptrs. entailer!. }
  forward_loop
    (EX KE1: list kent4, EX KE2: list kent4, EX l': val,
      PROP (KE = KE1 ++ KE2)
      LOCAL (temp HC._l l')
      SEP (hc4b_ke_hf2_seg CSw l l' (map (kent_snapped T) KE1); kents_rep CSw l' KE2; itable sht tab T))
  continue:
    (EX KE1: list kent4, EX e: kent4, EX KE2: list kent4, EX nx: val,
      PROP (KE = KE1 ++ e :: KE2)
      LOCAL (temp HC._l (ke_addr e))
      SEP (hc4b_ke_hf2_seg CSw l (ke_addr e) (map (kent_snapped T) KE1); kent_cell CSw (kent_snapped T e) nx;
           kents_rep CSw nx KE2; itable sht tab T))
  break:
    (PROP () LOCAL ()
     SEP (kents_rep CSw l (map (kent_snapped T) KE); itable sht tab T)).
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
      assert_PROP (@field_compatible CS4 t_kent [] (ke_addr e)) as FC by (sep_apply hc4b_ke_hf2_fc; entailer!).
      assert (Hin: In (ke_addr e) (saddrs (t_D T)) /\ e_peer (t_entry_d T (ke_addr e)) <> Vundef).
      { match goal with HF: Forall _ (KE1 ++ _) |- _ => rewrite Forall_forall in HF; apply HF end.
        apply in_or_app; right; left; reflexivity. }
      destruct Hin as [Hin HPU].
      destruct (hc4b_ke_hf2_sfind_in _ _ Hin) as (sh & E & F).
      rewrite (hc4b_ke_snap_ted T (ke_addr e) sh E F) in HPU.
      assert (WS: readable_share sh).
      { apply writable_readable_share. destruct W as (_ & _ & _ & HF). pose proof (hc4b_ke_hf2_sfind_In _ _ _ _ F) as F'.
        rewrite Forall_forall in HF. apply (HF _ F'). }
      pose proof (hc4b_ke_snap_succ_ptr T (ke_addr e) W PP) as PNx.
      sep_apply (derives_refl' _ _ (hc4b_ke_hf2_take sht tab T (ke_addr e) sh E W F)). Intros.
      sep_apply (derives_refl' _ _ (hc4b_ke_snap_entry sh (ke_addr e) E (succ_in (t_L T) (ke_addr e)) (vin (ke_addr e) (t_L T)) FC)).
      assert_PROP (is_pointer_or_null (e_peer E)) as PE.
      { entailer!. match goal with Hv: value_fits _ (entry_val _ _ _) |- _ =>
          unfold entry_val in Hv; rewrite value_fits_eq in Hv; simpl in Hv; destruct Hv as [Hv _]; apply Hv; auto end. }
      unfold kent_cell at 1. Intros.
      sep_apply hc4b_ke_snap_kp_open. Intros lk r.
      match goal with Hk: kp_ok (ke_K e) |- _ => rename Hk into KO end.
      match goal with Hk: @field_compatible Noise.CS t_kp [] (ke_addr e) |- _ => rename Hk into FCN end.
      sep_apply (hc4b_ke_snap_blank_of (ke_addr e) (ke_snap e)).
      eapply semax_pre; [| eapply semax_post';
        [| apply (hc4b_ke_snap_one_ok (ke_addr e) sh E (succ_in (t_L T) (ke_addr e)) (vin (ke_addr e) (t_L T))
                   (ke_K e) lk r
                   (hc4b_ke_hf2_irest sht tab T (ke_addr e) * hc4b_ke_hf2_seg CSw l (ke_addr e) (map (kent_snapped T) KE1) *
                    kents_rep CSw nx KE2 * @malloc_token CSw Ews t_kent (ke_addr e) *
                    @field_at CKS Ews t_kent [StructField HC._next] nx (ke_addr e) * kent_pads (ke_addr e)));
           auto]].
      * entailer!.
      * Exists KE1 e KE2 nx.
        unfold kent_snapped, kent_cell. cbv zeta. cbn [ke_addr ke_K ke_snap].
        rewrite (hc4b_ke_snap_ted T (ke_addr e) sh E F).
        pose proof KO as (L1 & L2 & L3).
        rewrite hc4b_ke_snap_full_eq by auto.
        sep_apply (hc4b_ke_snap_kp_close (ke_addr e) (ke_K e) lk r FCN KO).
        sep_apply (derives_refl' _ _ (eq_sym (hc4b_ke_snap_entry sh (ke_addr e) E (succ_in (t_L T) (ke_addr e)) (vin (ke_addr e) (t_L T)) FC))).
        sep_apply (derives_refl' _ _ (eq_sym (hc4b_ke_hf2_take sht tab T (ke_addr e) sh E W F))).
        entailer!.
    + forward. destruct KE2 as [|e KE2]; simpl kents_rep.
      * Intros. subst. rewrite app_nil_r. entailer!.
        pose proof (hc4b_ke_hf2_seg_app CSw l nullval (map (kent_snapped T) KE1) []) as X. rewrite app_nil_r in X.
        eapply derives_trans; [|exact X]. simpl kents_rep. entailer!.
      * Intros nx. sep_apply hc4b_ke_hf2_nonnull. Intros. congruence.
  - Intros KE1 e KE2 nx. rewrite hc4b_ke_hf2_split. Intros. forward.
    { sep_apply hc4b_ke_hf2_rep_ptr. entailer!. }
    sep_apply (derives_refl' _ _ (eq_sym (hc4b_ke_hf2_split CSw (kent_snapped T e) nx))).
    pose proof (hc4b_ke_hf2_seg_snoc CSw l (map (kent_snapped T) KE1) (kent_snapped T e) nx) as X.
    change (ke_addr (kent_snapped T e)) with (ke_addr e) in X. sep_apply X.
    Exists (KE1 ++ [e]) KE2 nx. rewrite hc4b_ke_snap_map_app. entailer!. rewrite <- app_assoc. reflexivity.
  - unfold POSTCONDITION, abbreviate. simpl_ret_assert. entailer!.
Qed.

End Body.
