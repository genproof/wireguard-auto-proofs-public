(* nb port of the hc4b_ke_k1.v., (common4 group kents): the body of kent_same_but_next. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_model3.
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
Require Import WgNoise.proof.harness.common4.hc4nb2_ke_k1_vp.
Require Import WgNoise.proof.harness.common4.hc4nb2_ke_k1_lem.
Require Import WgNoise.proof.harness.common4.hc4nb2_ke_k1_seg.
Require WgNoise.harness.x_cookie_mac.code.
Local Open Scope logic.

Module FC := WgNoise.harness.x_cookie_mac.code.

Section K1.
Variable CSw: compspecs.
#[local] Existing Instance CS4nb.

#[local] Instance hc4nb2_ke_k1_cce4 : change_composite_env Noise.CS CS4nb.
Proof. make_cs_preserve Noise.CS CS4nb. Defined.

Ltac hc4nb2_ke_k1_cc2 :=
  repeat match goal with
  | |- context [@field_at Noise.CS ?sh ?t ?gfs ?v ?p] =>
      rewrite (f_equal (fun f => f p) (@field_at_change_composite Noise.CS CS4nb hc4nb2_ke_k1_cce4 sh t gfs v v (JMeq_refl v) eq_refl))
  end.

Ltac hc4nb2_ke_k1_vpt CSw sht tab T k sh E VO x HVO VQ W F FC4 :=
  eapply derives_trans; [| apply (hc4nb2_ke_k1_vp CSw sht tab T k sh E VO x TT HVO VQ W F FC4)];
  unfold hc4nb2_ke_k1_ent; cancel.

Lemma hc4nb2_ke_k1_ok
  (HV: forall VO x, In x (vobjs_addrs VO) -> In x (hc4nb2_ke_k1_vobjs_vaddrs VO)) :
  @semax_body [] hc4_G_dev_same CS4nb FC.f_kent_same_but_next (kent_same_but_next4_spec CSw).
Proof.
  start_function.
  destruct e as [k K [s|]]; [|contradiction]. cbn [ke_addr ke_K ke_snap] in *.
  destruct (hc4nb2_ke_hf2_sfind_in _ _ H0) as (sh & E & F).
  assert_PROP (itable_wf T) as W by (unfold itable; entailer!).
  assert (TE: t_entry_d T k = E) by (unfold t_entry_d, t_entry; rewrite F; reflexivity).
  unfold kent_ptrs_nn in H2. cbn [ke_snap ke_addr] in H2. rewrite TE in H2. clear TE.
  pose proof (Forall_inv H2) as VP1. pose proof (Forall_inv (Forall_inv_tail H2)) as VP2. clear H2.
  sep_apply (hc4nb2_ke_k1_open CSw sht tab T k K s nx sh E W F). Intros lk r.
  rename H2 into FC4, H3 into FCn, H4 into OK, H5 into FCk.
  unfold hc4nb2_ke_k1_ent, hc4nb2_ke_k1_kp, hc4nb2_ke_k1_sn. repeat flatten_sepcon_in_SEP.
  hc4nb2_ke_k1_cc2.
  forward.
  match goal with |- context [temp FC._kp ?v] =>
    replace v with k by (destruct FC4 as [Pk _]; destruct k; try contradiction; simpl; rewrite Ptrofs.add_zero; reflexivity) end.
  assert (VQ1: e_peer (ks_E s) = nullval \/ In (e_peer (ks_E s)) (saddrs (t_D T)) \/
               In (e_peer (ks_E s)) (hc4nb2_ke_k1_vobjs_vaddrs VO)).
  { destruct VP1 as [? | Hin]; [auto|]. apply in_app_or in Hin. destruct Hin; auto. }
  assert (VQ2: e_peer E = nullval \/ In (e_peer E) (saddrs (t_D T)) \/ In (e_peer E) (hc4nb2_ke_k1_vobjs_vaddrs VO)).
  { destruct VP2 as [? | Hin]; [auto|]. apply in_app_or in Hin. destruct Hin; auto. }
  clear VP1 VP2.
  assert (RS: readable_share sh).
  { apply writable_readable_share. destruct W as (_ & _ & _ & HF). pose proof (hc4nb2_ke_hf2_sfind_In _ _ _ _ F) as F'.
    rewrite Forall_forall in HF. apply (HF _ F'). }
  assert_PROP (is_pointer_or_null (e_peer E)) as PN2.
  { go_lower. eapply derives_trans; [| apply hc4nb2_ke_k1_vpn].
    hc4nb2_ke_k1_vpt CSw sht tab T k sh E VO (e_peer E) H VQ2 W F FC4. }
  assert_PROP (is_pointer_or_null (e_peer (ks_E s))) as PN1.
  { go_lower. eapply derives_trans; [| apply hc4nb2_ke_k1_vpn].
    hc4nb2_ke_k1_vpt CSw sht tab T k sh E VO (e_peer (ks_E s)) H VQ1 W F FC4. }
  unfold entry_val.
  (* the || chain: segments LA, LB, LC *)
  repeat match goal with M := _ : statement |- _ => unfold abbreviate in M; subst M end.
  rewrite <- seq_assoc.
  eapply semax_seq'.
  { apply (hc4nb2_ke_k1_LC CSw k K s nx sht tab T VO sh E lk r); auto. }
  unfold hc4nb2_ke_k1_St. abbreviate_semax.

  pose proof OK as (OK1 & OK2 & OK3).
  assert (TE: t_entry_d T k = E) by (unfold t_entry_d, t_entry; rewrite F; reflexivity).
  assert (MOD: kent_eqb_cur T (mkKe k K (Some s)) = (hc4nb2_ke_k1_m17 T k E K s && int64s_eqb (kp_backtrack (ks_K s)) (kp_backtrack K))%bool).
  { unfold kent_eqb_cur. cbn [ke_addr ke_snap ke_K]. rewrite TE, hc4nb2_ke_k1_model. reflexivity. }
  set (b17 := hc4nb2_ke_k1_m17 T k E K s) in *. clearbody b17.
  assert_PROP (Zlength (kp_backtrack (ks_K s)) = 128) as LB.
  { entailer!. match goal with X: value_fits _ (map Vlong (kp_backtrack (ks_K s))) |- _ => exact (hc4nb2_ke_k1_vfl _ X) end. }
  forward_if.
  { match goal with Ht: typed_true tint _ |- _ => apply hc4nb2_ke_k1_tt in Ht; rename Ht into HM0 end.
    forward.
    rewrite MOD; try rewrite HM0; cbn [andb]. apply andp_right; [apply prop_right; reflexivity|].
    eapply derives_trans; [|apply sepcon_derives;
      [apply (hc4nb2_ke_k1_close4 CSw sht tab T k K s nx sh _ lk r W F FC4 FCn OK FCk) | apply derives_refl]].
    unfold hc4nb2_ke_k1_ent, hc4nb2_ke_k1_sn, entry_val, symkey_val. cancel. }
  match goal with Hf: typed_false tint _ |- _ => apply hc4nb2_ke_k1_tf in Hf; rename Hf into HM1 end.
  freeze FZ := - (field_at Ews t_kp (DOT I._receiving_counter) _ k) (field_at Ews t_kent (DOT HC._bt0) _ k).
  forward_for_simple_bound 128 (EX j: Z, PROP (sublist 0 j (kp_backtrack K) = sublist 0 j (kp_backtrack (ks_K s)))
    LOCAL (temp FC._kp k; temp FC._l k)
    SEP (field_at Ews t_kp (DOT I._receiving_counter) (Vlong (kp_rcounter K), (lk, map Vlong (kp_backtrack K))) k;
         field_at Ews t_kent (DOT HC._bt0) (map Vlong (kp_backtrack (ks_K s))) k; FRZL FZ))%assert.
  { entailer!. }
  { cbv beta. Intros. forward. forward.
    forward_if.
    { forward. thaw FZ.
      assert (X: int64s_eqb (kp_backtrack (ks_K s)) (kp_backtrack K) = false).
      { destruct (int64s_eqb (kp_backtrack (ks_K s)) (kp_backtrack K)) eqn:X; [|reflexivity].
        apply hc4nb2_ke_k1_i64s in X. rewrite X in *. contradiction. }
      rewrite MOD, X, andb_false_r. apply andp_right; [apply prop_right; reflexivity|].
      eapply derives_trans; [|apply sepcon_derives;
        [apply (hc4nb2_ke_k1_close4 CSw sht tab T k K s nx sh _ lk r W F FC4 FCn OK FCk) | apply derives_refl]].
      unfold hc4nb2_ke_k1_ent, hc4nb2_ke_k1_sn, entry_val, symkey_val. cancel. }
    { forward. entailer!.
      match goal with X: Int64.eq _ _ = true |- _ => apply hc4nb2_ke_k1_sub; auto; lia end. } }
  Intros. forward. thaw FZ.
  assert (X: int64s_eqb (kp_backtrack (ks_K s)) (kp_backtrack K) = true).
  { apply hc4nb2_ke_k1_i64s. rewrite !sublist_same in * by lia. auto. }
  rewrite MOD, X; try rewrite HM1; cbn [andb].
  apply andp_right; [apply prop_right; reflexivity|].
  eapply derives_trans; [|apply sepcon_derives;
    [apply (hc4nb2_ke_k1_close4 CSw sht tab T k K s nx sh _ lk r W F FC4 FCn OK FCk) | apply derives_refl]].
  unfold hc4nb2_ke_k1_ent, hc4nb2_ke_k1_sn, entry_val, symkey_val. cancel.
Qed.

End K1.
