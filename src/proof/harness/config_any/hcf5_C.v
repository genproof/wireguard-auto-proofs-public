(* law config_any: the six frame CHECKs C1..C6 (statements 31, 35, 38, 42, 85, 93):
   CHECK(dev_same(&ds, &w) && hs_same(&hs0, &p.handshake) && pr_same(&ps0, &p) && p.refcount.refcount == refs0 &&
         shim_same(&ss) && kents_same(kes) && it.head == head0)
   each from a state to itself (hcf5_SX1 for C1..C4, hcf5_SX5 for C5, C6).  The comparisons are true by the
   state's hcf5_same; their preconditions (valid pointers: lent objects VO) follow from hcf5_inv.  Each CHECK has
   its own temporaries but the same shape: prove ONE lemma over hcf5_F (any Px, X) per statement.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.config_any.hcf5_world.
Require Import WgNoise.proof.harness.config_any.hcf5_cut.
Require Import WgNoise.proof.harness.config_any.hcf5_globals.
Require Import WgNoise.proof.harness.config_any.hcf5_spec.
Require Import WgNoise.proof.harness.config_any.hcf5_defs.
Require Import WgNoise.proof.harness.config_any.hcf5_conv.
Require Import WgNoise.proof.harness.config_any.hcf5_pure.
Require WgNoise.harness.x_config_any.code.

#[local] Existing Instance W_config_any.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Helpers (prefix hcf5_c_)                                                *)
(* ---------------------------------------------------------------------- *)

Lemma hcf5_c_succ_in l a : succ_in l a = nullval \/ In (succ_in l a) l.
Proof.
  induction l as [| x l IH]; simpl; [left; reflexivity |].
  destruct (EqDec_val x a); [| destruct IH; [left | right; right]; auto].
  destruct l; simpl; [left; reflexivity | right; right; left; reflexivity].
Qed.

(* the valid-pointer facts of the six comparisons *)
Lemma hcf5_c_facts R L S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0 :
  hcf5_inv R L S w D P T KE qin -> hcf5_same L D P T KE S w D0 sn0 P0 r0 S0 w0 h0 -> itable_wf T ->
  Forall (vp_ok ([l_w L; d_ptab D] ++ vobjs_addrs [VPeer Tsh (l_p L) P; VItab Tsh (l_it L) T]))
    (dev_ptrs D0 (l_p L) D (l_p L)) /\
  In (hs_addr (l_p L)) (saddrs (t_D T)) /\
  Forall (vp_ok (hs_own (l_p L) T [VDev Tsh (l_w L) D])) (hs_ptrs sn0 (hs_snap_cur T (l_p L) P)) /\
  Forall (vp_ok (l_p L :: vobjs_addrs [VDev Tsh (l_w L) D; VItab Tsh (l_it L) T])) (pr_ptrs P0 P) /\
  Forall (fun e => In (ke_addr e) (saddrs (t_D T)) /\ ke_snap e <> None /\
                   Forall (vp_ok (saddrs (t_D T) ++ vobjs_addrs [VPeer Tsh (l_p L) P])) (kent_ptrs T e)) KE.
Proof.
  intros (Hrun & Hboot & Hw & Hdok & Hpok & Hslots & HTok & Hks) (Hdev & Hsn & Hpr & Hr & Hsh & Hke & Hh) Hwf.
  apply hcf5_dev_eqb_eq in Hdev. destruct Hdev as [-> _].
  apply hcf5_snap_eqb_eq in Hsn. subst sn0.
  apply hcf5_pr_eqb_val in Hpr. unfold prsnap_val in Hpr. inversion Hpr as [[Hd Hdd Hc Hp Hn Hl Hck Hi Hkk Hs1 Hm1 Hdk Hmk Hid Hk]].
  destruct Hdok as (Hdd0 & Hcc & Hpt & Hit).
  destruct Hpok as (Hpd & Hpk & Hsid & Hrs).
  destruct HTok as (HD & HKE & Htp & Hep & _).
  destruct Hwf as (_ & Hincl & _).
  assert (Hp_in: In (hs_addr (l_p L)) (saddrs (t_D T))) by (rewrite HD; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
  split; [| split; [exact Hp_in | split; [| split]]].
  - unfold dev_ptrs. rewrite Hdd0, Hcc, Hpt, Hit. unfold vp_ok; simpl.
    repeat apply Forall_cons; try apply Forall_nil; unfold vp_ok; cbn [In]; tauto.
  - unfold hs_ptrs, hs_ptrs_nn, hs_snap_cur, snap_of, hs_own, t_entry_d; cbn [sn_next sn_entry sn_hs].
    assert (Hnx: vp_ok (l_p L :: saddrs (t_D T) ++ vobjs_addrs [VDev Tsh (l_w L) D]) (succ_in (t_L T) (hs_addr (l_p L)))).
    { destruct (hcf5_c_succ_in (t_L T) (hs_addr (l_p L))) as [E | E]; [left; exact E |].
      right; right. apply in_or_app; left. apply Hincl; exact E. }
    assert (Hpo: vp_ok (l_p L :: saddrs (t_D T) ++ vobjs_addrs [VDev Tsh (l_w L) D]) (l_p L))
      by (right; left; reflexivity).
    assert (Hio: vp_ok (l_p L :: saddrs (t_D T) ++ vobjs_addrs [VDev Tsh (l_w L) D]) (id_addr (l_w L))).
    { right; right. apply in_or_app; right. unfold vobjs_addrs; cbn [map concat vobj_addrs app]. right; left; reflexivity. }
    unfold t_entry_d in Hep. rewrite Hep, Hsid.
    repeat apply Forall_cons; try apply Forall_nil; assumption.
  - unfold pr_ptrs. rewrite Hd, Hc, Hp, Hn, Hk, Hpd, Hpk.
    unfold hcf5_slots_ok in Hslots.
    inversion Hslots as [| ? ? Hc1 Hsl1]; subst. inversion Hsl1 as [| ? ? Hp1 Hsl2]; subst.
    inversion Hsl2 as [| ? ? Hn1 _]; subst.
    assert (G: forall v, v = nullval \/ In v (map ke_addr KE) ->
              vp_ok (l_p L :: vobjs_addrs [VDev Tsh (l_w L) D; VItab Tsh (l_it L) T]) v).
    { intros v [E | E]; [left; exact E |]. right; right.
      unfold vobjs_addrs; cbn [map concat vobj_addrs app]. right; right; right; right.
      rewrite app_nil_r, HD. apply in_or_app; right; apply in_or_app; left; exact E. }
    assert (Gw: vp_ok (l_p L :: vobjs_addrs [VDev Tsh (l_w L) D; VItab Tsh (l_it L) T]) (l_w L))
      by (right; simpl; tauto).
    assert (Gn: vp_ok (l_p L :: vobjs_addrs [VDev Tsh (l_w L) D; VItab Tsh (l_it L) T]) nullval)
      by (left; reflexivity).
    repeat (apply Forall_cons; [first [exact Gw | exact Gn | apply G; assumption] |]); apply Forall_nil.
  - unfold hcf5_ksnap_ok in Hks. rewrite Forall_forall in *. intros e He.
    destruct (Hks e He) as [Hs Hv]. split; [| split; [exact Hs |]].
    + rewrite HD. apply in_or_app; right; apply in_or_app; left. apply in_map; exact He.
    + rewrite Forall_forall in *. intros x Hx. destruct (Hv x Hx) as [E | [E | E]]; [left; exact E | |].
      * right. apply in_or_app; right. simpl. left; auto.
      * right. apply in_or_app; left. exact E.
Qed.

#[local] Instance hcf5_c_cceN : change_composite_env Noise.CS W_config_any.
Proof. make_cs_preserve Noise.CS W_config_any. Defined.

Lemma hcf5_c_refs sh p r :
  @field_at Noise.CS sh t_peer [StructField prot_repr3.I._refcount] (Vint r) p =
  @field_at W_config_any sh t_peer [StructField prot_repr3.I._refcount] (Vint r) p.
Proof.
  assert (Hc: cs_preserve_type Noise.CS W_config_any (@coeq _ _ hcf5_c_cceN) t_peer = true)
    by (vm_compute; reflexivity).
  assert (E := @field_at_change_composite Noise.CS W_config_any hcf5_c_cceN sh t_peer
                 [StructField prot_repr3.I._refcount] (Vint r) (Vint r) (JMeq_refl _) Hc).
  exact (f_equal (fun f => f p) E).
Qed.

(* peer_rep with its reference count at the world's compspecs *)
Definition hcf5_c_prest (sh: share) (p: val) (P: peer) : mpred :=
  (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] (p_device P) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p)%logic.

Lemma hcf5_c_split sh p P :
  peer_rep sh p P =
  (!! @field_compatible Noise.CS t_peer [] p &&
   (@field_at W_config_any sh t_peer [StructField prot_repr3.I._refcount] (Vint (p_refs P)) p *
    hcf5_c_prest sh p P))%logic.
Proof.
  rewrite <- hcf5_c_refs. unfold peer_rep, hcf5_c_prest.
  apply pred_ext; apply andp_derives; try apply derives_refl; cancel.
Qed.

(* the index table with its header at the world's compspecs *)
Lemma hcf5_c_itab sh tab T :
  itable sh tab T =
  (!! itable_wf T &&
   (@data_at W_config_any sh t_itab (hd nullval (t_L T)) tab * iter_sepcon (pool_item_rep (t_L T)) (t_D T)))%logic.
Proof.
  unfold itable. f_equal. f_equal.
  apply equal_f, (@data_at_change_composite Noise.CS W_config_any _ sh t_itab); [apply JMeq_refl | prove_cs_preserve_type].
Qed.

Lemma hcf5_c_vobjs1 (CS: compspecs) o : vobj_rep CS o = vobjs CS [o].
Proof. unfold vobjs. simpl. rewrite sepcon_emp. reflexivity. Qed.

Lemma hcf5_c_vobjs2 (CS: compspecs) o1 o2 : (vobj_rep CS o1 * vobj_rep CS o2)%logic = vobjs CS [o1; o2].
Proof. unfold vobjs. simpl. rewrite sepcon_emp. reflexivity. Qed.

Lemma hcf5_c_itable_fold sht tab T : itable_wf T ->
  (@data_at W_config_any sht t_itab (hd nullval (t_L T)) tab *
   iter_sepcon (pool_item_rep (t_L T)) (t_D T) |-- itable sht tab T)%logic.
Proof. intros HT. rewrite hcf5_c_itab. entailer!. Qed.

(* the table's first entry is a valid pointer (NULL or a pool entry) *)
Lemma hcf5_c_hd_valid sht tab T : itable sht tab T |-- valid_pointer (hd nullval (t_L T)).
Proof.
  unfold itable. Intros. destruct H as (_ & Hinc & _ & Hw).
  destruct (t_L T) as [| v l] eqn:EL; cbn [hd]; [apply valid_pointer_null |].
  assert (Hv: In v (saddrs (t_D T))) by (apply Hinc; left; reflexivity).
  unfold saddrs in Hv; apply in_map_iff in Hv; destruct Hv as ([[a sh] E] & Ha & Hin); cbn in Ha; subst a.
  rewrite Forall_forall in Hw; specialize (Hw _ Hin); cbn in Hw.
  apply sepcon_valid_pointer2.
  eapply derives_trans; [apply (iter_sepcon_in_true (pool_item_rep (v :: l)) (t_D T) _ Hin) |].
  apply sepcon_valid_pointer1. unfold pool_item_rep, entry_at.
  apply data_at_valid_ptr; [apply readable_nonidentity, writable_readable; auto | simpl; lia].
Qed.

Lemma hcf5_c_hd_pn sht tab T : itable sht tab T |-- !! is_pointer_or_null (hd nullval (t_L T)).
Proof.
  unfold itable. Intros. destruct H as (_ & Hinc & _ & Hw).
  destruct (t_L T) as [| v l] eqn:EL; cbn [hd]; [entailer! |].
  assert (Hv: In v (saddrs (t_D T))) by (apply Hinc; left; reflexivity).
  unfold saddrs in Hv; apply in_map_iff in Hv; destruct Hv as ([[a sh] E] & Ha & Hin); cbn in Ha; subst a.
  sep_apply (iter_sepcon_in_true (pool_item_rep (v :: l)) (t_D T) _ Hin).
  unfold pool_item_rep, entry_at. entailer!.
  match goal with X: field_compatible _ _ v |- _ => destruct X as [Hp _]; destruct v; try contradiction; exact I end.
Qed.

Lemma hcf5_c_cmp_self2 v : is_pointer_or_null v ->
  force_val (sem_cast tint tbool (eval_binop Oeq (tptr (Tstruct HF._index_hashtable_entry noattr))
    (tptr (Tstruct HF._index_hashtable_entry noattr)) v v)) = Vint Int.one.
Proof.
  intros Hv. destruct v; try contradiction.
  - cbn in Hv. subst. reflexivity.
  - unfold eval_binop, sem_binary_operation', sem_cmp; cbn. unfold sem_cmp_pp, Val.cmplu_bool; cbn.
    rewrite if_true by reflexivity. rewrite Ptrofs.eq_true. reflexivity.
Qed.

Lemma hcf5_c_C1 {Espec: OracleKind} x25519 gv L FR Px X R S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0 Rr :
  semax (hcf5_Delta x25519) (hcf5_F gv L FR Px X R S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0) hcf5_C1
    (overridePost (hcf5_F gv L FR Px X R S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0) Rr).
Proof.
  destruct Rr. unfold hcf5_Delta, hcf5_C1. simplify_func_tycontext. abbreviate_semax.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  2: { forward. apply ENTAIL_refl. }
  2: { unfold POSTCONDITION, abbreviate. rewrite overridePost_normal'. apply ENTAIL_refl. }
  unfold hcf5_F, hcf5_Fx. Intros.
  assert_PROP (itable_wf T) as WF by (unfold hcf5_core, itable; go_lowerx; entailer!).
  pose proof (hcf5_c_facts R L S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0 H0 H1 WF) as (Fdev & Fin & Fhs & Fpr & Fke).
  pose proof H1 as (Hdev & Hsn & Hpr & Hr & Hsh & Hke & Hh).
  pose proof H0 as (_ & _ & _ & (Hdd0 & Hcc & Hpt & Hit) & _).
  unfold hcf5_core, hcf5_globs, hcf5_lvars; cbn [app].
  (* dev_same(&ds, &w) *)
  gather_SEP 3 1.
  change (peer_rep Tsh (l_p L) P * itable Tsh (l_it L) T)%logic
    with (vobj_rep W (VPeer Tsh (l_p L) P) * vobj_rep W (VItab Tsh (l_it L) T))%logic.
  rewrite hcf5_c_vobjs2.
  rewrite <- Hpt.
  forward_call (Tsh, l_ds L, D0, l_p L, Tsh, l_w L, D, Tsh, l_p L, [VPeer Tsh (l_p L) P; VItab Tsh (l_it L) T]).
  { repeat apply Forall_cons; try apply Forall_nil; cbn [vobj_ok]; auto. }
  rewrite Hdev.
  rewrite <- hcf5_c_vobjs2. cbn [vobj_rep].
  (* hs_same(&hs0, &p.handshake) *)
  forward_if (temp HF5._t'7 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { change (device_rep Tsh (l_w L) D) with (vobj_rep W (VDev Tsh (l_w L) D)).
    rewrite (hcf5_c_vobjs1 W (VDev Tsh (l_w L) D)).
    change (peer_rep Tsh (l_p L) P) with (hs_mem true Tsh (l_p L) P).
    forward_call (Tsh, l_hs0 L, sn0, Tsh, l_p L, P, true, Tsh, l_it L, T, [VDev Tsh (l_w L) D]).
    { cancel. }
    { repeat apply Forall_cons; try apply Forall_nil; cbn [vobj_ok]; auto. }
    rewrite Hsn.
    rewrite <- hcf5_c_vobjs1. cbn [vobj_rep hs_mem].
    forward.
    entailer!. }
  repeat flatten_sepcon_in_SEP.
  (* pr_same(&ps0, &p) *)
  forward_if (temp HF5._t'9 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { gather_SEP 1 4.
    change (device_rep Tsh (l_w L) D * itable Tsh (l_it L) T)%logic
      with (vobj_rep W (VDev Tsh (l_w L) D) * vobj_rep W (VItab Tsh (l_it L) T))%logic.
    rewrite hcf5_c_vobjs2.
    forward_call (Tsh, l_ps0 L, P0, Tsh, l_p L, P, [VDev Tsh (l_w L) D; VItab Tsh (l_it L) T]).
    { repeat apply Forall_cons; try apply Forall_nil; cbn [vobj_ok]; auto. }
    rewrite Hpr.
    rewrite <- hcf5_c_vobjs2. cbn [vobj_rep]. repeat flatten_sepcon_in_SEP.
    forward.
    entailer!. }
  (* p.refcount.refcount == refs0 *)
  forward_if (temp HF5._t'11 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { rewrite (hcf5_c_split Tsh (l_p L) P). Intros.
    forward. forward. rewrite Hr, Int.eq_true. entailer!.
    rewrite (hcf5_c_split Tsh (l_p L) P). entailer!. }
  (* shim_same(&ss) *)
  forward_if (temp HF5._t'12 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { forward_call (gv, Tsh, l_ss L, S0, w0, S, w).
    rewrite Hsh. forward. entailer!. }
  (* kents_same(kes) *)
  forward_if (temp HF5._t'14 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { change (peer_rep Tsh (l_p L) P) with (vobj_rep W (VPeer Tsh (l_p L) P)).
    rewrite (hcf5_c_vobjs1 W (VPeer Tsh (l_p L) P)).
    forward_call (hcf5_khead KE, KE, Tsh, l_it L, T, [VPeer Tsh (l_p L) P]).
    { repeat apply Forall_cons; try apply Forall_nil; cbn [vobj_ok]; auto. }
    rewrite Hke. rewrite <- hcf5_c_vobjs1. cbn [vobj_rep].
    forward. entailer!. }
  (* it.head == head0 *)
  assert_PROP (is_pointer_or_null (hd nullval (t_L T))) as Hhd
    by (sep_apply (hcf5_c_hd_pn Tsh (l_it L) T); entailer!).
  forward_if (temp HF5._t'16 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { rewrite hcf5_c_itab. Intros.
    forward.
    sep_apply (hcf5_c_itable_fold Tsh (l_it L) T WF).
    forward.
    { entailer!. apply denote_tc_test_eq_split;
        (apply (derives_trans _ (itable Tsh (l_it L) T * TT)%logic); [cancel | apply sepcon_valid_pointer1; apply hcf5_c_hd_valid]). }
    rewrite Hh, (hcf5_c_cmp_self2 _ Hhd). entailer!. }
  (* if (!t) check_failed() *)
  forward_if.
  { match goal with Hx: _ |- _ => solve [inv Hx] end. }
  forward.
  rewrite Hpt.
  unfold hcf5_F, hcf5_Fx, hcf5_core, hcf5_globs, hcf5_lvars; cbn [app].
  entailer!.
Qed.

Lemma hcf5_c_C2 {Espec: OracleKind} x25519 gv L FR Px X R S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0 Rr :
  semax (hcf5_Delta x25519) (hcf5_F gv L FR Px X R S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0) hcf5_C2
    (overridePost (hcf5_F gv L FR Px X R S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0) Rr).
Proof.
  destruct Rr. unfold hcf5_Delta, hcf5_C2. simplify_func_tycontext. abbreviate_semax.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  2: { forward. apply ENTAIL_refl. }
  2: { unfold POSTCONDITION, abbreviate. rewrite overridePost_normal'. apply ENTAIL_refl. }
  unfold hcf5_F, hcf5_Fx. Intros.
  assert_PROP (itable_wf T) as WF by (unfold hcf5_core, itable; go_lowerx; entailer!).
  pose proof (hcf5_c_facts R L S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0 H0 H1 WF) as (Fdev & Fin & Fhs & Fpr & Fke).
  pose proof H1 as (Hdev & Hsn & Hpr & Hr & Hsh & Hke & Hh).
  pose proof H0 as (_ & _ & _ & (Hdd0 & Hcc & Hpt & Hit) & _).
  unfold hcf5_core, hcf5_globs, hcf5_lvars; cbn [app].
  (* dev_same(&ds, &w) *)
  gather_SEP 3 1.
  change (peer_rep Tsh (l_p L) P * itable Tsh (l_it L) T)%logic
    with (vobj_rep W (VPeer Tsh (l_p L) P) * vobj_rep W (VItab Tsh (l_it L) T))%logic.
  rewrite hcf5_c_vobjs2.
  rewrite <- Hpt.
  forward_call (Tsh, l_ds L, D0, l_p L, Tsh, l_w L, D, Tsh, l_p L, [VPeer Tsh (l_p L) P; VItab Tsh (l_it L) T]).
  { repeat apply Forall_cons; try apply Forall_nil; cbn [vobj_ok]; auto. }
  rewrite Hdev.
  rewrite <- hcf5_c_vobjs2. cbn [vobj_rep].
  (* hs_same(&hs0, &p.handshake) *)
  forward_if (temp HF5._t'18 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { change (device_rep Tsh (l_w L) D) with (vobj_rep W (VDev Tsh (l_w L) D)).
    rewrite (hcf5_c_vobjs1 W (VDev Tsh (l_w L) D)).
    change (peer_rep Tsh (l_p L) P) with (hs_mem true Tsh (l_p L) P).
    forward_call (Tsh, l_hs0 L, sn0, Tsh, l_p L, P, true, Tsh, l_it L, T, [VDev Tsh (l_w L) D]).
    { cancel. }
    { repeat apply Forall_cons; try apply Forall_nil; cbn [vobj_ok]; auto. }
    rewrite Hsn.
    rewrite <- hcf5_c_vobjs1. cbn [vobj_rep hs_mem].
    forward.
    entailer!. }
  repeat flatten_sepcon_in_SEP.
  (* pr_same(&ps0, &p) *)
  forward_if (temp HF5._t'20 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { gather_SEP 1 4.
    change (device_rep Tsh (l_w L) D * itable Tsh (l_it L) T)%logic
      with (vobj_rep W (VDev Tsh (l_w L) D) * vobj_rep W (VItab Tsh (l_it L) T))%logic.
    rewrite hcf5_c_vobjs2.
    forward_call (Tsh, l_ps0 L, P0, Tsh, l_p L, P, [VDev Tsh (l_w L) D; VItab Tsh (l_it L) T]).
    { repeat apply Forall_cons; try apply Forall_nil; cbn [vobj_ok]; auto. }
    rewrite Hpr.
    rewrite <- hcf5_c_vobjs2. cbn [vobj_rep]. repeat flatten_sepcon_in_SEP.
    forward.
    entailer!. }
  (* p.refcount.refcount == refs0 *)
  forward_if (temp HF5._t'22 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { rewrite (hcf5_c_split Tsh (l_p L) P). Intros.
    forward. forward. rewrite Hr, Int.eq_true. entailer!.
    rewrite (hcf5_c_split Tsh (l_p L) P). entailer!. }
  (* shim_same(&ss) *)
  forward_if (temp HF5._t'23 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { forward_call (gv, Tsh, l_ss L, S0, w0, S, w).
    rewrite Hsh. forward. entailer!. }
  (* kents_same(kes) *)
  forward_if (temp HF5._t'25 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { change (peer_rep Tsh (l_p L) P) with (vobj_rep W (VPeer Tsh (l_p L) P)).
    rewrite (hcf5_c_vobjs1 W (VPeer Tsh (l_p L) P)).
    forward_call (hcf5_khead KE, KE, Tsh, l_it L, T, [VPeer Tsh (l_p L) P]).
    { repeat apply Forall_cons; try apply Forall_nil; cbn [vobj_ok]; auto. }
    rewrite Hke. rewrite <- hcf5_c_vobjs1. cbn [vobj_rep].
    forward. entailer!. }
  (* it.head == head0 *)
  assert_PROP (is_pointer_or_null (hd nullval (t_L T))) as Hhd
    by (sep_apply (hcf5_c_hd_pn Tsh (l_it L) T); entailer!).
  forward_if (temp HF5._t'27 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { rewrite hcf5_c_itab. Intros.
    forward.
    sep_apply (hcf5_c_itable_fold Tsh (l_it L) T WF).
    forward.
    { entailer!. apply denote_tc_test_eq_split;
        (apply (derives_trans _ (itable Tsh (l_it L) T * TT)%logic); [cancel | apply sepcon_valid_pointer1; apply hcf5_c_hd_valid]). }
    rewrite Hh, (hcf5_c_cmp_self2 _ Hhd). entailer!. }
  (* if (!t) check_failed() *)
  forward_if.
  { match goal with Hx: _ |- _ => solve [inv Hx] end. }
  forward.
  rewrite Hpt.
  unfold hcf5_F, hcf5_Fx, hcf5_core, hcf5_globs, hcf5_lvars; cbn [app].
  entailer!.
Qed.

Lemma hcf5_c_C3 {Espec: OracleKind} x25519 gv L FR Px X R S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0 Rr :
  semax (hcf5_Delta x25519) (hcf5_F gv L FR Px X R S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0) hcf5_C3
    (overridePost (hcf5_F gv L FR Px X R S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0) Rr).
Proof.
  destruct Rr. unfold hcf5_Delta, hcf5_C3. simplify_func_tycontext. abbreviate_semax.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  2: { forward. apply ENTAIL_refl. }
  2: { unfold POSTCONDITION, abbreviate. rewrite overridePost_normal'. apply ENTAIL_refl. }
  unfold hcf5_F, hcf5_Fx. Intros.
  assert_PROP (itable_wf T) as WF by (unfold hcf5_core, itable; go_lowerx; entailer!).
  pose proof (hcf5_c_facts R L S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0 H0 H1 WF) as (Fdev & Fin & Fhs & Fpr & Fke).
  pose proof H1 as (Hdev & Hsn & Hpr & Hr & Hsh & Hke & Hh).
  pose proof H0 as (_ & _ & _ & (Hdd0 & Hcc & Hpt & Hit) & _).
  unfold hcf5_core, hcf5_globs, hcf5_lvars; cbn [app].
  (* dev_same(&ds, &w) *)
  gather_SEP 3 1.
  change (peer_rep Tsh (l_p L) P * itable Tsh (l_it L) T)%logic
    with (vobj_rep W (VPeer Tsh (l_p L) P) * vobj_rep W (VItab Tsh (l_it L) T))%logic.
  rewrite hcf5_c_vobjs2.
  rewrite <- Hpt.
  forward_call (Tsh, l_ds L, D0, l_p L, Tsh, l_w L, D, Tsh, l_p L, [VPeer Tsh (l_p L) P; VItab Tsh (l_it L) T]).
  { repeat apply Forall_cons; try apply Forall_nil; cbn [vobj_ok]; auto. }
  rewrite Hdev.
  rewrite <- hcf5_c_vobjs2. cbn [vobj_rep].
  (* hs_same(&hs0, &p.handshake) *)
  forward_if (temp HF5._t'29 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { change (device_rep Tsh (l_w L) D) with (vobj_rep W (VDev Tsh (l_w L) D)).
    rewrite (hcf5_c_vobjs1 W (VDev Tsh (l_w L) D)).
    change (peer_rep Tsh (l_p L) P) with (hs_mem true Tsh (l_p L) P).
    forward_call (Tsh, l_hs0 L, sn0, Tsh, l_p L, P, true, Tsh, l_it L, T, [VDev Tsh (l_w L) D]).
    { cancel. }
    { repeat apply Forall_cons; try apply Forall_nil; cbn [vobj_ok]; auto. }
    rewrite Hsn.
    rewrite <- hcf5_c_vobjs1. cbn [vobj_rep hs_mem].
    forward.
    entailer!. }
  repeat flatten_sepcon_in_SEP.
  (* pr_same(&ps0, &p) *)
  forward_if (temp HF5._t'31 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { gather_SEP 1 4.
    change (device_rep Tsh (l_w L) D * itable Tsh (l_it L) T)%logic
      with (vobj_rep W (VDev Tsh (l_w L) D) * vobj_rep W (VItab Tsh (l_it L) T))%logic.
    rewrite hcf5_c_vobjs2.
    forward_call (Tsh, l_ps0 L, P0, Tsh, l_p L, P, [VDev Tsh (l_w L) D; VItab Tsh (l_it L) T]).
    { repeat apply Forall_cons; try apply Forall_nil; cbn [vobj_ok]; auto. }
    rewrite Hpr.
    rewrite <- hcf5_c_vobjs2. cbn [vobj_rep]. repeat flatten_sepcon_in_SEP.
    forward.
    entailer!. }
  (* p.refcount.refcount == refs0 *)
  forward_if (temp HF5._t'33 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { rewrite (hcf5_c_split Tsh (l_p L) P). Intros.
    forward. forward. rewrite Hr, Int.eq_true. entailer!.
    rewrite (hcf5_c_split Tsh (l_p L) P). entailer!. }
  (* shim_same(&ss) *)
  forward_if (temp HF5._t'34 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { forward_call (gv, Tsh, l_ss L, S0, w0, S, w).
    rewrite Hsh. forward. entailer!. }
  (* kents_same(kes) *)
  forward_if (temp HF5._t'36 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { change (peer_rep Tsh (l_p L) P) with (vobj_rep W (VPeer Tsh (l_p L) P)).
    rewrite (hcf5_c_vobjs1 W (VPeer Tsh (l_p L) P)).
    forward_call (hcf5_khead KE, KE, Tsh, l_it L, T, [VPeer Tsh (l_p L) P]).
    { repeat apply Forall_cons; try apply Forall_nil; cbn [vobj_ok]; auto. }
    rewrite Hke. rewrite <- hcf5_c_vobjs1. cbn [vobj_rep].
    forward. entailer!. }
  (* it.head == head0 *)
  assert_PROP (is_pointer_or_null (hd nullval (t_L T))) as Hhd
    by (sep_apply (hcf5_c_hd_pn Tsh (l_it L) T); entailer!).
  forward_if (temp HF5._t'38 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { rewrite hcf5_c_itab. Intros.
    forward.
    sep_apply (hcf5_c_itable_fold Tsh (l_it L) T WF).
    forward.
    { entailer!. apply denote_tc_test_eq_split;
        (apply (derives_trans _ (itable Tsh (l_it L) T * TT)%logic); [cancel | apply sepcon_valid_pointer1; apply hcf5_c_hd_valid]). }
    rewrite Hh, (hcf5_c_cmp_self2 _ Hhd). entailer!. }
  (* if (!t) check_failed() *)
  forward_if.
  { match goal with Hx: _ |- _ => solve [inv Hx] end. }
  forward.
  rewrite Hpt.
  unfold hcf5_F, hcf5_Fx, hcf5_core, hcf5_globs, hcf5_lvars; cbn [app].
  entailer!.
Qed.

Lemma hcf5_c_C4 {Espec: OracleKind} x25519 gv L FR Px X R S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0 Rr :
  semax (hcf5_Delta x25519) (hcf5_F gv L FR Px X R S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0) hcf5_C4
    (overridePost (hcf5_F gv L FR Px X R S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0) Rr).
Proof.
  destruct Rr. unfold hcf5_Delta, hcf5_C4. simplify_func_tycontext. abbreviate_semax.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  2: { forward. apply ENTAIL_refl. }
  2: { unfold POSTCONDITION, abbreviate. rewrite overridePost_normal'. apply ENTAIL_refl. }
  unfold hcf5_F, hcf5_Fx. Intros.
  assert_PROP (itable_wf T) as WF by (unfold hcf5_core, itable; go_lowerx; entailer!).
  pose proof (hcf5_c_facts R L S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0 H0 H1 WF) as (Fdev & Fin & Fhs & Fpr & Fke).
  pose proof H1 as (Hdev & Hsn & Hpr & Hr & Hsh & Hke & Hh).
  pose proof H0 as (_ & _ & _ & (Hdd0 & Hcc & Hpt & Hit) & _).
  unfold hcf5_core, hcf5_globs, hcf5_lvars; cbn [app].
  (* dev_same(&ds, &w) *)
  gather_SEP 3 1.
  change (peer_rep Tsh (l_p L) P * itable Tsh (l_it L) T)%logic
    with (vobj_rep W (VPeer Tsh (l_p L) P) * vobj_rep W (VItab Tsh (l_it L) T))%logic.
  rewrite hcf5_c_vobjs2.
  rewrite <- Hpt.
  forward_call (Tsh, l_ds L, D0, l_p L, Tsh, l_w L, D, Tsh, l_p L, [VPeer Tsh (l_p L) P; VItab Tsh (l_it L) T]).
  { repeat apply Forall_cons; try apply Forall_nil; cbn [vobj_ok]; auto. }
  rewrite Hdev.
  rewrite <- hcf5_c_vobjs2. cbn [vobj_rep].
  (* hs_same(&hs0, &p.handshake) *)
  forward_if (temp HF5._t'40 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { change (device_rep Tsh (l_w L) D) with (vobj_rep W (VDev Tsh (l_w L) D)).
    rewrite (hcf5_c_vobjs1 W (VDev Tsh (l_w L) D)).
    change (peer_rep Tsh (l_p L) P) with (hs_mem true Tsh (l_p L) P).
    forward_call (Tsh, l_hs0 L, sn0, Tsh, l_p L, P, true, Tsh, l_it L, T, [VDev Tsh (l_w L) D]).
    { cancel. }
    { repeat apply Forall_cons; try apply Forall_nil; cbn [vobj_ok]; auto. }
    rewrite Hsn.
    rewrite <- hcf5_c_vobjs1. cbn [vobj_rep hs_mem].
    forward.
    entailer!. }
  repeat flatten_sepcon_in_SEP.
  (* pr_same(&ps0, &p) *)
  forward_if (temp HF5._t'42 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { gather_SEP 1 4.
    change (device_rep Tsh (l_w L) D * itable Tsh (l_it L) T)%logic
      with (vobj_rep W (VDev Tsh (l_w L) D) * vobj_rep W (VItab Tsh (l_it L) T))%logic.
    rewrite hcf5_c_vobjs2.
    forward_call (Tsh, l_ps0 L, P0, Tsh, l_p L, P, [VDev Tsh (l_w L) D; VItab Tsh (l_it L) T]).
    { repeat apply Forall_cons; try apply Forall_nil; cbn [vobj_ok]; auto. }
    rewrite Hpr.
    rewrite <- hcf5_c_vobjs2. cbn [vobj_rep]. repeat flatten_sepcon_in_SEP.
    forward.
    entailer!. }
  (* p.refcount.refcount == refs0 *)
  forward_if (temp HF5._t'44 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { rewrite (hcf5_c_split Tsh (l_p L) P). Intros.
    forward. forward. rewrite Hr, Int.eq_true. entailer!.
    rewrite (hcf5_c_split Tsh (l_p L) P). entailer!. }
  (* shim_same(&ss) *)
  forward_if (temp HF5._t'45 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { forward_call (gv, Tsh, l_ss L, S0, w0, S, w).
    rewrite Hsh. forward. entailer!. }
  (* kents_same(kes) *)
  forward_if (temp HF5._t'47 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { change (peer_rep Tsh (l_p L) P) with (vobj_rep W (VPeer Tsh (l_p L) P)).
    rewrite (hcf5_c_vobjs1 W (VPeer Tsh (l_p L) P)).
    forward_call (hcf5_khead KE, KE, Tsh, l_it L, T, [VPeer Tsh (l_p L) P]).
    { repeat apply Forall_cons; try apply Forall_nil; cbn [vobj_ok]; auto. }
    rewrite Hke. rewrite <- hcf5_c_vobjs1. cbn [vobj_rep].
    forward. entailer!. }
  (* it.head == head0 *)
  assert_PROP (is_pointer_or_null (hd nullval (t_L T))) as Hhd
    by (sep_apply (hcf5_c_hd_pn Tsh (l_it L) T); entailer!).
  forward_if (temp HF5._t'49 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { rewrite hcf5_c_itab. Intros.
    forward.
    sep_apply (hcf5_c_itable_fold Tsh (l_it L) T WF).
    forward.
    { entailer!. apply denote_tc_test_eq_split;
        (apply (derives_trans _ (itable Tsh (l_it L) T * TT)%logic); [cancel | apply sepcon_valid_pointer1; apply hcf5_c_hd_valid]). }
    rewrite Hh, (hcf5_c_cmp_self2 _ Hhd). entailer!. }
  (* if (!t) check_failed() *)
  forward_if.
  { match goal with Hx: _ |- _ => solve [inv Hx] end. }
  forward.
  rewrite Hpt.
  unfold hcf5_F, hcf5_Fx, hcf5_core, hcf5_globs, hcf5_lvars; cbn [app].
  entailer!.
Qed.

Lemma hcf5_c_C5 {Espec: OracleKind} x25519 gv L FR Px X R S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0 Rr :
  semax (hcf5_Delta x25519) (hcf5_F gv L FR Px X R S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0) hcf5_C5
    (overridePost (hcf5_F gv L FR Px X R S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0) Rr).
Proof.
  destruct Rr. unfold hcf5_Delta, hcf5_C5. simplify_func_tycontext. abbreviate_semax.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  2: { forward. apply ENTAIL_refl. }
  2: { unfold POSTCONDITION, abbreviate. rewrite overridePost_normal'. apply ENTAIL_refl. }
  unfold hcf5_F, hcf5_Fx. Intros.
  assert_PROP (itable_wf T) as WF by (unfold hcf5_core, itable; go_lowerx; entailer!).
  pose proof (hcf5_c_facts R L S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0 H0 H1 WF) as (Fdev & Fin & Fhs & Fpr & Fke).
  pose proof H1 as (Hdev & Hsn & Hpr & Hr & Hsh & Hke & Hh).
  pose proof H0 as (_ & _ & _ & (Hdd0 & Hcc & Hpt & Hit) & _).
  unfold hcf5_core, hcf5_globs, hcf5_lvars; cbn [app].
  (* dev_same(&ds, &w) *)
  gather_SEP 3 1.
  change (peer_rep Tsh (l_p L) P * itable Tsh (l_it L) T)%logic
    with (vobj_rep W (VPeer Tsh (l_p L) P) * vobj_rep W (VItab Tsh (l_it L) T))%logic.
  rewrite hcf5_c_vobjs2.
  rewrite <- Hpt.
  forward_call (Tsh, l_ds L, D0, l_p L, Tsh, l_w L, D, Tsh, l_p L, [VPeer Tsh (l_p L) P; VItab Tsh (l_it L) T]).
  { repeat apply Forall_cons; try apply Forall_nil; cbn [vobj_ok]; auto. }
  rewrite Hdev.
  rewrite <- hcf5_c_vobjs2. cbn [vobj_rep].
  (* hs_same(&hs0, &p.handshake) *)
  forward_if (temp HF5._t'78 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { change (device_rep Tsh (l_w L) D) with (vobj_rep W (VDev Tsh (l_w L) D)).
    rewrite (hcf5_c_vobjs1 W (VDev Tsh (l_w L) D)).
    change (peer_rep Tsh (l_p L) P) with (hs_mem true Tsh (l_p L) P).
    forward_call (Tsh, l_hs0 L, sn0, Tsh, l_p L, P, true, Tsh, l_it L, T, [VDev Tsh (l_w L) D]).
    { cancel. }
    { repeat apply Forall_cons; try apply Forall_nil; cbn [vobj_ok]; auto. }
    rewrite Hsn.
    rewrite <- hcf5_c_vobjs1. cbn [vobj_rep hs_mem].
    forward.
    entailer!. }
  repeat flatten_sepcon_in_SEP.
  (* pr_same(&ps0, &p) *)
  forward_if (temp HF5._t'80 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { gather_SEP 1 4.
    change (device_rep Tsh (l_w L) D * itable Tsh (l_it L) T)%logic
      with (vobj_rep W (VDev Tsh (l_w L) D) * vobj_rep W (VItab Tsh (l_it L) T))%logic.
    rewrite hcf5_c_vobjs2.
    forward_call (Tsh, l_ps0 L, P0, Tsh, l_p L, P, [VDev Tsh (l_w L) D; VItab Tsh (l_it L) T]).
    { repeat apply Forall_cons; try apply Forall_nil; cbn [vobj_ok]; auto. }
    rewrite Hpr.
    rewrite <- hcf5_c_vobjs2. cbn [vobj_rep]. repeat flatten_sepcon_in_SEP.
    forward.
    entailer!. }
  (* p.refcount.refcount == refs0 *)
  forward_if (temp HF5._t'82 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { rewrite (hcf5_c_split Tsh (l_p L) P). Intros.
    forward. forward. rewrite Hr, Int.eq_true. entailer!.
    rewrite (hcf5_c_split Tsh (l_p L) P). entailer!. }
  (* shim_same(&ss) *)
  forward_if (temp HF5._t'83 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { forward_call (gv, Tsh, l_ss L, S0, w0, S, w).
    rewrite Hsh. forward. entailer!. }
  (* kents_same(kes) *)
  forward_if (temp HF5._t'85 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { change (peer_rep Tsh (l_p L) P) with (vobj_rep W (VPeer Tsh (l_p L) P)).
    rewrite (hcf5_c_vobjs1 W (VPeer Tsh (l_p L) P)).
    forward_call (hcf5_khead KE, KE, Tsh, l_it L, T, [VPeer Tsh (l_p L) P]).
    { repeat apply Forall_cons; try apply Forall_nil; cbn [vobj_ok]; auto. }
    rewrite Hke. rewrite <- hcf5_c_vobjs1. cbn [vobj_rep].
    forward. entailer!. }
  (* it.head == head0 *)
  assert_PROP (is_pointer_or_null (hd nullval (t_L T))) as Hhd
    by (sep_apply (hcf5_c_hd_pn Tsh (l_it L) T); entailer!).
  forward_if (temp HF5._t'87 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { rewrite hcf5_c_itab. Intros.
    forward.
    sep_apply (hcf5_c_itable_fold Tsh (l_it L) T WF).
    forward.
    { entailer!. apply denote_tc_test_eq_split;
        (apply (derives_trans _ (itable Tsh (l_it L) T * TT)%logic); [cancel | apply sepcon_valid_pointer1; apply hcf5_c_hd_valid]). }
    rewrite Hh, (hcf5_c_cmp_self2 _ Hhd). entailer!. }
  (* if (!t) check_failed() *)
  forward_if.
  { match goal with Hx: _ |- _ => solve [inv Hx] end. }
  forward.
  rewrite Hpt.
  unfold hcf5_F, hcf5_Fx, hcf5_core, hcf5_globs, hcf5_lvars; cbn [app].
  entailer!.
Qed.

Lemma hcf5_c_C6 {Espec: OracleKind} x25519 gv L FR Px X R S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0 Rr :
  semax (hcf5_Delta x25519) (hcf5_F gv L FR Px X R S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0) hcf5_C6
    (overridePost (hcf5_F gv L FR Px X R S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0) Rr).
Proof.
  destruct Rr. unfold hcf5_Delta, hcf5_C6. simplify_func_tycontext. abbreviate_semax.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  2: { forward. apply ENTAIL_refl. }
  2: { unfold POSTCONDITION, abbreviate. rewrite overridePost_normal'. apply ENTAIL_refl. }
  unfold hcf5_F, hcf5_Fx. Intros.
  assert_PROP (itable_wf T) as WF by (unfold hcf5_core, itable; go_lowerx; entailer!).
  pose proof (hcf5_c_facts R L S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0 H0 H1 WF) as (Fdev & Fin & Fhs & Fpr & Fke).
  pose proof H1 as (Hdev & Hsn & Hpr & Hr & Hsh & Hke & Hh).
  pose proof H0 as (_ & _ & _ & (Hdd0 & Hcc & Hpt & Hit) & _).
  unfold hcf5_core, hcf5_globs, hcf5_lvars; cbn [app].
  (* dev_same(&ds, &w) *)
  gather_SEP 3 1.
  change (peer_rep Tsh (l_p L) P * itable Tsh (l_it L) T)%logic
    with (vobj_rep W (VPeer Tsh (l_p L) P) * vobj_rep W (VItab Tsh (l_it L) T))%logic.
  rewrite hcf5_c_vobjs2.
  rewrite <- Hpt.
  forward_call (Tsh, l_ds L, D0, l_p L, Tsh, l_w L, D, Tsh, l_p L, [VPeer Tsh (l_p L) P; VItab Tsh (l_it L) T]).
  { repeat apply Forall_cons; try apply Forall_nil; cbn [vobj_ok]; auto. }
  rewrite Hdev.
  rewrite <- hcf5_c_vobjs2. cbn [vobj_rep].
  (* hs_same(&hs0, &p.handshake) *)
  forward_if (temp HF5._t'92 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { change (device_rep Tsh (l_w L) D) with (vobj_rep W (VDev Tsh (l_w L) D)).
    rewrite (hcf5_c_vobjs1 W (VDev Tsh (l_w L) D)).
    change (peer_rep Tsh (l_p L) P) with (hs_mem true Tsh (l_p L) P).
    forward_call (Tsh, l_hs0 L, sn0, Tsh, l_p L, P, true, Tsh, l_it L, T, [VDev Tsh (l_w L) D]).
    { cancel. }
    { repeat apply Forall_cons; try apply Forall_nil; cbn [vobj_ok]; auto. }
    rewrite Hsn.
    rewrite <- hcf5_c_vobjs1. cbn [vobj_rep hs_mem].
    forward.
    entailer!. }
  repeat flatten_sepcon_in_SEP.
  (* pr_same(&ps0, &p) *)
  forward_if (temp HF5._t'94 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { gather_SEP 1 4.
    change (device_rep Tsh (l_w L) D * itable Tsh (l_it L) T)%logic
      with (vobj_rep W (VDev Tsh (l_w L) D) * vobj_rep W (VItab Tsh (l_it L) T))%logic.
    rewrite hcf5_c_vobjs2.
    forward_call (Tsh, l_ps0 L, P0, Tsh, l_p L, P, [VDev Tsh (l_w L) D; VItab Tsh (l_it L) T]).
    { repeat apply Forall_cons; try apply Forall_nil; cbn [vobj_ok]; auto. }
    rewrite Hpr.
    rewrite <- hcf5_c_vobjs2. cbn [vobj_rep]. repeat flatten_sepcon_in_SEP.
    forward.
    entailer!. }
  (* p.refcount.refcount == refs0 *)
  forward_if (temp HF5._t'96 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { rewrite (hcf5_c_split Tsh (l_p L) P). Intros.
    forward. forward. rewrite Hr, Int.eq_true. entailer!.
    rewrite (hcf5_c_split Tsh (l_p L) P). entailer!. }
  (* shim_same(&ss) *)
  forward_if (temp HF5._t'97 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { forward_call (gv, Tsh, l_ss L, S0, w0, S, w).
    rewrite Hsh. forward. entailer!. }
  (* kents_same(kes) *)
  forward_if (temp HF5._t'99 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { change (peer_rep Tsh (l_p L) P) with (vobj_rep W (VPeer Tsh (l_p L) P)).
    rewrite (hcf5_c_vobjs1 W (VPeer Tsh (l_p L) P)).
    forward_call (hcf5_khead KE, KE, Tsh, l_it L, T, [VPeer Tsh (l_p L) P]).
    { repeat apply Forall_cons; try apply Forall_nil; cbn [vobj_ok]; auto. }
    rewrite Hke. rewrite <- hcf5_c_vobjs1. cbn [vobj_rep].
    forward. entailer!. }
  (* it.head == head0 *)
  assert_PROP (is_pointer_or_null (hd nullval (t_L T))) as Hhd
    by (sep_apply (hcf5_c_hd_pn Tsh (l_it L) T); entailer!).
  forward_if (temp HF5._t'101 (Vint Int.one)).
  2: { match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
  { rewrite hcf5_c_itab. Intros.
    forward.
    sep_apply (hcf5_c_itable_fold Tsh (l_it L) T WF).
    forward.
    { entailer!. apply denote_tc_test_eq_split;
        (apply (derives_trans _ (itable Tsh (l_it L) T * TT)%logic); [cancel | apply sepcon_valid_pointer1; apply hcf5_c_hd_valid]). }
    rewrite Hh, (hcf5_c_cmp_self2 _ Hhd). entailer!. }
  (* if (!t) check_failed() *)
  forward_if.
  { match goal with Hx: _ |- _ => solve [inv Hx] end. }
  forward.
  rewrite Hpt.
  unfold hcf5_F, hcf5_Fx, hcf5_core, hcf5_globs, hcf5_lvars; cbn [app].
  entailer!.
Qed.

Lemma hcf5_c_post {Espec: OracleKind} {cs: compspecs} Delta P c (F Q: environ -> mpred) Rr :
  semax Delta P c (overridePost F Rr) -> F |-- Q -> semax Delta P c (overridePost Q Rr).
Proof.
  intros HS HF. eapply semax_post; [| | | | exact HS]; destruct Rr; simpl; intros; apply andp_left2;
    try apply derives_refl. apply HF.
Qed.

Lemma hcf5_c_lift1 {Espec: OracleKind} x25519 gv L FR c :
  (forall Px X R S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0 Rr,
     semax (hcf5_Delta x25519) (hcf5_F gv L FR Px X R S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0) c
       (overridePost (hcf5_F gv L FR Px X R S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0) Rr)) ->
  semax (hcf5_Delta x25519) (hcf5_SX1 x25519 gv L FR) c (overridePost (hcf5_SX1 x25519 gv L FR) (hcf5_R gv)).
Proof.
  intros HC. unfold hcf5_SX1 at 1.
  Intros R S w D P T KE D0. Intros sn0 P0 r0 S0 w0 h0 RAW.
  eapply hcf5_c_post; [apply HC |].
  unfold hcf5_SX1.
  apply (exp_right R); apply (exp_right S); apply (exp_right w); apply (exp_right D); apply (exp_right P);
  apply (exp_right T); apply (exp_right KE); apply (exp_right D0); apply (exp_right sn0); apply (exp_right P0);
  apply (exp_right r0); apply (exp_right S0); apply (exp_right w0); apply (exp_right h0); apply (exp_right RAW).
  apply derives_refl.
Qed.

Lemma hcf5_c_lift5 {Espec: OracleKind} x25519 gv L FR c :
  (forall Px X R S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0 Rr,
     semax (hcf5_Delta x25519) (hcf5_F gv L FR Px X R S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0) c
       (overridePost (hcf5_F gv L FR Px X R S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0) Rr)) ->
  semax (hcf5_Delta x25519) (hcf5_SX5 x25519 gv L FR) c (overridePost (hcf5_SX5 x25519 gv L FR) (hcf5_R gv)).
Proof.
  intros HC. unfold hcf5_SX5 at 1.
  Intros R S w D P T KE D0. Intros sn0 P0 r0 S0 w0 h0 RAW H.
  eapply hcf5_c_post; [apply HC |].
  unfold hcf5_SX5.
  apply (exp_right R); apply (exp_right S); apply (exp_right w); apply (exp_right D); apply (exp_right P);
  apply (exp_right T); apply (exp_right KE); apply (exp_right D0); apply (exp_right sn0); apply (exp_right P0);
  apply (exp_right r0); apply (exp_right S0); apply (exp_right w0); apply (exp_right h0); apply (exp_right RAW).
  apply (exp_right H). apply derives_refl.
Qed.

Definition hcf5_C1_stmt (x25519: list byte -> list byte -> list byte) : Prop :=
  forall {Espec: OracleKind} gv L FR,
  semax (hcf5_Delta x25519) (hcf5_SX1 x25519 gv L FR) hcf5_C1 (overridePost (hcf5_SX1 x25519 gv L FR) (hcf5_R gv)).

Definition hcf5_C2_stmt (x25519: list byte -> list byte -> list byte) : Prop :=
  forall {Espec: OracleKind} gv L FR,
  semax (hcf5_Delta x25519) (hcf5_SX1 x25519 gv L FR) hcf5_C2 (overridePost (hcf5_SX1 x25519 gv L FR) (hcf5_R gv)).

Definition hcf5_C3_stmt (x25519: list byte -> list byte -> list byte) : Prop :=
  forall {Espec: OracleKind} gv L FR,
  semax (hcf5_Delta x25519) (hcf5_SX1 x25519 gv L FR) hcf5_C3 (overridePost (hcf5_SX1 x25519 gv L FR) (hcf5_R gv)).

Definition hcf5_C4_stmt (x25519: list byte -> list byte -> list byte) : Prop :=
  forall {Espec: OracleKind} gv L FR,
  semax (hcf5_Delta x25519) (hcf5_SX1 x25519 gv L FR) hcf5_C4 (overridePost (hcf5_SX1 x25519 gv L FR) (hcf5_R gv)).

Definition hcf5_C5_stmt (x25519: list byte -> list byte -> list byte) : Prop :=
  forall {Espec: OracleKind} gv L FR,
  semax (hcf5_Delta x25519) (hcf5_SX5 x25519 gv L FR) hcf5_C5 (overridePost (hcf5_SX5 x25519 gv L FR) (hcf5_R gv)).

Definition hcf5_C6_stmt (x25519: list byte -> list byte -> list byte) : Prop :=
  forall {Espec: OracleKind} gv L FR,
  semax (hcf5_Delta x25519) (hcf5_SX5 x25519 gv L FR) hcf5_C6 (overridePost (hcf5_SX5 x25519 gv L FR) (hcf5_R gv)).

Theorem hcf5_C_ok x25519 :
  hcf5_hyps x25519 ->
  hcf5_C1_stmt x25519 /\ hcf5_C2_stmt x25519 /\ hcf5_C3_stmt x25519 /\ hcf5_C4_stmt x25519 /\
  hcf5_C5_stmt x25519 /\ hcf5_C6_stmt x25519.
Proof.
  intros HH. split; [| split; [| split; [| split; [| split]]]].
  - intros Espec gv L FR. apply hcf5_c_lift1. intros. apply hcf5_c_C1.
  - intros Espec gv L FR. apply hcf5_c_lift1. intros. apply hcf5_c_C2.
  - intros Espec gv L FR. apply hcf5_c_lift1. intros. apply hcf5_c_C3.
  - intros Espec gv L FR. apply hcf5_c_lift1. intros. apply hcf5_c_C4.
  - intros Espec gv L FR. apply hcf5_c_lift5. intros. apply hcf5_c_C5.
  - intros Espec gv L FR. apply hcf5_c_lift5. intros. apply hcf5_c_C6.
Qed.
