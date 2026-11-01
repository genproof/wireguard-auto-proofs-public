(* law handshake_receive, phase B8 branch C: segment C3 (CHECK(hnodes_same_except(peers, target->p) && itd.head == head0 && kents_same(kes) && shim_same(&ss))).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_cut.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mspec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require WgNoise.contracts.x_handshake_receive.
Require WgNoise.harness.x_handshake_receive.code.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_conv.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_ilem.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_C_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_C_W_pure.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* helpers (ports of hci5_p8_A2_sep.v and hci5_p8_b.v)                      *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hrx5_b8cw_cceK : change_composite_env CKS W_handshake_receive.
Proof. make_cs_preserve CKS W_handshake_receive. Defined.
#[local] Instance hrx5_b8cw_cceN : change_composite_env Noise.CS W_handshake_receive.
Proof. make_cs_preserve Noise.CS W_handshake_receive. Defined.

Definition hrx5_b8cw_acc (Q P: mpred) : Prop := P |-- Q * (Q -* P).

Lemma hrx5_b8cw_acc_l Q A F : hrx5_b8cw_acc Q A -> hrx5_b8cw_acc Q (A * F).
Proof.
  unfold hrx5_b8cw_acc. intros H. apply derives_trans with (Q * (Q -* A) * F).
  { apply sepcon_derives; [exact H | apply derives_refl]. }
  rewrite (sepcon_assoc Q). apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_assoc (Q -* A)), (sepcon_comm F Q), <- (sepcon_assoc (Q -* A)), (sepcon_comm (Q -* A) Q).
  apply sepcon_derives; [apply modus_ponens_wand | apply derives_refl].
Qed.

Lemma hrx5_b8cw_acc_r Q A F : hrx5_b8cw_acc Q A -> hrx5_b8cw_acc Q (F * A).
Proof. intros H. rewrite sepcon_comm. apply hrx5_b8cw_acc_l, H. Qed.

Lemma hrx5_b8cw_acc_prop Q (c: Prop) A : (c -> hrx5_b8cw_acc Q A) -> hrx5_b8cw_acc Q (!! c && A).
Proof.
  unfold hrx5_b8cw_acc. intros H. apply derives_extract_prop. intros Hc.
  eapply derives_trans; [apply H, Hc|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. apply andp_right; [apply prop_right, Hc|]. rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hrx5_b8cw_acc_ex {X: Type} Q (A: X -> mpred) : (forall x, hrx5_b8cw_acc Q (A x)) -> hrx5_b8cw_acc Q (EX x, A x).
Proof.
  unfold hrx5_b8cw_acc. intros H. apply exp_left. intros x.
  eapply derives_trans; [apply H|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. eapply derives_trans; [apply modus_ponens_wand|]. apply (exp_right x), derives_refl.
Qed.

(* the node's field p, at the world *)
Lemma hrx5_b8cw_node_split p sn r rs nx x :
  @data_at CKS Ews t_hnode4 (p, (sn, (r, (rs, nx)))) x |--
  @field_at W_handshake_receive Ews t_hnode4 [StructField HC._p] p x *
  (@field_at W_handshake_receive Ews t_hnode4 [StructField HC._p] p x -* @data_at CKS Ews t_hnode4 (p, (sn, (r, (rs, nx)))) x).
Proof.
  rewrite <- (@field_at_change_composite CKS W_handshake_receive _ Ews t_hnode4 [StructField HC._p] p p (JMeq_refl p))
    by (vm_compute; reflexivity).
  eapply derives_trans; [apply andp_right; [apply (@data_at_local_facts CKS) | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  (eapply derives_trans; [apply (@gfield_ramif CKS Ews t_hnode4 [] (StructField HC._p) _ p x); [apply JMeq_refl | auto with field_compatible] |]).
  apply sepcon_derives; [apply derives_refl|].
  apply (allp_left _ p).
  apply derives_refl.
Qed.

Lemma hrx5_b8cw_node_acc l NS N : In N NS ->
  hrx5_b8cw_acc (@field_at W_handshake_receive Ews t_hnode4 [StructField HC._p] (hn_p N) (hn_addr N))
    (hnodes_rep4 W_handshake_receive l NS).
Proof.
  revert l; induction NS as [|N0 NS IH]; intros l Hin; [destruct Hin|]. cbn [hnodes_rep4].
  apply hrx5_b8cw_acc_prop; intros Hl. apply hrx5_b8cw_acc_ex; intros nx.
  destruct Hin as [<-|Hin].
  - subst l. apply hrx5_b8cw_acc_l, hrx5_b8cw_acc_l, hrx5_b8cw_acc_r. apply hrx5_b8cw_node_split.
  - apply hrx5_b8cw_acc_r, IH, Hin.
Qed.

(* the lent objects *)
Lemma hrx5_b8cw_vo sh wg D l KE :
  device_rep sh wg D * kents_rep W_handshake_receive l KE = vobjs W_handshake_receive [VDev sh wg D; VKents l KE].
Proof. unfold vobjs. cbn [iter_sepcon vobj_rep]. rewrite sepcon_emp. reflexivity. Qed.

Lemma hrx5_b8cw_vo1 PS : peers_rep PS = vobjs W_handshake_receive [VPeers PS].
Proof. unfold vobjs. cbn [iter_sepcon vobj_rep]. rewrite sepcon_emp. reflexivity. Qed.

(* the index table's head field at the world *)
Lemma hrx5_b8cw_itab_W sh (v: val) p :
  @data_at Noise.CS sh t_itab v p = @data_at W_handshake_receive sh t_itab v p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W_handshake_receive _ sh t_itab v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hrx5_b8cw_itable_open sht tab T :
  itable sht tab T = (!! itable_wf T &&
    (@data_at W_handshake_receive sht t_itab (hd nullval (t_L T)) tab *
     iter_sepcon (pool_item_rep (t_L T)) (t_D T))).
Proof. unfold itable. rewrite hrx5_b8cw_itab_W. reflexivity. Qed.

Lemma hrx5_b8cw_itable_fold sht tab T : itable_wf T ->
  (@data_at W_handshake_receive sht t_itab (hd nullval (t_L T)) tab *
   iter_sepcon (pool_item_rep (t_L T)) (t_D T) |-- itable sht tab T).
Proof. intros HT. rewrite hrx5_b8cw_itable_open. entailer!. Qed.

Lemma hrx5_b8cw_hd_valid sht tab T : itable sht tab T |-- valid_pointer (hd nullval (t_L T)).
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

Lemma hrx5_b8cw_hd_pn sht tab T : itable sht tab T |-- !! is_pointer_or_null (hd nullval (t_L T)).
Proof.
  unfold itable. Intros. destruct H as (_ & Hinc & _ & Hw).
  destruct (t_L T) as [| v l] eqn:EL; cbn [hd]; [entailer! |].
  assert (Hv: In v (saddrs (t_D T))) by (apply Hinc; left; reflexivity).
  unfold saddrs in Hv; apply in_map_iff in Hv; destruct Hv as ([[a sh] E] & Ha & Hin); cbn in Ha; subst a.
  sep_apply (iter_sepcon_in_true (pool_item_rep (v :: l)) (t_D T) _ Hin).
  unfold pool_item_rep, entry_at. entailer!.
  match goal with X: field_compatible _ _ v |- _ => destruct X as [Hp _]; destruct v; try contradiction; exact I end.
Qed.

Lemma hrx5_b8cw_hn_pn l NS : hnodes_rep4 W_handshake_receive l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [|N NS]; cbn [hnodes_rep4].
  - entailer!.
  - Intros nx. subst l. entailer!.
    match goal with Hf: field_compatible _ _ _ |- _ => destruct Hf as [Hp _] end.
    apply isptr_is_pointer_or_null; exact Hp.
Qed.

Lemma hrx5_b8cw_peers_ptr PS a : In a (map peer_addr4 PS) -> peers_rep PS |-- !! isptr a.
Proof.
  intros Hin. apply in_map_iff in Hin. destruct Hin as ([[p sh] Q] & <- & Hin).
  unfold peers_rep. eapply derives_trans; [apply (iter_sepcon_in_true _ _ _ Hin)|].
  unfold peer_item_rep, peer_rep. Intros. entailer!.
  match goal with Hf: field_compatible _ _ _ |- _ => apply field_compatible_isptr in Hf; exact Hf end.
Qed.

Lemma hrx5_b8cw_cmp_self v : is_pointer_or_null v ->
  force_val (sem_cast tint tbool (eval_binop Oeq (tptr (Tstruct HRM._index_hashtable_entry noattr))
    (tptr (Tstruct HRM._index_hashtable_entry noattr)) v v)) = Vint Int.one.
Proof.
  intros Hv. destruct v; try contradiction.
  - cbn in Hv. subst. reflexivity.
  - unfold eval_binop, sem_binary_operation', sem_cmp; cbn. unfold sem_cmp_pp, Val.cmplu_bool; cbn.
    rewrite if_true by reflexivity. rewrite Ptrofs.eq_true. reflexivity.
Qed.

Lemma hrx5_B8C_C3_ok : hrx5_B8C_C3_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
    proto ip4 ip6 port M dp img a P pt HY.
  unfold hrx5_B8C_QC at 1. unfold hrx5_Delta, hrx5_B8C_C3. simplify_func_tycontext. abbreviate_semax.
  unfold hrx5_B8C_props, hrx5_B8C_temps, hrx5_B8C_sep, hrx5_B8C_world, hrx5_rest, hrx5_cglobs, hrx5_B8C_scr, hrx5_lvars;
    cbn [app].
  Intros.
  match goal with Hi: hrx5_inv _ _ _ _ _ _ _ _ _, Hs: sfind PS a = Some _ |- _ => rename Hi into Hinv; rename Hs into Hsf end.
  assert_PROP (itable_wf T) as HwfT by (unfold itable at 1; entailer!).
  assert_PROP (is_pointer_or_null (hd nullval (t_L T))) as Hhd.
  { sep_apply (hrx5_b8cw_hd_pn Tsh (l_itd L) T). entailer!. }
  assert_PROP (is_pointer_or_null (hrx5_head (hnodes_snapped4 T NS PS))) as Hhn.
  { sep_apply (hrx5_b8cw_hn_pn (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS)). entailer!. }
  destruct (hrx5_b8cw_facts x25519 R L sec birth NS PS KE T head nk a P (hrx5ck_new P pt (s_boot S))
              Hinv HwfT Hsf eq_refl eq_refl)
    as ((NS1 & N & NS2 & HNS & HNa & HNp) & Hvo & Hq1 & Hq2 & Hq3 & Hq4 & Hq5 & Hq6 & Hq7 & Hq8 & Hq9 & Hq10 & Hsame &
        HPo & Hkp).
  assert_PROP (isptr a) as Hpa.
  { assert (Ha: In a (map peer_addr4 (supd PS a (hrx5ck_new P pt (s_boot S))))).
    { rewrite hrx5_b8cw_supd_addr. apply (in_map peer_addr4 _ _ (hrx5cr_model_sfind_in _ _ _ _ Hsf)). }
    sep_apply (hrx5_b8cw_peers_ptr _ _ Ha). entailer!. }
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward.
    assert (HinN: In N (hnodes_snapped4 T NS PS)) by (rewrite HNS; apply in_or_app; right; left; reflexivity).
    pose proof (hrx5_b8cw_node_acc (hrx5_head (hnodes_snapped4 T NS PS)) _ N HinN) as A1.
    unfold hrx5_b8cw_acc in A1. sep_apply A1. clear A1. flatten_sepcon_in_SEP.
    rewrite <- HNa.
    forward.
    rewrite HNp.
    sep_apply wand_frame_elim.
    sep_apply (hrx5_b8cw_vo Tsh (l_wd L) (hrx5_DL x25519 R L sec birth) (hrx5_khead (map (kent_snapped T) KE))
                 (map (kent_snapped T) KE)).
    forward_call (hrx5_head (hnodes_snapped4 T NS PS), hnodes_snapped4 T NS PS, supd PS a (hrx5ck_new P pt (s_boot S)),
                  hrx5_b8cw_sns T PS, hrx5_b8cw_rs PS, hrx5_b8cw_prs PS, a, Tsh, l_itd L, T,
                  hrx5_b8cw_VO x25519 R L sec birth T KE).
    rewrite Hsame.
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HRM._t'214 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    { rewrite hrx5_b8cw_itable_open. Intros.
      forward.
      sep_apply (hrx5_b8cw_itable_fold Tsh (l_itd L) T HwfT).
      forward.
      { entailer!. apply denote_tc_test_eq_split;
          (apply (derives_trans _ (itable Tsh (l_itd L) T * TT)); [cancel | apply sepcon_valid_pointer1; apply hrx5_b8cw_hd_valid]). }
      rewrite (hrx5_b8cw_cmp_self _ Hhd). entailer!. }
    { exfalso. apply Int.one_not_zero. assumption. }
    unfold hrx5_b8cw_VO. rewrite <- hrx5_b8cw_vo. rewrite hrx5_b8cw_khead_snapped.
    rewrite (hrx5_b8cw_vo1 (supd PS a (hrx5ck_new P pt (s_boot S)))). flatten_sepcon_in_SEP.
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HRM._t'215 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    { forward_call (hrx5_khead KE, map (kent_snapped T) KE, Tsh, l_itd L, T,
                    [VPeers (supd PS a (hrx5ck_new P pt (s_boot S)))]).
      rewrite hrx5_b8cw_kents_refl. forward. entailer!. }
    { exfalso. apply Int.one_not_zero. assumption. }
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HRM._t'217 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    { forward_call (gv, Tsh, l_ss L, S, w, S, w).
      rewrite hrx5_b8cw_shim_refl. forward. entailer!. }
    { exfalso. apply Int.one_not_zero. assumption. }
    forward_if.
    { exfalso. apply Int.one_not_zero. assumption. }
    forward. rewrite <- hrx5_b8cw_vo1. rewrite hrx5_b8cw_khead_snapped. entailer!. }
  { forward. apply ENTAIL_refl. }
  unfold POSTCONDITION, abbreviate. unfold overridePost. destruct (hrx5_RB x25519 gv L FR) as [r1 r2 r3 r4].
  cbn [RA_normal].
  unfold hrx5_B8C_QC, hrx5_B8C_props, hrx5_B8C_temps, hrx5_B8C_sep, hrx5_B8C_world, hrx5_rest, hrx5_cglobs,
    hrx5_B8C_scr, hrx5_lvars; cbn [app].
  entailer!.
Qed.
