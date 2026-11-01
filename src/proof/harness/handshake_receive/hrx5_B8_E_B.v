(* law handshake_receive, phase B8, branch E: part B: the whole-state check and the fold into hrx5_S8.
   Statement: hrx5_B8_E_defs.v. *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_E_defs.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_E_B_pure.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* helpers (ports of B8 C W hrx5_B8_C_W.v and B8 C F hrx5_B8_C_F.v)         *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hrx5_b8eb_cceK : change_composite_env CKS W_handshake_receive.
Proof. make_cs_preserve CKS W_handshake_receive. Defined.
#[local] Instance hrx5_b8eb_cceN : change_composite_env Noise.CS W_handshake_receive.
Proof. make_cs_preserve Noise.CS W_handshake_receive. Defined.

(* the lent objects *)
Lemma hrx5_b8eb_vo sh wg D l KE :
  device_rep sh wg D * kents_rep W_handshake_receive l KE = vobjs W_handshake_receive [VDev sh wg D; VKents l KE].
Proof. unfold vobjs. cbn [iter_sepcon vobj_rep]. rewrite sepcon_emp. reflexivity. Qed.

Lemma hrx5_b8eb_vo1 PS : peers_rep PS = vobjs W_handshake_receive [VPeers PS].
Proof. unfold vobjs. cbn [iter_sepcon vobj_rep]. rewrite sepcon_emp. reflexivity. Qed.

(* the index table's head field at the world *)
Lemma hrx5_b8eb_itab_W sh (v: val) p :
  @data_at Noise.CS sh t_itab v p = @data_at W_handshake_receive sh t_itab v p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W_handshake_receive _ sh t_itab v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hrx5_b8eb_itable_open sht tab T :
  itable sht tab T = (!! itable_wf T &&
    (@data_at W_handshake_receive sht t_itab (hd nullval (t_L T)) tab *
     iter_sepcon (pool_item_rep (t_L T)) (t_D T))).
Proof. unfold itable. rewrite hrx5_b8eb_itab_W. reflexivity. Qed.

Lemma hrx5_b8eb_itable_fold sht tab T : itable_wf T ->
  (@data_at W_handshake_receive sht t_itab (hd nullval (t_L T)) tab *
   iter_sepcon (pool_item_rep (t_L T)) (t_D T) |-- itable sht tab T).
Proof. intros HT. rewrite hrx5_b8eb_itable_open. entailer!. Qed.

Lemma hrx5_b8eb_hd_valid sht tab T : itable sht tab T |-- valid_pointer (hd nullval (t_L T)).
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

Lemma hrx5_b8eb_hd_pn sht tab T : itable sht tab T |-- !! is_pointer_or_null (hd nullval (t_L T)).
Proof.
  unfold itable. Intros. destruct H as (_ & Hinc & _ & Hw).
  destruct (t_L T) as [| v l] eqn:EL; cbn [hd]; [entailer! |].
  assert (Hv: In v (saddrs (t_D T))) by (apply Hinc; left; reflexivity).
  unfold saddrs in Hv; apply in_map_iff in Hv; destruct Hv as ([[a sh] E] & Ha & Hin); cbn in Ha; subst a.
  sep_apply (iter_sepcon_in_true (pool_item_rep (v :: l)) (t_D T) _ Hin).
  unfold pool_item_rep, entry_at. entailer!.
  match goal with X: field_compatible _ _ v |- _ => destruct X as [Hp _]; destruct v; try contradiction; exact I end.
Qed.

Lemma hrx5_b8eb_hn_pn l NS : hnodes_rep4 W_handshake_receive l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [|N NS]; cbn [hnodes_rep4].
  - entailer!.
  - Intros nx. subst l. entailer!.
    match goal with Hf: field_compatible _ _ _ |- _ => destruct Hf as [Hp _] end.
    apply isptr_is_pointer_or_null; exact Hp.
Qed.

Lemma hrx5_b8eb_cmp_self v : is_pointer_or_null v ->
  force_val (sem_cast tint tbool (eval_binop Oeq (tptr (Tstruct HRM._index_hashtable_entry noattr))
    (tptr (Tstruct HRM._index_hashtable_entry noattr)) v v)) = Vint Int.one.
Proof.
  intros Hv. destruct v; try contradiction.
  - cbn in Hv. subst. reflexivity.
  - unfold eval_binop, sem_binary_operation', sem_cmp; cbn. unfold sem_cmp_pp, Val.cmplu_bool; cbn.
    rewrite if_true by reflexivity. rewrite Ptrofs.eq_true. reflexivity.
Qed.

(* ---- the fold ---- *)
Lemma hrx5_b8eb_snapped_a T NS PS :
  length NS = length PS -> map hn_addr (hnodes_snapped4 T NS PS) = map hn_addr NS.
Proof.
  unfold hnodes_snapped4. revert PS. induction NS as [|N NS IH]; intros [|x PS] H; simpl in *; try discriminate;
    [reflexivity|].
  destruct x as [[p sh] P]. simpl. f_equal. apply IH. lia.
Qed.

Lemma hrx5_b8eb_kaddr T KE : map ke_addr (map (kent_snapped T) KE) = map ke_addr KE.
Proof. rewrite map_map. apply map_ext. intros e. reflexivity. Qed.

Lemma hrx5_b8eb_inv x25519 R L NS PS KE T head nk :
  hrx5_inv x25519 R L NS PS KE T head nk ->
  hrx5_inv x25519 R L (hnodes_snapped4 T NS PS) PS (map (kent_snapped T) KE) T head nk.
Proof.
  intros HI.
  assert (Hlen: length NS = length PS).
  { destruct HI as (_ & _ & _ & _ & Hnp & _). apply hrx5_b8eb_peers_len; exact Hnp. }
  destruct HI as (HF & Hwf & HND & Hch & Hnp & Hnk & Hpool).
  unfold hrx5_inv. split; [exact HF|]. split; [exact Hwf|]. split; [exact HND|]. split; [exact Hch|].
  split; [unfold hnodes_peers4 in *; rewrite hrx5_b8eb_snapped_p by exact Hlen; exact Hnp|].
  split; [rewrite hrx5_b8eb_snapped_a by exact Hlen; exact Hnk|]. rewrite hrx5_b8eb_kaddr. exact Hpool.
Qed.

Lemma hrx5_b8eb_rxlog gv X : rxlog_rep gv X |-- @data_at_ HRX Ews t_rxlog (gv HM._wg_shim_rx).
Proof. unfold rxlog_rep. apply data_at_data_at_. Qed.

Lemma hrx5_b8eb_qlen gv q : qlen_rep gv q |-- @data_at_ HRX Ews tint (gv HM._wg_shim_handshake_queue_len).
Proof. unfold qlen_rep. apply data_at_data_at_. Qed.

Lemma hrx5_b8eb_ci x25519 aead_dec R PS o now ci :
  hrx5_ci_rep x25519 aead_dec R PS o now ci |-- @data_at_ HCS Tsh t_mcinit ci.
Proof.
  unfold hrx5_ci_rep. destruct o; try apply derives_refl.
  destruct (hrx5_fwd _); [| apply derives_refl].
  destruct (hrx5ci_tgt _ _ _ _ _ _) as [[[[[? ?] ?] ?] ?]|]; [| apply derives_refl].
  Intros key spub. apply data_at_data_at_.
Qed.

Lemma hrx5_b8eb_st x25519 aead_dec R T PS o st :
  hrx5_st_rep x25519 aead_dec R T PS o st |-- @data_at_ HCS Tsh t_mstate st.
Proof.
  unfold hrx5_st_rep. destruct o; try apply derives_refl.
  destruct (hrx5_fwd _); [| apply derives_refl].
  destruct (hrx5cr_tgt _ _ _ _ _ _) as [[[[? ?] ?] ?]|]; [| apply derives_refl].
  apply data_at_data_at_.
Qed.

Lemma hrx5_b8eb_pt xaead_enc xaead_dec T PS o pt :
  xaead_props xaead_enc xaead_dec -> obj_ok o ->
  hrx5_pt_rep xaead_dec T PS o pt |-- hout Tsh 16 pt.
Proof.
  intros HX Ho. unfold hrx5_pt_rep. destruct o as [| | |M]; try apply derives_refl.
  destruct (hrx5_fwd _); [| apply derives_refl].
  destruct (hrx5ck_tgt xaead_dec T PS M) as [[[a P] p]|] eqn:E; [| apply derives_refl].
  assert (Hl: Zlength p = 16).
  { unfold hrx5ck_tgt in E.
    destruct (t_find_index _ _ _) as [[? E0]|]; [|discriminate].
    destruct (Int.eq _ _); [discriminate|].
    destruct (sfind _ _) as [[? P0]|]; [|discriminate].
    destruct (ck_sent _); [|discriminate].
    destruct (xaead_dec _ _ _ _) eqn:Ed; [|discriminate].
    inv E. apply (xaead_dec_length _ _ HX) in Ed. destruct Ho as [_ Le]. rewrite Le in Ed. lia. }
  unfold hbytes, hout. rewrite Hl. apply data_at_data_at_.
Qed.

Lemma hrx5_B8E_B_ok : hrx5_B8E_B_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc q
    proto ip4 ip6 port o dp img tg ai ar sec1 birth1 S1 lul1 path HY.
  unfold hrx5_B8E_Q1. unfold hrx5_Delta, hrx5_B8E_B. simplify_func_tycontext. abbreviate_semax.
  unfold rxw_rep, hrx5_B8E_W, hrx5_rest, hrx5_cglobs, hrx5_scr5, hrx5_lvars, hrx5_ptrs;
    cbn [app rw_D rw_T rw_PS rw_KS rw_S rw_w rw_kc rw_lul rw_rx keypairs_rep iter_sepcon].
  change (d_itab (hrx5_DL x25519 R L sec1 birth1)) with (l_itd L).
  change (d_ptab (hrx5_DL x25519 R L sec1 birth1)) with (l_ptd L).
  Intros.
  match goal with Hi: hrx5_inv _ _ _ _ _ _ _ _ _ |- _ => rename Hi into Hinv end.
  assert_PROP (itable_wf T) as HwfT by (unfold itable at 1; entailer!).
  assert_PROP (is_pointer_or_null (hd nullval (t_L T))) as Hhd.
  { sep_apply (hrx5_b8eb_hd_pn Tsh (l_itd L) T). entailer!. }
  assert_PROP (is_pointer_or_null (hrx5_head (hnodes_snapped4 T NS PS))) as Hhn.
  { sep_apply (hrx5_b8eb_hn_pn (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS)). entailer!. }
  destruct (hrx5_b8eb_facts0 x25519 R L sec1 birth1 NS PS KE T head nk Hinv HwfT)
    as (Hvo & Hq1 & Hq2 & Hq3 & Hq4 & Hq5 & Hq6 & Hq7 & Hq8 & Hq9 & Hq10 & Hsame & HPo & Hkp).
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: (hrx5_S8 x25519 gv L FR) end.
  { apply ENTAIL_refl. }
  { forward.
    sep_apply (hrx5_b8eb_vo Tsh (l_wd L) (hrx5_DL x25519 R L sec1 birth1) (hrx5_khead (map (kent_snapped T) KE))
                 (map (kent_snapped T) KE)).
    forward_call (hrx5_head (hnodes_snapped4 T NS PS), hnodes_snapped4 T NS PS, PS,
                  hrx5_b8eb_sns T PS, hrx5_b8eb_rs PS, hrx5_b8eb_prs PS, nullval, Tsh, l_itd L, T,
                  hrx5_b8eb_VO x25519 R L sec1 birth1 T KE).
    rewrite Hsame.
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HRM._t'223 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    { rewrite hrx5_b8eb_itable_open. Intros.
      forward.
      sep_apply (hrx5_b8eb_itable_fold Tsh (l_itd L) T HwfT).
      forward.
      { entailer!. apply denote_tc_test_eq_split;
          (apply (derives_trans _ (itable Tsh (l_itd L) T * TT)); [cancel | apply sepcon_valid_pointer1; apply hrx5_b8eb_hd_valid]). }
      rewrite (hrx5_b8eb_cmp_self _ Hhd). entailer!. }
    { exfalso. apply Int.one_not_zero. assumption. }
    unfold hrx5_b8eb_VO. rewrite <- hrx5_b8eb_vo. rewrite hrx5_b8eb_khead_snapped.
    rewrite (hrx5_b8eb_vo1 PS). flatten_sepcon_in_SEP.
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HRM._t'224 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    { forward_call (hrx5_khead KE, map (kent_snapped T) KE, Tsh, l_itd L, T, [VPeers PS]).
      rewrite hrx5_b8eb_kents_refl. forward. entailer!. }
    { exfalso. apply Int.one_not_zero. assumption. }
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HRM._t'226 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    { forward_call (gv, Tsh, l_ss L, S, w, S1, w).
      rewrite H2. forward. entailer!. }
    { exfalso. apply Int.one_not_zero. assumption. }
    forward_if.
    { exfalso. apply Int.one_not_zero. assumption. }
    forward. rewrite <- hrx5_b8eb_vo1. rewrite hrx5_b8eb_khead_snapped. entailer!. }
  { forward.
    unfold loop2_ret_assert. destruct (hrx5_RB x25519 gv L FR) as [r1 r2 r3 r4]. cbn [RA_break].
    unfold hrx5_S8.
    Exists R sec1 birth1 S1 w (hnodes_snapped4 T NS PS) PS T.
    Exists head nk (map (kent_snapped T) KE) st i kc lul1 q.
    Exists proto ip4 ip6 port o dp img.
    unfold hrx5_ltemps. rewrite hrx5_b8eb_khead_snapped, H1.
    pose proof (hrx5_b8eb_inv x25519 R L NS PS KE T head nk Hinv) as HI.
    unfold hrx5_lvars, hrx5_wcore, hrx5_globs, hrx5_rglobs, hrx5_scr; cbn [app].
    entailer!.
    unfold hrx5_rest. cbn [app fold_right_sepcon]. rewrite hrx5_b8eb_khead_snapped.
    sep_apply (hrx5_b8eb_rxlog gv (hrx5_B8E_log path o)). sep_apply (hrx5_b8eb_qlen gv q).
    sep_apply (hrx5_b8eb_ci x25519 aead_dec R PS o (s_boot S) (l_ci L)).
    sep_apply (hrx5_b8eb_st x25519 aead_dec R T PS o (l_st L)).
    sep_apply (hrx5_b8eb_pt xaead_enc xaead_dec T PS o (l_pt L) (proj2 (proj2 HY)) H8).
    sep_apply (@data_at_data_at_ CKS Tsh t_devsnap (devsnap_val (hrx5_DL x25519 R L sec1 birth1) head) (l_ds L)).
    sep_apply (@data_at_data_at_ CKS Tsh t_shimsnap (shimsnap_val S w) (l_ss L)).
    sep_apply (@data_at_data_at_ CKS Tsh t_skbsnap (skbsnap_val (hrx5_skb dp o proto ip4 ip6 port)) (l_sks L)).
    cancel. }
  unfold POSTCONDITION, abbreviate, overridePost. destruct (hrx5_RB x25519 gv L FR) as [r1 r2 r3 r4].
  cbn [RA_normal]. apply andp_left2. apply derives_refl.
Qed.
