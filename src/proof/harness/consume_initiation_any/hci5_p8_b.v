(* law consume_initiation_any, phase P8, segment b: statement 33: CHECK(dev_same(&ds, &wb) && itb.head == head0 && kents_same(kes) && shim_same(&ss)); the state does not change.
   States and statements: hci5_p8_defs.v; (section P8).  The statement is
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_cut.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_model.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_globals.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_spec.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_conv.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_b_pure.
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

Local Open Scope logic.

#[local] Instance hci5_p8_b_cceN : change_composite_env Noise.CS W_consume_initiation_any.
Proof. make_cs_preserve Noise.CS W_consume_initiation_any. Defined.

(* the index table's head field at the world *)
Lemma hci5_p8_b_itab_W sh (v: val) p :
  @data_at Noise.CS sh t_itab v p = @data_at W_consume_initiation_any sh t_itab v p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W_consume_initiation_any _ sh t_itab v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hci5_p8_b_itable_open sht tab T :
  itable sht tab T = (!! itable_wf T &&
    (@data_at W_consume_initiation_any sht t_itab (hd nullval (t_L T)) tab *
     iter_sepcon (pool_item_rep (t_L T)) (t_D T)))%logic.
Proof. unfold itable. rewrite hci5_p8_b_itab_W. reflexivity. Qed.

Lemma hci5_p8_b_itable_fold sht tab T : itable_wf T ->
  (@data_at W_consume_initiation_any sht t_itab (hd nullval (t_L T)) tab *
   iter_sepcon (pool_item_rep (t_L T)) (t_D T) |-- itable sht tab T)%logic.
Proof. intros HT. rewrite hci5_p8_b_itable_open. entailer!. Qed.

(* the table's first entry is a valid pointer (NULL or a pool entry) *)
Lemma hci5_p8_b_hd_valid sht tab T : itable sht tab T |-- valid_pointer (hd nullval (t_L T)).
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

(* ... and a pointer or NULL *)
Lemma hci5_p8_b_hd_pn sht tab T : itable sht tab T |-- !! is_pointer_or_null (hd nullval (t_L T)).
Proof.
  unfold itable. Intros. destruct H as (_ & Hinc & _ & Hw).
  destruct (t_L T) as [| v l] eqn:EL; cbn [hd]; [entailer! |].
  assert (Hv: In v (saddrs (t_D T))) by (apply Hinc; left; reflexivity).
  unfold saddrs in Hv; apply in_map_iff in Hv; destruct Hv as ([[a sh] E] & Ha & Hin); cbn in Ha; subst a.
  sep_apply (iter_sepcon_in_true (pool_item_rep (v :: l)) (t_D T) _ Hin).
  unfold pool_item_rep, entry_at. entailer!.
  match goal with X: field_compatible _ _ v |- _ => destruct X as [Hp _]; destruct v; try contradiction; exact I end.
Qed.

(* lent objects *)
Lemma hci5_p8_b_vo2 sh tab T PS :
  itable sh tab T * peers_rep PS = vobjs W_consume_initiation_any [VItab sh tab T; VPeers PS].
Proof. unfold vobjs. cbn [iter_sepcon vobj_rep]. rewrite sepcon_emp. reflexivity. Qed.

Lemma hci5_p8_b_vo1 PS : peers_rep PS = vobjs W_consume_initiation_any [VPeers PS].
Proof. unfold vobjs. cbn [iter_sepcon vobj_rep]. rewrite sepcon_emp. reflexivity. Qed.

Lemma hci5_p8_b_cmp_self2 v : is_pointer_or_null v ->
  force_val (sem_cast tint tbool (eval_binop Oeq (tptr (Tstruct HC5._index_hashtable_entry noattr))
    (tptr (Tstruct HC5._index_hashtable_entry noattr)) v v)) = Vint Int.one.
Proof.
  intros Hv. destruct v; try contradiction.
  - cbn in Hv. subst. reflexivity.
  - unfold eval_binop, sem_binary_operation', sem_cmp; cbn. unfold sem_cmp_pp, Val.cmplu_bool; cbn.
    rewrite if_true by reflexivity. rewrite Ptrofs.eq_true. reflexivity.
Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hci5_p8_b_ok {Espec: OracleKind} gv L FR :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_p8_Q1 x25519 aead_dec gv L FR) hci5_p8_s33
    (overridePost (hci5_p8_Q1 x25519 aead_dec gv L FR) (hci5_R gv)).
Proof.
  intros HH. unfold hci5_p8_Q1 at 1, hci5_Delta, hci5_R, hci5_p8_s33. simplify_func_tycontext. abbreviate_semax.
  Intros R S w NS PS T head na KE m M.
  unfold hci5_lvars, hci5_world, hci5_globs, hci5_p8_scr; cbn [app].
  assert_PROP (itable_wf T) as HwfT by (unfold itable; entailer!).
  assert_PROP (is_pointer_or_null (hd nullval (t_L T))) as Hhd by (sep_apply (hci5_p8_b_hd_pn Tsh (l_itb L) T); entailer!).
  pose proof H0 as Hok. destruct Hok as (Hpok & Hwf & Hch & Hnp & Hna & HTok & Hsl).
  set (PS' := peers_after PS (cin_res x25519 aead_dec (hci5_DB x25519 R L) PS M S)).
  assert (HPS: map peer_addr4 PS' = map peer_addr4 PS) by apply hci5_p8_b_after_addrs.
  assert (HPSo: vobj_ok (VPeers PS')) by (eapply hci5_p8_b_after_ok; eauto).
  sep_apply (hci5_p8_b_vo2 Tsh (l_itb L) T PS').
  change (ptable Tsh (l_ptb L) head) with (ptable Tsh (d_ptab (hci5_DB x25519 R L)) head).
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end; [entailer! | | ].
  { forward_call (Tsh, l_ds L, hci5_DB x25519 R L, head, Tsh, l_wb L, hci5_DB x25519 R L, Tsh, head,
                  [VItab Tsh (l_itb L) T; VPeers PS']).
    { split; [repeat constructor; auto; apply readable_share_top |].
      apply hci5_p8_b_dpre with (PS := PS); auto. }
    rewrite hci5_p8_b_dev_refl.
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HC5._t'32 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    1: rewrite <- hci5_p8_b_vo2; rewrite hci5_p8_b_itable_open; Intros;
      forward;
      sep_apply (hci5_p8_b_itable_fold Tsh (l_itb L) T HwfT);
      forward.
    { entailer!. apply denote_tc_test_eq_split;
          (apply (derives_trans _ (itable Tsh (l_itb L) T * TT)); [cancel | apply sepcon_valid_pointer1; apply hci5_p8_b_hd_valid]). }
    { rewrite (hci5_p8_b_cmp_self2 _ Hhd). sep_apply (hci5_p8_b_vo2 Tsh (l_itb L) T PS'). entailer!. }
    { exfalso. apply Int.one_not_zero. auto. }
    rewrite <- hci5_p8_b_vo2. rewrite (hci5_p8_b_vo1 PS'). flatten_sepcon_in_SEP.
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HC5._t'33 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    { forward_call (hci5_khead KE, map (kent_snapped T) KE, Tsh, l_itb L, T, [VPeers PS']).
      { eapply hci5_p8_b_kpre; eauto. }
      rewrite hci5_p8_b_kents_refl. forward. entailer!. }
    { exfalso. apply Int.one_not_zero. auto. }
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HC5._t'35 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    { forward_call (gv, Tsh, l_ss L, S, w, S, w).
      rewrite hci5_p8_b_shim_refl. forward. entailer!. }
    { exfalso. apply Int.one_not_zero. auto. }
    forward_if True.
    { exfalso. apply Int.one_not_zero. auto. }
    { forward. entailer!. }
    forward. rewrite <- (hci5_p8_b_vo1 PS'). sep_apply (hci5_p8_b_vo2 Tsh (l_itb L) T PS'). entailer!. }
  rewrite <- hci5_p8_b_vo2. unfold hci5_p8_Q1.
  Exists R S w NS PS T head na KE m M.
  unfold hci5_lvars, hci5_world, hci5_globs, hci5_p8_scr; cbn [app].
  change (d_ptab (hci5_DB x25519 R L)) with (l_ptb L). subst PS'.
  entailer!.
Qed.

End Seg.
