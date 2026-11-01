(* law cookie_reply, phase P12, segment Y:
   s72: CHECK(dev_same(&da, &wa) && ita.head == head0 && kents_same(kes) && shim_same(&ss)) (NEW; template: consume_response_any's hcr5_Q4.v).
   St -> St over fixed values (hcy5_p12_defs.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p12_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p12_y_pure.
Require WgNoise.harness.x_cookie_reply.code.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

#[local] Instance hcy5_p12_y_cceN : change_composite_env Noise.CS W.
Proof. make_cs_preserve Noise.CS W. Defined.

(* the index table's head field at the world *)
Lemma hcy5_p12_y_itab_W sh (v: val) p :
  @data_at Noise.CS sh t_itab v p = @data_at W sh t_itab v p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W _ sh t_itab v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hcy5_p12_y_itable_open sht tab T :
  itable sht tab T = (!! itable_wf T &&
    (@data_at W sht t_itab (hd nullval (t_L T)) tab *
     iter_sepcon (pool_item_rep (t_L T)) (t_D T)))%logic.
Proof. unfold itable. rewrite hcy5_p12_y_itab_W. reflexivity. Qed.

Lemma hcy5_p12_y_itable_fold sht tab T : itable_wf T ->
  (@data_at W sht t_itab (hd nullval (t_L T)) tab *
   iter_sepcon (pool_item_rep (t_L T)) (t_D T) |-- itable sht tab T)%logic.
Proof. intros HT. rewrite hcy5_p12_y_itable_open. entailer!. Qed.

(* the table's first entry: NULL or a pool entry *)
Lemma hcy5_p12_y_hd_in sht tab T : itable sht tab T |--
  !! (hd nullval (t_L T) = nullval \/ exists sh E, In (hd nullval (t_L T), sh, E) (t_D T) /\ writable_share sh).
Proof.
  unfold itable. Intros. destruct H as (_ & Hinc & _ & Hw).
  destruct (t_L T) as [| v l] eqn:EL; cbn [hd]; [apply prop_right; left; reflexivity |].
  assert (Hv: In v (saddrs (t_D T))) by (apply Hinc; left; reflexivity).
  unfold saddrs in Hv; apply in_map_iff in Hv; destruct Hv as ([[a sh] E] & Ha & Hin); cbn in Ha; subst a.
  rewrite Forall_forall in Hw; specialize (Hw _ Hin); cbn in Hw.
  apply prop_right. right. exists sh, E. auto.
Qed.

Lemma hcy5_p12_y_hd_valid sht tab T : itable sht tab T |-- valid_pointer (hd nullval (t_L T)).
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

Lemma hcy5_p12_y_hd_pn sht tab T : itable sht tab T |-- !! is_pointer_or_null (hd nullval (t_L T)).
Proof.
  unfold itable. Intros. destruct H as (_ & Hinc & _ & Hw).
  destruct (t_L T) as [| v l] eqn:EL; cbn [hd]; [apply prop_right; reflexivity |].
  assert (Hv: In v (saddrs (t_D T))) by (apply Hinc; left; reflexivity).
  unfold saddrs in Hv; apply in_map_iff in Hv; destruct Hv as ([[a sh] E] & Ha & Hin); cbn in Ha; subst a.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply (iter_sepcon_in_true (pool_item_rep (v :: l)) (t_D T) _ Hin)] |].
  unfold pool_item_rep, entry_at. entailer!.
  match goal with X: field_compatible t_entry_s _ _ |- _ => destruct X as [Hp _] end.
  destruct v; try contradiction; exact I.
Qed.

(* lent objects *)
Lemma hcy5_p12_y_vo2 sh tab T PS :
  (itable sh tab T * peers_rep PS = vobjs W [VItab sh tab T; VPeers PS])%logic.
Proof. unfold vobjs. cbn [iter_sepcon vobj_rep]. rewrite sepcon_emp. reflexivity. Qed.

Lemma hcy5_p12_y_vo1 PS : peers_rep PS = vobjs W [VPeers PS].
Proof. unfold vobjs. cbn [iter_sepcon vobj_rep]. rewrite sepcon_emp. reflexivity. Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_p12_Y_ok {Espec: OracleKind} gv L FR R S m c rp Q nonce rr CK CM NS PS T np CL KE CM' honest now2 :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hcy5_p12_inv x25519 xaead_enc R L Q m nonce rr CK CM NS PS T np CL KE CM' honest now2 ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hcy5_p12_St x25519 xaead_dec gv L FR R S m c rp Q rr CK NS PS T np CL KE CM' honest now2)
    hcy5_p12_s72
    (normal_ret_assert (hcy5_p12_St x25519 xaead_dec gv L FR R S m c rp Q rr CK NS PS T np CL KE CM' honest now2)).
Proof.
  intros HH HI. unfold hcy5_p12_St, hcy5_Delta, hcy5_p12_s72. simplify_func_tycontext. abbreviate_semax.
  unfold hcy5_aside, hcy5_lvars, hcy5_globs, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB; cbn [app].
  destruct HI as (_ & Hlists & _ & HTok & _). destruct Hlists as (Hpok & _).
  assert_PROP (itable_wf T) as HwfT by (unfold itable; entailer!).
  assert_PROP (is_pointer_or_null (hd nullval (t_L T))) as Hhd
    by (sep_apply (hcy5_p12_y_hd_pn Tsh (l_ita L) T); entailer!).
  set (PS' := peers_after PS (hcy5_res xaead_dec T PS CM' now2)).
  assert (HPS: map peer_addr4 PS' = map peer_addr4 PS) by apply hcy5_p12_y_after_addrs.
  assert (Hh': hcy5_phead PS' = hcy5_phead PS) by apply hcy5_p12_y_phead_after.
  assert (HPSo: vobj_ok (VPeers PS')) by (eapply hcy5_p12_y_after_ok; eauto).
  sep_apply (hcy5_p12_y_vo2 Tsh (l_ita L) T PS').
  change (ptable Tsh (l_pta L) (hcy5_phead PS')) with (ptable Tsh (d_ptab (hcy5_DA x25519 R L)) (hcy5_phead PS')).
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end; [entailer! | | ].
  { forward_call (Tsh, l_da L, hcy5_DA x25519 R L, hcy5_phead PS, Tsh, l_wa L, hcy5_DA x25519 R L, Tsh,
                  hcy5_phead PS', [VItab Tsh (l_ita L) T; VPeers PS']).
    { split; [repeat constructor; auto; apply readable_share_top |].
      apply hcy5_p12_y_dpre; auto. }
    assert (Hde: dev_eqb (hcy5_DA x25519 R L) (hcy5_phead PS) (hcy5_DA x25519 R L) (hcy5_phead PS') = true)
      by (rewrite Hh'; apply hcy5_p12_y_dev_refl).
    rewrite Hde.
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HY._t'69 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    1: rewrite <- hcy5_p12_y_vo2; rewrite hcy5_p12_y_itable_open; Intros;
      forward;
      sep_apply (hcy5_p12_y_itable_fold Tsh (l_ita L) T HwfT);
      forward.
    { entailer!. apply denote_tc_test_eq_split;
          (apply (derives_trans _ (itable Tsh (l_ita L) T * TT)%logic); [cancel | apply sepcon_valid_pointer1; apply hcy5_p12_y_hd_valid]). }
    { assert (Hc: force_val (sem_cast tint tbool (eval_binop Oeq (tptr (Tstruct HY._index_hashtable_entry noattr)) (tptr (Tstruct HY._index_hashtable_entry noattr)) (hd nullval (t_L T)) (hd nullval (t_L T)))) = Vint Int.one).
      { revert Hhd. generalize (hd nullval (t_L T)). intros v Hv. destruct v; try contradiction.
        - cbn in Hv. subst. reflexivity.
        - unfold eval_binop, sem_binary_operation', sem_cmp; cbn. unfold sem_cmp_pp, Val.cmplu_bool; cbn. rewrite if_true by reflexivity. rewrite Ptrofs.eq_true. reflexivity. }
      rewrite Hc. sep_apply (hcy5_p12_y_vo2 Tsh (l_ita L) T PS'). entailer!. }
    { exfalso. apply Int.one_not_zero. auto. }
    rewrite <- hcy5_p12_y_vo2. rewrite (hcy5_p12_y_vo1 PS'). flatten_sepcon_in_SEP.
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HY._t'70 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    { forward_call (hcy5_khead KE, map (kent_snapped T) KE, Tsh, l_ita L, T, [VPeers PS']).
      { apply hcy5_p12_y_kpre with (PS := PS); auto. }
      rewrite hcy5_p12_y_kents_refl. forward. entailer!. }
    { exfalso. apply Int.one_not_zero. auto. }
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HY._t'72 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    { forward_call (gv, Tsh, l_ss L, S, hcy5_w0, S, hcy5_w0).
      rewrite hcy5_p12_y_shim_refl. forward. entailer!. }
    { exfalso. apply Int.one_not_zero. auto. }
    forward_if True.
    { exfalso. apply Int.one_not_zero. auto. }
    { forward. entailer!. }
    forward. rewrite <- (hcy5_p12_y_vo1 PS'). sep_apply (hcy5_p12_y_vo2 Tsh (l_ita L) T PS'). entailer!. }
  rewrite <- hcy5_p12_y_vo2. subst PS'.
  change (d_ptab (hcy5_DA x25519 R L)) with (l_pta L).
  unfold hcy5_aside, hcy5_lvars, hcy5_globs, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB; cbn [app].
  entailer!.
Qed.

End Seg.
