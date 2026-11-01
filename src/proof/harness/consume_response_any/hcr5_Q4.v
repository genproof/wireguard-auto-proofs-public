(* law consume_response_any, phase Q4: statements 14..16 of P6's then-branch: resp_img(img_after, msg); CHECK(bytes_eq(img, img_after, RESP_LEN)); CHECK(dev_same(&ds, &wa) && ita.head == head0 && kents_same(kes) && shim_same(&ss)).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_cut.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_model.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_spec.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_conv.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q4_pure.
Require WgNoise.harness.x_consume_response_any.code.

#[local] Existing Instance W_consume_response_any.
Local Open Scope logic.

#[local] Instance hcr5_q4_cceN : change_composite_env Noise.CS W_consume_response_any.
Proof. make_cs_preserve Noise.CS W_consume_response_any. Defined.

Lemma hcr5_q4_len M : rm_ok M -> Zlength (resp_bytes M) = 92.
Proof.
  intros (H1 & H2 & H3 & H4). unfold resp_bytes, le32. rewrite !Zlength_app, !Zlength_map.
  rewrite H1, H2, H3, H4. reflexivity.
Qed.

(* the index table's head field at the world *)
Lemma hcr5_q4_itab_W sh (v: val) p :
  @data_at Noise.CS sh t_itab v p = @data_at W_consume_response_any sh t_itab v p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W_consume_response_any _ sh t_itab v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hcr5_q4_itable_open sht tab T :
  itable sht tab T = (!! itable_wf T &&
    (@data_at W_consume_response_any sht t_itab (hd nullval (t_L T)) tab *
     iter_sepcon (pool_item_rep (t_L T)) (t_D T)))%logic.
Proof. unfold itable. rewrite hcr5_q4_itab_W. reflexivity. Qed.

Lemma hcr5_q4_itable_fold sht tab T : itable_wf T ->
  (@data_at W_consume_response_any sht t_itab (hd nullval (t_L T)) tab *
   iter_sepcon (pool_item_rep (t_L T)) (t_D T) |-- itable sht tab T)%logic.
Proof. intros HT. rewrite hcr5_q4_itable_open. entailer!. Qed.

(* the table's first entry is a valid pointer (NULL or a pool entry) *)
Lemma hcr5_q4_hd_valid sht tab T : itable sht tab T |-- valid_pointer (hd nullval (t_L T)).
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

Lemma hcr5_q4_kptrs l KE : kents_rep W_consume_response_any l KE |-- !! Forall (fun e => isptr (ke_addr e)) KE.
Proof.
  revert l; induction KE as [| e KE IH]; intros l; cbn [kents_rep].
  - entailer!.
  - Intros nx. sep_apply (IH nx). unfold kent_cell. entailer!.
    constructor; [| assumption].
    match goal with X: field_compatible t_kent [] (ke_addr e) |- _ => destruct X; assumption end.
Qed.

(* lent objects *)
Lemma hcr5_q4_vo2 sh tab T PS :
  itable sh tab T * peers_rep PS = vobjs W_consume_response_any [VItab sh tab T; VPeers PS].
Proof. unfold vobjs. cbn [iter_sepcon vobj_rep]. rewrite sepcon_emp. reflexivity. Qed.

Lemma hcr5_q4_vo1 PS : peers_rep PS = vobjs W_consume_response_any [VPeers PS].
Proof. unfold vobjs. cbn [iter_sepcon vobj_rep]. rewrite sepcon_emp. reflexivity. Qed.

Lemma hcr5_q4_RAn (Q: environ -> mpred) (Rr: ret_assert) : RA_normal (overridePost Q Rr) = Q.
Proof. destruct Rr; reflexivity. Qed.

Section Phase.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcr5_Q4_ok {Espec: OracleKind} gv L FR :
  hcr5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> 
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_SQ3 x25519 aead_dec gv L FR) hcr5_Q4
    (overridePost (hcr5_SQ4 x25519 aead_dec gv L FR) (hcr5_R gv)).
Proof.
  intros HH. unfold hcr5_SQ3, hcr5_Delta, hcr5_R, hcr5_Q4. simplify_func_tycontext. abbreviate_semax.
  Intros R S NS PS head nb T KE m M.
  unfold hcr5_lvars, hcr5_world, hcr5_globs, hcr5_snaps; cbn [app].
  forward_call (Tsh, l_imga L, Ews, m, M).
  assert (Hl: Zlength (resp_bytes M) = 92) by (apply hcr5_q4_len; auto).
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end; [entailer! | | ].
  { forward_call (Tsh, l_img L, resp_bytes M, Tsh, l_imga L, resp_bytes M).
    { rewrite Hl. entailer!. }
    rewrite hcr5_q4_bytes. forward_if True.
    { exfalso. apply Int.one_not_zero. auto. }
    { forward. entailer!. }
    forward. entailer!. }
  assert_PROP (itable_wf T) as HwfT by (unfold itable; entailer!).
  assert_PROP (Forall (fun e => isptr (ke_addr e)) KE) as Hkp by (sep_apply (hcr5_q4_kptrs (hcr5_khead KE) (map (kent_snapped T) KE)); entailer!; rewrite Forall_map in *; auto).
  pose proof H0 as Hok. destruct Hok as (Hpok & Hwf & Hch & Hnp & Hnd & Hnb).
  pose proof (hcr5_q4_hd_pn L KE NS PS head nb T H0 H1 HwfT Hkp) as Hhd.
  set (PS' := peers_after PS (hcr5_res x25519 aead_dec R L T PS M)).
  assert (HPS: map peer_addr4 PS' = map peer_addr4 PS) by apply hcr5_q4_after_addrs.
  assert (HPSo: vobj_ok (VPeers PS')) by (eapply hcr5_q4_after_ok; eauto).
  sep_apply (hcr5_q4_vo2 Tsh (l_ita L) T PS').
  change (ptable Tsh (l_pta L) head) with (ptable Tsh (d_ptab (hcr5_DAL x25519 R L)) head).
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end; [entailer! | | ].
  { forward_call (Tsh, l_ds L, hcr5_DAL x25519 R L, head, Tsh, l_wa L, hcr5_DAL x25519 R L, Tsh, head,
                  [VItab Tsh (l_ita L) T; VPeers PS']).
    { split; [repeat constructor; auto; apply readable_share_top |].
      apply hcr5_q4_dpre with (PS := PS); auto. }
    rewrite hcr5_q4_dev_refl.
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HR5._t'25 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    1: rewrite <- hcr5_q4_vo2; rewrite hcr5_q4_itable_open; Intros;
      forward;
      sep_apply (hcr5_q4_itable_fold Tsh (l_ita L) T HwfT);
      forward.
    { entailer!. apply denote_tc_test_eq_split;
          (apply (derives_trans _ (itable Tsh (l_ita L) T * TT)); [cancel | apply sepcon_valid_pointer1; apply hcr5_q4_hd_valid]). }
    { assert (Hc: force_val (sem_cast tint tbool (eval_binop Oeq (tptr (Tstruct HR5._index_hashtable_entry noattr)) (tptr (Tstruct HR5._index_hashtable_entry noattr)) (hd nullval (t_L T)) (hd nullval (t_L T)))) = Vint Int.one).
      { revert Hhd. generalize (hd nullval (t_L T)). intros v Hv. destruct v; try contradiction.
        - cbn in Hv. subst. reflexivity.
        - unfold eval_binop, sem_binary_operation', sem_cmp; cbn. unfold sem_cmp_pp, Val.cmplu_bool; cbn. rewrite if_true by reflexivity. rewrite Ptrofs.eq_true. reflexivity. }
      rewrite Hc. sep_apply (hcr5_q4_vo2 Tsh (l_ita L) T PS'). entailer!. }
    { exfalso. apply Int.one_not_zero. auto. }
    rewrite <- hcr5_q4_vo2. rewrite (hcr5_q4_vo1 PS'). flatten_sepcon_in_SEP.
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HR5._t'26 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    { forward_call (hcr5_khead KE, map (kent_snapped T) KE, Tsh, l_ita L, T, [VPeers PS']).
      { eapply hcr5_q4_kpre; eauto. }
      rewrite hcr5_q4_kents_refl. forward. entailer!. }
    { exfalso. apply Int.one_not_zero. auto. }
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HR5._t'28 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    { forward_call (gv, Tsh, l_ss L, S, hcr5_w0, S, hcr5_w0).
      rewrite hcr5_q4_shim_refl. forward. entailer!. }
    { exfalso. apply Int.one_not_zero. auto. }
    forward_if True.
    { exfalso. apply Int.one_not_zero. auto. }
    { forward. entailer!. }
    forward. rewrite <- (hcr5_q4_vo1 PS'). sep_apply (hcr5_q4_vo2 Tsh (l_ita L) T PS'). entailer!. }
  rewrite <- hcr5_q4_vo2. unfold hcr5_SQ4.
  Exists R S NS PS head nb T KE m M.
  unfold hcr5_lvars, hcr5_world, hcr5_globs, hcr5_snaps; cbn [app].
  change (d_ptab (hcr5_DAL x25519 R L)) with (l_pta L). subst PS'.
  entailer!.
Qed.

End Phase.
