(* law cookie_mac: main's phase P5c, statements 68 of hck5_cut.v:
   NEW (v2): CHECK(hs_same(&hs0, &p.handshake) && pr_same_but_cookie(&ps0, &p) && p.refcount.refcount == refs0 && dev_same(&da, &wa) && dev_same(&db, &wb) && shim_same(&ss) && ita.head == head0 && kents_same(kes)).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_mac.hck5_cut.
Require Import WgNoise.proof.harness.cookie_mac.hck5_spec.
Require Import WgNoise.proof.harness.cookie_mac.hck5_defs.
Require Import WgNoise.proof.harness.cookie_mac.hck5_conv.
Require Import WgNoise.proof.harness.cookie_mac.hck5_p5c_lemmas.
Require WgNoise.harness.x_cookie_mac.code.
Module HCM := WgNoise.harness.x_cookie_mac.code.

#[local] Existing Instance W_cookie_mac.
Local Open Scope Z_scope.

Lemma hck5_p5c_voD sh wg D : device_rep sh wg D = vobjs W_cookie_mac [VDev sh wg D].
Proof. apply (hck5_p5c_vo1 (VDev sh wg D)). Qed.

Lemma hck5_p5c_voI sh tab T : itable sh tab T = vobjs W_cookie_mac [VItab sh tab T].
Proof. apply (hck5_p5c_vo1 (VItab sh tab T)). Qed.

Lemma hck5_p5c_voP sh p P : peer_rep sh p P = vobjs W_cookie_mac [VPeer sh p P].
Proof. apply (hck5_p5c_vo1 (VPeer sh p P)). Qed.

Lemma hck5_p5c_voDK sh wg D l KE :
  (device_rep sh wg D * kents_rep W_cookie_mac l KE)%logic = vobjs W_cookie_mac [VDev sh wg D; VKents l KE].
Proof. apply (hck5_p5c_vo2 (VDev sh wg D) (VKents l KE)). Qed.

(* common4 v4.1: VKents lends no address; lend A's index table (the kents' entries) with the device *)
Lemma hck5_p5c_voDI sh wg D sht tab T :
  (device_rep sh wg D * itable sht tab T)%logic = vobjs W_cookie_mac [VDev sh wg D; VItab sht tab T].
Proof. apply (hck5_p5c_vo2 (VDev sh wg D) (VItab sht tab T)). Qed.

Lemma hck5_p5c_kincl L A D :
  hck5_aok L A ->
  incl (map ke_addr (a_KE A)) (vobjs_addrs [VDev Tsh (l_wa L) D; VItab Tsh (l_ita L) (a_T A)]).
Proof.
  intros (_ & _ & _ & _ & _ & _ & Hsa & _) x Hx. unfold vobjs_addrs; simpl. rewrite app_nil_r.
  right; right; right. right. rewrite Hsa. apply in_or_app. left. exact Hx.
Qed.

Lemma hck5_p5c_voIP sh tab T shp p P :
  (itable sh tab T * peer_rep shp p P)%logic = vobjs W_cookie_mac [VItab sh tab T; VPeer shp p P].
Proof. apply (hck5_p5c_vo2 (VItab sh tab T) (VPeer shp p P)). Qed.

Section P5c.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hck5_P5c_ok {Espec: OracleKind} gv L FR :
  hck5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hck5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hck5_S5 x25519 gv L FR) hck5_P5c
    (overridePost (hck5_S5c x25519 gv L FR) (hck5_R gv)).
Proof.
  intros HH. unfold hck5_S5, hck5_Delta, hck5_R, hck5_P5c. simplify_func_tycontext. abbreviate_semax.
  Intros R S A m c Q cmode C ck MSG1 C1.
  unfold hck5_A, hck5_bside, hck5_bufs, hck5_scr2, hck5_snaps, hck5_globs, hck5_lvars. cbn [app].
  pose proof H0 as Hok.
  assert_PROP (itable_wf (a_T A)) as Hwf by (sep_apply (hck5_p5c_itable_wf Tsh (l_ita L) (a_T A)); entailer!).
  sep_apply (hck5_p5c_fold_d Tsh (l_p L) (a_P A) C1).
  sep_apply (hck5_p5c_dev_in x25519 R L (hck5_CC2 x25519 R L (q_now Q) cmode)).
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end; [entailer! | | ].
  { (* hs_same(&hs0, &p.handshake) *)
    rewrite (hck5_p5c_voD Tsh (l_wa L) (hck5_DA x25519 R L)).
    change (peer_rep Tsh (l_p L) (p_set_cookie (a_P A) C1)) with (hs_mem true Tsh (l_p L) (p_set_cookie (a_P A) C1)).
    forward_call (Tsh, l_hs0 L, hs_snap_cur (a_T A) (l_p L) (a_P A), Tsh, l_p L, p_set_cookie (a_P A) C1, true,
                  Tsh, l_ita L, a_T A, [VDev Tsh (l_wa L) (hck5_DA x25519 R L)]).
    { split; [repeat constructor; apply readable_share_top |].
      split; [apply (hck5_p5c_hs_in L A Hok) |].
      apply hck5_p5c_hs_pre; auto. cbn. right. left. reflexivity. }
    rewrite hck5_p5c_snap_cur.
    change (hs_mem true Tsh (l_p L) (p_set_cookie (a_P A) C1)) with (peer_rep Tsh (l_p L) (p_set_cookie (a_P A) C1)).
    rewrite <- (hck5_p5c_voD Tsh (l_wa L) (hck5_DA x25519 R L)).
    (* pr_same_but_cookie(&ps0, &p) *)
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HK._t'53 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    { sep_apply (hck5_p5c_voDI Tsh (l_wa L) (hck5_DA x25519 R L) Tsh (l_ita L) (a_T A)).
      forward_call (Tsh, l_ps0 L, p_set_cookie (a_P A) C, Tsh, l_p L, p_set_cookie (a_P A) C1,
                    [VDev Tsh (l_wa L) (hck5_DA x25519 R L); VItab Tsh (l_ita L) (a_T A)]).
      { split; [repeat constructor; apply readable_share_top |].
        apply hck5_p5c_pr_pre; auto.
        - unfold vobjs_addrs; simpl; auto.
        - exact (hck5_p5c_kincl L A (hck5_DA x25519 R L) Hok). }
      rewrite hck5_p5c_pr_nc.
      rewrite <- (hck5_p5c_voDI Tsh (l_wa L) (hck5_DA x25519 R L) Tsh (l_ita L) (a_T A)). flatten_sepcon_in_SEP.
      forward. entailer!. }
    { exfalso. apply Int.one_not_zero. auto. }
    (* p.refcount.refcount == refs0 *)
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HK._t'55 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    { sep_apply (hck5_p5c_unfold_d Tsh (l_p L) (a_P A) C1).
      rewrite (hck5_p5c_open Tsh (l_p L) (a_P A)). Intros.
      forward. forward.
      sep_apply (hck5_p5c_close Tsh (l_p L) (a_P A)).
      sep_apply (hck5_p5c_fold_d Tsh (l_p L) (a_P A) C1).
      entailer!. rewrite Int.eq_true. reflexivity. }
    { exfalso. apply Int.one_not_zero. auto. }
    (* dev_same(&da, &wa) *)
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HK._t'56 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    { sep_apply (hck5_p5c_voIP Tsh (l_ita L) (a_T A) Tsh (l_p L) (p_set_cookie (a_P A) C1)).
      change (ptable Tsh (l_pta L) (l_p L)) with (ptable Tsh (d_ptab (hck5_DA x25519 R L)) (l_p L)).
      forward_call (Tsh, l_da L, hck5_DA x25519 R L, l_p L, Tsh, l_wa L, hck5_DA x25519 R L, Tsh, l_p L,
                    [VItab Tsh (l_ita L) (a_T A); VPeer Tsh (l_p L) (p_set_cookie (a_P A) C1)]).
      { split; [repeat constructor; apply readable_share_top |].
        apply hck5_p5c_da_pre; unfold vobjs_addrs; simpl; rewrite ?app_nil_r.
        - left. reflexivity.
        - right. apply in_or_app. right. left. reflexivity. }
      rewrite hck5_p5c_dev_refl.
      change (ptable Tsh (d_ptab (hck5_DA x25519 R L)) (l_p L)) with (ptable Tsh (l_pta L) (l_p L)).
      rewrite <- (hck5_p5c_voIP Tsh (l_ita L) (a_T A) Tsh (l_p L) (p_set_cookie (a_P A) C1)). flatten_sepcon_in_SEP.
      forward. entailer!. }
    { exfalso. apply Int.one_not_zero. auto. }
    (* dev_same(&db, &wb) *)
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HK._t'58 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    { rewrite (hck5_p5c_voI Tsh (l_itb L) (mkT [] [])).
      change (ptable Tsh (l_ptb L) nullval) with
        (ptable Tsh (d_ptab (hck5_DBc x25519 R L (hck5_CC2 x25519 R L (q_now Q) cmode))) nullval).
      forward_call (Tsh, l_db L, hck5_DBc x25519 R L (hck5_CC2 x25519 R L (q_now Q) cmode), nullval, Tsh, l_wb L,
                    hck5_DBc x25519 R L (hck5_CC2 x25519 R L (q_now Q) cmode), Tsh, nullval,
                    [VItab Tsh (l_itb L) (mkT [] [])]).
      { split; [repeat constructor; apply readable_share_top |].
        apply hck5_p5c_db_pre; [apply hck5_p5c_cc2_dev | unfold vobjs_addrs; simpl; left; reflexivity]. }
      rewrite hck5_p5c_dev_refl.
      change (ptable Tsh (d_ptab (hck5_DBc x25519 R L (hck5_CC2 x25519 R L (q_now Q) cmode))) nullval) with
        (ptable Tsh (l_ptb L) nullval).
      rewrite <- (hck5_p5c_voI Tsh (l_itb L) (mkT [] [])).
      forward. entailer!. }
    { exfalso. apply Int.one_not_zero. auto. }
    (* shim_same(&ss) *)
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HK._t'60 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    { forward_call (gv, Tsh, l_ss L, S, hck5_w0, S, hck5_w0).
      rewrite hck5_p5c_shim_refl. forward. entailer!. }
    { exfalso. apply Int.one_not_zero. auto. }
    (* ita.head == head0 *)
    pose proof Hok as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsnap & Hhead).
    pose proof (hck5_p5c_hd_pn L A Hok Hwf) as Hhd.
    rewrite Hhead.
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HK._t'62 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    { rewrite (hck5_p5c_itable_open Tsh (l_ita L) (a_T A)). Intros.
      forward.
      sep_apply (hck5_p5c_itable_fold Tsh (l_ita L) (a_T A) Hwf).
      forward.
      { entailer!. apply denote_tc_test_eq_split;
          (apply (derives_trans _ (itable Tsh (l_ita L) (a_T A) * TT)%logic); [cancel | apply sepcon_valid_pointer1; apply hck5_p5c_hd_valid]). }
      entailer!.
      revert Hhd. generalize (hd nullval (t_L (a_T A))). intros v Hv. destruct v; try contradiction.
      - cbn in Hv. subst. reflexivity.
      - unfold eval_binop, sem_binary_operation', sem_cmp; cbn. unfold sem_cmp_pp, Val.cmplu_bool; cbn.
        rewrite if_true by reflexivity. rewrite Ptrofs.eq_true. reflexivity. }
    { exfalso. apply Int.one_not_zero. auto. }
    (* kents_same(kes) *)
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HK._t'63 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    { rewrite (hck5_p5c_voP Tsh (l_p L) (p_set_cookie (a_P A) C1)).
      forward_call (a_kes A, a_KE A, Tsh, l_ita L, a_T A, [VPeer Tsh (l_p L) (p_set_cookie (a_P A) C1)]).
      { split; [repeat constructor; apply readable_share_top |].
        apply (hck5_p5c_kents_pre L A); auto. unfold vobjs_addrs; simpl; auto. }
      rewrite (hck5_p5c_kents_refl _ _ Hsnap).
      rewrite <- (hck5_p5c_voP Tsh (l_p L) (p_set_cookie (a_P A) C1)).
      forward. entailer!. }
    { exfalso. apply Int.one_not_zero. auto. }
    forward_if True.
    { exfalso. apply Int.one_not_zero. auto. }
    { forward. entailer!. }
    forward. rewrite <- Hhead. entailer!. }
  (* after the CHECK: the snapshots are dropped *)
  sep_apply (hck5_p5c_unfold_d Tsh (l_p L) (a_P A) C1).
  sep_apply (hck5_p5c_dev_out x25519 R L (hck5_CC2 x25519 R L (q_now Q) cmode)).
  unfold hck5_S5c. Exists R S A m c Q cmode C ck MSG1 C1.
  unfold hck5_A, hck5_bside, hck5_bufs, hck5_scr2, hck5_snaps0, hck5_globs, hck5_lvars. cbn [app].
  (* by hand: entailer! times out on this SEP *)
  sep_apply (@data_at_data_at_ HCS Tsh t_hsnap (hsnap_val (hs_snap_cur (a_T A) (l_p L) (a_P A))) (l_hs0 L)).
  sep_apply (@data_at_data_at_ CKS Tsh t_prsnap (prsnap_val (p_set_cookie (a_P A) C)) (l_ps0 L)).
  sep_apply (@data_at_data_at_ CKS Tsh t_devsnap (devsnap_val (hck5_DA x25519 R L) (l_p L)) (l_da L)).
  sep_apply (@data_at_data_at_ CKS Tsh t_devsnap
               (devsnap_val (hck5_DBc x25519 R L (hck5_CC2 x25519 R L (q_now Q) cmode)) nullval) (l_db L)).
  sep_apply (@data_at_data_at_ CKS Tsh t_shimsnap (shimsnap_val S hck5_w0) (l_ss L)).
  apply andp_right; [apply prop_right; cbn [fold_right]; repeat (split; [assumption |]); exact I |].
  apply andp_left2. unfold PROPx at 1. apply andp_left2. unfold LOCALx.
  apply andp_derives; [apply derives_refl |].
  intro rho. unfold SEPx. cbv beta. cbn [fold_right_sepcon]. cancel.
Qed.

End P5c.
