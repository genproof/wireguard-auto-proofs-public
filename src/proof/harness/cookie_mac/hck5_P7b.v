(* law cookie_mac: main's phase P7b, statements 87..89 of hck5_cut.v:
   NEW (v2): bytes_copy(db.secret, secret, 32), db.secret_birthdate = secret_birth, CHECK(dev_same(&db, &wb) && dev_same(&da, &wa) && skb_same(&sks, &skb) && hs_same(&hs0, &p.handshake) && pr_same(&ps0, &p) && p.refcount.refcount == refs0 && shim_same(&ss) && ita.head == head0 && kents_same(kes)).
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
Require Import WgNoise.proof.harness.cookie_mac.hck5_p7b_lemmas.
Require WgNoise.harness.x_cookie_mac.code.

#[local] Existing Instance W_cookie_mac.
Local Open Scope Z_scope.

Module HCM := WgNoise.harness.x_cookie_mac.code.

#[local] Instance hck5_p7b_cceK : change_composite_env CKS W_cookie_mac.
Proof. make_cs_preserve CKS W_cookie_mac. Defined.

(* db at the world *)
Lemma hck5_p7b_dbW sh D h p :
  @data_at CKS sh t_devsnap (devsnap_val D h) p = @data_at W_cookie_mac sh t_devsnap (devsnap_val D h) p.
Proof.
  apply equal_f. apply (@data_at_change_composite CKS W_cookie_mac _ sh t_devsnap); [apply JMeq_refl | prove_cs_preserve_type].
Qed.

(* the device D with B's checker's secret / birthdate replaced *)
Definition hck5_p7b_setcc (D: device) (s: list byte) (b: int64) : device :=
  mkDev (d_dev D) (d_id D) (mkChk s (cc_ekey (d_cc D)) (cc_mkey (d_cc D)) b (cc_dev (d_cc D))) (d_ptab D) (d_itab D).

Lemma hck5_p7b_sec sh D h p s :
  @data_at W_cookie_mac sh t_devsnap (devsnap_val D h) p |--
  @data_at_ W_cookie_mac sh (tarray tuchar 32) (@field_address W_cookie_mac t_devsnap (DOT HK._secret) p) *
  (@data_at W_cookie_mac sh (tarray tuchar 32) (bytes s) (@field_address W_cookie_mac t_devsnap (DOT HK._secret) p) -*
   @data_at W_cookie_mac sh t_devsnap (devsnap_val (hck5_p7b_setcc D s (cc_birth (d_cc D))) h) p).
Proof.
  assert_PROP (@field_compatible W_cookie_mac t_devsnap [] p) by entailer!.
  unfold data_at at 1.
  eapply derives_trans; [eapply (gfield_ramif sh t_devsnap [] (StructField HK._secret)) |].
  - apply JMeq_refl.
  - apply field_compatible_cons; split; auto. cbv; tauto.
  - rewrite field_at_data_at. apply sepcon_derives; [apply data_at_data_at_ |].
    apply (allp_left _ (bytes s)). apply wand_derives; [rewrite field_at_data_at; apply derives_refl |].
    unfold data_at. apply derives_refl.
Qed.

Lemma hck5_p7b_birth sh D h p b :
  @data_at W_cookie_mac sh t_devsnap (devsnap_val D h) p |--
  @field_at_ W_cookie_mac sh t_devsnap (DOT HK._secret_birthdate) p *
  (@field_at W_cookie_mac sh t_devsnap (DOT HK._secret_birthdate) (Vlong b) p -*
   @data_at W_cookie_mac sh t_devsnap (devsnap_val (hck5_p7b_setcc D (cc_secret (d_cc D)) b) h) p).
Proof.
  assert_PROP (@field_compatible W_cookie_mac t_devsnap [] p) by entailer!.
  unfold data_at at 1.
  eapply derives_trans; [eapply (gfield_ramif sh t_devsnap [] (StructField HK._secret_birthdate)) |].
  - apply JMeq_refl.
  - apply field_compatible_cons; split; auto. cbv; tauto.
  - apply sepcon_derives; [apply field_at_field_at_ |].
    apply (allp_left _ (Vlong b)). apply wand_derives; [apply derives_refl |].
    unfold data_at. apply derives_refl.
Qed.

Lemma hck5_p7b_dbclose x25519 R L CC CC' :
  CC' = mkChk (cc_secret CC') (cc_ekey CC) (cc_mkey CC) (cc_birth CC') (cc_dev CC) ->
  hck5_p7b_setcc (hck5_p7b_setcc (hck5_DBc x25519 R L CC) (cc_secret CC') (cc_birth CC)) (cc_secret CC')
    (cc_birth CC') = hck5_DBc x25519 R L CC'.
Proof.
  intros E. destruct CC' as [s1 e1 m1 b1 d1]. cbn in E. injection E; intros; subst. reflexivity.
Qed.

(* byte arrays are the same predicate in every compspecs (copy of hck5_P6's) *)
Section Bytes.
Context {cs1 cs2: compspecs}.

Lemma hck5_p7b_align_tuchar: forall (ce: composite_env) n z,
  align_compatible_rec ce (tarray tuchar n) z.
Proof.
  intros. apply align_compatible_rec_Tarray. intros.
  eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l].
Qed.

Lemma hck5_p7b_fc_tuchar: forall n p,
  @field_compatible cs1 (tarray tuchar n) nil p <-> @field_compatible cs2 (tarray tuchar n) nil p.
Proof.
  intros. unfold field_compatible, size_compatible, align_compatible.
  destruct p; simpl; try tauto.
  pose proof (hck5_p7b_align_tuchar (@cenv_cs cs1) n (Ptrofs.unsigned i)).
  pose proof (hck5_p7b_align_tuchar (@cenv_cs cs2) n (Ptrofs.unsigned i)).
  tauto.
Qed.

Lemma hck5_p7b_tuchar_cs: forall sh n (v: list val) p,
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  intros. unfold data_at, field_at.
  f_equal. f_equal. apply prop_ext. apply hck5_p7b_fc_tuchar.
Qed.

Lemma hck5_p7b_tuchar__cs: forall sh n p,
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof.
  intros. unfold data_at_, field_at_. apply hck5_p7b_tuchar_cs.
Qed.
End Bytes.

(* validate changes only the checker's secret and birthdate *)
Lemma hck5_p7b_vr CC sk msg chk now rl r :
  snd (validate_model CC sk msg chk now rl r) =
  mkChk (cc_secret (snd (validate_model CC sk msg chk now rl r))) (cc_ekey CC) (cc_mkey CC)
        (cc_birth (snd (validate_model CC sk msg chk now rl r))) (cc_dev CC).
Proof.
  destruct CC as [s0 e0 m0 b0 d0]. unfold validate_model, checker_rotate. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

Lemma hck5_p7b_vr_sec CC sk msg chk now rl r :
  cc_secret (snd (validate_model CC sk msg chk now rl r)) = cc_secret CC \/
  cc_secret (snd (validate_model CC sk msg chk now rl r)) = r.
Proof.
  destruct CC as [s0 e0 m0 b0 d0]. unfold validate_model, checker_rotate. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn [snd cc_secret]; auto.
Qed.

Lemma hck5_p7b_skb_refl sk : skb_eqb sk sk = true.
Proof.
  unfold skb_eqb. rewrite ?hck5_p7b_veqb, ?hck5_p7b_bytes, ?Int.eq_true, ?Z.eqb_refl. reflexivity.
Qed.

Lemma hck5_p7b_voD sh wg D : device_rep sh wg D = vobjs W_cookie_mac [VDev sh wg D].
Proof. apply (hck5_p7b_vo1 (VDev sh wg D)). Qed.

Lemma hck5_p7b_voI sh tab T : itable sh tab T = vobjs W_cookie_mac [VItab sh tab T].
Proof. apply (hck5_p7b_vo1 (VItab sh tab T)). Qed.

Lemma hck5_p7b_voP sh p P : peer_rep sh p P = vobjs W_cookie_mac [VPeer sh p P].
Proof. apply (hck5_p7b_vo1 (VPeer sh p P)). Qed.

Lemma hck5_p7b_voB sh l p : hbytes sh l p = vobjs W_cookie_mac [VBytes sh l p].
Proof.
  rewrite <- (hck5_p7b_vo1 (VBytes sh l p)). unfold vobj_rep, hbytes, bytes_at. apply hck5_p7b_tuchar_cs.
Qed.

(* common4 v4.1: VKents lends no address; lend A's index table (the kents' entries) with the device *)
Lemma hck5_p7b_voDI sh wg D sht tab T :
  (device_rep sh wg D * itable sht tab T)%logic = vobjs W_cookie_mac [VDev sh wg D; VItab sht tab T].
Proof. apply (hck5_p7b_vo2 (VDev sh wg D) (VItab sht tab T)). Qed.

Lemma hck5_p7b_kincl L A D :
  hck5_aok L A ->
  incl (map ke_addr (a_KE A)) (vobjs_addrs [VDev Tsh (l_wa L) D; VItab Tsh (l_ita L) (a_T A)]).
Proof.
  intros (_ & _ & _ & _ & _ & _ & Hsa & _) x Hx. unfold vobjs_addrs; simpl. rewrite app_nil_r.
  right; right; right. right. rewrite Hsa. apply in_or_app. left. exact Hx.
Qed.

Lemma hck5_p7b_voDK sh wg D l KE :
  (device_rep sh wg D * kents_rep W_cookie_mac l KE)%logic = vobjs W_cookie_mac [VDev sh wg D; VKents l KE].
Proof. apply (hck5_p7b_vo2 (VDev sh wg D) (VKents l KE)). Qed.

Lemma hck5_p7b_voIP sh tab T shp p P :
  (itable sh tab T * peer_rep shp p P)%logic = vobjs W_cookie_mac [VItab sh tab T; VPeer shp p P].
Proof. apply (hck5_p7b_vo2 (VItab sh tab T) (VPeer shp p P)). Qed.

(* a snapshot at the world's compspecs against the same at CKS *)
Ltac hck5_p7b_csrefl :=
  first [apply derives_refl
        | apply derives_refl'; apply equal_f; apply (@data_at_change_composite CKS W_cookie_mac _);
            [apply JMeq_refl | prove_cs_preserve_type]
        | apply derives_refl'; symmetry; apply equal_f; apply (@data_at_change_composite CKS W_cookie_mac _);
            [apply JMeq_refl | prove_cs_preserve_type]].

Section P7b.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* the state between the snapshot writes (87, 88) and the frame CHECK (89): S7 with db = B with validate's checker *)
Definition hck5_p7b_s89 := ltac:(let x := eval cbv beta iota delta [hck5_l hck5_seql firstn skipn hck5_stmts] in
  (hck5_seql (hck5_l 89 1)) in exact x).

Definition hck5_p7b_T (gv: globals) (L: hck5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hck5_run, EX S: shim, EX A: hck5_aval, EX m: val, EX c: val, EX Q: hck5_pkt, EX cmode: bool,
  EX C: cookie, EX ck: list byte, EX MSG1: list byte, EX C1: cookie,
  EX MSG2: list byte, EX corrupted: bool, EX chk: bool, EX rl: bool, EX r: list byte, EX VR: Z * checker,
  PROPx [hck5_run_ok x25519 R; hck5_aok L A; hck5_pkt_ok Q;
         hck5_is ck (cookie_of (r_secret R) (hck5_skb Q m)); hck5_ck_ok R Q cmode C ck;
         hck5_is (MSG1, C1) (add_mac_model C (q_msg Q) (q_now Q)); Zlength MSG1 = q_n Q;
         hck5_after_val x25519 R L Q m cmode MSG1 MSG2 corrupted chk rl r VR S]
  (LOCALx ([temp HK._corrupted (Vint (if corrupted then Int.one else Int.zero));
            temp HK._honest_peer (Vint (if r_honest R then Int.one else Int.zero));
            temp HK._kes (a_kes A); temp HK._head0 (a_head0 A); temp HK._refs0 (Vint (p_refs (a_P A)));
            temp HK._len (Vlong (Int64.repr (q_n Q))); temp HK._msg m; temp HK._copy c;
            temp HK._cookie_mode (Vint (if cmode then Int.one else Int.zero));
            temp HK._check_cookie (Vint (if chk then Int.one else Int.zero));
            temp HK._secret_birth (Vlong (cc_birth (snd VR)));
            temp HK._r (Vint (Int.repr (fst VR)))] ++ hck5_lvars gv L)
  (SEPx ([hck5_A x25519 R L A] ++ hck5_bside x25519 R L ++ hck5_bufs x25519 R L ++
         [checker_rep Tsh (cc_addr (l_wb L)) (snd VR);
          cookie_rep Tsh (cookie_addr (l_p L)) C1;
          skb_rep Tsh (l_skb L) (hck5_skb Q m);
          hck5_tok (q_n Q) m; hbytes Ews MSG2 m; hck5_tok (q_n Q) c; hbytes Ews MSG2 c;
          hbytes Tsh (cc_secret (snd VR)) (l_secret L)] ++
         hck5_scr2 L ++
         hck5_snaps x25519 R L A C1 (snd VR) S (Some (hck5_skb Q m)) ++
         hck5_globs gv S FR))).

(* statement 89: the frame CHECK *)
Lemma hck5_p7b_check_ok {Espec: OracleKind} gv L FR :
  hck5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hck5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hck5_p7b_T gv L FR) hck5_p7b_s89
    (overridePost (hck5_S7b x25519 gv L FR) (hck5_R gv)).
Proof.
  intros HH. unfold hck5_p7b_T, hck5_Delta, hck5_R, hck5_p7b_s89. simplify_func_tycontext. abbreviate_semax.
  Intros R S A m c Q cmode C ck MSG1 C1. Intros MSG2 corrupted chk rl r VR.
  unfold hck5_A, hck5_bside, hck5_bufs, hck5_scr2, hck5_snaps, hck5_globs, hck5_lvars. cbn [app].
  pose proof H6 as (Hc & HL2 & Hr & HVR & Hboot & Hrl & Hlog).
  assert (HLs: Zlength (cc_secret (snd VR)) = 32).
  { unfold hck5_is in HVR. rewrite HVR. destruct (hck5_p7b_vr_sec (hck5_CC2 x25519 R L (q_now Q) cmode)
      (hck5_skb Q m) MSG2 chk (q_now Q) rl r) as [-> | ->];
    [unfold hck5_CC2, hck5_CC1; destruct H as (_ & _ & _ & _ & Hs & _); destruct (andb _ _); exact Hs | assumption]. }
  assert (HCv: snd VR = mkChk (cc_secret (snd VR)) (cc_ekey (hck5_CC2 x25519 R L (q_now Q) cmode))
    (cc_mkey (hck5_CC2 x25519 R L (q_now Q) cmode)) (cc_birth (snd VR)) (cc_dev (hck5_CC2 x25519 R L (q_now Q) cmode))).
  { unfold hck5_is in HVR. rewrite HVR. apply hck5_p7b_vr. }
  pose proof H0 as Hok.
  assert_PROP (itable_wf (a_T A)) as Hwf by (sep_apply (hck5_p7b_itable_wf Tsh (l_ita L) (a_T A)); entailer!).
  sep_apply (hck5_p7b_fold_d Tsh (l_p L) (a_P A) C1).
  sep_apply (hck5_p7b_dev_in x25519 R L (snd VR)).
  assert (Hdev: cc_dev (snd VR) = l_wb L).
  { rewrite HCv. cbn [cc_dev]. apply hck5_p7b_cc2_dev. }
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end; [entailer! | | ].
  { (* dev_same(&db, &wb) *)
    rewrite (hck5_p7b_voI Tsh (l_itb L) (mkT [] [])).
    change (ptable Tsh (l_ptb L) nullval) with (ptable Tsh (d_ptab (hck5_DBc x25519 R L (snd VR))) nullval).
    forward_call (Tsh, l_db L, hck5_DBc x25519 R L (snd VR), nullval, Tsh, l_wb L,
                  hck5_DBc x25519 R L (snd VR), Tsh, nullval, [VItab Tsh (l_itb L) (mkT [] [])]).
    { split; [repeat constructor; apply readable_share_top |].
      apply hck5_p7b_db_pre; [exact Hdev | unfold vobjs_addrs; simpl; left; reflexivity]. }
    rewrite hck5_p7b_dev_refl.
    change (ptable Tsh (d_ptab (hck5_DBc x25519 R L (snd VR))) nullval) with (ptable Tsh (l_ptb L) nullval).
    rewrite <- (hck5_p7b_voI Tsh (l_itb L) (mkT [] [])).
    (* dev_same(&da, &wa) *)
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HK._t'80 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    { sep_apply (hck5_p7b_voIP Tsh (l_ita L) (a_T A) Tsh (l_p L) (p_set_cookie (a_P A) C1)).
      change (ptable Tsh (l_pta L) (l_p L)) with (ptable Tsh (d_ptab (hck5_DA x25519 R L)) (l_p L)).
      forward_call (Tsh, l_da L, hck5_DA x25519 R L, l_p L, Tsh, l_wa L, hck5_DA x25519 R L, Tsh, l_p L,
                    [VItab Tsh (l_ita L) (a_T A); VPeer Tsh (l_p L) (p_set_cookie (a_P A) C1)]).
      { split; [repeat constructor; apply readable_share_top |].
        apply hck5_p7b_da_pre; unfold vobjs_addrs; simpl; rewrite ?app_nil_r.
        - left. reflexivity.
        - right. apply in_or_app. right. left. reflexivity. }
      rewrite hck5_p7b_dev_refl.
      change (ptable Tsh (d_ptab (hck5_DA x25519 R L)) (l_p L)) with (ptable Tsh (l_pta L) (l_p L)).
      rewrite <- (hck5_p7b_voIP Tsh (l_ita L) (a_T A) Tsh (l_p L) (p_set_cookie (a_P A) C1)). flatten_sepcon_in_SEP.
      forward. entailer!; hck5_p7b_csrefl. }
    { exfalso. apply Int.one_not_zero. auto. }
    (* skb_same(&sks, &skb) *)
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HK._t'82 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    { rewrite (hck5_p7b_voB Ews MSG2 m).
      forward_call (Tsh, l_sks L, hck5_skb Q m, Tsh, l_skb L, hck5_skb Q m, [VBytes Ews MSG2 m]).
      { split.
        - constructor; [| constructor]. split; [apply writable_readable; apply writable_Ews | rewrite HL2; destruct H1; lia].
        - (* common4 v4.1: skb_ok of the snapshot *)
          repeat match goal with |- _ /\ _ => split end.
          all: match goal with
               | |- skb_ok _ => unfold skb_ok, hck5_skb; simpl;
                                destruct H1 as (? & ? & ? & ? & ? & ? & ?); repeat split; auto; lia
               | |- Forall _ _ => unfold vobjs_addrs; simpl; repeat constructor; right; left; reflexivity
               | _ => auto
               end. }
      rewrite hck5_p7b_skb_refl.
      rewrite <- (hck5_p7b_voB Ews MSG2 m).
      forward. entailer!; hck5_p7b_csrefl. }
    { exfalso. apply Int.one_not_zero. auto. }
    (* hs_same(&hs0, &p.handshake) *)
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HK._t'84 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    { rewrite (hck5_p7b_voD Tsh (l_wa L) (hck5_DA x25519 R L)).
      change (peer_rep Tsh (l_p L) (p_set_cookie (a_P A) C1)) with (hs_mem true Tsh (l_p L) (p_set_cookie (a_P A) C1)).
      forward_call (Tsh, l_hs0 L, hs_snap_cur (a_T A) (l_p L) (a_P A), Tsh, l_p L, p_set_cookie (a_P A) C1, true,
                    Tsh, l_ita L, a_T A, [VDev Tsh (l_wa L) (hck5_DA x25519 R L)]).
      { split; [repeat constructor; apply readable_share_top |].
        split; [apply (hck5_p7b_hs_in L A Hok) |].
        apply hck5_p7b_hs_pre; auto. cbn. right. left. reflexivity. }
      rewrite hck5_p7b_snap_cur.
      change (hs_mem true Tsh (l_p L) (p_set_cookie (a_P A) C1)) with (peer_rep Tsh (l_p L) (p_set_cookie (a_P A) C1)).
      rewrite <- (hck5_p7b_voD Tsh (l_wa L) (hck5_DA x25519 R L)).
      forward. entailer!; hck5_p7b_csrefl. }
    { exfalso. apply Int.one_not_zero. auto. }
    (* pr_same(&ps0, &p) *)
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HK._t'86 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    { sep_apply (hck5_p7b_voDI Tsh (l_wa L) (hck5_DA x25519 R L) Tsh (l_ita L) (a_T A)).
      forward_call (Tsh, l_ps0 L, p_set_cookie (a_P A) C1, Tsh, l_p L, p_set_cookie (a_P A) C1,
                    [VDev Tsh (l_wa L) (hck5_DA x25519 R L); VItab Tsh (l_ita L) (a_T A)]).
      { split; [repeat constructor; apply readable_share_top |].
        apply hck5_p7b_pr_pre; auto.
        - unfold vobjs_addrs; simpl; auto.
        - exact (hck5_p7b_kincl L A (hck5_DA x25519 R L) Hok). }
      rewrite hck5_p7b_pr_refl.
      rewrite <- (hck5_p7b_voDI Tsh (l_wa L) (hck5_DA x25519 R L) Tsh (l_ita L) (a_T A)). flatten_sepcon_in_SEP.
      forward. entailer!; hck5_p7b_csrefl. }
    { exfalso. apply Int.one_not_zero. auto. }
    (* p.refcount.refcount == refs0 *)
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HK._t'88 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    { sep_apply (hck5_p7b_unfold_d Tsh (l_p L) (a_P A) C1).
      rewrite (hck5_p7b_open Tsh (l_p L) (a_P A)). Intros.
      forward. forward.
      sep_apply (hck5_p7b_close Tsh (l_p L) (a_P A)).
      sep_apply (hck5_p7b_fold_d Tsh (l_p L) (a_P A) C1).
      entailer!; first [rewrite Int.eq_true; reflexivity | hck5_p7b_csrefl]. }
    { exfalso. apply Int.one_not_zero. auto. }
    (* shim_same(&ss) *)
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HK._t'89 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    { forward_call (gv, Tsh, l_ss L, S, hck5_w0, S, hck5_w0).
      rewrite hck5_p7b_shim_refl. forward. entailer!; hck5_p7b_csrefl. }
    { exfalso. apply Int.one_not_zero. auto. }
    (* ita.head == head0 *)
    pose proof Hok as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsnap & Hhead).
    pose proof (hck5_p7b_hd_pn L A Hok Hwf) as Hhd.
    rewrite Hhead.
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HK._t'91 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    { rewrite (hck5_p7b_itable_open Tsh (l_ita L) (a_T A)). Intros.
      forward.
      sep_apply (hck5_p7b_itable_fold Tsh (l_ita L) (a_T A) Hwf).
      forward.
      { entailer!. apply denote_tc_test_eq_split;
          (apply (derives_trans _ (itable Tsh (l_ita L) (a_T A) * TT)%logic); [cancel | apply sepcon_valid_pointer1; apply hck5_p7b_hd_valid]). }
      entailer!.
      revert Hhd. generalize (hd nullval (t_L (a_T A))). intros v Hv. destruct v; try contradiction.
      - cbn in Hv. subst. reflexivity.
      - unfold eval_binop, sem_binary_operation', sem_cmp; cbn. unfold sem_cmp_pp, Val.cmplu_bool; cbn.
        rewrite if_true by reflexivity. rewrite Ptrofs.eq_true. reflexivity. }
    { exfalso. apply Int.one_not_zero. auto. }
    (* kents_same(kes) *)
    match goal with |- semax _ (PROPx ?Pp (LOCALx ?Qq (SEPx ?Rr))) _ _ =>
      forward_if (PROPx Pp (LOCALx (temp HK._t'92 (Vint Int.one) :: Qq) (SEPx Rr))) end.
    { rewrite (hck5_p7b_voP Tsh (l_p L) (p_set_cookie (a_P A) C1)).
      forward_call (a_kes A, a_KE A, Tsh, l_ita L, a_T A, [VPeer Tsh (l_p L) (p_set_cookie (a_P A) C1)]).
      { split; [repeat constructor; apply readable_share_top |].
        apply (hck5_p7b_kents_pre L A); auto. unfold vobjs_addrs; simpl; auto. }
      rewrite (hck5_p7b_kents_refl _ _ Hsnap).
      rewrite <- (hck5_p7b_voP Tsh (l_p L) (p_set_cookie (a_P A) C1)).
      forward. entailer!; hck5_p7b_csrefl. }
    { exfalso. apply Int.one_not_zero. auto. }
    forward_if True.
    { exfalso. apply Int.one_not_zero. auto. }
    { forward. entailer!. }
    forward. rewrite <- Hhead. entailer!; hck5_p7b_csrefl. }
  (* after the CHECK: the snapshots and the secret are dropped *)
  drop_LOCAL 10%nat. drop_LOCAL 4%nat. drop_LOCAL 3%nat.
  sep_apply (hck5_p7b_unfold_d Tsh (l_p L) (a_P A) C1).
  sep_apply (hck5_p7b_dev_out x25519 R L (snd VR)).
  unfold hck5_S7b. Exists R S A m c Q cmode C ck. Exists MSG1 C1 MSG2 corrupted chk. Exists rl r VR.
  unfold hck5_A, hck5_bside, hck5_bufs, hck5_scr2, hck5_snaps0, hck5_globs, hck5_lvars. cbn [app].
  assert (Hsec: hbytes Tsh (cc_secret (snd VR)) (l_secret L) |-- hout Tsh 32 (l_secret L)).
  { unfold hbytes, hout. rewrite HLs. apply data_at_data_at_. }
  sep_apply Hsec.
  sep_apply (@data_at_data_at_ HCS Tsh t_hsnap (hsnap_val (hs_snap_cur (a_T A) (l_p L) (a_P A))) (l_hs0 L)).
  sep_apply (@data_at_data_at_ CKS Tsh t_prsnap (prsnap_val (p_set_cookie (a_P A) C1)) (l_ps0 L)).
  sep_apply (@data_at_data_at_ CKS Tsh t_devsnap (devsnap_val (hck5_DA x25519 R L) (l_p L)) (l_da L)).
  sep_apply (@data_at_data_at_ CKS Tsh t_devsnap (devsnap_val (hck5_DBc x25519 R L (snd VR)) nullval) (l_db L)).
  sep_apply (@data_at_data_at_ CKS Tsh t_skbsnap (skbsnap_val (hck5_skb Q m)) (l_sks L)).
  sep_apply (@data_at_data_at_ CKS Tsh t_shimsnap (shimsnap_val S hck5_w0) (l_ss L)).
  apply andp_right; [apply prop_right; cbn [fold_right]; repeat (split; [assumption |]); exact I |].
  apply andp_left2. unfold PROPx at 1. apply andp_left2. unfold LOCALx.
  apply andp_derives; [apply derives_refl |].
  intro rho. unfold SEPx. cbv beta. cbn [fold_right_sepcon]. cancel.
Qed.

Lemma hck5_P7b_ok {Espec: OracleKind} gv L FR :
  hck5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hck5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hck5_S7 x25519 gv L FR) hck5_P7b
    (overridePost (hck5_S7b x25519 gv L FR) (hck5_R gv)).
Proof.
  intros HH. unfold hck5_S7, hck5_Delta, hck5_R, hck5_P7b. simplify_func_tycontext. abbreviate_semax.
  Intros R S A m c Q cmode C ck MSG1 C1. Intros MSG2 corrupted chk rl r VR.
  unfold hck5_A, hck5_bside, hck5_bufs, hck5_scr2, hck5_snaps, hck5_globs, hck5_lvars. cbn [app].
  pose proof H6 as (Hc & HL2 & Hr & HVR & Hboot & Hrl & Hlog).
  assert (HL0: Zlength (cc_secret (hck5_CC2 x25519 R L (q_now Q) cmode)) = 32).
  { unfold hck5_CC2, hck5_CC1. destruct H as (_ & _ & _ & _ & Hs & _). destruct (andb _ _); exact Hs. }
  assert (HLs: Zlength (cc_secret (snd VR)) = 32).
  { unfold hck5_is in HVR. rewrite HVR. destruct (hck5_p7b_vr_sec (hck5_CC2 x25519 R L (q_now Q) cmode)
      (hck5_skb Q m) MSG2 chk (q_now Q) rl r) as [-> | ->]; assumption. }
  rewrite (hck5_p7b_dbW Tsh (hck5_DBc x25519 R L (hck5_CC2 x25519 R L (q_now Q) cmode)) nullval (l_db L)).
  assert_PROP (@field_compatible W_cookie_mac t_devsnap (DOT HK._secret) (l_db L)) as Hfc.
  { entailer!. }
  sep_apply (hck5_p7b_sec Tsh (hck5_DBc x25519 R L (hck5_CC2 x25519 R L (q_now Q) cmode)) nullval (l_db L)
    (cc_secret (snd VR))).
  replace (@data_at_ W_cookie_mac Tsh (tarray tuchar 32) (field_address t_devsnap (DOT HK._secret) (l_db L)))
    with (hout Tsh (Zlength (cc_secret (snd VR))) (field_address t_devsnap (DOT HK._secret) (l_db L)))
    by (rewrite HLs; unfold hout; apply hck5_p7b_tuchar__cs).
  flatten_sepcon_in_SEP.
  forward_call (Tsh, field_address t_devsnap (DOT HK._secret) (l_db L), Tsh, l_secret L, cc_secret (snd VR)).
  { rewrite HLs. entailer!. unfold field_address. rewrite if_true by exact Hfc. reflexivity. }
  replace (hbytes Tsh (cc_secret (snd VR)) (field_address t_devsnap (DOT HK._secret) (l_db L))) with
    (@data_at W_cookie_mac Tsh (tarray tuchar 32) (bytes (cc_secret (snd VR)))
       (field_address t_devsnap (DOT HK._secret) (l_db L)))
    by (unfold hbytes; rewrite HLs; symmetry; apply hck5_p7b_tuchar_cs).
  sep_apply (modus_ponens_wand (@data_at W_cookie_mac Tsh (tarray tuchar 32) (bytes (cc_secret (snd VR)))
    (field_address t_devsnap (DOT HK._secret) (l_db L)))).
  sep_apply (hck5_p7b_birth Tsh (hck5_p7b_setcc (hck5_DBc x25519 R L (hck5_CC2 x25519 R L (q_now Q) cmode))
    (cc_secret (snd VR)) (cc_birth (hck5_CC2 x25519 R L (q_now Q) cmode))) nullval (l_db L) (cc_birth (snd VR))).
  flatten_sepcon_in_SEP.
  forward.
  sep_apply (modus_ponens_wand (@field_at W_cookie_mac Tsh t_devsnap (DOT HK._secret_birthdate)
    (Vlong (cc_birth (snd VR))) (l_db L))).
  assert (HCv: snd VR = mkChk (cc_secret (snd VR)) (cc_ekey (hck5_CC2 x25519 R L (q_now Q) cmode))
    (cc_mkey (hck5_CC2 x25519 R L (q_now Q) cmode)) (cc_birth (snd VR)) (cc_dev (hck5_CC2 x25519 R L (q_now Q) cmode))).
  { unfold hck5_is in HVR. rewrite HVR. apply hck5_p7b_vr. }
  change (cc_secret (d_cc (hck5_p7b_setcc (hck5_DBc x25519 R L (hck5_CC2 x25519 R L (q_now Q) cmode))
    (cc_secret (snd VR)) (cc_birth (hck5_CC2 x25519 R L (q_now Q) cmode))))) with (cc_secret (snd VR)).
  rewrite (hck5_p7b_dbclose x25519 R L _ _ HCv).
  rewrite <- hck5_p7b_dbW.
  eapply semax_pre; [| apply (hck5_p7b_check_ok gv L FR HH)].
  unfold hck5_p7b_T. Exists R S A m c Q cmode C. Exists ck MSG1 C1 MSG2 corrupted chk rl r. Exists VR.
  unfold hck5_A, hck5_bside, hck5_bufs, hck5_scr2, hck5_snaps, hck5_globs, hck5_lvars. cbn [app].
  entailer!; hck5_p7b_csrefl.
Qed.

End P7b.
