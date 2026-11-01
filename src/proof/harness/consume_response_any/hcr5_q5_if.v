(* law consume_response_any, phase Q5, segment if: statement 17: if (target == NULL) CHECK(ret == NULL && hnodes_same_except(peers, NULL)) else ACC; the else branch ACC is the hypothesis HACC (proved by the segments A1..A5); the agreement: hcr5_agree (hcr5_model.v, Qed).
   States and statements: hcr5_q5_defs.v; pure facts: hcr5_q5_pure.v (its statement is a hypothesis here,
   proved separately); (section Q5);
   src/proof/harness/consume_response_any/hcr3_q5_if*.v. *)
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
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_cut.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_model.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_spec.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_conv.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q5_pure.
Require WgNoise.harness.x_consume_response_any.code.

#[local] Existing Instance W_consume_response_any.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* Helpers                                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma hcr5_q5_if_node_ptr NS : forall l a, In a (map hn_addr NS) ->
  hnodes_rep4 W l NS |-- !! isptr a.
Proof.
  induction NS as [| N NS IH]; intros l a Hin; [contradiction |].
  simpl in Hin. simpl hnodes_rep4. Intros nx. destruct Hin as [<- | Hin].
  - subst l. entailer!.
    match goal with Hf: field_compatible _ _ _ |- _ => destruct Hf as [Hp _] end. exact Hp.
  - sep_apply (IH nx a Hin). entailer!.
Qed.

Lemma hcr5_q5_if_node_valid NS : forall l a, In a (map hn_addr NS) ->
  hnodes_rep4 W l NS |-- valid_pointer a.
Proof.
  induction NS as [| N NS IH]; intros l a Hin; [contradiction |].
  simpl in Hin. simpl hnodes_rep4. Intros nx. destruct Hin as [<- | Hin].
  - subst l. entailer!.
  - sep_apply (IH nx a Hin). entailer!.
Qed.

Lemma hcr5_q5_if_pn l NS : hnodes_rep4 W l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [| N NS]; simpl.
  - Intros. subst. entailer!.
  - Intros nx. subst. entailer!.
    destruct H0 as [Hp _]. destruct (hn_addr N); simpl in *; try contradiction; auto.
Qed.

Lemma hcr5_q5_if_rlen M : rm_ok M -> Zlength (resp_bytes M) = 92%Z.
Proof.
  intros (H1 & H2 & H3 & H4). unfold resp_bytes. rewrite !Zlength_app, H1, H2, H3, H4.
  unfold le32. rewrite !Zlength_map. reflexivity.
Qed.

Lemma hcr5_q5_if_hout M p : rm_ok M -> hbytes Tsh (resp_bytes M) p |-- hout Tsh 92 p.
Proof. intros HM. unfold hbytes, hout. rewrite (hcr5_q5_if_rlen M HM). apply data_at_data_at_. Qed.

Lemma hcr5_q5_if_vo x25519 R L T KE :
  vobjs W (hcr5_q5_VO x25519 R L T KE) =
  device_rep Tsh (l_wa L) (hcr5_DAL x25519 R L) * kents_rep W (hcr5_khead KE) (map (kent_snapped T) KE).
Proof. unfold vobjs, hcr5_q5_VO. cbn [iter_sepcon vobj_rep]. rewrite sepcon_emp. reflexivity. Qed.

(* some peer (the pure fact (5) quantifies over the updated one) *)
Definition hcr5_q5_if_p0 : peer :=
  mkPeer nullval false nullval nullval nullval
         (mkHS HS_ZEROED Int64.zero nullval (zeros 32) (zeros 32) (zeros 32) (zeros 32) (zeros 32) (zeros 32)
               (zeros 32) (zeros 12) Int.zero)
         Int64.zero cookie_zero Int.one Int64.zero nullval.

Lemma hcr5_q5_if_refs L KA NS PS head nb : hcr5_list_ok L KA NS PS head nb -> peers_refs_ok PS.
Proof.
  intros (Hpok & _). unfold peers_refs_ok. eapply Forall_impl; [| exact Hpok].
  intros [[p sh] P] Hk. simpl in Hk. tauto.
Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcr5_q5_if_ok {Espec: OracleKind} gv L FR :
  hcr5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> hcr5_q5_pure_stmt x25519 aead_dec ->
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_q5_QA0 x25519 aead_dec gv L FR) (hcr5_seql hcr5_q5_acc) (overridePost (hcr5_q5_QE x25519 gv L FR) (hcr5_R gv)) ->
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_SQ4 x25519 aead_dec gv L FR) hcr5_q5_s17 (overridePost (hcr5_q5_QE x25519 gv L FR) (hcr5_R gv)).
Proof.
  intros Hy Hpure HACC.
  revert HACC. generalize (hcr5_R gv) as Rr. intros [r1 r2 r3 r4] HACC.
  unfold hcr5_SQ4. Intros R S NS PS head nb T KE m M.
  assert_PROP (itable_wf T) as HwfT.
  { unfold hcr5_world. simpl app. unfold itable at 1. Intros. apply prop_right. auto. }
  assert (Hag: hcr5_res x25519 aead_dec R L T PS M =
    match hcr5_tg x25519 aead_dec R T PS M with
    | Some (a, P, ck, h) => Some (a, hcr5_new P M ck h) | None => None end).
  { unfold hcr5_res, cre_res, hcr5_DAL, hcr5_tg. eapply hcr5_agree; [| exact H1].
    eapply hcr5_q5_if_refs; exact H0. }
  rewrite Hag.
  destruct (hcr5_tg x25519 aead_dec R T PS M) as [[[[a P] ck] h]|] eqn:Htg;
    cbv beta iota delta [hcr5_tnode peers_after peer_result hcr5_st_rep];
    (let s := eval hnf in hcr5_q5_s17 in match s with Sifthenelse ?b ?c1 _ =>
       change hcr5_q5_s17 with (Sifthenelse b c1 (hcr5_seql hcr5_q5_acc)) end).
  - destruct Hpure as (_ & _ & _ & Hp4 & _).
    destruct (Hp4 R L NS PS head nb KE T M a P ck h H0 H1 HwfT Htg)
      as (NS1 & N & NS2 & PS1 & PS2 & E & _ & _ & _ & HNS & HNa & _).
    clear Hp4 Hag.
    assert (HinN: In (hcr5_nfind NS a) (map hn_addr (hnodes_snapped4 T NS PS))).
    { rewrite HNS, <- HNa, map_app. apply in_or_app. right. left. reflexivity. }
    unfold hcr5_Delta. simplify_func_tycontext. abbreviate_semax.
    unfold hcr5_lvars, hcr5_world, hcr5_globs, hcr5_snaps; cbn [app].
    assert_PROP (isptr (hcr5_nfind NS a)) as Hpt.
    { sep_apply (hcr5_q5_if_node_ptr _ (hcr5_head NS) _ HinN). entailer!. }
    forward_if.
    { apply denote_tc_test_eq_split; [| apply valid_pointer_null].
      sep_apply (hcr5_q5_if_node_valid _ (hcr5_head NS) _ HinN). entailer!. }
    { exfalso. match goal with Hn: hcr5_nfind NS a = nullval |- _ => rewrite Hn in Hpt; exact Hpt end. }
    eapply semax_pre; [| exact HACC].
    unfold hcr5_q5_QA0. Exists R S NS PS head nb T KE m M. Exists a P ck h.
    unfold hcr5_lvars, hcr5_world, hcr5_globs, hcr5_snaps, hcr5_q5_scr; cbn [app].
    entailer!.
  - unfold hcr5_Delta. simplify_func_tycontext. abbreviate_semax.
    unfold hcr5_lvars, hcr5_world, hcr5_globs, hcr5_snaps; cbn [app].
    destruct Hpure as (Hp1 & Hp2 & _ & _ & Hp5 & _).
    destruct (Hp1 R L NS PS head nb KE T PS H0 H1 HwfT (or_introl eq_refl))
      as (Hq0 & Hq1 & Hq2 & Hq3 & Hq4 & Hq5 & Hq6 & Hq7 & Hq8 & Hq9).
    pose proof H0 as Hlo. destruct Hlo as (Hpok & Hwf & _ & Hnp & _).
    destruct (Hp5 L (hcr5_ka KE) NS PS T KE nullval hcr5_q5_if_p0 H1 Hnp Hwf Hpok) as (_ & Hk & Hkh & _ & _ & _ & _ & Hews).
    clear Hp1 Hp5 HACC Hag.
    forward_if.
    2: { exfalso. auto. }
    match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
    { apply ENTAIL_refl. }
    { forward_if (temp HR5._t'30 (Vint Int.one)).
      { assert_PROP (is_pointer_or_null (hcr5_head NS)) as Hhd.
        { sep_apply (hcr5_q5_if_pn (hcr5_head NS) (hnodes_snapped4 T NS PS)). entailer!. }
        forward.
        gather_SEP (device_rep _ _ _) (kents_rep _ _ _).
        rewrite <- (hcr5_q5_if_vo x25519 R L T KE).
        forward_call (hcr5_head NS, hnodes_snapped4 T NS PS, PS, hcr5_sns T PS, hcr5_rs PS, hcr5_prs PS,
                      nullval, Tsh, l_ita L, T, hcr5_q5_VO x25519 R L T KE).
        rewrite Hp2.
        forward.
        rewrite (hcr5_q5_if_vo x25519 R L T KE).
        entailer!. }
      { exfalso. auto. }
      forward_if.
      { exfalso. apply Int.one_not_zero. assumption. }
      forward. entailer!. }
    { forward. apply ENTAIL_refl. }
    unfold hcr5_q5_QE. Exists R S NS (hnodes_snapped4 T NS PS) PS head T (map (kent_snapped T) KE) m M.
    unfold hcr5_lvars, hcr5_world, hcr5_globs, hcr5_snaps0, hcr5_scr; cbn [app].
    rewrite Hkh.
    sep_apply (hcr5_q5_if_hout M (l_img L) H3). sep_apply (hcr5_q5_if_hout M (l_imga L) H3).
    sep_apply (@data_at_data_at_ CKS Tsh t_devsnap (devsnap_val (hcr5_DAL x25519 R L) head) (l_ds L)).
    sep_apply (@data_at_data_at_ CKS Tsh t_shimsnap (shimsnap_val S hcr5_w0) (l_ss L)).
    entailer!.
Qed.

End Seg.
