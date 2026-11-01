(* law consume_response_any, phase Q5, segment A5: CHECK(target->p->refcount == target->refs && pr_same(&target->rest, target->p)).
   States and statements: hcr5_q5_defs.v; pure facts: hcr5_q5_pure.v (its statement is a hypothesis here,
   proved separately); (section Q5);
   src/proof/harness/consume_response_any/hcr3_q5_A5*.v. *)
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
(* Helpers (copies of hcr5_q5_A1's / v1 hcr3_q5_A5's, renamed)             *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hcr5_q5_A5_CCE : change_composite_env Noise.CS W_consume_response_any.
Proof. make_cs_preserve Noise.CS W_consume_response_any. Defined.
#[local] Instance hcr5_q5_A5_CCEK : change_composite_env CKS W_consume_response_any.
Proof. make_cs_preserve CKS W_consume_response_any. Defined.

(* the node's value as ONE constant typed at W *)
Definition hcr5_q5_A5_nv (N: hnode4) (nx: val) : @reptype W_consume_response_any t_hnode4 :=
  (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))).

Lemma hcr5_q5_A5_node_W v l :
  @data_at CKS Ews t_hnode4 v l = @data_at W_consume_response_any Ews t_hnode4 v l.
Proof.
  rewrite (@data_at_change_composite CKS W_consume_response_any _ Ews t_hnode4 v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hcr5_q5_A5_node NS1 N NS2 : forall l,
  hnodes_rep4 W_consume_response_any l (NS1 ++ N :: NS2) |--
  EX nx: val,
    (@data_at W_consume_response_any Ews t_hnode4 (hcr5_q5_A5_nv N nx) (hn_addr N) *
     (@data_at W_consume_response_any Ews t_hnode4 (hcr5_q5_A5_nv N nx) (hn_addr N) -*
      hnodes_rep4 W_consume_response_any l (NS1 ++ N :: NS2)))%logic.
Proof.
  unfold hcr5_q5_A5_nv.
  induction NS1 as [| N1 NS1 IH]; intros l; simpl app; simpl hnodes_rep4.
  - Intros nx. subst l. Exists nx. rewrite <- hcr5_q5_A5_node_W. cancel.
    rewrite <- wand_sepcon_adjoint. Exists nx. entailer!.
  - Intros nx. sep_apply (IH nx). Intros nx'. Exists nx'. cancel.
    rewrite <- wand_sepcon_adjoint.
    match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
    Exists nx. entailer!.
Qed.

Lemma hcr5_q5_A5_node' NS NS1 N NS2 l : NS = NS1 ++ N :: NS2 ->
  hnodes_rep4 W_consume_response_any l NS |--
  EX nx: val,
    (@data_at W_consume_response_any Ews t_hnode4 (hcr5_q5_A5_nv N nx) (hn_addr N) *
     (@data_at W_consume_response_any Ews t_hnode4 (hcr5_q5_A5_nv N nx) (hn_addr N) -*
      hnodes_rep4 W_consume_response_any l NS))%logic.
Proof. intros ->. apply hcr5_q5_A5_node. Qed.

(* the node's field rest, as pr_same's snapshot (at CKS, offset 304 of struct hnode) *)
Lemma hcr5_q5_A5_rest N nx x P : hn_rest N = prsnap_val P ->
  @data_at W_consume_response_any Ews t_hnode4 (hcr5_q5_A5_nv N nx) x |--
  (@data_at CKS Ews t_prsnap (prsnap_val P) (offset_val 304 x) *
   (@data_at CKS Ews t_prsnap (prsnap_val P) (offset_val 304 x) -*
    @data_at W_consume_response_any Ews t_hnode4 (hcr5_q5_A5_nv N nx) x))%logic.
Proof.
  intros Hr. rewrite <- hcr5_q5_A5_node_W. unfold hcr5_q5_A5_nv.
  eapply derives_trans; [apply andp_right; [apply (@data_at_local_facts CKS) | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  eapply derives_trans; [apply (@gfield_ramif CKS Ews t_hnode4 [] (StructField HC._rest) _ (hn_rest N) x);
    [apply JMeq_refl | auto with field_compatible] |].
  apply sepcon_derives.
  - rewrite (@field_at_data_at CKS), (@field_address_offset CKS) by auto with field_compatible.
    rewrite Hr. apply derives_refl.
  - apply (allp_left _ (hn_rest N)).
    rewrite (@field_at_data_at CKS), (@field_address_offset CKS) by auto with field_compatible.
    rewrite Hr. apply derives_refl.
Qed.

(* the peers: the accepted one apart *)
Lemma hcr5_q5_A5_papp PS1 x PS2 : peers_rep (PS1 ++ x :: PS2) = (peer_item_rep x * peers_rep (PS1 ++ PS2))%logic.
Proof.
  unfold peers_rep. rewrite !iter_sepcon_app. simpl. apply pred_ext; cancel.
Qed.

(* the reference count of a peer, at the world's compspecs *)
Lemma hcr5_q5_A5_refs sh p r :
  peer_refs_rep sh p r = @field_at W_consume_response_any sh t_peer [StructField prot_repr3.I._refcount] (Vint r) p.
Proof.
  unfold peer_refs_rep.
  assert (Hc: cs_preserve_type Noise.CS W_consume_response_any (@coeq _ _ hcr5_q5_A5_CCE) t_peer = true)
    by (vm_compute; reflexivity).
  assert (E := @field_at_change_composite Noise.CS W_consume_response_any hcr5_q5_A5_CCE sh t_peer
                 [StructField prot_repr3.I._refcount] (Vint r) (Vint r) (JMeq_refl _) Hc).
  exact (f_equal (fun f => f p) E).
Qed.

(* peer_rep without its reference count *)
Definition hcr5_q5_A5_prest (sh: share) (p: val) (P: peer) : mpred :=
  (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] (p_device P) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p)%logic.

Lemma hcr5_q5_A5_split sh p P :
  peer_rep sh p P =
  (!! @field_compatible Noise.CS t_peer [] p &&
  (@field_at W_consume_response_any sh t_peer [StructField prot_repr3.I._refcount] (Vint (p_refs P)) p *
   hcr5_q5_A5_prest sh p P))%logic.
Proof.
  rewrite <- hcr5_q5_A5_refs. unfold peer_rep, hcr5_q5_A5_prest, peer_refs_rep.
  apply pred_ext; apply andp_derives; try apply derives_refl; cancel.
Qed.

Lemma hcr5_q5_A5_fold sh p Q : @field_compatible Noise.CS t_peer [] p ->
  (@field_at W_consume_response_any sh t_peer [StructField prot_repr3.I._refcount] (Vint (p_refs Q)) p *
   hcr5_q5_A5_prest sh p Q |-- peer_rep sh p Q)%logic.
Proof. intros Hfc. rewrite hcr5_q5_A5_split. apply andp_right; [apply prop_right; auto | cancel]. Qed.

Lemma hcr5_q5_A5_rlen M : rm_ok M -> Zlength (resp_bytes M) = 92.
Proof.
  intros (H1 & H2 & H3 & H4). unfold resp_bytes. rewrite !Zlength_app, H1, H2, H3, H4.
  unfold le32. rewrite !Zlength_map. reflexivity.
Qed.

Lemma hcr5_q5_A5_hout M p : rm_ok M -> hbytes Tsh (resp_bytes M) p |-- hout Tsh 92 p.
Proof. intros HM. unfold hbytes, hout. rewrite (hcr5_q5_A5_rlen M HM). apply data_at_data_at_. Qed.

#[local] Instance hcr5_q5_A5_cceK : change_composite_env CKS W_consume_response_any.
Proof. make_cs_preserve CKS W_consume_response_any. Defined.

(* the pr_snap field of the node at the world vs at CKS (pr_same4's compspecs) *)
Lemma hcr5_q5_A5_prsnap_cs sh P p :
  @data_at W_consume_response_any sh t_prsnap (prsnap_val P) p = @data_at CKS sh t_prsnap (prsnap_val P) p.
Proof.
  rewrite (@data_at_change_composite CKS W_consume_response_any _ sh t_prsnap (prsnap_val P) (prsnap_val P)
             (JMeq_refl _)); [reflexivity | prove_cs_preserve_type].
Qed.

(* the lent objects of pr_same (v4.1: the device, the index table, the other peers) *)
Lemma hcr5_q5_A5_vo x25519 R L T PS :
  (device_rep Tsh (l_wa L) (hcr5_DAL x25519 R L) * itable Tsh (l_ita L) T *
   peers_rep PS |-- vobjs W_consume_response_any (hcr5_q5_VOp x25519 R L T ++ [VPeers PS]))%logic.
Proof. unfold vobjs, hcr5_q5_VOp. simpl. cancel. Qed.

Lemma hcr5_q5_A5_ov x25519 R L T PS :
  (vobjs W_consume_response_any (hcr5_q5_VOp x25519 R L T ++ [VPeers PS]) |--
   device_rep Tsh (l_wa L) (hcr5_DAL x25519 R L) * itable Tsh (l_ita L) T *
   peers_rep PS)%logic.
Proof. unfold vobjs, hcr5_q5_VOp. simpl. cancel. Qed.

Lemma hcr5_q5_A5_pok L KA PS1 x PS2 : Forall (hcr5_pok L KA) (PS1 ++ x :: PS2) -> vobj_ok (VPeers (PS1 ++ PS2)).
Proof.
  intros H. cbn [vobj_ok]. rewrite Forall_app in H |- *. destruct H as [H1 H2]. inversion H2; subst.
  split; (eapply Forall_impl; [| eassumption]); intros [[p sh] Q] Hq; destruct Hq as [-> _]; auto.
Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcr5_q5_A5_ok {Espec: OracleKind} gv L FR :
  hcr5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> hcr5_q5_pure_stmt x25519 aead_dec ->
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_q5_QA1 x25519 aead_dec gv L FR) hcr5_q5_A5 (overridePost (hcr5_q5_QE x25519 gv L FR) (hcr5_R gv)).
Proof.
  intros HH HP. unfold hcr5_q5_QA1, hcr5_Delta, hcr5_R, hcr5_q5_A5. simplify_func_tycontext.
  Intros R S NS PS head nb T. Intros KE m M a P ck h.
  unfold hcr5_lvars, hcr5_q5_scr, hcr5_world, hcr5_globs, hcr5_snaps; cbn [app].
  abbreviate_semax.
  assert_PROP (itable_wf T) as Hwf by (unfold itable; entailer!).
  destruct HP as (HP1 & _ & _ & HP4 & HP5 & HP6).
  destruct (HP4 R L NS PS head nb KE T M a P ck h H0 H1 Hwf H4)
    as (NS1 & N & NS2 & PS1 & PS2 & E & HPS & Hsf & Hsupd & Hsn & Hna & Hpa & _ & Hnr & Hnrest & _ & _ & _ &
        Hok & _ & _ & _ & Hvp).
  destruct (HP6 PS a P M ck h Hsf) as (Hkeep & Heqb).
  destruct (Hkeep Ews P Hsf) as (_ & Hptrs).
  destruct (HP1 R L NS PS head nb KE T PS H0 H1 Hwf (or_introl eq_refl)) as (Hvo & _).
  assert (Hvo2: vobj_ok (VPeers (PS1 ++ PS2))) by (destruct H0 as (Hpk & _); rewrite HPS in Hpk; exact (hcr5_q5_A5_pok _ _ _ _ _ Hpk)).
  sep_apply (hcr5_q5_A5_node' (hnodes_snapped4 T NS PS) NS1 N NS2 (hcr5_head NS) Hsn). Intros nx.
  rewrite Hna.
  rewrite (Hsupd (hcr5_q5_put P M ck h)), hcr5_q5_A5_papp. unfold peer_item_rep.
  flatten_sepcon_in_SEP.
  (* SEP: 0 the node, 2 the device, 3 the index table, 10 the peer, 11 the other peers (positional freeze) *)
  freeze [1;4;5;6;7;8;9;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31] FR1.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  + apply ENTAIL_refl.
  + rewrite hcr5_q5_A5_split. Intros.
    match goal with Hx: @field_compatible Noise.CS t_peer [] a |- _ => rename Hx into Hfc end.
    forward.
    match goal with |- context [temp HR5._t'57 ?v] => change v with (hn_p N) end. rewrite Hpa.
    forward.
    sep_apply (hcr5_q5_A5_fold Ews a (hcr5_q5_put P M ck h) Hfc).
    forward.
    { match goal with |- context [tc_val tuint ?v] => change v with (hn_refs N) end. rewrite Hnr. entailer!. }
    match goal with |- context [temp HR5._t'59 ?v] => change v with (hn_refs N) end. rewrite Hnr.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
          forward_if (PROPx P (LOCALx (temp HR5._t'54 (Vint Int.one) :: Q) (SEPx R))) end.
    * forward.
      match goal with |- context [temp HR5._t'60 ?v] => change v with (hn_p N) end. rewrite Hpa.
      sep_apply (hcr5_q5_A5_vo x25519 R L T (PS1 ++ PS2)).
      sep_apply (hcr5_q5_A5_rest N nx (hcr5_nfind NS a) P Hnrest).
      forward_call (Ews, offset_val 304 (hcr5_nfind NS a), P, Ews, a, hcr5_q5_put P M ck h,
                    hcr5_q5_VOp x25519 R L T ++ [VPeers (PS1 ++ PS2)]).
      { match goal with |- isptr ?x => match goal with Hx: context [offset_val 304 x] |- _ =>
          apply field_compatible_isptr in Hx; destruct x; try contradiction; exact I end end. }
      { cancel. }
      { apply Forall_app; split; auto. unfold hcr5_q5_VOp; repeat constructor; simpl; auto. }
      rewrite Heqb.
      sep_apply (hcr5_q5_A5_ov x25519 R L T (PS1 ++ PS2)).
      rewrite ?hcr5_q5_A5_prsnap_cs.
      match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
      forward. entailer!.
    * match goal with Hc: ?x <> ?x |- _ => exfalso; exact (Hc eq_refl) end.
    * forward_if.
      { exfalso. match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
      forward. entailer!.
  + forward. apply ENTAIL_refl.
  + unfold POSTCONDITION, abbreviate, overridePost. cbn [RA_normal].
    thaw FR1.
    match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
    destruct H0 as (Hpok & Hpwf & _ & Hnp' & _).
    destruct (HP5 L (hcr5_ka KE) NS PS T KE a (hcr5_q5_put P M ck h) H1 Hnp' Hpwf Hpok)
      as (Hk1 & _ & Hkh & Hn1 & _ & Hw1 & He1 & _).
    unfold hcr5_q5_QE.
    Exists R S NS (hnodes_snapped4 T NS PS) (supd PS a (hcr5_q5_put P M ck h)) head T (map (kent_snapped T) KE) m M.
    unfold hcr5_lvars, hcr5_world, hcr5_globs, hcr5_scr, hcr5_snaps0; cbn [app].
    rewrite Hkh.
    rewrite (Hsupd (hcr5_q5_put P M ck h)), hcr5_q5_A5_papp. unfold peer_item_rep.
    rewrite <- (Hsupd (hcr5_q5_put P M ck h)).
    sep_apply (hcr5_q5_A5_hout M (l_img L) H3). sep_apply (hcr5_q5_A5_hout M (l_imga L) H3).
    sep_apply (@data_at_data_at_ HCS Tsh t_mstate (mstate_val ck h) (l_st L)).
    sep_apply (@data_at_data_at_ CKS Tsh t_devsnap (devsnap_val (hcr5_DAL x25519 R L) head) (l_ds L)).
    sep_apply (@data_at_data_at_ CKS Tsh t_shimsnap (shimsnap_val S hcr5_w0) (l_ss L)).
    go_lower.
    apply andp_right; [apply prop_right | cancel].
    refine (conj H (conj Hn1 (conj Hw1 (conj Hk1 (conj H2 (conj H3 (conj He1 _))))))).
    rewrite ?eqb_type_refl; repeat split; auto.
Time Qed.

End Seg.
