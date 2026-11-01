(* law consume_initiation_any, phase P8, segment A1: the else branch's statements 0..3: h = &target->p->handshake; s = &target->snap; CHECK(ret == target->p && target->p->refcount.refcount == target->refs + 1); wg_peer_put(ret).
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
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Helpers (port of v1 hci3_p8_A1.v)                                       *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hci5_p8_A1_CCE : change_composite_env Noise.CS W_consume_initiation_any.
Proof. make_cs_preserve Noise.CS W_consume_initiation_any. Defined.
#[local] Instance hci5_p8_A1_CCEK : change_composite_env CKS W_consume_initiation_any.
Proof. make_cs_preserve CKS W_consume_initiation_any. Defined.

Lemma hci5_p8_A1_tgt x25519 aead_dec IB PS M now a P t ck2 h2 :
  hci5_tgt x25519 aead_dec IB PS M now = Some (a, P, t, ck2, h2) -> exists s, pk_find PS s = Some (a, P).
Proof.
  unfold hci5_tgt. destruct (mi_ok IB); [|discriminate].
  destruct (m_consume_init1_model _ _ _ _ _) as [[[[s ?] ?] ?]|]; [|discriminate].
  destruct (pk_find PS s) as [[a' P']|] eqn:E; [|discriminate].
  destruct (m_consume_init2_model _ _ _ _ _) as [[[? ?] ?]|]; [|discriminate].
  destruct (andb _ _); [|discriminate]. intros Hs; inv Hs. eauto.
Qed.

Lemma hci5_p8_A1_find_in : forall PS s a P, pk_find PS s = Some (a, P) -> exists sh, In (a, sh, P) PS.
Proof.
  induction PS as [|[[x sh] Q] PS IH]; simpl; intros s a P H; [discriminate|].
  destruct (bytes_eqb (hs_rstatic (p_hs Q)) s).
  - inv H. eauto.
  - destruct (IH _ _ _ H) as [sh' Hin]. eauto.
Qed.

Lemma hci5_p8_A1_nodup PS KE T : itable_wf T -> hci5_T_ok PS KE T -> NoDup (map peer_addr4 PS).
Proof.
  intros (_ & _ & H & _) (Hs & _). rewrite Hs in H.
  apply NoDup_app_remove_l in H.
  apply (NoDup_map_inv hs_addr). rewrite map_map. exact H.
Qed.

Lemma hci5_p8_A1_sfind : forall PS a sh P, NoDup (map peer_addr4 PS) -> In (a, sh, P) PS ->
  sfind PS a = Some (sh, P).
Proof.
  induction PS as [|[[x sh0] w] PS IH]; simpl; intros a sh P Hnd Hin; [contradiction|].
  inv Hnd. destruct Hin as [Heq | Hin].
  - inv Heq. rewrite if_true by auto. reflexivity.
  - rewrite if_false; [eauto|]. intros ->. apply H1.
    change a with (peer_addr4 (a, sh, P)). apply in_map; auto.
Qed.

Lemma hci5_p8_A1_node_find T : forall PS NS a sh P,
  map hn_p NS = map peer_addr4 PS -> NoDup (map peer_addr4 PS) ->
  In (a, sh, P) PS ->
  exists NS1 N NS2, hnodes_snapped4 T NS PS = NS1 ++ N :: NS2 /\ hn_addr N = hci5_nfind NS a /\
    hn_p N = a /\ hn_refs N = Vint (p_refs P).
Proof.
  induction PS as [|[[x sh0] Q] PS IH]; intros NS a sh P Hmap Hnd Hin; [contradiction|].
  destruct NS as [|N0 NS]; [discriminate|]. simpl in Hmap. injection Hmap as Hx Hmap. subst x.
  simpl in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [H1 H2].
  change (hnodes_snapped4 T (N0 :: NS) ((hn_p N0, sh0, Q) :: PS)) with
    (hn_snapshot4 T N0 (hn_p N0, sh0, Q) :: hnodes_snapped4 T NS PS).
  destruct Hin as [Heq | Hin].
  - inv Heq.
    exists [], (hn_snapshot4 T N0 (hn_p N0, sh, P)), (hnodes_snapped4 T NS PS).
    simpl. rewrite if_true by auto. auto.
  - destruct (IH NS a sh P Hmap H2 Hin) as (NS1 & N & NS2 & E & Ha & Hp & Hr).
    exists (hn_snapshot4 T N0 (hn_p N0, sh0, Q) :: NS1), N, NS2.
    split; [rewrite E; reflexivity|]. split; [| auto].
    simpl. rewrite if_false; auto. intros Hx. rewrite Hx in H1. apply H1.
    change a with (peer_addr4 (a, sh, P)). apply in_map; auto.
Qed.

(* the node's value as ONE constant typed at W *)
Definition hci5_p8_A1_nv (N: hnode4) (nx: val) : @reptype W_consume_initiation_any t_hnode4 :=
  (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))).

Lemma hci5_p8_A1_node_W v l :
  @data_at CKS Ews t_hnode4 v l = @data_at W_consume_initiation_any Ews t_hnode4 v l.
Proof.
  rewrite (@data_at_change_composite CKS W_consume_initiation_any _ Ews t_hnode4 v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hci5_p8_A1_node NS1 N NS2 : forall l,
  hnodes_rep4 W_consume_initiation_any l (NS1 ++ N :: NS2) |--
  EX nx: val,
    (@data_at W_consume_initiation_any Ews t_hnode4 (hci5_p8_A1_nv N nx) (hn_addr N) *
     (@data_at W_consume_initiation_any Ews t_hnode4 (hci5_p8_A1_nv N nx) (hn_addr N) -*
      hnodes_rep4 W_consume_initiation_any l (NS1 ++ N :: NS2)))%logic.
Proof.
  unfold hci5_p8_A1_nv.
  induction NS1 as [| N1 NS1 IH]; intros l; simpl app; simpl hnodes_rep4.
  - Intros nx. subst l. Exists nx. rewrite <- hci5_p8_A1_node_W. cancel.
    rewrite <- wand_sepcon_adjoint. Exists nx. entailer!.
  - Intros nx. sep_apply (IH nx). Intros nx'. Exists nx'. cancel.
    rewrite <- wand_sepcon_adjoint.
    match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
    Exists nx. entailer!.
Qed.

Lemma hci5_p8_A1_node' NS NS1 N NS2 l : NS = NS1 ++ N :: NS2 ->
  hnodes_rep4 W_consume_initiation_any l NS |--
  EX nx: val,
    (@data_at W_consume_initiation_any Ews t_hnode4 (hci5_p8_A1_nv N nx) (hn_addr N) *
     (@data_at W_consume_initiation_any Ews t_hnode4 (hci5_p8_A1_nv N nx) (hn_addr N) -*
      hnodes_rep4 W_consume_initiation_any l NS))%logic.
Proof. intros ->. apply hci5_p8_A1_node. Qed.

(* the peer at a in the list after an update *)
Lemma hci5_p8_A1_peers PS a sh P Q : sfind PS a = Some (sh, P) ->
  peers_rep (supd PS a Q) = (peer_rep sh a Q * peers_rep (sdel PS a))%logic.
Proof.
  induction PS as [| [[x sh0] w] PS IH]; simpl; intros Hf; [discriminate |].
  unfold peers_rep in *. destruct (EqDec_val x a) as [Ex | Hne]; [subst x |].
  - inversion Hf; subst. simpl. reflexivity.
  - simpl. rewrite IH by exact Hf. unfold peer_item_rep.
    rewrite <- !sepcon_assoc, (sepcon_comm (peer_rep sh0 x w)). reflexivity.
Qed.

(* the reference count of a peer, at the world's compspecs *)
Lemma hci5_p8_A1_refs sh p r :
  peer_refs_rep sh p r = @field_at W_consume_initiation_any sh t_peer [StructField prot_repr3.I._refcount] (Vint r) p.
Proof.
  unfold peer_refs_rep.
  assert (Hc: cs_preserve_type Noise.CS W_consume_initiation_any (@coeq _ _ hci5_p8_A1_CCE) t_peer = true)
    by (vm_compute; reflexivity).
  assert (E := @field_at_change_composite Noise.CS W_consume_initiation_any hci5_p8_A1_CCE sh t_peer
                 [StructField prot_repr3.I._refcount] (Vint r) (Vint r) (JMeq_refl _) Hc).
  exact (f_equal (fun f => f p) E).
Qed.

(* peer_rep without its device field and its reference count *)
Definition hci5_p8_A1_rest (sh: share) (p: val) (P: peer) : mpred :=
  (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p)%logic.

Lemma hci5_p8_A1_split sh p P :
  peer_rep sh p P =
  (!! @field_compatible Noise.CS t_peer [] p &&
  (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] (p_device P) p *
   @field_at W_consume_initiation_any sh t_peer [StructField prot_repr3.I._refcount] (Vint (p_refs P)) p *
   hci5_p8_A1_rest sh p P))%logic.
Proof.
  rewrite <- hci5_p8_A1_refs. unfold peer_rep, hci5_p8_A1_rest, peer_refs_rep.
  apply pred_ext; apply andp_derives; try apply derives_refl; cancel.
Qed.

Lemma hci5_p8_A1_fold sh p P r :
  @field_compatible Noise.CS t_peer [] p ->
  (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] (p_device P) p *
   @field_at W_consume_initiation_any sh t_peer [StructField prot_repr3.I._refcount] (Vint r) p *
   hci5_p8_A1_rest sh p P |-- peer_rep sh p (p_set_refs P r))%logic.
Proof.
  intros Hfc. rewrite <- hci5_p8_A1_refs. unfold peer_rep, hci5_p8_A1_rest, peer_refs_rep.
  cbn [p_set_refs p_device p_dead p_cur p_prev p_next p_hs p_lsh p_cookie p_refs p_id p_pknext].
  apply andp_right; [apply prop_right; auto | cancel].
Qed.

Lemma hci5_p8_A1_putpre sh p d r : p <> nullval ->
  (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] d p *
   @field_at W_consume_initiation_any sh t_peer [StructField prot_repr3.I._refcount] (Vint r) p |--
   (if eq_dec p nullval then emp
    else (peer_refs_rep sh p r * @field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] d p)))%logic.
Proof. intros Hp. rewrite if_false by exact Hp. rewrite hci5_p8_A1_refs. cancel. Qed.

Lemma hci5_p8_A1_putpost sh p d r : p <> nullval ->
  ((if eq_dec p nullval then emp
    else (peer_refs_rep sh p r * @field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] d p)) |--
   @field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] d p *
   @field_at W_consume_initiation_any sh t_peer [StructField prot_repr3.I._refcount] (Vint r) p)%logic.
Proof. intros Hp. rewrite if_false by exact Hp. rewrite hci5_p8_A1_refs. cancel. Qed.

Lemma hci5_p8_A1_vp sh d p : sepalg.nonidentity sh ->
  (@field_at Noise.CS sh t_peer [StructField prot_repr3.I._device] d p * TT |-- valid_pointer p)%logic.
Proof.
  intros Hsh. apply sepcon_valid_pointer1. apply field_at_valid_ptr0; auto; vm_compute; reflexivity.
Qed.

(* the reference count arithmetic below INT_MAX *)
Lemma hci5_p8_A1_rc (r: int) w : 0 < Int.unsigned r < 2147483647 ->
  rc_add1 r = Int.add r Int.one /\ rc_sub1 (rc_add1 r) = r /\ rc_dec_warn (rc_add1 r) w = w /\
  Int.eq r Int.zero = false.
Proof.
  intros H. pose proof (rc_add1_small r ltac:(lia)) as E.
  split; [exact E|]. split; [apply rc_sub1_add1; exact H|]. split.
  - apply rc_dec_warn_small. rewrite E. unfold Int.add. rewrite Int.unsigned_one.
    rewrite Int.unsigned_repr by rep_lia. lia.
  - apply Int.eq_false. intros ->. rewrite Int.unsigned_zero in H. lia.
Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hci5_p8_A1_ok {Espec: OracleKind} gv L FR :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_p8_QA0 x25519 aead_dec gv L FR) hci5_p8_A1
    (overridePost (hci5_p8_QA1 x25519 aead_dec gv L FR) (hci5_R gv)).
Proof.
  intros HH. unfold hci5_p8_QA0, hci5_p8_QA1, hci5_Delta, hci5_R, hci5_p8_A1. simplify_func_tycontext.
  Intros R S w NS PS T head na KE m M. Intros a P t ck2 h2 key spub.
  unfold hci5_lvars, hci5_p8_scr, hci5_world, hci5_globs, hci5_snaps0; cbn [app].
  abbreviate_semax.
  assert_PROP (itable_wf T) as Hwf by (unfold itable; entailer!).
  destruct (hci5_p8_A1_tgt _ _ _ _ _ _ _ _ _ _ _ H3) as [s Hpk].
  destruct (hci5_p8_A1_find_in _ _ _ _ Hpk) as [sh Hin].
  pose proof H0 as [Hpok [_ [_ [Hnp [_ [HTok _]]]]]].
  pose proof (hci5_p8_A1_nodup PS KE T Hwf HTok) as Hnd.
  assert (Hok: hci5_pok x25519 R L (a, sh, P)) by (rewrite Forall_forall in Hpok; apply Hpok; exact Hin).
  destruct Hok as (-> & _ & _ & _ & _ & Hr & _).
  destruct (hci5_p8_A1_rc (p_refs P) w Hr) as (Hadd & Hsub & Hwarn & Hnz).
  pose proof (hci5_p8_A1_sfind PS a Ews P Hnd Hin) as Hsf.
  destruct (hci5_p8_A1_node_find T PS NS a Ews P Hnp Hnd Hin)
    as (NS1 & N & NS2 & Hsn & Hna & Hpa & Hnr).
  sep_apply (hci5_p8_A1_node' (hnodes_snapped4 T NS PS) NS1 N NS2 (hci5_head NS) Hsn). Intros nx.
  rewrite Hna.
  rewrite (hci5_p8_A1_peers PS a Ews P (hci5_new P M (s_boot S) t ck2 h2) Hsf), hci5_p8_A1_split. Intros.
  match goal with Hx: @field_compatible Noise.CS t_peer [] a |- _ => rename Hx into Hfc end.
  assert (Hpn: a <> nullval) by (intros Ea; rewrite Ea in Hfc; exact (field_compatible_isptr _ _ _ Hfc)).
  freeze FR1 := - (data_at Ews t_hnode4 _ _) (shim_state4 _ _ _)
    (@field_at _ Ews t_peer (DOT prot_repr3.I._device) _ a) (@field_at _ Ews t_peer (DOT prot_repr3.I._refcount) _ a).
  forward.
  match goal with |- context [temp HC5._t'90 ?v] => change v with (hn_p N) end. rewrite Hpa.
  forward. forward.
  match goal with |- context [temp HC._s ?v] => replace v with (offset_val 8 (hci5_nfind NS a)) by (simpl; reflexivity) end.
  match goal with |- context [temp HC._h ?v] =>
    replace v with (hs_addr a) by (unfold hs_addr, OFS_PEER_HANDSHAKE; f_equal; compute; reflexivity) end.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  + apply ENTAIL_refl.
  + forward.
    match goal with |- context [temp HC5._t'86 ?v] => change v with (hn_p N) end. rewrite Hpa.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
          forward_if (PROPx P (LOCALx (temp HC5._t'39 (Vint Int.one) :: Q) (SEPx R))) end.
    * entailer!. apply denote_tc_test_eq_split;
          (eapply derives_trans; [| apply (hci5_p8_A1_vp Ews); auto]); cancel.
    * forward.
      match goal with |- context [temp HC5._t'87 ?v] => change v with (hn_p N) end. rewrite Hpa.
      forward. forward.
      { match goal with |- context [tc_val tuint ?v] => change v with (hn_refs N) end. rewrite Hnr. entailer!. }
      match goal with |- context [temp HC5._t'89 ?v] => change v with (hn_refs N) end. rewrite Hnr.
      forward. entailer!.
      unfold hci5_new, p_set_hs, p_set_refs. cbn [p_refs]. rewrite Hadd, Int.eq_true. reflexivity.
    * exfalso. auto.
    * forward_if.
      { forward_call tt. all: first [ match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end | entailer!]. }
      forward. entailer!.
  + forward. apply ENTAIL_refl.
  + set (Q := hci5_new P M (s_boot S) t ck2 h2).
    sep_apply (hci5_p8_A1_putpre Ews a (p_device Q) (p_refs Q) Hpn).
    forward_call (gv, S, w, Ews, a, p_refs Q, p_device Q).
    sep_apply (hci5_p8_A1_putpost Ews a (p_device Q) (rc_sub1 (p_refs Q)) Hpn).
    rewrite !if_false by exact Hpn.
    assert (HQ: p_refs Q = rc_add1 (p_refs P)) by reflexivity.
    rewrite HQ, Hsub, Hwarn, Hnz.
    thaw FR1. subst Q.
    sep_apply (hci5_p8_A1_fold Ews a (hci5_new P M (s_boot S) t ck2 h2) (p_refs P) Hfc).
    Exists R S w NS PS T head na KE m M. Exists a P t ck2 h2 key spub.
    rewrite (hci5_p8_A1_peers PS a Ews P (hci5_p8_put P M (s_boot S) t ck2 h2) Hsf). unfold hci5_p8_put.
    match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
    entailer!.
Time Qed.

End Seg.
