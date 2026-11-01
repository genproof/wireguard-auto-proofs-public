(* law consume_initiation_any, phase P8, segment A3, statement s12 (port of v1's hci3_p8_A3_s12.v):
     CHECK(target->p->refcount.refcount == target->refs && pr_same(&target->rest, target->p))   QA1 -> Q2
   Shared: hci5_p8_A3_defs.v (statements, cut), hci5_p8_A3_pure.v
   (hci5_p8_A3_facts), hci5_p8_A3_sep.v (accessors). *)
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
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A3_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A3_pure.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A3_sep.
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

(* ---- helpers (port of consume_response_any's hcr5_q5_A5, same CHECK) ---- *)

(* the node's value as ONE constant typed at W *)
Definition hci5_p8_A3_s12_nv (N: hnode4) (nx: val) : @reptype W t_hnode4 :=
  (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))).

Lemma hci5_p8_A3_s12_node_W v l :
  @data_at CKS Ews t_hnode4 v l = @data_at W Ews t_hnode4 v l.
Proof.
  rewrite (@data_at_change_composite CKS W _ Ews t_hnode4 v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hci5_p8_A3_s12_node NS1 N NS2 : forall l,
  hnodes_rep4 W l (NS1 ++ N :: NS2) |--
  EX nx: val,
    (@data_at W Ews t_hnode4 (hci5_p8_A3_s12_nv N nx) (hn_addr N) *
     (@data_at W Ews t_hnode4 (hci5_p8_A3_s12_nv N nx) (hn_addr N) -*
      hnodes_rep4 W l (NS1 ++ N :: NS2)))%logic.
Proof.
  unfold hci5_p8_A3_s12_nv.
  induction NS1 as [| N1 NS1 IH]; intros l; simpl app; simpl hnodes_rep4.
  - Intros nx. subst l. Exists nx. rewrite <- hci5_p8_A3_s12_node_W. cancel.
    rewrite <- wand_sepcon_adjoint. Exists nx. entailer!.
  - Intros nx. sep_apply (IH nx). Intros nx'. Exists nx'. cancel.
    rewrite <- wand_sepcon_adjoint.
    match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
    Exists nx. entailer!.
Qed.

Lemma hci5_p8_A3_s12_node' NS NS1 N NS2 l : NS = NS1 ++ N :: NS2 ->
  hnodes_rep4 W l NS |--
  EX nx: val,
    (@data_at W Ews t_hnode4 (hci5_p8_A3_s12_nv N nx) (hn_addr N) *
     (@data_at W Ews t_hnode4 (hci5_p8_A3_s12_nv N nx) (hn_addr N) -*
      hnodes_rep4 W l NS))%logic.
Proof. intros ->. apply hci5_p8_A3_s12_node. Qed.

(* the node's field rest, as pr_same's snapshot (at CKS, offset 304 of struct hnode) *)
Lemma hci5_p8_A3_s12_rest N nx x P : hn_rest N = prsnap_val P ->
  @data_at W Ews t_hnode4 (hci5_p8_A3_s12_nv N nx) x |--
  (@data_at CKS Ews t_prsnap (prsnap_val P) (offset_val 304 x) *
   (@data_at CKS Ews t_prsnap (prsnap_val P) (offset_val 304 x) -*
    @data_at W Ews t_hnode4 (hci5_p8_A3_s12_nv N nx) x))%logic.
Proof.
  intros Hr. rewrite <- hci5_p8_A3_s12_node_W. unfold hci5_p8_A3_s12_nv.
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

(* pr_same's post gives the snapshot back at the world (common4 v4.1); the node's wand wants it at CKS *)
Lemma hci5_p8_A3_s12_mp P p X :
  (@data_at W Ews t_prsnap (prsnap_val P) p * (@data_at CKS Ews t_prsnap (prsnap_val P) p -* X) |-- X)%logic.
Proof.
  rewrite <- (@data_at_change_composite CKS W _ Ews t_prsnap (prsnap_val P) (prsnap_val P) (JMeq_refl _))
    by prove_cs_preserve_type.
  apply modus_ponens_wand.
Qed.

(* the objects lent to pr_same (common4 v4.1: the kents' addresses are lent by the index table) *)
Definition hci5_p8_A3_s12_VO (D: device) (wb itb: val) (T: tstate) (PS: list (val * share * peer)) : list vobj :=
  [VDev Tsh wb D; VItab Tsh itb T; VPeers PS].

Lemma hci5_p8_A3_s12_vo D wb itb T PS :
  (device_rep Tsh wb D * itable Tsh itb T * peers_rep PS |--
   vobjs W (hci5_p8_A3_s12_VO D wb itb T PS))%logic.
Proof. unfold vobjs, hci5_p8_A3_s12_VO. simpl. cancel. Qed.

Lemma hci5_p8_A3_s12_ov D wb itb T PS :
  (vobjs W (hci5_p8_A3_s12_VO D wb itb T PS) |--
   device_rep Tsh wb D * itable Tsh itb T * peers_rep PS)%logic.
Proof. unfold vobjs, hci5_p8_A3_s12_VO. simpl. cancel. Qed.

Lemma hci5_p8_A3_s12_vook D wb itb T PS :
  Forall (fun x => match x with (_, sh, _) => sh = Ews end) PS ->
  Forall vobj_ok (hci5_p8_A3_s12_VO D wb itb T PS).
Proof.
  intros H. unfold hci5_p8_A3_s12_VO. repeat constructor; cbn [vobj_ok]; auto.
  eapply Forall_impl; [| exact H]. intros [[p sh] Q] ->. auto.
Qed.

Lemma hci5_p8_A3_s12_ptrs D wb itb KE T PS a P M now t ck2 h2 :
  (forall k, In k (map ke_addr KE) -> In k (saddrs (t_D T))) ->
  p_device P = wb ->
  (p_pknext P = nullval \/ In (p_pknext P) (map peer_addr4 PS)) ->
  Forall (fun k : val => k = nullval \/ In k (map ke_addr KE)) [p_cur P; p_prev P; p_next P] ->
  Forall (vp_ok (a :: vobjs_addrs (hci5_p8_A3_s12_VO D wb itb T PS))) (pr_ptrs P (hci5_p8_put P M now t ck2 h2)).
Proof.
  intros HK Hd Hk Hs. unfold vobjs_addrs, hci5_p8_A3_s12_VO. cbn [map vobj_addrs concat].
  rewrite app_nil_r.
  pose proof (Forall_inv Hs) as Hc. pose proof (Forall_inv (Forall_inv_tail Hs)) as Hp.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail Hs))) as Hn.
  assert (G: forall x, x = nullval \/ In x (map ke_addr KE) ->
    vp_ok (a :: [wb; id_addr wb; cc_addr wb] ++ (itb :: saddrs (t_D T)) ++ map peer_addr4 PS) x).
  { intros x [-> | Hx]; [left; reflexivity |].
    right; right; apply in_app_iff; right; apply in_app_iff; left; right; apply HK; exact Hx. }
  assert (G2: vp_ok (a :: [wb; id_addr wb; cc_addr wb] ++ (itb :: saddrs (t_D T)) ++ map peer_addr4 PS) (p_pknext P)).
  { destruct Hk as [-> | Hx]; [left; reflexivity |
      right; right; apply in_app_iff; right; apply in_app_iff; right; exact Hx]. }
  assert (G3: vp_ok (a :: [wb; id_addr wb; cc_addr wb] ++ (itb :: saddrs (t_D T)) ++ map peer_addr4 PS) (p_device P)).
  { rewrite Hd. right. right. left. reflexivity. }
  unfold pr_ptrs, hci5_p8_put, hci5_new, p_set_hs, p_set_refs. cbn [p_device p_cur p_prev p_next p_pknext].
  repeat (apply Forall_cons; [solve [auto] |]). apply Forall_nil.
Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hci5_p8_A3_s12_ok {Espec: OracleKind} gv L FR :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_p8_QA1 x25519 aead_dec gv L FR)
    hci5_p8_A3_s12 (overridePost (hci5_p8_Q2 x25519 gv L FR) (hci5_R gv)).
Proof.
  intros HH. destruct HH as (Hx & Ha & Hxa & Hrep).
  unfold hci5_p8_QA1, hci5_p8_Q2, hci5_Delta, hci5_R, hci5_p8_A3_s12. simplify_func_tycontext.
  Intros R S w NS PS T head na KE m M. Intros a P t ck2 h2 key spub.
  unfold hci5_lvars, hci5_world, hci5_globs, hci5_snaps0, hci5_p8_scr; cbn [app].
  abbreviate_semax.
  assert_PROP (itable_wf T) as Hwf by (unfold itable; entailer!).
  destruct (hci5_p8_A3_facts x25519 aead_enc aead_dec R L NS PS KE T head na M (s_boot S) a P t ck2 h2 Ha H0 Hwf H1 H3)
    as (NS1 & N & NS2 & PS1 & PS2 & HNS & Hna & Hnp & Hsn & Hnr & Hnrest & HPS & Hdel & Hsf & Hin & Hpok & HinT & Hep
        & Hpkn & Hslot & Lt & Lck & Lh).
  rewrite (hci5_p8_A3_peers PS a Ews P (hci5_p8_put P M (s_boot S) t ck2 h2) Hsf), Hdel.
  sep_apply (hci5_p8_A3_s12_node' (hnodes_snapped4 T NS PS) NS1 N NS2 (hci5_head NS) HNS). Intros nx.
  rewrite Hna.
  assert (Hsh: Forall (fun x : val * share * peer => match x with (_, sh, _) => sh = Ews end) (PS1 ++ PS2)).
  { destruct H0 as (Hok & _). rewrite HPS in Hok. apply Forall_app in Hok. destruct Hok as [Hk1 Hk2].
    inversion Hk2; subst. apply Forall_app; split; (eapply Forall_impl; [| eassumption]);
    intros [[p sh] Q] Hq; destruct Hq as [-> _]; reflexivity. }
  assert (HKT: forall k, In k (map ke_addr KE) -> In k (saddrs (t_D T))).
  { destruct H0 as (_ & _ & _ & _ & _ & (HD & _) & _). intros k Hk. rewrite HD. apply in_app_iff. left. exact Hk. }
  assert (Hptrs := hci5_p8_A3_s12_ptrs (hci5_DB x25519 R L) (l_wb L) (l_itb L) KE T (PS1 ++ PS2) a P M (s_boot S) t ck2 h2
    HKT (proj1 (proj2 Hpok)) Hpkn Hslot).
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: Pre end.
  - apply ENTAIL_refl.
  - sep_apply (hci5_p8_A3_pk_refs Ews a (hci5_p8_put P M (s_boot S) t ck2 h2)).
    rewrite (hci5_p8_A3_put_refs P M (s_boot S) t ck2 h2). Intros.
    forward.
    match goal with |- context [temp HC5._t'63 ?v] => change v with (hn_p N) end. rewrite Hnp.
    forward. forward.
    { match goal with |- context [tc_val tuint ?v] => change v with (hn_refs N) end. rewrite Hnr. entailer!. }
    match goal with |- context [temp HC5._t'65 ?v] => change v with (hn_refs N) end. rewrite Hnr.
    sep_apply (hci5_p8_A3_mp (@field_at W Ews t_peer [StructField prot_repr3.I._refcount] (Vint (p_refs P)) a)
      (peer_rep Ews a (hci5_p8_put P M (s_boot S) t ck2 h2))).
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
          forward_if (PROPx P (LOCALx (temp HC5._t'60 (Vint Int.one) :: Q) (SEPx R))) end.
    + forward.
      match goal with |- context [temp HC5._t'66 ?v] => change v with (hn_p N) end. rewrite Hnp.
      sep_apply (hci5_p8_A3_s12_vo (hci5_DB x25519 R L) (l_wb L) (l_itb L) T (PS1 ++ PS2)).
      sep_apply (hci5_p8_A3_s12_rest N nx (hci5_nfind NS a) P Hnrest).
      forward_call (Ews, offset_val 304 (hci5_nfind NS a), P, Ews, a, hci5_p8_put P M (s_boot S) t ck2 h2,
                    hci5_p8_A3_s12_VO (hci5_DB x25519 R L) (l_wb L) (l_itb L) T (PS1 ++ PS2)).
      { match goal with |- isptr ?x => match goal with Hx: context [offset_val 304 x] |- _ =>
          apply field_compatible_isptr in Hx; destruct x; try contradiction; exact I end end. }
      { cancel. }
      { apply hci5_p8_A3_s12_vook; exact Hsh. }
      rewrite hci5_p8_A3_pr_eqb.
      sep_apply (hci5_p8_A3_s12_ov (hci5_DB x25519 R L) (l_wb L) (l_itb L) T (PS1 ++ PS2)).
      sep_apply (hci5_p8_A3_s12_mp P (offset_val 304 (hci5_nfind NS a))
                   (@data_at W Ews t_hnode4 (hci5_p8_A3_s12_nv N nx) (hci5_nfind NS a))).
      forward.
      entailer!.
    + match goal with Hc: ?x <> ?x |- _ => exfalso; exact (Hc eq_refl) end.
    + forward_if True.
      * exfalso. match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end.
      * forward. entailer!.
      * forward. entailer!.
  - assert (E1 := hci5_p8_A3_supd_addrs PS a (hci5_p8_put P M (s_boot S) t ck2 h2)).
    assert (E2: Forall (fun x : val * share * peer => match x with (_, sh, _) => sh = Ews end)
                  (supd PS a (hci5_p8_put P M (s_boot S) t ck2 h2))).
    { apply hci5_p8_A3_supd_shares. destruct H0 as (Hok & _). eapply Forall_impl; [| exact Hok].
      intros [[x sh] w0] Hq. destruct Hq as [-> _]. reflexivity. }
    assert (E3: map hn_p (hnodes_snapped4 T NS PS) = map hn_p NS).
    { apply hci5_p8_A3_snapped_p. destruct H0 as (_ & _ & _ & Hnp' & _). exact Hnp'. }
    assert (E4 := hci5_p8_A3_kents_addr T KE).
    match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
    sep_apply (@data_at_data_at_ HCS Tsh t_mcinit (mcinit_val ck2 h2 key spub (bytes t)) (l_ci L)).
    Exists R S w NS (hnodes_snapped4 T NS PS) PS (supd PS a (hci5_p8_put P M (s_boot S) t ck2 h2)).
    Exists T head na KE (map (kent_snapped T) KE) m M.
    rewrite (hci5_p8_A3_peers PS a Ews P (hci5_p8_put P M (s_boot S) t ck2 h2) Hsf), Hdel.
    entailer!.
Qed.

End Seg.
