(* law handshake_clear, phase P6: statement 18,
   CHECK(target->p->refcount.refcount == target->refs && pr_same(&target->rest, target->p)). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_world.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_cut.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_globals.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_spec.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_defs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_conv.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_p6_lem.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_p6_defs.
Require WgNoise.harness.x_handshake_clear.code.

#[local] Existing Instance W_handshake_clear.
Local Open Scope Z_scope.

(* the objects lent to pr_same: the device, the index table (v4.1: the kents' addresses = the keypair slots are
   pool entries of the table), the other peers (pubkey_next) *)
Definition hcl5_p6_VO (wg: val) (D: device) (it: val) (T': tstate) (others: list (val * share * peer)) : list vobj :=
  [VDev Tsh wg D; VItab Tsh it T'; VPeers others].

Lemma hcl5_p6_vo3 wg D it T' others :
  vobjs W (hcl5_p6_VO wg D it T' others) = (device_rep Tsh wg D * itable Tsh it T' * peers_rep others)%logic.
Proof. unfold vobjs, hcl5_p6_VO. simpl. rewrite sepcon_emp, sepcon_assoc. reflexivity. Qed.

Lemma hcl5_p6_vp18 p wg D it T' others P H :
  p_device P = wg ->
  Forall (fun k => k = nullval \/ In k (saddrs (t_D T'))) [p_cur P; p_prev P; p_next P] ->
  p_pknext P = nullval \/ In (p_pknext P) (map peer_addr4 others) ->
  Forall (vp_ok (p :: vobjs_addrs (hcl5_p6_VO wg D it T' others)))
    (pr_ptrs P (p_set_hs P H)).
Proof.
  intros Hd Hs Hpk.
  assert (E: vobjs_addrs (hcl5_p6_VO wg D it T' others) =
             [wg; id_addr wg; cc_addr wg] ++ (it :: saddrs (t_D T')) ++ map peer_addr4 others).
  { unfold vobjs_addrs, hcl5_p6_VO. simpl. rewrite app_nil_r. reflexivity. }
  rewrite E. clear E.
  set (A := p :: [wg; id_addr wg; cc_addr wg] ++ (it :: saddrs (t_D T')) ++ map peer_addr4 others).
  assert (Hk: forall k, k = nullval \/ In k (saddrs (t_D T')) -> vp_ok A k).
  { intros k [Hk|Hk]; [left; exact Hk |]. right. subst A. right. rewrite in_app_iff. right.
    rewrite in_app_iff. left. right. exact Hk. }
  assert (Hdv: vp_ok A (p_device P)).
  { right. subst A. right. rewrite Hd. left. reflexivity. }
  assert (Hpv: vp_ok A (p_pknext P)).
  { destruct Hpk as [Hpk|Hpk]; [left; exact Hpk|].
    right. subst A. right. rewrite in_app_iff; right; rewrite in_app_iff; right; exact Hpk. }
  inversion Hs as [|a l Hc Hs1]; subst. inversion Hs1 as [|b l' Hp Hs2]; subst.
  inversion Hs2 as [|c l'' Hn _]; subst.
  unfold pr_ptrs, p_set_hs. cbn [p_device p_cur p_prev p_next p_pknext].
  repeat apply Forall_cons; try apply Forall_nil; auto.
Qed.

Section S18.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcl5_p6_seg18 {Espec: OracleKind} gv L KE x p P T nx D others WN FRM Rp :
  p_device P = l_w L ->
  Forall (fun k => k = nullval \/ In k (map ke_addr KE)) [p_cur P; p_prev P; p_next P] ->
  p_pknext P = nullval \/ In (p_pknext P) (map peer_addr4 others) ->
  Forall (fun y => match y with (_, sh, _) => sh = Ews end) others ->
  incl (map ke_addr KE) (saddrs (t_D T)) ->
  semax (hcl5_Delta x25519) (hcl5_p6_Q gv L KE x p P T nx D others WN FRM) hcl5_p6_s18
    (overridePost (hcl5_p6_Q gv L KE x p P T nx D others WN FRM) Rp).
Proof.
  intros Hd Hs Hpk Hoth Hke.
  assert (Hs': Forall (fun k => k = nullval \/ In k (saddrs (t_D (t_remove T (hs_addr p))))) [p_cur P; p_prev P; p_next P]).
  { eapply Forall_impl; [| exact Hs]. intros k [Hk|Hk]; [left; exact Hk | right; apply Hke, Hk]. }
  destruct Rp as [Rn Rb Rc Rr].
  unfold hcl5_Delta. simplify_func_tycontext. unfold hcl5_p6_s18, hcl5_p6_Q. abbreviate_semax.
  assert_PROP (field_compatible t_hnode4 [] x) as FCx by entailer!.
  assert_PROP (@field_compatible Noise.CS t_peer [] p) as FC.
  { sep_apply (hcl5_p6_peer_fc Ews p (p_set_hs P (hs_zero (p_hs P)))). entailer!. }
  assert (Pp: isptr p) by (destruct FC; auto).
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { sep_apply (hcl5_p6_node_p Ews p (hs_snap_cur T p P) (p_refs P) P nx x). Intros.
    forward.
    sep_apply (hcl5_p6_mp (field_at Ews t_hnode4 [StructField HC._p] p x)).
    pose proof (hcl5_p6_peer_refs Ews p (p_set_hs P (hs_zero (p_hs P)))) as A; unfold hcl5_p6_acc in A;
      sep_apply A; clear A. Intros.
    forward.
    sep_apply (hcl5_p6_mp (@field_at W Ews t_peer [StructField HCL5._refcount]
                             (Vint (p_refs (p_set_hs P (hs_zero (p_hs P))))) p)).
    sep_apply (hcl5_p6_node_refs Ews p (hs_snap_cur T p P) (p_refs P) P nx x). Intros.
    forward.
    sep_apply (hcl5_p6_mp (field_at Ews t_hnode4 [StructField HC._refs] (Vint (p_refs P)) x)).
    cbn [p_refs p_set_hs].
    forward_if (temp HCL5._t'9 (Vint Int.one)).
    { sep_apply (hcl5_p6_node_p Ews p (hs_snap_cur T p P) (p_refs P) P nx x). Intros.
      forward.
      sep_apply (hcl5_p6_mp (field_at Ews t_hnode4 [StructField HC._p] p x)).
      sep_apply (hcl5_p6_node_rest Ews p (hs_snap_cur T p P) (p_refs P) P nx x). Intros.
      sep_apply (derives_refl' _ _ (eq_sym (hcl5_p6_vo3 (l_w L) D (l_it L) (t_remove T (hs_addr p)) others))).
      forward_call (Ews, field_address t_hnode4 [StructField HC._rest] x, P, Ews, p, p_set_hs P (hs_zero (p_hs P)),
                    hcl5_p6_VO (l_w L) D (l_it L) (t_remove T (hs_addr p)) others).
      { split; [|apply hcl5_p6_vp18; auto].
        unfold hcl5_p6_VO. repeat apply Forall_cons; try apply Forall_nil; simpl; auto.
        eapply Forall_impl; [|exact Hoth]. intros [[a sh] Q] ->. auto. }
      rewrite hcl5_p6_pr_eqb.
      forward.
      rewrite hcl5_p6_vo3. Intros.
      rewrite hcl5_p6_PW.
      sep_apply (hcl5_p6_mp (@data_at W_handshake_clear Ews t_prsnap (prsnap_val P) (field_address t_hnode4 [StructField HC._rest] x))).
      entailer!. }
    { exfalso. apply H. reflexivity. }
    forward_if.
    { exfalso. apply Int.one_not_zero. assumption. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  unfold POSTCONDITION, abbreviate. simpl RA_normal. apply ENTAIL_refl.
Qed.

End S18.
