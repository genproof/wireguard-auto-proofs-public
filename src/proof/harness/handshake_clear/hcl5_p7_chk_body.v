(* law handshake_clear, phase P7 segment CHK: the CHECK block on the
   opened state hcl5_p7_chk_S (the node at W, its peer, the table, the lent objects; the rest framed in FRM). *)
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
Require Import WgNoise.proof.harness.handshake_clear.hcl5_p7_defs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_p7_chk_lem.

#[local] Existing Instance W_handshake_clear.
Local Open Scope Z_scope.

(* the opened state *)
Definition hcl5_p7_chk_S (gv: globals) (L: hcl5_loc) (KE: list kent4) (x hv tg q: val) (Q: peer) (T: tstate)
  (a nx: val) (D: device) (others: list (val * share * peer)) (FRM: mpred) : environ -> mpred :=
  PROPx []
  (LOCALx ([temp HCL._nd x; temp HCL._hashed hv; temp HCL._kes (hcl5_khead KE); temp HCL._target tg] ++
           hcl5_lvars gv L)
  (SEPx [@data_at W_handshake_clear Ews t_hnode4 (hcl5_p7_nv q (hs_snap_cur T q Q) Q nx) x;
         peer_rep Ews q Q; itable Tsh (l_it L) (t_remove T a); device_rep Tsh (l_w L) D;
         kents_rep W_handshake_clear (hcl5_khead KE) (map (kent_snapped T) KE); peers_rep others; FRM])).

Section Body.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcl5_p7_chk_body {Espec: OracleKind} gv L KE x hv tg q Q T a nx D others FRM Rp :
  In (hs_addr q) (saddrs (t_D T)) ->
  e_peer (t_entry_d T (hs_addr q)) = q ->
  hs_sid (p_hs Q) = id_addr (l_w L) ->
  hs_addr q <> a ->
  p_device Q = l_w L ->
  Forall (fun k => k = nullval \/ In k (map ke_addr KE)) [p_cur Q; p_prev Q; p_next Q] ->
  p_pknext Q = nullval \/ In (p_pknext Q) (map peer_addr4 others) ->
  Forall (fun y => match y with (_, sh, _) => sh = Ews end) others ->
  incl (map ke_addr KE) (saddrs (t_D T)) ->
  semax (hcl5_Delta x25519) (hcl5_p7_chk_S gv L KE x hv tg q Q T a nx D others FRM) hcl5_p7_chk
    (overridePost (hcl5_p7_chk_S gv L KE x hv tg q Q T a nx D others FRM) Rp).
Proof.
  intros Hin Hep Hsid Hne Hd Hs Hpk Hoth Hke.
  assert (Hs': Forall (fun k => k = nullval \/ In k (saddrs (t_D (t_remove T a)))) [p_cur Q; p_prev Q; p_next Q]).
  { eapply Forall_impl; [| exact Hs]. intros k [Hk|Hk]; [left; exact Hk | right; apply Hke, Hk]. }
  destruct Rp as [Rn Rb Rc Rr].
  unfold hcl5_Delta. simplify_func_tycontext. unfold hcl5_p7_chk, hcl5_p7_chk_S, hcl5_lvars. cbn [app].
  abbreviate_semax.
  assert_PROP (field_compatible t_hnode4 [] x) as FCx by entailer!.
  assert_PROP (@field_compatible Noise.CS t_peer [] q) as FC.
  { sep_apply (hcl5_p7_chk_peer_fc Ews q Q). entailer!. }
  assert (Pq: isptr q) by (destruct FC; auto).
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { sep_apply (hcl5_p7_chk_node_p Ews q (hs_snap_cur T q Q) Q nx x). Intros.
    forward.
    sep_apply (hcl5_p7_chk_mp (field_at Ews t_hnode4 [StructField HC._p] q x)).
    sep_apply (hcl5_p7_chk_node_snap Ews q (hs_snap_cur T q Q) Q nx x). Intros.
    rewrite hcl5_p7_chk_HW.
    rewrite <- (hcl5_p7_chk_vo1 Tsh (l_w L) D).
    change (peer_rep Ews q Q) with (hs_mem true Ews q Q).
    forward_call (Ews, field_address t_hnode4 [StructField HC._snap] x, hs_snap_cur T q Q, Ews, q,
                  Q, true, Tsh, l_it L, t_remove T a, [VDev Tsh (l_w L) D]).
    { split; [constructor; [simpl; auto | constructor]|].
      unfold hs_ptrs_nn, hs_snap_cur, snap_of; cbn [sn_entry sn_hs].
      change (t_entry_d (t_remove T a) (hs_addr q)) with (t_entry_d T (hs_addr q)).
      rewrite Hep, Hsid. unfold hs_own, vp_ok.
      apply Forall_forall; intros y Hy; right; simpl in Hy |- *.
      destruct Hy as [<-|[<-|[<-|[<-|[]]]]]; auto 10.
      all: right; apply in_app_iff; right; simpl; auto. }
    rewrite hcl5_p7_chk_snap by exact Hne.
    rewrite <- hcl5_p7_chk_HW.
    sep_apply (hcl5_p7_chk_mp (@data_at HCS Ews t_hsnap (hsnap_val (hs_snap_cur T q Q))
                             (field_address t_hnode4 [StructField HC._snap] x))).
    rewrite hcl5_p7_chk_vo1. unfold hs_mem.
    forward_if (temp HCL._t'12 (Vint Int.one)).
    { sep_apply (hcl5_p7_chk_node_p Ews q (hs_snap_cur T q Q) Q nx x). Intros.
      forward.
      sep_apply (hcl5_p7_chk_mp (field_at Ews t_hnode4 [StructField HC._p] q x)).
      pose proof (hcl5_p7_chk_peer_refs Ews q Q) as A; unfold hcl5_p7_chk_acc in A; sep_apply A; clear A. Intros.
      forward.
      sep_apply (hcl5_p7_chk_mp (@field_at W_handshake_clear Ews t_peer [StructField HCL5._refcount]
                                   (Vint (p_refs Q)) q)).
      sep_apply (hcl5_p7_chk_node_refs Ews q (hs_snap_cur T q Q) Q nx x). Intros.
      forward.
      sep_apply (hcl5_p7_chk_mp (field_at Ews t_hnode4 [StructField HC._refs] (Vint (p_refs Q)) x)).
      forward.
      entailer!. rewrite Int.eq_true. reflexivity. }
    { exfalso; apply Int.one_not_zero; assumption. }
    forward_if (temp HCL._t'13 (Vint Int.one)).
    { sep_apply (hcl5_p7_chk_node_p Ews q (hs_snap_cur T q Q) Q nx x). Intros.
      forward.
      sep_apply (hcl5_p7_chk_mp (field_at Ews t_hnode4 [StructField HC._p] q x)).
      sep_apply (hcl5_p7_chk_node_rest Ews q (hs_snap_cur T q Q) Q nx x). Intros.
      sep_apply (derives_refl' _ _ (eq_sym (hcl5_p7_chk_vo3 (l_w L) D (l_it L) (t_remove T a) others))).
      forward_call (Ews, field_address t_hnode4 [StructField HC._rest] x, Q, Ews, q, Q,
                    hcl5_p7_chk_VO (l_w L) D (l_it L) (t_remove T a) others).
      { split; [|apply hcl5_p7_chk_vp; auto].
        unfold hcl5_p7_chk_VO. repeat apply Forall_cons; try apply Forall_nil; simpl; auto.
        eapply Forall_impl; [|exact Hoth]. intros [[b sh] Q'] ->. auto. }
      rewrite hcl5_p7_chk_pr_refl.
      forward.
      rewrite hcl5_p7_chk_vo3. Intros.
      first [ sep_apply (hcl5_p7_chk_mp (@data_at CKS Ews t_prsnap (prsnap_val Q) (field_address t_hnode4 [StructField HC._rest] x)))
            | rewrite hcl5_p7_chk_PW;
              sep_apply (hcl5_p7_chk_mp (@data_at W_handshake_clear Ews t_prsnap (prsnap_val Q) (field_address t_hnode4 [StructField HC._rest] x))) ].
      entailer!. }
    { exfalso. apply Int.one_not_zero. assumption. }
    forward_if.
    { exfalso. first [apply Int.one_not_zero; assumption | apply H; reflexivity]. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  unfold POSTCONDITION, abbreviate. simpl RA_normal. apply ENTAIL_refl.
Qed.

End Body.
