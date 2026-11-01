(* law handshake_receive, B8 branch R segment D part CHK: the CHECK block
   on the opened state hrx5_B8RDc_S (the node at W, its peer, the table, the device, the other peers; the rest framed
   in FRM).  Port of law handshake_clear's hcl5_p7_chk_body.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_cut.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mspec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require WgNoise.contracts.x_handshake_receive.
Require WgNoise.harness.x_handshake_receive.code.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_conv.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_ilem.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_D_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_D_chk_lem.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Section Body.
Context {Espec: OracleKind}.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variables (gv: globals) (L: hrx5_loc) (tg: val).
Variables (vh vs vallok vsess vnk vkes vsteps vi vnow vlul vbuf vmi vmr vmc vimg vlen vkind vai var vhead0
           vpath: val).

(* the opened state *)
Definition hrx5_B8RDc_S (x: val) (h: Z) (q: val) (Q: peer) (T Tf: tstate) (nx: val) (D: device)
  (others: list (val * share * peer)) (FRM: mpred) : environ -> mpred :=
  PROPx []
  (LOCALx (hrx5_B8RD_lc gv L tg vh vs vallok vsess vnk vkes vsteps vi vnow vlul vbuf vmi vmr vmc vimg vlen vkind
             vai var vhead0 vpath x h)
  (SEPx [@data_at W_handshake_receive Ews t_hnode4 (hrx5_B8RD_nv q (hs_snap_cur T q Q) Q nx) x;
         peer_rep Ews q Q; itable Tsh (l_itd L) Tf; device_rep Tsh (l_wd L) D; peers_rep others; FRM])).

Lemma hrx5_B8RDc_body x h q Q T Tf nx D others FRM Rp :
  In (hs_addr q) (saddrs (t_D Tf)) ->
  e_peer (t_entry_d T (hs_addr q)) = q ->
  e_peer (t_entry_d Tf (hs_addr q)) = q ->
  hs_sid (p_hs Q) = id_addr (l_wd L) ->
  snap_eqb_nn (hs_snap_cur T q Q) (hs_snap_cur Tf q Q) = true ->
  p_device Q = l_wd L -> p_cur Q = nullval -> p_prev Q = nullval -> p_next Q = nullval ->
  p_pknext Q = nullval \/ In (p_pknext Q) (map peer_addr4 others) ->
  Forall (fun y => match y with (_, sh, _) => sh = Ews end) others ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B8RDc_S x h q Q T Tf nx D others FRM)
    hrx5_B8RD_chk (overridePost (hrx5_B8RDc_S x h q Q T Tf nx D others FRM) Rp).
Proof.
  intros Hin Hep Hepf Hsid Hsnap Hd Hc Hp Hn Hpk Hoth. destruct Rp as [Rn Rb Rc Rr].
  unfold hrx5_Delta. simplify_func_tycontext.
  unfold hrx5_B8RD_chk, hrx5_B8RDc_S, hrx5_B8RD_lc, hrx5_B8RD_lcr, hrx5_lvars. cbn [app].
  abbreviate_semax.
  assert_PROP (field_compatible t_hnode4 [] x) as FCx by entailer!.
  assert_PROP (@field_compatible Noise.CS t_peer [] q) as FC.
  { sep_apply (hrx5_B8RDc_peer_fc Ews q Q). entailer!. }
  assert (Pq: isptr q) by (destruct FC; auto).
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { sep_apply (hrx5_B8RDc_node_p Ews q (hs_snap_cur T q Q) Q nx x). Intros.
    forward.
    sep_apply (hrx5_B8RDc_mp (field_at Ews t_hnode4 [StructField HC._p] q x)).
    sep_apply (hrx5_B8RDc_node_snap Ews q (hs_snap_cur T q Q) Q nx x). Intros.
    rewrite hrx5_B8RDc_HW.
    rewrite <- (hrx5_B8RDc_vo1 Tsh (l_wd L) D).
    change (peer_rep Ews q Q) with (hs_mem true Ews q Q).
    forward_call (Ews, field_address t_hnode4 [StructField HC._snap] x, hs_snap_cur T q Q, Ews, q,
                  Q, true, Tsh, l_itd L, Tf, [VDev Tsh (l_wd L) D]).
    { split; [constructor; [simpl; auto | constructor]|].
      unfold hs_ptrs_nn, hs_snap_cur, snap_of; cbn [sn_entry sn_hs].
      rewrite Hep, Hepf, Hsid. unfold hs_own, vp_ok.
      apply Forall_forall; intros y Hy; right; simpl in Hy |- *.
      destruct Hy as [<-|[<-|[<-|[<-|[]]]]]; auto 10.
      all: right; apply in_app_iff; right; simpl; auto. }
    rewrite Hsnap.
    rewrite <- hrx5_B8RDc_HW.
    sep_apply (hrx5_B8RDc_mp (@data_at HCS Ews t_hsnap (hsnap_val (hs_snap_cur T q Q))
                             (field_address t_hnode4 [StructField HC._snap] x))).
    rewrite hrx5_B8RDc_vo1. unfold hs_mem.
    forward_if (temp HRM._t'189 (Vint Int.one)).
    { sep_apply (hrx5_B8RDc_node_p Ews q (hs_snap_cur T q Q) Q nx x). Intros.
      forward.
      sep_apply (hrx5_B8RDc_mp (field_at Ews t_hnode4 [StructField HC._p] q x)).
      pose proof (hrx5_B8RDc_peer_refs Ews q Q) as A; unfold hrx5_B8RDc_acc in A; sep_apply A; clear A. Intros.
      forward.
      sep_apply (hrx5_B8RDc_mp (@field_at W_handshake_receive Ews t_peer (DOT HC._refcount DOT HC._refcount)
                                   (Vint (p_refs Q)) q)).
      sep_apply (hrx5_B8RDc_node_refs Ews q (hs_snap_cur T q Q) Q nx x). Intros.
      forward.
      sep_apply (hrx5_B8RDc_mp (field_at Ews t_hnode4 [StructField HC._refs] (Vint (p_refs Q)) x)).
      forward.
      entailer!. rewrite Int.eq_true. reflexivity. }
    { exfalso; apply Int.one_not_zero; assumption. }
    forward_if (temp HRM._t'190 (Vint Int.one)).
    { sep_apply (hrx5_B8RDc_node_p Ews q (hs_snap_cur T q Q) Q nx x). Intros.
      forward.
      sep_apply (hrx5_B8RDc_mp (field_at Ews t_hnode4 [StructField HC._p] q x)).
      sep_apply (hrx5_B8RDc_node_rest Ews q (hs_snap_cur T q Q) Q nx x). Intros.
      sep_apply (derives_refl' _ _ (eq_sym (hrx5_B8RDc_vo2 (l_wd L) D others))).
      forward_call (Ews, field_address t_hnode4 [StructField HC._rest] x, Q, Ews, q, Q,
                    hrx5_B8RDc_VO (l_wd L) D others).
      { split; [|apply hrx5_B8RDc_vp; auto].
        unfold hrx5_B8RDc_VO. repeat apply Forall_cons; try apply Forall_nil; simpl; auto.
        eapply Forall_impl; [|exact Hoth]. intros [[b sh] Q'] ->. auto. }
      rewrite hrx5_B8RDc_pr_refl.
      forward.
      rewrite hrx5_B8RDc_vo2. Intros.
      first [ sep_apply (hrx5_B8RDc_mp (@data_at CKS Ews t_prsnap (prsnap_val Q) (field_address t_hnode4 [StructField HC._rest] x)))
            | rewrite hrx5_B8RDc_PW;
              sep_apply (hrx5_B8RDc_mp (@data_at W_handshake_receive Ews t_prsnap (prsnap_val Q) (field_address t_hnode4 [StructField HC._rest] x))) ].
      entailer!. }
    { exfalso. apply Int.one_not_zero. assumption. }
    forward_if.
    { exfalso. first [apply Int.one_not_zero; assumption | apply H; reflexivity]. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  unfold POSTCONDITION, abbreviate. simpl RA_normal. apply ENTAIL_refl.
Qed.

End Body.
