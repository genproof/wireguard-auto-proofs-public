(* law handshake_receive, phase B8 branch I, segment I0: t341 = target->p; h = &t341->handshake; s = &target->snap; CHECK(rx_authenticated(target->p, &skb, 1, 0))  (QI0 -> QI).

   Shared (proved): hrx5_B8_I_sep.v (accessors, port of hci5_p8_A3_sep.v), hrx5_B8_I_pure.v (the model analysis). *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_I_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_I_sep.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_I_pure.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

(* ---- helpers of segment I0 (prefix hrx5_B8I0_) ---- *)
Lemma hrx5_B8I0_node T NS PS a sh P : hnodes_peers4 NS PS -> In (a, sh, P) PS ->
  exists N, In N (hnodes_snapped4 T NS PS) /\ hn_addr N = hrx5_nfind NS a /\ hn_p N = a.
Proof.
  unfold hnodes_peers4, hnodes_snapped4. revert PS.
  induction NS as [|N NS IH]; intros [|x PS] Hm Hin; simpl in Hm; try discriminate; try contradiction.
  injection Hm as H0 H1. cbn [combine map hrx5_nfind].
  destruct (eq_dec (hn_p N) a) as [E|E].
  - exists (hn_snapshot4 T N x). split; [left; reflexivity|].
    destruct x as [[p s0] Q]. cbn [hn_snapshot4 hn_addr hn_p]. auto.
  - destruct Hin as [Hin|Hin].
    + subst x. cbn [peer_addr4] in H0. congruence.
    + destruct (IH PS H1 Hin) as (N0 & HN0 & HA & HP). exists N0. split; [right; exact HN0|]. auto.
Qed.

Lemma hrx5_B8I0_sfind (l: list (val * share * peer)) a sh v :
  NoDup (map peer_addr4 l) -> In (a, sh, v) l -> sfind l a = Some (sh, v).
Proof.
  induction l as [|[[x s0] w0] l IH]; simpl; intros Hn H; [contradiction|].
  inversion Hn as [|? ? Hx Hn']; subst. destruct (EqDec_val x a) as [->|n].
  - destruct H as [H|H]; [inversion H; auto|].
    exfalso. apply Hx. apply (in_map peer_addr4) in H. exact H.
  - destruct H as [H|H]; [inversion H; congruence | auto].
Qed.

Lemma hrx5_B8I0_acc_dev sh a Q : hrx5_B8I_acc (rx_pfield sh a (p_device Q)) (peer_rep sh a Q).
Proof.
  unfold peer_rep, rx_pfield. apply hrx5_B8I_acc_prop; intros _.
  do 10 apply hrx5_B8I_acc_l. apply hrx5_B8I_acc_refl.
Qed.

Lemma hrx5_B8I_I0_ok : hrx5_B8I_I0_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc q
    proto ip4 ip6 port M dp img a P t ck2 h2 key spub sec1 birth1 S1 lul1 HY.
  unfold hrx5_B8I_QI0, hrx5_B8I_QI, hrx5_B8I_props, hrx5_B8I_temps, hrx5_B8I_world, hrx5_B8I_scr.
  unfold hrx5_Delta, hrx5_lvars, hrx5_rest, hrx5_cglobs; cbn [app].
  simplify_func_tycontext. abbreviate_semax.
  Intros.
  destruct (hrx5_B8I_tgt_in x25519 aead_dec _ _ _ _ _ _ _ _ _ H9) as [sh Hin].
  pose proof H3 as (Hpok & _ & Hnd & _ & Hnp & _).
  assert (Hsh: sh = Ews) by (rewrite Forall_forall in Hpok; exact (proj1 (Hpok _ Hin))). subst sh.
  pose proof (hrx5_B8I0_sfind PS a Ews P Hnd Hin) as Hsf.
  destruct (hrx5_B8I0_node T NS PS a Ews P Hnp Hin) as (N & HN & HNa & HNp).
  pose proof (hrx5_B8I_nodes_acc (@field_at W Ews t_hnode4 [StructField HC._p] (hn_p N) (hn_addr N)) N _
    (hrx5_head (hnodes_snapped4 T NS PS)) HN (fun nx => hrx5_B8I_nfld_p N nx)) as HA.
  unfold hrx5_B8I_acc in HA. sep_apply HA. clear HA.
  rewrite HNp, HNa.
  rewrite (hrx5_B8I_peers PS a Ews P _ Hsf).
  assert_PROP (@field_compatible Noise.CS t_peer [] a) as Hfca. { unfold peer_rep. entailer!. }
  assert (Pa: isptr a) by exact (@field_compatible_isptr Noise.CS _ _ _ Hfca).
  repeat flatten_sepcon_in_SEP.
  unfold hrx5_B8I_I0.
  forward. forward. forward.
  match goal with |- context [temp HRM._h__1 ?v] => change v with (hs_addr a) end.
  match goal with |- context [temp HRM._s ?v] => change v with (offset_val 8 (hrx5_nfind NS a)) end.
  pose proof (hrx5_B8I0_acc_dev Ews a (hrx5_B8I_put P M (s_boot S) t ck2 h2)) as HA.
  unfold hrx5_B8I_acc in HA. sep_apply HA. clear HA.
  repeat flatten_sepcon_in_SEP.
  destruct (hrx5_B8I_log_auth a (l_skb L) (sk_len (hrx5_skb dp (OInit M) proto ip4 ip6 port))) as (Hau & Hpe & Hes).
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: Pre end.
  { apply ENTAIL_refl. }
  - forward.
    forward_call (gv, hrx5_B8I_log a (l_skb L) (sk_len (hrx5_skb dp (OInit M) proto ip4 ip6 port)), a, Ews,
      p_device (hrx5_B8I_put P M (s_boot S) t ck2 h2), Tsh, l_skb L, hrx5_skb dp (OInit M) proto ip4 ip6 port,
      Int.one, Int.zero).
    rewrite Hau. change (if true then Int.one else Int.zero) with Int.one.
    match goal with |- semax _ ?Pre _ _ => forward_if Pre end.
    + exfalso. match goal with H: Int.one = Int.zero |- _ => exact (Int.one_not_zero H) end.
    + forward. destruct (hrx5_RB x25519 gv L FR) as [r1 r2 r3 r4].
      cbv beta iota delta [loop_nocontinue_ret_assert loop1_ret_assert overridePost RA_normal RA_break].
      entailer!.
    + forward. destruct (hrx5_RB x25519 gv L FR) as [r1 r2 r3 r4].
      cbv beta iota delta [loop_nocontinue_ret_assert loop1_ret_assert overridePost RA_normal RA_break].
      entailer!.
  - destruct (hrx5_RB x25519 gv L FR) as [r1 r2 r3 r4].
    cbv beta iota delta [overridePost RA_normal].
    sep_apply (hrx5_B8I_mp (rx_pfield Ews a (p_device (hrx5_B8I_put P M (s_boot S) t ck2 h2)))
      (peer_rep Ews a (hrx5_B8I_put P M (s_boot S) t ck2 h2))).
    sep_apply (hrx5_B8I_mp (field_at Ews t_hnode4 (DOT HC._p) a (hrx5_nfind NS a))
      (hnodes_rep4 W (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS))).
    rewrite (hrx5_B8I_peers PS a Ews P _ Hsf).
    entailer!.
Qed.
