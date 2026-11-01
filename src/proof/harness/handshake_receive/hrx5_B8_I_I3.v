(* law handshake_receive, phase B8 branch I, segment I3: CHECK(target->p->refcount.refcount == target->refs && pr_same(&target->rest, target->p))  (QI -> QI).

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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_I_I3_pure.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_I_I3_sep.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Lemma hrx5_B8I_I3_ok : hrx5_B8I_I3_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc q
    proto ip4 ip6 port M dp img a P t ck2 h2 key spub sec1 birth1 S1 lul1 HY.
  unfold hrx5_B8I_QI, hrx5_B8I_props, hrx5_B8I_temps, hrx5_B8I_world, hrx5_B8I_scr, hrx5_Delta,
    hrx5_lvars, hrx5_rest, hrx5_cglobs; cbn [app].
  simplify_func_tycontext. abbreviate_semax.
  Intros.
  assert (Hin: exists sh, In (a, sh, P) PS) by (eapply hrx5_B8I_tgt_in; eassumption).
  destruct Hin as [sh Hin].
  destruct (hrx5_B8I3_pure x25519 R L sec1 birth1 NS PS KE T head nk a sh P (hrx5_B8I_put P M (s_boot S) t ck2 h2)
              ltac:(assumption) Hin eq_refl eq_refl eq_refl eq_refl eq_refl)
    as (N & NS1 & NS2 & PS1 & PS2 & Hsh & Hsf & HNS & HNa & HNp & HNr & HNrest & HPS' & Hvo & Hvo2 & Hvp).
  subst sh.
  set (P' := hrx5_B8I_put P M (s_boot S) t ck2 h2) in *.
  assert_PROP (@field_compatible CKS t_hnode4 [] (hn_addr N)) as Hfcn.
  { rewrite HNS. sep_apply (hrx5_B8I3_node NS1 N NS2 (hrx5_head (NS1 ++ N :: NS2))). Intros nx. entailer!. }
  rewrite <- HNa.
  freeze FR0 := - (device_rep _ _ _) (peers_rep _) (hnodes_rep4 _ _ _) (kents_rep _ _ _).
  unfold hrx5_B8I_I3.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { sep_apply (hrx5_B8I3_node' _ NS1 N NS2 (hrx5_head (hnodes_snapped4 T NS PS)) HNS). Intros nx.
    unfold hrx5_B8I3_flds. Intros.
    rewrite HPS', hrx5_B8I3_papp. unfold peer_item_rep. Intros.
    rewrite HNp.
    assert_PROP (@field_compatible Noise.CS t_peer [] a) as Hfca.
    { unfold peer_rep. Intros. entailer!. }
    assert (Hpa: isptr a) by exact (@field_compatible_isptr Noise.CS _ _ _ Hfca).
    forward.
    sep_apply (hrx5_B8I3_refs Ews a P'). Intros.
    forward.
    forward.
    { rewrite HNr. entailer!. }
    rewrite HNr.
    match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HRM._t'138 (Vint Int.one) :: Q) (SEPx R))) end.
    { forward.
      rewrite (hrx5_B8I3_rest N P (hn_addr N) Hfcn HNrest).
      sep_apply (derives_refl' _ _ (hrx5_B8I3_vo2 x25519 R L sec1 birth1 T KE (PS1 ++ PS2))).
      forward_call (Ews, offset_val 304 (hn_addr N), P, Ews, a, P',
                    hrx5_B8I3_VO x25519 R L sec1 birth1 T KE ++ [VPeers (PS1 ++ PS2)]).
      { apply Forall_app; split; [exact Hvo | constructor; [exact Hvo2 | constructor]]. }
      assert (Hq: pr_eqb P P' = true) by exact (hrx5_B8I3_pr_eqb P _ _ _ _ _).
      rewrite Hq.
      sep_apply (derives_refl' _ _ (eq_sym (hrx5_B8I3_vo2 x25519 R L sec1 birth1 T KE (PS1 ++ PS2)))). Intros.
      rewrite <- (hrx5_B8I3_rest N P (hn_addr N) Hfcn HNrest).
      forward.
      entailer!. }
    { exfalso. match goal with Hc: _ |- _ => apply Hc end.
      change (p_refs P') with (p_refs P). reflexivity. }
    forward_if.
    { exfalso. apply Int.one_not_zero. assumption. }
    forward.
    match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
    change (peer_rep Ews a P') with (peer_item_rep (a, Ews, P')).
    sep_apply (derives_refl' _ _ (eq_sym (hrx5_B8I3_papp PS1 (a, Ews, P') PS2))).
    rewrite HPS'.
    entailer!. }
  { forward. apply ENTAIL_refl. }
  unfold POSTCONDITION, abbreviate. unfold overridePost. destruct (hrx5_RB x25519 gv L FR) as [r1 r2 r3 r4].
  cbn [RA_normal]. thaw FR0. rewrite HNa.
  unfold hrx5_B8I_QI, hrx5_B8I_props, hrx5_B8I_temps, hrx5_B8I_world, hrx5_B8I_scr, hrx5_lvars,
    hrx5_rest, hrx5_cglobs; cbn [app].
  go_lower.
  apply andp_right;
    [apply prop_right; refine (conj H (conj H0 (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7
       (conj H8 (conj H9 (conj H10 (conj H11 _))))))))))))); repeat split; rewrite ?eqb_type_refl; reflexivity |].
  cancel.
Qed.
