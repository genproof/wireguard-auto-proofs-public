(* law handshake_receive, phase B3, branch kind 3, segment A:
   stmts 0..3 (mc = malloc; img = malloc(64); NULL -> free both, continue; len = 64): hrx5_B3_P 3 -> hrx5_K3_A.
*)
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
#[local] Existing Instance W_handshake_receive.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_defs.
Local Open Scope logic.

Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K3_defs.
Local Open Scope logic.

Lemma hrx5_k3a_mc sh p :
  @malloc_token W sh t_cmsg p = !! malloc_compatible 64 p && @malloc_token W sh t_cmsg p.
Proof.
  apply pred_ext.
  - apply andp_right; [| apply derives_refl].
    eapply derives_trans; [apply (@malloc_token_local_facts W sh t_cmsg p) |]. simpl. apply derives_refl.
  - apply andp_left2, derives_refl.
Qed.

Lemma hrx5_k3a_skb L proto ip4 ip6 port : hrx5_skb_part L proto ip4 ip6 port |-- @data_at_ Cookie.CS Tsh t_skb (l_skb L).
Proof. unfold hrx5_skb_part. Intros dv lv. apply (@data_at_data_at_ Cookie.CS). Qed.
Lemma hrx5_k3a_q gv q : qlen_rep gv q |-- @data_at_ HRX Ews tint (gv HM._wg_shim_handshake_queue_len).
Proof. unfold qlen_rep. apply (@data_at_data_at_ HRX). Qed.

Section K3A.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_K3_A_ok {Espec: OracleKind} gv L FR :
  hrx5_B3_lem_stmt x25519 ->
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B3_P x25519 3 gv L FR) hrx5_K3_SA
    (overridePost (hrx5_K3_A x25519 gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HLEM HY. unfold hrx5_Delta, hrx5_B3_P.
  Intros R sec birth S w NS PS T head. Intros nk KE st i kc lul q proto. Intros ip4 ip6 port.
  unfold hrx5_K3_SA, hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app].
  unfold hrx5_RB, hrx5_R.
  abbreviate_semax.
  forward_call (t_cmsg, gv). Intros mc.
  forward_call (tarray tuchar 64, gv). { simpl. rep_lia. } Intros img.
  destruct (eq_dec mc nullval) as [Hmc|Hmc].
  - (* mc == NULL: free both, continue *)
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HRM._t'62 (Vint Int.one) :: Q) (SEPx R))) end.
    + forward. entailer!.
    + subst mc. exfalso. auto.
    + forward_if.
      2: { exfalso. revert H3; vm_compute; discriminate. }
      forward_call (t_cmsg, mc, gv). { destruct (eq_dec mc nullval); [|contradiction]. cancel. }
      forward_call (tarray tuchar 64, img, gv).
      forward.
      unfold hrx5_SC, hrx5_SLc.
      Exists R sec birth S w NS PS T head. Exists nk KE st i kc lul.
      unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr, hrx5_rglobs, hrx5_skb0; cbn [app].
      sep_apply (hrx5_k3a_skb L proto ip4 ip6 port). sep_apply (hrx5_k3a_q gv q).
      entailer!.
  - Intros.
    destruct (eq_dec img nullval) as [Himg|Himg].
    + (* img == NULL: free both, continue *)
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROPx P (LOCALx (temp HRM._t'62 (Vint Int.one) :: Q) (SEPx R))) end.
      * exfalso. auto.
      * forward. subst img. entailer!.
      * forward_if.
        2: { exfalso. revert H3; vm_compute; discriminate. }
        forward_call (t_cmsg, mc, gv). { rewrite if_false by auto. cancel. }
        forward_call (tarray tuchar 64, img, gv). { rewrite if_true by auto. cancel. }
        forward.
        unfold hrx5_SC, hrx5_SLc.
        Exists R sec birth S w NS PS T head. Exists nk KE st i kc lul.
        unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr, hrx5_rglobs, hrx5_skb0; cbn [app].
        sep_apply (hrx5_k3a_skb L proto ip4 ip6 port). sep_apply (hrx5_k3a_q gv q).
        entailer!.
    + (* both allocated *)
      Intros.
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROPx P (LOCALx (temp HRM._t'62 (Vint Int.zero) :: Q) (SEPx R))) end.
      * exfalso. auto.
      * forward. entailer!. destruct img; try contradiction; simpl; auto.
      * forward_if.
        { exfalso. apply H3'. reflexivity. }
        forward.
        rewrite (hrx5_k3a_mc Ews mc). Intros.
        unfold hrx5_K3_A, hrx5_K3_St.
        Exists R sec birth S w NS PS T head. Exists nk KE st i kc lul q proto.
        Exists ip4 ip6 port mc img (mkCM Int.zero Int.zero [] []).
        unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr, hrx5_K3_XA; cbn [app].
        entailer!.
Qed.

End K3A.
