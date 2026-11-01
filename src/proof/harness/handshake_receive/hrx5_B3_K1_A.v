(* law handshake_receive, B3 kind 1: segment A (hrx5_B3_K1_defs.v). *)
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

Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K1_defs.
Local Open Scope logic.

Ltac k1a_sc R sec birth S w NS PS T head nk KE st i kc lul H H0 H1 :=
  unfold hrx5_SC, hrx5_SLc;
  Exists R sec birth S w NS PS T head; Exists nk KE st i kc lul;
  unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr, hrx5_rglobs, hrx5_skb0; cbn [app];
  unfold hrx5_skb_part, qlen_rep; Intros dv lv;
  go_lower;
  apply andp_right;
    [apply prop_right; refine (conj H (conj H0 (conj H1 _))); repeat split; auto; try lia;
     try (rewrite eqb_type_refl; reflexivity) |];
  sep_apply (@data_at_data_at_ HRX Ews tint);
  sep_apply (@data_at_data_at_ Cookie.CS Tsh t_skb);
  cancel.

Section K1A.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_K1_A_ok {Espec: OracleKind} gv L FR :
  hrx5_B3_lem_stmt x25519 ->
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B3_P x25519 1 gv L FR) hrx5_K1_SA
    (overridePost (hrx5_K1_A x25519 gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HLEM HY. unfold hrx5_Delta, hrx5_B3_P.
  Intros R sec birth S w NS PS T head. Intros nk KE st i kc lul q proto. Intros ip4 ip6 port.
  unfold hrx5_K1_SA, hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app].
  unfold hrx5_RB, hrx5_R.
  abbreviate_semax.
  forward_call (t_init, gv). Intros mi.
  forward_call (tarray tuchar 148, gv). { simpl. rep_lia. } Intros img.
  destruct (eq_dec mi nullval) as [Hmi|Hmi].
  - (* mi == NULL: free both, continue *)
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HRM._t'50 (Vint Int.one) :: Q) (SEPx R))) end.
    + forward. entailer!.
    + subst mi. exfalso. auto.
    + forward_if.
      2: { exfalso. revert H3; vm_compute; discriminate. }
      forward_call (t_init, mi, gv). { destruct (eq_dec mi nullval); [|contradiction]. cancel. }
      forward_call (tarray tuchar 148, img, gv).
      forward.
      k1a_sc R sec birth S w NS PS T head nk KE st i kc lul H H0 H1.
  - destruct (eq_dec mi nullval); [contradiction|].
    destruct (eq_dec img nullval) as [Himg|Himg].
    + (* img == NULL: free both, continue *)
      Intros.
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROPx P (LOCALx (temp HRM._t'50 (Vint Int.one) :: Q) (SEPx R))) end.
      * contradiction.
      * forward. entailer!.
      * forward_if.
        2: { exfalso. revert H3; vm_compute; discriminate. }
        forward_call (t_init, mi, gv). { destruct (eq_dec mi nullval); [contradiction|]. cancel. }
        forward_call (tarray tuchar 148, img, gv). { destruct (eq_dec img nullval); [|contradiction]. cancel. }
        forward.
        k1a_sc R sec birth S w NS PS T head nk KE st i kc lul H H0 H1.
    + destruct (eq_dec img nullval); [contradiction|].
      Intros.
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROPx P (LOCALx (temp HRM._t'50 (Vint Int.zero) :: Q) (SEPx R))) end.
      * contradiction.
      * forward. entailer!.
        match goal with Hf: field_compatible (tarray tuchar 148) [] img |- _ =>
          apply field_compatible_isptr in Hf end.
        destruct img; try contradiction. reflexivity.
      * forward_if.
        { exfalso; match goal with Hz: ?a <> ?a |- _ => apply Hz; reflexivity end. }
        forward.
        assert_PROP (malloc_compatible 148 mi) as Hmc.
        { go_lower. sep_apply (malloc_token_local_facts Ews t_init mi). Intros. apply prop_right. assumption. }
        unfold hrx5_K1_A, hrx5_K1_St.
        Exists R sec birth S w NS PS T head. Exists nk KE st i kc lul q proto.
        Exists ip4 ip6 port mi img. Exists (mkIM Int.zero Int.zero [] [] [] [] []) (@nil byte).
        unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr, hrx5_K1_XA; cbn [app].
        go_lower.
        apply andp_right;
          [apply prop_right; refine (conj H (conj H0 (conj H1 (conj H2 _)))); repeat split; auto; try lia;
           try (rewrite eqb_type_refl; reflexivity) |].
        cancel.
Qed.

End K1A.
