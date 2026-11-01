(* law handshake_receive: main's phase PA = the setup of D and the harness's keys (statements 0..13).
   From hrx5_S0 to hrx5_SA (hrx5_defs.v; the cut: hrx5_cut.v). *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_PA_lem.
Require Import WgNoise.proof.libc.libc_bytes.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Section PA.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_PA_ok {Espec: OracleKind} gv L FR :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_S0 gv L FR) hrx5_PA
    (overridePost (hrx5_SA x25519 gv L FR) (hrx5_R gv)).
Proof.
  intros HH. unfold hrx5_S0, hrx5_Delta, hrx5_R, hrx5_PA. simplify_func_tycontext.
  abbreviate_semax.
  unfold hrx5_lvars, hrx5_scr, hrx5_rglobs; cbn [app].
  rewrite shim_state_ex4. Intros w.
  forward. forward. forward_call tt.
  Intros v.
  unfold shim_state4. rewrite (hrx5_pa_core_open gv hrx5_shim0). Intros.
  forward. gather_SEP 11 12 13. replace_SEP 0 (shim_state4 gv (hrx5_pa_set_boot hrx5_shim0 v) w).
  1: unfold shim_state4; rewrite hrx5_pa_core_open; entailer!; apply derives_refl.
  forward_call (gv, zeros32, zeros32, Int64.zero).
  rewrite !hrx5_conv_bytes.
  forward_call (l_rawd L, 32, Tsh). Intros bsd.
  forward_call (l_rawk L, 32, Tsh). Intros bsk.
  rewrite (hrx5_pa_nd Tsh 32 bsd) by tauto. rewrite (hrx5_pa_nd Tsh 32 bsk) by tauto.
  rewrite <- !hrx5_conv_bytes.
  forward_call (gv, hrx5_pa_set_boot hrx5_shim0 v, w, Tsh, l_wd L, l_itd L, l_ptd L, Tsh, l_rawd L,
                map Byte.repr bsd).
  { rewrite Zlength_map; tauto. }
  Intros sec0.
  unfold hrx5_consts. Intros.
  forward_call (gv, Tsh, l_id L, Tsh, l_rawd L, map Byte.repr bsd).
  1: rewrite Zlength_map; tauto.
  forward_call (gv, Tsh, l_ik L, Tsh, l_rawk L, map Byte.repr bsk).
  1: rewrite Zlength_map; tauto.
  set (R := mkRunR5 (map Byte.repr bsd) (map Byte.repr bsk)).
  change (mident_of x25519 (map Byte.repr bsd)) with (hrx5_ID x25519 R).
  change (mident_of x25519 (map Byte.repr bsk)) with (hrx5_IK x25519 R).
  assert (HID: Zlength (mi_pub (hrx5_ID x25519 R)) = 32) by (destruct HH as [Hx _]; apply Hx).
  assert (HIK: Zlength (mi_priv (hrx5_IK x25519 R)) = 32).
  { unfold hrx5_IK, mident_of; simpl. unfold clamp. list_solve. }
  sep_apply (hrx5_pa_mident_split Tsh (hrx5_ID x25519 R) (l_id L) HID).
  forward_call (Tsh, l_ssk L, Tsh, l_ik L, hrx5_IK x25519 R, Tsh, offset_val 32 (l_id L), mi_pub (hrx5_ID x25519 R)).
  1: cancel.
  unfold hrx5_pa_mrest. Intros. rewrite hrx5_pa_ok_cs. forward.
  rewrite <- hrx5_pa_ok_cs.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?S))) _ _ =>
    let S' := eval cbv beta iota delta [replace_nth] in (replace_nth 14 S (hbytes Tsh (hrx5_mk1 x25519 R) (l_mk1 L))) in
    forward_if (PROPx P (LOCALx Q (SEPx S'))) end.
  - pose proof H6 as H6'.
    change ((if mi_ok (hrx5_ID x25519 R) then Int.one else Int.repr 0) <> Int.zero) in H6'.
    destruct (mi_ok (hrx5_ID x25519 R)) eqn:Eok; [| contradiction H6'; reflexivity].
    unfold wg_consts. Intros.
    change (hc_const gv HRC._x_handshake_receive__M_LABEL_MAC1 mac1_label)
      with (hbytes Ers mac1_label (gv HRC._x_handshake_receive__M_LABEL_MAC1)).
    rewrite (hrx5_pa_ers_split (mi_pub (hrx5_ID x25519 R))). Intros.
    forward_call (gv, Tsh, l_mk1 L, Ers, gv HRC._x_handshake_receive__M_LABEL_MAC1, mac1_label,
                  offset_val 32 (l_id L), mi_pub (hrx5_ID x25519 R)).
    rewrite (hrx5_pa_mk1_ok x25519 R Eok).
    entailer!.
    rewrite (hrx5_pa_ers_split (mi_pub (hrx5_ID x25519 R))). unfold wg_consts. cancel. apply derives_refl.
  - pose proof H6 as H6'.
    change ((if mi_ok (hrx5_ID x25519 R) then Int.one else Int.repr 0) = Int.zero) in H6'.
    destruct (mi_ok (hrx5_ID x25519 R)) eqn:Eok; [discriminate |].
    forward_call (Tsh, l_mk1 L, Byte.zero, 32).
    rewrite (hrx5_pa_mk1_nok x25519 R Eok).
    entailer!.
  - set (DD := setup_dev x25519 (l_wd L) (l_itd L) (l_ptd L) (map Byte.repr bsd) sec0
                 (s_boot (hrx5_pa_set_boot hrx5_shim0 v))).
    rewrite (hrx5_pa_dev_split Tsh (l_wd L) DD).
    assert_PROP (@field_compatible Noise.CS t_dev [] (l_wd L)) as FCB by (unfold hrx5_pa_drest; entailer!).
    rewrite (hrx5_pa_cc_open Tsh (l_wd L)) by exact FCB. Intros.
    match goal with Hc: cc_ok (d_cc DD) |- _ => pose proof Hc as (Ls & Le & Lm) end.
    sep_apply (hrx5_pa_hbytes_free Tsh (cc_secret (d_cc DD)) (cc_addr (l_wd L))). rewrite Ls.
    forward_call (cc_addr (l_wd L), 32, Tsh). Intros bsS.
    match goal with H1: Zlength bsS = 32, H2: Forall _ bsS |- _ => rewrite (hrx5_pa_nd _ _ _ _ H1 H2) end.
    forward_call tt. Intros birth.
    forward.
    set (CC1 := mkChk (map Byte.repr bsS) (cc_ekey (d_cc DD)) (cc_mkey (d_cc DD)) birth (cc_dev (d_cc DD))).
    assert (HCC1: cc_ok CC1).
    { unfold CC1, cc_ok; simpl. rewrite Zlength_map. auto. }
    rewrite (hrx5_pa_ccrest_eq Tsh (cc_addr (l_wd L)) (d_cc DD) CC1) by reflexivity.
    change (hbytes Tsh (map Byte.repr bsS) (cc_addr (l_wd L))) with (hbytes Tsh (cc_secret CC1) (cc_addr (l_wd L))).
    change (Vlong birth) with (Vlong (cc_birth CC1)).
    sep_apply (hrx5_pa_cc_close Tsh (l_wd L) CC1 FCB HCC1).
    set (sec := map Byte.repr bsS) in *.
    set (D' := hrx5_D x25519 R (l_wd L) (l_itd L) (l_ptd L) sec birth).
    change (hrx5_pa_drest Tsh (l_wd L) DD) with (hrx5_pa_drest Tsh (l_wd L) D').
    change (checker_rep Tsh (cc_addr (l_wd L)) CC1) with (checker_rep Tsh (cc_addr (l_wd L)) (d_cc D')).
    sep_apply (derives_refl' _ _ (eq_sym (hrx5_pa_dev_split Tsh (l_wd L) D'))).
    pose proof (hrx5_pa_mident_join Tsh (hrx5_ID x25519 R) (l_id L) HID) as J. unfold hrx5_pa_mrest in J.
    sep_apply J. clear J.
    unfold hrx5_SA.
    Exists R sec birth (shim_draw (hrx5_pa_set_boot hrx5_shim0 v) sec0) w.
    unfold hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_rglobs, hrx5_scr, hrx5_lvars, hrx5_DL, hrx5_consts;
      cbn [app hrx5_head hrx5_khead s_boot shim_draw hrx5_pa_set_boot].
    change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with (Vlong Int64.zero).
    entailer!.
    { unfold hrx5_base_ok, hrx5_run_ok, sec; simpl. rewrite !Zlength_map. repeat split; auto; lia. }
    unfold hnodes_rep4, kents_rep; simpl; entailer!.
    apply derives_refl.
Qed.

End PA.
