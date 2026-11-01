(* law handshake_receive, B4 segment R, part W: the table walk
   e = itd.head; for (; e && e->index != mr->receiver_index; e = e->next);  (port of hcr5_q3_Lwalk) *)
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
#[local] Existing Instance W_handshake_receive.
#[local] Existing Instance W_handshake_receive.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_R_pure.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_R_sep.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_R_defs.
Local Open Scope logic.

Section W.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Local Notation D4 := (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec).

(* ---- the table walk: for (; e && e->index != msg->receiver_index; e = e->next); ---- *)
Definition hrx5_B4_R_WI gv L nk KE st i S lul m img n tw T M (F: mpred) (L1 L2: list val) : environ -> mpred :=
  PROPx [t_L T = L1 ++ L2; t_find_index T L1 (rm_receiver M) = None]
  (LOCALx (temp HM._e (hd nullval L2) :: temp HM._acc_resp (Vint Int.zero) :: temp HM._target nullval :: hrx5_B4_R_Q gv L nk KE st i S lul m img n tw)
  (SEPx [@data_at W Ews t_resp (resp_val M) m; iter_sepcon (pool_item_rep (t_L T)) (t_D T); F])).
Definition hrx5_B4_R_WC gv L nk KE st i S lul m img n tw T M (F: mpred) (L1: list val) (a: val) (L2: list val) : environ -> mpred :=
  PROPx [t_L T = L1 ++ a :: L2; t_find_index T (L1 ++ [a]) (rm_receiver M) = None]
  (LOCALx (temp HM._e a :: temp HM._acc_resp (Vint Int.zero) :: temp HM._target nullval :: hrx5_B4_R_Q gv L nk KE st i S lul m img n tw)
  (SEPx [@data_at W Ews t_resp (resp_val M) m; iter_sepcon (pool_item_rep (t_L T)) (t_D T); F])).
Definition hrx5_B4_R_WB gv L nk KE st i S lul m img n tw T M (F: mpred) : environ -> mpred :=
  PROPx []
  (LOCALx (temp HM._e (hrx5_B4_R_ef T (rm_receiver M)) :: temp HM._acc_resp (Vint Int.zero) :: temp HM._target nullval :: hrx5_B4_R_Q gv L nk KE st i S lul m img n tw)
  (SEPx [@data_at W Ews t_resp (resp_val M) m; iter_sepcon (pool_item_rep (t_L T)) (t_D T); F])).
Definition hrx5_B4_R_WIx gv L nk KE st i S lul m img n tw T M (F: mpred) : environ -> mpred :=
  EX L1: list val, EX L2: list val, hrx5_B4_R_WI gv L nk KE st i S lul m img n tw T M F L1 L2.
Definition hrx5_B4_R_WCx gv L nk KE st i S lul m img n tw T M (F: mpred) : environ -> mpred :=
  EX L1: list val, EX a: val, EX L2: list val, hrx5_B4_R_WC gv L nk KE st i S lul m img n tw T M F L1 a L2.

Lemma hrx5_B4_R_Lb_nil {Espec: OracleKind} gv L nk KE st i S lul m img n tw T M F L1 Rr :
  semax D4 (hrx5_B4_R_WI gv L nk KE st i S lul m img n tw T M F L1 []) hrx5_B4_R_B1
    (loop1_ret_assert (hrx5_B4_R_WCx gv L nk KE st i S lul m img n tw T M F) (overridePost (hrx5_B4_R_WB gv L nk KE st i S lul m img n tw T M F) Rr)).
Proof.
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost loop1_ret_assert].
  unfold hrx5_B4_R_WI, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars, hrx5_Delta, hrx5_B4_R_B1. cbn [app hd]. simplify_func_tycontext.
  Intros.
  lazymatch goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?Rs))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HM._t'83 (Vint Int.zero) :: Q) (SEPx Rs))) end.
  { exfalso. congruence. }
  { forward. entailer!. }
  forward_if; [exfalso; congruence |].
  forward.
  unfold hrx5_B4_R_WB, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars. cbn [app]. entailer!. unfold hrx5_B4_R_ef.
  match goal with Hl: t_L T = L1 ++ [], Hf: t_find_index T L1 _ = None |- _ =>
    rewrite Hl, app_nil_r, Hf end. reflexivity.
Qed.

Lemma hrx5_B4_R_Lb_cons {Espec: OracleKind} gv L nk KE st i S lul m img n tw T M F L1 a L2 Rr :
  itable_wf T -> (forall a, In a (t_L T) -> isptr a) ->
  semax D4 (hrx5_B4_R_WI gv L nk KE st i S lul m img n tw T M F L1 (a :: L2)) hrx5_B4_R_B1
    (loop1_ret_assert (hrx5_B4_R_WCx gv L nk KE st i S lul m img n tw T M F) (overridePost (hrx5_B4_R_WB gv L nk KE st i S lul m img n tw T M F) Rr)).
Proof.
  intros Hwf HLp. destruct Hwf as (HwL & HwI & HwD & HwS).
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost loop1_ret_assert].
  unfold hrx5_B4_R_WI, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars, hrx5_Delta, hrx5_B4_R_B1. cbn [app hd]. simplify_func_tycontext.
  Intros.
  assert (Ha: In a (t_L T)).
  { match goal with Hl: t_L T = L1 ++ a :: L2 |- _ => rewrite Hl end. apply in_or_app; right; left; reflexivity. }
  destruct (hrx5_B4_R_focus2 (t_L T) (t_D T) a (HwI _ Ha) HwD HwS) as (sh & E & Rst & Hrd & Hsf & Heq).
  rewrite Heq. Intros.
  lazymatch goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?Rs))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HM._t'83 (Vint (if Int.eq (e_index E) (rm_receiver M) then Int.zero else Int.one)) :: Q) (SEPx Rs))) end.
  { forward. forward. forward. entailer!. destruct (Int.eq (e_index E) (rm_receiver M)); reflexivity. }
  { exfalso. specialize (HLp a Ha). destruct a; try contradiction. discriminate. }
  gather_SEP (data_at sh t_entry_s _ a) Rst. rewrite <- Heq.
  assert (Hfa: t_find_index T (L1 ++ [a]) (rm_receiver M) =
               if Int.eq (e_index E) (rm_receiver M) then Some (a, E) else None).
  { match goal with Hf: t_find_index T L1 _ = None |- _ => rewrite hrx5_B4_R_find_app, Hf end.
    simpl. unfold t_entry. rewrite Hsf. destruct (Int.eq (e_index E) (rm_receiver M)); reflexivity. }
  forward_if.
  - forward.
    unfold hrx5_B4_R_WCx, hrx5_B4_R_WC, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars. cbn [app]. Exists L1 a L2. entailer!.
    rewrite Hfa. destruct (Int.eq (e_index E) (rm_receiver M)); [exfalso | reflexivity].
    match goal with Hn: Int.repr 0 <> Int.zero |- _ => apply Hn; reflexivity end.
  - forward.
    unfold hrx5_B4_R_WB, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars. cbn [app]. entailer!. unfold hrx5_B4_R_ef.
    match goal with Hl: t_L T = L1 ++ a :: L2, Hf: t_find_index T L1 _ = None |- _ =>
      rewrite Hl, hrx5_B4_R_find_app, Hf end.
    simpl. unfold t_entry. rewrite Hsf.
    destruct (Int.eq (e_index E) (rm_receiver M)); [reflexivity | exfalso].
    match goal with Hn: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hn) end.
Qed.

Lemma hrx5_B4_R_Li {Espec: OracleKind} gv L nk KE st i S lul m img n tw T M F L1 a L2 Rr :
  itable_wf T -> (forall a, In a (t_L T) -> isptr a) ->
  semax D4 (hrx5_B4_R_WC gv L nk KE st i S lul m img n tw T M F L1 a L2) hrx5_B4_R_I1
    (loop2_ret_assert (hrx5_B4_R_WIx gv L nk KE st i S lul m img n tw T M F) (overridePost (hrx5_B4_R_WB gv L nk KE st i S lul m img n tw T M F) Rr)).
Proof.
  intros Hwf HLp. destruct Hwf as (HwL & HwI & HwD & HwS).
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost loop2_ret_assert].
  unfold hrx5_B4_R_WC, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars, hrx5_Delta, hrx5_B4_R_I1. cbn [app]. simplify_func_tycontext.
  Intros.
  assert (Ha: In a (t_L T)).
  { match goal with Hl: t_L T = L1 ++ a :: L2 |- _ => rewrite Hl end. apply in_or_app; right; left; reflexivity. }
  destruct (hrx5_B4_R_focus2 (t_L T) (t_D T) a (HwI _ Ha) HwD HwS) as (sh & E & Rst & Hrd & Hsf & Heq).
  rewrite Heq. Intros. forward.
  { entailer!. unfold entry_val. apply hrx5_B4_R_succ_pn; auto. }
  gather_SEP (data_at sh t_entry_s _ a) Rst. rewrite <- Heq.
  unfold hrx5_B4_R_WIx, hrx5_B4_R_WI, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars. cbn [app].
  Exists (L1 ++ [a]) L2. entailer!.
  match goal with Hl: t_L T = L1 ++ a :: L2 |- _ => rename Hl into HL1 end. split.
  - rewrite HL1, <- app_assoc. reflexivity.
  - rewrite hrx5_B4_R_entry_next. rewrite HL1 in HwL |- *. symmetry. apply hrx5_B4_R_succ_mid; auto.
Qed.

Lemma hrx5_B4_R_Lloop {Espec: OracleKind} gv L nk KE st i S lul m img n tw T M F Rr :
  itable_wf T -> (forall a, In a (t_L T) -> isptr a) ->
  semax D4 (hrx5_B4_R_WI gv L nk KE st i S lul m img n tw T M F [] (t_L T)) (Sloop hrx5_B4_R_B1 hrx5_B4_R_I1)
    (overridePost (hrx5_B4_R_WB gv L nk KE st i S lul m img n tw T M F) Rr).
Proof.
  intros Hwf HLp.
  eapply semax_pre with (P' := hrx5_B4_R_WIx gv L nk KE st i S lul m img n tw T M F).
  { unfold hrx5_B4_R_WIx. apply andp_left2. Exists (@nil val) (t_L T). apply derives_refl. }
  apply semax_loop with (Q' := hrx5_B4_R_WCx gv L nk KE st i S lul m img n tw T M F).
  - unfold hrx5_B4_R_WIx at 1. apply semax_extract_exists; intro L1. apply semax_extract_exists; intro L2.
    destruct L2 as [| a L2]; [apply hrx5_B4_R_Lb_nil | apply hrx5_B4_R_Lb_cons; assumption].
  - unfold hrx5_B4_R_WCx at 1. apply semax_extract_exists; intro L1. apply semax_extract_exists; intro a.
    apply semax_extract_exists; intro L2. apply hrx5_B4_R_Li; assumption.
Qed.

(* e = ita.head; for (; e && e->index != msg->receiver_index; e = e->next); *)
Lemma hrx5_B4_R_Lwalk {Espec: OracleKind} gv L nk KE st i S lul m img n tw IA NS NSs T M FX Rr :
  semax D4 (hrx5_B4_R_A0 gv L nk KE st i S lul m img n tw IA NS NSs T M FX)
    (Ssequence hrx5_B4_R_se (Sloop hrx5_B4_R_B1 hrx5_B4_R_I1))
    (overridePost (hrx5_B4_R_A1 gv L nk KE st i S lul m img n tw IA NS NSs T M FX) Rr).
Proof.
  unfold hrx5_B4_R_A0, hrx5_B4_R_R, hrx5_B4_R_Q, hrx5_ltemps, hrx5_Delta, hrx5_B4_R_se.
  simplify_func_tycontext. unfold hrx5_lvars; cbn [app].
  unfold itable, resp_rep. Intros. rewrite hrx5_B4_R_conv_itab, hrx5_B4_R_conv_resp.
  match goal with Hw: itable_wf T |- _ => pose proof Hw as Hwf; destruct Hw as (HwL & HwI & HwD & HwS) end.
  assert_PROP (Forall isptr (saddrs (t_D T))) as Hptr. { sep_apply (hrx5_B4_R_ptrs (t_L T) (t_D T)). entailer!. }
  assert (HLp: forall a, In a (t_L T) -> isptr a).
  { intros a Ha. rewrite Forall_forall in Hptr. apply Hptr, HwI, Ha. }
  forward.
  { entailer!. destruct (t_L T) as [| a0 L'] eqn:HL; simpl; auto.
    specialize (HLp a0 (or_introl eq_refl)). destruct a0; try contradiction; simpl; auto. }
  freeze FZ := - (data_at _ t_resp _ m) (iter_sepcon _ _).
  eapply semax_pre; [| eapply hrx5_B4_R_post; [| apply (hrx5_B4_R_Lloop gv L nk KE st i S lul m img n tw T M (FRZL FZ)); assumption]].
  - unfold hrx5_B4_R_WI, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars; cbn [app hd]. entailer!.
  - unfold hrx5_B4_R_WB, hrx5_B4_R_A1, hrx5_B4_R_R, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars; cbn [app].
    thaw FZ. rewrite <- hrx5_B4_R_conv_resp, <- hrx5_B4_R_conv_itab. unfold itable, resp_rep.
    entailer!.
Qed.

End W.

Lemma hrx5_B4_R_W_ok : hrx5_B4_R_W_stmt.
Proof.
  intros Espec x25519 aead_dec xaead_enc xaead_dec gv L nk KE st i S lul m img n tw IA NS NSs T M FX Rr.
  apply hrx5_B4_R_Lwalk.
Qed.
