(* law handshake_receive, B4 segment R, part E: the entry test if (e != NULL && e->type == INDEX_HASHTABLE_HANDSHAKE) HS. *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_R_pure.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_R_sep.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_R_defs.
Local Open Scope logic.

Module hrx5_B4_R_Em.
Section E.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Local Notation D4 := (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec).

(* ---- if (e != NULL && e->type == INDEX_HASHTABLE_HANDSHAKE) HS ---- *)
(* not found *)
Lemma hrx5_B4_R_Lnf {Espec: OracleKind} gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX Rr :
  mi_ok IA = true -> t_find_index T (t_L T) (rm_receiver M) = None ->
  semax D4 (hrx5_B4_R_A1 gv L nk KE st i S lul m img n tw IA NS NSs T M FX)
    (Ssequence hrx5_B4_R_if86 (Sifthenelse hrx5_B4_R_c86 hrx5_B4_R_HS Sskip))
    (overridePost (hrx5_B4_R_OUT x25519 aead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX) Rr).
Proof.
  intros Hok Hfind.
  assert (Htg: hrx5cr_tgt x25519 aead_dec IA T PS M = None) by (unfold hrx5cr_tgt; rewrite Hok, Hfind; reflexivity).
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost].
  unfold hrx5_B4_R_A1, hrx5_B4_R_ef. rewrite Hfind.
  unfold hrx5_B4_R_R, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars, hrx5_Delta, hrx5_B4_R_if86, hrx5_B4_R_c86. cbn [app]. simplify_func_tycontext.
  lazymatch goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?Rs))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HM._t'86 (Vint Int.zero) :: Q) (SEPx Rs))) end.
  { exfalso. discriminate. }
  { forward. entailer!. }
  forward_if; [exfalso; congruence |].
  forward.
  unfold hrx5_B4_R_OUT, hrx5_B4_R_R, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars. Exists nullval 0.
  unfold hrx5_B4_R_acc, hrx5_B4_R_strep. rewrite Htg. cbn [app].
  entailer!. all: auto.
Qed.

(* found, not a handshake entry *)
Lemma hrx5_B4_R_Lnhs {Espec: OracleKind} gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX Rr a E :
  mi_ok IA = true -> t_find_index T (t_L T) (rm_receiver M) = Some (a, E) ->
  Int.eq (e_type E) IDX_HANDSHAKE = false ->
  semax D4 (hrx5_B4_R_A1 gv L nk KE st i S lul m img n tw IA NS NSs T M FX)
    (Ssequence hrx5_B4_R_if86 (Sifthenelse hrx5_B4_R_c86 hrx5_B4_R_HS Sskip))
    (overridePost (hrx5_B4_R_OUT x25519 aead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX) Rr).
Proof.
  intros Hok Hfind Hty.
  assert (Htg: hrx5cr_tgt x25519 aead_dec IA T PS M = None)
    by (unfold hrx5cr_tgt; rewrite Hok, Hfind, Hty; reflexivity).
  destruct hrx5_B4_R_pure_ok as (Pfind & _).
  destruct (Pfind T (t_L T) (rm_receiver M) a E Hfind) as [Ha HtE].
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost].
  unfold hrx5_B4_R_A1, hrx5_B4_R_ef. rewrite Hfind.
  unfold hrx5_B4_R_R, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars, hrx5_Delta, hrx5_B4_R_if86, hrx5_B4_R_c86. cbn [app]. simplify_func_tycontext.
  unfold itable. Intros.
  match goal with Hw: itable_wf T |- _ => pose proof Hw as Hwf; destruct Hw as (HwL & HwI & HwD & HwS) end.
  assert_PROP (Forall isptr (saddrs (t_D T))) as Hptr. { sep_apply (hrx5_B4_R_ptrs (t_L T) (t_D T)). entailer!. }
  destruct (hrx5_B4_R_focus2 (t_L T) (t_D T) a (HwI _ Ha) HwD HwS) as (sh & E' & Rst & Hrd & Hsf & Heq).
  assert (E' = E) as ->. { unfold t_entry in HtE. rewrite Hsf in HtE. congruence. }
  rewrite Heq. Intros.
  lazymatch goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?Rs))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HM._t'86 (Vint (if Int.eq (e_type E) IDX_HANDSHAKE then Int.one else Int.zero)) :: Q) (SEPx Rs))) end.
  { forward. forward. entailer!. unfold IDX_HANDSHAKE. destruct (Int.eq (e_type E) (Int.repr 1)); reflexivity. }
  { exfalso. rewrite Forall_forall in Hptr. specialize (Hptr a (HwI _ Ha)). destruct a; try contradiction. discriminate. }
  gather_SEP (data_at sh t_entry_s _ a) Rst. rewrite <- Heq. rewrite Hty.
  forward_if; [exfalso; congruence |].
  forward.
  unfold hrx5_B4_R_OUT, hrx5_B4_R_R, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars, itable. Exists nullval 0.
  unfold hrx5_B4_R_acc, hrx5_B4_R_strep. rewrite Htg. cbn [app].
  entailer!. all: auto.
Qed.

(* found, a handshake entry: HS *)
Lemma hrx5_B4_R_Lhs {Espec: OracleKind} gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX Rr a E :
  t_find_index T (t_L T) (rm_receiver M) = Some (a, E) ->
  Int.eq (e_type E) IDX_HANDSHAKE = true ->
  semax D4 (hrx5_B4_R_A3 gv L nk KE st i S lul m img n tw IA NS NSs T M FX a) hrx5_B4_R_HS
    (overridePost (hrx5_B4_R_OUT x25519 aead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX) Rr) ->
  semax D4 (hrx5_B4_R_A1 gv L nk KE st i S lul m img n tw IA NS NSs T M FX)
    (Ssequence hrx5_B4_R_if86 (Sifthenelse hrx5_B4_R_c86 hrx5_B4_R_HS Sskip))
    (overridePost (hrx5_B4_R_OUT x25519 aead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX) Rr).
Proof.
  intros Hfind Hty HHS.
  destruct hrx5_B4_R_pure_ok as (Pfind & _).
  destruct (Pfind T (t_L T) (rm_receiver M) a E Hfind) as [Ha HtE].
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost] in HHS |- *.
  unfold hrx5_B4_R_A1, hrx5_B4_R_ef. rewrite Hfind.
  unfold hrx5_B4_R_R, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars, hrx5_Delta, hrx5_B4_R_if86, hrx5_B4_R_c86. cbn [app].
  unfold hrx5_Delta in HHS. simplify_func_tycontext.
  unfold itable. Intros.
  match goal with Hw: itable_wf T |- _ => pose proof Hw as Hwf; destruct Hw as (HwL & HwI & HwD & HwS) end.
  assert_PROP (Forall isptr (saddrs (t_D T))) as Hptr. { sep_apply (hrx5_B4_R_ptrs (t_L T) (t_D T)). entailer!. }
  destruct (hrx5_B4_R_focus2 (t_L T) (t_D T) a (HwI _ Ha) HwD HwS) as (sh & E' & Rst & Hrd & Hsf & Heq).
  assert (E' = E) as ->. { unfold t_entry in HtE. rewrite Hsf in HtE. congruence. }
  rewrite Heq. Intros.
  lazymatch goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?Rs))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HM._t'86 (Vint (if Int.eq (e_type E) IDX_HANDSHAKE then Int.one else Int.zero)) :: Q) (SEPx Rs))) end.
  { forward. forward. entailer!. unfold IDX_HANDSHAKE. destruct (Int.eq (e_type E) (Int.repr 1)); reflexivity. }
  { exfalso. rewrite Forall_forall in Hptr. specialize (Hptr a (HwI _ Ha)). destruct a; try contradiction. discriminate. }
  gather_SEP (data_at sh t_entry_s _ a) Rst. rewrite <- Heq. rewrite Hty.
  forward_if.
  2: { exfalso. match goal with Hc: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
  eapply semax_pre; [| exact HHS].
  unfold hrx5_B4_R_A3, hrx5_B4_R_R, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars, itable; cbn [app].
  entailer!.
Qed.

End E.
End hrx5_B4_R_Em.

Lemma hrx5_B4_R_E_ok : hrx5_B4_R_E_stmt.
Proof.
  unfold hrx5_B4_R_E_stmt. intros. split; [| split]; intros.
  - eapply hrx5_B4_R_Em.hrx5_B4_R_Lnf; eassumption.
  - eapply hrx5_B4_R_Em.hrx5_B4_R_Lnhs; eassumption.
  - eapply hrx5_B4_R_Em.hrx5_B4_R_Lhs; eassumption.
Qed.
