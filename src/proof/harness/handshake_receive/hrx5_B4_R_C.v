(* law handshake_receive, B4 segment R, part C: the two copies into before (bytes_copy x2), then the rest of CALL. *)
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

Module hrx5_B4_R_Cm.
Section C.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Local Notation D4 := (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec).

Definition hrx5_B4_R_Lp gv L nk KE st i S lul m img n tw (p a: val) : list localdef :=
  temp HM._target p :: temp HM._e a :: temp HM._acc_resp (Vint Int.zero) :: hrx5_B4_R_Q gv L nk KE st i S lul m img n tw.

(* core: bytes_copy(before.ck, p->snap.chaining_key, 32) *)
Lemma hrx5_B4_R_cBC1 {Espec: OracleKind} gv L nk KE st i S lul m img n tw x a (ck: list byte) (F: mpred) Rr :
  Zlength ck = 32 -> isptr x ->
  semax D4 (PROPx [] (LOCALx (hrx5_B4_R_Lp gv L nk KE st i S lul m img n tw x a)
              (SEPx [F; hout Tsh 32 (l_before L); hbytes Ews ck (offset_val 248 x)])))
    hrx5_B4_R_bc1
    (overridePost (PROPx [] (LOCALx (hrx5_B4_R_Lp gv L nk KE st i S lul m img n tw x a)
              (SEPx [F; hbytes Tsh ck (l_before L); hbytes Ews ck (offset_val 248 x)]))) Rr).
Proof.
  intros Hl Hx.
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost].
  unfold hrx5_B4_R_Lp, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars, hrx5_Delta, hrx5_B4_R_bc1. cbn [app].
  simplify_func_tycontext.
  forward_call (Tsh, l_before L, Ews, offset_val 248 x, ck).
  2: { rewrite Hl. cancel. }
  { entailer!. rewrite Hl. simpl. rewrite offset_offset_val, isptr_offset_val_zero by auto. reflexivity. }
  entailer!.
Qed.

(* core: bytes_copy(before.h, p->snap.hash, 32) *)
Lemma hrx5_B4_R_cBC2 {Espec: OracleKind} gv L nk KE st i S lul m img n tw x a (h: list byte) (F: mpred) Rr :
  Zlength h = 32 -> isptr x ->
  semax D4 (PROPx [] (LOCALx (hrx5_B4_R_Lp gv L nk KE st i S lul m img n tw x a)
              (SEPx [F; hout Tsh 32 (offset_val 32 (l_before L)); hbytes Ews h (offset_val 216 x)])))
    hrx5_B4_R_bc2
    (overridePost (PROPx [] (LOCALx (hrx5_B4_R_Lp gv L nk KE st i S lul m img n tw x a)
              (SEPx [F; hbytes Tsh h (offset_val 32 (l_before L)); hbytes Ews h (offset_val 216 x)]))) Rr).
Proof.
  intros Hl Hx.
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost].
  unfold hrx5_B4_R_Lp, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars, hrx5_Delta, hrx5_B4_R_bc2. cbn [app].
  simplify_func_tycontext.
  forward_call (Tsh, offset_val 32 (l_before L), Ews, offset_val 216 x, h).
  2: { rewrite Hl. cancel. }
  { entailer!. rewrite Hl. simpl. rewrite offset_offset_val. reflexivity. }
  entailer!.
Qed.

(* wrapper: the two copies into before, then the rest of CALL *)
Lemma hrx5_B4_R_LBC {Espec: OracleKind} gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX a E NSa N0 NSb P rest Rr :
  NSs = NSa ++ N0 :: NSb -> isptr (hn_addr N0) -> hs_ok (p_hs P) ->
  hn_snap N0 = hsnap_val (hs_snap_cur T (e_peer E) P) ->
  hrx5_head NSs = hrx5_head NS ->
  semax D4 (hrx5_B4_R_A6 gv L nk KE st i S lul m img n tw IA NS NSs T M FX a (hn_addr N0) (hs_ck (p_hs P)) (hs_hash (p_hs P)))
    rest (overridePost (hrx5_B4_R_OUT x25519 aead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX) Rr) ->
  semax D4 (hrx5_B4_R_A4 gv L nk KE st i S lul m img n tw IA NS NSs T M FX a (hn_addr N0))
    (Ssequence hrx5_B4_R_bc1 (Ssequence hrx5_B4_R_bc2 rest))
    (overridePost (hrx5_B4_R_OUT x25519 aead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX) Rr).
Proof.
  intros HNS0 HpA0 HhsP HsnN0 HsH Hrest.
  destruct hrx5_B4_R_sep_ok as (_ & _ & _ & _ & _ & _ & Sms1 & Sms2 & _).
  pose proof HhsP as (HlE & _ & _ & _ & HlPsk & HlH & HlCk & _).
  unfold hrx5_B4_R_A4, hrx5_B4_R_R, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars; cbn [app].
  rewrite <- HsH. sep_apply (hrx5_B4_R_open NSs NSa N0 NSb HNS0). Intros.
  sep_apply (hrx5_B4_R_fields T N0 (hrx5_head NSb) (e_peer E) P HsnN0 HhsP).
  sep_apply (Sms1 Tsh (l_before L)). Intros.
  hrx5_B4_R_keep [hout Tsh 32 (l_before L); hbytes Ews (hs_ck (p_hs P)) (offset_val 248 (hn_addr N0))] FZ.
  eapply semax_seq.
  { eapply semax_pre; [| apply (hrx5_B4_R_cBC1 gv L nk KE st i S lul m img n tw (hn_addr N0) a (hs_ck (p_hs P)) (FRZL FZ)); assumption].
    unfold hrx5_B4_R_Lp, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars; cbn [app]. entailer!. }
  unfold hrx5_B4_R_Lp, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars; cbn [app]. thaw FZ.
  hrx5_B4_R_keep [hout Tsh 32 (offset_val 32 (l_before L)); hbytes Ews (hs_hash (p_hs P)) (offset_val 216 (hn_addr N0))] FZ2.
  eapply semax_seq.
  { eapply semax_pre; [| apply (hrx5_B4_R_cBC2 gv L nk KE st i S lul m img n tw (hn_addr N0) a (hs_hash (p_hs P)) (FRZL FZ2)); assumption].
    unfold hrx5_B4_R_Lp, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars; cbn [app]. entailer!. }
  unfold hrx5_B4_R_Lp, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars; cbn [app]. thaw FZ2.
  sep_apply (Sms2 Tsh (hs_ck (p_hs P)) (hs_hash (p_hs P)) (l_before L) ltac:(assumption) HlCk HlH).
  sep_apply (hrx5_B4_R_unfields N0 (hrx5_head NSb) (p_hs P)).
  sep_apply (hrx5_B4_R_wand1 (hrx5_B4_R_nodeA N0 (hrx5_head NSb)) (hnodes_rep4 W (hrx5_head NSs) NSs)).
  rewrite HsH.
  eapply semax_pre; [| exact Hrest].
  unfold hrx5_B4_R_A6, hrx5_B4_R_Lp, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars; cbn [app]. entailer!.
Qed.

End C.
End hrx5_B4_R_Cm.

Lemma hrx5_B4_R_C_ok : hrx5_B4_R_C_stmt.
Proof.
  unfold hrx5_B4_R_C_stmt. intros. eapply hrx5_B4_R_Cm.hrx5_B4_R_LBC; eassumption.
Qed.
