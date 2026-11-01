(* law handshake_receive, B4 segment R, part K: the state test if (target != NULL && target->snap.state == HANDSHAKE_CREATED_INITIATION) CALL. *)
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

Module hrx5_B4_R_Km.
Section K.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Local Notation D4 := (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec).

Definition hrx5_B4_R_Lp gv L nk KE st i S lul m img n tw (p a: val) : list localdef :=
  temp HM._target p :: temp HM._e a :: temp HM._acc_resp (Vint Int.zero) :: hrx5_B4_R_Q gv L nk KE st i S lul m img n tw.

(* core: if (p != NULL) { t'87 = p->snap.state; t'23 = t'87 == 1; } else t'23 = 0; *)
Lemma hrx5_B4_R_k23v {Espec: OracleKind} gv L nk KE st i S lul m img n tw x a pp sn r (rs: @reptype CKS t_prsnap) nx F Rr :
  isptr x ->
  semax D4 (PROPx [] (LOCALx (hrx5_B4_R_Lp gv L nk KE st i S lul m img n tw x a)
              (SEPx [F; @data_at W Ews t_hnode4 (pp, (hsnap_val sn, (r, (rs, nx)))) x])))
    hrx5_B4_R_if85
    (overridePost (PROPx [] (LOCALx (temp HM._t'85 (Vint (if Int.eq (hs_state (sn_hs sn)) HS_CREATED_INITIATION
                                                          then Int.one else Int.zero)) ::
                                     hrx5_B4_R_Lp gv L nk KE st i S lul m img n tw x a)
              (SEPx [F; @data_at W Ews t_hnode4 (pp, (hsnap_val sn, (r, (rs, nx)))) x]))) Rr).
Proof.
  intros Hx. destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost].
  unfold hrx5_B4_R_Lp, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars, hrx5_Delta, hrx5_B4_R_if85. cbn [app]. simplify_func_tycontext.
  forward_if.
  { forward. forward. entailer!.
    all: unfold HS_CREATED_INITIATION; destruct (Int.eq (hs_state (sn_hs sn)) (Int.repr 1)); reflexivity. }
  { exfalso. first [ match goal with Hc: x = nullval |- _ => rewrite Hc in Hx; exact Hx end | exact Hx ]. }
Qed.

(* the node atom with a known snapshot (hn_snap is typed in HNS, hsnap_val in HCS: rewriting one into the
   other inside a Floyd proof costs a 3 s kernel conversion per occurrence; here it is done once) *)
Lemma hrx5_B4_R_nodeA_eq N nx sn : hn_snap N = hsnap_val sn ->
  hrx5_B4_R_nodeA N nx = @data_at W Ews t_hnode4 (hn_p N, (hsnap_val sn, (hn_refs N, (hn_rest N, nx)))) (hn_addr N).
Proof. intros Hs. unfold hrx5_B4_R_nodeA. rewrite Hs. reflexivity. Qed.

Lemma hrx5_B4_R_k23 {Espec: OracleKind} gv L nk KE st i S lul m img n tw a N nx sn F Rr :
  isptr (hn_addr N) -> hn_snap N = hsnap_val sn ->
  semax D4 (PROPx [] (LOCALx (hrx5_B4_R_Lp gv L nk KE st i S lul m img n tw (hn_addr N) a) (SEPx [F; hrx5_B4_R_nodeA N nx])))
    hrx5_B4_R_if85
    (overridePost (PROPx [] (LOCALx (temp HM._t'85 (Vint (if Int.eq (hs_state (sn_hs sn)) HS_CREATED_INITIATION
                                                          then Int.one else Int.zero)) ::
                                     hrx5_B4_R_Lp gv L nk KE st i S lul m img n tw (hn_addr N) a)
              (SEPx [F; hrx5_B4_R_nodeA N nx]))) Rr).
Proof.
  intros Hx Hs. rewrite (hrx5_B4_R_nodeA_eq N nx sn Hs). apply hrx5_B4_R_k23v. exact Hx.
Qed.

(* wrapper: if23 on the node of the entry's peer *)
Lemma hrx5_B4_R_L23 {Espec: OracleKind} gv L nk KE st i S lul m img n tw IA NS NSs T M FX a E NSa N0 NSb P Rr :
  NSs = NSa ++ N0 :: NSb -> isptr (hn_addr N0) ->
  hn_snap N0 = hsnap_val (hs_snap_cur T (e_peer E) P) ->
  hrx5_head NSs = hrx5_head NS ->
  semax D4 (hrx5_B4_R_A4 gv L nk KE st i S lul m img n tw IA NS NSs T M FX a (hn_addr N0)) hrx5_B4_R_if85
    (overridePost (hrx5_B4_R_A7 gv L nk KE st i S lul m img n tw IA NS NSs T M FX a (hn_addr N0)
       (if Int.eq (hs_state (p_hs P)) HS_CREATED_INITIATION then Int.one else Int.zero)) Rr).
Proof.
  intros HNS0 HpA0 HsnN0 HsH.
  unfold hrx5_B4_R_A4, hrx5_B4_R_R, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars; cbn [app].
  rewrite <- HsH. sep_apply (hrx5_B4_R_open NSs NSa N0 NSb HNS0). Intros.
  hrx5_B4_R_keep [hrx5_B4_R_nodeA N0 (hrx5_head NSb)] FZ.
  eapply semax_pre; [| eapply hrx5_B4_R_post; [| apply (hrx5_B4_R_k23 gv L nk KE st i S lul m img n tw a N0 (hrx5_head NSb)
      (hs_snap_cur T (e_peer E) P) (FRZL FZ)); assumption]].
  - unfold hrx5_B4_R_Lp, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars; cbn [app]. entailer!.
  - unfold hrx5_B4_R_Lp, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars; cbn [app]. thaw FZ.
    sep_apply (hrx5_B4_R_wand1 (hrx5_B4_R_nodeA N0 (hrx5_head NSb)) (hnodes_rep4 W (hrx5_head NSs) NSs)).
    rewrite HsH. cbn [hs_snap_cur snap_of sn_hs].
    unfold hrx5_B4_R_A7, hrx5_B4_R_R, hrx5_B4_R_Lp, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars; cbn [app]. entailer!.
Qed.

(* if (t'23): the state is not CREATED_INITIATION *)
Lemma hrx5_B4_R_L23n {Espec: OracleKind} gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX a E p shp P Rr :
  mi_ok IA = true -> t_find_index T (t_L T) (rm_receiver M) = Some (a, E) ->
  Int.eq (e_type E) IDX_HANDSHAKE = true -> sfind PS (e_peer E) = Some (shp, P) ->
  Int.eq (hs_state (p_hs P)) HS_CREATED_INITIATION = false -> In p (map hn_addr NS) ->
  semax D4 (hrx5_B4_R_A7 gv L nk KE st i S lul m img n tw IA NS NSs T M FX a p Int.zero)
    (Sifthenelse hrx5_B4_R_c85 hrx5_B4_R_CALL Sskip)
    (overridePost (hrx5_B4_R_OUT x25519 aead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX) Rr).
Proof.
  intros Hok Hfind Hty HsfP Hst Hpin.
  assert (Htg: hrx5cr_tgt x25519 aead_dec IA T PS M = None).
  { unfold hrx5cr_tgt. rewrite Hok, Hfind, Hty, HsfP, Hst. reflexivity. }
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost].
  unfold hrx5_B4_R_A7, hrx5_B4_R_R, hrx5_B4_R_Lp, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars, hrx5_Delta, hrx5_B4_R_c85. cbn [app].
  simplify_func_tycontext.
  forward_if.
  { exfalso. match goal with Hc: _ <> _ |- _ => apply Hc; reflexivity end. }
  forward.
  unfold hrx5_B4_R_OUT, hrx5_B4_R_R, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars. Exists p 0.
  unfold hrx5_B4_R_acc, hrx5_B4_R_strep. rewrite Htg. cbn [app].
  entailer!. all: auto.
Qed.

(* if (t'23): the state is CREATED_INITIATION: CALL *)
Lemma hrx5_B4_R_L23c {Espec: OracleKind} gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX a p Rr :
  semax D4 (hrx5_B4_R_A4 gv L nk KE st i S lul m img n tw IA NS NSs T M FX a p) hrx5_B4_R_CALL
    (overridePost (hrx5_B4_R_OUT x25519 aead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX) Rr) ->
  semax D4 (hrx5_B4_R_A7 gv L nk KE st i S lul m img n tw IA NS NSs T M FX a p Int.one)
    (Sifthenelse hrx5_B4_R_c85 hrx5_B4_R_CALL Sskip)
    (overridePost (hrx5_B4_R_OUT x25519 aead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX) Rr).
Proof.
  intros HCALL.
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost] in HCALL |- *.
  unfold hrx5_B4_R_A7, hrx5_B4_R_Lp, hrx5_Delta, hrx5_B4_R_c85. unfold hrx5_Delta in HCALL.
  simplify_func_tycontext. unfold hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars; cbn [app].
  forward_if.
  { eapply semax_pre; [| exact HCALL].
    unfold hrx5_B4_R_A4, hrx5_B4_R_R, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars; cbn [app]. entailer!. }
  { exfalso. match goal with Hc: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
Qed.

End K.
End hrx5_B4_R_Km.

Lemma hrx5_B4_R_K_ok : hrx5_B4_R_K_stmt.
Proof.
  unfold hrx5_B4_R_K_stmt. intros. split; [| split]; intros.
  - eapply hrx5_B4_R_Km.hrx5_B4_R_L23; eassumption.
  - eapply hrx5_B4_R_Km.hrx5_B4_R_L23n; eassumption.
  - eapply hrx5_B4_R_Km.hrx5_B4_R_L23c; eassumption.
Qed.
