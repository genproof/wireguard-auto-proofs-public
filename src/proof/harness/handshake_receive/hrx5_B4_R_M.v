(* law handshake_receive, B4 segment R, part M: t'84 = m_consume_response(..); acc_resp = t'84. *)
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

Module hrx5_B4_R_Mm.
Section M.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Local Notation D4 := (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec).

Definition hrx5_B4_R_Lp gv L nk KE st i S lul m img n tw (p a: val) : list localdef :=
  temp HM._target p :: temp HM._e a :: temp HM._acc_resp (Vint Int.zero) :: hrx5_B4_R_Q gv L nk KE st i S lul m img n tw.

(* core: t'22 = m_consume_response(&st, &before, p->snap.ephemeral_private, ia.priv, p->snap.preshared_key,
   msg->unencrypted_ephemeral, msg->encrypted_nothing) *)
Lemma hrx5_B4_R_cMC {Espec: OracleKind} gv L nk KE st i S lul m img n tw x a CK H EPRIV SPRIV PSK E ENCN (F: mpred) Rr :
  isptr x -> isptr m -> Zlength CK = 32 -> Zlength H = 32 -> Zlength EPRIV = 32 -> Zlength SPRIV = 32 ->
  Zlength PSK = 32 -> Zlength E = 32 -> Zlength ENCN = 16 ->
  semax D4 (PROPx [] (LOCALx (hrx5_B4_R_Lp gv L nk KE st i S lul m img n tw x a)
     (SEPx [F; @data_at_ HCS Tsh t_mstate (l_st L); @data_at HCS Tsh t_mstate (mstate_val CK H) (l_before L);
            hbytes Ews EPRIV (offset_val 56 x); hbytes Ews SPRIV (l_id L); hbytes Ews PSK (offset_val 184 x);
            hbytes Ews E (offset_val 12 m); hbytes Ews ENCN (offset_val 44 m);
            WgNoise.proof.blake2s.spec.blake2s_globals gv; @zero_page Noise.CS gv])))
    hrx5_B4_R_mcall
    (overridePost (PROPx [] (LOCALx
       (temp HM._t'84 (Vint (match m_consume_response_model x25519 aead_dec CK H EPRIV SPRIV PSK E ENCN with
                             Some _ => Int.one | None => Int.zero end)) :: hrx5_B4_R_Lp gv L nk KE st i S lul m img n tw x a)
     (SEPx [F; match m_consume_response_model x25519 aead_dec CK H EPRIV SPRIV PSK E ENCN with
               | Some (ck, h) => @data_at HCS Tsh t_mstate (mstate_val ck h) (l_st L)
               | None => @data_at_ HCS Tsh t_mstate (l_st L) end;
            @data_at HCS Tsh t_mstate (mstate_val CK H) (l_before L);
            hbytes Ews EPRIV (offset_val 56 x); hbytes Ews SPRIV (l_id L); hbytes Ews PSK (offset_val 184 x);
            hbytes Ews E (offset_val 12 m); hbytes Ews ENCN (offset_val 44 m);
            WgNoise.proof.blake2s.spec.blake2s_globals gv; @zero_page Noise.CS gv]))) Rr).
Proof.
  intros Hx Hm HlCK HlH HlE HlS HlP HlEm HlN.
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost].
  unfold hrx5_B4_R_Lp, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars, hrx5_Delta, hrx5_B4_R_mcall. cbn [app].
  simplify_func_tycontext.
  forward_call (gv, Tsh, l_st L, Tsh, l_before L, CK, H, Ews, offset_val 56 x, EPRIV, l_id L, SPRIV,
                offset_val 184 x, PSK, offset_val 12 m, E, offset_val 44 m, ENCN).
  entailer!.
Qed.

(* wrapper: the call *)
Lemma hrx5_B4_R_LMC1 {Espec: OracleKind} gv L nk KE st i S lul m img n tw IA NS NSs T M FX a E NSa N0 NSb P Rr :
  NSs = NSa ++ N0 :: NSb -> isptr (hn_addr N0) ->
  hn_snap N0 = hsnap_val (hs_snap_cur T (e_peer E) P) ->
  hrx5_head NSs = hrx5_head NS -> hs_ok (p_hs P) -> Zlength (mi_priv IA) = 32 ->
  semax D4 (hrx5_B4_R_A6 gv L nk KE st i S lul m img n tw IA NS NSs T M FX a (hn_addr N0) (hs_ck (p_hs P)) (hs_hash (p_hs P)))
    hrx5_B4_R_mcall
    (overridePost (hrx5_B4_R_A8 gv L nk KE st i S lul m img n tw IA NS NSs T M FX a (hn_addr N0) (hs_ck (p_hs P)) (hs_hash (p_hs P))
       (m_consume_response_model x25519 aead_dec (hs_ck (p_hs P)) (hs_hash (p_hs P)) (hs_eph (p_hs P))
          (mi_priv IA) (hs_psk (p_hs P)) (rm_eph M) (rm_encn M))) Rr).
Proof.
  intros HNS0 HpA0 HsnN0 HsH HhsP HlIA.
  destruct hrx5_B4_R_sep_ok as (_ & _ & _ & _ & _ & Spriv & _).
  pose proof HhsP as (HlE & _ & _ & _ & HlPsk & HlH & HlCk & _).
  unfold hrx5_B4_R_A6, hrx5_B4_R_Lp, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars; cbn [app].
  rewrite <- HsH. sep_apply (hrx5_B4_R_open NSs NSa N0 NSb HNS0). Intros.
  sep_apply (hrx5_B4_R_fields T N0 (hrx5_head NSb) (e_peer E) P HsnN0 HhsP).
  sep_apply (Spriv Tsh IA (l_id L) HlIA).
  sep_apply (hrx5_B4_R_split_T (mi_priv IA) (l_id L)).
  assert_PROP (isptr m) as Hpm.
  { unfold resp_rep. Intros. entailer!.
    all: match goal with Hf: @field_compatible _ _ _ ?mm |- isptr ?mm => exact (field_compatible_isptr _ _ _ Hf) end. }
  sep_apply (hrx5_B4_R_resp_open M m). Intros.
  match goal with HM: rm_ok M |- _ => rename HM into HrM end.
  pose proof HrM as (HlEm & HlNm & _ & _).
  unfold wg_consts. Intros.
  hrx5_B4_R_keep [@data_at_ HCS Tsh t_mstate (l_st L);
    @data_at HCS Tsh t_mstate (mstate_val (hs_ck (p_hs P)) (hs_hash (p_hs P))) (l_before L);
    hbytes Ews (hs_eph (p_hs P)) (offset_val 56 (hn_addr N0)); hbytes Ews (mi_priv IA) (l_id L);
    hbytes Ews (hs_psk (p_hs P)) (offset_val 184 (hn_addr N0)); hbytes Ews (rm_eph M) (offset_val 12 m);
    hbytes Ews (rm_encn M) (offset_val 44 m); WgNoise.proof.blake2s.spec.blake2s_globals gv;
    @zero_page Noise.CS gv] FZ.
  eapply semax_pre; [| eapply hrx5_B4_R_post; [| apply (hrx5_B4_R_cMC gv L nk KE st i S lul m img n tw (hn_addr N0) a
      (hs_ck (p_hs P)) (hs_hash (p_hs P)) (hs_eph (p_hs P)) (mi_priv IA) (hs_psk (p_hs P)) (rm_eph M) (rm_encn M)
      (FRZL FZ)); assumption]].
  - unfold hrx5_B4_R_Lp, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars; cbn [app]. entailer!.
  - unfold hrx5_B4_R_Lp, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars; cbn [app]. thaw FZ.
    sep_apply (hrx5_B4_R_resp_close M m HrM).
    sep_apply (hrx5_B4_R_join_T (mi_priv IA) (l_id L)).
    sep_apply (hrx5_B4_R_wand1 (hbytes Tsh (mi_priv IA) (l_id L)) (@data_at HCS Tsh t_mident (mident_val IA) (l_id L))).
    sep_apply (hrx5_B4_R_unfields N0 (hrx5_head NSb) (p_hs P)).
    sep_apply (hrx5_B4_R_wand1 (hrx5_B4_R_nodeA N0 (hrx5_head NSb)) (hnodes_rep4 W (hrx5_head NSs) NSs)).
    rewrite HsH.
    unfold hrx5_B4_R_A8, hrx5_B4_R_Lp, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars, wg_consts; cbn [app].
    entailer!.
Qed.

(* if (t'22) target = p; *)
Lemma hrx5_B4_R_LMC2 {Espec: OracleKind} gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX a E x shp P Rr :
  mi_ok IA = true -> t_find_index T (t_L T) (rm_receiver M) = Some (a, E) ->
  Int.eq (e_type E) IDX_HANDSHAKE = true -> sfind PS (e_peer E) = Some (shp, P) ->
  Int.eq (hs_state (p_hs P)) HS_CREATED_INITIATION = true ->
  x = hrx5_nfind NS (e_peer E) -> In x (map hn_addr NS) ->
  semax D4 (hrx5_B4_R_A8 gv L nk KE st i S lul m img n tw IA NS NSs T M FX a x (hs_ck (p_hs P)) (hs_hash (p_hs P))
       (m_consume_response_model x25519 aead_dec (hs_ck (p_hs P)) (hs_hash (p_hs P)) (hs_eph (p_hs P))
          (mi_priv IA) (hs_psk (p_hs P)) (rm_eph M) (rm_encn M)))
    hrx5_B4_R_asg (overridePost (hrx5_B4_R_OUT x25519 aead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX) Rr).
Proof.
  intros Hok Hfind Hty HsfP Hst Hx Hxin.
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost].
  destruct (m_consume_response_model x25519 aead_dec (hs_ck (p_hs P)) (hs_hash (p_hs P)) (hs_eph (p_hs P))
              (mi_priv IA) (hs_psk (p_hs P)) (rm_eph M) (rm_encn M)) as [[ck h] |] eqn:Hmc.
  - assert (Htg: hrx5cr_tgt x25519 aead_dec IA T PS M = Some (e_peer E, P, ck, h)).
    { unfold hrx5cr_tgt. rewrite Hok, Hfind, Hty, HsfP, Hst, Hmc. reflexivity. }
    unfold hrx5_B4_R_A8, hrx5_B4_R_Lp, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars, hrx5_Delta, hrx5_B4_R_asg. cbn [app].
    simplify_func_tycontext.
    forward.
    sep_apply (@data_at_data_at_ HCS Tsh t_mstate (mstate_val (hs_ck (p_hs P)) (hs_hash (p_hs P))) (l_before L)).
    unfold hrx5_B4_R_OUT, hrx5_B4_R_R, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars. Exists x 1.
    unfold hrx5_B4_R_acc, hrx5_B4_R_strep. rewrite Htg. cbn [app].
    entailer!. all: auto.
  - assert (Htg: hrx5cr_tgt x25519 aead_dec IA T PS M = None).
    { unfold hrx5cr_tgt. rewrite Hok, Hfind, Hty, HsfP, Hst, Hmc. reflexivity. }
    unfold hrx5_B4_R_A8, hrx5_B4_R_Lp, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars, hrx5_Delta, hrx5_B4_R_asg. cbn [app].
    simplify_func_tycontext.
    forward.
    sep_apply (@data_at_data_at_ HCS Tsh t_mstate (mstate_val (hs_ck (p_hs P)) (hs_hash (p_hs P))) (l_before L)).
    unfold hrx5_B4_R_OUT, hrx5_B4_R_R, hrx5_B4_R_Q, hrx5_ltemps, hrx5_lvars. Exists x 0.
    unfold hrx5_B4_R_acc, hrx5_B4_R_strep. rewrite Htg. cbn [app].
    entailer!. all: auto.
Qed.

End M.
End hrx5_B4_R_Mm.

Lemma hrx5_B4_R_M_ok : hrx5_B4_R_M_stmt.
Proof.
  unfold hrx5_B4_R_M_stmt. intros. split; intros.
  - eapply hrx5_B4_R_Mm.hrx5_B4_R_LMC1; eassumption.
  - eapply hrx5_B4_R_Mm.hrx5_B4_R_LMC2; eassumption.
Qed.
