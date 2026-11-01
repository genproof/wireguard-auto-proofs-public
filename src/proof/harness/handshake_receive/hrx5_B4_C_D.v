(* law handshake_receive, phase B4, segment C, part D:
   the decryption for a non-NULL target (sD): port of cookie_reply's hcy5_p11_C (no CHECK).  Cut and states: hrx5_B4_C_defs.v. *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_C_defs.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_C_D_sep.
Local Open Scope logic.

(* the model's target for the entry E of peer P *)
Lemma hrx5_B4_C_D_tgt (xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte)) T PS M a E P :
  t_lookup T (Int.or IDX_HANDSHAKE IDX_KEYPAIR) (cm_receiver M) = Some (a, E) ->
  sfind PS (e_peer E) = Some (Ews, P) ->
  hrx5ck_tgt xaead_dec T PS M =
  if ck_sent (p_cookie P) then
    match xaead_dec (ck_dkey (p_cookie P)) (cm_nonce M) (ck_last_mac1 (p_cookie P)) (cm_enc M) with
    | Some pt => Some (e_peer E, P, pt) | None => None end
  else None.
Proof.
  unfold t_lookup, hrx5ck_tgt. destruct (t_find_index T (t_L T) (cm_receiver M)) as [[a' E']|]; [|discriminate].
  destruct (Int.eq _ Int.zero); [discriminate|]. intros H; inv H. intros ->. reflexivity.
Qed.

Ltac hrx5_B4_C_D_dead :=
  exfalso;
  first
  [ match goal with Hf: ?x <> ?x |- _ => exact (Hf eq_refl) end
  | match goal with Hf: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hf) end
  | match goal with Hf: Int.zero = Int.one |- _ => exact (Int.one_not_zero (eq_sym Hf)) end
  | discriminate | congruence ].

(* the proof's steps (they name the lemma's hypotheses) *)
Ltac hrx5_B4_C_D_tc :=
  apply denote_tc_test_eq_split; [| apply valid_pointer_zero64; auto];
  match goal with |- context [hnodes_rep4 W ?l ?L] =>
    apply derives_trans with (hnodes_rep4 W l L * TT); [cancel |] end;
  apply sepcon_valid_pointer1; apply hrx5_B4_C_D_hn_valid;
  match goal with H: hnodes_snapped4 _ _ _ = _ |- _ => rewrite H end;
  rewrite map_app; apply in_or_app; right; left; reflexivity.

Ltac hrx5_B4_C_D_tt :=
  match goal with
  | Hs: ck_sent _ = _, Ht: typed_true _ _ |- _ => rewrite Hs in Ht; cbv in Ht
  | Hs: ck_sent _ = _, Ht: typed_false _ _ |- _ => rewrite Hs in Ht; cbv in Ht
  end;
  exfalso; first [discriminate | contradiction | congruence].

Ltac hrx5_B4_C_D_openn :=
  match goal with
  | HNS: hnodes_snapped4 ?T ?NS ?PS = ?NS1 ++ ?N :: ?NS2, HNr: hn_rest ?N = prsnap_val ?P, HCok: cookie_ok _ |- _ =>
      sep_apply (hrx5_B4_C_D_open _ NS1 N NS2 (hrx5_head (hnodes_snapped4 T NS PS)) P HNS HNr HCok)
  end;
  unfold hrx5_B4_C_D_ckq; Intros;
  match goal with HCok: cookie_ok ?C |- _ =>
    assert (TCB: tc_val tbool (Val.of_bool (ck_sent C))) by (destruct (ck_sent C); hnf; auto)
  end.

Ltac hrx5_B4_C_D_pre :=
  rewrite hrx5_B4_C_D_cm_open; Intros; unfold hrx5_B4_C_D_cm;
  unfold wg_consts; rewrite hrx5_B4_C_D_zp;
  match goal with
  | Lno: Zlength (cm_nonce ?M) = 24, Ldk: Zlength (ck_dkey ?C) = 32, Pt: isptr (hn_addr ?N),
    Hmc: @field_compatible W t_cmsg [] ?dp |- context [hout Tsh 16 (l_pt ?L)] =>
      rewrite (hrx5_B4_C_D_hprim Ews (cm_enc M) (offset_val 32 dp)) by lia;
      rewrite (hrx5_B4_C_D_hprim Ews (ck_last_mac1 C) (offset_val 378 (hn_addr N))) by lia;
      rewrite (hrx5_B4_C_D_hW Ews (cm_nonce M) (offset_val 8 dp)),
        (hrx5_B4_C_D_hW Ews (ck_dkey C) (offset_val 394 (hn_addr N))), Lno, Ldk;
      rewrite (hrx5_B4_C_D_hout16 Tsh (l_pt L))
  end.

Ltac hrx5_B4_C_D_args :=
  match goal with
  | Len: Zlength (cm_enc _) = 32, Llm: Zlength (ck_last_mac1 _) = 16, Pt: isptr (hn_addr ?N),
    Hmc: @field_compatible W t_cmsg [] ?dp |- _ =>
      entailer!; rewrite Len, Llm; destruct (hn_addr N); try contradiction; destruct dp; try contradiction;
      simpl; rewrite !Ptrofs.add_assoc; reflexivity
  end.

Ltac hrx5_B4_C_D_post :=
  match goal with
  | Lno: Zlength (cm_nonce ?M) = 24, Ldk: Zlength (ck_dkey ?C) = 32, Pt: isptr (hn_addr ?N), Hok: cm_ok _,
    Hmc: @field_compatible W t_cmsg [] ?dp |- _ =>
      rewrite <- (hrx5_B4_C_D_hprim Ews (cm_enc M) (offset_val 32 dp)) by lia;
      rewrite <- (hrx5_B4_C_D_hprim Ews (ck_last_mac1 C) (offset_val 378 (hn_addr N))) by lia;
      replace (@data_at W Ews (tarray tuchar 24) (map Vubyte (cm_nonce M)) (offset_val 8 dp))
        with (hbytes Ews (cm_nonce M) (offset_val 8 dp)) by (rewrite hrx5_B4_C_D_hW, Lno; reflexivity);
      replace (@data_at W Ews (tarray tuchar 32) (map Vubyte (ck_dkey C)) (offset_val 394 (hn_addr N)))
        with (hbytes Ews (ck_dkey C) (offset_val 394 (hn_addr N))) by (rewrite hrx5_B4_C_D_hW, Ldk; reflexivity);
      rewrite <- hrx5_B4_C_D_zp;
      let Hf := fresh "Hf" in
      assert (Hf := hrx5_B4_C_D_cm_fold Ews dp M Hok Hmc); unfold hrx5_B4_C_D_cm in Hf; sep_apply Hf; clear Hf
  end.

Ltac hrx5_B4_C_D_shut :=
  match goal with
  | Pt: isptr (hn_addr ?N), HCok: cookie_ok ?C |- context [hnodes_rep4 W ?l ?L] =>
      let Hf := fresh "Hf" in
      assert (Hf := hrx5_B4_C_D_close C (hn_addr N) (hnodes_rep4 W l L)); unfold hrx5_B4_C_D_ckq in Hf;
      sep_apply Hf; clear Hf
  end;
  cbv beta iota delta [hrx5_RB loop1_ret_assert overridePost hrx5_R frame_ret_assert function_body_ret_assert
                       RA_break RA_normal];
  unfold wg_consts; entailer!.

Lemma hrx5_B4_C_D_ok : hrx5_B4_C_D_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
    proto ip4 ip6 port M dp img a E P NS1 N NS2 HH Hlk Hsf HNS HNa HNr.
  pose proof HH as (_ & _ & HX).
  assert (HinP := hrx5_B4_C_D_sfind_in _ _ _ _ Hsf).
  assert (Htg := hrx5_B4_C_D_tgt xaead_dec T PS M a E P Hlk Hsf).
  unfold hrx5_B4_C_st, hrx5_B4_C_scr, hrx5_Delta, hrx5_RB, hrx5_ltemps, hrx5_ptrs, hrx5_lvars, hrx5_wcore, hrx5_rest,
    hrx5_globs; cbn [app obj_bytes obj_kind obj_rep obj_ok].
  simplify_func_tycontext. abbreviate_semax.
  unfold hrx5_B4_C_sD.
  Intros.
  assert_PROP (cookie_ok (p_cookie P)) as HCok.
  { sep_apply (hrx5_B4_C_D_peers_ck PS (e_peer E) Ews P HinP). entailer!. }
  assert_PROP (isptr (hn_addr N)) as Pt.
  { sep_apply (hrx5_B4_C_D_open _ NS1 N NS2 (hrx5_head (hnodes_snapped4 T NS PS)) P HNS HNr HCok).
    unfold hrx5_B4_C_D_ckq. entailer!. }
  pose proof H3 as (Lno & Len).
  pose proof HCok as (Lck & Llm & Ldk & Lmk).
  destruct (ck_sent (p_cookie P)) eqn:Hsent;
    [destruct (xaead_dec (ck_dkey (p_cookie P)) (cm_nonce M) (ck_last_mac1 (p_cookie P)) (cm_enc M)) as [pt|] eqn:Hdec |].
  - (* mac1 sent, the decryption succeeds *)
    pose proof (xaead_dec_length _ _ HX _ _ _ _ _ Hdec) as Lpt. rewrite Len in Lpt. simpl in Lpt.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
      let F := eval pattern (hout Tsh 16 (l_pt L)) in Sp in
      match F with ?f _ => let Sp2 := eval cbv beta in (f (hbytes Tsh pt (l_pt L))) in
        forward_if (PROPx P (LOCALx (temp HM._t'90 (Vint Int.zero) :: Lc) (SEPx Sp2))) end end.
    { hrx5_B4_C_D_tc. }
    { hrx5_B4_C_D_openn.
      forward.
      forward_if.
      { hrx5_B4_C_D_tt. }
      hrx5_B4_C_D_pre.
      forward_call (Tsh, l_pt L, Zrepeat Vundef 16, Ews, offset_val 32 dp, cm_enc M, Ews,
                    offset_val 378 (hn_addr N), ck_last_mac1 (p_cookie P), Ews, offset_val 8 dp, cm_nonce M, Ews,
                    offset_val 394 (hn_addr N), ck_dkey (p_cookie P), gv).
      { hrx5_B4_C_D_args. }
      { cancel. }
      { rewrite Len. reflexivity. }
      rewrite Hdec. cbv iota.
      rewrite (hrx5_B4_C_D_pout Tsh pt (l_pt L)) by lia.
      hrx5_B4_C_D_post.
      forward. forward.
      hrx5_B4_C_D_shut. }
    { rewrite H6 in Pt. contradiction. }
    forward_if.
    { hrx5_B4_C_D_dead. }
    forward.
    match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with (hrx5_S4 x25519 aead_dec xaead_dec gv L FR) end.
    unfold hrx5_S4.
    Exists R sec birth S w NS PS T.
    Exists head nk KE st i kc lul q.
    Exists proto ip4 ip6 port (OCookie M) dp img (hn_addr N).
    Exists 0 0.
    unfold hrx5_scr4, hrx5_ci_rep, hrx5_st_rep, hrx5_pt_rep, hrx5_ltemps, hrx5_ptrs, hrx5_lvars, hrx5_wcore, hrx5_rest,
      hrx5_globs.
    cbn [app obj_bytes obj_kind].
    assert (Hacc: hrx5_acc_ok x25519 aead_dec xaead_dec R NS PS T (OCookie M) (s_boot S) (hn_addr N) 0 0)
      by (unfold hrx5_acc_ok; cbn [obj_bytes]; rewrite H5, Htg;
          split; [reflexivity | split; [reflexivity | first [exact HNa | reflexivity]]]).
    rewrite H5, Htg. entailer!.
    all: unfold obj_rep; cancel.
  - (* mac1 sent, the decryption fails *)
    match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HM._t'90 (Vint Int.one) :: Lc) (SEPx Sp))) end.
    { hrx5_B4_C_D_tc. }
    { hrx5_B4_C_D_openn.
      forward.
      forward_if.
      { hrx5_B4_C_D_tt. }
      hrx5_B4_C_D_pre.
      forward_call (Tsh, l_pt L, Zrepeat Vundef 16, Ews, offset_val 32 dp, cm_enc M, Ews,
                    offset_val 378 (hn_addr N), ck_last_mac1 (p_cookie P), Ews, offset_val 8 dp, cm_nonce M, Ews,
                    offset_val 394 (hn_addr N), ck_dkey (p_cookie P), gv).
      { hrx5_B4_C_D_args. }
      { cancel. }
      { rewrite Len. reflexivity. }
      rewrite Hdec. cbv iota.
      rewrite <- (hrx5_B4_C_D_hout16 Tsh (l_pt L)).
      hrx5_B4_C_D_post.
      forward. forward.
      hrx5_B4_C_D_shut. }
    { rewrite H6 in Pt. contradiction. }
    forward_if.
    2: { hrx5_B4_C_D_dead. }
    forward.
    match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with (hrx5_S4 x25519 aead_dec xaead_dec gv L FR) end.
    unfold hrx5_S4.
    Exists R sec birth S w NS PS T.
    Exists head nk KE st i kc lul q.
    Exists proto ip4 ip6 port (OCookie M) dp img nullval.
    Exists 0 0.
    unfold hrx5_scr4, hrx5_ci_rep, hrx5_st_rep, hrx5_pt_rep, hrx5_ltemps, hrx5_ptrs, hrx5_lvars, hrx5_wcore, hrx5_rest,
      hrx5_globs.
    cbn [app obj_bytes obj_kind].
    assert (Hacc: hrx5_acc_ok x25519 aead_dec xaead_dec R NS PS T (OCookie M) (s_boot S) nullval 0 0)
      by (unfold hrx5_acc_ok; cbn [obj_bytes]; rewrite H5, Htg;
          split; [reflexivity | split; [reflexivity | first [exact HNa | reflexivity]]]).
    rewrite H5, Htg. entailer!.
    all: unfold obj_rep; cancel.
  - (* no mac1 sent *)
    match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HM._t'90 (Vint Int.one) :: Lc) (SEPx Sp))) end.
    { hrx5_B4_C_D_tc. }
    { hrx5_B4_C_D_openn.
      forward.
      forward_if.
      2: { hrx5_B4_C_D_tt. }
      forward.
      hrx5_B4_C_D_shut. }
    { rewrite H6 in Pt. contradiction. }
    forward_if.
    2: { hrx5_B4_C_D_dead. }
    forward.
    match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with (hrx5_S4 x25519 aead_dec xaead_dec gv L FR) end.
    unfold hrx5_S4.
    Exists R sec birth S w NS PS T.
    Exists head nk KE st i kc lul q.
    Exists proto ip4 ip6 port (OCookie M) dp img nullval.
    Exists 0 0.
    unfold hrx5_scr4, hrx5_ci_rep, hrx5_st_rep, hrx5_pt_rep, hrx5_ltemps, hrx5_ptrs, hrx5_lvars, hrx5_wcore, hrx5_rest,
      hrx5_globs.
    cbn [app obj_bytes obj_kind].
    assert (Hacc: hrx5_acc_ok x25519 aead_dec xaead_dec R NS PS T (OCookie M) (s_boot S) nullval 0 0)
      by (unfold hrx5_acc_ok; cbn [obj_bytes]; rewrite H5, Htg;
          split; [reflexivity | split; [reflexivity | first [exact HNa | reflexivity]]]).
    rewrite H5, Htg. entailer!.
    all: unfold obj_rep; cancel.
Qed.
