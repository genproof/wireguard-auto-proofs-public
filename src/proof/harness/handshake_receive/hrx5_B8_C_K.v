(* law handshake_receive, phase B8 branch C: segments C0 (ck = &target->p->latest_cookie; CHECK(rx_only_cookie(0))) and C1 (CHECK of the cookie's fields).
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_ilem.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_C_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_C_K_sep.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Lemma hrx5_B8CK_pfc PS a sh P :
  In (a, sh, P) PS -> peers_rep PS |-- !! (@field_compatible Noise.CS t_peer [] a).
Proof.
  intros Hin. destruct (in_split _ _ Hin) as (l1 & l2 & ->).
  unfold peers_rep. rewrite iter_sepcon_app. simpl iter_sepcon. cbn [peer_item_rep].
  unfold peer_rep at 1. entailer!.
Qed.

Lemma hrx5_B8CK_sfind_in (PS: list (val * share * peer)) a sh P :
  sfind PS a = Some (sh, P) -> In (a, sh, P) PS.
Proof.
  induction PS as [| [[x shx] Px] PS IH]; simpl; [discriminate |].
  match goal with |- context [if ?d then _ else _] => destruct d as [-> | Hne] end; intros Hs.
  - inv Hs. left. reflexivity.
  - right. apply IH. exact Hs.
Qed.

Lemma hrx5_B8CK_hb_ptr sh bs p : hbytes sh bs p |-- !! isptr p.
Proof. unfold hbytes. entailer!. destruct H as [Hp _]; exact Hp. Qed.

Lemma hrx5_B8CK_ckq_close C x X :
  hbytes Ews (ck_last_mac1 C) (offset_val 378 x) * hbytes Ews (ck_dkey C) (offset_val 394 x) *
  hbytes Ews (ck_mkey C) (offset_val 426 x) * (hrx5_B8CK_ckq C x -* X) |-- X.
Proof. apply hrx5_B8CK_wand1. Qed.

Ltac hrx5_B8CK_dead :=
  exfalso;
  first
  [ match goal with Hf: ?x <> ?x |- _ => exact (Hf eq_refl) end
  | match goal with Hf: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hf) end
  | match goal with Hf: Int.zero = Int.one |- _ => exact (Int.one_not_zero (eq_sym Hf)) end
  | discriminate | congruence ].

Ltac hrx5_B8CK_fif t v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
    forward_if (PROPx P (LOCALx (temp t v :: Lc) (SEPx Sp))) end.

Lemma hrx5_B8CK_C0 : hrx5_B8C_C0_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
    proto ip4 ip6 port M dp img a P pt HY.
  unfold hrx5_B8C_QC0, hrx5_B8C_QC, hrx5_B8C_props, hrx5_B8C_temps, hrx5_B8C_sep, hrx5_B8C_world, hrx5_B8C_scr,
    hrx5_rest, hrx5_cglobs, hrx5_lvars, hrx5_Delta, hrx5_B8C_C0; cbn [app].
  abbreviate_semax.
  Intros.
  match goal with H: hrx5_inv _ _ _ _ _ _ _ _ _ |- _ => pose proof H as (_ & _ & _ & _ & Hmap & _) end.
  match goal with H: hrx5_nfind NS a <> nullval |- _ => rename H into Hnf end.
  match goal with H: sfind PS a = Some (Ews, P) |- _ => rename H into Hsf end.
  destruct (hrx5_B8CK_find T NS PS a Ews P Hmap Hnf Hsf) as (NS1 & N & NS2 & HS & Ha & Hp & Hr).
  sep_apply (hrx5_B8CK_open_p _ NS1 N NS2 (hrx5_head (hnodes_snapped4 T NS PS)) HS).
  rewrite Hp, Ha. Intros.
  assert (HinP: In (a, Ews, hrx5ck_new P pt (s_boot S)) (supd PS a (hrx5ck_new P pt (s_boot S))))
    by (eapply hrx5_B8CK_supd_in; eauto).
  assert_PROP (@field_compatible Noise.CS t_peer [] a) as FCp.
  { sep_apply (hrx5_B8CK_pfc _ _ _ _ HinP). entailer!. }
  assert (Pa: isptr a) by (destruct FCp; auto).
  forward.
  forward.
  sep_apply (hrx5_B8CK_wand1 (field_at Ews t_hnode4 (DOT HRK._p) a (hrx5_nfind NS a))).
  match goal with |- context [temp HRM._ck__1 (offset_val ?z a)] => replace z with 360 by reflexivity end.
  unfold POSTCONDITION, abbreviate. destruct (hrx5_RB x25519 gv L FR) as [rn rb rc rr]. unfold overridePost.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward_call (gv, rx0, Int.repr 0).
    replace (rx_only_cookie_b rx0 (Int.repr 0)) with true by reflexivity.
    forward_if.
    { exfalso. apply Int.one_not_zero. assumption. }
    forward. entailer!. }
  forward. entailer!.
  cbn [RA_normal]. entailer!.
Qed.

Lemma hrx5_B8CK_C1 : hrx5_B8C_C1_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
    proto ip4 ip6 port M dp img a P pt HY.
  unfold hrx5_B8C_QC, hrx5_B8C_props, hrx5_B8C_temps, hrx5_B8C_sep, hrx5_B8C_world, hrx5_B8C_scr,
    hrx5_rest, hrx5_cglobs, hrx5_lvars, hrx5_Delta, hrx5_B8C_C1; cbn [app].
  abbreviate_semax.
  Intros.
  match goal with H: hrx5_inv _ _ _ _ _ _ _ _ _ |- _ => pose proof H as (_ & _ & _ & _ & Hmap & _) end.
  match goal with H: hrx5_nfind NS a <> nullval |- _ => rename H into Hnf end.
  match goal with H: sfind PS a = Some (Ews, P) |- _ => rename H into Hsf end.
  match goal with H: Zlength pt = 16 |- _ => rename H into Lpt end.
  destruct (hrx5_B8CK_find T NS PS a Ews P Hmap Hnf Hsf) as (NS1 & N & NS2 & HS & Ha & Hp & Hr).
  clear Hp.
  set (P' := hrx5ck_new P pt (s_boot S)) in *.
  assert (HinP: In (a, Ews, P') (supd PS a P')) by (eapply hrx5_B8CK_supd_in; eauto).
  assert (HinP0: In (a, Ews, P) PS) by (eapply hrx5_B8CK_sfind_in; eauto).
  assert_PROP (cookie_ok (p_cookie P')) as HCok'.
  { sep_apply (hrx5_B8CK_peers_ck _ _ _ _ HinP). entailer!. }
  assert (Hck3: hrx5_B8CK_ck3 (p_cookie P)).
  { destruct HCok' as (_ & A1 & A2 & A3). exact (conj A1 (conj A2 A3)). }
  pose proof Hck3 as (Llm & Ldk & Lmk).
  assert_PROP (@field_compatible Noise.CS t_peer [] a) as FCp.
  { sep_apply (hrx5_B8CK_pfc _ _ _ _ HinP). entailer!. }
  assert (Pa: isptr a) by (destruct FCp; auto).
  sep_apply (hrx5_B8CK_open_ck _ NS1 N NS2 (hrx5_head (hnodes_snapped4 T NS PS)) P HS Hr Hck3).
  rewrite Ha. unfold hrx5_B8CK_ckq at 1. Intros.
  assert_PROP (isptr (offset_val 378 (hrx5_nfind NS a))) as Pt378.
  { sep_apply (hrx5_B8CK_hb_ptr Ews (ck_last_mac1 (p_cookie P)) (offset_val 378 (hrx5_nfind NS a))). entailer!. }
  assert (Pt: isptr (hrx5_nfind NS a)) by (destruct (hrx5_nfind NS a); try contradiction; exact I).
  sep_apply (hrx5_B8CK_ck_open _ a P' (s_boot S) true pt false (ck_last_mac1 (p_cookie P)) (ck_dkey (p_cookie P))
    (ck_mkey (p_cookie P)) HinP eq_refl).
  Intros lk.
  match goal with Hf: cookie_ok (mkCookie _ _ _ _ _ _ _) |- _ => rename Hf into HCk end.
  match goal with Hf: field_compatible hrx5_B8CK_tck [] _ |- _ => rename Hf into FCck end.
  unfold hrx5_B8CK_ckp, hrx5_B8CK_tck. Intros.
  change (offset_val 360 a) with (cookie_addr a).
  unfold POSTCONDITION, abbreviate. destruct (hrx5_RB x25519 gv L FR) as [rn rb rc rr]. unfold overridePost.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward_call (Ews, offset_val 9 (cookie_addr a), pt, Tsh, l_pt L, pt).
    { entailer!. unfold cookie_addr. destruct a; try contradiction. rewrite Lpt. reflexivity. }
    rewrite hrx5_B8CK_eqb_refl.
    hrx5_B8CK_fif HRM._t'200 (Vint Int.one).
    { forward. forward. unfold Int64.cmpu. rewrite Int64.eq_true. entailer!. }
    { hrx5_B8CK_dead. }
    hrx5_B8CK_fif HRM._t'201 (Vint Int.one).
    { forward. forward. entailer!. }
    { hrx5_B8CK_dead. }
    hrx5_B8CK_fif HRM._t'202 (Vint Int.one).
    { forward. forward. entailer!. }
    { hrx5_B8CK_dead. }
    hrx5_B8CK_fif HRM._t'203 (Vint Int.one).
    { forward_call (Ews, offset_val 26 (cookie_addr a), ck_last_mac1 (p_cookie P), Ews,
                    offset_val 378 (hrx5_nfind NS a), ck_last_mac1 (p_cookie P)).
      { entailer!. unfold cookie_addr. revert Pt. generalize (hrx5_nfind NS a) as t. intros t Ptt.
        destruct a; try contradiction. destruct t; try contradiction. rewrite Llm. simpl.
        rewrite !Ptrofs.add_assoc. reflexivity. }
      rewrite hrx5_B8CK_eqb_refl. forward. entailer!. }
    { hrx5_B8CK_dead. }
    hrx5_B8CK_fif HRM._t'205 (Vint Int.one).
    { forward_call (Ews, offset_val 42 (cookie_addr a), ck_dkey (p_cookie P), Ews,
                    offset_val 394 (hrx5_nfind NS a), ck_dkey (p_cookie P)).
      { entailer!. unfold cookie_addr. revert Pt. generalize (hrx5_nfind NS a) as t. intros t Ptt.
        destruct a; try contradiction. destruct t; try contradiction. rewrite Ldk. simpl.
        rewrite !Ptrofs.add_assoc. reflexivity. }
      rewrite hrx5_B8CK_eqb_refl. forward. entailer!. }
    { hrx5_B8CK_dead. }
    hrx5_B8CK_fif HRM._t'207 (Vint Int.one).
    { forward_call (Ews, offset_val 74 (cookie_addr a), ck_mkey (p_cookie P), Ews,
                    offset_val 426 (hrx5_nfind NS a), ck_mkey (p_cookie P)).
      { entailer!. unfold cookie_addr. revert Pt. generalize (hrx5_nfind NS a) as t. intros t Ptt.
        destruct a; try contradiction. destruct t; try contradiction. rewrite Lmk. simpl.
        rewrite !Ptrofs.add_assoc. reflexivity. }
      rewrite hrx5_B8CK_eqb_refl. forward. entailer!. }
    { hrx5_B8CK_dead. }
    forward_if.
    { hrx5_B8CK_dead. }
    forward. entailer!. }
  forward. entailer!.
  cbn [RA_normal].
  assert (CKC := hrx5_B8CK_ck_close (cookie_addr a) (s_boot S) true pt false (ck_last_mac1 (p_cookie P))
    (ck_dkey (p_cookie P)) (ck_mkey (p_cookie P)) lk (peers_rep (supd PS a P')) HCk FCck).
  unfold hrx5_B8CK_ckp, hrx5_B8CK_tck in CKC.
  sep_apply CKC.
  sep_apply (hrx5_B8CK_ckq_close (p_cookie P) (hrx5_nfind NS a)
    (hnodes_rep4 W (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS))).
  entailer!.
Qed.

Lemma hrx5_B8C_K_ok : hrx5_B8C_C0_stmt /\ hrx5_B8C_C1_stmt.
Proof. exact (conj hrx5_B8CK_C0 hrx5_B8CK_C1). Qed.
