(* law handshake_receive: phase B8, branch R: the
   segment hrx5_B8R_D_stmt. *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_D_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_D_s8.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_D_glue.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Lemma hrx5_B8RDm_supd (PS: list (val * share * peer)) j a sh P v :
  NoDup (map peer_addr4 PS) -> 0 <= j < Zlength PS -> Znth j PS = (a, sh, P) ->
  supd PS a v = upd_Znth j PS (a, sh, v).
Proof.
  revert j; induction PS as [| [[b shb] Q] PS IH]; intros j Hnd Hj E.
  - rewrite Zlength_nil in Hj; lia.
  - cbn [map peer_addr4] in Hnd. inversion Hnd as [| ? ? Hni Hnd']; subst.
    cbn [supd]. destruct (Z.eq_dec j 0) as [-> | Hj0].
    + rewrite Znth_0_cons in E. inversion E; subst.
      rewrite if_true by reflexivity. rewrite upd_Znth0. reflexivity.
    + rewrite Znth_pos_cons in E by lia. rewrite Zlength_cons in Hj.
      assert (Hin: In a (map peer_addr4 PS)).
      { replace a with (peer_addr4 (Znth (j - 1) PS)) by (rewrite E; reflexivity).
        apply in_map, Znth_In. lia. }
      rewrite if_false by (intros <-; contradiction).
      rewrite (IH (j - 1)) by (auto; lia).
      rewrite upd_Znth_cons by lia. reflexivity.
Qed.

Lemma hrx5_B8R_D_ok : hrx5_B8R_D_stmt.
Proof.
  unfold hrx5_B8R_D_stmt, hrx5_B8R_seg.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul
    q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY.
  rewrite hrx5_B8RD_eq. eapply semax_seq.
  { rewrite overridePost_overridePost.
    apply (hrx5_B8RD_s8_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head
             nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY). }
  cbv beta zeta delta [hrx5_B8R_RB hrx5_B8R_RD hrx5_B8R_St hrx5_B8R_F hrx5_B8R_facts].
  match goal with |- semax ?D (PROPx ?pl ?QR) ?c ?Post =>
    let pl' := eval cbn [app] in pl in change (semax D (PROPx pl' QR) c Post) end.
  Intros.
  set (Wx := hrx5_B8R_Wxv x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6 port o dp
               d a P M ck h).
  set (Pf := hrx5_B8R_Pf d P M ck h).
  assert (HL: Zlength NS = Zlength PS) by (destruct H0 as (_ & _ & _ & _ & Hnp & _); apply hrx5_B8RDg_len, Hnp).
  assert (Hj: 0 <= j < Zlength NS) by lia.
  assert (HPS: rw_PS Wx = upd_Znth j PS (a, Ews, Pf)).
  { unfold Wx, hrx5_B8R_Wxv, hrx5_B8R_Wx. cbn [rw_PS].
    apply (hrx5_B8RDm_supd PS j a Ews P); [destruct H0 as (_ & _ & Hnd & _); exact Hnd | lia | exact H13]. }
  assert (HTf: rw_T Wx = T \/ rw_T Wx = t_remove T (hs_addr a)).
  { unfold Wx, hrx5_B8R_Wxv, hrx5_B8R_Wx, hrx5_B8R_Tf. cbn [rw_T]. destruct (hrx5_B8R_sess d P); auto. }
  assert (Hitab: d_itab (rw_D Wx) = l_itd L).
  { unfold Wx, hrx5_B8R_Wxv, hrx5_B8R_Wx. cbn [rw_D]. unfold hrx5_B8R_W1v. rewrite H16. reflexivity. }
  assert (HKS: rw_KS Wx = []) by reflexivity.
  unfold rxw_rep at 1. unfold hrx5_rest at 1. unfold hrx5_cglobs at 1. unfold hrx5_scr5 at 1.
  match goal with |- semax ?D (PROPx ?pl (LOCALx ?Q (SEPx ?sl))) ?c ?Post =>
    let sl' := eval cbn [app] in sl in change (semax D (PROPx pl (LOCALx Q (SEPx sl'))) c Post) end.
  do 8 flatten_sepcon_in_SEP.
  unfold hrx5_B8R_tl at 1. unfold hrx5_ptrs at 1. unfold hrx5_lvars at 1.
  match goal with |- semax ?D (PROPx ?pl (LOCALx ?Q ?R)) ?c ?Post =>
    let Q' := eval cbn [app] in Q in change (semax D (PROPx pl (LOCALx Q' R)) c Post) end.
  rewrite Hitab, HPS, HKS.
  freeze FR0 := - (device_rep _ _ _) (itable _ _ _) (peers_rep _) (@data_at _ _ (tptr t_hnode4) _ _)
    (hnodes_rep4 _ _ _).
  assert_PROP (NoDup (map hn_addr NS)) as Hnd.
  { sep_apply (hrx5_B8RDg_nodup (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS)).
    rewrite (hrx5_B8RDg_addr_snap T NS PS HL). entailer!. }
  assert (HYP: hrx5_B8RD_hyp x25519 L R NS PS KE T head nk j a tg (rw_T Wx))
    by exact (conj H0 (conj Hj (conj H14 (conj H15 (conj Hnd HTf))))).
  match goal with |- context [temp HM._m_lul ?vl] => set (VLUL := vl) end.
  match goal with |- context [temp HM._path ?vp] => set (VPATH := vp) end.
  apply semax_pre with (P' := hrx5_B8RD_P0 gv L NS PS T j a tg Pf (rw_T Wx) (rw_D Wx) (FRZL FR0)
    (hs_addr a) (offset_val 8 tg) (Vint (if hrx5_B8R_alloc d then Int.one else Int.zero))
    (Vint (if hrx5_B8R_sess d P then Int.one else Int.zero)) nk (hrx5_khead KE) (Vlong (Int64.repr st))
    (Vlong (Int64.repr i)) (Vlong (s_boot S)) VLUL
    (match o with OBuf _ => dp | _ => nullval end) (match o with OInit _ => dp | _ => nullval end)
    (match o with OResp _ => dp | _ => nullval end) (match o with OCookie _ => dp | _ => nullval end)
    img (Vlong (Int64.repr (Zlength (obj_bytes o)))) (Vint (Int.repr (obj_kind o))) (Vint (Int.repr ai))
    (Vint (Int.repr ar)) (hd nullval (t_L T)) VPATH).
  { unfold hrx5_B8RD_P0, hrx5_B8RD_fix, hrx5_B8RD_lcr, hrx5_lvars. cbn [app].
    entailer!. }
  eapply semax_post; [| | | | apply (hrx5_B8RDg_loop_ok x25519 aead_dec xaead_enc xaead_dec gv L R NS PS KE T head
    nk j a tg Pf (rw_T Wx) (rw_D Wx) (FRZL FR0)
    (hs_addr a) (offset_val 8 tg) (Vint (if hrx5_B8R_alloc d then Int.one else Int.zero))
    (Vint (if hrx5_B8R_sess d P then Int.one else Int.zero)) nk (hrx5_khead KE) (Vlong (Int64.repr st))
    (Vlong (Int64.repr i)) (Vlong (s_boot S)) VLUL
    (match o with OBuf _ => dp | _ => nullval end) (match o with OInit _ => dp | _ => nullval end)
    (match o with OResp _ => dp | _ => nullval end) (match o with OCookie _ => dp | _ => nullval end)
    img (Vlong (Int64.repr (Zlength (obj_bytes o)))) (Vint (Int.repr (obj_kind o))) (Vint (Int.repr ai))
    (Vint (Int.repr ar)) (hd nullval (t_L T)) VPATH (hrx5_RB x25519 gv L FR) HYP)].
  2-4: intros; unfold overridePost; destruct (hrx5_RB x25519 gv L FR) as [r1 r2 r3 r4];
       cbn [RA_break RA_continue RA_return];
       apply andp_left2, derives_refl.
  unfold overridePost; destruct (hrx5_RB x25519 gv L FR) as [r1 r2 r3 r4]; cbn [RA_normal].
  unfold hrx5_B8RD_X, hrx5_B8RD_fix, hrx5_B8RD_lc, hrx5_B8RD_lcr, hrx5_lvars. cbn [app].
  thaw FR0.
  unfold rxw_rep, hrx5_rest, hrx5_cglobs, hrx5_scr5, hrx5_B8R_tl, hrx5_ptrs. rewrite Hitab, HPS, HKS. cbn [app].
  go_lowerx.
  apply andp_right; [apply prop_right; repeat (split; [assumption|]); auto |].
  apply andp_right; [apply prop_right; repeat (split; [assumption|]); auto |].
  cancel.
Qed.
