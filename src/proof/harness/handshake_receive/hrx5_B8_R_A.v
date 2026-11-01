(* law handshake_receive: phase B8, branch R: the
   segment hrx5_B8R_A_stmt. *)
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
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_A_pure.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_A_sep.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_A_core.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Lemma hrx5_B8RA_sfind x25519 aead_dec R L NS PS KE T head nk M a P ck h :
  hrx5_inv x25519 R L NS PS KE T head nk ->
  hrx5cr_tgt x25519 aead_dec (hrx5_ID x25519 R) T PS M = Some (a, P, ck, h) -> sfind PS a = Some (Ews, P).
Proof.
  intros Hinv. unfold hrx5cr_tgt. destruct (mi_ok _); [|discriminate].
  destruct (t_find_index _ _ _) as [[x E]|]; [|discriminate].
  destruct (Int.eq (e_type E) IDX_HANDSHAKE); [|discriminate].
  destruct (sfind PS (e_peer E)) as [[sh P0]|] eqn:Hf; [|discriminate].
  destruct (Int.eq _ _); [|discriminate].
  destruct (m_consume_response_model _ _ _ _ _ _ _ _ _) as [[ck0 h0]|]; [|discriminate].
  intros HE; inv HE.
  destruct Hinv as (Hpok & _).
  pose proof (prot_rep3_sfind_In _ _ _ _ Hf) as HIn.
  rewrite Forall_forall in Hpok. destruct (Hpok _ HIn) as (-> & _). exact Hf.
Qed.

Lemma hrx5_B8RA_addprops Delta Ps Q R : fold_right and True Ps ->
  ENTAIL Delta, PROPx [] (LOCALx Q (SEPx R)) |-- PROPx Ps (LOCALx Q (SEPx R)).
Proof.
  intros HP. unfold PROPx. apply andp_left2. apply andp_right; [apply prop_right; exact HP |].
  apply andp_left2. apply derives_refl.
Qed.

Lemma hrx5_B8R_A_ok : hrx5_B8R_A_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
    proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY.
  unfold hrx5_B8R_R0, hrx5_B8R_RA, hrx5_B8R_St, hrx5_B8R_F, hrx5_B8R_facts, hrx5_B8R_tl.
  set (W1 := hrx5_B8R_W1v x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6 port o dp d).
  unfold hrx5_Delta, hrx5_lvars, hrx5_rest, hrx5_cglobs, hrx5_ptrs, hrx5_scr5; cbn [app].
  simplify_func_tycontext. abbreviate_semax.
  Intros.
  subst o ai ar tg.
  set (s := hrx5_skb dp (OResp M) proto ip4 ip6 port) in *.
  set (D := hrx5_DL x25519 R L sec birth) in *.
  assert (HIn: In (a, Ews, P) PS) by (rewrite <- H13; apply Znth_In; exact H12).
  pose proof H0 as (Hpok & _ & _ & _ & Hnp & _ & _).
  assert (HP0: hrx5_pok x25519 R L (a, Ews, P)) by (rewrite Forall_forall in Hpok; exact (Hpok _ HIn)).
  destruct HP0 as (_ & _ & _ & _ & _ & Hrefs & _ & _ & Hcur & Hprev & Hnext).
  assert (HLN: Zlength NS = Zlength PS)
    by (unfold hnodes_peers4 in Hnp; rewrite <- (Zlength_map _ _ hn_p NS), Hnp, Zlength_map; reflexivity).
  pose proof (hrx5_B8RA_vin x25519 aead_dec R L NS PS KE T head nk M a P ck h H0 H11) as Hvin.
  pose proof (hrx5_B8RA_sfind x25519 aead_dec R L NS PS KE T head nk M a P ck h H0 H11) as Hsf.
  assert (HS1: s_fails (hrx5_B8R_S1 D S q lul (obj_bytes (OResp M)) d) = s_fails S)
    by (unfold hrx5_B8R_S1; destruct (validate_rotates _ _ _ _); reflexivity).
  pose proof (hrx5_B8RA_pure D (hrx5_B8R_D1 D S q lul s (obj_bytes (OResp M)) d) T PS S
    (hrx5_B8R_S1 D S q lul (obj_bytes (OResp M)) d) w kc lul (hrx5_B8R_lul1 S q lul) a P M ck h d (l_skb L) (sk_len s)
    Hvin Hrefs Hcur Hprev Hnext HS1) as HPure.
  cbv zeta in HPure. rewrite <- H16 in HPure.
  assert (EW: hrx5_B8R_W1 x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6 port
     (OResp M) dp d = W1) by reflexivity.
  rewrite EW in HPure. clear EW.
  destruct HPure as (Hfail & Hauth & Hpeer & Heskb & Hw & P' & HPS & HrefP').
  clearbody W1.
  unfold POSTCONDITION, abbreviate. destruct (hrx5_RB x25519 gv L FR) as [rn rb rc rr]. unfold overridePost.
  freeze [1;2;3;4;5;6;7;9;10;11;12;13;14;16;17;18;19;21;22;23;24;25;26;27;28;29;30;31;32] FR0.
  match goal with |- semax _ (PROPx ?Pr (LOCALx ?Q (SEPx ?Rr))) _ _ =>
    apply (semax_post (normal_ret_assert (PROPx Pr (LOCALx
      (hrx5_B8RA_new a (hn_addr (Znth j NS)) d P ++ Q) (SEPx Rr))))) end.
  { cbn [RA_normal normal_ret_assert]. thaw FR0. unfold hrx5_B8RA_new. cbn [app].
    match goal with |- ENTAIL _, PROPx _ (LOCALx ?Lq (SEPx _)) |-- PROPx _ (LOCALx _ (SEPx ?R2)) =>
      apply ENTAIL_trans with (PROPx [] (LOCALx Lq (SEPx R2))) end.
    { apply SEP_entail. cbn [fold_right_sepcon]. cancel. }
    apply hrx5_B8RA_addprops. cbn [fold_right].
    repeat match goal with |- _ /\ _ => split end; first [assumption | reflexivity | tauto]. }
  { cbn [RA_break normal_ret_assert]. apply andp_left2, FF_left. }
  { cbn [RA_continue normal_ret_assert]. apply andp_left2, FF_left. }
  { intros vl. cbn [RA_return normal_ret_assert]. apply andp_left2, FF_left. }
  pose proof hrx5_B8RA_core as HC. unfold hrx5_B8RA_core_stmt in HC.
  eapply HC with (PS := PS) (P := P) (P' := P') (a := a) (d := d) (S := S) (w := w)
    (NS1 := sublist 0 j (hnodes_snapped4 T NS PS)) (N := hn_snapshot4 T (Znth j NS) (Znth j PS))
    (NS2 := sublist (j + 1) (Zlength PS) (hnodes_snapped4 T NS PS)); clear HC.
  - exact HPS.
  - exact Hsf.
  - exact (hrx5_B8RA_split T NS PS j HLN H12).
  - rewrite H13. reflexivity.
  - rewrite H13. exact H14.
  - rewrite H13. reflexivity.
  - rewrite H13. reflexivity.
  - exact Hfail.
  - exact Hauth.
  - exact Hpeer.
  - exact Heskb.
  - exact Hw.
  - exact HrefP'.
Qed.
