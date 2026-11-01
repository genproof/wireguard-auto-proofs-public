(* law handshake_receive: B8 branch R segment B: CLR = wg_noise_keypairs_clear(&target->p->keypairs); CHECK(frees + 1), into the final world.
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_L_sep.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Lemma hrx5_b8rbl_tulong {cs1 cs2: compspecs} sh v p :
  @data_at cs1 sh tulong v p = @data_at cs2 sh tulong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible; simpl.
  split; intros (?&?&?&?&?); (repeat split); auto;
    destruct p; try contradiction; unfold align_compatible in *;
    (apply align_compatible_rec_by_value with Mint64; [reflexivity|]);
    apply (align_compatible_rec_by_value_inv _ _ Mint64) in H2; auto.
Qed.

Lemma hrx5_b8rbl_ss sh v p : @data_at CKS sh t_shimsnap v p = @data_at W sh t_shimsnap v p.
Proof.
  apply (f_equal (fun f => f p)). apply (@data_at_change_composite CKS W _ sh t_shimsnap); [apply JMeq_refl | reflexivity].
Qed.

Ltac hrx5_b8rbl_sub :=
  let Q0 := fresh "Q0" in let HQ := fresh "HQ" in
  intros Q0 HQ; simpl In in HQ;
  repeat (destruct HQ as [<- | HQ]; [simpl In; repeat (first [left; reflexivity | right]) | ]);
  contradiction.

Lemma hrx5_b8rbl_peer_isptr sh a Q : peer_rep sh a Q |-- !! isptr a.
Proof. unfold peer_rep. apply andp_left1. apply prop_derives. intros H. apply H. Qed.

Lemma hrx5_B8RB_CLR_ok : hrx5_B8RB_CLR_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
    proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY.
  cbv beta zeta delta [hrx5_B8RB_Ssk hrx5_B8RB_Sx hrx5_B8R_St].
  unfold hrx5_Delta, hrx5_B8RB_CLR.
  abbreviate_semax.
  match goal with |- semax _ (PROPx ?Pl _) _ _ => assert_PROP (fold_right and True Pl) as HP end.
  { apply andp_left2. unfold PROPx. apply andp_left1. apply derives_refl. }
  rewrite !fold_right_and_app_low in HP.
  destruct HP as [HP0 [HG [HFA HFS]]].
  unfold hrx5_B8RB_G in HG. unfold hrx5_B8RB_FA in HFA. unfold hrx5_B8RB_FS in HFS. cbn [fold_right] in HG, HFA, HFS.
  destruct HFS as (Hsess & HFk & HFv1 & HFv2 & HFsk & HFinit & HFri & HFrefs & HFclr & HFwarn & HFx & _).
  rewrite Hsess in HFA.
  destruct HFA as (HFal & HFPS & HFT & HFKS & HFS & HFin & HFsf & HFz & _ & _).
  destruct HG as (HG1 & HG2 & HG3 & HG4 & HG5 & HG6 & HG7 & HG8 & HG9 & HG10 & HG11 & HG12 & HG13 & HG14 & HG15
    & HGal & HGfa & HGfr & _).
  pose proof HP0 as HP0'. cbn [fold_right] in HP0'.
  destruct HP0' as (_ & HI & _).
  destruct HI as (HIpok & HIwf & HInd & _).
  assert (HPin: In (a, Ews, P) PS) by (rewrite <- HG7; apply Znth_In; exact HG6).
  assert (HSF: sfind PS a = Some (Ews, P)) by (apply hrx5_B8RBL_sfind; auto).
  assert (HDev: p_device P = l_wd L).
  { rewrite Forall_forall in HIpok. destruct (HIpok _ HPin) as (_ & Hd & _). exact Hd. }
  assert (HNin: In (Znth j (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS)).
  { apply Znth_In. rewrite hrx5_B8RBL_snapped_len by auto. rewrite HG10; exact HG6. }
  rewrite HG11 in HNin.
  set (W1 := hrx5_B8R_W1 x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6 port o dp d) in *.
  set (S1 := hrx5_B8RB_S1 x25519 R L sec birth S q lul o d) in *.
  set (K := hrx5_B8RB_K P M ck h kc S1) in *.
  set (Pz := hrx5_B8RB_Pz d P M ck h) in *.
  set (T3 := hrx5_B8RB_T3 T a (rd_k d)) in *.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    apply semax_pre with (PROPx [] (LOCALx Q (SEPx R)));
    [ apply andp_left2; apply andp_derives; [apply prop_derives; intros; exact I | apply derives_refl] | ] end.
  unfold hrx5_B8R_tl, hrx5_ptrs, hrx5_lvars, hrx5_scr5, hrx5_rest, hrx5_cglobs. cbn [app].
  unfold rxw_rep at 1. rewrite HFPS, HFT, HFKS, HFS.
  rewrite (hrx5_B8RBL_peers PS a Ews P Pz HSF).
  repeat flatten_sepcon_in_SEP.
  assert_PROP (isptr a) as Ha.
  { go_lower. sep_apply (hrx5_b8rbl_peer_isptr Ews a Pz). rewrite sepcon_andp_prop'.
    apply derives_extract_prop; intros Hx. apply prop_right; exact Hx. }
  sep_apply (hrx5_B8RBL_node_p _ _ (hrx5_head (hnodes_snapped4 T NS PS)) HNin). cbn [hn_p hn_addr]. Intros.
  forward.
  sep_apply (hrx5_B8RBL_mp (@field_at W Ews t_hnode4 [StructField HC._p] a tg)
    (hnodes_rep4 W (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS))).
  assert (HPzd: p_device Pz = l_wd L).
  { unfold Pz, hrx5_B8RB_Pz. rewrite Hsess. exact HDev. }
  assert (HPzs: p_cur Pz = rd_k d /\ p_prev Pz = nullval /\ p_next Pz = nullval).
  { unfold Pz, hrx5_B8RB_Pz. rewrite Hsess. repeat split. }
  assert (HSL: slots_ok Pz [(rd_k d, K)]).
  { unfold slots_ok. destruct HPzs as (-> & -> & ->). split.
    - constructor; [right; left; reflexivity|]. constructor; [left; reflexivity|].
      constructor; [left; reflexivity | constructor].
    - cbn [filter]. destruct (eq_dec (rd_k d) nullval); [contradiction|].
      destruct (eq_dec nullval nullval); [|congruence].
      constructor; [intros []|constructor]. }
  assert (HKP: kps_in_pool T3 a [(rd_k d, K)]).
  { split.
    - constructor; [intros []|constructor].
    - constructor; [|constructor]. eexists; split; [exact HFsk | reflexivity]. }
  forward_call (gv, shim_alloc_ok S1, rw_w W1, [(rd_k d, K)], T3, Ews, a, Pz, Tsh, l_wd L, rw_D W1, Tsh).
  rewrite HFclr, HFwarn. cbn [fst snd kw_S kw_KS kw_T].
  unfold shim_state4 at 1, shim_core at 1. Intros.
  cbn [s_frees shim_free shim_alloc_ok]. rewrite HGfr.
  rewrite (hrx5_b8rbl_tulong (cs1 := Noise.CS) (cs2 := W) Ews _ (gv _wg_shim_frees)).
  rewrite (hrx5_b8rbl_ss Tsh _ (l_ss L)).
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  forward. forward.
  forward_if.
  { exfalso. match goal with H: Int.repr (Z.b2z (Int64.eq _ _)) = Int.zero |- _ =>
      change (Int64.repr 1) with Int64.one in H; rewrite Int64.eq_true in H; apply Int.one_not_zero; exact H end. }
  forward. apply andp_left2. apply LOCALx_shuffle_derives. hrx5_b8rbl_sub.
  forward.
  { destruct (hrx5_RB x25519 gv L FR) as [r1 r2 r3 r4]. unfold loop2_ret_assert. cbn [RA_break RA_normal].
    apply ENTAIL_refl. }
  unfold POSTCONDITION, abbreviate, overridePost.
  destruct (hrx5_RB x25519 gv L FR) as [r1 r2 r3 r4]. cbn [RA_normal].
  rewrite HFx.
  apply andp_left2.
  unfold hrx5_B8R_tl, hrx5_ptrs, hrx5_lvars, hrx5_scr5, hrx5_rest, hrx5_cglobs. cbn [app].
  match goal with |- PROPx ?P1 (LOCALx ?Q1 (SEPx ?R1)) |-- PROPx ?P2 (LOCALx ?Q2 (SEPx ?R2)) =>
    apply derives_trans with (PROPx P1 (LOCALx Q2 (SEPx R1))); [apply LOCALx_shuffle_derives; hrx5_b8rbl_sub | ] end.
  apply andp_derives; [apply prop_derives; intros _; exact HP0 | ].
  apply andp_derives; [apply derives_refl | ].
  unfold rxw_rep at 1. cbn [rw_D rw_T rw_PS rw_KS rw_S rw_w rw_kc rw_lul rw_rx].
  rewrite (hrx5_B8RBL_peers PS a Ews P (hrx5_B8R_Pf d P M ck h) HSF).
  unfold shim_state4 at 1, shim_core at 1.
  match goal with H: shim_ok _ |- _ => rewrite (prop_true_andp (shim_ok _) _ H) end.
  cbn [s_frees shim_free shim_alloc_ok]. rewrite HGfr.
  rewrite (hrx5_b8rbl_tulong (cs1 := Noise.CS) (cs2 := W) Ews _ (gv _wg_shim_frees)).
  rewrite (hrx5_b8rbl_ss Tsh _ (l_ss L)).
  unfold keypairs_rep at 1. cbn [iter_sepcon].
  unfold SEPx. intro rho. cbn [fold_right_sepcon]. cancel.
Qed.
