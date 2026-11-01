(* law handshake_receive: B8 branch R segment B: C1 = CHECK(allocs same, frees same, failures + 1) of the failed allocation.
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
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

#[local] Instance hrx5_b8rbc1_cce_K : change_composite_env CKS W.
Proof. make_cs_preserve CKS W. Defined.

Lemma hrx5_b8rbc1_tulong {cs1 cs2: compspecs} sh v p :
  @data_at cs1 sh tulong v p = @data_at cs2 sh tulong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible; simpl.
  split; intros (?&?&?&?&?); (repeat split); auto;
    destruct p; try contradiction; unfold align_compatible in *;
    (apply align_compatible_rec_by_value with Mint64; [reflexivity|]);
    apply (align_compatible_rec_by_value_inv _ _ Mint64) in H2; auto.
Qed.

Lemma hrx5_b8rbc1_ss sh v p : @data_at CKS sh t_shimsnap v p = @data_at W sh t_shimsnap v p.
Proof.
  apply (f_equal (fun f => f p)). apply (@data_at_change_composite CKS W _ sh t_shimsnap); [apply JMeq_refl | reflexivity].
Qed.

(* Q' a sublist of Q, element by element (cheap: no intuition over 50 disjuncts) *)
Ltac hrx5_b8rbc1_sub :=
  let Q0 := fresh "Q0" in let HQ := fresh "HQ" in
  intros Q0 HQ; simpl In in HQ;
  repeat (destruct HQ as [<- | HQ]; [simpl In; repeat (first [left; reflexivity | right]) | ]);
  contradiction.

Ltac hrx5_b8rbc1_conj :=
  first [ exact I | assumption | split; hrx5_b8rbc1_conj ].

Lemma hrx5_B8RB_C1_ok : hrx5_B8RB_C1_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
    proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY.
  cbv beta zeta delta [hrx5_B8RB_Sf hrx5_B8R_St].
  unfold hrx5_Delta, hrx5_B8RB_C1.
  abbreviate_semax.
  match goal with |- semax _ (PROPx ?Pl _) _ _ => assert_PROP (fold_right and True Pl) as HP end.
  { apply andp_left2. unfold PROPx. apply andp_left1. apply derives_refl. }
  rewrite !fold_right_and_app_low in HP.
  destruct HP as [HP0 [HG HFF]].
  unfold hrx5_B8RB_G in HG. unfold hrx5_B8RB_FF in HFF. cbn [fold_right] in HG, HFF.
  destruct HFF as (HFa & HFT & HFPS & HFKS & HFS & HFx & _).
  destruct HG as (HG1 & HG2 & HG3 & HG4 & HG5 & HG6 & HG7 & HG8 & HG9 & HG10 & HG11 & HG12 & HG13 & HG14 & HG15
    & HGal & HGfa & HGfr & _).
  clear HP0.
  unfold hrx5_B8R_tl, hrx5_ptrs, hrx5_lvars, hrx5_scr5, hrx5_rest, hrx5_cglobs. cbn [app].
  unfold rxw_rep at 1. rewrite HFS. unfold shim_state4, shim_core.
  cbn [s_allocs s_fails s_frees shim_alloc_fail]. rewrite HGal, HGfa, HGfr.
  Intros.
  rewrite (hrx5_b8rbc1_tulong (cs1 := Noise.CS) (cs2 := W) Ews _ (gv _wg_shim_allocs)).
  rewrite (hrx5_b8rbc1_tulong (cs1 := Noise.CS) (cs2 := W) Ews _ (gv _wg_shim_alloc_failures)).
  rewrite (hrx5_b8rbc1_tulong (cs1 := Noise.CS) (cs2 := W) Ews _ (gv _wg_shim_frees)).
  rewrite (hrx5_b8rbc1_ss Tsh _ (l_ss L)).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    apply semax_pre with (PROPx [] (LOCALx Q (SEPx R)));
    [ apply andp_left2; apply andp_derives; [apply prop_derives; intros; exact I | apply derives_refl] | ] end.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  forward. forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HRM._t'150 (Vint Int.one) :: Q) (SEPx R))) end.
  { forward. forward. forward.
    unfold Int64.cmpu. rewrite Int64.eq_true. apply andp_left2. apply LOCALx_shuffle_derives.
    hrx5_b8rbc1_sub.
  }
  { match goal with H: ?x <> ?x |- _ => exfalso; exact (H eq_refl) end. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HRM._t'151 (Vint Int.one) :: Q) (SEPx R))) end.
  { forward. forward. forward.
    replace (Int64.repr (Int.signed (Int.repr 1))) with Int64.one by reflexivity.
    unfold Int64.cmpu. rewrite Int64.eq_true. apply andp_left2. apply LOCALx_shuffle_derives.
    hrx5_b8rbc1_sub.
  }
  { match goal with H: Int.one = Int.zero |- _ => exfalso; exact (Int.one_not_zero H) end. }
  forward_if.
  { match goal with H: Int.one = Int.zero |- _ => exfalso; exact (Int.one_not_zero H) end. }
  { forward. apply andp_left2. apply LOCALx_shuffle_derives. hrx5_b8rbc1_sub. }
  forward.
  { destruct (hrx5_RB x25519 gv L FR) as [r1 r2 r3 r4]. unfold loop2_ret_assert. cbn [RA_break RA_normal].
    apply ENTAIL_refl. }
  unfold POSTCONDITION, abbreviate, overridePost.
  destruct (hrx5_RB x25519 gv L FR) as [r1 r2 r3 r4]. cbn [RA_normal].
  apply andp_left2.
  unfold hrx5_B8R_tl, hrx5_ptrs, hrx5_lvars, hrx5_scr5, hrx5_rest, hrx5_cglobs. cbn [app].
  unfold rxw_rep at 1. rewrite HFS. unfold shim_state4, shim_core.
  rewrite (prop_true_andp (shim_ok _) _ H7).
  cbn [s_allocs s_fails s_frees shim_alloc_fail]. rewrite HGal, HGfa, HGfr.
  rewrite (hrx5_b8rbc1_tulong (cs1 := Noise.CS) (cs2 := W) Ews _ (gv _wg_shim_allocs)).
  rewrite (hrx5_b8rbc1_tulong (cs1 := Noise.CS) (cs2 := W) Ews _ (gv _wg_shim_alloc_failures)).
  rewrite (hrx5_b8rbc1_tulong (cs1 := Noise.CS) (cs2 := W) Ews _ (gv _wg_shim_frees)).
  rewrite (hrx5_b8rbc1_ss Tsh _ (l_ss L)).
  apply andp_derives; [apply prop_derives; intros _ | ].
  2: { apply andp_derives; [apply derives_refl |]. unfold SEPx. intro rho. cbn [fold_right_sepcon]. cancel. }
  cbn [fold_right]. rewrite !fold_right_and_app_low. unfold hrx5_B8RB_G, hrx5_B8RB_FF. cbn [fold_right].
  hrx5_b8rbc1_conj.
Qed.
