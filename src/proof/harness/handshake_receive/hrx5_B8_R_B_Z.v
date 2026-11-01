(* law handshake_receive: B8 branch R segment B: Z = CHECK(hs_zeroed_from(s, h) && allocs + 1 && failures same).
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_Z_sep.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Lemma hrx5_B8RB_Z_ok : hrx5_B8RB_Z_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
    proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY.
  cbv beta zeta delta [hrx5_B8RB_Sa hrx5_B8R_St].
  unfold hrx5_Delta, hrx5_B8RB_Z.
  abbreviate_semax.
  match goal with |- semax _ (PROPx ?Pl _) _ _ => assert_PROP (fold_right and True Pl) as HP end.
  { apply andp_left2. unfold PROPx. apply andp_left1. apply derives_refl. }
  pose proof HP as HPall.
  rewrite !fold_right_and_app_low in HP.
  destruct HP as [HP0 [HG HFA]].
  unfold hrx5_B8RB_G in HG. unfold hrx5_B8RB_FA in HFA. cbn [fold_right] in HG, HFA.
  destruct HFA as (HFa & HFPS & HFT & HFKS & HFS & HFin & HFsf & HFz & HFx & _).
  destruct HG as (HG1 & HG2 & HG3 & HG4 & HG5 & HG6 & HG7 & HG8 & HG9 & HG10 & HG11 & HG12 & HG13 & HG14 & HG15
    & HGal & HGfa & HGfr & _).
  destruct HP0 as (Hbase & Hinv & _).
  destruct (hrx5_b8rbz_pok x25519 R L NS PS KE T head nk j a P Hinv HG6 HG7) as (Hnd & Hin & Hsid).
  set (W1 := hrx5_B8R_W1 x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6 port o
    dp d) in *.
  set (S1 := hrx5_B8RB_S1 x25519 R L sec birth S q lul o d) in *.
  set (Pz := hrx5_B8RB_Pz d P M ck h) in *.
  clearbody W1 S1 Pz.
  assert (Hcnt: s_allocs (rw_S W1) = Int64.add (s_allocs S) Int64.one /\ s_fails (rw_S W1) = s_fails S).
  { rewrite HFS. destruct (hrx5_B8R_sess d P); cbn [s_allocs s_fails shim_alloc_ok shim_free]; rewrite HGal, HGfa;
    auto. }
  assert (Hj': 0 <= j < Zlength (hnodes_snapped4 T NS PS)) by (rewrite hrx5_b8rbz_snapped_len; lia).
  pose proof (hrx5_b8rbz_nsnap _ j _ (hs_snap_cur T a P) (hrx5_head (hnodes_snapped4 T NS PS)) Hj' HG11 eq_refl)
    as HN.
  cbn [hn_addr] in HN.
  pose proof (hrx5_b8rbz_vp T (rw_T W1) a P Pz (l_wd L) (rw_D W1) HFz HG14 Hsid) as Hvp.
  unfold hrx5_B8R_tl, hrx5_ptrs, hrx5_lvars, hrx5_scr5, hrx5_rest, hrx5_cglobs. cbn [app].
  unfold rxw_rep at 1.
  repeat flatten_sepcon_in_SEP.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    apply semax_pre with (PROPx [] (LOCALx Q (SEPx R)));
    [ apply andp_left2; apply andp_derives; [apply prop_derives; intros; exact I | apply derives_refl] | ] end.
  destruct Hcnt as [Hc1 Hc2].
  replace_SEP 16 (@data_at HCS Ews t_hsnap (hsnap_val (hs_snap_cur T a P)) (offset_val 8 tg) *
    (@data_at HCS Ews t_hsnap (hsnap_val (hs_snap_cur T a P)) (offset_val 8 tg) -*
     hnodes_rep4 W (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS))).
  { go_lower. exact HN. }
  replace_SEP 3 (peer_rep Ews a Pz * (peer_rep Ews a Pz -* peers_rep (rw_PS W1))).
  { go_lower. exact (hrx5_b8rbz_peer PS (rw_PS W1) a P Pz Hnd Hin HFPS). }
  replace_SEP 5 ((data_at Ews tulong (Vlong (Int64.add (s_allocs S) Int64.one)) (gv _wg_shim_allocs) *
                  data_at Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures)) *
    ((data_at Ews tulong (Vlong (Int64.add (s_allocs S) Int64.one)) (gv _wg_shim_allocs) *
      data_at Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures)) -* shim_state4 gv (rw_S W1) (rw_w W1))).
  { go_lower. pose proof (hrx5_b8rbz_shim gv (rw_S W1) (rw_w W1)) as Hs. rewrite Hc1, Hc2 in Hs. exact Hs. }
  replace_SEP 28 (@data_at W Tsh t_shimsnap (shimsnap_val S w) (l_ss L)).
  { go_lower. rewrite hrx5_b8rbz_ss. apply derives_refl. }
  replace_SEP 0 (vobjs W [VDev Tsh (l_wd L) (rw_D W1)]).
  { go_lower. rewrite hrx5_b8rbz_dev. apply derives_refl. }
  replace_SEP 3 (hs_mem true Ews a Pz * (peer_rep Ews a Pz -* peers_rep (rw_PS W1))).
  { go_lower. apply derives_refl. }
  repeat flatten_sepcon_in_SEP.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { freeze [2;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;20;21;22;23;24;25;26;27;28;29;30;31;32;33;34;35;36;37;38;39;40;41;42;43;44] FR0.
    forward_call (Ews, offset_val 8 tg, hs_snap_cur T a P, Ews, a, Pz, true, Tsh, d_itab (rw_D W1), rw_T W1,
                  [VDev Tsh (l_wd L) (rw_D W1)]).
    { repeat constructor; simpl; auto. }
    thaw FR0.
    rewrite HFz.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HRM._t'176 (Vint Int.one) :: Q) (SEPx R))) end.
    { forward. forward. forward.
      assert (E: bool2val (Int64.cmpu Ceq (Int64.add (s_allocs S) Int64.one)
                   (Int64.add (s_allocs S) (Int64.repr (Int.signed (Int.repr 1))))) = Vint Int.one).
      { change (Int64.repr (Int.signed (Int.repr 1))) with Int64.one. unfold Int64.cmpu. rewrite Int64.eq_true.
        reflexivity. }
      rewrite E. apply andp_left2. apply LOCALx_shuffle_derives. intros q0 Hq.
      destruct Hq as [<-|[<-|Hq]]; [left; reflexivity | do 3 right; left; reflexivity | do 4 right; exact Hq]. }
    { exfalso. apply Int.one_not_zero. assumption. }
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HRM._t'177 (Vint Int.one) :: Q) (SEPx R))) end.
    { forward. forward. forward.
      assert (E: bool2val (Int64.cmpu Ceq (s_fails S) (s_fails S)) = Vint Int.one).
      { unfold Int64.cmpu. rewrite Int64.eq_true. reflexivity. }
      rewrite E. apply andp_left2. apply LOCALx_shuffle_derives. intros q0 Hq.
      destruct Hq as [<-|Hq]; [left; reflexivity | do 3 right; exact Hq]. }
    { exfalso. apply Int.one_not_zero. assumption. }
    forward_if.
    { exfalso. apply Int.one_not_zero. assumption. }
    forward.
    apply (hrx5_b8rbz_fin _ [] _ _ _ _ I); [intros q0 Hq; do 3 right; exact Hq | cbn [fold_right_sepcon]; cancel].
  }
  { forward. apply ENTAIL_refl. }
  unfold POSTCONDITION, abbreviate. unfold overridePost. destruct (hrx5_RB x25519 gv L FR) as [r1 r2 r3 r4].
  cbn [RA_normal].
  apply (hrx5_b8rbz_fin _ _ _ _ _ _ HPall).
  { intros q0 Hq. unfold hrx5_B8R_tl, hrx5_ptrs, hrx5_lvars in Hq. cbn [app] in Hq. exact Hq. }
  unfold rxw_rep, hrx5_rest, hrx5_cglobs, hrx5_scr5. cbn [app fold_right_sepcon].
  cbn [hs_mem].
  rewrite <- (hrx5_b8rbz_dev Tsh (l_wd L) (rw_D W1)).
  rewrite <- (hrx5_b8rbz_ss Tsh _ (l_ss L)).
  sep_apply (modus_ponens_wand (peer_rep Ews a Pz) (peers_rep (rw_PS W1))).
  sep_apply (modus_ponens_wand (@data_at HCS Ews t_hsnap (hsnap_val (hs_snap_cur T a P)) (offset_val 8 tg))
    (hnodes_rep4 W (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS))).
  match goal with |- context [?A -* shim_state4 ?g ?s ?w] => sep_apply (modus_ponens_wand A (shim_state4 g s w)) end.
  cancel.
Qed.
