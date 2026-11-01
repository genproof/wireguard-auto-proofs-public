(* law handshake_receive: phase B8, branch I
   of statement 41. *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_I_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_I_pure.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_I_I0.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_I_I1.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_I_I2.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_I_I3.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_I_I4.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_I_fold.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

(* the last segment with the fold to the loop's state *)
Lemma hrx5_B8I_I4f {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR
    R sec birth S w NS PS T head nk KE st i kc q proto ip4 ip6 port M dp img a P t ck2 h2 key spub sec1 birth1
    S1 lul1 :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B8I_QI x25519 aead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc q proto ip4 ip6 port M dp img
       a P t ck2 h2 key spub sec1 birth1 S1 lul1)
    hrx5_B8I_I4 (overridePost (hrx5_S8 x25519 gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HY.
  eapply semax_post; [| | | | exact (hrx5_B8I_I4_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR
    R sec birth S w NS PS T head nk KE st i kc q proto ip4 ip6 port M dp img a P t ck2 h2 key spub sec1 birth1
    S1 lul1 HY)].
  - intros rho. unfold overridePost at 1 2. cbn [RA_normal].
    apply (hrx5_B8I_fold_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR
      R sec birth S w NS PS T head nk KE st i kc q proto ip4 ip6 port M dp img a P t ck2 h2 key spub sec1 birth1
      S1 lul1 HY).
  - intros rho. destruct (hrx5_RB x25519 gv L FR); cbn. apply andp_left2, derives_refl.
  - intros rho. destruct (hrx5_RB x25519 gv L FR); cbn. apply andp_left2, derives_refl.
  - intros v rho. destruct (hrx5_RB x25519 gv L FR); cbn. apply andp_left2, derives_refl.
Qed.

Lemma hrx5_B8_I_ok : hrx5_B8_I_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul
    q proto ip4 ip6 port o dp img tg ai ar d HY (Hpath & Hk & Hai).
  unfold hrx5_B8_path in Hpath.
  pose proof (hrx5_B8I_path_fwd _ _ _ _ _ Hpath) as Hfwd.
  unfold hrx5_B8_Q.
  match goal with |- semax _ ?P _ _ => let P' := eval cbv zeta in P in change P with P' end.
  rewrite Hpath.
  Intros.
  match goal with H: hrx5_acc_ok _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (hrx5_B8I_case x25519 aead_dec xaead_dec _ _ _ _ _ _ _ _ _ H Hk Hai Hfwd)
      as (M & a & P & t & ck2 & h2 & -> & -> & -> & Ht) end.
  cbn [obj_bytes obj_ok obj_rep hrx5_ptrs obj_kind] in *.
  match goal with H1: hrx5_base_ok _ _ _ _, H2: hrx5_inv _ _ _ _ _ _ _ _ _, H3: im_ok _, H4: rxdraw_ok _ _ |- _ =>
    destruct (hrx5_B8I_model x25519 aead_dec xaead_enc xaead_dec L R sec birth S w NS PS T head nk KE kc lul q proto
      ip4 ip6 port dp M d a P t ck2 h2 H1 H2 H3 H4 Hpath Ht) as (sec1 & birth1 & S1 & HW & Hb1 & HS1 & HSe & _) end.
  rewrite HW. cbn [rw_D rw_T rw_PS rw_KS rw_S rw_w rw_kc rw_lul rw_rx].
  subst ai.
  unfold hrx5_scr5, hrx5_ci_rep, hrx5_st_rep, hrx5_pt_rep, hrx5_ptrs. cbv beta iota. cbn [obj_bytes].
  rewrite Hfwd, Ht.
  unfold hrx5_rest, hrx5_cglobs. cbn [app]. Intros key spub.
  apply hrx5_B8I_cut with
    (hrx5_B8I_QI x25519 aead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc q proto ip4 ip6 port M dp img
       a P t ck2 h2 key spub sec1 birth1 S1 (snd (load_model q lul (s_boot S)))).
  - eapply semax_pre; [| exact (hrx5_B8I_I0_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR
      R sec birth S w NS PS T head nk KE st i kc q proto ip4 ip6 port M dp img a P t ck2 h2 key spub sec1 birth1
      S1 (snd (load_model q lul (s_boot S))) HY)].
    unfold hrx5_B8I_QI0, hrx5_B8I_props, hrx5_B8I_temps, hrx5_B8I_world, hrx5_B8I_scr, rxw_rep, hrx5_rest,
      hrx5_cglobs.
    cbn [app keypairs_rep iter_sepcon rw_D rw_T rw_PS rw_KS rw_S rw_w rw_kc rw_lul rw_rx].
    change (d_itab (hrx5_DL x25519 R L sec1 birth1)) with (l_itd L).
    change (d_ptab (hrx5_DL x25519 R L sec1 birth1)) with (l_ptd L).
    rewrite sepcon_emp. repeat flatten_sepcon_in_SEP.
    unfold hrx5_lvars. entailer!.
  - exact (hrx5_B8I_I1_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR
      R sec birth S w NS PS T head nk KE st i kc q proto ip4 ip6 port M dp img a P t ck2 h2 key spub sec1 birth1
      S1 (snd (load_model q lul (s_boot S))) HY).
  - exact (hrx5_B8I_I2_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR
      R sec birth S w NS PS T head nk KE st i kc q proto ip4 ip6 port M dp img a P t ck2 h2 key spub sec1 birth1
      S1 (snd (load_model q lul (s_boot S))) HY).
  - exact (hrx5_B8I_I3_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR
      R sec birth S w NS PS T head nk KE st i kc q proto ip4 ip6 port M dp img a P t ck2 h2 key spub sec1 birth1
      S1 (snd (load_model q lul (s_boot S))) HY).
  - exact (hrx5_B8I_I4f x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR
      R sec birth S w NS PS T head nk KE st i kc q proto ip4 ip6 port M dp img a P t ck2 h2 key spub sec1 birth1
      S1 (snd (load_model q lul (s_boot S))) HY).
Qed.
