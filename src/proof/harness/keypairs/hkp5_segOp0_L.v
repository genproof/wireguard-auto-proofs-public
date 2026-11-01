(* law keypairs, segment Op0 branch L: the live branch hkp5_o0_sL (initiator,
   kp = the role's slot, CHECK(kp != NULL), CHECK(fresh counters), the node k filled and pushed on live, next_id,
   CHECK(r == snap.hashed && !p.handshake.entry.hashed), the shadow add_new_keypair with m_put). "Op0". *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.keypairs.hkp5_defs.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_defs.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_L_defs.
Require WgNoise.proof.harness.common.hc3_body_kdf.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_L_1.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_L_C.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_L_2a.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_L_2b.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_L_3.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_L_4i.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_L_4r.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

(* begin_session's result: hkp5_o0_live_fact instantiated *)
Lemma hkp5_o0L_facts_ok (F: hkp5_fix) (V: hkp5_val) (O: hkp5_o0) :
  hkp5_o0_live_fact -> p_dead (y_P (o_Y O)) = false ->
  hkp5_inv0 F V (o_Y O) -> s_boot (y_S (o_Y O)) = y_now (o_Y O) -> hs_ok (p_hs (y_P (o_Y O))) ->
  o_k O <> nullval -> ~ In (o_k O) (map fst (h5_ML (y_H (o_Y O)))) ->
  t_entry (y_T (o_Y O)) (hs_addr (f_p F)) = Some (o_E O) ->
  (o_kp O <> nullval -> ~ In (o_kp O) (saddrs (t_D (y_T (o_Y O)))) /\ ~ In (o_kp O) (map fst (y_KS (o_Y O)))) ->
  hkp5_o0_stok O = true -> o_kp O <> nullval ->
  hkp5_o0L_facts F V O.
Proof.
  intros HL Hd Hinv Hboot Hok Hk Hk2 HE Hkp Hst Hkp0.
  destruct (Hkp Hkp0) as [Hkp1 Hkp2].
  destruct Hinv as (Hrel & Hw & _ & _ & _ & Hfr & Hal & _).
  pose proof (HL (f_p F) (v_OD V) (v_OH V) (y_H (o_Y O)) (y_P (o_Y O)) (y_KS (o_Y O)) (y_T (o_Y O)) (y_S (o_Y O))
                (v_w0 V) (y_w (o_Y O)) (y_kc (o_Y O)) (o_kp O) (o_k O) (o_E O) _ _ Hrel Hw Hst Hd Hok Hkp0 Hkp1 Hkp2
                Hk Hk2 HE Hfr Hal) as X.
  cbv zeta in X. rewrite Hboot in X.
  destruct (WgNoise.proof.harness.common.hc3_body_kdf.hc3b_kdf_kdf_len (hs_ck (p_hs (y_P (o_Y O)))) [])
    as (L1 & L2 & _).
  destruct X as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
  exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj X7 (conj X8 (conj X9 (conj X10
    (conj X11 (conj X12 (conj X13 (conj X14 (conj X15 (conj X16 (conj L1 L2))))))))))))))))).
Qed.

(* the loop state after the live branch *)
Definition hkp5_o0L_Y (F: hkp5_fix) (O: hkp5_o0) : hkp5_dyn :=
  let res := o5_res (f_p F) O in
  mkKY5 (kw_S (snd (fst res))) (o5_w (f_p F) O) (snd res) (snd (fst (fst res))) (kw_KS (snd (fst res)))
    (kw_T (snd (fst res))) (hkp5_o0L_H3 F O) (y_now (o_Y O))
    (Int64.add (Int64.add (y_kc (o_Y O)) Int64.one) Int64.one) true (y_hsn (o_Y O)).

Lemma hkp5_o0L_inv (F: hkp5_fix) (V: hkp5_val) (O: hkp5_o0) :
  hkp5_o0L_facts F V O -> hkp5_inv0 F V (o_Y O) -> hkp5_inv0 F V (hkp5_o0L_Y F O).
Proof.
  intros FA Hinv.
  destruct FA as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & L1 & L2).
  destruct Hinv as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10).
  unfold hkp5_inv0, hkp5_o0L_Y. cbn [y_S y_w y_kc y_P y_KS y_T y_H y_now y_next_id y_id_known y_hsn].
  refine (conj X13 (conj X14 (conj _ (conj _ (conj _ (conj X15 (conj X16 (conj _ (conj I9 _))))))))).
  - rewrite X4. exact I3.
  - rewrite X3. exact I4.
  - rewrite X5. exact I5.
  - intros _. rewrite X2. reflexivity.
  - rewrite (hk5_prsnap_val_pknext _ _ X6). exact I10.
Qed.

(* hbytes of 32 bytes is an output buffer *)
Lemma hkp5_o0L_hout sh bs p : Zlength bs = 32 -> hbytes sh bs p |-- hout sh 32 p.
Proof. intros L. unfold hbytes, hout. rewrite L. apply data_at_data_at_. Qed.

(* the end: the loop state (but hsm) with begin_session's result and the harness's update *)
Lemma hkp5_o0L_fin x25519 (F: hkp5_fix) (FR: mpred) V steps i (O: hkp5_o0) :
  hkp5_o0L_facts F V O ->
  local (tc_environ (hkp5_Delta hkp5_G_Op0)) && hkp5_o0L_3 x25519 F V steps FR i O |--
    hkp5_o0_Z x25519 F V steps FR i.
Proof.
  intros FA.
  unfold hkp5_o0L_3, hkp5_o0_Z.
  Exists (hkp5_o0L_Y F O).
  unfold hkp5_o0L_props, hkp5_o0_props, hkp5_o0L_locals2, hkp5_o0L_SEP, hkp5_o0L_fs, hkp5_temps, hkp5_SEP,
    hkp5_world, hkp5_hglobs.
  cbn [app]. Intros.
  match goal with H: hkp5_inv0 _ _ (o_Y O) |- _ => assert (Hinv' := hkp5_o0L_inv F V O FA H) end.
  destruct FA as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & L1 & L2).
  unfold hkp5_o0L_Y. cbn [y_S y_w y_kc y_P y_KS y_T y_H y_now y_next_id y_id_known y_hsn].
  unfold hkp5_o0L_Y in Hinv'.
  rewrite X6.
  unfold hk5_items, hkp5_globs, hkp5_lvars. cbn [app].
  sep_apply (hkp5_o0L_hout Tsh (kdf1 (hs_ck (p_hs (y_P (o_Y O)))) []) (f_first F) L1).
  sep_apply (hkp5_o0L_hout Tsh (kdf2 (hs_ck (p_hs (y_P (o_Y O)))) []) (f_second F) L2).
  sep_apply (@data_at_data_at_ HCS Tsh t_hsnap (hsnap_val (o5_sn (f_p F) O)) (f_snap F)).
  entailer!.
Qed.

Lemma hkp5_segOp0_L_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps FR i R (O: hkp5_o0) :
  hkp5_model_facts -> x25519_props x25519 -> hkp5_o0_live_fact -> p_dead (y_P (o_Y O)) = false ->
  semax (hkp5_Delta hkp5_G_Op0) (hkp5_o0_M2 x25519 F V steps FR i O) hkp5_o0_sL
    (overridePost (hkp5_o0_Z x25519 F V steps FR i) R).
Proof.
  intros HF HX HL Hd.
  assert (FA0: hkp5_o0_M2 x25519 F V steps FR i O |-- !! hkp5_o0L_facts F V O).
  { unfold hkp5_o0_M2, hkp5_o0_props, PROPx. cbv zeta. apply andp_left1. apply prop_derives.
    cbn [fold_right app].
    intros (_ & _ & Hinv & _ & Hboot & _ & Hok & Hk & Hk2 & HE & _ & Hkp & Hst & Hkp0 & _).
    apply hkp5_o0L_facts_ok; assumption. }
  apply semax_pre with (P' := (!! hkp5_o0L_facts F V O && hkp5_o0_M2 x25519 F V steps FR i O)%logic).
  { apply andp_left2. apply andp_right; [apply FA0 | apply derives_refl]. }
  apply semax_extract_prop. intros FA. clear FA0.
  pose proof hkp5_o0L_shape as (E0 & E1 & E2 & E3 & E4).
  rewrite E0.
  eapply hkp5_semax_cut; [discriminate | rewrite <- E1; apply hkp5_o0L_1_ok; auto |].
  eapply semax_seq; [apply hkp5_o0L_C_ok; auto |].
  eapply hkp5_semax_cut; [discriminate | rewrite <- E2; apply hkp5_o0L_2a_ok; auto |].
  eapply hkp5_semax_cut; [discriminate | rewrite <- E3; apply hkp5_o0L_2b_ok; auto |].
  eapply semax_seq; [apply hkp5_o0L_3_ok; auto |].
  destruct R as [Rn Rb Rc Rr].
  apply semax_post with (R' := overridePost (hkp5_o0L_3 x25519 F V steps FR i O)
    (overridePost (hkp5_o0_Z x25519 F V steps FR i) (Build_ret_assert Rn Rb Rc Rr))).
  { unfold overridePost. apply hkp5_o0L_fin; exact FA. }
  all: try (unfold overridePost; intros; apply andp_left2; apply derives_refl).
  destruct (hkp5_o0L_init O) eqn:Ei.
  - apply hkp5_o0L_4i_ok; auto.
  - apply hkp5_o0L_4r_ok; auto.
Qed.
