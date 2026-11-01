(* law keypairs: operation 0 of the loop body (hkp5_sOp0). *)
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
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_A.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_W.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_Fl.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_S.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_D.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_L.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_live.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

(* statement 14: hs_take(&hsm, &p.handshake) re-establishes hk5_hsm_ok *)
Lemma hkp5_o0_s14_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps FR i R :
  semax (hkp5_Delta hkp5_G_Op0) (hkp5_o0_Z x25519 F V steps FR i) hkp5_o0_s14
    (loop1_ret_assert (hkp5_Icont x25519 F V steps FR i) R).
Proof.
  unfold hkp5_o0_Z. Intros Y.
  destruct R as [Rn Rb Rc Rr]. unfold loop1_ret_assert.
  destruct F as [gv w t pt p raw pub snap opub first second].
  destruct Y as [S ws kc P KS T HH now next_id id_known hsn].
  unfold hkp5_SEP, hkp5_world, hkp5_hglobs, hkp5_globs, hk5_items, hkp5_temps, hkp5_lvars.
  cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second y_S y_w y_kc y_P y_KS y_T y_H y_now
       y_next_id y_id_known y_hsn].
  pose proof H1 as Hinv0.
  destruct H1 as (Hrel & Hwarn & Hdev & Hsid & Hrefs & Hfr & Hal & Hid & Hnow).
  cbn [y_P y_H y_KS y_T y_S y_kc y_now y_next_id y_id_known f_w f_p] in Hrel, Hdev, Hsid.
  pose proof Hrel as ((_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & (idx & Hhs) & _)) & _).
  set (E := mkEntry p IDX_HANDSHAKE idx) in *.
  assert (HtE: t_entry T (hs_addr p) = Some E) by (unfold t_entry; rewrite Hhs; reflexivity).
  assert_PROP (@field_compatible Noise.CS t_peer [] p) as Hfcp by (unfold peer_rep; entailer!).
  assert_PROP (isptr w) as Pw by (unfold device_rep; entailer!).
  assert (Pp: isptr p) by (destruct Hfcp; auto).
  unfold hkp5_o0_s14, hkp5_Delta. abbreviate_semax.
  sep_apply (@data_at_data_at_ HCS Ews t_hsnap (hsnap_val hsn) (gv KC._hsm)).
  forward_call (Ews, gv KC._hsm, Tsh, p, P, Tsh, t, T, E).
  { split; [unfold E; cbn [e_peer]; destruct p; try contradiction; discriminate |].
    rewrite Hsid. unfold id_addr. destruct w; try contradiction; discriminate. }
  unfold hkp5_Icont, hkp5_St.
  Exists (mkKY5 S ws kc P KS T HH now next_id id_known (snap_of T (hs_addr p) E (p_hs P))).
  unfold hkp5_SEP, hkp5_world, hkp5_hglobs, hkp5_globs, hk5_items, hkp5_temps, hkp5_lvars.
  cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second y_S y_w y_kc y_P y_KS y_T y_H y_now
       y_next_id y_id_known y_hsn].
  entailer!.
  apply hkp5_inv_split. split; [exact Hinv0 |].
  split; [exact HtE | split; reflexivity].
Qed.

Lemma hkp5_o0_tulong_cs {cs1 cs2: compspecs} sh v p :
  @data_at cs1 sh tulong v p = @data_at cs2 sh tulong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible; simpl.
  split; intros (?&?&?&?&?); (repeat split); auto;
    destruct p; try contradiction; unfold align_compatible in *;
    (apply align_compatible_rec_by_value with Mint64; [reflexivity|]);
    apply (align_compatible_rec_by_value_inv _ _ Mint64) in H2; auto.
Qed.

Lemma hkp5_o0_shim_fold gv S : shim_ok S ->
  (@data_at Noise.CS Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
   @data_at Noise.CS Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
   @data_at Noise.CS Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
   @data_at Noise.CS Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
   @data_at Noise.CS Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   @data_at Noise.CS Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
   @data_at Noise.CS Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   @data_at Noise.CS Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow))%logic
  |-- shim_core gv S.
Proof. intros H. unfold shim_core. apply andp_right; [apply prop_right; exact H | apply derives_refl]. Qed.

(* begin_session's allocation counters in the success cases (dead: by unfolding; live: hkp5_o0_live_fact) *)
Lemma hkp5_o0_succ_shim (F: hkp5_fix) (V: hkp5_val) (O: hkp5_o0) :
  hkp5_o0_live_fact -> hkp5_inv0 F V (o_Y O) -> hs_ok (p_hs (y_P (o_Y O))) ->
  o_k O <> nullval -> ~ In (o_k O) (map fst (h5_ML (y_H (o_Y O)))) ->
  t_entry (y_T (o_Y O)) (hs_addr (f_p F)) = Some (o_E O) ->
  (o_kp O <> nullval -> ~ In (o_kp O) (saddrs (t_D (y_T (o_Y O)))) /\ ~ In (o_kp O) (map fst (y_KS (o_Y O)))) ->
  hkp5_o0_stok O = true -> o_kp O <> nullval ->
  s_fails (kw_S (snd (fst (o5_res (f_p F) O)))) = s_fails (y_S (o_Y O)).
Proof.
  intros HL Hinv Hok Hk Hk2 HE Hkp Hst Hkp0.
  destruct (Hkp Hkp0) as [Hkp1 Hkp2].
  unfold o5_res. destruct (p_dead (y_P (o_Y O))) eqn:Ed.
  - rewrite hkp5_o0_res_dead by auto. reflexivity.
  - destruct Hinv as (Hrel & Hw & _ & _ & _ & Hfr & Hal & _).
    pose proof (HL (f_p F) _ _ (y_H (o_Y O)) (y_P (o_Y O)) (y_KS (o_Y O)) (y_T (o_Y O)) (y_S (o_Y O)) _ _
                  (y_kc (o_Y O)) (o_kp O) (o_k O) (o_E O) _ _ Hrel Hw Hst Ed Hok Hkp0 Hkp1 Hkp2 Hk Hk2 HE Hfr Hal)
      as X.
    cbv zeta in X. destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf & _). exact Hf.
Qed.

Lemma hkp5_o0_fail_shim (F: hkp5_fix) (O: hkp5_o0) :
  hkp5_o0_stok O = true -> o_kp O = nullval ->
  s_fails (kw_S (snd (fst (o5_res (f_p F) O)))) = Int64.add (s_fails (y_S (o_Y O))) Int64.one.
Proof. intros Hst Hkp. unfold o5_res. rewrite Hkp, hkp5_o0_res_fail by exact Hst. reflexivity. Qed.

Lemma hkp5_o0_add_one_neq x : Int64.add x Int64.one <> x.
Proof.
  intros E. apply (f_equal Int64.unsigned) in E. unfold Int64.add in E.
  rewrite Int64.unsigned_one in E. pose proof (Int64.unsigned_range x) as Rx.
  destruct (zeq (Int64.unsigned x + 1) Int64.modulus) as [Em | Em].
  - rewrite Em in E. change (Int64.unsigned (Int64.repr Int64.modulus)) with 0 in E.
    rewrite <- E in Em. vm_compute in Em. discriminate.
  - rewrite Int64.unsigned_repr in E by (unfold Int64.max_unsigned; lia). lia.
Qed.

(* statement 13: t'34 = st != 3 && st != 4; the branches *)
Lemma hkp5_o0_B {Espec: OracleKind} x25519 (F: hkp5_fix) V steps FR i R (O: hkp5_o0) :
  hkp5_model_facts -> x25519_props x25519 -> hkp5_o0_live_fact ->
  semax (hkp5_Delta hkp5_G_Op0) (hkp5_o0_M x25519 F V steps FR i O) hkp5_o0_s13
    (overridePost (hkp5_o0_Z x25519 F V steps FR i) R).
Proof.
  intros HF HX HL.
  pose proof hkp5_o0_shape as (_ & _ & E13 & E13a & E13b & _ & Hne & _).
  rewrite E13, E13a, E13b.
  unfold hkp5_o0_M, hkp5_Delta.
  destruct R as [Rn Rb Rc Rr]. unfold overridePost.
  unfold hkp5_o0_props, hkp5_o0_locals, hkp5_o0_SEP, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
  cbv zeta. cbn [app].
  abbreviate_semax.
  set (st := hs_state (p_hs (y_P (o_Y O)))).
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
    forward_if (PROPx P (LOCALx (temp KC._t'34 (Vint (if orb (Int.eq st HS_CREATED_RESPONSE)
      (Int.eq st HS_CONSUMED_RESPONSE) then Int.zero else Int.one)) :: L) (SEPx S))) end.
  { forward. entailer!. unfold HS_CREATED_RESPONSE, HS_CONSUMED_RESPONSE. rewrite (Int.eq_false _ _ H).
    destruct (Int.eq st (Int.repr 4)); reflexivity. }
  { forward. entailer!. unfold HS_CREATED_RESPONSE. rewrite H, Int.eq_true. reflexivity. }
  Intros.
  forward_if.
  { (* wrong state *)
    assert (Hst: hkp5_o0_stok O = false).
    { unfold hkp5_o0_stok. fold st. destruct (orb _ _); [contradiction | reflexivity]. }
    unfold POSTCONDITION, abbreviate.
    eapply semax_pre; [| apply (hkp5_segOp0_W_ok x25519 F V steps FR i (Build_ret_assert Rn Rb Rc Rr) O HF HX Hst)].
    unfold hkp5_o0_M, hkp5_o0_props, hkp5_o0_locals, hkp5_o0_SEP, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps,
      hkp5_lvars.
    cbv zeta. cbn [app].
    entailer!. }
  assert (Hst: hkp5_o0_stok O = true).
  { unfold hkp5_o0_stok. fold st. destruct (orb _ _) eqn:Eo; [reflexivity | exfalso; apply Int.one_not_zero; assumption]. }
  set (S' := kw_S (snd (fst (o5_res (f_p F) O)))).
  unfold shim_state4 at 1, shim_core at 1. Intros.
  rewrite (@hkp5_o0_tulong_cs Noise.CS W_keypairs _ _ (f_gv F _wg_shim_alloc_failures)).
  change _wg_shim_alloc_failures with KC._wg_shim_alloc_failures.
  forward.
  rewrite (@hkp5_o0_tulong_cs W_keypairs Noise.CS _ _ (f_gv F KC._wg_shim_alloc_failures)).
  change KC._wg_shim_alloc_failures with _wg_shim_alloc_failures.
  match goal with H: shim_ok S' |- _ => rename H into HSok end.
  sep_apply (hkp5_o0_shim_fold (f_gv F) S' HSok).
  match goal with H: hkp5_inv0 _ _ _ |- _ => rename H into Hinv end.
  forward_if.
  { (* the allocation failed *)
    assert (Hkp: o_kp O = nullval).
    { destruct (eq_dec (o_kp O) nullval) as [E | E]; [exact E | exfalso].
      match goal with Hn: s_fails S' <> _ |- _ => apply Hn end.
      unfold S'. apply (hkp5_o0_succ_shim F V O HL Hinv); auto. }
    unfold POSTCONDITION, abbreviate.
    eapply semax_pre; [| apply (hkp5_segOp0_Fl_ok x25519 F V steps FR i (Build_ret_assert Rn Rb Rc Rr) O HF HX Hst Hkp)].
    unfold S' in *. clear S'.
    unfold hkp5_o0_M, hkp5_o0_props, hkp5_o0_locals, hkp5_o0_SEP, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps,
      hkp5_lvars.
    cbv zeta. cbn [app]. unfold shim_state4.
    entailer!. }
  assert (Hkp: o_kp O <> nullval).
  { intros E. pose proof (hkp5_o0_fail_shim F O Hst E) as Hf. unfold S' in *. rewrite Hf in *.
    apply (hkp5_o0_add_one_neq (s_fails (y_S (o_Y O)))).
    match goal with Hq: Int64.eq _ _ = true |- _ => apply Int64.same_if_eq; exact Hq end. }
  unfold POSTCONDITION, abbreviate.
  unfold S' in *. clear S'.
  eapply hkp5_semax_cut; [exact Hne | |].
  { eapply semax_pre; [| apply (hkp5_segOp0_S_ok x25519 F V steps FR i (Build_ret_assert Rn Rb Rc Rr) O HF HX HL Hst Hkp)].
    unfold hkp5_o0_M, hkp5_o0_props, hkp5_o0_locals, hkp5_o0_SEP, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps,
      hkp5_lvars.
    cbv zeta. cbn [app]. unfold shim_state4.
    entailer!. }
  unfold hkp5_o0_M2.
  unfold hkp5_o0_props, hkp5_o0_locals, hkp5_o0_SEP, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
  cbv zeta. cbn [app].
  abbreviate_semax.
  forward_if.
  { assert (Hd: p_dead (y_P (o_Y O)) = true).
    { match goal with Ht: typed_true _ _ |- _ => destruct (p_dead (y_P (o_Y O))); [reflexivity | inv Ht] end. }
    eapply semax_pre; [| apply (hkp5_segOp0_D_ok x25519 F V steps FR i (Build_ret_assert Rn Rb Rc Rr) O HF HX Hd)].
    unfold hkp5_o0_M2, hkp5_o0_props, hkp5_o0_locals, hkp5_o0_SEP, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps,
      hkp5_lvars.
    cbv zeta. cbn [app].
    entailer!. }
  { assert (Hd: p_dead (y_P (o_Y O)) = false).
    { match goal with Ht: typed_false _ _ |- _ => destruct (p_dead (y_P (o_Y O))); [inv Ht | reflexivity] end. }
    eapply semax_pre; [| apply (hkp5_segOp0_L_ok x25519 F V steps FR i (Build_ret_assert Rn Rb Rc Rr) O HF HX HL Hd)].
    unfold hkp5_o0_M2, hkp5_o0_props, hkp5_o0_locals, hkp5_o0_SEP, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps,
      hkp5_lvars.
    cbv zeta. cbn [app].
    entailer!. }
Qed.

Lemma hkp5_segOp0_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps FR i R :
  hkp5_model_facts -> x25519_props x25519 ->
  semax (hkp5_Delta hkp5_G_Op0) (hkp5_PL0 x25519 F V steps FR i 0) hkp5_sOp0
    (loop1_ret_assert (hkp5_Icont x25519 F V steps FR i) R).
Proof.
  intros HF HX.
  pose proof hkp5_o0_shape as (E0 & EA & _ & _ & _ & _ & _ & HneA).
  rewrite E0.
  eapply hkp5_semax_cut; [exact HneA | rewrite <- EA; apply hkp5_segOp0_A_ok; auto |].
  eapply semax_seq.
  - apply extract_exists_pre. intros O.
    apply hkp5_o0_B; auto.
    apply hkp5_segOp0_live_ok. exact HF.
  - apply hkp5_o0_s14_ok.
Qed.
