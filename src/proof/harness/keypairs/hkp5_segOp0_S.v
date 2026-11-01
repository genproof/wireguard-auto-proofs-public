(* law keypairs, segment Op0 part S: the success prefix hkp5_o0_sS (kp = NULL;
   CHECK(allocs == a0 + 1); m_transport(first, second, snap.chaining_key); CHECK(hs_zeroed_from(&snap, &p.handshake))).
   "Op0". *)
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
Require Import WgNoise.proof.harness.common.hc3_cs.
Require WgNoise.proof.harness.common.hc3_body_snap.
Require Import WgNoise.proof.harness.keypairs.hkp5_zfspec.

Module HB := WgNoise.proof.harness.common.hc3_body_snap.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

(* ---- helpers (prefix hkp5_o0S_) ---- *)

Lemma hkp5_o0S_bytes_eqb_refl (a: list byte) : bytes_eqb a a = true.
Proof. unfold bytes_eqb; destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

Lemma hkp5_o0S_tulong_cs {cs1 cs2: compspecs} sh v p :
  @data_at cs1 sh tulong v p = @data_at cs2 sh tulong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible; simpl.
  split; intros (?&?&?&?&?); (repeat split); auto;
    destruct p; try contradiction; unfold align_compatible in *;
    (apply align_compatible_rec_by_value with Mint64; [reflexivity|]);
    apply (align_compatible_rec_by_value_inv _ _ Mint64) in H2; auto.
Qed.

(* the shim's globals other than the allocation counter *)
Definition hkp5_o0S_srest (gv: globals) (S: shim) : mpred :=
  !! shim_ok S &&
  (@data_at Noise.CS Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
   @data_at Noise.CS Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
   @data_at Noise.CS Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
   @data_at Noise.CS Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
   @data_at Noise.CS Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
   @data_at Noise.CS Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   @data_at Noise.CS Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow)).

Lemma hkp5_o0S_shim gv S w : shim_state4 gv S w =
  (@data_at W_keypairs Ews tulong (Vlong (s_allocs S)) (gv KC._wg_shim_allocs) * hkp5_o0S_srest gv S *
   refwarn4 gv w).
Proof.
  unfold shim_state4, shim_core, hkp5_o0S_srest.
  rewrite <- (@hkp5_o0S_tulong_cs Noise.CS W_keypairs).
  change KC._wg_shim_allocs with _wg_shim_allocs.
  apply pred_ext; Intros; entailer!.
Qed.

Lemma hkp5_o0S_wgc_fold gv :
  spec.blake2s_globals gv * @curve25519_globals Noise.CS gv * @zero_page Noise.CS gv * cookie_globals gv
  |-- wg_consts gv.
Proof. unfold wg_consts. apply derives_refl. Qed.

(* begin_session's result in the success cases: the handshake zeroed, its entry kept, one allocation more
   (dead: by unfolding; live: hkp5_o0_live_fact) *)
Lemma hkp5_o0S_res (F: hkp5_fix) (V: hkp5_val) (O: hkp5_o0) :
  hkp5_o0_live_fact -> hkp5_inv0 F V (o_Y O) -> hs_ok (p_hs (y_P (o_Y O))) ->
  o_k O <> nullval -> ~ In (o_k O) (map fst (h5_ML (y_H (o_Y O)))) ->
  t_entry (y_T (o_Y O)) (hs_addr (f_p F)) = Some (o_E O) ->
  (o_kp O <> nullval -> ~ In (o_kp O) (saddrs (t_D (y_T (o_Y O)))) /\ ~ In (o_kp O) (map fst (y_KS (o_Y O)))) ->
  hkp5_o0_stok O = true -> o_kp O <> nullval ->
  p_hs (snd (fst (fst (o5_res (f_p F) O)))) = hs_zero (p_hs (y_P (o_Y O))) /\
  t_entry (kw_T (snd (fst (o5_res (f_p F) O)))) (hs_addr (f_p F)) = Some (o_E O) /\
  s_allocs (kw_S (snd (fst (o5_res (f_p F) O)))) = Int64.add (s_allocs (y_S (o_Y O))) Int64.one.
Proof.
  intros HL Hinv Hok Hk Hk2 HE Hkp Hst Hkp0.
  destruct (Hkp Hkp0) as [Hkp1 Hkp2].
  unfold hkp5_o0_stok in Hst.
  unfold o5_res. destruct (p_dead (y_P (o_Y O))) eqn:Ed.
  - rewrite hkp5_o0_res_dead by auto. cbn [fst snd kw_T kw_S]. split; [reflexivity |]. split; [exact HE | reflexivity].
  - destruct Hinv as (Hrel & Hw & _ & _ & _ & Hfr & Hal & _).
    pose proof (HL (f_p F) (v_OD V) (v_OH V) (y_H (o_Y O)) (y_P (o_Y O)) (y_KS (o_Y O)) (y_T (o_Y O))
                  (y_S (o_Y O)) (v_w0 V) (y_w (o_Y O)) (y_kc (o_Y O))
                  (o_kp O) (o_k O) (o_E O) _ _ Hrel Hw Hst Ed Hok Hkp0 Hkp1 Hkp2 Hk Hk2 HE Hfr Hal) as X.
    cbv zeta in X. destruct X as (_ & _ & Hhs & _ & _ & _ & _ & _ & HE' & _ & Ha & _).
    split; [exact Hhs |]. split; [exact HE' | exact Ha].
Qed.

(* the handshake's entry belongs to p (hk5_pool) *)
Lemma hkp5_o0S_epeer p OD OH KS T E :
  hk5_pool p OD OH KS T -> t_entry T (hs_addr p) = Some E -> e_peer E = p.
Proof.
  intros Hpool HE.
  destruct Hpool as (_ & _ & _ & _ & (idx & Hf) & _).
  unfold t_entry in HE. rewrite Hf in HE. inv HE. reflexivity.
Qed.

(* hs_zeroed_from's precondition and result after begin_session *)
Lemma hkp5_o0S_cmp T T' p w Hs P' E :
  t_entry T' (hs_addr p) = Some E -> e_peer E = p -> hs_sid Hs = id_addr w -> p_hs P' = hs_zero Hs ->
  hk5_cmp_pre (snap_of T (hs_addr p) E Hs) T' p w P' E.
Proof.
  intros HE Ep Hsid Hz. unfold hk5_cmp_pre, snap_of. cbn [sn_entry sn_hs].
  rewrite Hz. unfold hs_zero. cbn [hs_sid]. auto.
Qed.

Lemma hkp5_o0S_zf T T' a E Hs :
  zeroed_from (snap_of T a E Hs) (snap_of T' a E (hs_zero Hs)) = true.
Proof.
  unfold zeroed_from, snap_of, hs_zero. cbn [sn_entry sn_hs hs_state hs_rindex hs_eph hs_reph hs_hash hs_ck
    hs_lic hs_sid hs_rstatic hs_ss hs_psk hs_ts].
  rewrite !Int.eq_true, !Int64.eq_true, !hkp5_o0S_bytes_eqb_refl.
  assert (Z0: is_zero (zeros 32) = true) by (vm_compute; reflexivity). rewrite Z0.
  rewrite !if_true by reflexivity.
  reflexivity.
Qed.

(* the snapshot's chaining key as a byte buffer (m_transport's third argument), the rest kept in a wand *)
Lemma hkp5_o0S_wand_gen (A B R: mpred) : (B |-- A * R) -> (R * A |-- B) -> (B |-- A * (A -* B)).
Proof.
  intros H1 H2. eapply derives_trans; [exact H1 |]. apply sepcon_derives; [apply derives_refl |].
  apply wand_sepcon_adjoint. exact H2.
Qed.

(* t without the factor A (a left-nested sepcon chain) *)
Ltac hkp5_o0S_remove A t :=
  match t with
  | sepcon ?X A => X
  | sepcon ?X ?Y => let X' := hkp5_o0S_remove A X in constr:(sepcon X' Y)
  end.

Lemma hkp5_o0S_snap_open sh sn s :
  Zlength (hs_ck (sn_hs sn)) = 32 ->
  @data_at HCS sh t_hsnap (hsnap_val sn) s |--
  hbytes sh (hs_ck (sn_hs sn)) (offset_val 240 s) *
  (hbytes sh (hs_ck (sn_hs sn)) (offset_val 240 s) -* @data_at HCS sh t_hsnap (hsnap_val sn) s).
Proof.
  intros L.
  assert_PROP (@field_compatible CSkh t_hsnap [] s) as FC.
  { sep_apply (@data_at_data_at_ HCS sh t_hsnap (hsnap_val sn) s). sep_apply HB.hc3b_snap_take_fcs. entailer!. }
  destruct sn as [E nx hd H]. cbn [sn_hs] in *.
  unfold hsnap_val. cbn [sn_entry sn_next sn_hashed sn_hs].
  rewrite HB.hc3b_snap_take_snap_eq.
  rewrite (@field_address_offset CSkh t_hsnap [StructField WgNoise.harness.x_handshake.code._chaining_key] s)
    by auto with field_compatible.
  simpl nested_field_offset.
  rewrite (HB.hc3b_snap_take_hbytes sh 32 (hs_ck H)) by exact L.
  match goal with |- ?B |-- sepcon ?A _ =>
    let R := hkp5_o0S_remove A B in apply (hkp5_o0S_wand_gen A B R); cancel end.
Qed.

Lemma hkp5_segOp0_S_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps FR i R (O: hkp5_o0) :
  hkp5_model_facts -> x25519_props x25519 -> hkp5_o0_live_fact ->
  hkp5_o0_stok O = true -> o_kp O <> nullval ->
  semax (hkp5_Delta hkp5_G_Op0) (hkp5_o0_M x25519 F V steps FR i O) hkp5_o0_sS
    (overridePost (hkp5_o0_M2 x25519 F V steps FR i O) R).
Proof.
  intros HF HX HL Hst Hkp.
  unfold hkp5_o0_M, hkp5_o0_M2, hkp5_Delta.
  destruct R as [Rn Rb Rc Rr]. unfold overridePost.
  unfold hkp5_o0_props, hkp5_o0_locals, hkp5_o0_SEP, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
  cbv zeta. cbn [app].
  Intros.
  pose proof H1 as Hinv.
  destruct H1 as (Hrel & _ & _ & Hsid & _).
  destruct (hkp5_o0S_res F V O HL Hinv H5 H6 H7 H8 H10 Hst Hkp) as (Ehs & Ent & Eal).
  pose proof (hkp5_o0S_epeer _ _ _ _ _ _
    (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 Hrel))))))))) H8) as Ep.
  set (res := o5_res (f_p F) O) in *.
  set (Hs := p_hs (y_P (o_Y O))) in *.
  set (sn := o5_sn (f_p F) O).
  set (D := hkp5_D x25519 F V).
  unfold hkp5_o0_sS.
  abbreviate_semax.
  forward.
  replace (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval by reflexivity.
  (* CHECK(wg_shim_allocs == a0 + 1) *)
  set (S' := kw_S (snd (fst res))) in *.
  rewrite hkp5_o0S_shim. Intros.
  match goal with |- semax _ ?Pre (Ssequence _ ?C) _ =>
    apply semax_seq with Pre; [forward_loop Pre continue: Pre break: Pre | abbreviate_semax] end.
  - apply ENTAIL_refl.
  - forward.
    forward_if.
    { forward_call tt. all: first [match goal with Hc: Int.repr (Z.b2z (Int64.eq _ _)) = Int.zero |- _ =>
        change (Int64.repr 1) with Int64.one in Hc; rewrite Eal, Int64.eq_true in Hc; exact (Int.one_not_zero Hc) end
        | entailer!]. }
    forward. entailer!.
  - forward. apply ENTAIL_refl.
  - apply ENTAIL_refl.
  - gather_SEP (data_at _ tulong _ (f_gv F KC._wg_shim_allocs)) (hkp5_o0S_srest _ _) (refwarn4 _ _).
    rewrite <- hkp5_o0S_shim.
    (* m_transport(first, second, snap.chaining_key) *)
    assert (Lsn: Zlength (hs_ck (sn_hs sn)) = 32) by (destruct H5 as (_ & _ & _ & _ & _ & _ & Lck & _); exact Lck).
    sep_apply (hkp5_o0S_snap_open Tsh sn (f_snap F) Lsn).
    unfold wg_consts. Intros.
    forward_call (f_gv F, Tsh, f_first F, Tsh, f_second F, Tsh, offset_val 240 (f_snap F), hs_ck (sn_hs sn)).
    sep_apply (wand_frame_elim (hbytes Tsh (hs_ck (sn_hs sn)) (offset_val 240 (f_snap F)))
                               (data_at Tsh t_hsnap (hsnap_val sn) (f_snap F))).
    sep_apply (hkp5_o0S_wgc_fold (f_gv F)).
    (* CHECK(hs_zeroed_from(&snap, &p.handshake)) *)
    set (P' := snd (fst (fst res))) in *.
    set (T' := kw_T (snd (fst res))) in *.
    assert (Hcmp: hk5_cmp_pre sn T' (f_p F) (f_w F) P' (o_E O)) by (apply hkp5_o0S_cmp; auto).
    assert (Hzf: zeroed_from sn (snap_of T' (hs_addr (f_p F)) (o_E O) (p_hs P')) = true)
      by (rewrite Ehs; apply hkp5_o0S_zf).
    match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
    + apply ENTAIL_refl.
    + forward_call (Tsh, f_snap F, sn, Tsh, f_p F, P', Tsh, f_t F, T', o_E O, Tsh, f_w F, D).
      rewrite Hzf.
      forward_if.
      { forward_call tt. all: first [match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end | entailer!]. }
      forward. entailer!.
    + forward. apply ENTAIL_refl.
    + unfold POSTCONDITION, abbreviate. cbn [RA_normal].
      change (sn_hs sn) with Hs.
      entailer!.
Qed.
