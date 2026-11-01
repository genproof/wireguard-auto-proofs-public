(* law transport_order: main's segment L4 (body statements 18..21): bad tag -> CHECK(rc_same); good tag -> wm_accepts,
   wg_counter_validate, CHECK(r == pred), on acceptance CHECK(bytes_eq) and wm_commit (failure: 3 frees + break),
   CHECK(rc.counter == wm.top), have_auth, last_nonce; the three frees.
   States and the cut: ht4o_main_defs.v; *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.counter.counter_spec.
Require Import WgNoise.proof.harness.common4t.ht4_worlds.
Require Import WgNoise.proof.harness.common4t.ht4c_spec.
Require Import WgNoise.proof.harness.common4t.ht4r_spec.
Require Import WgNoise.proof.harness.common4t.ht4a_aead.
Require Import WgNoise.proof.harness.transport_order.ht4o_main_defs.
Require WgNoise.proof.aead.aead_models_props3.
Require WgNoise.proof.harness.counter.hcnt_defs3.

#[local] Existing Instance W_transport_order.
Local Open Scope Z_scope.

(* the state after the if (before the three frees): the loop state Y, the snapshot and the three buffers *)
Definition ht4o_L4mid (F: ht4o_fix) (FR: mpred) (i: Z) (snapv: reptype ht4o_tsnap) (n m: Z) (v1 v2 v3: list val)
  (pkt po rp: val) : environ -> mpred :=
  EX Y: ht4o_dyn,
  PROPx [ht4o_inv Y]
  (LOCALx (temp TO._pkt pkt :: temp TO._pt_out po :: temp TO._ref_pt rp :: ht4o_temps F Y i ++ ht4o_lvars F)
  (SEPx (data_at Tsh ht4o_tsnap snapv (f_snap F) :: ht4o_buf n v1 pkt :: ht4o_buf m v2 po :: ht4o_buf m v3 rp ::
         ht4o_world F Y FR))).

(* a buffer is freed as free_spec' wants it *)
Lemma ht4o_L4_free_pre (n: Z) (v: list val) (p: val) :
  ht4o_buf n v p |-- (if eq_dec p nullval then emp
                      else (malloc_token Ews (tarray tuchar n) p * data_at_ Ews (tarray tuchar n) p))%logic.
Proof.
  unfold ht4o_buf. destruct (eq_dec p nullval) as [->|Hn].
  - entailer!.
  - cancel.
Qed.

(* the replay counter at the counter piece's compspecs (as law counter's hcnt_c_change) *)
#[local] Instance ht4o_L4_CCE : change_composite_env Counter.CS W_transport_order.
Proof. make_cs_preserve Counter.CS W_transport_order. Defined.

Lemma ht4o_L4_rc_change sh top bm v:
  @data_at W_transport_order sh ht4o_trc (ht4o_rc top bm) v =
  @data_at Counter.CS sh (Tstruct counter_spec._noise_replay_counter noattr) (cnt_val top Vundef bm) v.
Proof.
  symmetry. unfold ht4o_trc.
  exact (f_equal (fun f => f v) (@data_at_change_composite Counter.CS W_transport_order ht4o_L4_CCE sh
    (Tstruct counter_spec._noise_replay_counter noattr) (cnt_val top Vundef bm) (ht4o_rc top bm) (JMeq_refl _) eq_refl)).
Qed.

Lemma ht4o_L4_free_pre2 (n: Z) (v: list val) (p: val) :
  (malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) v p)%logic
  |-- (if eq_dec p nullval then emp
       else (malloc_token Ews (tarray tuchar n) p * data_at_ Ews (tarray tuchar n) p))%logic.
Proof. apply ht4o_L4_free_pre. Qed.

Lemma ht4o_segL4_ok {Espec: OracleKind} (F: ht4o_fix) (FR: mpred) (i: Z) (R: ret_assert) :
  semax ht4o_Delta (ht4o_PL3 F FR i) ht4o_segL4
    (loop1_ret_assert (ht4o_Icont F FR i) (overridePost (ht4o_Brk F FR) R)).
Proof.
  intros. destruct F as [gv vrc vwm vsnap vkey K steps]. destruct R as [Rn Rb Rc Rr].
  cbn [overridePost loop1_ret_assert].
  unfold ht4o_PL3, ht4o_Delta, ht4o_temps, ht4o_lvars, ht4o_world, ht4o_tB, ht4o_segL4.
  cbn [f_gv f_rc f_wm f_snap f_key f_K f_steps]. simpl app. simplify_func_tycontext. abbreviate_semax.
  Intros Y kind L pkt po rp nonce hdr ct.
  destruct Y as [top S bm have ln]. cbn [y_top y_S y_bm y_have y_ln] in *.
  destruct H0 as [HK Hst]. cbn [f_K f_steps] in HK, Hst.
  destruct H1 as [Hinv Hln]. cbn [y_top y_S y_bm y_have y_ln] in Hinv, Hln.
  destruct H2 as [Hkind HL].
  forward_if (ht4o_L4mid (mkTFix gv vrc vwm vsnap vkey K steps) FR i (ht4o_snap top bm)
    (16 + ht4o_enc kind L) (ht4o_plen (ht4o_enc kind L)) (hdr ++ map Vubyte ct)
    (ht4o_ptv (ht4o_dec (mkTFix gv vrc vwm vsnap vkey K steps) nonce ct) (ht4o_plen (ht4o_enc kind L)))
    (ht4o_ptv (ht4o_dec (mkTFix gv vrc vwm vsnap vkey K steps) nonce ct) (ht4o_plen (ht4o_enc kind L)))
    pkt po rp).
  - (* bad tag: CHECK(rc_same(&snap, &rc)) *)
    destruct (ht4o_dec _ nonce ct) as [pt|] eqn:Hd; [exfalso; apply Int.one_not_zero; exact H0 |].
    cbn [ht4o_okv ht4o_ptv].
    assert (Hw: ht4o_words bm) by (split; [apply (cnt_len _ _ _ Hinv) | apply (cnt_words _ _ _ Hinv)]).
    pose proof (cnt_top_range _ _ _ Hinv) as Htop. unfold CNT_R, CNT_W in Htop.
    match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
    { apply ENTAIL_refl. }
    { forward_call (Tsh, vsnap, top, bm, Tsh, vrc, top, bm).
      rewrite !if_true by auto.
      match goal with |- semax _ ?P _ _ => forward_if P end.
      { exfalso; apply Int.one_not_zero; assumption. }
      { forward. entailer!. }
      { forward. entailer!. } }
    unfold ht4o_L4mid. Exists (mkTDyn top S bm have ln).
    unfold ht4o_temps, ht4o_lvars, ht4o_world, ht4o_inv.
    cbn [f_gv f_rc f_wm f_snap f_key f_K f_steps y_top y_S y_bm y_have y_ln ht4o_ptv]. simpl app.
    entailer!.
  - (* good tag *)
    destruct (ht4o_dec _ nonce ct) as [pt|] eqn:Hd; [| exfalso; apply H0; reflexivity].
    cbn [ht4o_okv ht4o_ptv] in *.
    assert (Hpt: Zlength pt = ht4o_enc kind L - 16).
    { unfold ht4o_dec in Hd; cbn [f_K] in Hd. rewrite <- H5.
      exact (aead_dec_length _ _ (proj1 aead_models_props3.aead_models_ok3) _ _ _ _ _ Hd). }
    assert (Hplen: ht4o_plen (ht4o_enc kind L) = Zlength pt)
      by (unfold ht4o_plen; pose proof (Zlength_nonneg pt); lia).
    rewrite Hplen.
    pose proof Hinv as [Hlen Hwords Htop HSr _ _].
    assert (HS: Forall (fun x => 0 <= x <= Int64.max_unsigned) S).
    { rewrite Forall_forall; intros x Hx; specialize (HSr x Hx); unfold CNT_R, CNT_W in Htop; rep_lia. }
    unfold CNT_R, CNT_W in Htop.
    forward_call (Tsh, vwm, top, S, nonce).
    rewrite ht4o_L4_rc_change.
    forward_call (Tsh, vrc, top, S, bm, Vundef, nonce).
    Intros bm'.
    rewrite <- ht4o_L4_rc_change.
    unfold cnt_top', cnt_L' in H1 |- *.
    destruct (cnt_ok top S nonce) eqn:Hok; cbn [Val.of_bool] in *.
    + (* accepted *)
      match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
      { apply ENTAIL_refl. }
      { match goal with |- semax _ ?P _ _ => forward_if P end.
        { exfalso. rewrite Int.eq_true in H2. apply Int.one_not_zero; exact H2. }
        { forward. entailer!. }
        { forward. entailer!. } }
      assert (Hn: nonce < CNT_R /\ top <= nonce + 1 + CNT_W)
        by (unfold cnt_ok in Hok; rewrite !andb_true_iff, !Z.ltb_lt, Z.leb_le in Hok; tauto).
      assert (HS': Forall (fun x => 0 <= x < CNT_R) S)
        by (rewrite Forall_forall; intros x Hx; specialize (HSr x Hx); unfold CNT_R, CNT_W; lia).
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx (?rc :: ?wm :: ?rest)))) _ _ =>
        forward_if (PROPx P (LOCALx Q (SEPx (rc :: ht4o_wm Tsh (Z.max top (nonce+1))
          (ht4o_prune (Z.max top (nonce+1)) (nonce :: S)) vwm :: rest)))) end.
      2: { exfalso. apply Int.one_not_zero; exact H2. }
      { unfold ht4o_buf. Intros.
        match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
        { apply ENTAIL_refl. }
        { forward_call (Ews, po, pt, Ews, rp, pt).
          { entailer!. apply field_compatible_isptr in H15, H19. destruct po, rp; try contradiction.
            rewrite Hpt. reflexivity. }
          { rewrite Hpt; unfold ht4o_enc; destruct (kind =? 3), (L <? 16); simpl; rep_lia. }
          destruct (list_eq_dec Byte.eq_dec pt pt) as [_|]; [| congruence].
          match goal with |- semax _ ?P _ _ => forward_if P end.
          { exfalso; apply Int.one_not_zero; assumption. }
          { forward. entailer!. }
          { forward. entailer!. } }
        forward_call (Tsh, vwm, top, S, nonce, gv).
        Intros b. destruct b; forward_if.
        { exfalso; apply Int.one_not_zero; assumption. }
        { forward. unfold ht4o_buf. entailer!. }
        { (* wm_commit failed: the three frees, break *)
          sep_apply (ht4o_L4_free_pre2 (16 + ht4o_enc kind L) (hdr ++ map Vubyte ct) pkt).
          forward_call (tarray tuchar (16 + ht4o_enc kind L), pkt, gv).
          sep_apply (ht4o_L4_free_pre2 (Zlength pt) (map Vubyte pt) po).
          forward_call (tarray tuchar (Zlength pt), po, gv).
          sep_apply (ht4o_L4_free_pre2 (Zlength pt) (map Vubyte pt) rp).
          forward_call (tarray tuchar (Zlength pt), rp, gv).
          forward.
          unfold ht4o_Brk. Exists top S. unfold ht4o_lvars. cbn [f_gv f_rc f_wm f_snap f_key f_K f_steps].
          sep_apply (data_at_data_at_ Tsh ht4o_tsnap (ht4o_snap top bm) vsnap).
          sep_apply (data_at_data_at_ Tsh ht4o_trc (ht4o_rc (Z.max top (nonce + 1)) bm') vrc).
          entailer!. }
        { exfalso; apply H6; reflexivity. } }
      (* CHECK(rc.counter == wm.top); have_auth = 1; last_nonce = nonce *)
      unfold ht4o_wm at 1. Intros pw.
      match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
      { apply ENTAIL_refl. }
      { unfold ht4o_rc. forward. forward.
        match goal with |- semax _ ?P _ _ => forward_if P end.
        { exfalso. rewrite Int64.eq_true in *. apply Int.one_not_zero; assumption. }
        { forward. entailer!. }
        { forward. entailer!. } }
      forward. forward.
      rewrite Hplen. unfold ht4o_L4mid.
      Exists (mkTDyn (Z.max top (nonce+1)) (ht4o_prune (Z.max top (nonce+1)) (nonce :: S)) bm' true nonce).
      unfold ht4o_temps, ht4o_lvars, ht4o_world, ht4o_inv, ht4o_wm.
      cbn [f_gv f_rc f_wm f_snap f_key f_K f_steps y_top y_S y_bm y_have y_ln]. simpl app.
      Exists pw. entailer!. apply hcnt_defs3.cnt_inv_prune3; auto.
    + (* rejected *)
      match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
      { apply ENTAIL_refl. }
      { match goal with |- semax _ ?P _ _ => forward_if P end.
        { exfalso. rewrite Int.eq_true in H2. apply Int.one_not_zero; exact H2. }
        { forward. entailer!. }
        { forward. entailer!. } }
      match goal with |- semax _ ?P _ _ => forward_if P end.
      { exfalso. apply H2; reflexivity. }
      { forward. entailer!. }
      (* CHECK(rc.counter == wm.top); have_auth = 1; last_nonce = nonce *)
      unfold ht4o_wm at 1. Intros pw.
      match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
      { apply ENTAIL_refl. }
      { unfold ht4o_rc. forward. forward.
        match goal with |- semax _ ?P _ _ => forward_if P end.
        { exfalso. rewrite Int64.eq_true in *. apply Int.one_not_zero; assumption. }
        { forward. entailer!. }
        { forward. entailer!. } }
      forward. forward.
      rewrite Hplen. unfold ht4o_L4mid.
      Exists (mkTDyn top S bm' true nonce).
      unfold ht4o_temps, ht4o_lvars, ht4o_world, ht4o_inv, ht4o_wm.
      cbn [f_gv f_rc f_wm f_snap f_key f_K f_steps y_top y_S y_bm y_have y_ln]. simpl app.
      Exists pw. entailer!.
  - (* the three frees *)
    unfold ht4o_L4mid. Intros Y'. unfold ht4o_temps, ht4o_lvars, ht4o_world.
    cbn [f_gv f_rc f_wm f_snap f_key f_K f_steps]. simpl app.
    forget (ht4o_ptv (ht4o_dec (mkTFix gv vrc vwm vsnap vkey K steps) nonce ct) (ht4o_plen (ht4o_enc kind L)))
      as v2.
    sep_apply (ht4o_L4_free_pre (16 + ht4o_enc kind L) (hdr ++ map Vubyte ct) pkt).
    forward_call (tarray tuchar (16 + ht4o_enc kind L), pkt, gv).
    sep_apply (ht4o_L4_free_pre (ht4o_plen (ht4o_enc kind L)) v2 po).
    forward_call (tarray tuchar (ht4o_plen (ht4o_enc kind L)), po, gv).
    sep_apply (ht4o_L4_free_pre (ht4o_plen (ht4o_enc kind L)) v2 rp).
    forward_call (tarray tuchar (ht4o_plen (ht4o_enc kind L)), rp, gv).
    assert (Hfix: ht4o_fix_ok (mkTFix gv vrc vwm vsnap vkey K steps)) by (split; auto).
    unfold ht4o_Icont, ht4o_St. Exists Y'. unfold ht4o_temps, ht4o_lvars, ht4o_world.
    cbn [f_gv f_rc f_wm f_snap f_key f_K f_steps]. simpl app.
    sep_apply (data_at_data_at_ Tsh ht4o_tsnap (ht4o_snap top bm) vsnap).
    entailer!.
Qed.
