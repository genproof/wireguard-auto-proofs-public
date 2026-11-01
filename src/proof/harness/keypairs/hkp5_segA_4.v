(* law keypairs, prologue A, piece 4: statements 21..28 (hs_take(&hsm), pr_take(&prm), prefs, dev_take(&dsm), allocs0, frees0, the warn0 loop, steps).
   States: hkp5_segA_defs.v. "Prologue A".
*)
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
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.keypairs.hkp5_op1.
Require Import WgNoise.proof.harness.keypairs.hkp5_spec.
Require Import WgNoise.proof.harness.keypairs.hkp5_segA_defs.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

#[local] Instance hkp5A4_CCEn : change_composite_env Noise.CS W_keypairs.
Proof. make_cs_preserve Noise.CS W_keypairs. Defined.
Definition hkp5A4_CCEh : change_composite_env HCS W_keypairs.
Proof. make_cs_preserve HCS W_keypairs. Defined.
Definition hkp5A4_CCEk : change_composite_env CKS W_keypairs.
Proof. make_cs_preserve CKS W_keypairs. Defined.

Lemma hkp5A4_tulong_cs {cs1 cs2: compspecs} sh v p :
  @data_at cs1 sh tulong v p = @data_at cs2 sh tulong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible; simpl.
  split; intros (?&?&?&?&?); (repeat split); auto;
    destruct p; try contradiction; unfold align_compatible in *;
    (apply align_compatible_rec_by_value with Mint64; [reflexivity|]);
    apply (align_compatible_rec_by_value_inv _ _ Mint64) in H2; auto.
Qed.

Lemma hkp5A4_warr_cs sh (v: list val) p :
  @data_at Noise.CS sh (tarray tulong 5) v p = @data_at W_keypairs sh (tarray tulong 5) v p.
Proof.
  refine (f_equal (fun f => f p) (@data_at_change_composite Noise.CS W_keypairs hkp5A4_CCEn sh (tarray tulong 5) v v
    _ _)); [apply JMeq_refl | reflexivity].
Qed.

Lemma hkp5A4_hsm sh x :
  @data_at_ W_keypairs sh (Tstruct KC._hs_snap noattr) x = @data_at_ HCS sh t_hsnap x.
Proof.
  symmetry. exact (f_equal (fun f => f x) (@data_at__change_composite HCS W_keypairs hkp5A4_CCEh sh t_hsnap
    ltac:(vm_compute; reflexivity))).
Qed.

Lemma hkp5A4_dsm sh x :
  @data_at_ W_keypairs sh (Tstruct KC._dev_snap noattr) x = @data_at_ CKS sh t_devsnap x.
Proof.
  symmetry. exact (f_equal (fun f => f x) (@data_at__change_composite CKS W_keypairs hkp5A4_CCEk sh t_devsnap
    ltac:(vm_compute; reflexivity))).
Qed.

Lemma hkp5A4_prm0 sh x :
  @data_at_ W_keypairs sh (Tstruct KC._pr_snap noattr) x = @data_at_ CKS sh t_prsnap x.
Proof.
  symmetry. exact (f_equal (fun f => f x) (@data_at__change_composite CKS W_keypairs hkp5A4_CCEk sh t_prsnap
    ltac:(vm_compute; reflexivity))).
Qed.

Lemma hkp5A4_prm sh P x : p_cur P = nullval -> p_prev P = nullval -> p_next P = nullval ->
  @data_at CKS sh t_prsnap (prsnap_val P) x = @data_at W_keypairs sh (Tstruct KC._pr_snap noattr) (hk5_prsnap_val P) x.
Proof.
  intros H1 H2 H3. unfold prsnap_val. rewrite H1, H2, H3.
  exact (f_equal (fun f => f x) (@data_at_change_composite CKS W_keypairs hkp5A4_CCEk sh t_prsnap _ _ (JMeq_refl _)
    ltac:(vm_compute; reflexivity))).
Qed.

Lemma hkp5A4_refs sh p r :
  @field_at Noise.CS sh t_peer [StructField I._refcount] (Vint r) p =
  @field_at W_keypairs sh (Tstruct KC._wg_peer noattr) [StructField KC._refcount] (Vint r) p.
Proof.
  exact (f_equal (fun f => f p) (@field_at_change_composite Noise.CS W_keypairs hkp5A4_CCEn sh t_peer
           [StructField I._refcount] (Vint r) (Vint r) (JMeq_refl _) ltac:(vm_compute; reflexivity))).
Qed.

(* peer_rep with the reference count at the world *)
Definition hkp5A4_prest (sh: share) (p: val) (P: peer) : mpred :=
  (@field_at Noise.CS sh t_peer [StructField I._device] (p_device P) p *
   @field_at Noise.CS sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   @field_at Noise.CS sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   @field_at Noise.CS sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Lemma hkp5A4_peer sh p P :
  peer_rep sh p P =
  (!! @field_compatible Noise.CS t_peer [] p &&
   (@field_at W_keypairs sh (Tstruct KC._wg_peer noattr) [StructField KC._refcount] (Vint (p_refs P)) p *
    hkp5A4_prest sh p P)).
Proof.
  rewrite <- hkp5A4_refs. unfold peer_rep, hkp5A4_prest.
  apply pred_ext; apply andp_derives; try apply derives_refl; cancel.
Qed.

Lemma hkp5A4_peer_fold sh p P : @field_compatible Noise.CS t_peer [] p ->
  (@field_at W_keypairs sh (Tstruct KC._wg_peer noattr) [StructField KC._refcount] (Vint (p_refs P)) p *
   hkp5A4_prest sh p P) |-- peer_rep sh p P.
Proof.
  intros Hfc. rewrite hkp5A4_peer. apply andp_right; [apply prop_right; exact Hfc | apply derives_refl].
Qed.

Lemma hkp5A_4_ok {Espec: OracleKind} x25519 (F: hkp5_fix) (FR: mpred) R :
  x25519_props x25519 ->
  semax (hkp5_Delta (hkp5_G_A x25519)) (hkp5A_S3 x25519 F FR) hkp5A_s4 (overridePost (hkp5A_S4 x25519 F FR) R).
Proof.
  intros HX.
  destruct F as [gv w t pt p raw pub snap opub first second].
  unfold hkp5A_S3, hkp5_Delta, hkp5A_s4.
  Intros RR P S ww NS PS KE T head.
  unfold hkp5A_world, hk5_items, hkp5A_snaps0, hkp5A_oth, hkp5A_kes, hkp5A_globs, hkp5A_temps, hkp5_lvars.
  cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second].
  abbreviate_semax.
  set (F0 := {| f_gv := gv; f_w := w; f_t := t; f_pt := pt; f_p := p; f_raw := raw; f_pub := pub;
    f_snap := snap; f_opub := opub; f_first := first; f_second := second |}) in *.
  pose proof H1 as Hinv.
  destruct H1 as (Hp & Hdev & Hsid & Hcur & Hprev & Hnext & Hpkn & Hhn & Hwf & Hnd & Hpa & Hka & Hoth & Hhead &
    Hsad & Hsf & Hent & Hkent & Hidx).
  cbn [f_p f_w F0] in *.
  assert_PROP (isptr w /\ isptr t /\ isptr pt) as Hw by entailer!.
  destruct Hw as (Hw & Ht & Hpt).
  (* hs_take(&hsm, &p.handshake) *)
  rewrite hkp5A4_hsm.
  change (peer_rep Tsh p P) with (hs_mem true Tsh p P).
  forward_call (Ews, gv KC._hsm, Tsh, p, P, true, Tsh, t, T).
  { split; [| split].
    - rewrite Hsad. apply in_or_app. right. apply in_or_app. right. left. reflexivity.
    - unfold t_entry_d, t_entry. rewrite Hsf. cbn. destruct p; try contradiction; discriminate.
    - rewrite Hsid. unfold id_addr. destruct w; try contradiction; discriminate. }
  change (hs_mem true Tsh p P) with (peer_rep Tsh p P).
  (* pr_take(&prm, &p) *)
  rewrite hkp5A4_prm0.
  forward_call (Ews, gv KC._prm, Tsh, p, P).
  { rewrite Hdev, Hcur, Hprev, Hnext, Hpkn. repeat constructor; try discriminate.
    destruct w; try contradiction; discriminate. }
  rewrite (hkp5A4_prm Ews P (gv KC._prm) Hcur Hprev Hnext).
  (* prefs = p.refcount.refcount *)
  rewrite hkp5A4_peer. Intros.
  forward.
  forward.
  sep_apply (hkp5A4_peer_fold Tsh p P ltac:(assumption)).
  (* dev_take(&dsm, &w) *)
  rewrite hkp5A4_dsm.
  change (ptable Tsh pt head) with (ptable Tsh (d_ptab (hkp5A_D x25519 F0 RR)) head).
  forward_call (Ews, gv KC._dsm, Tsh, w, hkp5A_D x25519 F0 RR, Tsh, head).
  { assert (Hh: head <> Vundef).
    { destruct Hhead as [-> | Hin]; [destruct p; try contradiction; discriminate|].
      rewrite Forall_forall in Hpa. specialize (Hpa _ Hin). destruct head; try contradiction; discriminate. }
    unfold hkp5A_D, setup_dev; cbn.
    repeat constructor; try discriminate; auto;
      [destruct w | destruct pt | destruct t]; try contradiction; discriminate. }
  change (d_ptab (hkp5A_D x25519 F0 RR)) with pt.
  (* allocs0 = wg_shim_allocs; frees0 = wg_shim_frees *)
  unfold shim_state4 at 1, shim_core at 1. Intros.
  rewrite (@hkp5A4_tulong_cs Noise.CS W_keypairs _ _ (gv _wg_shim_allocs)).
  rewrite (@hkp5A4_tulong_cs Noise.CS W_keypairs _ _ (gv _wg_shim_frees)).
  change _wg_shim_allocs with KC._wg_shim_allocs. change _wg_shim_frees with KC._wg_shim_frees.
  forward. forward.
  rewrite (@hkp5A4_tulong_cs W_keypairs Noise.CS _ _ (gv KC._wg_shim_allocs)).
  rewrite (@hkp5A4_tulong_cs W_keypairs Noise.CS _ _ (gv KC._wg_shim_frees)).
  change KC._wg_shim_allocs with _wg_shim_allocs. change KC._wg_shim_frees with _wg_shim_frees.
  (* the warn0 loop *)
  unfold refwarn4. Intros.
  rewrite hkp5A4_warr_cs.
  change _wg_shim_refcount_warn with KC._wg_shim_refcount_warn.
  focus_SEP 19.
  match goal with |- semax _ (PROPx _ (LOCALx ?L (SEPx (?X :: ?rest)))) _ _ =>
    change X with (data_at_ Ews (tarray tulong 5) (gv KC._warn0));
    forward_for_simple_bound 5 (EX i: Z, PROPx [] (LOCALx L (SEPx (
      data_at Ews (tarray tulong 5) (map Vlong (sublist 0 i ww) ++ Zrepeat Vundef (5 - i)) (gv KC._warn0) :: rest))))
  end.
  { entailer!. }
  { cbv beta.
    assert (E1: Znth i (map Vlong ww) = Vlong (Znth i ww)) by (rewrite Znth_map by lia; reflexivity).
    forward. forward.
    entailer!.
    apply derives_refl'. f_equal.
    rewrite (sublist_split 0 i (i+1) ww) by lia. rewrite (sublist_one i (i+1) ww) by lia.
    list_solve. }
  rewrite Z.sub_diag, Zrepeat_0, app_nil_r, sublist_same by lia.
  (* steps = draw_steps() *)
  forward_call tt. Intros steps.
  forward.
  destruct R as [Rn Rb Rc Rr]. cbn [RA_normal].
  unfold hkp5A_S4. Exists RR P S ww NS PS KE T head steps.
  unfold hkp5A_world, hk5_items, hkp5A_snaps, hkp5A_oth, hkp5A_kes, hkp5A_globs, hkp5A_temps, hkp5_lvars.
  cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second F0].
  unfold shim_state4, shim_core, refwarn4, hk5_warr.
  rewrite hkp5A4_warr_cs.
  change _wg_shim_refcount_warn with KC._wg_shim_refcount_warn.
  entailer!.
Qed.
