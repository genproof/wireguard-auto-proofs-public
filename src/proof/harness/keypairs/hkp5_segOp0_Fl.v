(* law keypairs, segment Op0 branch Fl: the failed-allocation branch
   hkp5_o0_sFl (CHECK(!r && hs_same(&snap, &p.handshake) && allocs == a0); free(k)).
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

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

(* ---- helpers (prefix hkp5_o0Fl_) ---- *)

Lemma hkp5_o0Fl_bytes_eqb_refl (a: list byte) : bytes_eqb a a = true.
Proof. unfold bytes_eqb; destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

Lemma hkp5_o0Fl_snap_eqb_refl (sn: hsnap) : snap_eqb sn sn = true.
Proof.
  destruct sn as [[ep et ei] nx hd [st lic sid eph rs reph ss psk h ck ts ri]];
    unfold snap_eqb, entry_eqb, hs_eqb; simpl.
  rewrite !Int.eq_true, !Int64.eq_true, !hkp5_o0Fl_bytes_eqb_refl, Bool.eqb_reflx.
  destruct (EqDec_val ep ep), (EqDec_val nx nx), (EqDec_val sid sid); try congruence.
  reflexivity.
Qed.

Lemma hkp5_o0Fl_succ L a : succ_in L a = nullval \/ In (succ_in L a) L.
Proof.
  induction L as [|x L IH]; simpl; [auto|].
  destruct (EqDec_val x a); [|destruct IH; auto].
  destruct L as [|y L]; simpl; auto.
Qed.

(* hs_same's precondition for the handshake's own snapshot *)
Lemma hkp5_o0Fl_cmp p OD OH KS T E w P :
  hk5_pool p OD OH KS T -> t_entry T (hs_addr p) = Some E -> hs_sid (p_hs P) = id_addr w ->
  hs_cmp_pre (snap_of T (hs_addr p) E (p_hs P)) T p w P E.
Proof.
  intros Hpool HE Hsid.
  destruct Hpool as (_ & _ & _ & _ & (idx & Hf) & _ & _ & Hwf).
  assert (Ep: e_peer E = p).
  { unfold t_entry in HE. rewrite Hf in HE. inv HE. reflexivity. }
  unfold hs_cmp_pre, snap_of. cbn [sn_entry sn_hs sn_next].
  split; [exact HE |]. split; [exact Ep |]. split; [exact Ep |]. split; [exact Hsid |]. split; [exact Hsid |].
  destruct Hwf as (_ & HI & _).
  destruct (hkp5_o0Fl_succ (t_L T) (hs_addr p)) as [-> | Hin]; [left; reflexivity | right; apply HI; exact Hin].
Qed.

Lemma hkp5_o0Fl_tulong_cs {cs1 cs2: compspecs} sh v p :
  @data_at cs1 sh tulong v p = @data_at cs2 sh tulong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible; simpl.
  split; intros (?&?&?&?&?); (repeat split); auto;
    destruct p; try contradiction; unfold align_compatible in *;
    (apply align_compatible_rec_by_value with Mint64; [reflexivity|]);
    apply (align_compatible_rec_by_value_inv _ _ Mint64) in H2; auto.
Qed.

Lemma hkp5_o0Fl_shim_fold gv S : shim_ok S ->
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
   @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow))
  |-- shim_core gv S.
Proof. intros H. unfold shim_core. apply andp_right; [apply prop_right; exact H | apply derives_refl]. Qed.

Lemma hkp5_segOp0_Fl_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps FR i R (O: hkp5_o0) :
  hkp5_model_facts -> x25519_props x25519 -> hkp5_o0_stok O = true -> o_kp O = nullval ->
  semax (hkp5_Delta hkp5_G_Op0) (hkp5_o0_M x25519 F V steps FR i O) hkp5_o0_sFl
    (overridePost (hkp5_o0_Z x25519 F V steps FR i) R).
Proof.
  intros HF HX Hst Hkp.
  destruct O as [Y E k kp]. cbn [o_kp] in Hkp. subst kp.
  unfold hkp5_o0_stok in Hst. cbn [o_Y] in Hst.
  unfold hkp5_o0_M, hkp5_Delta.
  destruct R as [Rn Rb Rc Rr]. unfold overridePost.
  unfold hkp5_o0_props, hkp5_o0_locals, hkp5_o0_SEP, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
  cbv zeta. cbn [app].
  unfold o5_res, o5_w, o5_sn. cbn [o_Y o_E o_k o_kp].
  rewrite hkp5_o0_res_fail by exact Hst. rewrite hkp5_o0_warn_fail.
  cbn [fst snd kw_S kw_T kw_KS].
  Intros.
  match goal with H: hkp5_inv0 _ _ _ |- _ => pose proof H as Hinv; destruct H as (Hrel & _ & _ & Hsid & _) end.
  match goal with H: t_entry _ _ = Some E |- _ => rename H into HE end.
  pose proof (hkp5_o0Fl_cmp _ _ _ _ _ _ _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 Hrel)))))))))
                HE Hsid) as Hcmp.
  set (D := hkp5_D x25519 F V).
  set (sn := snap_of (y_T Y) (hs_addr (f_p F)) E (p_hs (y_P Y))) in *.
  abbreviate_semax.
  unfold shim_state4 at 1, shim_core at 1. Intros.
  match goal with Hs: shim_ok (shim_alloc_fail (y_S Y)) |- _ => rename Hs into HSok end.
  rewrite (@hkp5_o0Fl_tulong_cs Noise.CS W_keypairs _ _ (f_gv F _wg_shim_allocs)).
  change _wg_shim_allocs with KC._wg_shim_allocs.
  unfold hkp5_o0_sFl.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  - apply ENTAIL_refl.
  - match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp KC._t'20 (Vint Int.one) :: Q) (SEPx R))) end.
    + forward_call (Tsh, f_snap F, sn, Tsh, f_p F, y_P Y, Tsh, f_t F, y_T Y, E, Tsh, f_w F, D).
      fold sn. rewrite hkp5_o0Fl_snap_eqb_refl. forward. entailer!.
    + exfalso. match goal with Hc: ?x <> ?x |- _ => exact (Hc eq_refl) end.
    + match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROPx P (LOCALx (temp KC._t'22 (Vint Int.one) :: Q) (SEPx R))) end.
      { forward. forward. entailer!.
        unfold shim_alloc_fail; cbn [s_allocs]. unfold Int64.cmpu. rewrite Int64.eq_true. reflexivity. }
      { exfalso. match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
      forward_if.
      { forward_call tt. all: first [match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end | entailer!]. }
      forward. entailer!.
  - forward. apply ENTAIL_refl.
  - forward_call (t_mk5, k, f_gv F).
    { rewrite if_false by auto. cancel. }
    rewrite (@hkp5_o0Fl_tulong_cs W_keypairs Noise.CS _ _ (f_gv F KC._wg_shim_allocs)).
    change KC._wg_shim_allocs with _wg_shim_allocs.
    sep_apply (hkp5_o0Fl_shim_fold (f_gv F) (shim_alloc_fail (y_S Y)) HSok).
    sep_apply (@data_at_data_at_ HCS Tsh t_hsnap (hsnap_val sn) (f_snap F)).
    unfold hkp5_o0_Z.
    Exists (mkKY5 (shim_alloc_fail (y_S Y)) (y_w Y) (y_kc Y) (y_P Y) (y_KS Y) (y_T Y) (y_H Y) (y_now Y)
              (y_next_id Y) (y_id_known Y) (y_hsn Y)).
    unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars. cbn [app].
    cbn [y_S y_w y_kc y_P y_KS y_T y_H y_now y_next_id y_id_known y_hsn].
    unfold shim_state4.
    entailer!.
    all: apply derives_refl.
Qed.
