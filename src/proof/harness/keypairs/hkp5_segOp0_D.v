(* law keypairs, segment Op0 branch D: the dead branch hkp5_o0_sD
   (CHECK(!r && frees == fr0 + 1 && entry.hashed == snap.hashed && entry.index == snap.index); m_frees++;
   if (id_known) next_id++; free(k)). "Op0". *)
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

(* ---- helpers (prefix hkp5_o0D_; copies of v1's hkp4_o0D_ / sibling W's) ---- *)

Lemma hkp5_o0D_tulong_cs {cs1 cs2: compspecs} sh v p :
  @data_at cs1 sh tulong v p = @data_at cs2 sh tulong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible; simpl.
  split; intros (?&?&?&?&?); (repeat split); auto;
    destruct p; try contradiction; unfold align_compatible in *;
    (apply align_compatible_rec_by_value with Mint64; [reflexivity|]);
    apply (align_compatible_rec_by_value_inv _ _ Mint64) in H2; auto.
Qed.

Lemma hkp5_o0D_shim_fold gv S : shim_ok S ->
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

Lemma hkp5_o0D_hash_len m : Zlength (HASH m) = 32.
Proof. unfold HASH, model.blake2s, model.b2s_digest_stream, model.b2s_out. rewrite Zlength_map. reflexivity. Qed.
Lemma hkp5_o0D_kdf1_len a b : Zlength (kdf1 a b) = 32.
Proof. unfold kdf1, hmac. cbv zeta. apply hkp5_o0D_hash_len. Qed.
Lemma hkp5_o0D_kdf2_len a b : Zlength (kdf2 a b) = 32.
Proof. unfold kdf2, hmac. cbv zeta. apply hkp5_o0D_hash_len. Qed.

Lemma hkp5_o0D_hout bs p : Zlength bs = 32 -> hbytes Tsh bs p |-- hout Tsh 32 p.
Proof. intros L. unfold hbytes, hout. rewrite L. apply data_at_data_at_. Qed.

Lemma hkp5_o0D_tc_bool b : tc_val tbool (Val.of_bool b).
Proof. destruct b; simpl; auto. Qed.

#[local] Instance hkp5_o0D_CCE : change_composite_env Noise.CS W_keypairs.
Proof. make_cs_preserve Noise.CS W_keypairs. Defined.

Definition hkp5_o0D_CCEh : change_composite_env HCS W_keypairs.
Proof. make_cs_preserve HCS W_keypairs. Defined.

Lemma hkp5_o0D_snapcs : cs_preserve_type HCS W_keypairs (@coeq _ _ hkp5_o0D_CCEh) t_hsnap = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hkp5_o0D_split (D: list (val * share * entry)) a sh E (f: val * share * entry -> mpred) :
  sfind D a = Some (sh, E) ->
  VST.msl.iter_sepcon.iter_sepcon f D = (f (a, sh, E) * VST.msl.iter_sepcon.iter_sepcon f (sdel D a)).
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; reflexivity|].
  rewrite (IH H); simpl. rewrite <- !sepcon_assoc, (sepcon_comm (f _) (f _)). reflexivity.
Qed.

Lemma hkp5_o0D_hscs : cs_preserve_type Noise.CS W_keypairs (@coeq _ _ hkp5_o0D_CCE) t_hs = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hkp5_o0D_fcW p : @field_compatible Noise.CS t_peer [] p ->
  @field_compatible W_keypairs (Tstruct KC._wg_peer noattr) [] p.
Proof.
  intros H. apply (@field_compatible_change_composite Noise.CS W_keypairs hkp5_o0D_CCE t_peer);
    [vm_compute; reflexivity | exact H].
Qed.

Lemma hkp5_o0D_hsaddr p : @field_compatible Noise.CS t_peer [] p ->
  @field_address W_keypairs (Tstruct KC._wg_peer noattr) [StructField KC._handshake] p = hs_addr p.
Proof. intros H. apply hkp5_o0D_fcW in H. rewrite field_address_offset by auto with field_compatible. reflexivity. Qed.

Lemma hkp5_o0D_entry sh E nx hd p : @field_compatible Noise.CS t_peer [] p ->
  @data_at Noise.CS sh t_entry_s (entry_val E nx hd) (hs_addr p) =
  @field_at W_keypairs sh (Tstruct KC._wg_peer noattr) [StructField KC._entry; StructField KC._handshake]
    (entry_val E nx hd) p.
Proof.
  intros FC.
  change [StructField KC._entry; StructField KC._handshake] with ([StructField KC._entry] ++ [StructField KC._handshake]).
  rewrite (@field_at_app W_keypairs sh (Tstruct KC._wg_peer noattr) [StructField KC._entry] [StructField KC._handshake]
             (entry_val E nx hd) (entry_val E nx hd) p (JMeq_refl _)).
  rewrite hkp5_o0D_hsaddr by exact FC.
  transitivity (@field_at Noise.CS sh t_hs (DOT I._entry) (entry_val E nx hd) (hs_addr p)).
  2: { exact (f_equal (fun f => f (hs_addr p)) (@field_at_change_composite Noise.CS W_keypairs hkp5_o0D_CCE sh t_hs
           [StructField I._entry] (entry_val E nx hd) (entry_val E nx hd) (JMeq_refl _) hkp5_o0D_hscs)). }
  assert (FC1: @field_compatible Noise.CS t_peer (DOT I._handshake) p) by auto with field_compatible.
  assert (FC2: @field_compatible Noise.CS t_hs [] (hs_addr p)).
  { apply field_compatible_nested_field in FC1. exact FC1. }
  assert (FC3: @field_compatible Noise.CS t_hs (DOT I._entry) (hs_addr p)) by auto with field_compatible.
  rewrite (@field_at_data_at Noise.CS). rewrite (@field_address_offset Noise.CS) by auto. simpl.
  rewrite isptr_offset_val_zero by (unfold hs_addr; destruct FC as [Hp _]; destruct p; try contradiction; exact I).
  reflexivity.
Qed.

Lemma hkp5_o0D_open sht tab T p she E :
  @field_compatible Noise.CS t_peer [] p -> itable_wf T -> sfind (t_D T) (hs_addr p) = Some (she, E) ->
  itable sht tab T =
  (@data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab *
   @field_at W_keypairs she (Tstruct KC._wg_peer noattr) [StructField KC._entry; StructField KC._handshake]
     (entry_val E (succ_in (t_L T) (hs_addr p)) (vin (hs_addr p) (t_L T))) p *
   VST.msl.iter_sepcon.iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) (hs_addr p))).
Proof.
  intros FC W HS. unfold itable. rewrite (hkp5_o0D_split _ _ _ _ _ HS).
  unfold pool_item_rep at 1, entry_at. rewrite hkp5_o0D_entry by exact FC.
  apply pred_ext; entailer!.
Qed.

Lemma hkp5_o0D_close sht tab T p she E :
  @field_compatible Noise.CS t_peer [] p -> itable_wf T -> sfind (t_D T) (hs_addr p) = Some (she, E) ->
  (@data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab *
   @field_at W_keypairs she (Tstruct KC._wg_peer noattr) [StructField KC._entry; StructField KC._handshake]
     (e_peer E, (succ_in (t_L T) (hs_addr p), (Val.of_bool (vin (hs_addr p) (t_L T)), (Vint (e_type E), Vint (e_index E))))) p *
   VST.msl.iter_sepcon.iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) (hs_addr p)))
  |-- itable sht tab T.
Proof. intros FC W HS. rewrite (hkp5_o0D_open sht tab T p she E FC W HS). apply derives_refl. Qed.

(* the loop state after the dead branch: one allocation and one free more, keypair_counter + 1, the handshake
   zeroed, m_frees + 1, next_id + 1 if known; hk5_rel looks neither at m_frees nor at P's handshake *)
Lemma hkp5_o0D_inv F V S w kc P KS T ML sp sc sn fr mw now next_id id_known hsn :
  hkp5_inv0 F V (mkKY5 S w kc P KS T (mkH5 ML sp sc sn fr mw) now next_id id_known hsn) ->
  hkp5_inv0 F V (mkKY5 (shim_free (shim_alloc_ok S)) w (Int64.add kc Int64.one) (p_set_hs P (hs_zero (p_hs P)))
     KS T (mkH5 ML sp sc sn (Int64.add fr Int64.one) mw) now
     (if id_known then Int64.add next_id Int64.one else next_id) id_known hsn).
Proof.
  intros (Hrel & Hw & Hdev & Hsid & Hrefs & Hfr & Hal & Hid & Hnow & Hpk).
  unfold hkp5_inv0.
  cbn [y_S y_w y_kc y_P y_KS y_T y_H y_now y_next_id y_id_known y_hsn h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn
       shim_free shim_alloc_ok s_frees s_allocs p_set_hs p_device p_hs p_refs hs_zero hs_sid] in *.
  split; [exact Hrel |]. split; [exact Hw |].
  split; [exact Hdev |]. split; [exact Hsid |]. split; [exact Hrefs |].
  split; [rewrite Int64.sub_add_l, Hfr; reflexivity |].
  split; [rewrite Int64.sub_add_l, Hal, !Int64.add_assoc, (Int64.add_commut _ Int64.one); reflexivity |].
  split; [| exact (conj Hnow Hpk)].
  intros Ek. rewrite Ek in *. rewrite (Hid eq_refl). reflexivity.
Qed.

Lemma hkp5_segOp0_D_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps FR i R (O: hkp5_o0) :
  hkp5_model_facts -> x25519_props x25519 -> p_dead (y_P (o_Y O)) = true ->
  semax (hkp5_Delta hkp5_G_Op0) (hkp5_o0_M2 x25519 F V steps FR i O) hkp5_o0_sD
    (overridePost (hkp5_o0_Z x25519 F V steps FR i) R).
Proof.
  intros HF HX Hd.
  destruct O as [Y E k kp]. cbn [o_Y o_E o_k o_kp] in *.
  destruct F as [gv w t pt p raw pub snap opub first second].
  destruct Y as [S ws kc P KS T HH now next_id id_known hsn].
  cbn [y_S y_w y_kc y_P y_KS y_T y_H y_now y_next_id y_id_known y_hsn] in Hd.
  unfold hkp5_o0_M2, hkp5_Delta.
  unfold hkp5_o0_props, hkp5_o0_locals, hkp5_o0_SEP, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars,
    hkp5_o0_stok, o5_res, o5_w, o5_sn.
  cbv zeta.
  cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second o_Y o_E o_k o_kp
       y_S y_w y_kc y_P y_KS y_T y_H y_now y_next_id y_id_known y_hsn].
  Intros.
  match goal with Hst: orb _ _ = true |- _ => rename Hst into Hstok end.
  match goal with Hk: kp <> nullval |- _ => rename Hk into Hkp end.
  rewrite (hkp5_o0_res_dead P p kp kc KS T S Hstok Hkp Hd).
  rewrite (hkp5_o0_warn_dead P (hs_addr p) kp kc (mkKW KS T S) ws Hd).
  cbn [fst snd kw_S kw_KS kw_T]. rewrite Hd.
  destruct R as [Rn Rb Rc Rr]. unfold overridePost.
  abbreviate_semax.
  match goal with H: hkp5_inv0 _ _ _ |- _ => pose proof H as Hinv; destruct H as (Hrel & _) end.
  cbn [f_p y_H y_P y_KS y_T] in Hrel.
  match goal with H: t_entry T (hs_addr p) = Some E |- _ => rename H into HE end.
  set (sn := snap_of T (hs_addr p) E (p_hs P)) in *.
  assert (Hpool: hk5_pool p (v_OD V) (v_OH V) KS T) by (destruct Hrel as ((_ & _ & _ & _ & _ & _ & _ & _ & Hp) & _); exact Hp).
  assert (HS: sfind (t_D T) (hs_addr p) = Some (Tsh, E)).
  { destruct Hpool as (_ & _ & _ & _ & (idx & Hf) & _).
    unfold t_entry in HE. rewrite Hf in HE |- *. injection HE as <-. reflexivity. }
  assert (HW: itable_wf T) by (destruct Hpool as (_ & _ & _ & _ & _ & _ & _ & Hwf); exact Hwf).
  assert_PROP (@field_compatible Noise.CS t_peer [] p) as Hfcp by (unfold peer_rep; entailer!).
  rewrite (hkp5_o0D_open Tsh t T p Tsh E Hfcp HW HS).
  rewrite (@data_at_change_composite HCS W_keypairs hkp5_o0D_CCEh Tsh t_hsnap (hsnap_val sn) (hsnap_val sn) (JMeq_refl _) hkp5_o0D_snapcs).
  unfold entry_val, hsnap_val, sn, snap_of. cbn [sn_entry sn_next sn_hashed sn_hs].
  unfold shim_state4 at 1, shim_core at 1. Intros.
  match goal with Hs: shim_ok _ |- _ => rename Hs into HSok end.
  rewrite (@hkp5_o0D_tulong_cs Noise.CS W_keypairs _ _ (gv _wg_shim_frees)).
  change _wg_shim_frees with KC._wg_shim_frees.
  unfold hkp5_o0_sD.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  + apply ENTAIL_refl.
  + match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp KC._t'24 (Vint Int.one) :: Q) (SEPx R))) end.
    { forward. forward. entailer!.
      unfold shim_free, shim_alloc_ok; cbn [s_frees]. unfold Int64.cmpu. change (Int64.repr 1) with Int64.one.
      rewrite Int64.eq_true. reflexivity. }
    { exfalso. auto. }
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp KC._t'25 (Vint Int.one) :: Q) (SEPx R))) end.
    { forward. { entailer!. apply hkp5_o0D_tc_bool. }
      forward.
      forward. entailer!. destruct (vin (hs_addr p) (t_L T)); reflexivity. }
    { exfalso. match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp KC._t'26 (Vint Int.one) :: Q) (SEPx R))) end.
    { forward. forward. forward. entailer!. simpl. rewrite Int.eq_true. reflexivity. }
    { exfalso. match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
    forward_if.
    { forward_call tt. all: first [match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end | entailer!]. }
    forward. entailer!.
  + forward. apply ENTAIL_refl.
  + forward. forward.
    forward_if (temp KC._next_id (Vlong (if id_known then Int64.add next_id Int64.one else next_id))).
    { forward. entailer!. destruct id_known; [reflexivity |].
      exfalso. match goal with Hc: _ <> Int.zero |- _ => apply Hc; reflexivity end. }
    { forward. entailer!. destruct id_known; [| reflexivity].
      exfalso. match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
    rewrite (@hkp5_o0D_tulong_cs W_keypairs Noise.CS _ _ (gv KC._wg_shim_frees)).
    change KC._wg_shim_frees with _wg_shim_frees.
    sep_apply (hkp5_o0D_shim_fold gv (shim_free (shim_alloc_ok S)) HSok).
    sep_apply (hkp5_o0D_close Tsh t T p Tsh E Hfcp HW HS).
    forward_call (t_mk5, k, gv).
    { rewrite if_false by auto. cancel. }
    destruct HH as [ML sp sc sn0 fr mw]. cbn [h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn] in *.
    pose proof (hkp5_o0D_inv _ V S ws kc P KS T ML sp sc sn0 fr mw now next_id id_known hsn Hinv) as Hinv'.
    sep_apply (hkp5_o0D_hout _ first (hkp5_o0D_kdf1_len (hs_ck (p_hs P)) [])).
    sep_apply (hkp5_o0D_hout _ second (hkp5_o0D_kdf2_len (hs_ck (p_hs P)) [])).
    sep_apply (data_at_data_at_ Tsh t_hsnap).
    rewrite <- (@data_at__change_composite HCS W_keypairs hkp5_o0D_CCEh Tsh t_hsnap hkp5_o0D_snapcs).
    change (Int64.repr (Int.signed (Int.repr 1))) with Int64.one.
    unfold hkp5_o0_Z.
    Exists (mkKY5 (shim_free (shim_alloc_ok S)) ws (Int64.add kc Int64.one) (p_set_hs P (hs_zero (p_hs P))) KS T
      (mkH5 ML sp sc sn0 (Int64.add fr Int64.one) mw) now (if id_known then Int64.add next_id Int64.one else next_id)
      id_known hsn).
    unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
    cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second y_S y_w y_kc y_P y_KS y_T y_H y_now
       y_next_id y_id_known y_hsn h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn].
    unfold shim_state4.
    entailer!.
Qed.
