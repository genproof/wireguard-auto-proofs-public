(* law replay: main's segment A (statements 0..14: draws, wg_noise_init, setup_device x2, m_identity_of x2,
   setup_peer x2 with their entries added to the index tables' pools, m_precomputed).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.protocol.prot_prog3.
Require Import WgNoise.proof.harness.common.hc_prog3.
Require Import WgNoise.proof.harness.replay.hrp3_spec.
Require Import WgNoise.proof.harness.replay.hrp3_model.
Require Import WgNoise.proof.harness.replay.hrp3_defs.
Require WgNoise.contracts.x_replay.
Require WgNoise.harness.x_replay.code.
Require Import WgNoise.proof.libc.libc_bytes.

#[local] Existing Instance W_replay.
Local Open Scope Z_scope.

#[local] Instance hrp3_segA_CCE_NW : change_composite_env Noise.CS W_replay.
Proof. make_cs_preserve Noise.CS W_replay. Defined.
#[local] Instance hrp3_segA_CCE_HW : change_composite_env HCS W_replay.
Proof. make_cs_preserve HCS W_replay. Defined.

Lemma hrp3_segA_conv_dev sh v :
  @data_at_ W_replay sh (Tstruct RC._wg_device noattr) v = @data_at_ Noise.CS sh t_dev v.
Proof. symmetry. exact (equal_f (@data_at__change_composite Noise.CS W_replay _ sh t_dev eq_refl) v). Qed.
Lemma hrp3_segA_conv_itab sh v :
  @data_at_ W_replay sh (Tstruct RC._index_hashtable noattr) v = @data_at_ Noise.CS sh t_itab v.
Proof. symmetry. exact (equal_f (@data_at__change_composite Noise.CS W_replay _ sh t_itab eq_refl) v). Qed.
Lemma hrp3_segA_conv_ptab sh v :
  @data_at_ W_replay sh (Tstruct RC._pubkey_hashtable noattr) v = @data_at_ Noise.CS sh t_ptab v.
Proof. symmetry. exact (equal_f (@data_at__change_composite Noise.CS W_replay _ sh t_ptab eq_refl) v). Qed.
Lemma hrp3_segA_conv_peer sh v :
  @data_at_ W_replay sh (Tstruct RC._wg_peer noattr) v = @data_at_ Noise.CS sh t_peer v.
Proof. symmetry. exact (equal_f (@data_at__change_composite Noise.CS W_replay _ sh t_peer eq_refl) v). Qed.
Lemma hrp3_segA_conv_mident sh v :
  @data_at_ W_replay sh (Tstruct RC._m_identity noattr) v = @data_at_ HCS sh t_mident v.
Proof. symmetry. exact (equal_f (@data_at__change_composite HCS W_replay _ sh t_mident eq_refl) v). Qed.
Lemma hrp3_segA_conv_mcinit sh v :
  @data_at_ W_replay sh (Tstruct RC._m_consumed_initiation noattr) v = @data_at_ HCS sh t_mcinit v.
Proof. symmetry. exact (equal_f (@data_at__change_composite HCS W_replay _ sh t_mcinit eq_refl) v). Qed.
Lemma hrp3_segA_conv_hsnap sh v :
  @data_at_ W_replay sh (Tstruct RC._hs_snap noattr) v = @data_at_ HCS sh t_hsnap v.
Proof. symmetry. exact (equal_f (@data_at__change_composite HCS W_replay _ sh t_hsnap eq_refl) v). Qed.
Lemma hrp3_segA_conv_bytes sh n v :
  @data_at_ W_replay sh (tarray tuchar n) v = hout sh n v.
Proof. unfold hout. apply data_at__tarray_tuchar_cs. Qed.

Lemma hrp3_segA_nd sh n bs p : Zlength bs = n -> Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  @data_at W_replay sh (tarray tuchar n) (map (fun b => Vint (Int.repr b)) bs) p = hbytes sh (map Byte.repr bs) p.
Proof.
  intros <- HB. unfold hbytes. rewrite Zlength_map. rewrite (@data_at_tarray_tuchar_cs W_replay HCS). f_equal.
  unfold bytes. rewrite map_map. apply map_ext_Forall. eapply Forall_impl; [|exact HB]. intros b Hb.
  unfold Vubyte. rewrite Byte.unsigned_repr by exact Hb. reflexivity.
Qed.

Lemma hrp3_segA_msplit sh I p : Zlength (mi_priv I) = 32 -> Zlength (mi_pub I) = 32 ->
  @data_at HCS sh t_mident (mident_val I) p =
  (!! (@field_compatible HCS t_mident [] p) &&
   (@field_at HCS sh t_mident (DOT HH._priv) (bytes (mi_priv I)) p *
    hbytes sh (mi_pub I) (offset_val 32 p) *
    @field_at HCS sh t_mident (DOT HH._ok) (Vint (if mi_ok I then Int.one else Int.zero)) p))%logic.
Proof.
  intros L1 L2. apply pred_ext.
  - assert_PROP (@field_compatible HCS t_mident [] p) by entailer!.
    unfold_data_at (@data_at HCS sh t_mident (mident_val I) p).
    rewrite (@field_at_data_at HCS sh t_mident (DOT HH._pub)).
    rewrite (@field_address_offset HCS) by auto with field_compatible.
    unfold hbytes. rewrite L2. entailer!.
  - Intros. unfold_data_at (@data_at HCS sh t_mident (mident_val I) p).
    rewrite (@field_at_data_at HCS sh t_mident (DOT HH._pub)).
    rewrite (@field_address_offset HCS) by auto with field_compatible.
    unfold hbytes. rewrite L2. entailer!.
Qed.

Lemma hrp3_segA_mfold sh I p : @field_compatible HCS t_mident [] p ->
  Zlength (mi_priv I) = 32 -> Zlength (mi_pub I) = 32 ->
  (@field_at HCS sh t_mident (DOT HH._priv) (bytes (mi_priv I)) p *
   hbytes sh (mi_pub I) (offset_val 32 p) *
   @field_at HCS sh t_mident (DOT HH._ok) (Vint (if mi_ok I then Int.one else Int.zero)) p)%logic
  |-- @data_at HCS sh t_mident (mident_val I) p.
Proof. intros FC L1 L2. rewrite hrp3_segA_msplit by auto. apply andp_right; [apply prop_right; exact FC | apply derives_refl]. Qed.

Lemma hrp3_segA_and1 ub : 0 <= ub <= Byte.max_unsigned ->
  Int.and (Int.repr ub) (Int.repr 1) = if Z.odd ub then Int.one else Int.zero.
Proof.
  intros H. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia.
  change 1 with (Z.ones 1). rewrite Z.land_ones by lia. rewrite Zmod_odd.
  destruct (Z.odd ub); reflexivity.
Qed.

Lemma hrp3_segA_pskx sh PSK psk (u: bool) : isptr psk ->
  hbytes sh PSK psk =
  ((if eq_dec (if u then psk else nullval) nullval then emp else hbytes sh PSK (if u then psk else nullval)) *
   (if eq_dec (if u then psk else nullval) nullval then hbytes sh PSK psk else emp))%logic.
Proof.
  intros Hp. destruct u.
  - destruct (eq_dec psk nullval); [subst; contradiction|]. rewrite sepcon_emp. reflexivity.
  - rewrite if_true by reflexivity. rewrite emp_sepcon. reflexivity.
Qed.

Lemma hrp3_segA_pskv PSK psk (u: bool) : isptr psk ->
  (if eq_dec (if u then psk else nullval) nullval then zeros32 else PSK) = (if u then PSK else zeros32).
Proof.
  intros Hp. destruct u.
  - destruct (eq_dec psk nullval); [subst; contradiction|]. reflexivity.
  - rewrite if_true by reflexivity. reflexivity.
Qed.

Lemma hrp3_segA_tulong_cs {cs1 cs2: compspecs} sh v p :
  @data_at cs1 sh tulong v p = @data_at cs2 sh tulong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible; simpl.
  split; intros (?&?&?&?&?); (repeat split); auto;
    destruct p; try contradiction; unfold align_compatible in *;
    (apply align_compatible_rec_by_value with Mint64; [reflexivity|]);
    apply (align_compatible_rec_by_value_inv _ _ Mint64) in H2; auto.
Qed.

Lemma hrp3_segA_shim_fold gv S : shim_ok S ->
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
   @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow) * refwarn gv)%logic
  |-- shim_state gv S.
Proof. intros H. unfold shim_state. apply andp_right; [apply prop_right; exact H | apply derives_refl]. Qed.

Lemma hrp3_segA_ok {Espec: OracleKind} x25519 aead_enc aead_dec (F: hrp3_fix) (FR: mpred) :
  hrp3_facts -> x25519_props x25519 -> aead_props aead_enc aead_dec ->
  semax (hrp3_Delta x25519 aead_enc aead_dec) (hrp3_P0 F FR) hrp3_segA
    (overridePost (hrp3_PA x25519 F FR) (hrp3_R (f_gv F))).
Proof.
  intros HF HX HA.
  destruct F as [gv wa wb ita itb pta ptb pa pb ia ib rawa rawb psk ssb latest ci snap].
  unfold hrp3_P0, hrp3_Delta, hrp3_R, hrp3_lvars, hrp3_segA. cbn [f_gv f_wa f_wb f_ita f_itb f_pta f_ptb f_pa f_pb f_ia f_ib f_rawa f_rawb f_psk f_ssb f_latest f_ci f_snap].
  abbreviate_semax.
  forward. forward.
  forward_call tt. Intros boot. unfold shim_state at 1. Intros. unfold hrp3_S0 at 1. cbn [s_boot].
  rewrite (@hrp3_segA_tulong_cs Noise.CS W_replay _ _ (gv _wg_shim_boottime_ns)).
  change _wg_shim_boottime_ns with RC._wg_shim_boottime_ns. forward.
  rewrite (@hrp3_segA_tulong_cs W_replay Noise.CS _ _ (gv RC._wg_shim_boottime_ns)).
  change RC._wg_shim_boottime_ns with _wg_shim_boottime_ns.
  sep_apply (hrp3_segA_shim_fold gv (shim_set_boot hrp3_S0 boot) H0).
  forward_call (gv, zeros32, zeros32, Int64.zero).
  forward_call (rawa, 32, Tsh). Intros bsA.
  forward_call (rawb, 32, Tsh). Intros bsB.
  forward_call tt. Intros ub.
  forward.
  forward_call (psk, 32, Tsh). Intros bsP.
  rewrite (hrp3_segA_nd _ _ _ _ H1 H2), (hrp3_segA_nd _ _ _ _ H3 H4), (hrp3_segA_nd _ _ _ _ H6 H7).
  rewrite !hrp3_segA_conv_dev, !hrp3_segA_conv_itab, !hrp3_segA_conv_ptab, !hrp3_segA_conv_peer,
    !hrp3_segA_conv_mident, !hrp3_segA_conv_mcinit, !hrp3_segA_conv_hsnap, !hrp3_segA_conv_bytes.
  assert (LA: Zlength (map Byte.repr bsA) = 32) by (rewrite Zlength_map; auto).
  assert (LB: Zlength (map Byte.repr bsB) = 32) by (rewrite Zlength_map; auto).
  assert (LP: Zlength (map Byte.repr bsP) = 32) by (rewrite Zlength_map; auto).
  forward_call (gv, shim_set_boot hrp3_S0 boot, Tsh, wa, ita, pta, Tsh, rawa, map Byte.repr bsA).
  Intros secA.
  forward_call (gv, shim_draw (shim_set_boot hrp3_S0 boot) secA, Tsh, wb, itb, ptb, Tsh, rawb, map Byte.repr bsB).
  Intros secB.
  change (s_boot (shim_set_boot hrp3_S0 boot)) with boot.
  change (s_boot (shim_draw (shim_set_boot hrp3_S0 boot) secA)) with boot.
  unfold hrp3_consts. repeat flatten_sepcon_in_SEP.
  forward_call (gv, Tsh, ia, Tsh, rawa, map Byte.repr bsA).
  forward_call (gv, Tsh, ib, Tsh, rawb, map Byte.repr bsB).
  rewrite (hrp3_segA_and1 ub H5).
  set (u := Z.odd ub).
  assert_PROP (isptr psk) as Psk by entailer!.
  set (RAWA := map Byte.repr bsA). set (RAWB := map Byte.repr bsB). set (PSK := map Byte.repr bsP).
  set (IA := mident_of x25519 RAWA). set (IB := mident_of x25519 RAWB).
  assert (LIA1: Zlength (mi_priv IA) = 32) by (unfold IA, RAWA, mident_of, clamp; cbn [mi_priv]; list_solve).
  assert (LIB1: Zlength (mi_priv IB) = 32) by (unfold IB, RAWB, mident_of, clamp; cbn [mi_priv]; list_solve).
  assert (LIA2: Zlength (mi_pub IA) = 32) by (apply HX).
  assert (LIB2: Zlength (mi_pub IB) = 32) by (apply HX).
  rewrite (hrp3_segA_msplit Tsh IB ib) by auto. Intros.
  forward_if (temp RC._t'3 (if u then psk else nullval)).
  { forward. entailer!.
    destruct u; [reflexivity | exfalso; match goal with Hx: _ <> Int.zero |- _ => apply Hx; reflexivity end]. }
  { forward. entailer!.
    destruct u; [exfalso; match goal with Hx: _ = Int.zero |- _ => apply Int.one_not_zero; exact Hx end | reflexivity]. }
  destruct HF as (HM & HR & HC).
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 HR))))) as Tadd.
  set (DA := setup_dev x25519 wa ita pta RAWA secA boot).
  set (DB := setup_dev x25519 wb itb ptb RAWB secB boot).
  rewrite (hrp3_segA_pskx Tsh PSK psk u Psk). repeat flatten_sepcon_in_SEP.
  change (ptable Tsh pta nullval) with (ptable Tsh (d_ptab DA) nullval).
  forward_call (gv, Tsh, pb, Tsh, wa, DA, nullval, Tsh, offset_val 32 ib, mi_pub IB, if u then psk else nullval, PSK,
                Int64.repr 1).
  change (ptable Tsh (d_ptab DA) pb) with (ptable Tsh pta pb).
  rewrite (hrp3_segA_pskv PSK psk u Psk).
  sep_apply (Tadd Tsh ita (mkT [] []) (hs_addr pb) Tsh (mkEntry pb IDX_HANDSHAKE Int.zero) writable_share_top).
  sep_apply (derives_refl' _ _ (eq_sym (hrp3_segA_pskx Tsh PSK psk u Psk))).
  sep_apply (hrp3_segA_mfold Tsh IB ib H10 LIB1 LIB2).
  assert_PROP (@field_compatible HCS t_mident [] ia) as FCa by entailer!.
  rewrite (hrp3_segA_msplit Tsh IA ia) by auto. Intros.
  forward_if (temp RC._t'4 (if u then psk else nullval)).
  { forward. entailer!.
    destruct u; [reflexivity | exfalso; match goal with Hx: _ <> Int.zero |- _ => apply Hx; reflexivity end]. }
  { forward. entailer!.
    destruct u; [exfalso; match goal with Hx: _ = Int.zero |- _ => apply Int.one_not_zero; exact Hx end | reflexivity]. }
  rewrite (hrp3_segA_pskx Tsh PSK psk u Psk). repeat flatten_sepcon_in_SEP.
  change (ptable Tsh ptb nullval) with (ptable Tsh (d_ptab DB) nullval).
  forward_call (gv, Tsh, pa, Tsh, wb, DB, nullval, Tsh, offset_val 32 ia, mi_pub IA, if u then psk else nullval, PSK,
                Int64.repr 2).
  change (ptable Tsh (d_ptab DB) pa) with (ptable Tsh ptb pa).
  rewrite (hrp3_segA_pskv PSK psk u Psk).
  sep_apply (Tadd Tsh itb (mkT [] []) (hs_addr pa) Tsh (mkEntry pa IDX_HANDSHAKE Int.zero) writable_share_top).
  sep_apply (derives_refl' _ _ (eq_sym (hrp3_segA_pskx Tsh PSK psk u Psk))).
  forward_call (Tsh, ssb, Tsh, ib, IB, Tsh, offset_val 32 ia, mi_pub IA).
  sep_apply (hrp3_segA_mfold Tsh IA ia FCa LIA1 LIA2).
  unfold hrp3_PA.
  Exists (mkRVal RAWA RAWB PSK u secA secB boot boot Int64.zero)
         (shim_draw (shim_draw (shim_set_boot hrp3_S0 boot) secA) secB).
  unfold hrp3_globs, hrp3_consts, hrp3_fix_ok, hrp3_PB0, hrp3_PA0, hrp3_DA, hrp3_DB, hrp3_IA, hrp3_IB, hrp3_pskv,
    hrp3_SS, hrp3_TB0, hrp3_E0, hrp3_lvars.
  cbn [f_gv f_wa f_wb f_ita f_itb f_pta f_ptb f_pa f_pb f_ia f_ib f_rawa f_rawb f_psk f_ssb f_latest f_ci f_snap
       v_RAWA v_RAWB v_PSK v_use v_secA v_secB v_bootA v_bootB v_kc app].
  fold DA DB IA IB.
  entailer!.
  apply derives_refl.
Qed.
