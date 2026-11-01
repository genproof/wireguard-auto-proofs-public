(* (port of v1's hca3_F0b_lib.v), law create_any: segment F0b, separation-logic helpers shared by its pieces (hca5_F0b_defs.v):
   byte-buffer windows (exp), the snapshot structs s / x opened at their byte fields, m_state at its fields,
   the device's static public key, the shim's random_log / random_u32, the harness's constants as hbytes. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.create_any.hca3_model.
Require Import WgNoise.proof.harness.create_any.hca5_defs.
Require WgNoise.harness.x_create_any.code.
Local Open Scope logic.

#[local] Instance hca5_F0b_cceN : change_composite_env Noise.CS W_create_any.
Proof. make_cs_preserve Noise.CS W_create_any. Defined.
#[local] Instance hca5_F0b_cceH : change_composite_env HCS W_create_any.
Proof. make_cs_preserve HCS W_create_any. Defined.
#[local] Existing Instance HCS.

(* byte arrays are the same in every compspecs *)
Lemma hca5_F0b_bytes_HN (sh: share) n (v: list val) p :
  @data_at HCS sh (tarray tuchar n) v p = @data_at Noise.CS sh (tarray tuchar n) v p.
Proof.
  rewrite (@data_at_change_composite HCS W_create_any _ sh (tarray tuchar n) v v),
    (@data_at_change_composite Noise.CS W_create_any _ sh (tarray tuchar n) v v); auto.
Qed.
Lemma hca5_F0b_bytes_HW (sh: share) n (v: list val) p :
  @data_at HCS sh (tarray tuchar n) v p = @data_at W_create_any sh (tarray tuchar n) v p.
Proof. rewrite (@data_at_change_composite HCS W_create_any _ sh (tarray tuchar n) v v); auto. Qed.

(* ---------------------------------------------------------------------- *)
(* byte buffers: a window [o, o+n) of b                                    *)
(* ---------------------------------------------------------------------- *)

Lemma hca5_F0b_Zlength_put b o w : 0 <= o -> o + Zlength w <= Zlength b ->
  Zlength (hca3_put b o w) = Zlength b.
Proof. intros. unfold hca3_put. list_solve. Qed.

Lemma hca5_F0b_hbytes_fc sh b p : hbytes sh b p |-- !! field_compatible (tarray tuchar (Zlength b)) [] p.
Proof. unfold hbytes. entailer!. Qed.

Lemma hca5_F0b_hout sh bs n p : Zlength bs = n -> hbytes sh bs p |-- hout sh n p.
Proof. intros <-. unfold hbytes, hout. apply data_at_data_at_. Qed.

Lemma hca5_F0b_hin sh bs p : Zlength bs <> 0 -> hin sh bs p = hbytes sh bs p.
Proof. intros. unfold hin. rewrite if_false by auto. reflexivity. Qed.

(* open the window: the prefix, n writable bytes at o, the suffix *)
Lemma hca5_F0b_open sh b o n p : 0 <= o -> 0 <= n -> o + n <= Zlength b ->
  hbytes sh b p |--
  !! field_compatible (tarray tuchar (Zlength b)) [] p &&
  (hbytes sh (sublist 0 o b) p * hout sh n (offset_val o p) *
   hbytes sh (sublist (o + n) (Zlength b) b) (offset_val (o + n) p)).
Proof.
  intros H0 H1 H2. unfold hbytes, hout. assert_PROP (field_compatible (tarray tuchar (Zlength b)) [] p) as FC
    by entailer!.
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh (Zlength b) o (o + n)) by (unfold bytes; list_solve).
  rewrite !field_address0_offset by auto with field_compatible. simpl nested_field_offset.
  rewrite !Z.mul_1_l, !Z.add_0_l.
  rewrite !Zlength_sublist by lia. unfold bytes. rewrite !sublist_map.
  replace (o + n - o) with n by lia. replace (o - 0) with o by lia.
  entailer!.
Qed.

(* close it with w written at o *)
Lemma hca5_F0b_close sh b o w p : 0 <= o -> o + Zlength w <= Zlength b ->
  field_compatible (tarray tuchar (Zlength b)) [] p ->
  hbytes sh (sublist 0 o b) p * hbytes sh w (offset_val o p) *
  hbytes sh (sublist (o + Zlength w) (Zlength b) b) (offset_val (o + Zlength w) p) |--
  hbytes sh (hca3_put b o w) p.
Proof.
  intros H0 H1 FC. pose proof (Zlength_nonneg w). unfold hbytes. rewrite hca5_F0b_Zlength_put by lia.
  assert (Zlength (hca3_put b o w) = Zlength b) as HL by (apply hca5_F0b_Zlength_put; lia).
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh (Zlength b) o (o + Zlength w));
    [| lia | lia | unfold bytes; rewrite Zlength_map; auto].
  rewrite !field_address0_offset by auto with field_compatible. simpl nested_field_offset.
  rewrite !Z.mul_1_l, !Z.add_0_l.
  replace (sublist 0 o (bytes (hca3_put b o w))) with (bytes (sublist 0 o b))
    by (unfold bytes, hca3_put; list_solve).
  replace (sublist o (o + Zlength w) (bytes (hca3_put b o w))) with (bytes w)
    by (unfold bytes, hca3_put; list_solve).
  replace (sublist (o + Zlength w) (Zlength b) (bytes (hca3_put b o w)))
    with (bytes (sublist (o + Zlength w) (Zlength b) b))
    by (unfold bytes, hca3_put; list_solve).
  rewrite !Zlength_sublist by lia. replace (o + Zlength w - o) with (Zlength w) by lia.
  replace (o - 0) with o by lia. cancel.
Qed.

(* ---------------------------------------------------------------------- *)
(* the snapshot struct (HCS) opened at its five byte fields and state      *)
(* ---------------------------------------------------------------------- *)

(* the fields the block never touches *)
Definition hca5_F0b_srest (sh: share) (sn: hsnap) (p: val) : mpred :=
  let E := sn_entry sn in let H := sn_hs sn in
  !! (@field_compatible HCS t_hsnap [] p) &&
  (@field_at HCS sh t_hsnap [StructField HC._peer] (e_peer E) p *
   @field_at HCS sh t_hsnap [StructField HC._next] (sn_next sn) p *
   @field_at HCS sh t_hsnap [StructField HC._hashed] (Val.of_bool (sn_hashed sn)) p * spacer sh 17 20 p *
   @field_at HCS sh t_hsnap [StructField HC._type] (Vint (e_type E)) p *
   @field_at HCS sh t_hsnap [StructField HC._index] (Vint (e_index E)) p *
   @field_at HCS sh t_hsnap [StructField HC._last_initiation_consumption] (Vlong (hs_lic H)) p *
   @field_at HCS sh t_hsnap [StructField HC._static_identity] (hs_sid H) p *
   @field_at HCS sh t_hsnap [StructField HC._remote_ephemeral] (bytes (hs_reph H)) p *
   @field_at HCS sh t_hsnap [StructField HC._preshared_key] (bytes (hs_psk H)) p *
   @field_at HCS sh t_hsnap [StructField HC._latest_timestamp] (bytes (hs_ts H)) p *
   @field_at HCS sh t_hsnap [StructField HC._remote_index] (Vint (hs_rindex H)) p).

Lemma hca5_F0b_fb_eph sh (bs: list byte) p : @field_compatible HCS t_hsnap [] p -> Zlength bs = 32 ->
  @field_at HCS sh t_hsnap (DOT HC._ephemeral_private) (bytes bs) p = hbytes sh bs (offset_val 48 p).
Proof. intros. rewrite field_at_data_at, field_address_offset by auto with field_compatible. unfold hbytes; rewrite H0. reflexivity. Qed.
Lemma hca5_F0b_fb_rs sh (bs: list byte) p : @field_compatible HCS t_hsnap [] p -> Zlength bs = 32 ->
  @field_at HCS sh t_hsnap (DOT HC._remote_static) (bytes bs) p = hbytes sh bs (offset_val 80 p).
Proof. intros. rewrite field_at_data_at, field_address_offset by auto with field_compatible. unfold hbytes; rewrite H0. reflexivity. Qed.
Lemma hca5_F0b_fb_ss sh (bs: list byte) p : @field_compatible HCS t_hsnap [] p -> Zlength bs = 32 ->
  @field_at HCS sh t_hsnap (DOT HC._precomputed_static_static) (bytes bs) p = hbytes sh bs (offset_val 144 p).
Proof. intros. rewrite field_at_data_at, field_address_offset by auto with field_compatible. unfold hbytes; rewrite H0. reflexivity. Qed.
Lemma hca5_F0b_fb_h sh (bs: list byte) p : @field_compatible HCS t_hsnap [] p -> Zlength bs = 32 ->
  @field_at HCS sh t_hsnap (DOT HC._hash) (bytes bs) p = hbytes sh bs (offset_val 208 p).
Proof. intros. rewrite field_at_data_at, field_address_offset by auto with field_compatible. unfold hbytes; rewrite H0. reflexivity. Qed.
Lemma hca5_F0b_fb_ck sh (bs: list byte) p : @field_compatible HCS t_hsnap [] p -> Zlength bs = 32 ->
  @field_at HCS sh t_hsnap (DOT HC._chaining_key) (bytes bs) p = hbytes sh bs (offset_val 240 p).
Proof. intros. rewrite field_at_data_at, field_address_offset by auto with field_compatible. unfold hbytes; rewrite H0. reflexivity. Qed.
Lemma hca5_F0b_f_state sh (v: val) p :
  @field_at HCS sh t_hsnap (DOT HC._state) v p = @field_at W_create_any sh t_hsnap (DOT HC._state) v p.
Proof.
  exact (f_equal (fun f => f p) (@field_at_change_composite HCS W_create_any hca5_F0b_cceH sh t_hsnap (DOT HC._state) v v
    (@JMeq_refl _ v) ltac:(vm_compute; reflexivity))).
Qed.

Lemma hca5_F0b_snap_split0 sh sn p : hs_ok (sn_hs sn) -> @field_compatible HCS t_hsnap [] p ->
  @data_at HCS sh t_hsnap (hsnap_val sn) p =
  hbytes sh (hs_eph (sn_hs sn)) (offset_val 48 p) *
  hbytes sh (hs_rstatic (sn_hs sn)) (offset_val 80 p) *
  hbytes sh (hs_ss (sn_hs sn)) (offset_val 144 p) *
  hbytes sh (hs_hash (sn_hs sn)) (offset_val 208 p) *
  hbytes sh (hs_ck (sn_hs sn)) (offset_val 240 p) *
  @field_at W_create_any sh t_hsnap [StructField HC._state] (Vint (hs_state (sn_hs sn))) p *
  hca5_F0b_srest sh sn p.
Proof.
  intros (He & Hr & _ & Hs & _ & Hh & Hc & _) FC.
  destruct sn as [En nx hd H]; unfold hsnap_val; cbn [sn_hs sn_entry sn_next sn_hashed] in *.
  unfold hca5_F0b_srest; cbn [sn_hs sn_entry sn_next sn_hashed].
  unfold_data_at (data_at _ _ _ p).
  rewrite <- (hca5_F0b_fb_eph sh _ p FC He), <- (hca5_F0b_fb_rs sh _ p FC Hr), <- (hca5_F0b_fb_ss sh _ p FC Hs),
    <- (hca5_F0b_fb_h sh _ p FC Hh), <- (hca5_F0b_fb_ck sh _ p FC Hc), <- hca5_F0b_f_state.
  apply pred_ext; entailer!.
Qed.

(* field offsets of struct hs_snap: ephemeral_private 48, remote_static 80, precomputed_static_static 144,
   hash 208, chaining_key 240 *)
Lemma hca5_F0b_snap_split sh sn p : hs_ok (sn_hs sn) ->
  @data_at HCS sh t_hsnap (hsnap_val sn) p =
  hbytes sh (hs_eph (sn_hs sn)) (offset_val 48 p) *
  hbytes sh (hs_rstatic (sn_hs sn)) (offset_val 80 p) *
  hbytes sh (hs_ss (sn_hs sn)) (offset_val 144 p) *
  hbytes sh (hs_hash (sn_hs sn)) (offset_val 208 p) *
  hbytes sh (hs_ck (sn_hs sn)) (offset_val 240 p) *
  @field_at W_create_any sh t_hsnap [StructField HC._state] (Vint (hs_state (sn_hs sn))) p *
  hca5_F0b_srest sh sn p.
Proof.
  intros Hok. apply pred_ext.
  - assert_PROP (@field_compatible HCS t_hsnap [] p) as FC by entailer!.
    rewrite (hca5_F0b_snap_split0 sh sn p Hok FC). auto.
  - assert_PROP (@field_compatible HCS t_hsnap [] p) as FC by (unfold hca5_F0b_srest; entailer!).
    rewrite (hca5_F0b_snap_split0 sh sn p Hok FC). auto.
Qed.

Lemma hca5_F0b_srest_ckh sh E nx hd H ck h p :
  hca5_F0b_srest sh (mkSnap E nx hd (hs_set_ckh H ck h)) p = hca5_F0b_srest sh (mkSnap E nx hd H) p.
Proof. reflexivity. Qed.
Lemma hca5_F0b_srest_eph sh E nx hd H e p :
  hca5_F0b_srest sh (mkSnap E nx hd (hs_set_eph H e)) p = hca5_F0b_srest sh (mkSnap E nx hd H) p.
Proof. reflexivity. Qed.
Lemma hca5_F0b_srest_state sh E nx hd H s p :
  hca5_F0b_srest sh (mkSnap E nx hd (hs_set_state H s)) p = hca5_F0b_srest sh (mkSnap E nx hd H) p.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* m_state (HCS) at its fields ck (offset 0) and h (offset 32)             *)
(* ---------------------------------------------------------------------- *)

Lemma hca5_F0b_st_split sh ck h p : Zlength ck = 32 -> Zlength h = 32 ->
  @data_at HCS sh t_mstate (mstate_val ck h) p =
  !! (@field_compatible HCS t_mstate [] p) && (hbytes sh ck p * hbytes sh h (offset_val 32 p)).
Proof.
  intros Hc Hh. unfold mstate_val. apply pred_ext.
  - assert_PROP (@field_compatible HCS t_mstate [] p) as FC by entailer!.
    unfold_data_at (data_at _ _ _ p).
    rewrite !field_at_data_at, !field_address_offset by auto with field_compatible.
    unfold hbytes. rewrite Hc, Hh. simpl nested_field_offset. rewrite isptr_offset_val_zero by auto with field_compatible.
    entailer!.
  - Intros. unfold_data_at (data_at _ _ _ p).
    rewrite !field_at_data_at, !field_address_offset by auto with field_compatible.
    unfold hbytes. rewrite Hc, Hh. simpl nested_field_offset. rewrite isptr_offset_val_zero by auto with field_compatible.
    entailer!.
Qed.

(* ---------------------------------------------------------------------- *)
(* the device: wa.static_identity.static_public (offset 8)                 *)
(* ---------------------------------------------------------------------- *)

Definition hca5_F0b_drest (sh: share) (wg: val) (D: device) : mpred :=
  !! (@field_compatible Noise.CS t_dev [] wg /\ id_ok (d_id D)) &&
  (@field_at Noise.CS sh t_dev [StructField I._dev] (d_dev D) wg *
   (EX lk: val, @field_at Noise.CS sh t_sid [StructField I._static_private] (bytes (id_priv (d_id D))) (id_addr wg) *
                @field_at Noise.CS sh t_sid [StructField I._lock] lk (id_addr wg) *
                @field_at Noise.CS sh t_sid [StructField I._has_identity] (Val.of_bool (id_has (d_id D))) (id_addr wg) *
                spacer sh 69 72 (id_addr wg)) *
   checker_rep sh (cc_addr wg) (d_cc D) *
   @field_at Noise.CS sh t_dev [StructField I._peer_hashtable] (d_ptab D) wg *
   @field_at Noise.CS sh t_dev [StructField I._index_hashtable] (d_itab D) wg).

Lemma hca5_F0b_dev_split sh wg D :
  device_rep sh wg D = hbytes sh (id_pub (d_id D)) (offset_val 8 wg) * hca5_F0b_drest sh wg D.
Proof.
  unfold device_rep, identity_rep, hca5_F0b_drest. apply pred_ext.
  - Intros lk. unfold_data_at (@data_at Noise.CS _ t_sid _ _).
    assert (FC: @field_compatible Noise.CS t_sid [] (id_addr wg)).
    { assert (F1: @field_compatible Noise.CS t_dev (DOT I._static_identity) wg) by auto with field_compatible.
      pose proof (@field_compatible_nested_field Noise.CS _ _ _ F1) as F2. unfold id_addr, OFS_DEV_IDENTITY.
      simpl in F2. exact F2. }
    pose proof H0 as [Hp _].
    rewrite (@field_at_data_at Noise.CS sh t_sid (DOT noise.code._static_public)),
      (@field_address_offset Noise.CS) by auto with field_compatible.
    unfold hbytes. rewrite Hp. unfold id_addr, OFS_DEV_IDENTITY. simpl nested_field_offset. simpl nested_field_type.
    rewrite offset_offset_val, Z.add_0_r, hca5_F0b_bytes_HN. Exists lk. entailer!; apply derives_refl.
  - Intros lk. Exists lk. unfold_data_at (@data_at Noise.CS _ t_sid _ _).
    assert (FC: @field_compatible Noise.CS t_sid [] (id_addr wg)).
    { assert (F1: @field_compatible Noise.CS t_dev (DOT I._static_identity) wg) by auto with field_compatible.
      pose proof (@field_compatible_nested_field Noise.CS _ _ _ F1) as F2. unfold id_addr, OFS_DEV_IDENTITY.
      simpl in F2. exact F2. }
    pose proof H0 as [Hp Hq].
    rewrite (@field_at_data_at Noise.CS sh t_sid (DOT noise.code._static_public)),
      (@field_address_offset Noise.CS) by auto with field_compatible.
    unfold hbytes. rewrite Hp. unfold id_addr, OFS_DEV_IDENTITY. simpl nested_field_offset. simpl nested_field_type.
    rewrite offset_offset_val, Z.add_0_r, hca5_F0b_bytes_HN. entailer!; apply derives_refl.
Qed.

(* ---------------------------------------------------------------------- *)
(* the shim's globals: random_log, random_u32                              *)
(* ---------------------------------------------------------------------- *)

Definition hca5_F0b_shrest (gv: globals) (S: shim) (w: list int64) : mpred :=
  !! shim_ok S &&
  (@data_at Noise.CS Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
   @data_at Noise.CS Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
   @data_at Noise.CS Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
   @data_at Noise.CS Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   @data_at Noise.CS Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
   @data_at Noise.CS Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   @data_at Noise.CS Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow) *
   refwarn4 gv w).

(* random_log as an hbytes at the harness's name of the global; random_u32 at the world *)
Lemma hca5_F0b_shim_split gv S w :
  shim_state4 gv S w =
  !! (Zlength (s_log S) = 32) &&
  (hbytes Ews (s_log S) (gv HC._wg_shim_random_log) *
   @data_at W_create_any Ews tuint (Vint (s_u32 S)) (gv HC._wg_shim_random_u32) *
   hca5_F0b_shrest gv S w).
Proof.
  unfold shim_state4, shim_core, hca5_F0b_shrest, hbytes.
  change (gv HC._wg_shim_random_log) with (gv _wg_shim_random_log).
  change (gv HC._wg_shim_random_u32) with (gv _wg_shim_random_u32).
  rewrite <- (@data_at_change_composite Noise.CS W_create_any _ Ews tuint (Vint (s_u32 S)) (Vint (s_u32 S)))
    by auto.
  apply pred_ext.
  - Intros. pose proof H as [Hl Hp]. rewrite Hl, hca5_F0b_bytes_HN. entailer!.
  - Intros. rewrite H, hca5_F0b_bytes_HN. entailer!.
Qed.

(* ---------------------------------------------------------------------- *)
(* the harness's constants                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma hca5_F0b_consts gv :
  hca5_consts gv =
  hbytes Ers basepoint9 (gv HC._x_create_any__M_BASEPOINT) *
  hc_const gv HC._x_create_any__M_CONSTRUCTION construction_bytes *
  hc_const gv HC._x_create_any__M_IDENTIFIER identifier_bytes.
Proof. reflexivity. Qed.
