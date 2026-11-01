(* law create_any: segment F1b, the top's separation-logic helpers (adapted from hca5_F0b_lib.v):
   the snapshot structs s / x opened at the fields the block uses (hca5_F1b_defs.v: hca5_F1b_ss / hca5_F1b_xs),
   the shim's random_log / random_u32. *)
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
Require Import WgNoise.proof.harness.create_any.hca3_model.
Require Import WgNoise.proof.harness.create_any.hca5_defs.
Require Import WgNoise.proof.harness.create_any.hca5_F1b_defs.
Require WgNoise.harness.x_create_any.code.
Local Open Scope logic.

#[local] Instance hca5_F1b_cceN : change_composite_env Noise.CS W_create_any.
Proof. make_cs_preserve Noise.CS W_create_any. Defined.
#[local] Instance hca5_F1b_cceH3 : change_composite_env HCS W_create_any.
Proof. make_cs_preserve HCS W_create_any. Defined.
#[local] Existing Instance HCS.

Lemma hca5_F1b_bytes_HN (sh: share) n (v: list val) p :
  @data_at HCS sh (tarray tuchar n) v p = @data_at Noise.CS sh (tarray tuchar n) v p.
Proof.
  rewrite (@data_at_change_composite HCS W_create_any _ sh (tarray tuchar n) v v),
    (@data_at_change_composite Noise.CS W_create_any _ sh (tarray tuchar n) v v); auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* the snapshot struct, every field                                        *)
(* ---------------------------------------------------------------------- *)

Definition hca5_F1b_all (sh: share) (sn: hsnap) (p: val) : mpred :=
  let E := sn_entry sn in let H := sn_hs sn in
  !! (@field_compatible HCS t_hsnap [] p) &&
  (@field_at HCS sh t_hsnap [StructField HC._peer] (e_peer E) p *
   @field_at HCS sh t_hsnap [StructField HC._next] (sn_next sn) p *
   @field_at HCS sh t_hsnap [StructField HC._hashed] (Val.of_bool (sn_hashed sn)) p * spacer sh 17 20 p *
   @field_at HCS sh t_hsnap [StructField HC._type] (Vint (e_type E)) p *
   @field_at HCS sh t_hsnap [StructField HC._index] (Vint (e_index E)) p *
   @field_at HCS sh t_hsnap [StructField HC._state] (Vint (hs_state H)) p *
   @field_at HCS sh t_hsnap [StructField HC._last_initiation_consumption] (Vlong (hs_lic H)) p *
   @field_at HCS sh t_hsnap [StructField HC._static_identity] (hs_sid H) p *
   @field_at HCS sh t_hsnap [StructField HC._ephemeral_private] (bytes (hs_eph H)) p *
   @field_at HCS sh t_hsnap [StructField HC._remote_static] (bytes (hs_rstatic H)) p *
   @field_at HCS sh t_hsnap [StructField HC._remote_ephemeral] (bytes (hs_reph H)) p *
   @field_at HCS sh t_hsnap [StructField HC._precomputed_static_static] (bytes (hs_ss H)) p *
   @field_at HCS sh t_hsnap [StructField HC._preshared_key] (bytes (hs_psk H)) p *
   @field_at HCS sh t_hsnap [StructField HC._hash] (bytes (hs_hash H)) p *
   @field_at HCS sh t_hsnap [StructField HC._chaining_key] (bytes (hs_ck H)) p *
   @field_at HCS sh t_hsnap [StructField HC._latest_timestamp] (bytes (hs_ts H)) p *
   @field_at HCS sh t_hsnap [StructField HC._remote_index] (Vint (hs_rindex H)) p).

Lemma hca5_F1b_all_eq0 sh sn p : @field_compatible HCS t_hsnap [] p ->
  @data_at HCS sh t_hsnap (hsnap_val sn) p = hca5_F1b_all sh sn p.
Proof.
  intros FC. destruct sn as [En nx hd H]; unfold hsnap_val, hca5_F1b_all; cbn [sn_hs sn_entry sn_next sn_hashed].
  unfold_data_at (data_at _ _ _ p).
  apply pred_ext; entailer!.
Qed.

Lemma hca5_F1b_all_eq sh sn p : @data_at HCS sh t_hsnap (hsnap_val sn) p = hca5_F1b_all sh sn p.
Proof.
  apply pred_ext.
  - assert_PROP (@field_compatible HCS t_hsnap [] p) as FC by entailer!.
    rewrite (hca5_F1b_all_eq0 sh sn p FC). auto.
  - assert_PROP (@field_compatible HCS t_hsnap [] p) as FC by (unfold hca5_F1b_all; entailer!).
    rewrite (hca5_F1b_all_eq0 sh sn p FC). auto.
Qed.

Lemma hca5_F1b_fb_eph sh (bs: list byte) p : @field_compatible HCS t_hsnap [] p -> Zlength bs = 32 ->
  @field_at HCS sh t_hsnap (DOT HC._ephemeral_private) (bytes bs) p = hbytes sh bs (offset_val 48 p).
Proof. intros. rewrite field_at_data_at, field_address_offset by auto with field_compatible. unfold hbytes; rewrite H0. reflexivity. Qed.
Lemma hca5_F1b_fb_rs sh (bs: list byte) p : @field_compatible HCS t_hsnap [] p -> Zlength bs = 32 ->
  @field_at HCS sh t_hsnap (DOT HC._remote_static) (bytes bs) p = hbytes sh bs (offset_val 80 p).
Proof. intros. rewrite field_at_data_at, field_address_offset by auto with field_compatible. unfold hbytes; rewrite H0. reflexivity. Qed.
Lemma hca5_F1b_fb_re sh (bs: list byte) p : @field_compatible HCS t_hsnap [] p -> Zlength bs = 32 ->
  @field_at HCS sh t_hsnap (DOT HC._remote_ephemeral) (bytes bs) p = hbytes sh bs (offset_val 112 p).
Proof. intros. rewrite field_at_data_at, field_address_offset by auto with field_compatible. unfold hbytes; rewrite H0. reflexivity. Qed.
Lemma hca5_F1b_fb_psk sh (bs: list byte) p : @field_compatible HCS t_hsnap [] p -> Zlength bs = 32 ->
  @field_at HCS sh t_hsnap (DOT HC._preshared_key) (bytes bs) p = hbytes sh bs (offset_val 176 p).
Proof. intros. rewrite field_at_data_at, field_address_offset by auto with field_compatible. unfold hbytes; rewrite H0. reflexivity. Qed.
Lemma hca5_F1b_fb_h sh (bs: list byte) p : @field_compatible HCS t_hsnap [] p -> Zlength bs = 32 ->
  @field_at HCS sh t_hsnap (DOT HC._hash) (bytes bs) p = hbytes sh bs (offset_val 208 p).
Proof. intros. rewrite field_at_data_at, field_address_offset by auto with field_compatible. unfold hbytes; rewrite H0. reflexivity. Qed.
Lemma hca5_F1b_fb_ck sh (bs: list byte) p : @field_compatible HCS t_hsnap [] p -> Zlength bs = 32 ->
  @field_at HCS sh t_hsnap (DOT HC._chaining_key) (bytes bs) p = hbytes sh bs (offset_val 240 p).
Proof. intros. rewrite field_at_data_at, field_address_offset by auto with field_compatible. unfold hbytes; rewrite H0. reflexivity. Qed.
Lemma hca5_F1b_f_state sh (v: val) p :
  @field_at HCS sh t_hsnap (DOT HC._state) v p = @field_at W_create_any sh t_hsnap (DOT HC._state) v p.
Proof.
  exact (f_equal (fun f => f p) (@field_at_change_composite HCS W_create_any hca5_F1b_cceH3 sh t_hsnap (DOT HC._state) v v
    (@JMeq_refl _ v) ltac:(vm_compute; reflexivity))).
Qed.
Lemma hca5_F1b_f_rindex sh (v: val) p :
  @field_at HCS sh t_hsnap (DOT HC._remote_index) v p = @field_at W_create_any sh t_hsnap (DOT HC._remote_index) v p.
Proof.
  exact (f_equal (fun f => f p) (@field_at_change_composite HCS W_create_any hca5_F1b_cceH3 sh t_hsnap (DOT HC._remote_index) v v
    (@JMeq_refl _ v) ltac:(vm_compute; reflexivity))).
Qed.

(* ---------------------------------------------------------------------- *)
(* x: eph @48, hash @208, ck @240, state (W) and the rest                  *)
(* ---------------------------------------------------------------------- *)

Definition hca5_F1b_xrest (sh: share) (sn: hsnap) (p: val) : mpred :=
  let E := sn_entry sn in let H := sn_hs sn in
  !! (@field_compatible HCS t_hsnap [] p) &&
  (@field_at HCS sh t_hsnap [StructField HC._peer] (e_peer E) p *
   @field_at HCS sh t_hsnap [StructField HC._next] (sn_next sn) p *
   @field_at HCS sh t_hsnap [StructField HC._hashed] (Val.of_bool (sn_hashed sn)) p * spacer sh 17 20 p *
   @field_at HCS sh t_hsnap [StructField HC._type] (Vint (e_type E)) p *
   @field_at HCS sh t_hsnap [StructField HC._index] (Vint (e_index E)) p *
   @field_at HCS sh t_hsnap [StructField HC._last_initiation_consumption] (Vlong (hs_lic H)) p *
   @field_at HCS sh t_hsnap [StructField HC._static_identity] (hs_sid H) p *
   @field_at HCS sh t_hsnap [StructField HC._remote_static] (bytes (hs_rstatic H)) p *
   @field_at HCS sh t_hsnap [StructField HC._remote_ephemeral] (bytes (hs_reph H)) p *
   @field_at HCS sh t_hsnap [StructField HC._precomputed_static_static] (bytes (hs_ss H)) p *
   @field_at HCS sh t_hsnap [StructField HC._preshared_key] (bytes (hs_psk H)) p *
   @field_at HCS sh t_hsnap [StructField HC._latest_timestamp] (bytes (hs_ts H)) p *
   @field_at HCS sh t_hsnap [StructField HC._remote_index] (Vint (hs_rindex H)) p).

Lemma hca5_F1b_xsplit0 sh sn p : @field_compatible HCS t_hsnap [] p ->
  Zlength (hs_eph (sn_hs sn)) = 32 -> Zlength (hs_hash (sn_hs sn)) = 32 -> Zlength (hs_ck (sn_hs sn)) = 32 ->
  @data_at HCS sh t_hsnap (hsnap_val sn) p =
  hbytes sh (hs_eph (sn_hs sn)) (offset_val 48 p) * hbytes sh (hs_hash (sn_hs sn)) (offset_val 208 p) *
  hbytes sh (hs_ck (sn_hs sn)) (offset_val 240 p) *
  @field_at W_create_any sh t_hsnap (DOT HC._state) (Vint (hs_state (sn_hs sn))) p *
  hca5_F1b_xrest sh sn p.
Proof.
  intros FC He Hh Hc. rewrite hca5_F1b_all_eq. unfold hca5_F1b_all, hca5_F1b_xrest.
  rewrite <- (hca5_F1b_fb_eph sh _ p FC He), <- (hca5_F1b_fb_h sh _ p FC Hh), <- (hca5_F1b_fb_ck sh _ p FC Hc),
    <- hca5_F1b_f_state.
  apply pred_ext; entailer!.
Qed.

Lemma hca5_F1b_xsplit sh sn p :
  Zlength (hs_eph (sn_hs sn)) = 32 -> Zlength (hs_hash (sn_hs sn)) = 32 -> Zlength (hs_ck (sn_hs sn)) = 32 ->
  @data_at HCS sh t_hsnap (hsnap_val sn) p =
  hbytes sh (hs_eph (sn_hs sn)) (offset_val 48 p) * hbytes sh (hs_hash (sn_hs sn)) (offset_val 208 p) *
  hbytes sh (hs_ck (sn_hs sn)) (offset_val 240 p) *
  @field_at W_create_any sh t_hsnap (DOT HC._state) (Vint (hs_state (sn_hs sn))) p *
  hca5_F1b_xrest sh sn p.
Proof.
  intros He Hh Hc. apply pred_ext.
  - assert_PROP (@field_compatible HCS t_hsnap [] p) as FC by entailer!.
    rewrite (hca5_F1b_xsplit0 sh sn p FC He Hh Hc). auto.
  - assert_PROP (@field_compatible HCS t_hsnap [] p) as FC by (unfold hca5_F1b_xrest; entailer!).
    rewrite (hca5_F1b_xsplit0 sh sn p FC He Hh Hc). auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* s: rstatic @80, reph @112, psk @176, hash @208, ck @240, remote_index (W) and the rest *)
(* ---------------------------------------------------------------------- *)

Definition hca5_F1b_srest (sh: share) (sn: hsnap) (p: val) : mpred :=
  let E := sn_entry sn in let H := sn_hs sn in
  !! (@field_compatible HCS t_hsnap [] p) &&
  (@field_at HCS sh t_hsnap [StructField HC._peer] (e_peer E) p *
   @field_at HCS sh t_hsnap [StructField HC._next] (sn_next sn) p *
   @field_at HCS sh t_hsnap [StructField HC._hashed] (Val.of_bool (sn_hashed sn)) p * spacer sh 17 20 p *
   @field_at HCS sh t_hsnap [StructField HC._type] (Vint (e_type E)) p *
   @field_at HCS sh t_hsnap [StructField HC._index] (Vint (e_index E)) p *
   @field_at HCS sh t_hsnap [StructField HC._state] (Vint (hs_state H)) p *
   @field_at HCS sh t_hsnap [StructField HC._last_initiation_consumption] (Vlong (hs_lic H)) p *
   @field_at HCS sh t_hsnap [StructField HC._static_identity] (hs_sid H) p *
   @field_at HCS sh t_hsnap [StructField HC._ephemeral_private] (bytes (hs_eph H)) p *
   @field_at HCS sh t_hsnap [StructField HC._precomputed_static_static] (bytes (hs_ss H)) p *
   @field_at HCS sh t_hsnap [StructField HC._latest_timestamp] (bytes (hs_ts H)) p).

Lemma hca5_F1b_ssplit0 sh sn p : @field_compatible HCS t_hsnap [] p -> hs_ok (sn_hs sn) ->
  @data_at HCS sh t_hsnap (hsnap_val sn) p =
  hbytes sh (hs_rstatic (sn_hs sn)) (offset_val 80 p) * hbytes sh (hs_reph (sn_hs sn)) (offset_val 112 p) *
  hbytes sh (hs_psk (sn_hs sn)) (offset_val 176 p) * hbytes sh (hs_hash (sn_hs sn)) (offset_val 208 p) *
  hbytes sh (hs_ck (sn_hs sn)) (offset_val 240 p) *
  @field_at W_create_any sh t_hsnap (DOT HC._remote_index) (Vint (hs_rindex (sn_hs sn))) p *
  hca5_F1b_srest sh sn p.
Proof.
  intros FC (_ & Hr & Hre & _ & Hp & Hh & Hc & _). rewrite hca5_F1b_all_eq. unfold hca5_F1b_all, hca5_F1b_srest.
  rewrite <- (hca5_F1b_fb_rs sh _ p FC Hr), <- (hca5_F1b_fb_re sh _ p FC Hre), <- (hca5_F1b_fb_psk sh _ p FC Hp),
    <- (hca5_F1b_fb_h sh _ p FC Hh), <- (hca5_F1b_fb_ck sh _ p FC Hc), <- hca5_F1b_f_rindex.
  apply pred_ext; entailer!.
Qed.

Lemma hca5_F1b_ssplit sh sn p : hs_ok (sn_hs sn) ->
  @data_at HCS sh t_hsnap (hsnap_val sn) p =
  hbytes sh (hs_rstatic (sn_hs sn)) (offset_val 80 p) * hbytes sh (hs_reph (sn_hs sn)) (offset_val 112 p) *
  hbytes sh (hs_psk (sn_hs sn)) (offset_val 176 p) * hbytes sh (hs_hash (sn_hs sn)) (offset_val 208 p) *
  hbytes sh (hs_ck (sn_hs sn)) (offset_val 240 p) *
  @field_at W_create_any sh t_hsnap (DOT HC._remote_index) (Vint (hs_rindex (sn_hs sn))) p *
  hca5_F1b_srest sh sn p.
Proof.
  intros Hok. apply pred_ext.
  - assert_PROP (@field_compatible HCS t_hsnap [] p) as FC by entailer!.
    rewrite (hca5_F1b_ssplit0 sh sn p FC Hok). auto.
  - assert_PROP (@field_compatible HCS t_hsnap [] p) as FC by (unfold hca5_F1b_srest; entailer!).
    rewrite (hca5_F1b_ssplit0 sh sn p FC Hok). auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* the shim's globals: random_log, random_u32                              *)
(* ---------------------------------------------------------------------- *)

Definition hca5_F1b_shrest (gv: globals) (S: shim) (w: list int64) : mpred :=
  (!! shim_ok S &&
  (@data_at Noise.CS Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
   @data_at Noise.CS Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
   @data_at Noise.CS Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
   @data_at Noise.CS Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   @data_at Noise.CS Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
   @data_at Noise.CS Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   @data_at Noise.CS Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow))) * refwarn4 gv w.

Lemma hca5_F1b_shim_split gv S w :
  shim_state4 gv S w =
  !! (Zlength (s_log S) = 32) &&
  (hbytes Ews (s_log S) (gv HC._wg_shim_random_log) *
   @data_at W_create_any Ews tuint (Vint (s_u32 S)) (gv HC._wg_shim_random_u32) *
   hca5_F1b_shrest gv S w).
Proof.
  unfold shim_state4, shim_core, hca5_F1b_shrest, hbytes.
  change (gv HC._wg_shim_random_log) with (gv _wg_shim_random_log).
  change (gv HC._wg_shim_random_u32) with (gv _wg_shim_random_u32).
  rewrite <- (@data_at_change_composite Noise.CS W_create_any _ Ews tuint (Vint (s_u32 S)) (Vint (s_u32 S)))
    by auto.
  apply pred_ext.
  - Intros. pose proof H as [Hl Hp]. rewrite Hl, hca5_F1b_bytes_HN. entailer!.
  - Intros. rewrite H, hca5_F1b_bytes_HN. entailer!.
Qed.
