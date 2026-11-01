(* The law hs_begin_session_state: A's peer seen by main.  main runs in the world compspecs W_hbs and writes
   seven fields of A's handshake (state, remote index, ephemeral keys, hash, chaining key, timestamp), reads
   the state, the three keypair slots and the shim's allocation count.  peer_rep5 (Noise.CS) is split here
   into those fields at W_hbs and the rest, which does not depend on them (hbs_peer_split); hbs_hs_set is
   the handshake after the writes. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol5.prot_repr5.
Require Import WgNoise.proof.protocol.prot_cs.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Local Open Scope logic.

Notation W_hbs := W_hs_begin_session_state.

#[local] Instance hbs_cce_N : change_composite_env Noise.CS W_hbs.
Proof. make_cs_preserve Noise.CS W_hbs. Defined.

(* the handshake H with the seven fields the harness writes set *)
Definition hbs_hs_set (H: handshake) (st ri: int) (eph reph hh ck ts: list byte) : handshake :=
  mkHS st (hs_lic H) (hs_sid H) eph (hs_rstatic H) reph (hs_ss H) (hs_psk H) hh ck ts ri.

(* the seven fields at W_hbs *)
Definition hbs_hsW (sh: share) (h: val) (H: handshake) : mpred :=
  @field_at W_hbs sh t_hs [StructField I._state] (Vint (hs_state H)) h *
  @field_at W_hbs sh t_hs [StructField I._ephemeral_private] (bytes (hs_eph H)) h *
  @field_at W_hbs sh t_hs [StructField I._remote_ephemeral] (bytes (hs_reph H)) h *
  @field_at W_hbs sh t_hs [StructField I._hash] (bytes (hs_hash H)) h *
  @field_at W_hbs sh t_hs [StructField I._chaining_key] (bytes (hs_ck H)) h *
  @field_at W_hbs sh t_hs [StructField I._latest_timestamp] (bytes (hs_ts H)) h *
  @field_at W_hbs sh t_hs [StructField I._remote_index] (Vint (hs_rindex H)) h.

(* the other fields of the handshake *)
Definition hbs_hs_rest (sh: share) (h: val) (H: handshake) : mpred :=
  @field_at Noise.CS sh t_hs [StructField I._last_initiation_consumption] (Vlong (hs_lic H)) h *
  @field_at Noise.CS sh t_hs [StructField I._static_identity] (hs_sid H) h *
  @field_at Noise.CS sh t_hs [StructField I._remote_static] (bytes (hs_rstatic H)) h *
  @field_at Noise.CS sh t_hs [StructField I._precomputed_static_static] (bytes (hs_ss H)) h *
  @field_at Noise.CS sh t_hs [StructField I._preshared_key] (bytes (hs_psk H)) h *
  (EX lk: val, @field_at Noise.CS sh t_hs [StructField I._lock] lk h) *
  spacer sh 36 40 h * spacer sh 300 304 h.

(* the keypair slots at W_hbs *)
Definition hbs_kpsW (sh: share) (a: val) (cur prev next: val) : mpred :=
  EX lk: val, @data_at W_hbs sh t_kps (cur, (prev, (next, lk))) a.

(* the rest of the peer *)
Definition hbs_peer_rest (sh: share) (p: val) (P: peer) : mpred :=
  @field_at Noise.CS sh t_peer [StructField I._device] (p_device P) p *
  @field_at Noise.CS sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
  @field_at_ Noise.CS sh t_peer [StructField I._last_sent_handshake] p *
  @field_at_ Noise.CS sh t_peer [StructField I._latest_cookie] p *
  @field_at Noise.CS sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
  @field_at_ Noise.CS sh t_peer [StructField I._internal_id] p *
  @field_at Noise.CS sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
  spacer sh 9 16 p * spacer sh 476 480 p.

Lemma hbs_kps_conv sh a c p n : kps_rep sh a c p n = hbs_kpsW sh a c p n.
Proof.
  unfold kps_rep, hbs_kpsW. f_equal. extensionality lk.
  apply data_at_cs_eq; [apply JMeq_refl | reflexivity].
Qed.

Lemma hbs_hs_split sh h H : hs_rep sh h H = !! hs_ok H && (hbs_hsW sh h H * hbs_hs_rest sh h H).
Proof.
  unfold hs_rep, hbs_hsW, hbs_hs_rest.
  assert (E1: forall v, @field_at Noise.CS sh t_hs [StructField I._state] v h =
                        @field_at W_hbs sh t_hs [StructField I._state] v h)
    by (intros; apply field_at_cs_eq; [apply JMeq_refl | reflexivity]).
  assert (E2: forall v, @field_at Noise.CS sh t_hs [StructField I._remote_index] v h =
                        @field_at W_hbs sh t_hs [StructField I._remote_index] v h)
    by (intros; apply field_at_cs_eq; [apply JMeq_refl | reflexivity]).
  assert (E3: forall v, @field_at Noise.CS sh t_hs [StructField I._ephemeral_private] v h =
                        @field_at W_hbs sh t_hs [StructField I._ephemeral_private] v h)
    by (intros; apply field_at_cs_eq; [apply JMeq_refl | reflexivity]).
  assert (E4: forall v, @field_at Noise.CS sh t_hs [StructField I._remote_ephemeral] v h =
                        @field_at W_hbs sh t_hs [StructField I._remote_ephemeral] v h)
    by (intros; apply field_at_cs_eq; [apply JMeq_refl | reflexivity]).
  assert (E5: forall v, @field_at Noise.CS sh t_hs [StructField I._hash] v h =
                        @field_at W_hbs sh t_hs [StructField I._hash] v h)
    by (intros; apply field_at_cs_eq; [apply JMeq_refl | reflexivity]).
  assert (E6: forall v, @field_at Noise.CS sh t_hs [StructField I._chaining_key] v h =
                        @field_at W_hbs sh t_hs [StructField I._chaining_key] v h)
    by (intros; apply field_at_cs_eq; [apply JMeq_refl | reflexivity]).
  assert (E7: forall v, @field_at Noise.CS sh t_hs [StructField I._latest_timestamp] v h =
                        @field_at W_hbs sh t_hs [StructField I._latest_timestamp] v h)
    by (intros; apply field_at_cs_eq; [apply JMeq_refl | reflexivity]).
  rewrite E1, E2, E3, E4, E5, E6, E7. f_equal. apply pred_ext; cancel.
Qed.

Lemma hbs_peer_split sh p P :
  peer_rep5 sh p P =
  !! (@field_compatible Noise.CS t_peer [] p /\ hs_ok (p_hs P)) &&
  (hbs_kpsW sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) * hbs_hsW sh (hs_addr p) (p_hs P) *
   hbs_hs_rest sh (hs_addr p) (p_hs P) * hbs_peer_rest sh p P).
Proof.
  unfold peer_rep5, hbs_peer_rest. rewrite hbs_kps_conv, hbs_hs_split.
  apply pred_ext; Intros; entailer!.
Qed.

(* the shim's allocation count, read by main *)
Lemma hbs_tulong_conv sh v p : @data_at Noise.CS sh tulong v p = @data_at W_hbs sh tulong v p.
Proof. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

(* the shim's state without its allocation count *)
Definition hbs_shim_rest (gv: globals) (S: shim) (w: list int64) : mpred :=
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
   @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow) *
   refwarn4 gv w).

Lemma hbs_shim_split gv S w :
  shim_state4 gv S w =
  @data_at W_hbs Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) * hbs_shim_rest gv S w.
Proof.
  unfold shim_state4, shim_core, hbs_shim_rest. rewrite <- hbs_tulong_conv.
  apply pred_ext; Intros; entailer!.
Qed.

Lemma hbs_shim_join gv S w :
  @data_at W_hbs Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) * hbs_shim_rest gv S w |-- shim_state4 gv S w.
Proof. rewrite hbs_shim_split. apply derives_refl. Qed.

(* the bytes nondet_bytes writes *)
Lemma hbs_bytes_of (bs: list Z) :
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  map (fun b => Vint (Int.repr b)) bs = bytes (map Byte.repr bs).
Proof.
  intros H. unfold bytes. induction H as [| b bs Hb _ IH]; simpl; [reflexivity |].
  rewrite IH. f_equal. unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

(* A's peer after the harness's writes: state st, remote index ri, the drawn bytes *)
Lemma hbs_fold sh p P lk st ri (eph reph hh ck ts: list Z) :
  hs_ok (p_hs P) -> @field_compatible Noise.CS t_peer [] p ->
  Zlength eph = 32 -> Zlength reph = 32 -> Zlength hh = 32 -> Zlength ck = 32 -> Zlength ts = 12 ->
  Forall (fun b => 0 <= b <= Byte.max_unsigned) eph -> Forall (fun b => 0 <= b <= Byte.max_unsigned) reph ->
  Forall (fun b => 0 <= b <= Byte.max_unsigned) hh -> Forall (fun b => 0 <= b <= Byte.max_unsigned) ck ->
  Forall (fun b => 0 <= b <= Byte.max_unsigned) ts ->
  @data_at W_hbs sh t_kps (p_cur P, (p_prev P, (p_next P, lk))) (kps_addr p) *
  @field_at W_hbs sh t_hs [StructField I._state] (Vint st) (hs_addr p) *
  @data_at W_hbs sh (tarray tuchar 32) (map (fun b => Vint (Int.repr b)) eph)
    (@field_address W_hbs t_hs [StructField I._ephemeral_private] (hs_addr p)) *
  @data_at W_hbs sh (tarray tuchar 32) (map (fun b => Vint (Int.repr b)) reph)
    (@field_address W_hbs t_hs [StructField I._remote_ephemeral] (hs_addr p)) *
  @data_at W_hbs sh (tarray tuchar 32) (map (fun b => Vint (Int.repr b)) hh)
    (@field_address W_hbs t_hs [StructField I._hash] (hs_addr p)) *
  @data_at W_hbs sh (tarray tuchar 32) (map (fun b => Vint (Int.repr b)) ck)
    (@field_address W_hbs t_hs [StructField I._chaining_key] (hs_addr p)) *
  @data_at W_hbs sh (tarray tuchar 12) (map (fun b => Vint (Int.repr b)) ts)
    (@field_address W_hbs t_hs [StructField I._latest_timestamp] (hs_addr p)) *
  @field_at W_hbs sh t_hs [StructField I._remote_index] (Vint ri) (hs_addr p) *
  hbs_hs_rest sh (hs_addr p) (p_hs P) * hbs_peer_rest sh p P
  |-- peer_rep5 sh p (p_set_hs P (hbs_hs_set (p_hs P) st ri (map Byte.repr eph) (map Byte.repr reph)
                                   (map Byte.repr hh) (map Byte.repr ck) (map Byte.repr ts))).
Proof.
  intros HH Hfc L1 L2 L3 L4 L5 B1 B2 B3 B4 B5.
  rewrite hbs_peer_split. unfold hbs_kpsW, hbs_hsW. cbn [p_hs p_set_hs p_cur p_prev p_next hbs_hs_set
    hs_state hs_eph hs_reph hs_hash hs_ck hs_ts hs_rindex].
  rewrite <- (hbs_bytes_of eph), <- (hbs_bytes_of reph), <- (hbs_bytes_of hh), <- (hbs_bytes_of ck),
    <- (hbs_bytes_of ts) by assumption.
  rewrite !(@field_at_data_at W_hbs sh t_hs).
  Exists lk.
  destruct HH as (h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8).
  entailer!.
  - unfold hs_ok; simpl. rewrite !Zlength_map. tauto.
  - apply derives_refl.
Qed.
