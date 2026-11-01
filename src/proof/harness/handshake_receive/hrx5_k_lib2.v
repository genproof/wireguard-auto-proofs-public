(* law handshake_receive: helpers of hrx5_body_k.v for k_initiation:
   the initiation message / struct m_initiation field by field at HRX, the shim's real clock globals. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_k_lib.
Local Open Scope logic.

#[local] Existing Instance HRX.

#[local] Instance hrx5_k2_cce_N : change_composite_env Noise.CS HRX.
Proof. make_cs_preserve Noise.CS HRX. Defined.
#[local] Instance hrx5_k2_cce_H : change_composite_env HCS HRX.
Proof. make_cs_preserve HCS HRX. Defined.

Lemma hrx5_k2_cinit_len x25519 aead_enc aead_dec SPUB RPUB SS ERAW TS E encs enct ep ck h :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> Zlength SPUB = 32 -> Zlength TS = 12 ->
  m_create_initiation_model x25519 aead_enc SPUB RPUB SS ERAW TS = Some (E, encs, enct, ep, ck, h) ->
  Zlength E = 32 /\ Zlength encs = 48 /\ Zlength enct = 28.
Proof.
  intros Hx Ha Hs Ht Hm. unfold m_create_initiation_model in Hm.
  repeat match type of Hm with context [if ?c then _ else _] => destruct c end; try discriminate.
  inversion Hm; subst. rewrite !(aead_enc_length _ _ Ha), Hs, Ht. auto.
Qed.

Lemma hrx5_k2_minit_cs0 sh p : @data_at_ HRX sh (Tstruct HRC._m_initiation noattr) p = @data_at_ HCS sh t_minit p.
Proof.
  rewrite !data_at__eq. symmetry. apply (@hrx5_k_cs_eq HCS HRX _); [apply JMeq_refl | prove_cs_preserve_type].
Qed.

Lemma hrx5_k2_minit_split sh E encs enct ep ck h p :
  Zlength E = 32 -> Zlength encs = 48 -> Zlength enct = 28 ->
  @data_at HCS sh t_minit (minit_val E encs enct ep ck h) p =
  (hbytes sh E (@field_address HRX t_minit [StructField HRC._ephemeral] p) *
   hbytes sh encs (@field_address HRX t_minit [StructField HRC._enc_static] p) *
   hbytes sh enct (@field_address HRX t_minit [StructField HRC._enc_timestamp] p) *
   @field_at HRX sh t_minit [StructField HRC._eph_priv] (bytes ep) p *
   @field_at HRX sh t_minit [StructField HRC._st] (bytes ck, bytes h) p)%logic.
Proof.
  intros H1 H2 H3.
  rewrite (@hrx5_k_cs_eq HCS HRX _ sh t_minit (minit_val E encs enct ep ck h) (minit_val E encs enct ep ck h) p)
    by (apply JMeq_refl || prove_cs_preserve_type).
  rewrite !hrx5_k_hb, H1, H2, H3. unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_minit [StructField HRC._ephemeral]).
  rewrite (field_at_data_at sh t_minit [StructField HRC._enc_static]).
  rewrite (field_at_data_at sh t_minit [StructField HRC._enc_timestamp]). apply pred_ext; cancel.
Qed.

Lemma hrx5_k2_init_split sh ty se eph encs enct mac1 mac2 m :
  Zlength eph = 32 -> Zlength encs = 48 -> Zlength enct = 28 ->
  @data_at Noise.CS sh t_init (init_val (mkIM ty se eph encs enct mac1 mac2)) m =
  (@field_at HRX sh t_init [StructField HRC._header] (Vint ty) m *
   @field_at HRX sh t_init [StructField HRC._sender_index] (Vint se) m *
   hbytes sh eph (@field_address HRX t_init [StructField HRC._unencrypted_ephemeral] m) *
   hbytes sh encs (@field_address HRX t_init [StructField HRC._encrypted_static] m) *
   hbytes sh enct (@field_address HRX t_init [StructField HRC._encrypted_timestamp] m) *
   @field_at HRX sh t_init [StructField HRC._macs] (bytes mac1, bytes mac2) m)%logic.
Proof.
  intros H1 H2 H3.
  rewrite (@hrx5_k_cs_eq Noise.CS HRX _ sh t_init (init_val _) (init_val (mkIM ty se eph encs enct mac1 mac2)) m)
    by (apply JMeq_refl || prove_cs_preserve_type).
  rewrite !hrx5_k_hb, H1, H2, H3. unfold_data_at (data_at _ _ _ m).
  rewrite (field_at_data_at sh t_init [StructField HRC._unencrypted_ephemeral]).
  rewrite (field_at_data_at sh t_init [StructField HRC._encrypted_static]).
  rewrite (field_at_data_at sh t_init [StructField HRC._encrypted_timestamp]). apply pred_ext; cancel.
Qed.

(* the shim's state with the real-time clock's two globals at HRX *)
Definition hrx5_k2_shim_rest (gv: globals) (S: shim) (w: list int64) : mpred :=
  (!! shim_ok S &&
   (@data_at Noise.CS Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
    @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
    @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
    @data_at Noise.CS Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
    @data_at Noise.CS Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
    @data_at Noise.CS Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
    @data_at Noise.CS Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
    @data_at Noise.CS Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
    @data_at Noise.CS Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
    @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow))) *
  refwarn4 gv w.

Lemma hrx5_k2_shim_open gv S w :
  shim_state4 gv S w =
  (@data_at HRX Ews tlong (Vlong (s_rsec S)) (gv HRC._wg_shim_real_sec) *
   @data_at HRX Ews tlong (Vlong (s_rnsec S)) (gv HRC._wg_shim_real_nsec) *
   hrx5_k2_shim_rest gv S w)%logic.
Proof.
  unfold shim_state4, shim_core, hrx5_k2_shim_rest.
  rewrite <- (@hrx5_k_cs_eq Noise.CS HRX _ Ews tlong (Vlong (s_rsec S)) (Vlong (s_rsec S)))
    by (apply JMeq_refl || reflexivity).
  rewrite <- (@hrx5_k_cs_eq Noise.CS HRX _ Ews tlong (Vlong (s_rnsec S)) (Vlong (s_rnsec S)))
    by (apply JMeq_refl || reflexivity).
  change (gv HRC._wg_shim_real_sec) with (gv _wg_shim_real_sec).
  change (gv HRC._wg_shim_real_nsec) with (gv _wg_shim_real_nsec).
  apply pred_ext; Intros; entailer!.
Qed.
