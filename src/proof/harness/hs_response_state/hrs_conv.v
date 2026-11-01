(* The law hs_response_state: main's view of its locals.  main runs in the world's compspecs W_hrs, the
   specifications of the functions it calls are stated in noise.c's (Noise.CS) and the helpers' (CSh).
   Here: main's stack variables in the specifications' compspecs (hrs_conv_pair, hrs_conv_init,
   hrs_conv_resp), and A's peer split into the state field of its handshake, which main writes and reads as
   p.a_peer.handshake.state, and the rest (hrs_peer_split, hrs_peer_join). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_cs.
Require Import WgNoise.proof.protocol5.prot_repr5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require WgNoise.harness.hs_response_state.code.
Local Open Scope logic.

Module HRS := WgNoise.harness.hs_response_state.code.
Notation W_hrs := W_hs_response_state.

#[export] Instance hrs_cce_N : change_composite_env Noise.CS W_hrs.
Proof. make_cs_preserve Noise.CS W_hrs. Defined.
#[export] Instance hrs_cce_H : change_composite_env CSh W_hrs.
Proof. make_cs_preserve CSh W_hrs. Defined.

(* main's stack frame, from the world's compspecs to those of the specifications *)
Lemma hrs_conv_pair sh p : @data_at_ W_hrs sh (Tstruct HRS._pair noattr) p = @data_at_ CSh sh t_pair p.
Proof. rewrite (@data_at__change_composite CSh W_hrs _ sh t_pair); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hrs_conv_init sh p :
  @data_at_ W_hrs sh (Tstruct HRS._message_handshake_initiation noattr) p = @data_at_ Noise.CS sh t_init p.
Proof. rewrite (@data_at__change_composite Noise.CS W_hrs _ sh t_init); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hrs_conv_resp sh p :
  @data_at_ W_hrs sh (Tstruct HRS._message_handshake_response noattr) p = @data_at_ Noise.CS sh t_resp p.
Proof. rewrite (@data_at__change_composite Noise.CS W_hrs _ sh t_resp); [reflexivity | prove_cs_preserve_type]. Qed.

(* the state field of A's handshake, as main addresses it: p.a_peer.handshake.state *)
Definition hrs_state_at (sh: share) (v: val) (p: val) : mpred :=
  @field_at W_hrs sh (Tstruct HRS._pair noattr)
    [StructField HRS._state; StructField HRS._handshake; StructField HRS._a_peer] v p.

Lemma hrs_state_conv sh v p :
  @field_compatible CSh t_pair [] p ->
  @field_at Noise.CS sh t_hs [StructField I._state] v (hs_addr (pair_ap p)) = hrs_state_at sh v p.
Proof.
  intros Hfc.
  assert (Hfw: @field_compatible W_hrs (Tstruct HRS._pair noattr) [] p).
  { apply (@field_compatible_change_composite CSh W_hrs _ t_pair); [prove_cs_preserve_type | exact Hfc]. }
  rewrite (@field_at_cs_eq Noise.CS W_hrs _ sh t_hs [StructField I._state] v v) by
    first [apply JMeq_refl | reflexivity].
  unfold hrs_state_at.
  change [StructField HRS._state; StructField HRS._handshake; StructField HRS._a_peer]
    with ([StructField HRS._state] ++ [StructField HRS._handshake; StructField HRS._a_peer]).
  rewrite (@field_at_app W_hrs sh (Tstruct HRS._pair noattr) [StructField HRS._state]
             [StructField HRS._handshake; StructField HRS._a_peer] v v p (JMeq_refl v)).
  f_equal.
  unfold hs_addr, pair_ap.
  rewrite (@field_address_offset W_hrs) by auto with field_compatible.
  rewrite (@field_address_offset CSh) by auto with field_compatible.
  rewrite offset_offset_val. reflexivity.
Qed.

Section Peer.
#[local] Existing Instance Noise.CS.

(* a peer without the state field of its handshake *)
Definition hrs_peer_rest (sh: share) (p: val) (P: peer) : mpred :=
  let H := p_hs P in let h := hs_addr p in
  !! (field_compatible t_peer [] p /\ hs_ok H) &&
  (field_at sh t_peer [StructField I._device] (p_device P) p *
   field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   field_at sh t_hs [StructField I._last_initiation_consumption] (Vlong (hs_lic H)) h *
   field_at sh t_hs [StructField I._static_identity] (hs_sid H) h *
   field_at sh t_hs [StructField I._ephemeral_private] (bytes (hs_eph H)) h *
   field_at sh t_hs [StructField I._remote_static] (bytes (hs_rstatic H)) h *
   field_at sh t_hs [StructField I._remote_ephemeral] (bytes (hs_reph H)) h *
   field_at sh t_hs [StructField I._precomputed_static_static] (bytes (hs_ss H)) h *
   field_at sh t_hs [StructField I._preshared_key] (bytes (hs_psk H)) h *
   field_at sh t_hs [StructField I._hash] (bytes (hs_hash H)) h *
   field_at sh t_hs [StructField I._chaining_key] (bytes (hs_ck H)) h *
   field_at sh t_hs [StructField I._latest_timestamp] (bytes (hs_ts H)) h *
   field_at sh t_hs [StructField I._remote_index] (Vint (hs_rindex H)) h *
   (EX lk: val, field_at sh t_hs [StructField I._lock] lk h) *
   spacer sh 36 40 h * spacer sh 300 304 h *
   field_at_ sh t_peer [StructField I._last_sent_handshake] p *
   field_at_ sh t_peer [StructField I._latest_cookie] p *
   field_at sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   field_at_ sh t_peer [StructField I._internal_id] p *
   field_at sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Lemma hrs_peer_split0 sh p P :
  peer_rep5 sh p P =
  field_at sh t_hs [StructField I._state] (Vint (hs_state (p_hs P))) (hs_addr p) * hrs_peer_rest sh p P.
Proof.
  unfold peer_rep5, hrs_peer_rest, hs_rep. apply pred_ext; Intros; entailer!.
Qed.

(* the rest does not depend on the state *)
Lemma hrs_peer_rest_state sh p P s :
  hrs_peer_rest sh p (p_set_hs P (hs_set_state (p_hs P) s)) = hrs_peer_rest sh p P.
Proof. reflexivity. Qed.

End Peer.

(* A's peer, its state field as main addresses it *)
Lemma hrs_peer_split sh p P :
  @field_compatible CSh t_pair [] p ->
  peer_rep5 sh (pair_ap p) P = hrs_state_at sh (Vint (hs_state (p_hs P))) p * hrs_peer_rest sh (pair_ap p) P.
Proof. intros Hfc. rewrite hrs_peer_split0, hrs_state_conv by exact Hfc. reflexivity. Qed.

(* A's peer after main's store of the state s *)
Lemma hrs_peer_join sh p P s :
  @field_compatible CSh t_pair [] p ->
  hrs_state_at sh (Vint s) p * hrs_peer_rest sh (pair_ap p) P
  |-- peer_rep5 sh (pair_ap p) (p_set_hs P (hs_set_state (p_hs P) s)).
Proof.
  intros Hfc. rewrite hrs_peer_split by exact Hfc. rewrite hrs_peer_rest_state. apply derives_refl.
Qed.
