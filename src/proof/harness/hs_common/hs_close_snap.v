(* copy_peer's copy of a peer (hs_specs.v, snap_rep) is again uninitialised memory of struct wg_peer: main of
   the hs_reject_ laws frees its local `struct wg_peer before` at its return.  snap_rep owns every byte of the
   struct, padding included. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Local Open Scope logic.

Section Snap.
#[local] Existing Instance Noise.CS.

(* padding at offsets a..b of a member that starts at offset o of its struct is padding at o+a..o+b of the struct *)
Lemma hs_close_spacer_shift sh a b o p : spacer sh (o + a) (o + b) p = spacer sh a b (offset_val o p).
Proof.
  unfold spacer. replace (o + b - (o + a)) with (b - a) by lia.
  destruct (Z.eq_dec (b - a) 0); auto. unfold at_offset. rewrite offset_offset_val. auto.
Qed.

(* the four members of the peer's keypairs and its padding are together the member keypairs *)
Lemma hs_close_snap_kps sh q (c pr nx: val) :
  field_compatible t_peer [] q ->
  field_at sh t_peer (DOT I._keypairs DOT I._current_keypair) c q *
  field_at sh t_peer (DOT I._keypairs DOT I._previous_keypair) pr q *
  field_at sh t_peer (DOT I._keypairs DOT I._next_keypair) nx q *
  field_at_ sh t_peer (DOT I._keypairs DOT I._keypair_update_lock) q *
  spacer sh (OFS_PEER_KEYPAIRS + 28) (OFS_PEER_KEYPAIRS + 32) q
  |-- field_at_ sh t_peer (DOT I._keypairs) q.
Proof.
  intros FC. unfold field_at_.
  repeat match goal with |- context [@field_at Noise.CS sh t_peer [StructField ?f; StructField I._keypairs] ?v q] =>
    let E := fresh in
    pose proof (@field_at_app Noise.CS sh t_peer [StructField f] (DOT I._keypairs) v v q (JMeq_refl v)) as E;
    change ([StructField f] ++ [StructField I._keypairs]) with [StructField f; StructField I._keypairs] in E;
    rewrite E; clear E end.
  rewrite hs_close_spacer_shift.
  rewrite (field_at_data_at sh t_peer (DOT I._keypairs)).
  assert (A: field_address t_peer (DOT I._keypairs) q = offset_val OFS_PEER_KEYPAIRS q)
    by (rewrite field_address_offset by auto with field_compatible; reflexivity).
  rewrite !A.
  change (nested_field_type t_peer (DOT I._keypairs)) with t_kps.
  unfold_data_at (data_at sh t_kps _ (offset_val OFS_PEER_KEYPAIRS q)).
  repeat match goal with |- _ |-- ?R => match R with context [@field_at Noise.CS sh ?t ?g ?v ?p] =>
    change (@field_at Noise.CS sh t g v p) with (@field_at_ Noise.CS sh t g p) end end.
  repeat match goal with |- context [@field_at Noise.CS sh ?t ?g ?v (offset_val OFS_PEER_KEYPAIRS q)] =>
    sep_apply (@field_at_field_at_ Noise.CS sh t g v (offset_val OFS_PEER_KEYPAIRS q)) end.
  cancel.
Qed.

(* the members of the peer's handshake (its entry included) and its padding are together the member handshake *)
Lemma hs_close_snap_hs sh q H E next hashed :
  field_compatible t_peer [] q ->
  field_at sh t_peer (DOT I._handshake DOT I._entry) (entry_val E next hashed) q *
  field_at sh t_peer (DOT I._handshake DOT I._state) (Vint (hs_state H)) q *
  field_at sh t_peer (DOT I._handshake DOT I._last_initiation_consumption) (Vlong (hs_lic H)) q *
  field_at sh t_peer (DOT I._handshake DOT I._static_identity) (hs_sid H) q *
  field_at sh t_peer (DOT I._handshake DOT I._ephemeral_private) (bytes (hs_eph H)) q *
  field_at sh t_peer (DOT I._handshake DOT I._remote_static) (bytes (hs_rstatic H)) q *
  field_at sh t_peer (DOT I._handshake DOT I._remote_ephemeral) (bytes (hs_reph H)) q *
  field_at sh t_peer (DOT I._handshake DOT I._precomputed_static_static) (bytes (hs_ss H)) q *
  field_at sh t_peer (DOT I._handshake DOT I._preshared_key) (bytes (hs_psk H)) q *
  field_at sh t_peer (DOT I._handshake DOT I._hash) (bytes (hs_hash H)) q *
  field_at sh t_peer (DOT I._handshake DOT I._chaining_key) (bytes (hs_ck H)) q *
  field_at sh t_peer (DOT I._handshake DOT I._latest_timestamp) (bytes (hs_ts H)) q *
  field_at sh t_peer (DOT I._handshake DOT I._remote_index) (Vint (hs_rindex H)) q *
  field_at_ sh t_peer (DOT I._handshake DOT I._lock) q *
  spacer sh (OFS_PEER_HANDSHAKE + 36) (OFS_PEER_HANDSHAKE + 40) q *
  spacer sh (OFS_PEER_HANDSHAKE + 300) (OFS_PEER_HANDSHAKE + 304) q
  |-- field_at_ sh t_peer (DOT I._handshake) q.
Proof.
  intros FC. unfold field_at_.
  repeat match goal with |- context [@field_at Noise.CS sh t_peer [StructField ?f; StructField I._handshake] ?v q] =>
    let E := fresh in
    pose proof (@field_at_app Noise.CS sh t_peer [StructField f] (DOT I._handshake) v v q (JMeq_refl v)) as E;
    change ([StructField f] ++ [StructField I._handshake]) with [StructField f; StructField I._handshake] in E;
    rewrite E; clear E end.
  rewrite !hs_close_spacer_shift.
  rewrite (field_at_data_at sh t_peer (DOT I._handshake)).
  assert (A: field_address t_peer (DOT I._handshake) q = offset_val OFS_PEER_HANDSHAKE q)
    by (rewrite field_address_offset by auto with field_compatible; reflexivity).
  rewrite !A.
  change (nested_field_type t_peer (DOT I._handshake)) with t_hs.
  unfold_data_at (data_at sh t_hs _ (offset_val OFS_PEER_HANDSHAKE q)).
  repeat match goal with |- _ |-- ?R => match R with context [@field_at Noise.CS sh ?t ?g ?v ?p] =>
    change (@field_at Noise.CS sh t g v p) with (@field_at_ Noise.CS sh t g p) end end.
  repeat match goal with |- context [@field_at Noise.CS sh ?t ?g ?v (offset_val OFS_PEER_HANDSHAKE q)] =>
    sep_apply (@field_at_field_at_ Noise.CS sh t g v (offset_val OFS_PEER_HANDSHAKE q)) end.
  cancel.
Qed.

Lemma hs_close_snap sh q P E next hashed : snap_rep sh q P E next hashed |-- data_at_ sh t_peer q.
Proof.
  unfold snap_rep. Intros. rename H into FC.
  sep_apply (hs_close_snap_kps sh q (p_cur P) (p_prev P) (p_next P) FC).
  sep_apply (hs_close_snap_hs sh q (p_hs P) E next hashed FC).
  sep_apply (field_at_field_at_ sh t_peer (DOT I._refcount)).
  unfold_data_at (data_at_ sh t_peer q).
  repeat match goal with |- _ |-- ?R => match R with context [@field_at Noise.CS sh t_peer ?g ?v q] =>
    change (@field_at Noise.CS sh t_peer g v q) with (@field_at_ Noise.CS sh t_peer g q) end end.
  cancel.
Qed.

End Snap.
