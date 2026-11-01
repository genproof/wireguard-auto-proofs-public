(* The law hs_reject_response: main's message (struct message_handshake_response, a local variable of main).
   main writes it field by field (the three indices by stores, the byte arrays by nondet_bytes): hrr_resp_split
   gives an uninitialised message as its fields, the byte arrays as plain buffers at their offsets (header 0,
   sender 4, receiver 8, ephemeral 12, encrypted_nothing 44, mac1 60, mac2 76); hrr_resp_fold gives the written
   message as resp_rep5 (prot_repr5.v), the form noise.c's specifications take. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol5.prot_repr5.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require Import WgNoise.proof.harness.hs_reject_response.hrr_conv.
Local Open Scope logic.

#[local] Existing Instance W_hs_reject_response.

Lemma hrr_resp_split sh m :
  data_at_ sh t_resp m |--
  !! field_compatible t_resp [] m &&
  (field_at_ sh t_resp (DOT I._header) m * field_at_ sh t_resp (DOT I._sender_index) m *
   field_at_ sh t_resp (DOT I._receiver_index) m *
   data_at_ sh (tarray tuchar 32) (offset_val 12 m) * data_at_ sh (tarray tuchar 16) (offset_val 44 m) *
   data_at_ sh (tarray tuchar 16) (offset_val 60 m) * data_at_ sh (tarray tuchar 16) (offset_val 76 m)).
Proof.
  assert_PROP (field_compatible t_resp [] m) as Hf by entailer!.
  rewrite data_at__eq. unfold_data_at (data_at sh t_resp _ m).
  rewrite (field_at_data_at sh t_resp (DOT I._unencrypted_ephemeral)).
  rewrite (field_at_data_at sh t_resp (DOT I._encrypted_nothing)).
  rewrite (field_at_data_at sh t_resp (DOT I._macs)).
  rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type; simpl nested_field_offset.
  match goal with |- context [data_at sh (Tstruct ?i ?a) ?v (offset_val 60 m)] =>
    unfold_data_at (data_at sh (Tstruct i a) v (offset_val 60 m)) end.
  assert (Hf60: field_compatible (Tstruct I._message_macs noattr) [] (offset_val 60 m)).
  { exact (field_compatible_nested_field t_resp (DOT I._macs) m ltac:(auto with field_compatible)). }
  rewrite (field_at_data_at sh (Tstruct I._message_macs noattr) (DOT I._mac1)).
  rewrite (field_at_data_at sh (Tstruct I._message_macs noattr) (DOT I._mac2)).
  rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type; simpl nested_field_offset.
  rewrite !offset_offset_val. simpl Z.add.
  entailer!.
Qed.

Lemma hrr_resp_fold sh m t s r e n v1 v2 :
  field_compatible t_resp [] m -> Zlength e = 32 -> Zlength n = 16 ->
  field_at sh t_resp (DOT I._header) (Vint t) m * field_at sh t_resp (DOT I._sender_index) (Vint s) m *
  field_at sh t_resp (DOT I._receiver_index) (Vint r) m *
  data_at sh (tarray tuchar 32) (bytes e) (offset_val 12 m) *
  data_at sh (tarray tuchar 16) (bytes n) (offset_val 44 m) *
  data_at sh (tarray tuchar 16) v1 (offset_val 60 m) * data_at sh (tarray tuchar 16) v2 (offset_val 76 m)
  |-- resp_rep5 sh m (mkRM t s r e n (zeros 16) (zeros 16)).
Proof.
  intros Hf He Hn. unfold resp_rep5, rm_ok5. cbn [rm_type rm_sender rm_receiver rm_eph rm_encn].
  rewrite (@field_at_change_composite Noise.CS W_hs_reject_response _ sh t_resp (DOT I._header)
             (Vint t) (Vint t) (JMeq_refl _)) by reflexivity.
  rewrite (@field_at_change_composite Noise.CS W_hs_reject_response _ sh t_resp (DOT I._sender_index)
             (Vint s) (Vint s) (JMeq_refl _)) by reflexivity.
  rewrite (@field_at_change_composite Noise.CS W_hs_reject_response _ sh t_resp (DOT I._receiver_index)
             (Vint r) (Vint r) (JMeq_refl _)) by reflexivity.
  rewrite (@field_at_change_composite Noise.CS W_hs_reject_response _ sh t_resp (DOT I._unencrypted_ephemeral)
             (bytes e) (bytes e) (JMeq_refl _)) by reflexivity.
  rewrite (@field_at_change_composite Noise.CS W_hs_reject_response _ sh t_resp (DOT I._encrypted_nothing)
             (bytes n) (bytes n) (JMeq_refl _)) by reflexivity.
  rewrite (@field_at__change_composite Noise.CS W_hs_reject_response _ sh t_resp) by reflexivity.
  rewrite (field_at_data_at sh t_resp (DOT I._unencrypted_ephemeral)).
  rewrite (field_at_data_at sh t_resp (DOT I._encrypted_nothing)).
  rewrite (field_at__data_at_ sh t_resp (DOT I._macs)).
  rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type; simpl nested_field_offset.
  assert (Hf60: field_compatible (Tstruct I._message_macs noattr) [] (offset_val 60 m)).
  { exact (field_compatible_nested_field t_resp (DOT I._macs) m ltac:(auto with field_compatible)). }
  rewrite data_at__eq.
  match goal with |- context [data_at sh (Tstruct ?i ?a) ?v (offset_val 60 m)] =>
    unfold_data_at (data_at sh (Tstruct i a) v (offset_val 60 m)) end.
  rewrite (field_at_data_at sh (Tstruct I._message_macs noattr) (DOT I._mac1)).
  rewrite (field_at_data_at sh (Tstruct I._message_macs noattr) (DOT I._mac2)).
  rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type; simpl nested_field_offset.
  rewrite !offset_offset_val. simpl Z.add.
  entailer!.
Qed.

(* the bytes nondet_bytes returns *)
Lemma hrr_nd_bytes (bs: list Z) :
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  map (fun b => Vint (Int.repr b)) bs = bytes (map Byte.repr bs).
Proof.
  intros HF. unfold bytes. rewrite map_map. apply map_ext_Forall. eapply Forall_impl; [| exact HF].
  intros b Hb. simpl. unfold Vubyte. rewrite Byte.unsigned_repr by (unfold Byte.max_unsigned in *; lia).
  reflexivity.
Qed.

