(* The law hs_reject_response: main's local variables at its world W_hs_reject_response and at the compspecs
   of the specifications (CSh for struct pair, Noise.CS for the kernel structs); the structs are the same in
   both (same composite definitions), so the representations are equal. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol5.prot_repr5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require Import WgNoise.proof.harness.hs_common.hs_itable1.
Require Import WgNoise.proof.harness.hs_common.hs_close.
Local Open Scope logic.

#[export] Instance hrr_cce_N : change_composite_env Noise.CS W_hs_reject_response.
Proof. make_cs_preserve Noise.CS W_hs_reject_response. Defined.
#[export] Instance hrr_cce_H : change_composite_env CSh W_hs_reject_response.
Proof. make_cs_preserve CSh W_hs_reject_response. Defined.

Lemma hrr_conv_pair sh p : @data_at_ CSh sh t_pair p = @data_at_ W_hs_reject_response sh t_pair p.
Proof. rewrite (@data_at__change_composite CSh W_hs_reject_response _ sh t_pair); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hrr_conv_peer sh p : @data_at_ Noise.CS sh t_peer p = @data_at_ W_hs_reject_response sh t_peer p.
Proof. rewrite (@data_at__change_composite Noise.CS W_hs_reject_response _ sh t_peer); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hrr_conv_init sh p : @data_at_ Noise.CS sh t_init p = @data_at_ W_hs_reject_response sh t_init p.
Proof. rewrite (@data_at__change_composite Noise.CS W_hs_reject_response _ sh t_init); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hrr_conv_resp sh p : @data_at_ Noise.CS sh t_resp p = @data_at_ W_hs_reject_response sh t_resp p.
Proof. rewrite (@data_at__change_composite Noise.CS W_hs_reject_response _ sh t_resp); [reflexivity | prove_cs_preserve_type]. Qed.

(* the members of struct pair (hs_specs.v's pair_a .. pair_bp) at their offsets *)
Lemma hrr_pair_addrs p : @field_compatible CSh t_pair [] p ->
  pair_a p = p /\ pair_b p = offset_val 216 p /\ pair_ai p = offset_val 432 p /\ pair_bi p = offset_val 440 p /\
  pair_ak p = offset_val 448 p /\ pair_bk p = offset_val 456 p /\ pair_ap p = offset_val 464 p /\
  pair_bp p = offset_val 960 p.
Proof.
  intros Hf. assert (Hp: isptr p) by (destruct Hf; assumption).
  unfold pair_a, pair_b, pair_ai, pair_bi, pair_ak, pair_bk, pair_ap, pair_bp, field_address.
  rewrite !if_true by (apply field_compatible_cons; split; [assumption | left; reflexivity] || auto with field_compatible).
  simpl. rewrite isptr_offset_val_zero by assumption. repeat split; reflexivity.
Qed.

(* a peer's address is a valid pointer (main compares the result of consume_initiation with NULL) *)
Lemma hrr_peer_valid p P : peer_rep5 Tsh p P |-- valid_pointer p.
Proof.
  unfold peer_rep5. Intros.
  rewrite (@field_at_data_at Noise.CS Tsh t_peer (DOT I._device)).
  rewrite field_address_offset by auto with field_compatible. simpl.
  rewrite isptr_offset_val_zero by auto with field_compatible.
  repeat apply sepcon_valid_pointer1.
  apply data_at_valid_ptr; [auto | simpl; lia].
Qed.
#[export] Hint Resolve hrr_peer_valid : valid_pointer.

(* the state field of A's handshake (in hs_rep, at noise.c's compspecs) is main's p.a_peer.handshake.state *)
Lemma hrr_state_conv sh p v : @field_compatible CSh t_pair [] p ->
  @field_at Noise.CS sh t_hs (DOT I._state) v (hs_addr (pair_ap p)) =
  @field_at W_hs_reject_response sh t_pair [StructField I._state; StructField I._handshake; StructField H._a_peer] v p.
Proof.
  intros Hf.
  rewrite (@field_at_change_composite Noise.CS W_hs_reject_response _ sh t_hs (DOT I._state) v v (JMeq_refl _))
    by reflexivity.
  change [StructField I._state; StructField I._handshake; StructField H._a_peer] with ([StructField I._state] ++ [StructField I._handshake; StructField H._a_peer]).
  rewrite (@field_at_app W_hs_reject_response sh t_pair [StructField I._state] [StructField I._handshake; StructField H._a_peer] v v p
             (JMeq_refl _)).
  f_equal.
  destruct (hrr_pair_addrs p Hf) as (_&_&_&_&_&_&Eap&_). rewrite Eap.
  unfold hs_addr, OFS_PEER_HANDSHAKE.
  assert (Hf': @field_compatible W_hs_reject_response t_pair [] p).
  { rewrite <- (@field_compatible_change_composite CSh W_hs_reject_response _ t_pair) by reflexivity. exact Hf. }
  rewrite field_address_offset by auto with field_compatible.
  rewrite offset_offset_val. reflexivity.
Qed.

(* an index table whose pool is one entry, given back from its head and that entry (after copy_peer) *)
Lemma hrr_itable_fold sht tab T a sh E : t_D T = [(a, sh, E)] -> itable_wf T ->
  @data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab * entry_at sh a E (succ_in (t_L T) a) (vin a (t_L T))
  |-- itable sht tab T.
Proof. intros HD Hw. rewrite (hs_itable1 sht tab T a sh E HD). entailer!. Qed.

(* the same, with the entry's successor known *)
Lemma hrr_itable_fold' sht tab T a sh E n : t_D T = [(a, sh, E)] -> itable_wf T -> succ_in (t_L T) a = n ->
  @data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab * entry_at sh a E n (vin a (t_L T))
  |-- itable sht tab T.
Proof. intros HD Hw <-. apply hrr_itable_fold; assumption. Qed.

Section Dev.
#[local] Existing Instance Noise.CS.

(* a device from its fields (main opens A's device to hand its identity to same_peer) *)
Lemma hrr_dev_fold sh wg D : field_compatible t_dev [] wg ->
  field_at_ sh t_dev (DOT I._dev) wg * identity_rep sh (id_addr wg) (d_id D) *
  field_at_ sh t_dev (DOT I._cookie_checker) wg * field_at sh t_dev (DOT I._peer_hashtable) (d_ptab D) wg *
  field_at sh t_dev (DOT I._index_hashtable) (d_itab D) wg
  |-- device_rep5 sh wg D.
Proof. intros Hf. unfold device_rep5. entailer!. Qed.

(* an initiation buffer, written or not, is a struct of its type *)
Lemma hrr_close_init_opt sh m Mo : init_opt_rep sh m Mo |-- data_at_ sh t_init m.
Proof. destruct Mo as [M|]; cbn [init_opt_rep]; [apply hs_close_init | apply derives_refl]. Qed.

End Dev.
