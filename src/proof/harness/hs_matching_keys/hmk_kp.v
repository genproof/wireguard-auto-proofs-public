(* The law hs_matching_keys: the views of the keypairs and of the peers' keypair slots that main reads at the
   end (a = p.a_peer.keypairs.current_keypair, b = p.b_peer.keypairs.next_keypair, their keys, their roles),
   at main's compspecs (the world W_hs_matching_keys).  Adapted from the x_handshake law (hhs3_p6_C1.v), whose
   peers are not inside a struct pair. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol5.prot_repr5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require WgNoise.harness.hs_matching_keys.code.
Local Open Scope logic.

Module C := WgNoise.harness.hs_matching_keys.code.

Notation W := W_hs_matching_keys.
#[local] Existing Instance W_hs_matching_keys.

#[local] Instance hmk_kp_cce_N : change_composite_env Noise.CS W.
Proof. make_cs_preserve Noise.CS W. Defined.
#[local] Instance hmk_kp_cce_H : change_composite_env CSh W.
Proof. make_cs_preserve CSh W. Defined.

(* a byte buffer is the same in any compspecs *)
Lemma hmk_tuchar_cs {cs1 cs2: compspecs} sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible, size_compatible, align_compatible. destruct p; simpl; try tauto.
  assert (A: forall ce, align_compatible_rec ce (tarray tuchar n) (Ptrofs.unsigned i)).
  { intros ce. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  pose proof (A (@cenv_cs cs1)). pose proof (A (@cenv_cs cs2)). tauto.
Qed.

(* ---------------------------------------------------------------------- *)
(* The peers' keypair slots as fields of struct pair                      *)
(* ---------------------------------------------------------------------- *)

Section PR.
#[local] Existing Instance Noise.CS.
(* a peer without its keypair slots *)
Definition hmk_prest (sh: share) (p: val) (P: peer) : mpred :=
  !! field_compatible t_peer [] p &&
  (field_at sh t_peer [StructField I._device] (p_device P) p *
   field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   hs_rep sh (hs_addr p) (p_hs P) *
   field_at_ sh t_peer [StructField I._last_sent_handshake] p *
   field_at_ sh t_peer [StructField I._latest_cookie] p *
   field_at sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   field_at_ sh t_peer [StructField I._internal_id] p *
   field_at sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).
End PR.

Lemma hmk_peer_split sh p P :
  peer_rep5 sh p P = hmk_prest sh p P * kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P).
Proof. unfold peer_rep5, hmk_prest. apply pred_ext; Intros; entailer!. Qed.

(* A's and B's keypair slots, as fields of struct pair at main's compspecs *)
Lemma hmk_kps_a sh p c pr n : @field_compatible CSh t_pair [] p ->
  kps_rep sh (kps_addr (pair_ap p)) c pr n =
  EX lk: val, @field_at W sh (Tstruct C._pair noattr) (DOT C._a_peer DOT C._keypairs) (c, (pr, (n, lk))) p.
Proof.
  intros FC0. assert (FC: @field_compatible W (Tstruct C._pair noattr) [] p)
    by (apply (@field_compatible_change_composite CSh W _); [prove_cs_preserve_type | exact FC0]).
  unfold kps_rep. apply pred_ext; Intros lk; Exists lk;
  rewrite field_at_data_at; rewrite field_address_offset by auto with field_compatible;
  unfold kps_addr, pair_ap, pair_bp, field_address; rewrite if_true by auto with field_compatible;
  rewrite offset_offset_val; simpl nested_field_type; simpl nested_field_offset;
  erewrite <- (@data_at_change_composite Noise.CS W _ sh t_kps); try apply JMeq_refl; try prove_cs_preserve_type;
  apply derives_refl.
Qed.

Lemma hmk_kps_b sh p c pr n : @field_compatible CSh t_pair [] p ->
  kps_rep sh (kps_addr (pair_bp p)) c pr n =
  EX lk: val, @field_at W sh (Tstruct C._pair noattr) (DOT C._b_peer DOT C._keypairs) (c, (pr, (n, lk))) p.
Proof.
  intros FC0. assert (FC: @field_compatible W (Tstruct C._pair noattr) [] p)
    by (apply (@field_compatible_change_composite CSh W _); [prove_cs_preserve_type | exact FC0]).
  unfold kps_rep. apply pred_ext; Intros lk; Exists lk;
  rewrite field_at_data_at; rewrite field_address_offset by auto with field_compatible;
  unfold kps_addr, pair_ap, pair_bp, field_address; rewrite if_true by auto with field_compatible;
  rewrite offset_offset_val; simpl nested_field_type; simpl nested_field_offset;
  erewrite <- (@data_at_change_composite Noise.CS W _ sh t_kps); try apply JMeq_refl; try prove_cs_preserve_type;
  apply derives_refl.
Qed.

(* ---------------------------------------------------------------------- *)
(* A keypair: its keys as byte buffers, its role at main's compspecs     *)
(* ---------------------------------------------------------------------- *)

Ltac hmk_sym_tac fld :=
  let FC0 := fresh in let LK := fresh in let E := fresh in
  intros sh k S FC0 LK;
  assert (FC: @field_compatible W t_kp [] k)
    by (apply (@field_compatible_change_composite Noise.CS W _); [prove_cs_preserve_type | exact FC0]);
  assert (E: @field_at Noise.CS sh t_kp [StructField fld] (symkey_val S) =
             @field_at W sh t_kp [StructField fld] (symkey_val S))
   by (apply (@field_at_change_composite Noise.CS W _ sh t_kp); [apply JMeq_refl | prove_cs_preserve_type]);
  rewrite E;
  unfold_field_at (@field_at W _ t_kp [StructField _] _ _);
  rewrite (@field_at_data_at W _ t_kp [StructField _; StructField _]);
  rewrite field_address_offset by auto with field_compatible;
  simpl nested_field_type; simpl nested_field_offset; unfold symkey_val, bytes_at; cbn [fst snd]; rewrite LK;
  change (Tarray (Tint I8 Unsigned _) 32 _) with (tarray tuchar 32);
  rewrite (hmk_tuchar_cs (cs1 := W) (cs2 := Noise.CS));
  apply pred_ext; cancel.

Lemma hmk_send : forall sh k S, @field_compatible Noise.CS t_kp [] k -> Zlength (sk_key S) = 32 ->
  @field_at Noise.CS sh t_kp [StructField I._sending] (symkey_val S) k =
  bytes_at sh (sk_key S) (offset_val 32 k) *
  @field_at W sh t_kp [StructField I._birthdate; StructField I._sending] (Vlong (sk_birth S)) k *
  @field_at W sh t_kp [StructField I._is_valid; StructField I._sending] (Val.of_bool (sk_valid S)) k *
  spacer sh 73 80 k.
Proof. hmk_sym_tac I._sending. Qed.

Lemma hmk_recv : forall sh k S, @field_compatible Noise.CS t_kp [] k -> Zlength (sk_key S) = 32 ->
  @field_at Noise.CS sh t_kp [StructField I._receiving] (symkey_val S) k =
  bytes_at sh (sk_key S) (offset_val 88 k) *
  @field_at W sh t_kp [StructField I._birthdate; StructField I._receiving] (Vlong (sk_birth S)) k *
  @field_at W sh t_kp [StructField I._is_valid; StructField I._receiving] (Val.of_bool (sk_valid S)) k *
  spacer sh 129 136 k.
Proof. hmk_sym_tac I._receiving. Qed.

Lemma hmk_ini sh k (v: val) :
  @field_at Noise.CS sh t_kp [StructField I._i_am_the_initiator] v k =
  @field_at W sh t_kp [StructField I._i_am_the_initiator] v k.
Proof. apply equal_f, (@field_at_change_composite Noise.CS W _ sh t_kp); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

Section KP.
#[local] Existing Instance Noise.CS.

(* a keypair without the fields main reads *)
Definition hmk_kprest (k: val) (K: keypair) : mpred :=
  @malloc_token W Ews (tarray tuchar SIZEOF_KEYPAIR) k *
  @field_at W Ews t_kp [StructField I._birthdate; StructField I._sending] (Vlong (sk_birth (kp_send K))) k *
  @field_at W Ews t_kp [StructField I._is_valid; StructField I._sending] (Val.of_bool (sk_valid (kp_send K))) k *
  spacer Ews 73 80 k *
  @field_at W Ews t_kp [StructField I._birthdate; StructField I._receiving] (Vlong (sk_birth (kp_recv K))) k *
  @field_at W Ews t_kp [StructField I._is_valid; StructField I._receiving] (Val.of_bool (sk_valid (kp_recv K))) k *
  spacer Ews 129 136 k *
  field_at Ews t_kp [StructField I._sending_counter] (Vlong (kp_scounter K)) k *
  (EX lk: val, field_at Ews t_kp [StructField I._receiving_counter]
                  (Vlong (kp_rcounter K), (lk, map Vlong (kp_backtrack K))) k) *
  field_at Ews t_kp [StructField I._remote_index] (Vint (kp_rindex K)) k *
  field_at Ews t_kp [StructField I._refcount] (Vint (kp_refs K)) k *
  (EX r: val, field_at Ews t_kp [StructField I._rcu] r k) *
  field_at Ews t_kp [StructField I._internal_id] (Vlong (kp_id K)) k *
  spacer Ews 1181 1184 k.

End KP.

(* the one keypair of a peer: its two keys, its role, the rest *)
Lemma hmk_kp_open k K :
  keypairs_rep W [(k, K)] =
  !! (@field_compatible Noise.CS t_kp [] k /\ kp_ok K) &&
  (bytes_at Ews (sk_key (kp_send K)) (offset_val 32 k) * bytes_at Ews (sk_key (kp_recv K)) (offset_val 88 k) *
   @field_at W Ews t_kp [StructField I._i_am_the_initiator] (Val.of_bool (kp_init K)) k * hmk_kprest k K).
Proof.
  unfold keypairs_rep, keypair_item_rep, keypair_rep, hmk_kprest.
  cbn [VST.msl.iter_sepcon.iter_sepcon]. rewrite sepcon_emp.
  apply pred_ext; Intros; rename H into FC; pose proof H0 as (L1 & L2 & L3);
  rewrite (hmk_send Ews k (kp_send K) FC L1), (hmk_recv Ews k (kp_recv K) FC L2), hmk_ini;
  entailer!.
Qed.

(* a keypair's entry is in its peer's index table: the keypair's address is a valid pointer (main compares
   it with NULL) *)
Lemma hmk_itable_vp sh tab k E D L : itable sh tab (mkT ((k, Ews, E) :: D) L) |-- valid_pointer k.
Proof.
  unfold itable, pool_item_rep, entry_at. cbn [t_D t_L VST.msl.iter_sepcon.iter_sepcon].
  Intros. entailer!.
Qed.

(* back from the views above, for main's return *)
Lemma hmk_kps_a_fold sh p c pr n lk : @field_compatible CSh t_pair [] p ->
  @field_at W sh (Tstruct C._pair noattr) (DOT C._a_peer DOT C._keypairs) (c, (pr, (n, lk))) p
  |-- kps_rep sh (kps_addr (pair_ap p)) c pr n.
Proof. intros FC. rewrite (hmk_kps_a sh p c pr n FC). Exists lk. apply derives_refl. Qed.

Lemma hmk_kps_b_fold sh p c pr n lk : @field_compatible CSh t_pair [] p ->
  @field_at W sh (Tstruct C._pair noattr) (DOT C._b_peer DOT C._keypairs) (c, (pr, (n, lk))) p
  |-- kps_rep sh (kps_addr (pair_bp p)) c pr n.
Proof. intros FC. rewrite (hmk_kps_b sh p c pr n FC). Exists lk. apply derives_refl. Qed.

Lemma hmk_peer_fold sh p P c pr n :
  p_cur P = c -> p_prev P = pr -> p_next P = n ->
  hmk_prest sh p P * kps_rep sh (kps_addr p) c pr n |-- peer_rep5 sh p P.
Proof. intros <- <- <-. rewrite hmk_peer_split. apply derives_refl. Qed.

Lemma hmk_bytes_eqb_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.
