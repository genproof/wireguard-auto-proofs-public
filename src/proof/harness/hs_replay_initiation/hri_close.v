(* law hs_replay_initiation: giving back main's stack memory at its returns.

   main's locals are struct pair p, the initiation message and the response message.  At a return they must be
   uninitialised memory (data_at_) of their types again.  The messages hold a message (init_rep5 / resp_rep5) or
   are still uninitialised.  The pair holds the devices, tables and peers as the handshake functions left them;
   B's index table may hold, besides B's handshake entry, the entry of a keypair begin_session allocated (that
   entry lives in the keypair's heap memory and is dropped with it).  So the pair is closed from each table's
   own handshake entry, found in its pool with the pair's share (hri_in_pool, hri_model.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol5.prot_repr5.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_close.
Require Import WgNoise.proof.harness.hs_replay_initiation.hri_model.
Local Open Scope logic.

Section Objects.
#[local] Existing Instance Noise.CS.

(* a device is a struct wg_device *)
Lemma hri_close_dev sh wg D : device_rep5 sh wg D |-- data_at_ sh t_dev wg.
Proof.
  unfold device_rep5, identity_rep. Intros lk.
  assert (FI: data_at sh t_sid (bytes (id_pub (d_id D)), (bytes (id_priv (d_id D)), (lk, Val.of_bool (id_has (d_id D)))))
                (id_addr wg) |-- field_at_ sh t_dev [StructField I._static_identity] wg).
  { unfold field_at_. rewrite field_at_data_at. unfold id_addr, OFS_DEV_IDENTITY.
    rewrite field_address_offset by auto with field_compatible. apply data_at_data_at_. }
  sep_apply FI.
  unfold_data_at (data_at_ sh t_dev wg).
  repeat match goal with |- _ |-- ?R => match R with context [@field_at Noise.CS sh t_dev ?g ?v wg] =>
    change (@field_at Noise.CS sh t_dev g v wg) with (@field_at_ Noise.CS sh t_dev g wg) end end.
  repeat match goal with |- context [@field_at Noise.CS sh t_dev ?g ?v wg] =>
    sep_apply (@field_at_field_at_ Noise.CS sh t_dev g v wg) end.
  cancel.
Qed.

(* a peer with its handshake entry is a struct wg_peer *)
Lemma hri_close_peer sh p P E n h : peer_rep5 sh p P * entry_at sh (hs_addr p) E n h |-- data_at_ sh t_peer p.
Proof.
  unfold peer_rep5. Intros.
  sep_apply (prot_rep3_hs_whole sh (hs_addr p) (p_hs P) E n h).
  assert (FH: data_at_ sh t_hs (hs_addr p) |-- field_at_ sh t_peer (DOT I._handshake) p).
  { unfold field_at_. rewrite field_at_data_at. rewrite field_address_offset by auto with field_compatible.
    apply derives_refl. }
  assert (FK: kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) |-- field_at_ sh t_peer (DOT I._keypairs) p).
  { unfold kps_rep. Intros lk. unfold field_at_. rewrite field_at_data_at.
    rewrite field_address_offset by auto with field_compatible. apply data_at_data_at_. }
  sep_apply FH. sep_apply FK.
  unfold_data_at (data_at_ sh t_peer p).
  repeat match goal with |- _ |-- ?R => match R with context [@field_at Noise.CS sh t_peer ?g ?v p] =>
    change (@field_at Noise.CS sh t_peer g v p) with (@field_at_ Noise.CS sh t_peer g p) end end.
  repeat match goal with |- context [@field_at Noise.CS sh t_peer ?g ?v p] =>
    sep_apply (@field_at_field_at_ Noise.CS sh t_peer g v p) end.
  cancel.
Qed.

(* an index table is its struct and the entries of its pool *)
Lemma hri_close_itable sh tab T : itable sh tab T |-- data_at_ sh t_itab tab * iter_sepcon hs_pool_entry (t_D T).
Proof.
  unfold itable. Intros. apply sepcon_derives; [apply data_at_data_at_ |].
  apply iter_sepcon_derives. intros [[a sh'] E] _. unfold pool_item_rep, hs_pool_entry.
  Exists (succ_in (t_L T) a) (vin a (t_L T)). apply derives_refl.
Qed.

(* a message (macs any) is a struct message_handshake_initiation / _response *)
Lemma hri_close_init sh m M : init_rep5 sh m M |-- data_at_ sh t_init m.
Proof.
  unfold init_rep5. Intros.
  unfold_data_at (data_at_ sh t_init m).
  repeat match goal with |- _ |-- ?R => match R with context [@field_at Noise.CS sh t_init ?g ?v m] =>
    change (@field_at Noise.CS sh t_init g v m) with (@field_at_ Noise.CS sh t_init g m) end end.
  repeat match goal with |- context [@field_at Noise.CS sh t_init ?g ?v m] =>
    sep_apply (@field_at_field_at_ Noise.CS sh t_init g v m) end.
  cancel.
Qed.

Lemma hri_close_resp sh m M : resp_rep5 sh m M |-- data_at_ sh t_resp m.
Proof.
  unfold resp_rep5. Intros.
  unfold_data_at (data_at_ sh t_resp m).
  repeat match goal with |- _ |-- ?R => match R with context [@field_at Noise.CS sh t_resp ?g ?v m] =>
    change (@field_at Noise.CS sh t_resp g v m) with (@field_at_ Noise.CS sh t_resp g m) end end.
  repeat match goal with |- context [@field_at Noise.CS sh t_resp ?g ?v m] =>
    sep_apply (@field_at_field_at_ Noise.CS sh t_resp g v m) end.
  cancel.
Qed.

(* the entry at a, found in a pool with share sh, can be taken out of the pool's items *)
Lemma hri_pool_take D a sh E :
  sfind D a = Some (sh, E) ->
  iter_sepcon hs_pool_entry D |-- (EX n: val, EX h: bool, entry_at sh a E n h) * TT.
Proof.
  induction D as [|[[x shx] w] D IH]; cbn; [discriminate|]. intros H.
  destruct (EqDec_val x a) as [->|N].
  - inversion H; subst. cancel.
  - specialize (IH H). sep_apply IH. cancel.
Qed.

End Objects.

(* the structs of noise.c have the same layout in the harness's compspecs *)
#[local] Instance hri_close_n2h : change_composite_env Noise.CS CSh.
Proof. make_cs_preserve Noise.CS CSh. Defined.

(* struct pair is its eight members, each uninitialised memory of its struct *)
Lemma hri_pair_join sh p :
  @data_at_ Noise.CS sh t_dev (pair_a p) * @data_at_ Noise.CS sh t_dev (pair_b p) *
  @data_at_ Noise.CS sh t_itab (pair_ai p) * @data_at_ Noise.CS sh t_itab (pair_bi p) *
  @data_at_ Noise.CS sh t_ptab (pair_ak p) * @data_at_ Noise.CS sh t_ptab (pair_bk p) *
  @data_at_ Noise.CS sh t_peer (pair_ap p) * @data_at_ Noise.CS sh t_peer (pair_bp p)
  |-- @data_at_ CSh sh t_pair p.
Proof.
  rewrite !(@data_at__change_composite Noise.CS CSh _ sh) by reflexivity.
  (* unfold_data_at does not go through at CSh: split struct pair by field_at_Tstruct by hand, keeping its
     default value abstract while the member list is computed (struct pair has no padding: no spacer) *)
  unfold data_at_ at 9. unfold field_at_.
  pose (V := @default_val CSh (@nested_field_type CSh t_pair [])).
  pose proof (@field_at_Tstruct CSh sh t_pair [] H._pair noattr V V p eq_refl (JMeq_refl _)) as HH.
  fold V. rewrite HH. clear HH.
  simpl co_members. lazy beta iota zeta delta [nested_sfieldlist_at]. cbv beta iota zeta delta [withspacer].
  assert (HV: V = default_val (nested_field_type t_pair [])) by reflexivity.
  clearbody V. simpl. subst V.
  repeat match goal with |- context [@field_at CSh sh t_pair ?g ?v p] =>
    change (@field_at CSh sh t_pair g v p) with (@field_at_ CSh sh t_pair g p) end.
  rewrite !field_at__data_at_.
  unfold pair_a, pair_b, pair_ai, pair_bi, pair_ak, pair_bk, pair_ap, pair_bp.
  simpl nested_field_type.
  cancel.
Qed.

(* struct pair after a run: devices DA, DB, index tables TA, TB each holding its peer's handshake entry in its
   pool with the pair's share (and possibly other entries), any public-key tables, peers PA, PB *)
Lemma hri_pair_close sh p DA DB TA TB ka kb PA PB :
  @field_compatible CSh t_pair [] p ->
  hri_in_pool TA (hs_addr (pair_ap p)) sh -> hri_in_pool TB (hs_addr (pair_bp p)) sh ->
  device_rep5 sh (pair_a p) DA * device_rep5 sh (pair_b p) DB *
  itable sh (pair_ai p) TA * itable sh (pair_bi p) TB *
  ptable sh (pair_ak p) ka * ptable sh (pair_bk p) kb *
  peer_rep5 sh (pair_ap p) PA * peer_rep5 sh (pair_bp p) PB
  |-- @data_at_ CSh sh t_pair p * TT.
Proof.
  intros Hfc [EA HA] [EB HB].
  sep_apply (hri_close_dev sh (pair_a p) DA). sep_apply (hri_close_dev sh (pair_b p) DB).
  sep_apply (hri_close_itable sh (pair_ai p) TA). sep_apply (hri_close_itable sh (pair_bi p) TB).
  sep_apply (hri_pool_take _ _ _ _ HA). sep_apply (hri_pool_take _ _ _ _ HB).
  Intros nB hB nA hA.
  sep_apply (hri_close_peer sh (pair_ap p) PA EA nA hA). sep_apply (hri_close_peer sh (pair_bp p) PB EB nB hB).
  assert (Hpt: forall t h, ptable sh t h |-- @data_at_ Noise.CS sh t_ptab t)
    by (intros; unfold ptable; apply data_at_data_at_).
  sep_apply (Hpt (pair_ak p) ka). sep_apply (Hpt (pair_bk p) kb).
  sep_apply (hri_pair_join sh p). cancel.
Qed.

(* the closing lemmas together *)
Theorem hri_close_all :
  (forall sh m M, init_rep5 sh m M |-- @data_at_ Noise.CS sh t_init m) /\
  (forall sh m M, resp_rep5 sh m M |-- @data_at_ Noise.CS sh t_resp m) /\
  (forall sh p DA DB TA TB ka kb PA PB,
     @field_compatible CSh t_pair [] p ->
     hri_in_pool TA (hs_addr (pair_ap p)) sh -> hri_in_pool TB (hs_addr (pair_bp p)) sh ->
     device_rep5 sh (pair_a p) DA * device_rep5 sh (pair_b p) DB *
     itable sh (pair_ai p) TA * itable sh (pair_bi p) TB *
     ptable sh (pair_ak p) ka * ptable sh (pair_bk p) kb *
     peer_rep5 sh (pair_ap p) PA * peer_rep5 sh (pair_bp p) PB
     |-- @data_at_ CSh sh t_pair p * TT).
Proof.
  split; [exact hri_close_init|]. split; [exact hri_close_resp|]. exact hri_pair_close.
Qed.
