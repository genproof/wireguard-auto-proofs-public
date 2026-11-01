(* Giving back the stack memory of the hs_ harnesses: the objects new_pair builds in struct pair (hs_specs.v,
   hs_pair), after any run of noise.c's handshake functions, are again uninitialised memory (data_at_) of
   their structs.  main needs this at its return, where VST frees its local variables (struct pair p).

   A run may change the devices, the tables and the peers' states (any D, T, P below), but each index table
   still holds exactly its peer's handshake entry in its pool (the handshake functions update that entry in
   place; an entry lives inside its peer's struct, the pool is a separation of the entries).  The v5 predicates
   own every byte of their structs (padding included), so nothing is lost. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol5.prot_repr5.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Local Open Scope logic.

(* a pool item of an index table, with any list fields *)
Definition hs_pool_entry (x: val * share * entry) : mpred :=
  match x with (a, sh, E) => EX n: val, EX h: bool, entry_at sh a E n h end.

Section Objects.
#[local] Existing Instance Noise.CS.

(* a device is a struct wg_device *)
Lemma hs_close_dev sh wg D : device_rep5 sh wg D |-- data_at_ sh t_dev wg.
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
Lemma hs_close_peer sh p P E n h : peer_rep5 sh p P * entry_at sh (hs_addr p) E n h |-- data_at_ sh t_peer p.
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
Lemma hs_close_itable sh tab T : itable sh tab T |-- data_at_ sh t_itab tab * iter_sepcon hs_pool_entry (t_D T).
Proof.
  unfold itable. Intros. apply sepcon_derives; [apply data_at_data_at_ |].
  apply iter_sepcon_derives. intros [[a sh'] E] _. unfold pool_item_rep, hs_pool_entry.
  Exists (succ_in (t_L T) a) (vin a (t_L T)). apply derives_refl.
Qed.

(* a handshake message (its macs any) is a struct of its type *)
Lemma hs_close_init sh m M : init_rep5 sh m M |-- data_at_ sh t_init m.
Proof.
  unfold init_rep5. Intros.
  unfold_data_at (data_at_ sh t_init m).
  repeat match goal with |- _ |-- ?R => match R with context [@field_at Noise.CS sh t_init ?g ?v m] =>
    change (@field_at Noise.CS sh t_init g v m) with (@field_at_ Noise.CS sh t_init g m) end end.
  repeat match goal with |- context [@field_at Noise.CS sh t_init ?g ?v m] =>
    sep_apply (@field_at_field_at_ Noise.CS sh t_init g v m) end.
  cancel.
Qed.

Lemma hs_close_resp sh m M : resp_rep5 sh m M |-- data_at_ sh t_resp m.
Proof.
  unfold resp_rep5. Intros.
  unfold_data_at (data_at_ sh t_resp m).
  repeat match goal with |- _ |-- ?R => match R with context [@field_at Noise.CS sh t_resp ?g ?v m] =>
    change (@field_at Noise.CS sh t_resp g v m) with (@field_at_ Noise.CS sh t_resp g m) end end.
  repeat match goal with |- context [@field_at Noise.CS sh t_resp ?g ?v m] =>
    sep_apply (@field_at_field_at_ Noise.CS sh t_resp g v m) end.
  cancel.
Qed.

End Objects.

(* the structs of noise.c have the same layout in the harness's compspecs *)
#[local] Instance hs_close_n2h : change_composite_env Noise.CS CSh.
Proof. make_cs_preserve Noise.CS CSh. Defined.

(* struct pair is its eight members, each uninitialised memory of its struct (the step of hs_pair_close below;
   a law whose tables hold more entries, e.g. keypairs, frees those itself and uses this) *)
Lemma hs_pair_join sh p :
  @field_compatible CSh t_pair [] p ->
  @data_at_ Noise.CS sh t_dev (pair_a p) * @data_at_ Noise.CS sh t_dev (pair_b p) *
  @data_at_ Noise.CS sh t_itab (pair_ai p) * @data_at_ Noise.CS sh t_itab (pair_bi p) *
  @data_at_ Noise.CS sh t_ptab (pair_ak p) * @data_at_ Noise.CS sh t_ptab (pair_bk p) *
  @data_at_ Noise.CS sh t_peer (pair_ap p) * @data_at_ Noise.CS sh t_peer (pair_bp p)
  |-- @data_at_ CSh sh t_pair p.
Proof.
  intros _.
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

(* struct pair after a run: devices DA, DB, index tables TA, TB each holding its peer's handshake entry, any
   public-key tables, peers PA, PB *)
Lemma hs_pair_close sh p DA DB TA TB ka kb PA PB EA EB :
  @field_compatible CSh t_pair [] p ->
  t_D TA = [(hs_addr (pair_ap p), sh, EA)] -> t_D TB = [(hs_addr (pair_bp p), sh, EB)] ->
  device_rep5 sh (pair_a p) DA * device_rep5 sh (pair_b p) DB *
  itable sh (pair_ai p) TA * itable sh (pair_bi p) TB *
  ptable sh (pair_ak p) ka * ptable sh (pair_bk p) kb *
  peer_rep5 sh (pair_ap p) PA * peer_rep5 sh (pair_bp p) PB
  |-- @data_at_ CSh sh t_pair p.
Proof.
  intros FC HA HB.
  sep_apply (hs_close_dev sh (pair_a p) DA). sep_apply (hs_close_dev sh (pair_b p) DB).
  sep_apply (hs_close_itable sh (pair_ai p) TA). sep_apply (hs_close_itable sh (pair_bi p) TB).
  rewrite HA, HB. simpl iter_sepcon. unfold hs_pool_entry. rewrite !sepcon_emp. Intros nb hb na ha.
  sep_apply (hs_close_peer sh (pair_ap p) PA EA na ha). sep_apply (hs_close_peer sh (pair_bp p) PB EB nb hb).
  unfold ptable.
  sep_apply (@data_at_data_at_ Noise.CS sh t_ptab ka (pair_ak p)).
  sep_apply (@data_at_data_at_ Noise.CS sh t_ptab kb (pair_bk p)).
  eapply derives_trans; [| apply (hs_pair_join sh p FC)].
  cancel.
Qed.
