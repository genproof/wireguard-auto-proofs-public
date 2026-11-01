(* The layout lemmas of hs_laws.h's struct pair and of the objects new_pair builds in it.

   struct pair (harness/hs_laws.h) holds two devices, their index and public-key tables and a peer for each
   device, with no padding: a at 0, b at 216, a_indices at 432, b_indices at 440, a_keys at 448, b_keys at
   456, a_peer at 464, b_peer at 960, size 1456.  Its members are noise.c's structs, described at noise.c's
   compspecs (Noise.CS) by the v5 representation, while struct pair itself exists only in the harness's
   compspecs CSh.  These lemmas move between the two:
   - hs_pair_split: uninitialised struct pair is its eight members, each uninitialised memory of its struct
     (main allocates struct pair on its stack, new_pair fills the members, main frees it at its return);
   - hs_dev_pub_split: a device's static public key as a byte buffer (new_pair passes B's public key to A's
     peer and A's to B's);
   - hs_table_itable: the index table of hs_table is the table head NULL and the peer's handshake entry;
   - hs_nondet_bytes, hs_bytes_free: the bytes drawn by nondet_bytes as a byte buffer, and back to memory. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise.
Require Import WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.protocol.prot_cs.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol5.prot_repr5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Local Open Scope logic.

(* noise.c's structs are the same in the harness's compspecs *)
#[export] Instance hs_pair_cce_NH : change_composite_env Noise.CS CSh.
Proof. make_cs_preserve Noise.CS CSh. Defined.
#[export] Instance hs_pair_cce_HN : change_composite_env CSh Noise.CS.
Proof. make_cs_preserve CSh Noise.CS. Defined.

(* ------------------------------------------------------------------------------------------------ *)
(* struct pair and its members                                                                       *)
(* ------------------------------------------------------------------------------------------------ *)

(* a memory block is two adjacent ones *)
Lemma hs_mb_split sh n m p :
  0 <= n -> 0 <= m -> n + m < Ptrofs.modulus ->
  memory_block sh (n + m) p = memory_block sh n p * memory_block sh m (offset_val n p).
Proof.
  intros N M NM.
  Transparent memory_block.
  destruct p as [| | | | | b i]; try (unfold memory_block; simpl; rewrite FF_sepcon; reflexivity).
  pose proof (Ptrofs.unsigned_range i).
  destruct (zlt (Ptrofs.unsigned i + (n + m)) Ptrofs.modulus).
  - rewrite <- (Ptrofs.repr_unsigned i). simpl offset_val. rewrite ptrofs_add_repr. apply memory_block_split; lia.
  - unfold memory_block. simpl offset_val.
    apply pred_ext.
    + normalize.
    + rewrite Ptrofs.add_unsigned, (Ptrofs.unsigned_repr n) by rep_lia.
      destruct (zlt (Ptrofs.unsigned i + n) Ptrofs.modulus).
      * rewrite Ptrofs.unsigned_repr by rep_lia. normalize; lia.
      * normalize; lia.
Qed.
Opaque memory_block.

Section Pair.
#[local] Existing Instance CSh.

(* the member fld of struct pair at p, of noise.c's struct t, is compatible with t at Noise.CS *)
Local Ltac hs_member fld t :=
  rewrite field_address_offset by auto with field_compatible;
  apply (@field_compatible_change_composite CSh Noise.CS _ t); [reflexivity |];
  apply (@field_compatible_nested_field CSh t_pair [StructField fld]); auto with field_compatible.

Lemma hs_pair_split sh p :
  @field_compatible CSh t_pair [] p ->
  @data_at_ CSh sh t_pair p =
  @data_at_ Noise.CS sh t_dev (pair_a p) * @data_at_ Noise.CS sh t_dev (pair_b p) *
  @data_at_ Noise.CS sh t_itab (pair_ai p) * @data_at_ Noise.CS sh t_itab (pair_bi p) *
  @data_at_ Noise.CS sh t_ptab (pair_ak p) * @data_at_ Noise.CS sh t_ptab (pair_bk p) *
  @data_at_ Noise.CS sh t_peer (pair_ap p) * @data_at_ Noise.CS sh t_peer (pair_bp p).
Proof.
  intros FC.
  (* each member is a struct of noise.c at its offset *)
  assert (F1: @field_compatible Noise.CS t_dev [] (pair_a p)) by (unfold pair_a; hs_member H._a t_dev).
  assert (F2: @field_compatible Noise.CS t_dev [] (pair_b p)) by (unfold pair_b; hs_member H._b t_dev).
  assert (F3: @field_compatible Noise.CS t_itab [] (pair_ai p)) by (unfold pair_ai; hs_member H._a_indices t_itab).
  assert (F4: @field_compatible Noise.CS t_itab [] (pair_bi p)) by (unfold pair_bi; hs_member H._b_indices t_itab).
  assert (F5: @field_compatible Noise.CS t_ptab [] (pair_ak p)) by (unfold pair_ak; hs_member H._a_keys t_ptab).
  assert (F6: @field_compatible Noise.CS t_ptab [] (pair_bk p)) by (unfold pair_bk; hs_member H._b_keys t_ptab).
  assert (F7: @field_compatible Noise.CS t_peer [] (pair_ap p)) by (unfold pair_ap; hs_member H._a_peer t_peer).
  assert (F8: @field_compatible Noise.CS t_peer [] (pair_bp p)) by (unfold pair_bp; hs_member H._b_peer t_peer).
  rewrite (@data_at__memory_block CSh), !(@data_at__memory_block Noise.CS), !prop_true_andp by auto.
  unfold pair_a, pair_b, pair_ai, pair_bi, pair_ak, pair_bk, pair_ap, pair_bp.
  rewrite !field_address_offset by auto with field_compatible.
  change (@sizeof CSh t_pair) with (216 + (216 + (8 + (8 + (8 + (8 + (496 + 496))))))).
  change (@sizeof Noise.CS t_dev) with 216. change (@sizeof Noise.CS t_itab) with 8.
  change (@sizeof Noise.CS t_ptab) with 8. change (@sizeof Noise.CS t_peer) with 496.
  rewrite !hs_mb_split by rep_lia.
  rewrite !offset_offset_val, !sepcon_assoc.
  assert (isptr p) by (destruct FC; auto). rewrite isptr_offset_val_zero by auto.
  reflexivity.
Qed.

End Pair.

(* ------------------------------------------------------------------------------------------------ *)
(* The objects of noise.c                                                                            *)
(* ------------------------------------------------------------------------------------------------ *)

Section NoiseObjects.
#[local] Existing Instance Noise.CS.

(* struct noise_static_identity: the two keys, the lock, has_identity and the tail padding *)
Lemma hs_sid_split sh a (pub priv: list val) (lk hv: val) :
  field_compatible t_sid [] a ->
  data_at sh t_sid ((pub, (priv, (lk, hv))) : reptype t_sid) a =
  data_at sh (tarray tuchar 32) pub a * data_at sh (tarray tuchar 32) priv (offset_val 32 a) *
  field_at sh t_sid (DOT I._lock) lk a * field_at sh t_sid (DOT I._has_identity) hv a * spacer sh 69 72 a.
Proof.
  intros FC.
  unfold_data_at (data_at _ _ _ a).
  rewrite (field_at_data_at _ _ (DOT I._static_public)), (field_at_data_at _ _ (DOT I._static_private)).
  rewrite !field_address_offset by auto with field_compatible.
  change (nested_field_offset t_sid (DOT I._static_public)) with 0.
  change (nested_field_offset t_sid (DOT I._static_private)) with 32.
  assert (isptr a) by (destruct FC; auto). rewrite isptr_offset_val_zero by auto.
  rewrite !sepcon_assoc. reflexivity.
Qed.

(* a device without its static public key: the rest of its identity and its other fields *)
Definition hs_dev_rest (sh: share) (wg: val) (D: device) : mpred :=
  !! (field_compatible t_dev [] wg /\ id_ok (d_id D)) &&
  EX lk: val,
  (field_at_ sh t_dev [StructField I._dev] wg *
   data_at sh (tarray tuchar 32) (bytes (id_priv (d_id D))) (offset_val 32 (id_addr wg)) *
   field_at sh t_sid [StructField I._lock] lk (id_addr wg) *
   field_at sh t_sid [StructField I._has_identity] (Val.of_bool (id_has (d_id D))) (id_addr wg) *
   spacer sh 69 72 (id_addr wg) *
   field_at_ sh t_dev [StructField I._cookie_checker] wg *
   field_at sh t_dev [StructField I._peer_hashtable] (d_ptab D) wg *
   field_at sh t_dev [StructField I._index_hashtable] (d_itab D) wg).

(* a device is its static public key (the first bytes of its identity) and the rest *)
Lemma hs_dev_pub_split sh wg D :
  device_rep5 sh wg D = bytes_at sh (id_pub (d_id D)) (id_addr wg) * hs_dev_rest sh wg D.
Proof.
  unfold device_rep5, hs_dev_rest, identity_rep, bytes_at.
  apply pred_ext.
  - Intros lk.
    assert_PROP (field_compatible t_sid [] (id_addr wg)) by entailer!.
    rewrite hs_sid_split by auto.
    Exists lk. match goal with Hi: id_ok _ |- _ => rewrite (proj1 Hi) end. entailer!.
  - Intros lk.
    assert (field_compatible t_sid [] (id_addr wg)).
    { unfold id_addr, OFS_DEV_IDENTITY.
      change 8 with (nested_field_offset t_dev [StructField I._static_identity]).
      assert (X: field_compatible t_dev (DOT I._static_identity) wg) by auto with field_compatible.
      exact (field_compatible_nested_field _ _ _ X). }
    Exists lk. rewrite hs_sid_split by auto.
    match goal with Hi: id_ok _ |- _ => rewrite (proj1 Hi) end. entailer!.
Qed.

(* the index table of new_pair: head NULL, its pool the peer's handshake entry, outside the hash lists *)
Lemma hs_table_itable sh tab pa :
  writable_share sh ->
  itable sh tab (hs_table sh pa) =
  data_at sh t_itab nullval tab * entry_out sh (hs_addr pa) (mkEntry pa IDX_HANDSHAKE Int.zero).
Proof.
  intros W. unfold itable, hs_table, entry_out. simpl.
  rewrite prop_true_andp.
  - rewrite sepcon_emp. reflexivity.
  - unfold itable_wf; simpl. split; [constructor |]. split; [intros x [] |].
    split; [constructor; [intros [] | constructor] |]. constructor; [exact W | constructor].
Qed.

End NoiseObjects.

(* the bytes drawn by nondet_bytes (as integers in byte range) are a byte buffer, in any compspecs *)
Lemma hs_nondet_bytes {cs: compspecs} sh n (bs: list Z) p :
  Zlength bs = n -> Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  @data_at cs sh (tarray tuchar n) (map (fun b => Vint (Int.repr b)) bs) p =
  bytes_at sh (map Byte.repr bs) p.
Proof.
  intros <- R. unfold bytes_at, bytes. rewrite Zlength_map.
  rewrite (@data_at_tarray_tuchar_cs cs Noise.CS). f_equal.
  induction R as [| b bs' Hb R IH]; [reflexivity |]. simpl. rewrite IH. f_equal.
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

(* a byte buffer is uninitialised memory of its size again, in any compspecs (freeing a local array) *)
Lemma hs_bytes_free {cs: compspecs} sh (bs: list byte) p :
  bytes_at sh bs p |-- @data_at_ cs sh (tarray tuchar (Zlength bs)) p.
Proof.
  unfold bytes_at. rewrite (@data_at_tarray_tuchar_cs Noise.CS cs). apply data_at_data_at_.
Qed.
