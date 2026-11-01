(* law keypairs: helpers of check_all's segment NODE
   (hkp5_check_body_node.v): the keypair, the table and the node opened field by field, the byte arrays bytes_eq
   compares focused with a wand.  Port of v1's hkp4_check_node.v, prefix hkc5n_. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_defs.

#[local] Existing Instance W_keypairs.
Local Open Scope Z_scope.
Local Notation iter_sepcon := VST.msl.iter_sepcon.iter_sepcon.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* Noise.CS -> W_keypairs                                                  *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hkc5n_CCE : change_composite_env Noise.CS W_keypairs.
Proof. make_cs_preserve Noise.CS W_keypairs. Defined.

Lemma hkc5n_kpcs : cs_preserve_type Noise.CS W_keypairs (@coeq _ _ hkc5n_CCE) t_kp = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hkc5n_fc k : @field_compatible Noise.CS t_kp [] k -> @field_compatible W_keypairs t_kp [] k.
Proof.
  intros H. apply (@field_compatible_change_composite Noise.CS W_keypairs hkc5n_CCE t_kp hkc5n_kpcs). exact H.
Qed.

(* byte arrays do not depend on the compspecs *)
Lemma hkc5n_bytes_cs {cs1 cs2: compspecs} sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  intros. unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  assert (forall (ce: composite_env) z, align_compatible_rec ce (tarray tuchar n) z).
  { intros. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  unfold field_compatible, size_compatible, align_compatible.
  destruct p; simpl; try tauto.
  pose proof (H (@cenv_cs cs1) (Ptrofs.unsigned i)). pose proof (H (@cenv_cs cs2) (Ptrofs.unsigned i)). tauto.
Qed.

Ltac hkc5n_cs f :=
  exact (f_equal (fun g => g _) (@field_at_change_composite Noise.CS W_keypairs hkc5n_CCE _ t_kp
           [StructField f] _ _ (JMeq_refl _) hkc5n_kpcs)).

Lemma hkc5n_cs_sending sh (v: @reptype Noise.CS t_sym) k :
  @field_at Noise.CS sh t_kp [StructField prot_repr3.I._sending] v k = @field_at W_keypairs sh t_kp (DOT KC._sending) v k.
Proof. hkc5n_cs prot_repr3.I._sending. Qed.

Lemma hkc5n_cs_receiving sh (v: @reptype Noise.CS t_sym) k :
  @field_at Noise.CS sh t_kp [StructField prot_repr3.I._receiving] v k = @field_at W_keypairs sh t_kp (DOT KC._receiving) v k.
Proof. hkc5n_cs prot_repr3.I._receiving. Qed.

Lemma hkc5n_cs_rindex sh v k :
  @field_at Noise.CS sh t_kp [StructField prot_repr3.I._remote_index] v k = @field_at W_keypairs sh t_kp (DOT KC._remote_index) v k.
Proof. hkc5n_cs prot_repr3.I._remote_index. Qed.

Lemma hkc5n_cs_init sh v k :
  @field_at Noise.CS sh t_kp [StructField prot_repr3.I._i_am_the_initiator] v k =
  @field_at W_keypairs sh t_kp (DOT KC._i_am_the_initiator) v k.
Proof. hkc5n_cs prot_repr3.I._i_am_the_initiator. Qed.

Lemma hkc5n_cs_refcount sh v k :
  @field_at Noise.CS sh t_kp [StructField prot_repr3.I._refcount] v k = @field_at W_keypairs sh t_kp (DOT KC._refcount) v k.
Proof. hkc5n_cs prot_repr3.I._refcount. Qed.

Lemma hkc5n_cs_id sh v k :
  @field_at Noise.CS sh t_kp [StructField prot_repr3.I._internal_id] v k = @field_at W_keypairs sh t_kp (DOT KC._internal_id) v k.
Proof. hkc5n_cs prot_repr3.I._internal_id. Qed.

Lemma hkc5n_cs_scnt sh v k :
  @field_at Noise.CS sh t_kp [StructField prot_repr3.I._sending_counter] v k =
  @field_at W_keypairs sh t_kp (DOT KC._sending_counter) v k.
Proof. hkc5n_cs prot_repr3.I._sending_counter. Qed.

Lemma hkc5n_cs_rcnt sh (v: @reptype Noise.CS hk5_t_rc) k :
  @field_at Noise.CS sh t_kp [StructField prot_repr3.I._receiving_counter] v k =
  @field_at W_keypairs sh t_kp (DOT KC._receiving_counter) v k.
Proof. hkc5n_cs prot_repr3.I._receiving_counter. Qed.

Lemma hkc5n_cs_entry sh v k : @field_compatible Noise.CS t_kp [] k ->
  @data_at Noise.CS sh t_entry_s v k = @field_at W_keypairs sh t_kp (DOT KC._entry) v k.
Proof.
  intros FC0. pose proof (hkc5n_fc k FC0) as FC.
  rewrite (@data_at_change_composite Noise.CS W_keypairs _ sh t_entry_s v v (JMeq_refl v)) by (vm_compute; reflexivity).
  assert (FC3: @field_compatible W_keypairs t_kp (DOT KC._entry) k) by auto with field_compatible.
  rewrite field_at_data_at. rewrite field_address_offset by auto. simpl.
  rewrite isptr_offset_val_zero by (destruct FC as [Hp _]; exact Hp).
  reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* The opened keypair and table                                            *)
(* ---------------------------------------------------------------------- *)

(* the fields of the keypair the loop body does not read *)
Definition hkc5n_kp_rest (k: val) (K: keypair) : mpred :=
  @malloc_token W_keypairs Ews (tarray tuchar SIZEOF_KEYPAIR) k *
  (EX r: val, @field_at Noise.CS Ews t_kp [StructField prot_repr3.I._rcu] r k) *
  spacer Ews 1181 1184 k.

(* the opened keypair (lk: the receiving counter's lock) *)
Definition hkc5n_kp_fields (k: val) (K: keypair) (lk: val) : mpred :=
  @field_at W_keypairs Ews t_kp (DOT KC._sending) (symkey_val (kp_send K)) k *
  @field_at W_keypairs Ews t_kp (DOT KC._receiving) (symkey_val (kp_recv K)) k *
  @field_at W_keypairs Ews t_kp (DOT KC._remote_index) (Vint (kp_rindex K)) k *
  @field_at W_keypairs Ews t_kp (DOT KC._i_am_the_initiator) (Val.of_bool (kp_init K)) k *
  @field_at W_keypairs Ews t_kp (DOT KC._refcount) (Vint (kp_refs K)) k *
  @field_at W_keypairs Ews t_kp (DOT KC._internal_id) (Vlong (kp_id K)) k *
  @field_at W_keypairs Ews t_kp (DOT KC._sending_counter) (Vlong (kp_scounter K)) k *
  @field_at W_keypairs Ews t_kp (DOT KC._receiving_counter) (Vlong (kp_rcounter K), (lk, map Vlong (kp_backtrack K))) k.

Lemma hkc5n_kp_open_d k K :
  keypair_rep W_keypairs k K |--
  EX lk: val, !! (@field_compatible Noise.CS t_kp [] k /\ kp_ok K) &&
  (hkc5n_kp_fields k K lk * hkc5n_kp_rest k K).
Proof.
  unfold keypair_rep, hkc5n_kp_rest, hkc5n_kp_fields. Intros r lk. Exists lk.
  rewrite hkc5n_cs_sending, hkc5n_cs_receiving, hkc5n_cs_rindex, hkc5n_cs_init, hkc5n_cs_refcount, hkc5n_cs_id,
    hkc5n_cs_scnt, hkc5n_cs_rcnt.
  entailer!. Exists r. cancel.
Qed.

Lemma hkc5n_kp_close k K lk :
  @field_compatible Noise.CS t_kp [] k -> kp_ok K ->
  hkc5n_kp_fields k K lk * hkc5n_kp_rest k K |-- keypair_rep W_keypairs k K.
Proof.
  intros FC KO. unfold keypair_rep, hkc5n_kp_rest, hkc5n_kp_fields.
  Intros r. apply andp_right; [apply prop_right; auto |]. Exists r lk.
  rewrite hkc5n_cs_sending, hkc5n_cs_receiving, hkc5n_cs_rindex, hkc5n_cs_init, hkc5n_cs_refcount, hkc5n_cs_id,
    hkc5n_cs_scnt, hkc5n_cs_rcnt.
  cancel.
Qed.

Lemma hkc5n_pool_split {A: Type} (D: list (val * share * A)) a sh E (f: val * share * A -> mpred) :
  sfind D a = Some (sh, E) -> iter_sepcon f D = f (a, sh, E) * iter_sepcon f (sdel D a).
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros Hs; [discriminate|].
  destruct (EqDec_val x a); [inv Hs; reflexivity|].
  rewrite (IH Hs); simpl. rewrite <- !sepcon_assoc, (sepcon_comm (f _) (f _)). reflexivity.
Qed.

Lemma hkc5n_sfind_in {A: Type} (D: list (val * share * A)) a sh E :
  sfind D a = Some (sh, E) -> In a (saddrs D).
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros Hs; [discriminate|].
  destruct (EqDec_val x a); [left; auto | right; auto].
Qed.

(* the table without the keypair's entry *)
Definition hkc5n_itab_rest (sht: share) (tab: val) (T: tstate) (k: val) : mpred :=
  @data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab * iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) k).

Lemma hkc5n_itab_open sht tab T k E :
  @field_compatible Noise.CS t_kp [] k -> sfind (t_D T) k = Some (Ews, E) ->
  itable sht tab T =
  !! itable_wf T &&
  (hkc5n_itab_rest sht tab T k *
   @field_at W_keypairs Ews t_kp (DOT KC._entry) (entry_val E (succ_in (t_L T) k) (vin k (t_L T))) k).
Proof.
  intros FC Hs. unfold itable, hkc5n_itab_rest. rewrite (hkc5n_pool_split _ _ _ _ _ Hs).
  unfold pool_item_rep at 1, entry_at. rewrite hkc5n_cs_entry by auto.
  f_equal. apply pred_ext; cancel.
Qed.

Lemma hkc5n_itab_open_d sht tab T k E :
  @field_compatible Noise.CS t_kp [] k -> sfind (t_D T) k = Some (Ews, E) ->
  itable sht tab T |--
  !! itable_wf T &&
  (hkc5n_itab_rest sht tab T k *
   @field_at W_keypairs Ews t_kp (DOT KC._entry) (entry_val E (succ_in (t_L T) k) (vin k (t_L T))) k).
Proof. intros FC Hs. rewrite (hkc5n_itab_open sht tab T k E FC Hs). apply derives_refl. Qed.

Lemma hkc5n_itab_close sht tab T k E h :
  @field_compatible Noise.CS t_kp [] k -> sfind (t_D T) k = Some (Ews, E) -> itable_wf T -> vin k (t_L T) = h ->
  hkc5n_itab_rest sht tab T k *
  @field_at W_keypairs Ews t_kp (DOT KC._entry) (entry_val E (succ_in (t_L T) k) h) k |-- itable sht tab T.
Proof.
  intros FC Hs W <-. rewrite (hkc5n_itab_open sht tab T k E FC Hs).
  apply andp_right; [apply prop_right; auto | apply derives_refl].
Qed.

(* ---------------------------------------------------------------------- *)
(* The byte arrays compared by bytes_eq, focused with a wand               *)
(* ---------------------------------------------------------------------- *)

(* the node, field by field (its byte arrays as data_at at their addresses) *)
Lemma hkc5n_node_eq M nx m :
  @data_at W_keypairs Ews t_mk5 (hk5_mk_val M nx) m =
  field_at Ews t_mk5 (DOT KC._kp) (m5_kp M) m * field_at Ews t_mk5 (DOT KC._refs) (Vint (m5_refs M)) m *
  spacer Ews 12 16 m * field_at Ews t_mk5 (DOT KC._held) (Vlong (m5_held M)) m *
  field_at Ews t_mk5 (DOT KC._hashed) (Val.of_bool (m5_hashed M)) m * spacer Ews 25 28 m *
  field_at Ews t_mk5 (DOT KC._index) (Vint (m5_index M)) m *
  data_at Ews (tarray tuchar 32) (bytes (m5_send M)) (field_address t_mk5 (DOT KC._send) m) *
  data_at Ews (tarray tuchar 32) (bytes (m5_recv M)) (field_address t_mk5 (DOT KC._recv) m) *
  field_at Ews t_mk5 (DOT KC._send_valid) (Val.of_bool (m5_sv M)) m *
  field_at Ews t_mk5 (DOT KC._recv_valid) (Val.of_bool (m5_rv M)) m *
  field_at Ews t_mk5 (DOT KC._initiator) (Val.of_bool (m5_init M)) m * spacer Ews 99 100 m *
  field_at Ews t_mk5 (DOT KC._remote_index) (Vint (m5_rindex M)) m *
  field_at Ews t_mk5 (DOT KC._birth) (Vlong (m5_birth M)) m *
  field_at Ews t_mk5 (DOT KC._id) (Vlong (m5_id M)) m *
  field_at Ews t_mk5 (DOT KC._scnt) (Vlong (m5_scnt M)) m *
  field_at Ews t_mk5 (DOT KC._rcnt) (Vlong (m5_rcnt M)) m *
  field_at Ews t_mk5 (DOT KC._next) nx m.
Proof.
  match goal with |- @data_at _ _ _ ?v _ = _ => set (V := v) end.
  unfold data_at. rewrite (@field_at_Tstruct W_keypairs Ews t_mk5 [] KC._mk noattr V V m eq_refl (JMeq_refl _)).
  simpl co_members. lazy beta iota zeta delta [nested_sfieldlist_at].
  simpl struct_pred. unfold withspacer. simpl nested_field_offset. simpl sizeof.
  repeat match goal with |- context [Z.eq_dec ?x ?y] =>
    destruct (Z.eq_dec x y); [try (exfalso; lia) | try (exfalso; lia)] end.
  subst V.
  rewrite (field_at_data_at Ews t_mk5 (DOT KC._send)), (field_at_data_at Ews t_mk5 (DOT KC._recv)).
  simpl nested_field_type. apply pred_ext; cancel.
Qed.

Lemma hkc5n_sym_eq_send S k :
  @field_at W_keypairs Ews t_kp (DOT KC._sending) (symkey_val S) k =
  data_at Ews (tarray tuchar 32) (bytes (sk_key S)) (field_address t_kp [StructField KC._key; StructField KC._sending] k) *
  field_at Ews t_kp [StructField KC._birthdate; StructField KC._sending] (Vlong (sk_birth S)) k *
  field_at Ews t_kp [StructField KC._is_valid; StructField KC._sending] (Val.of_bool (sk_valid S)) k *
  spacer Ews 73 80 k.
Proof.
  match goal with |- @field_at _ _ _ _ ?v _ = _ => set (V := v) end.
  rewrite (@field_at_Tstruct W_keypairs Ews t_kp (DOT KC._sending) KC._noise_symmetric_key noattr V V k eq_refl (JMeq_refl _)).
  simpl co_members. lazy beta iota zeta delta [nested_sfieldlist_at].
  simpl struct_pred. unfold withspacer. simpl nested_field_offset. simpl sizeof.
  repeat match goal with |- context [Z.eq_dec ?x ?y] =>
    destruct (Z.eq_dec x y); [try (exfalso; lia) | try (exfalso; lia)] end.
  subst V.
  rewrite (field_at_data_at Ews t_kp [StructField KC._key; StructField KC._sending]).
  simpl nested_field_type. apply pred_ext; cancel.
Qed.

Lemma hkc5n_sym_eq_recv S k :
  @field_at W_keypairs Ews t_kp (DOT KC._receiving) (symkey_val S) k =
  data_at Ews (tarray tuchar 32) (bytes (sk_key S)) (field_address t_kp [StructField KC._key; StructField KC._receiving] k) *
  field_at Ews t_kp [StructField KC._birthdate; StructField KC._receiving] (Vlong (sk_birth S)) k *
  field_at Ews t_kp [StructField KC._is_valid; StructField KC._receiving] (Val.of_bool (sk_valid S)) k *
  spacer Ews 129 136 k.
Proof.
  match goal with |- @field_at _ _ _ _ ?v _ = _ => set (V := v) end.
  rewrite (@field_at_Tstruct W_keypairs Ews t_kp (DOT KC._receiving) KC._noise_symmetric_key noattr V V k eq_refl (JMeq_refl _)).
  simpl co_members. lazy beta iota zeta delta [nested_sfieldlist_at].
  simpl struct_pred. unfold withspacer. simpl nested_field_offset. simpl sizeof.
  repeat match goal with |- context [Z.eq_dec ?x ?y] =>
    destruct (Z.eq_dec x y); [try (exfalso; lia) | try (exfalso; lia)] end.
  subst V.
  rewrite (field_at_data_at Ews t_kp [StructField KC._key; StructField KC._receiving]).
  simpl nested_field_type. apply pred_ext; cancel.
Qed.

Lemma hkc5n_hb sh A x : Zlength A = 32 -> @data_at W_keypairs sh (tarray tuchar 32) (bytes A) x = hbytes sh A x.
Proof. intros L. unfold hbytes. rewrite L. apply hkc5n_bytes_cs. Qed.

Lemma hkc5n_focus_node_send M nx m : Zlength (m5_send M) = 32 ->
  @data_at W_keypairs Ews t_mk5 (hk5_mk_val M nx) m |--
  hbytes Ews (m5_send M) (offset_val 32 m) *
  (hbytes Ews (m5_send M) (offset_val 32 m) -* @data_at W_keypairs Ews t_mk5 (hk5_mk_val M nx) m).
Proof.
  intros L. assert_PROP (@field_compatible W_keypairs t_mk5 [] m) as FC by entailer!.
  assert (FA: field_address t_mk5 (DOT KC._send) m = offset_val 32 m).
  { rewrite field_address_offset by auto with field_compatible. reflexivity. }
  rewrite (hkc5n_node_eq M nx m) at 1. rewrite FA, (hkc5n_hb Ews (m5_send M)) by exact L.
  rewrite (sepcon_comm (hbytes _ _ _) (_ -* _)).
  cancel. rewrite <- wand_sepcon_adjoint.
  rewrite (hkc5n_node_eq M nx m). rewrite FA, (hkc5n_hb Ews (m5_send M)) by exact L. cancel.
Qed.

Lemma hkc5n_focus_node_recv M nx m : Zlength (m5_recv M) = 32 ->
  @data_at W_keypairs Ews t_mk5 (hk5_mk_val M nx) m |--
  hbytes Ews (m5_recv M) (offset_val 64 m) *
  (hbytes Ews (m5_recv M) (offset_val 64 m) -* @data_at W_keypairs Ews t_mk5 (hk5_mk_val M nx) m).
Proof.
  intros L. assert_PROP (@field_compatible W_keypairs t_mk5 [] m) as FC by entailer!.
  assert (FA: field_address t_mk5 (DOT KC._recv) m = offset_val 64 m).
  { rewrite field_address_offset by auto with field_compatible. reflexivity. }
  rewrite (hkc5n_node_eq M nx m) at 1. rewrite FA, (hkc5n_hb Ews (m5_recv M)) by exact L.
  rewrite (sepcon_comm (hbytes _ _ _) (_ -* _)).
  cancel. rewrite <- wand_sepcon_adjoint.
  rewrite (hkc5n_node_eq M nx m). rewrite FA, (hkc5n_hb Ews (m5_recv M)) by exact L. cancel.
Qed.

Lemma hkc5n_focus_kp_send S k : Zlength (sk_key S) = 32 ->
  @field_at W_keypairs Ews t_kp (DOT KC._sending) (symkey_val S) k |--
  hbytes Ews (sk_key S) (offset_val 32 k) *
  (hbytes Ews (sk_key S) (offset_val 32 k) -* @field_at W_keypairs Ews t_kp (DOT KC._sending) (symkey_val S) k).
Proof.
  intros L. assert_PROP (@field_compatible W_keypairs t_kp (DOT KC._sending) k) as FC by entailer!.
  assert (FA: field_address t_kp [StructField KC._key; StructField KC._sending] k = offset_val 32 k).
  { rewrite field_address_offset by auto with field_compatible. reflexivity. }
  rewrite (hkc5n_sym_eq_send S k) at 1. rewrite FA, (hkc5n_hb Ews (sk_key S)) by exact L.
  rewrite (sepcon_comm (hbytes _ _ _) (_ -* _)).
  cancel. rewrite <- wand_sepcon_adjoint.
  rewrite (hkc5n_sym_eq_send S k). rewrite FA, (hkc5n_hb Ews (sk_key S)) by exact L. cancel.
Qed.

Lemma hkc5n_focus_kp_recv S k : Zlength (sk_key S) = 32 ->
  @field_at W_keypairs Ews t_kp (DOT KC._receiving) (symkey_val S) k |--
  hbytes Ews (sk_key S) (offset_val 88 k) *
  (hbytes Ews (sk_key S) (offset_val 88 k) -* @field_at W_keypairs Ews t_kp (DOT KC._receiving) (symkey_val S) k).
Proof.
  intros L. assert_PROP (@field_compatible W_keypairs t_kp (DOT KC._receiving) k) as FC by entailer!.
  assert (FA: field_address t_kp [StructField KC._key; StructField KC._receiving] k = offset_val 88 k).
  { rewrite field_address_offset by auto with field_compatible. reflexivity. }
  rewrite (hkc5n_sym_eq_recv S k) at 1. rewrite FA, (hkc5n_hb Ews (sk_key S)) by exact L.
  rewrite (sepcon_comm (hbytes _ _ _) (_ -* _)).
  cancel. rewrite <- wand_sepcon_adjoint.
  rewrite (hkc5n_sym_eq_recv S k). rewrite FA, (hkc5n_hb Ews (sk_key S)) by exact L. cancel.
Qed.

Lemma hkc5n_tc_bool b : tc_val tbool (Val.of_bool b).
Proof. destruct b; simpl; auto. Qed.

(* the peer's device field is at offset 0: p is a valid pointer *)
Lemma hkc5n_peer_valid shp p P : readable_share shp -> peer_rep shp p P |-- valid_pointer p.
Proof.
  intros Hsh. unfold peer_rep. apply derives_extract_prop; intros FC.
  repeat apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; [apply readable_nonidentity; auto | simpl; lia | reflexivity].
Qed.

Lemma hkc5n_peer_tc shp p P Q : readable_share shp -> Q * peer_rep shp p P |-- denote_tc_test_eq p p.
Proof.
  intros Hsh. apply denote_tc_test_eq_split; apply sepcon_valid_pointer2; apply hkc5n_peer_valid; auto.
Qed.

Lemma hkc5n_peer_ptr shp p P : peer_rep shp p P |-- !! isptr p.
Proof.
  unfold peer_rep. apply derives_extract_prop; intros FC. apply prop_right. destruct FC; auto.
Qed.

Lemma hkc5n_cmp_self p : isptr p -> Vint Int.zero = force_val (sem_cast_i2bool (force_val (sem_cmp_pp Cne p p))).
Proof.
  destruct p; try contradiction. intros _. unfold sem_cmp_pp; simpl.
  destruct (eq_block b b); [|congruence]. rewrite Ptrofs.eq_true. reflexivity.
Qed.

Lemma hkc5n_bytes_eqb_refl A : bytes_eqb A A = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec A A); congruence. Qed.

Lemma hkc5n_node_open_d M nx m :
  hk5_node m M nx |--
  !! (Zlength (m5_send M) = 32 /\ Zlength (m5_recv M) = 32) &&
  (@data_at W_keypairs Ews t_mk5 (hk5_mk_val M nx) m * @malloc_token W_keypairs Ews t_mk5 m).
Proof. unfold hk5_node. apply derives_refl. Qed.

Lemma hkc5n_node_close M nx m : Zlength (m5_send M) = 32 -> Zlength (m5_recv M) = 32 ->
  @data_at W_keypairs Ews t_mk5 (hk5_mk_val M nx) m * @malloc_token W_keypairs Ews t_mk5 m |-- hk5_node m M nx.
Proof. intros L1 L2. unfold hk5_node. apply andp_right; [apply prop_right; auto | apply derives_refl]. Qed.

Lemma hkc5n_cmpu64 x : Vint Int.zero = bool2val (Int64.cmpu Cne x x).
Proof. unfold Int64.cmpu. rewrite Int64.eq_true. reflexivity. Qed.

Lemma hkc5n_cmp32 x : Vint Int.zero = bool2val (negb (Int.eq x x)).
Proof. rewrite Int.eq_true. reflexivity. Qed.
