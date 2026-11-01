
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_body3_shim_table1.
Local Open Scope logic.

#[local] Existing Instance Noise.CS.

(* ---- the keypair list ---- *)
Section KS.
Context {A: Type}.
Lemma prot3_noise_kp_afind_in (KS: list (val * A)) k :
  In k (map fst KS) -> exists K, afind KS k = Some K.
Proof.
  induction KS as [|[x w] KS IH]; simpl; intros H; [contradiction|].
  destruct (EqDec_val x k); [eauto|]. destruct H; [congruence|auto].
Qed.

Lemma prot3_noise_kp_split (KS: list (val * A)) k K (f: val * A -> mpred) :
  afind KS k = Some K -> iter_sepcon f KS = f (k, K) * iter_sepcon f (adel KS k).
Proof.
  induction KS as [|[x w] KS IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x k); [inv H; reflexivity|].
  rewrite (IH H); simpl. rewrite <- !sepcon_assoc, (sepcon_comm (f _) (f _)). reflexivity.
Qed.

Lemma prot3_noise_kp_upd (KS: list (val * A)) k K K' (f: val * A -> mpred) :
  afind KS k = Some K -> iter_sepcon f (aupd KS k K') = f (k, K') * iter_sepcon f (adel KS k).
Proof.
  induction KS as [|[x w] KS IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x k); [inv H; reflexivity|].
  simpl. rewrite (IH H). rewrite <- !sepcon_assoc, (sepcon_comm (f _) (f _)). reflexivity.
Qed.
End KS.

(* ---- the pool: a keypair entry is in it ---- *)
Lemma prot3_noise_kp_inpool T p KS k :
  kps_in_pool T p KS -> In k (map fst KS) ->
  exists E, sfind (t_D T) k = Some (Ews, E) /\ e_peer E = p.
Proof.
  intros [_ HF] Hk. apply list_in_map_inv in Hk. destruct Hk as [[x K] [? Hin]]. simpl in H; subst.
  rewrite Forall_forall in HF. apply (HF _ Hin).
Qed.

Lemma prot3_noise_kp_sfind_saddrs {A: Type} (D: list (val * share * A)) a sh E :
  sfind D a = Some (sh, E) -> In a (saddrs D).
Proof.
  intros H. apply prot3_shim_table1_sfind_In in H. eapply prot3_shim_table1_saddrs_in; eauto.
Qed.

Lemma prot3_noise_kp_saddrs_sdel {A: Type} (D: list (val * share * A)) a x :
  In x (saddrs D) -> x <> a -> In x (saddrs (sdel D a)).
Proof.
  induction D as [|[[y shy] w] D IH]; simpl; intros H Hne; [contradiction|].
  destruct (EqDec_val y a).
  - subst. destruct H; [congruence|auto].
  - simpl. destruct H; [auto|right; auto].
Qed.

(* an unhashed entry leaves the pool *)
Lemma prot3_noise_kp_pool_free sht tab T a sh E :
  sfind (t_D T) a = Some (sh, E) -> ~ In a (t_L T) ->
  itable sht tab T |-- itable sht tab (t_free T a) * entry_out sh a E.
Proof.
  intros HE HL. unfold itable. Intros.
  rewrite (prot3_shim_table1_split _ _ _ _ _ HE).
  unfold t_free; simpl. rewrite (prot3_shim_table1_vremove_notin _ _ HL).
  unfold pool_item_rep at 1, entry_out.
  rewrite (prot3_shim_table1_succ_notin _ _ HL).
  replace (vin a (t_L T)) with false.
  2:{ unfold vin. destruct (in_dec eq_dec a (t_L T)); [contradiction|reflexivity]. }
  destruct H as (H1 & H2 & H3 & H4).
  apply andp_right.
  - apply prop_right. unfold itable_wf; simpl. split; [auto|split; [|split]].
    + intros x Hx. apply prot3_noise_kp_saddrs_sdel; [auto|]. intro; subst; contradiction.
    + apply prot3_shim_table1_sdel_nodup; auto.
    + rewrite Forall_forall in *. intros [[x shx] w] Hin. apply (H4 (x, shx, w)).
      eapply prot3_shim_table1_sdel_in; eauto.
  - unfold pool_item_rep. cancel.
Qed.

(* the whole keypair: its fields, its entry (out of the pool) and its padding *)
Lemma prot3_noise_kp_whole CSw k K E :
  keypair_rep CSw k K * entry_out Ews k E |--
  @malloc_token CSw Ews (tarray tuchar SIZEOF_KEYPAIR) k * @data_at_ Noise.CS Ews (tarray tuchar SIZEOF_KEYPAIR) k.
Proof.
  unfold keypair_rep, entry_out, entry_at. Intros lk r. cancel.
  eapply derives_trans with (@data_at_ Noise.CS Ews t_kp k).
  2:{ rewrite data_at__memory_block by auto. Intros. unfold SIZEOF_KEYPAIR.
      change (@sizeof Noise.CS t_kp) with 1200. rewrite (@memory_block_data_at__tarray_tuchar_eq Noise.CS) by (simpl; rep_lia). auto. }
  assert (FE: data_at Ews t_entry_s (entry_val E nullval false) k |-- @field_at_ Noise.CS Ews t_kp (DOT I._entry) k).
  { unfold field_at_. rewrite field_at_data_at. rewrite field_address_offset by auto with field_compatible. simpl.
    assert (isptr k) by (destruct H; auto). rewrite isptr_offset_val_zero by auto. apply data_at_data_at_. }
  sep_apply FE.
  unfold_data_at (@data_at_ Noise.CS Ews t_kp k).
  repeat match goal with |- _ |-- ?R => match R with context [@field_at Noise.CS Ews t_kp ?g ?v k] =>
    change (@field_at Noise.CS Ews t_kp g v k) with (@field_at_ Noise.CS Ews t_kp g k) end end.
  repeat match goal with |- context [@field_at Noise.CS Ews t_kp ?g ?v k] =>
    sep_apply (@field_at_field_at_ Noise.CS Ews t_kp g v k) end.
  cancel.
Qed.

(* the entry of a keypair (or any struct with the entry at offset 0) in the pool, as a field of the keypair *)
Definition prot3_noise_kp_irest (sht: share) (tab: val) (T: tstate) (a: val) : mpred :=
  !! itable_wf T &&
  (data_at sht t_itab (hd nullval (t_L T)) tab * iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) a)).

Lemma prot3_noise_kp_open sht tab T k sh E :
  field_compatible t_kp [] k -> sfind (t_D T) k = Some (sh, E) ->
  itable sht tab T =
  field_at sh t_kp (DOT I._entry) (entry_val E (succ_in (t_L T) k) (vin k (t_L T))) k *
  prot3_noise_kp_irest sht tab T k.
Proof.
  intros FC HE. unfold itable, prot3_noise_kp_irest. rewrite (prot3_shim_table1_split _ _ _ _ _ HE).
  unfold pool_item_rep at 1, entry_at.
  rewrite field_at_data_at. rewrite field_address_offset by auto with field_compatible. simpl.
  rewrite isptr_offset_val_zero by (destruct FC; auto).
  apply pred_ext; entailer!.
Qed.

Section KRest.
Variable CSw: compspecs.
#[local] Existing Instance Noise.CS.

(* a keypair without its reference count (independent of kp_refs) *)
Definition prot3_noise_kp_krest (k: val) (K: keypair) : mpred :=
  !! (field_compatible t_kp [] k /\ kp_ok K) &&
  (@malloc_token CSw Ews (tarray tuchar SIZEOF_KEYPAIR) k *
   field_at Ews t_kp [StructField I._sending] (symkey_val (kp_send K)) k *
   field_at Ews t_kp [StructField I._sending_counter] (Vlong (kp_scounter K)) k *
   field_at Ews t_kp [StructField I._receiving] (symkey_val (kp_recv K)) k *
   (EX lk: val, field_at Ews t_kp [StructField I._receiving_counter]
                   (Vlong (kp_rcounter K), (lk, map Vlong (kp_backtrack K))) k) *
   field_at Ews t_kp [StructField I._remote_index] (Vint (kp_rindex K)) k *
   field_at Ews t_kp [StructField I._i_am_the_initiator] (Val.of_bool (kp_init K)) k *
   (EX r: val, field_at Ews t_kp [StructField I._rcu] r k) *
   field_at Ews t_kp [StructField I._internal_id] (Vlong (kp_id K)) k *
   spacer Ews 1181 1184 k).

Lemma prot3_noise_kp_rc_split k K :
  keypair_rep CSw k K =
  field_at Ews t_kp (DOT I._refcount) (Vint (kp_refs K)) k * prot3_noise_kp_krest k K.
Proof.
  unfold keypair_rep, prot3_noise_kp_krest. apply pred_ext; Intros lk r; Exists lk r; entailer!.
Qed.

Lemma prot3_noise_kp_krest_refs k K r :
  prot3_noise_kp_krest k (kp_set_refs K r) = prot3_noise_kp_krest k K.
Proof. reflexivity. Qed.

Lemma prot3_noise_kp_krest_fc k K :
  prot3_noise_kp_krest k K |-- !! field_compatible t_kp [] k.
Proof. unfold prot3_noise_kp_krest. entailer!. Qed.

End KRest.
