(* (common4 group kents, kents_snap): helpers at CS4 *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require Import WgNoise.proof.harness.common4.hc4b_ke_hf.
Require Import WgNoise.proof.harness.common4.hc4b_ke_hf2.
Require WgNoise.harness.x_cookie_mac.code.
Local Open Scope logic.

Section ArrCs.
Context {cs1 cs2: compspecs}.
Lemma hc4b_ke_snap_fc_cs n p :
  @field_compatible cs1 (tarray tuchar n) [] p <-> @field_compatible cs2 (tarray tuchar n) [] p.
Proof.
  unfold field_compatible. simpl. split; intros (? & ? & ? & ? & ?); repeat split; auto;
  unfold align_compatible in *; destruct p; auto;
  (eapply align_compatible_rec_Tarray; intros; eapply align_compatible_rec_Tarray_inv in H2; eauto;
   inv H2; econstructor; eauto).
Qed.
Lemma hc4b_ke_snap_data_at_cs sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext. apply hc4b_ke_snap_fc_cs.
Qed.
End ArrCs.

Section S.
Variable CSw: compspecs.
#[local] Existing Instance CS4.

#[local] Instance hc4b_ke_snap_cce1 : change_composite_env CKS CS4.
Proof. make_cs_preserve CKS CS4. Defined.
#[local] Instance hc4b_ke_snap_cce2 : change_composite_env Noise.CS CS4.
Proof. make_cs_preserve Noise.CS CS4. Defined.

(* the keypair body at CS4, the symmetric keys split (key as a byte buffer) *)
Definition hc4b_ke_snap_ss (k: val) (S: symkey) : mpred :=
  hbytes Ews (sk_key S) (field_address t_kp [StructField I._key; StructField I._sending] k) *
  field_at Ews t_kp [StructField I._birthdate; StructField I._sending] (Vlong (sk_birth S)) k *
  field_at Ews t_kp [StructField I._is_valid; StructField I._sending] (Val.of_bool (sk_valid S)) k *
  spacer Ews 73 80 k.
Definition hc4b_ke_snap_rs (k: val) (S: symkey) : mpred :=
  hbytes Ews (sk_key S) (field_address t_kp [StructField I._key; StructField I._receiving] k) *
  field_at Ews t_kp [StructField I._birthdate; StructField I._receiving] (Vlong (sk_birth S)) k *
  field_at Ews t_kp [StructField I._is_valid; StructField I._receiving] (Val.of_bool (sk_valid S)) k *
  spacer Ews 129 136 k.

Definition hc4b_ke_snap_kpo (k: val) (K: keypair) (lk r: val) : mpred :=
  hc4b_ke_snap_ss k (kp_send K) *
  field_at Ews t_kp [StructField I._sending_counter] (Vlong (kp_scounter K)) k *
  hc4b_ke_snap_rs k (kp_recv K) *
  field_at Ews t_kp [StructField I._receiving_counter] (Vlong (kp_rcounter K), (lk, map Vlong (kp_backtrack K))) k *
  field_at Ews t_kp [StructField I._remote_index] (Vint (kp_rindex K)) k *
  field_at Ews t_kp [StructField I._i_am_the_initiator] (Val.of_bool (kp_init K)) k *
  field_at Ews t_kp [StructField I._refcount] (Vint (kp_refs K)) k *
  field_at Ews t_kp [StructField I._rcu] r k *
  field_at Ews t_kp [StructField I._internal_id] (Vlong (kp_id K)) k *
  spacer Ews 1181 1184 k.

Ltac hc4b_ke_snap_cs :=
  repeat match goal with |- context [@field_at Noise.CS ?sh ?t ?gfs ?v ?p] =>
    rewrite (@field_at_change_composite Noise.CS CS4 _ sh t gfs v v (JMeq_refl v)) by reflexivity end.

Lemma hc4b_ke_snap_ss_eq k S :
  Zlength (sk_key S) = 32 ->
  @field_at Noise.CS Ews t_kp [StructField I._sending] (symkey_val S) k = hc4b_ke_snap_ss k S.
Proof.
  intros L. unfold_field_at 1%nat. unfold symkey_val; simpl fst; simpl snd. hc4b_ke_snap_cs.
  unfold hc4b_ke_snap_ss, hbytes.
  rewrite L. rewrite <- (@hc4b_ke_snap_data_at_cs CS4 HCS).
  rewrite (field_at_data_at Ews t_kp [StructField I._key; StructField I._sending]).
  change (nested_field_type t_kp [StructField I._key; StructField I._sending]) with (tarray tuchar 32).
  rewrite !sepcon_assoc. reflexivity.
Qed.
Lemma hc4b_ke_snap_rs_eq k S :
  Zlength (sk_key S) = 32 ->
  @field_at Noise.CS Ews t_kp [StructField I._receiving] (symkey_val S) k = hc4b_ke_snap_rs k S.
Proof.
  intros L. unfold_field_at 1%nat. unfold symkey_val; simpl fst; simpl snd. hc4b_ke_snap_cs.
  unfold hc4b_ke_snap_rs, hbytes.
  rewrite L. rewrite <- (@hc4b_ke_snap_data_at_cs CS4 HCS).
  rewrite (field_at_data_at Ews t_kp [StructField I._key; StructField I._receiving]).
  change (nested_field_type t_kp [StructField I._key; StructField I._receiving]) with (tarray tuchar 32).
  rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma hc4b_ke_snap_kp_open k K :
  kp_body_rep k K |-- EX lk: val, EX r: val,
    !! (@field_compatible Noise.CS t_kp [] k /\ kp_ok K) && hc4b_ke_snap_kpo k K lk r.
Proof.
  unfold kp_body_rep. Intros lk r. Exists r lk.
  pose proof H0 as (L1 & L2 & L3).
  rewrite hc4b_ke_snap_ss_eq by auto.
  rewrite hc4b_ke_snap_rs_eq by auto. hc4b_ke_snap_cs.
  unfold hc4b_ke_snap_kpo. entailer!.
Qed.

Lemma hc4b_ke_snap_kp_close k K lk r :
  @field_compatible Noise.CS t_kp [] k -> kp_ok K ->
  hc4b_ke_snap_kpo k K lk r |-- kp_body_rep k K.
Proof.
  intros FC KO. unfold kp_body_rep. apply andp_right; [apply prop_right; auto|].
  Exists r. Exists lk.
  pose proof KO as (L1 & L2 & L3).
  rewrite hc4b_ke_snap_ss_eq by auto.
  rewrite hc4b_ke_snap_rs_eq by auto. hc4b_ke_snap_cs.
  unfold hc4b_ke_snap_kpo. cancel.
Qed.

(* the snapshot fields at CS4: any contents (blank) and taken (full); the keys as byte buffers *)
Definition hc4b_ke_snap_blank (k: val) : mpred :=
  field_at_ Ews t_kent [StructField HC._peer0] k *
  field_at_ Ews t_kent [StructField HC._next0] k *
  field_at_ Ews t_kent [StructField HC._type0] k *
  field_at_ Ews t_kent [StructField HC._index0] k *
  field_at_ Ews t_kent [StructField HC._hashed0] k *
  hout Ews 32 (field_address t_kent [StructField HC._skey0] k) *
  hout Ews 32 (field_address t_kent [StructField HC._rkey0] k) *
  field_at_ Ews t_kent [StructField HC._sbirth0] k *
  field_at_ Ews t_kent [StructField HC._rbirth0] k *
  field_at_ Ews t_kent [StructField HC._svalid0] k *
  field_at_ Ews t_kent [StructField HC._rvalid0] k *
  field_at_ Ews t_kent [StructField HC._scnt0] k *
  field_at_ Ews t_kent [StructField HC._rcnt0] k *
  field_at_ Ews t_kent [StructField HC._bt0] k *
  field_at_ Ews t_kent [StructField HC._remote_index0] k *
  field_at_ Ews t_kent [StructField HC._initiator0] k *
  field_at_ Ews t_kent [StructField HC._refs0] k *
  field_at_ Ews t_kent [StructField HC._id0] k.

Definition hc4b_ke_snap_full (k: val) (E: entry) (nx: val) (h: bool) (K: keypair) : mpred :=
  field_at Ews t_kent [StructField HC._peer0] (e_peer E) k *
  field_at Ews t_kent [StructField HC._next0] nx k *
  field_at Ews t_kent [StructField HC._type0] (Vint (e_type E)) k *
  field_at Ews t_kent [StructField HC._index0] (Vint (e_index E)) k *
  field_at Ews t_kent [StructField HC._hashed0] (Val.of_bool h) k *
  hbytes Ews (sk_key (kp_send K)) (field_address t_kent [StructField HC._skey0] k) *
  hbytes Ews (sk_key (kp_recv K)) (field_address t_kent [StructField HC._rkey0] k) *
  field_at Ews t_kent [StructField HC._sbirth0] (Vlong (sk_birth (kp_send K))) k *
  field_at Ews t_kent [StructField HC._rbirth0] (Vlong (sk_birth (kp_recv K))) k *
  field_at Ews t_kent [StructField HC._svalid0] (Val.of_bool (sk_valid (kp_send K))) k *
  field_at Ews t_kent [StructField HC._rvalid0] (Val.of_bool (sk_valid (kp_recv K))) k *
  field_at Ews t_kent [StructField HC._scnt0] (Vlong (kp_scounter K)) k *
  field_at Ews t_kent [StructField HC._rcnt0] (Vlong (kp_rcounter K)) k *
  field_at Ews t_kent [StructField HC._bt0] (map Vlong (kp_backtrack K)) k *
  field_at Ews t_kent [StructField HC._remote_index0] (Vint (kp_rindex K)) k *
  field_at Ews t_kent [StructField HC._initiator0] (Val.of_bool (kp_init K)) k *
  field_at Ews t_kent [StructField HC._refs0] (Vint (kp_refs K)) k *
  field_at Ews t_kent [StructField HC._id0] (Vlong (kp_id K)) k.

Ltac hc4b_ke_snap_cks :=
  repeat match goal with
  | |- context [@field_at CKS ?sh ?t ?gfs ?v ?p] =>
    rewrite (@field_at_change_composite CKS CS4 _ sh t gfs v v (JMeq_refl v)) by reflexivity
  | |- context [@field_at_ CKS ?sh ?t ?gfs ?p] =>
    rewrite (@field_at__change_composite CKS CS4 _ sh t gfs) by reflexivity
  end.

Lemma hc4b_ke_snap_hout_eq sh n x :
  @data_at CS4 sh (tarray tuchar n) (Zrepeat Vundef n) x = hout sh n x.
Proof. unfold hout, data_at_, field_at_. apply hc4b_ke_snap_data_at_cs. Qed.

Lemma hc4b_ke_snap_fa_hout f k :
  f = HC._skey0 \/ f = HC._rkey0 ->
  field_at_ Ews t_kent [StructField f] k = hout Ews 32 (field_address t_kent [StructField f] k).
Proof.
  intros [-> | ->]; rewrite <- hc4b_ke_snap_hout_eq; unfold field_at_; rewrite field_at_data_at; reflexivity.
Qed.

Lemma hc4b_ke_snap_hb_skey0 k A :
  Zlength A = 32 ->
  hbytes Ews A (field_address t_kent [StructField HC._skey0] k) = field_at Ews t_kent [StructField HC._skey0] (bytes A) k.
Proof.
  intros L; unfold hbytes; rewrite L, <- (@hc4b_ke_snap_data_at_cs CS4 HCS), field_at_data_at; reflexivity.
Qed.
Lemma hc4b_ke_snap_hb_rkey0 k A :
  Zlength A = 32 ->
  hbytes Ews A (field_address t_kent [StructField HC._rkey0] k) = field_at Ews t_kent [StructField HC._rkey0] (bytes A) k.
Proof.
  intros L; unfold hbytes; rewrite L, <- (@hc4b_ke_snap_data_at_cs CS4 HCS), field_at_data_at; reflexivity.
Qed.

Lemma hc4b_ke_snap_blank_of k o : kent_snap_rep k o |-- hc4b_ke_snap_blank k.
Proof.
  unfold hc4b_ke_snap_blank.
  rewrite <- (hc4b_ke_snap_fa_hout HC._skey0), <- (hc4b_ke_snap_fa_hout HC._rkey0) by auto.
  destruct o as [s|]; unfold kent_snap_rep; hc4b_ke_snap_cks.
  - cbv zeta. repeat (apply sepcon_derives; [|apply field_at_field_at_]). apply field_at_field_at_.
  - apply derives_refl.
Qed.

Lemma hc4b_ke_snap_full_eq k E nx h K :
  Zlength (sk_key (kp_send K)) = 32 -> Zlength (sk_key (kp_recv K)) = 32 ->
  hc4b_ke_snap_full k E nx h K = kent_snap_rep k (Some (mkKs E nx h K)).
Proof.
  intros L1 L2. unfold hc4b_ke_snap_full, kent_snap_rep. cbv zeta. simpl ks_E; simpl ks_K; simpl ks_next; simpl ks_hashed.
  hc4b_ke_snap_cks.
  rewrite hc4b_ke_snap_hb_skey0, hc4b_ke_snap_hb_rkey0 by auto.
  reflexivity.
Qed.

(* the entry of the kent's keypair, as the keypair's field (kp = &l->kp is l) *)
Lemma hc4b_ke_snap_entry sh l E nx h :
  @field_compatible CS4 t_kent [] l ->
  entry_at sh l E nx h = @field_at CS4 sh t_kp [StructField I._entry] (entry_val E nx h) l.
Proof.
  intros FC. unfold entry_at. rewrite (@field_at_data_at CS4).
  assert (FC1: @field_compatible CS4 t_kp [] l).
  { assert (FC2: @field_compatible CS4 t_kent [StructField HC._kp] l) by auto with field_compatible.
    apply field_compatible_nested_field in FC2. simpl in FC2.
    rewrite isptr_offset_val_zero in FC2 by (destruct FC; auto). exact FC2. }
  rewrite (@field_address_offset CS4) by auto with field_compatible.
  assert (Hp: isptr l) by (destruct FC; auto).
  change (@nested_field_offset CS4 t_kp [StructField I._entry]) with 0.
  rewrite isptr_offset_val_zero by auto.
  exact (f_equal (fun f => f l)
    (@data_at_change_composite Noise.CS CS4 _ sh t_entry_s (entry_val E nx h) (entry_val E nx h) (JMeq_refl _) eq_refl)).
Qed.

End S.
