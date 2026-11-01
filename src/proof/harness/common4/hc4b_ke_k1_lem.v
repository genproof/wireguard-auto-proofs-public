(* (common4 group kents): helpers of the body of kent_same_but_next (hc4b_ke_k1.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require Import WgNoise.proof.harness.common4.hc4b_ke_hf.
Require Import WgNoise.proof.harness.common4.hc4b_ke_hf2.
Require Import WgNoise.proof.harness.common4.hc4b_ke_k1_vp.
Require WgNoise.harness.x_cookie_mac.code.
Local Open Scope logic.

Section K1.
Variable CSw: compspecs.
#[local] Existing Instance CS4.

#[local] Instance hc4b_ke_k1_cce1 : change_composite_env CKS CS4.
Proof. make_cs_preserve CKS CS4. Defined.
#[local] Instance hc4b_ke_k1_cce2 : change_composite_env Noise.CS CS4.
Proof. make_cs_preserve Noise.CS CS4. Defined.

(* the entry of a kent's keypair as the keypair's field *)
Lemma hc4b_ke_k1_entry sh l E nx h :
  @field_compatible CS4 t_kp [] l ->
  entry_at sh l E nx h = @field_at CS4 sh t_kp (DOT I._entry) (entry_val E nx h) l.
Proof.
  intros FC. unfold entry_at. rewrite (@field_at_data_at CS4).
  rewrite (@field_address_offset CS4) by auto with field_compatible.
  assert (Hp: isptr l) by (destruct FC; auto).
  change (@nested_field_offset CS4 t_kp (DOT I._entry)) with 0.
  rewrite isptr_offset_val_zero by auto.
  exact (f_equal (fun f => f l)
    (@data_at_change_composite Noise.CS CS4 _ sh t_entry_s (entry_val E nx h) (entry_val E nx h) (JMeq_refl _) eq_refl)).
Qed.

(* byte arrays do not depend on the compspecs *)
Lemma hc4b_ke_k1_arr_cs {cs1 cs2: compspecs}: forall sh n (v: list val) p,
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

Ltac hc4b_ke_k1_cc :=
  repeat match goal with
  | |- context [@field_at Noise.CS ?sh ?t ?gfs ?v ?p] =>
      rewrite (f_equal (fun f => f p) (@field_at_change_composite Noise.CS CS4 hc4b_ke_k1_cce2 sh t gfs v v (JMeq_refl v) eq_refl))
  | |- context [@field_at CKS ?sh ?t ?gfs ?v ?p] =>
      rewrite (f_equal (fun f => f p) (@field_at_change_composite CKS CS4 hc4b_ke_k1_cce1 sh t gfs v v (JMeq_refl v) eq_refl))
  end.

(* the kent and the table, opened: the entry and the keypair's fields at CS4, the snapshot fields at CS4 *)
Definition hc4b_ke_k1_kp (k: val) (K: keypair) (lk r: val) : mpred :=
  field_at Ews t_kp (DOT I._sending) (symkey_val (kp_send K)) k *
  field_at Ews t_kp (DOT I._sending_counter) (Vlong (kp_scounter K)) k *
  field_at Ews t_kp (DOT I._receiving) (symkey_val (kp_recv K)) k *
  field_at Ews t_kp (DOT I._receiving_counter) (Vlong (kp_rcounter K), (lk, map Vlong (kp_backtrack K))) k *
  field_at Ews t_kp (DOT I._remote_index) (Vint (kp_rindex K)) k *
  field_at Ews t_kp (DOT I._i_am_the_initiator) (Val.of_bool (kp_init K)) k *
  field_at Ews t_kp (DOT I._refcount) (Vint (kp_refs K)) k *
  field_at Ews t_kp (DOT I._rcu) r k *
  field_at Ews t_kp (DOT I._internal_id) (Vlong (kp_id K)) k *
  spacer Ews 1181 1184 k.

Definition hc4b_ke_k1_sn (k: val) (s: ksnap) : mpred :=
  let E := ks_E s in let K := ks_K s in
  field_at Ews t_kent (DOT HC._peer0) (e_peer E) k *
  field_at Ews t_kent (DOT HC._next0) (ks_next s) k *
  field_at Ews t_kent (DOT HC._type0) (Vint (e_type E)) k *
  field_at Ews t_kent (DOT HC._index0) (Vint (e_index E)) k *
  field_at Ews t_kent (DOT HC._hashed0) (Val.of_bool (ks_hashed s)) k *
  field_at Ews t_kent (DOT HC._skey0) (bytes (sk_key (kp_send K))) k *
  field_at Ews t_kent (DOT HC._rkey0) (bytes (sk_key (kp_recv K))) k *
  field_at Ews t_kent (DOT HC._sbirth0) (Vlong (sk_birth (kp_send K))) k *
  field_at Ews t_kent (DOT HC._rbirth0) (Vlong (sk_birth (kp_recv K))) k *
  field_at Ews t_kent (DOT HC._svalid0) (Val.of_bool (sk_valid (kp_send K))) k *
  field_at Ews t_kent (DOT HC._rvalid0) (Val.of_bool (sk_valid (kp_recv K))) k *
  field_at Ews t_kent (DOT HC._scnt0) (Vlong (kp_scounter K)) k *
  field_at Ews t_kent (DOT HC._rcnt0) (Vlong (kp_rcounter K)) k *
  field_at Ews t_kent (DOT HC._bt0) (map Vlong (kp_backtrack K)) k *
  field_at Ews t_kent (DOT HC._remote_index0) (Vint (kp_rindex K)) k *
  field_at Ews t_kent (DOT HC._initiator0) (Val.of_bool (kp_init K)) k *
  field_at Ews t_kent (DOT HC._refs0) (Vint (kp_refs K)) k *
  field_at Ews t_kent (DOT HC._id0) (Vlong (kp_id K)) k.

(* the frame: token, list link, padding *)
Definition hc4b_ke_k1_fr (k nx: val) : mpred :=
  @malloc_token CSw Ews t_kent k * @field_at CKS Ews t_kent [StructField HC._next] nx k * kent_pads k.

Lemma hc4b_ke_k1_kp_eq k K :
  kp_body_rep k K =
  !! (@field_compatible Noise.CS t_kp [] k /\ kp_ok K) && EX lk: val, EX r: val, hc4b_ke_k1_kp k K lk r.
Proof.
  unfold kp_body_rep, hc4b_ke_k1_kp. hc4b_ke_k1_cc.
  apply pred_ext.
  - Intros lk r. Exists r lk. hc4b_ke_k1_cc. entailer!.
  - Intros lk r. Exists r lk. hc4b_ke_k1_cc. entailer!.
Qed.

Lemma hc4b_ke_k1_sn_eq k s : kent_snap_rep k (Some s) = hc4b_ke_k1_sn k s.
Proof. unfold kent_snap_rep, hc4b_ke_k1_sn. hc4b_ke_k1_cc. reflexivity. Qed.

(* the key of a symmetric key of the keypair, lent to bytes_eq *)
Lemma hc4b_ke_k1_key_s sh k Ks :
  Zlength (sk_key Ks) = 32 -> @field_compatible CS4 t_kp [] k ->
  @field_at CS4 sh t_kp (DOT I._sending) (symkey_val Ks) k |--
  hbytes sh (sk_key Ks) (field_address t_kp [StructField I._key; StructField I._sending] k) *
  (hbytes sh (sk_key Ks) (field_address t_kp [StructField I._key; StructField I._sending] k) -*
   @field_at CS4 sh t_kp (DOT I._sending) (symkey_val Ks) k).
Proof.
  intros L FC.
  eapply derives_trans.
  { apply (@gfield_ramif CS4 sh t_kp (DOT I._sending) (StructField I._key) (symkey_val Ks) (bytes (sk_key Ks)) k).
    - apply JMeq_refl.
    - auto with field_compatible. }
  rewrite (@field_at_data_at CS4 sh t_kp [StructField I._key; StructField I._sending]).
  unfold hbytes. rewrite L. simpl nested_field_type.
  apply sepcon_derives.
  { erewrite hc4b_ke_k1_arr_cs. apply derives_refl. }
  apply (allp_left _ (bytes (sk_key Ks))).
  apply wand_derives.
  { rewrite (@field_at_data_at CS4 sh t_kp [StructField I._key; StructField I._sending]). simpl nested_field_type.
    erewrite hc4b_ke_k1_arr_cs. apply derives_refl. }
  apply derives_refl.
Qed.

Lemma hc4b_ke_k1_key_r sh k Ks :
  Zlength (sk_key Ks) = 32 -> @field_compatible CS4 t_kp [] k ->
  @field_at CS4 sh t_kp (DOT I._receiving) (symkey_val Ks) k |--
  hbytes sh (sk_key Ks) (field_address t_kp [StructField I._key; StructField I._receiving] k) *
  (hbytes sh (sk_key Ks) (field_address t_kp [StructField I._key; StructField I._receiving] k) -*
   @field_at CS4 sh t_kp (DOT I._receiving) (symkey_val Ks) k).
Proof.
  intros L FC.
  eapply derives_trans.
  { apply (@gfield_ramif CS4 sh t_kp (DOT I._receiving) (StructField I._key) (symkey_val Ks) (bytes (sk_key Ks)) k).
    - apply JMeq_refl.
    - auto with field_compatible. }
  rewrite (@field_at_data_at CS4 sh t_kp [StructField I._key; StructField I._receiving]).
  unfold hbytes. rewrite L. simpl nested_field_type.
  apply sepcon_derives.
  { erewrite hc4b_ke_k1_arr_cs. apply derives_refl. }
  apply (allp_left _ (bytes (sk_key Ks))).
  apply wand_derives.
  { rewrite (@field_at_data_at CS4 sh t_kp [StructField I._key; StructField I._receiving]). simpl nested_field_type.
    erewrite hc4b_ke_k1_arr_cs. apply derives_refl. }
  apply derives_refl.
Qed.

(* the snapshot's key fields as byte buffers *)
Lemma hc4b_ke_k1_sn_skey0 sh k (A: list byte) :
  Zlength A = 32 ->
  @field_at CS4 sh t_kent (DOT HC._skey0) (bytes A) k = hbytes sh A (field_address t_kent (DOT HC._skey0) k).
Proof.
  intros L. rewrite (@field_at_data_at CS4). unfold hbytes. rewrite L. simpl nested_field_type.
  apply hc4b_ke_k1_arr_cs.
Qed.

Lemma hc4b_ke_k1_sn_rkey0 sh k (A: list byte) :
  Zlength A = 32 ->
  @field_at CS4 sh t_kent (DOT HC._rkey0) (bytes A) k = hbytes sh A (field_address t_kent (DOT HC._rkey0) k).
Proof.
  intros L. rewrite (@field_at_data_at CS4). unfold hbytes. rewrite L. simpl nested_field_type.
  apply hc4b_ke_k1_arr_cs.
Qed.

(* opening the kent and the table's pool item at it *)
Definition hc4b_ke_k1_ent (sh: share) (T: tstate) (k: val) (E: entry) : mpred :=
  @field_at CS4 sh t_kp (DOT I._entry) (entry_val E (succ_in (t_L T) k) (vin k (t_L T))) k.

Lemma hc4b_ke_k1_open sht tab T k K s nx sh E :
  itable_wf T -> sfind (t_D T) k = Some (sh, E) ->
  kent_cell CSw (mkKe k K (Some s)) nx * itable sht tab T |--
  EX lk: val, EX r: val,
    !! (@field_compatible CS4 t_kp [] k /\ @field_compatible Noise.CS t_kp [] k /\ kp_ok K /\
        @field_compatible CKS t_kent [] k) &&
    (hc4b_ke_k1_ent sh T k E * hc4b_ke_hf2_irest sht tab T k * hc4b_ke_k1_kp k K lk r * hc4b_ke_k1_sn k s *
     hc4b_ke_k1_fr k nx).
Proof.
  intros W F. rewrite (hc4b_ke_hf2_take sht tab T k sh E W F).
  unfold kent_cell. cbn [ke_addr ke_K ke_snap]. rewrite hc4b_ke_k1_kp_eq, hc4b_ke_k1_sn_eq. Intros lk r. Exists lk r.
  assert (FC4: @field_compatible CS4 t_kp [] k)
    by (apply (@field_compatible_change_composite Noise.CS CS4 _ t_kp); [reflexivity | auto]).
  unfold hc4b_ke_k1_ent. rewrite <- hc4b_ke_k1_entry by auto. unfold hc4b_ke_k1_fr. entailer!.
Qed.

Lemma hc4b_ke_k1_close sht tab T k K s nx sh E lk r :
  itable_wf T -> sfind (t_D T) k = Some (sh, E) ->
  @field_compatible CS4 t_kp [] k -> @field_compatible Noise.CS t_kp [] k -> kp_ok K ->
  @field_compatible CKS t_kent [] k ->
  hc4b_ke_k1_ent sh T k E * hc4b_ke_hf2_irest sht tab T k * hc4b_ke_k1_kp k K lk r * hc4b_ke_k1_sn k s *
  hc4b_ke_k1_fr k nx |--
  kent_cell CSw (mkKe k K (Some s)) nx * itable sht tab T.
Proof.
  intros W F FC4 FCn OK FCk. rewrite (hc4b_ke_hf2_take sht tab T k sh E W F).
  unfold kent_cell. cbn [ke_addr ke_K ke_snap]. rewrite hc4b_ke_k1_kp_eq, hc4b_ke_k1_sn_eq.
  unfold hc4b_ke_k1_ent. rewrite <- hc4b_ke_k1_entry by auto. unfold hc4b_ke_k1_fr.
  Exists lk r. entailer!.
Qed.

(* the compared pointers are valid: NULL, a pool entry or a lent object *)
Lemma hc4b_ke_k1_vp sht tab T k sh E VO x R :
  Forall vobj_ok VO -> (x = nullval \/ In x (saddrs (t_D T)) \/ In x (hc4b_ke_k1_vobjs_vaddrs VO)) ->
  itable_wf T -> sfind (t_D T) k = Some (sh, E) -> @field_compatible CS4 t_kp [] k ->
  hc4b_ke_k1_ent sh T k E * hc4b_ke_hf2_irest sht tab T k * vobjs CSw VO * R |-- valid_pointer x.
Proof.
  intros HF Hx W F FC. destruct Hx as [-> | [Hin | Hin]].
  - apply valid_pointer_null.
  - unfold hc4b_ke_k1_ent. rewrite <- hc4b_ke_k1_entry by auto.
    rewrite <- (hc4b_ke_hf2_take sht tab T k sh E W F).
    eapply derives_trans; [| apply (hc4b_ke_hf2_valid (vobjs CSw VO * R) sht tab T x Hin)].
    cancel.
  - eapply derives_trans; [| apply (hc4b_ke_k1_vp_vobjs CSw VO x (hc4b_ke_k1_ent sh T k E * hc4b_ke_hf2_irest sht tab T k * R) HF Hin)].
    cancel.
Qed.

End K1.
