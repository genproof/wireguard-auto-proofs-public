(* body of setup_device (v4 spec), closes hc4_body_setup_device *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require Import WgNoise.proof.harness.common4.hc4a_nb_cs.
Require WgNoise.harness.x_cookie_mac.code WgNoise.harness.x_consume_initiation_any.code WgNoise.harness.x_keypairs.code
        WgNoise.harness.x_handshake.code WgNoise.harness.x_consume_response_any.code
        WgNoise.harness.x_handshake_receive.code.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.

Module FH := WgNoise.harness.x_handshake.code.
Require WgNoise.noise.code.
Module N := WgNoise.noise.code.

(* byte arrays across compspecs (copies of libc_bytes.v's lemmas, not loaded here) *)
Lemma hc4nb2_hs_setup_field_compatible_cs {cs1 cs2: compspecs}: forall n p,
  @field_compatible cs1 (tarray tuchar n) nil p <-> @field_compatible cs2 (tarray tuchar n) nil p.
Proof.
  assert (A: forall (ce: composite_env) n z, align_compatible_rec ce (tarray tuchar n) z).
  { intros. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  intros. unfold field_compatible, size_compatible, align_compatible.
  destruct p; simpl; try tauto.
  pose proof (A (@cenv_cs cs1) n (Ptrofs.unsigned i)).
  pose proof (A (@cenv_cs cs2) n (Ptrofs.unsigned i)).
  tauto.
Qed.

Lemma hc4nb2_hs_setup_data_at_cs {cs1 cs2: compspecs}: forall sh n (v: list val) p,
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  intros. unfold data_at, field_at.
  f_equal. f_equal. apply prop_ext. apply hc4nb2_hs_setup_field_compatible_cs.
Qed.

Lemma hc4nb2_hs_setup_data_at__cs {cs1 cs2: compspecs}: forall sh n p,
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof.
  intros. unfold data_at_, field_at_. apply hc4nb2_hs_setup_data_at_cs.
Qed.

(* the protocol objects are stated at Noise.CS, the bodies run at CSknb (same kernel structs) *)
#[local] Instance hc4nb2_hs_setup_N_K : change_composite_env Noise.CS CSknb.
Proof. make_cs_preserve Noise.CS CSknb. Defined.
#[local] Instance hc4nb2_hs_setup_K_N : change_composite_env CSknb Noise.CS.
Proof. make_cs_preserve CSknb Noise.CS. Defined.

#[local] Existing Instance CSknb.

Local Open Scope logic.

(* struct wg_device at Noise.CS: its fields as the reps use them *)
Lemma hc4nb2_hs_setup_dev_split sh wg (dv pt it: val) (sv: @reptype Noise.CS t_sid) (cv: @reptype Noise.CS t_cc) :
  @field_compatible Noise.CS t_dev [] wg ->
  @data_at Noise.CS sh t_dev ((dv, (sv, (cv, (pt, it)))) : @reptype Noise.CS t_dev) wg =
  @field_at Noise.CS sh t_dev (DOT FH._dev) dv wg * @data_at Noise.CS sh t_sid sv (id_addr wg) *
  @data_at Noise.CS sh t_cc cv (cc_addr wg) * @field_at Noise.CS sh t_dev (DOT FH._peer_hashtable) pt wg *
  @field_at Noise.CS sh t_dev (DOT FH._index_hashtable) it wg.
Proof.
  intros FC.
  unfold_data_at (@data_at Noise.CS _ _ _ wg).
  rewrite (@field_at_data_at Noise.CS _ _ (DOT FH._static_identity)), (@field_at_data_at Noise.CS _ _ (DOT FH._cookie_checker)).
  rewrite !(@field_address_offset Noise.CS) by auto with field_compatible.
  change (@nested_field_offset Noise.CS t_dev (DOT FH._static_identity)) with 8.
  change (@nested_field_offset Noise.CS t_dev (DOT FH._cookie_checker)) with 80.
  unfold id_addr, cc_addr, OFS_DEV_IDENTITY, OFS_DEV_CHECKER. rewrite !sepcon_assoc. reflexivity.
Qed.

(* struct noise_static_identity: the two arrays, the lock, has_identity and the padding *)
Lemma hc4nb2_hs_setup_sid_split sh a (pub priv: list val) (lk hv: val) :
  @field_compatible Noise.CS t_sid [] a ->
  @data_at Noise.CS sh t_sid ((pub, (priv, (lk, hv))) : @reptype Noise.CS t_sid) a =
  @data_at Noise.CS sh (tarray tuchar 32) pub a * @data_at Noise.CS sh (tarray tuchar 32) priv (offset_val 32 a) *
  @field_at Noise.CS sh t_sid (DOT FH._lock) lk a * @field_at Noise.CS sh t_sid (DOT FH._has_identity) hv a *
  spacer sh 69 72 a.
Proof.
  intros FC.
  unfold_data_at (@data_at Noise.CS _ _ _ a).
  rewrite (@field_at_data_at Noise.CS _ _ (DOT FH._static_public)), (@field_at_data_at Noise.CS _ _ (DOT FH._static_private)).
  rewrite !(@field_address_offset Noise.CS) by auto with field_compatible.
  change (@nested_field_offset Noise.CS t_sid (DOT FH._static_public)) with 0.
  change (@nested_field_offset Noise.CS t_sid (DOT FH._static_private)) with 32.
  assert (isptr a) by (destruct FC; auto). rewrite isptr_offset_val_zero by auto.
  rewrite !sepcon_assoc. reflexivity.
Qed.

(* struct cookie_checker: its fields and the padding after secret_lock *)
Lemma hc4nb2_hs_setup_cc_split sh c (sec ek mk: list val) (b lk d: val) :
  @field_compatible Noise.CS t_cc [] c ->
  @data_at Noise.CS sh t_cc ((sec, (ek, (mk, (b, (lk, d))))) : @reptype Noise.CS t_cc) c =
  @field_at Noise.CS sh t_cc (DOT FH._secret) sec c * @field_at Noise.CS sh t_cc (DOT FH._cookie_encryption_key) ek c *
  @field_at Noise.CS sh t_cc (DOT FH._message_mac1_key) mk c * @field_at Noise.CS sh t_cc (DOT FH._secret_birthdate) b c *
  @field_at Noise.CS sh t_cc (DOT FH._secret_lock) lk c * spacer sh 108 112 c *
  @field_at Noise.CS sh t_cc (DOT FH._device) d c.
Proof.
  intros FC.
  unfold_data_at (@data_at Noise.CS _ _ _ c).
  rewrite !sepcon_assoc. reflexivity.
Qed.

(* wg_cookie_checker_init_spec's PRE lacks the checker's padding (spacer 108..112, fixed in the
   protocol's round 3) while its POST checker_rep owns it: the caller's copy of the padding conflicts with it *)
Lemma hc4nb2_hs_setup_spacer_dup sh c CC :
  writable_share sh -> spacer sh 108 112 c * checker_rep sh c CC |-- FF.
Proof.
  intros W. unfold checker_rep. Intros lk.
  assert_PROP (@field_compatible Noise.CS t_cc [] c) by entailer!.
  rewrite hc4nb2_hs_setup_cc_split by auto.
  unfold spacer. simpl. unfold at_offset.
  sep_apply (memory_block_conflict sh 4 4 (offset_val 108 c)).
  { apply sepalg.nonidentity_nonunit. apply readable_nonidentity. auto. }
  { split; [lia | vm_compute; congruence]. }
  rewrite FF_sepcon. auto.
Qed.

Lemma hc4nb2_hs_setup_cc_split_ sh c :
  @field_compatible Noise.CS t_cc [] c ->
  @data_at_ Noise.CS sh t_cc c =
  @field_at_ Noise.CS sh t_cc (DOT FH._secret) c * @field_at_ Noise.CS sh t_cc (DOT FH._cookie_encryption_key) c *
  @field_at_ Noise.CS sh t_cc (DOT FH._message_mac1_key) c * @field_at_ Noise.CS sh t_cc (DOT FH._secret_birthdate) c *
  @field_at_ Noise.CS sh t_cc (DOT FH._secret_lock) c * spacer sh 108 112 c *
  @field_at_ Noise.CS sh t_cc (DOT FH._device) c.
Proof.
  intros FC. unfold data_at_, field_at_. apply hc4nb2_hs_setup_cc_split. auto.
Qed.

(* the key arrays of the checker as byte buffers *)
Lemma hc4nb2_hs_setup_cc_ek sh c (v: list val) :
  @field_compatible Noise.CS t_cc [] c ->
  @field_at Noise.CS sh t_cc (DOT FH._cookie_encryption_key) v c =
  @data_at Noise.CS sh (tarray tuchar 32) v (offset_val 32 c).
Proof.
  intros FC. rewrite (@field_at_data_at Noise.CS). rewrite (@field_address_offset Noise.CS) by auto with field_compatible.
  reflexivity.
Qed.

Lemma hc4nb2_hs_setup_cc_mk sh c (v: list val) :
  @field_compatible Noise.CS t_cc [] c ->
  @field_at Noise.CS sh t_cc (DOT FH._message_mac1_key) v c =
  @data_at Noise.CS sh (tarray tuchar 32) v (offset_val 64 c).
Proof.
  intros FC. rewrite (@field_at_data_at Noise.CS). rewrite (@field_address_offset Noise.CS) by auto with field_compatible.
  reflexivity.
Qed.

Lemma hc4nb2_hs_setup_mk_identity sh a (lk: val) :
  @field_compatible Noise.CS t_sid [] a ->
  hbytes sh (Zrepeat Byte.zero 32) a * hbytes sh (Zrepeat Byte.zero 32) (offset_val 32 a) *
  @field_at Noise.CS sh t_sid (DOT FH._lock) lk a * @field_at Noise.CS sh t_sid (DOT FH._has_identity) (Vint Int.zero) a *
  spacer sh 69 72 a |-- identity_rep sh a (mkId zeros32 zeros32 false).
Proof.
  intros FC. unfold identity_rep, hbytes. Exists lk.
  rewrite (hc4nb2_hs_setup_sid_split sh a) by auto.
  rewrite !(@hc4nb2_hs_setup_data_at_cs HCS Noise.CS).
  entailer!. split; reflexivity.
Qed.

Lemma hc4nb2_hs_setup_spacer_dup_dev sh wg D :
  writable_share sh -> spacer sh 108 112 (cc_addr wg) * device_rep sh wg D |-- FF.
Proof.
  intros W. unfold device_rep. Intros.
  sep_apply (hc4nb2_hs_setup_spacer_dup sh (cc_addr wg) (d_cc D) W).
  rewrite !FF_sepcon. auto.
Qed.

Lemma hc4nb2_hs_setup_to_hout sh (v: list val) p :
  v = Zrepeat Vundef 32 -> @data_at Noise.CS sh (tarray tuchar 32) v p = hout sh 32 p.
Proof. intros ->. unfold hout. apply (@hc4nb2_hs_setup_data_at__cs Noise.CS HCS). Qed.

Lemma hc4nb2_hs_setup_of_hbytes sh p :
  hbytes sh (Zrepeat Byte.zero 32) p = @data_at Noise.CS sh (tarray tuchar 32) (bytes zeros32) p.
Proof. unfold hbytes. apply (@hc4nb2_hs_setup_data_at_cs HCS Noise.CS). Qed.

Lemma hc4nb2_hs_setup_body :
  forall x25519, @semax_body [] (hc4_G_setup_device x25519) CSknb WgNoise.harness.x_handshake.code.f_setup_device (setup_device4_spec x25519).
Proof.
  intros x25519.
  start_function.
  assert_PROP (@field_compatible Noise.CS t_dev [] wg) as FC by entailer!.
  rewrite (@data_at__change_composite Noise.CS CSknb _ sh t_dev) by reflexivity.
  rewrite (@data_at__change_composite Noise.CS CSknb _ sh t_itab) by reflexivity.
  rewrite (@data_at__change_composite Noise.CS CSknb _ sh t_ptab) by reflexivity.
  do 6 forward.
  erewrite (@data_at_change_composite CSknb Noise.CS _ sh t_dev _ _ (JMeq_refl _)) by reflexivity.
  rewrite hc4nb2_hs_setup_dev_split by auto. repeat flatten_sepcon_in_SEP.
  assert_PROP (@field_compatible Noise.CS t_sid [] (id_addr wg) /\ @field_compatible Noise.CS t_cc [] (cc_addr wg))
    as FCsc by entailer!.
  destruct FCsc as [FCs FCc].
  rewrite hc4nb2_hs_setup_sid_split by auto.
  change (@data_at Noise.CS sh t_cc (fst (snd (snd (@default_val CSknb t_dev)))) (cc_addr wg))
    with (@data_at_ Noise.CS sh t_cc (cc_addr wg)).
  rewrite hc4nb2_hs_setup_cc_split_ by auto. repeat flatten_sepcon_in_SEP.
  unfold field_at_ at 2 3.
  rewrite hc4nb2_hs_setup_cc_ek, hc4nb2_hs_setup_cc_mk by auto.
  rewrite !hc4nb2_hs_setup_to_hout by reflexivity.
  forward_call (sh, id_addr wg, Byte.zero, 32).
  { destruct FC; auto. }
  forward_call (sh, offset_val 32 (id_addr wg), Byte.zero, 32).
  all: try (destruct FC; auto; fail).
  forward_call (sh, offset_val 32 (cc_addr wg), Byte.zero, 32).
  all: try (destruct FC; auto; fail).
  forward_call (sh, offset_val 64 (cc_addr wg), Byte.zero, 32).
  all: try (destruct FC; auto; fail).
  sep_apply (hc4nb2_hs_setup_mk_identity sh (id_addr wg)).
  replace (hbytes shr RAW r) with (bytes_at shr RAW r) by (unfold hbytes, bytes_at; apply hc4nb2_hs_setup_data_at_cs).
  forward_call (gv, sh, id_addr wg, mkId zeros32 zeros32 false, shr, r, RAW).
  { destruct FC; auto. }
  rewrite !hc4nb2_hs_setup_of_hbytes.
  rewrite <- (hc4nb2_hs_setup_cc_ek sh (cc_addr wg)) by auto.
  rewrite <- (hc4nb2_hs_setup_cc_mk sh (cc_addr wg)) by auto.
  forward_call (gv, S, w, sh, cc_addr wg, zeros32, zeros32, wg).
  { destruct FC; auto. }
  { change N._secret with FH._secret. change N._secret_birthdate with FH._secret_birthdate.
    change N._secret_lock with FH._secret_lock. change N._device with FH._device. cancel. }
  Intros sec.
  replace (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval by reflexivity.
  forward_call (gv, sh, wg, mkDev nullval (setup_identity x25519 RAW) (mkChk sec zeros32 zeros32 (s_boot S) wg) ptab itab).
  { destruct FC; auto. }
  { unfold device_rep, setup_identity. entailer!. }
  Exists sec.
  (* the checker's padding is held twice (see hc4nb2_hs_setup_spacer_dup): contradiction.  With the
     round-3 wg_cookie_checker_init_spec (PRE += spacer sh 108 112 c) the padding goes into the call and the
     tail is (tested):
       unfold itable, ptable, itable_wf. cbn [t_L t_D hd VST.msl.iter_sepcon.iter_sepcon].
       rewrite prop_true_andp by (repeat split; try constructor; intros ? ?; contradiction).
       rewrite (@data_at_change_composite CSknb Noise.CS _ sh t_itab nullval nullval (JMeq_refl _)) by reflexivity.
       rewrite (@data_at_change_composite CSknb Noise.CS _ sh t_ptab nullval nullval (JMeq_refl _)) by reflexivity.
       replace (bytes_at shr RAW r) with (hbytes shr RAW r) by (unfold hbytes, bytes_at; apply hc4nb2_hs_setup_data_at_cs).
       unfold setup_dev, dev_set_cc, checker_set_keys. cbn [d_dev d_id d_cc d_ptab d_itab cc_secret cc_birth cc_dev].
       entailer!. *)
  unfold itable, ptable, itable_wf. cbn [t_L t_D hd VST.msl.iter_sepcon.iter_sepcon].
  rewrite prop_true_andp by (repeat split; try constructor; intros ? ?; contradiction).
  rewrite (@data_at_change_composite CSknb Noise.CS _ sh t_itab nullval nullval (JMeq_refl _)) by reflexivity.
  rewrite (@data_at_change_composite CSknb Noise.CS _ sh t_ptab nullval nullval (JMeq_refl _)) by reflexivity.
  replace (bytes_at shr RAW r) with (hbytes shr RAW r) by (unfold hbytes, bytes_at; apply hc4nb2_hs_setup_data_at_cs).
  unfold setup_dev, dev_set_cc, checker_set_keys. cbn [d_dev d_id d_cc d_ptab d_itab cc_secret cc_birth cc_dev].
  entailer!.
Qed.
