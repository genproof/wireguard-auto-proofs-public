(* hc_pieces3, group setup: common.h bodies, proved once at a small compspecs with the callee context
   of hc3_ctx.v.  One lemma per function (per law where the Clight
   reads a renamed constant). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.blake2s.b2s_spec3.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common.hc3_ctx.
Require WgNoise.harness.x_handshake.code WgNoise.harness.x_cookie_reply.code WgNoise.harness.x_consume_response_any.code
        WgNoise.harness.x_keypairs.code WgNoise.harness.x_create_any.code WgNoise.harness.x_replay.code
        WgNoise.harness.x_cookie_mac.code WgNoise.harness.x_consume_initiation_any.code.
Require WgNoise.contracts.x_cookie_reply.

Module FH := WgNoise.harness.x_handshake.code.
Module FK := WgNoise.harness.x_cookie_reply.code.
Module FR := WgNoise.harness.x_consume_response_any.code.

(* byte arrays across compspecs (copies of libc_bytes.v's lemmas, not loaded here) *)
Lemma hc3b_setup_field_compatible_cs {cs1 cs2: compspecs}: forall n p,
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

Lemma hc3b_setup_data_at_cs {cs1 cs2: compspecs}: forall sh n (v: list val) p,
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  intros. unfold data_at, field_at.
  f_equal. f_equal. apply prop_ext. apply hc3b_setup_field_compatible_cs.
Qed.

Lemma hc3b_setup_data_at__cs {cs1 cs2: compspecs}: forall sh n p,
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof.
  intros. unfold data_at_, field_at_. apply hc3b_setup_data_at_cs.
Qed.

(* the protocol objects are stated at Noise.CS, the bodies run at CSk (same kernel structs) *)
#[local] Instance hc3b_setup_N_K : change_composite_env Noise.CS CSk.
Proof. make_cs_preserve Noise.CS CSk. Defined.
#[local] Instance hc3b_setup_K_N : change_composite_env CSk Noise.CS.
Proof. make_cs_preserve CSk Noise.CS. Defined.

(* every lemma takes all the section variables and hypotheses (a stable signature for the assembly) *)
#[local] Set Default Proof Using "All".

Section Bodies.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Hypothesis X25519: x25519_props x25519.
Hypothesis AEAD: aead_props aead_enc aead_dec.
Hypothesis XAEAD: xaead_props xaead_enc xaead_dec.

#[local] Existing Instance CSk.

Local Open Scope logic.

(* struct wg_device at Noise.CS: its fields as the reps use them *)
Lemma hc3b_setup_dev_split sh wg (dv pt it: val) (sv: @reptype Noise.CS t_sid) (cv: @reptype Noise.CS t_cc) :
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
Lemma hc3b_setup_sid_split sh a (pub priv: list val) (lk hv: val) :
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
Lemma hc3b_setup_cc_split sh c (sec ek mk: list val) (b lk d: val) :
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
Lemma hc3b_setup_spacer_dup sh c CC :
  writable_share sh -> spacer sh 108 112 c * checker_rep sh c CC |-- FF.
Proof.
  intros W. unfold checker_rep. Intros lk.
  assert_PROP (@field_compatible Noise.CS t_cc [] c) by entailer!.
  rewrite hc3b_setup_cc_split by auto.
  unfold spacer. simpl. unfold at_offset.
  sep_apply (memory_block_conflict sh 4 4 (offset_val 108 c)).
  { apply sepalg.nonidentity_nonunit. apply readable_nonidentity. auto. }
  { split; [lia | vm_compute; congruence]. }
  rewrite FF_sepcon. auto.
Qed.

Lemma hc3b_setup_cc_split_ sh c :
  @field_compatible Noise.CS t_cc [] c ->
  @data_at_ Noise.CS sh t_cc c =
  @field_at_ Noise.CS sh t_cc (DOT FH._secret) c * @field_at_ Noise.CS sh t_cc (DOT FH._cookie_encryption_key) c *
  @field_at_ Noise.CS sh t_cc (DOT FH._message_mac1_key) c * @field_at_ Noise.CS sh t_cc (DOT FH._secret_birthdate) c *
  @field_at_ Noise.CS sh t_cc (DOT FH._secret_lock) c * spacer sh 108 112 c *
  @field_at_ Noise.CS sh t_cc (DOT FH._device) c.
Proof.
  intros FC. unfold data_at_, field_at_. apply hc3b_setup_cc_split. auto.
Qed.

(* the key arrays of the checker as byte buffers *)
Lemma hc3b_setup_cc_ek sh c (v: list val) :
  @field_compatible Noise.CS t_cc [] c ->
  @field_at Noise.CS sh t_cc (DOT FH._cookie_encryption_key) v c =
  @data_at Noise.CS sh (tarray tuchar 32) v (offset_val 32 c).
Proof.
  intros FC. rewrite (@field_at_data_at Noise.CS). rewrite (@field_address_offset Noise.CS) by auto with field_compatible.
  reflexivity.
Qed.

Lemma hc3b_setup_cc_mk sh c (v: list val) :
  @field_compatible Noise.CS t_cc [] c ->
  @field_at Noise.CS sh t_cc (DOT FH._message_mac1_key) v c =
  @data_at Noise.CS sh (tarray tuchar 32) v (offset_val 64 c).
Proof.
  intros FC. rewrite (@field_at_data_at Noise.CS). rewrite (@field_address_offset Noise.CS) by auto with field_compatible.
  reflexivity.
Qed.

Lemma hc3b_setup_mk_identity sh a (lk: val) :
  @field_compatible Noise.CS t_sid [] a ->
  hbytes sh (Zrepeat Byte.zero 32) a * hbytes sh (Zrepeat Byte.zero 32) (offset_val 32 a) *
  @field_at Noise.CS sh t_sid (DOT FH._lock) lk a * @field_at Noise.CS sh t_sid (DOT FH._has_identity) (Vint Int.zero) a *
  spacer sh 69 72 a |-- identity_rep sh a (mkId zeros32 zeros32 false).
Proof.
  intros FC. unfold identity_rep, hbytes. Exists lk.
  rewrite (hc3b_setup_sid_split sh a) by auto.
  rewrite !(@hc3b_setup_data_at_cs HCS Noise.CS).
  entailer!. split; reflexivity.
Qed.

Lemma hc3b_setup_spacer_dup_dev sh wg D :
  writable_share sh -> spacer sh 108 112 (cc_addr wg) * device_rep sh wg D |-- FF.
Proof.
  intros W. unfold device_rep. Intros.
  sep_apply (hc3b_setup_spacer_dup sh (cc_addr wg) (d_cc D) W).
  rewrite !FF_sepcon. auto.
Qed.

Lemma hc3b_setup_to_hout sh (v: list val) p :
  v = Zrepeat Vundef 32 -> @data_at Noise.CS sh (tarray tuchar 32) v p = hout sh 32 p.
Proof. intros ->. unfold hout. apply (@hc3b_setup_data_at__cs Noise.CS HCS). Qed.

Lemma hc3b_setup_of_hbytes sh p :
  hbytes sh (Zrepeat Byte.zero 32) p = @data_at Noise.CS sh (tarray tuchar 32) (bytes zeros32) p.
Proof. unfold hbytes. apply (@hc3b_setup_data_at_cs HCS Noise.CS). Qed.

Lemma hc3_body_setup_device :
  @semax_body [] (hc3_G_setup_device x25519) CSk FH.f_setup_device (setup_device_spec x25519).
Proof.
  start_function.
  assert_PROP (@field_compatible Noise.CS t_dev [] wg) as FC by entailer!.
  rewrite (@data_at__change_composite Noise.CS CSk _ sh t_dev) by reflexivity.
  rewrite (@data_at__change_composite Noise.CS CSk _ sh t_itab) by reflexivity.
  rewrite (@data_at__change_composite Noise.CS CSk _ sh t_ptab) by reflexivity.
  do 6 forward.
  erewrite (@data_at_change_composite CSk Noise.CS _ sh t_dev _ _ (JMeq_refl _)) by reflexivity.
  rewrite hc3b_setup_dev_split by auto. repeat flatten_sepcon_in_SEP.
  assert_PROP (@field_compatible Noise.CS t_sid [] (id_addr wg) /\ @field_compatible Noise.CS t_cc [] (cc_addr wg))
    as FCsc by entailer!.
  destruct FCsc as [FCs FCc].
  rewrite hc3b_setup_sid_split by auto.
  change (@data_at Noise.CS sh t_cc (fst (snd (snd (@default_val CSk t_dev)))) (cc_addr wg))
    with (@data_at_ Noise.CS sh t_cc (cc_addr wg)).
  rewrite hc3b_setup_cc_split_ by auto. repeat flatten_sepcon_in_SEP.
  unfold field_at_ at 2 3.
  rewrite hc3b_setup_cc_ek, hc3b_setup_cc_mk by auto.
  rewrite !hc3b_setup_to_hout by reflexivity.
  forward_call (sh, id_addr wg, Byte.zero, 32).
  { destruct FC; auto. }
  forward_call (sh, offset_val 32 (id_addr wg), Byte.zero, 32).
  all: try (destruct FC; auto; fail).
  forward_call (sh, offset_val 32 (cc_addr wg), Byte.zero, 32).
  all: try (destruct FC; auto; fail).
  forward_call (sh, offset_val 64 (cc_addr wg), Byte.zero, 32).
  all: try (destruct FC; auto; fail).
  sep_apply (hc3b_setup_mk_identity sh (id_addr wg)).
  replace (hbytes shr RAW r) with (bytes_at shr RAW r) by (unfold hbytes, bytes_at; apply hc3b_setup_data_at_cs).
  forward_call (gv, sh, id_addr wg, mkId zeros32 zeros32 false, shr, r, RAW).
  { destruct FC; auto. }
  rewrite !hc3b_setup_of_hbytes.
  rewrite <- (hc3b_setup_cc_ek sh (cc_addr wg)) by auto.
  rewrite <- (hc3b_setup_cc_mk sh (cc_addr wg)) by auto.
  forward_call (gv, S, sh, cc_addr wg, zeros32, zeros32, wg).
  { destruct FC; auto. }
  { change N._secret with FH._secret. change N._secret_birthdate with FH._secret_birthdate.
    change N._secret_lock with FH._secret_lock. change N._device with FH._device. cancel. }
  Intros sec.
  replace (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval by reflexivity.
  forward_call (gv, sh, wg, mkDev nullval (setup_identity x25519 RAW) (mkChk sec zeros32 zeros32 (s_boot S) wg) ptab itab).
  { destruct FC; auto. }
  { unfold device_rep, setup_identity. entailer!. }
  Exists sec.
  (* the checker's padding is held twice (see hc3b_setup_spacer_dup): contradiction.  With the
     round-3 wg_cookie_checker_init_spec (PRE += spacer sh 108 112 c) the padding goes into the call and the
     tail is (tested):
       unfold itable, ptable, itable_wf. cbn [t_L t_D hd VST.msl.iter_sepcon.iter_sepcon].
       rewrite prop_true_andp by (repeat split; try constructor; intros ? ?; contradiction).
       rewrite (@data_at_change_composite CSk Noise.CS _ sh t_itab nullval nullval (JMeq_refl _)) by reflexivity.
       rewrite (@data_at_change_composite CSk Noise.CS _ sh t_ptab nullval nullval (JMeq_refl _)) by reflexivity.
       replace (bytes_at shr RAW r) with (hbytes shr RAW r) by (unfold hbytes, bytes_at; apply hc3b_setup_data_at_cs).
       unfold setup_dev, dev_set_cc, checker_set_keys. cbn [d_dev d_id d_cc d_ptab d_itab cc_secret cc_birth cc_dev].
       entailer!. *)
  unfold itable, ptable, itable_wf. cbn [t_L t_D hd VST.msl.iter_sepcon.iter_sepcon].
  rewrite prop_true_andp by (repeat split; try constructor; intros ? ?; contradiction).
  rewrite (@data_at_change_composite CSk Noise.CS _ sh t_itab nullval nullval (JMeq_refl _)) by reflexivity.
  rewrite (@data_at_change_composite CSk Noise.CS _ sh t_ptab nullval nullval (JMeq_refl _)) by reflexivity.
  replace (bytes_at shr RAW r) with (hbytes shr RAW r) by (unfold hbytes, bytes_at; apply hc3b_setup_data_at_cs).
  unfold setup_dev, dev_set_cc, checker_set_keys. cbn [d_dev d_id d_cc d_ptab d_itab cc_secret cc_birth cc_dev].
  entailer!.
Qed.

(* setup_peer: struct wg_peer at Noise.CS cut into the pieces the stores and the callees use *)
Definition hc3b_setup_peer_hsrest (sh: share) (h: val) : mpred :=
  (@field_at_ Noise.CS sh t_hs (DOT FH._state) h * spacer sh 36 40 h *
  @field_at_ Noise.CS sh t_hs (DOT FH._last_initiation_consumption) h *
  @field_at_ Noise.CS sh t_hs (DOT FH._static_identity) h *
  @field_at_ Noise.CS sh t_hs (DOT FH._ephemeral_private) h *
  @field_at_ Noise.CS sh t_hs (DOT FH._remote_static) h *
  @field_at_ Noise.CS sh t_hs (DOT FH._remote_ephemeral) h *
  @field_at_ Noise.CS sh t_hs (DOT FH._precomputed_static_static) h *
  @field_at_ Noise.CS sh t_hs (DOT FH._preshared_key) h *
  @field_at_ Noise.CS sh t_hs (DOT FH._hash) h *
  @field_at_ Noise.CS sh t_hs (DOT FH._chaining_key) h *
  @field_at_ Noise.CS sh t_hs (DOT FH._latest_timestamp) h *
  @field_at_ Noise.CS sh t_hs (DOT FH._remote_index) h *
  @field_at_ Noise.CS sh t_hs (DOT FH._lock) h * spacer sh 300 304 h)%logic.

Lemma hc3b_setup_peer_hs_split sh h :
  @data_at_ Noise.CS sh t_hs h = (@field_at_ Noise.CS sh t_hs (DOT FH._entry) h * hc3b_setup_peer_hsrest sh h)%logic.
Proof.
  change (@data_at_ Noise.CS sh t_hs h) with (@data_at Noise.CS sh t_hs (@default_val Noise.CS t_hs) h).
  unfold_data_at (@data_at Noise.CS sh t_hs _ h).
  unfold hc3b_setup_peer_hsrest, field_at_. rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma hc3b_setup_peer_entry_hs sh h v :
  @field_compatible Noise.CS t_hs [] h ->
  @field_at Noise.CS sh t_hs (DOT FH._entry) v h = @data_at Noise.CS sh t_entry_s v h.
Proof.
  intros FC. rewrite (@field_at_data_at Noise.CS). rewrite (@field_address_offset Noise.CS) by auto with field_compatible.
  change (@nested_field_offset Noise.CS t_hs (DOT FH._entry)) with 0.
  assert (isptr h) by (destruct FC; auto). rewrite isptr_offset_val_zero by auto. reflexivity.
Qed.

Lemma hc3b_setup_peer_entry_peer sh p v :
  @field_compatible Noise.CS t_peer [] p ->
  @field_at Noise.CS sh t_peer (DOT FH._handshake DOT FH._entry) v p = @data_at Noise.CS sh t_entry_s v (hs_addr p).
Proof.
  intros FC. rewrite (@field_at_data_at Noise.CS). rewrite (@field_address_offset Noise.CS) by auto with field_compatible.
  reflexivity.
Qed.

Lemma hc3b_setup_peer_kps sh p v :
  @field_compatible Noise.CS t_peer [] p ->
  @field_at Noise.CS sh t_peer (DOT FH._keypairs) v p = @data_at Noise.CS sh t_kps v (kps_addr p).
Proof.
  intros FC. rewrite (@field_at_data_at Noise.CS). rewrite (@field_address_offset Noise.CS) by auto with field_compatible.
  reflexivity.
Qed.

Lemma hc3b_setup_peer_hs sh p :
  @field_compatible Noise.CS t_peer [] p ->
  @field_at_ Noise.CS sh t_peer (DOT FH._handshake) p = @data_at_ Noise.CS sh t_hs (hs_addr p).
Proof.
  intros FC. unfold field_at_. rewrite (@field_at_data_at Noise.CS).
  rewrite (@field_address_offset Noise.CS) by auto with field_compatible.
  reflexivity.
Qed.

Lemma hc3b_setup_peer_cookie sh p :
  @field_compatible Noise.CS t_peer [] p ->
  @field_at_ Noise.CS sh t_peer (DOT FH._latest_cookie) p = @data_at_ Noise.CS sh t_cookie (cookie_addr p).
Proof.
  intros FC. unfold field_at_. rewrite (@field_at_data_at Noise.CS).
  rewrite (@field_address_offset Noise.CS) by auto with field_compatible.
  reflexivity.
Qed.

Lemma hc3b_setup_peer_entry_cs sh p :
  @field_compatible Noise.CS t_peer [] p -> @field_compatible Noise.CS t_hs [] (hs_addr p) ->
  @field_at_ Noise.CS sh t_hs (DOT FH._entry) (hs_addr p) =
  @field_at_ CSk sh t_peer (DOT FH._handshake DOT FH._entry) p.
Proof.
  intros FCp FCh. unfold field_at_. rewrite hc3b_setup_peer_entry_hs by auto.
  rewrite <- (hc3b_setup_peer_entry_peer sh p _ FCp).
  change (@field_at Noise.CS sh t_peer (DOT FH._handshake DOT FH._entry)
            (@default_val Noise.CS (@nested_field_type Noise.CS t_hs (DOT FH._entry))) p)
    with (@field_at_ Noise.CS sh t_peer (DOT FH._handshake DOT FH._entry) p).
  exact (f_equal (fun f => f p) (@field_at__change_composite Noise.CS CSk _ sh t_peer (DOT FH._handshake DOT FH._entry) eq_refl)).
Qed.

Lemma hc3b_setup_peer_split sh p :
  @data_at_ Noise.CS sh t_peer p =
  (@field_at_ Noise.CS sh t_peer (DOT FH._device) p * @field_at_ Noise.CS sh t_peer (DOT FH._is_dead) p *
  spacer sh 9 16 p * @field_at_ Noise.CS sh t_peer (DOT FH._keypairs) p *
  @field_at_ Noise.CS sh t_peer (DOT FH._handshake) p *
  @field_at_ Noise.CS sh t_peer (DOT FH._last_sent_handshake) p *
  @field_at_ Noise.CS sh t_peer (DOT FH._latest_cookie) p *
  @field_at_ Noise.CS sh t_peer (DOT FH._refcount) p * spacer sh 476 480 p *
  @field_at_ Noise.CS sh t_peer (DOT FH._internal_id) p * @field_at_ Noise.CS sh t_peer (DOT FH._pubkey_next) p)%logic.
Proof.
  change (@data_at_ Noise.CS sh t_peer p) with (@data_at Noise.CS sh t_peer (@default_val Noise.CS t_peer) p).
  unfold_data_at (@data_at Noise.CS sh t_peer _ p).
  unfold field_at_. rewrite !sepcon_assoc. reflexivity.
Qed.

(* setup_peer_spec (hc_specs3.v) with the fact the body needs about the old head of the public-key table:
   `t'3 = wg->peer_hashtable->head` loads it into a temporary, and VST's load rule requires a defined value
   (tc_val), while ptable's data_at allows head = Vundef. The body is proved against this spec. *)
Definition hc3b_setup_peer_spec_fix :=
  DECLARE HH._setup_peer
  WITH gv: globals, shp: share, p: val, shd: share, wg: val, D: device, head: val,
       sh: share, pp: val, PUB: list byte, pk: val, PSK: list byte, id: int64
  PRE [ tptr t_peer, tptr t_dev, tptr tuchar, tptr tuchar, tulong ]
    PROP (writable_share shp; writable_share shd; readable_share sh; Zlength PUB = 32;
          pk <> nullval -> Zlength PSK = 32; is_pointer_or_null head)
    PARAMS (p; wg; pp; pk; Vlong id) GLOBALS (gv)
    SEP (@data_at_ Noise.CS shp t_peer p; device_rep shd wg D; ptable shd (d_ptab D) head;
         hbytes sh PUB pp; if eq_dec pk nullval then emp else hbytes sh PSK pk; wg_consts gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (peer_rep shp p (setup_peer_val x25519 D wg p head PUB (if eq_dec pk nullval then zeros32 else PSK) id);
         entry_out shp (hs_addr p) (mkEntry p IDX_HANDSHAKE Int.zero);
         device_rep shd wg D; ptable shd (d_ptab D) p;
         hbytes sh PUB pp; if eq_dec pk nullval then emp else hbytes sh PSK pk; wg_consts gv).

Lemma hc3b_setup_peer_body_fix :
  @semax_body [] (hc3_G_setup_peer x25519) CSk FH.f_setup_peer hc3b_setup_peer_spec_fix.
Proof.
  start_function.
  assert_PROP (@field_compatible Noise.CS t_peer [] p) as FCp by entailer!.
  rewrite hc3b_setup_peer_split, (hc3b_setup_peer_hs shp p FCp), (hc3b_setup_peer_cookie shp p FCp).
  assert_PROP (@field_compatible Noise.CS t_hs [] (hs_addr p)) as FCh by entailer!.
  rewrite hc3b_setup_peer_hs_split.
  rewrite (hc3b_setup_peer_entry_cs shp p FCp FCh).
  rewrite !(@field_at__change_composite Noise.CS CSk _ shp t_peer) by reflexivity.
  repeat flatten_sepcon_in_SEP.
  do 10 forward.
  sep_apply (field_at_field_at_ shp t_peer (DOT FH._handshake DOT FH._entry)).
  rewrite <- (hc3b_setup_peer_entry_cs shp p FCp FCh).
  sep_apply (derives_refl' _ _ (eq_sym (hc3b_setup_peer_hs_split shp (hs_addr p)))).
  unfold device_rep. Intros.
  replace (hbytes sh PUB pp) with (bytes_at sh PUB pp) by (unfold hbytes, bytes_at; apply hc3b_setup_data_at_cs).
  replace (if eq_dec pk nullval then emp else hbytes sh PSK pk)
    with (if eq_dec pk nullval then emp else bytes_at sh PSK pk)
    by (destruct (eq_dec pk nullval); [reflexivity | unfold hbytes, bytes_at; apply hc3b_setup_data_at_cs]).
  forward_call (gv, shp, p, shd, id_addr wg, d_id D, sh, pp, PUB, sh, pk, PSK).
  { match goal with F: field_compatible t_dev [] wg |- _ => destruct F; auto end. }
  forward_call (shp, cookie_addr p).
  forward_call (gv, shp, p, hs_initial x25519 (d_id D) (id_addr wg) PUB (if eq_dec pk nullval then zeros32 else PSK),
                cookie_zero).
  erewrite (@field_at_change_composite Noise.CS CSk _ shd t_dev (DOT I._peer_hashtable) _ _ (JMeq_refl _))
    by reflexivity.
  unfold ptable. erewrite (@data_at_change_composite Noise.CS CSk _ shd t_ptab _ _ (JMeq_refl _)) by reflexivity.
  change I._peer_hashtable with FH._peer_hashtable.
  do 5 forward.
  erewrite (@field_at_change_composite CSk Noise.CS _ shp t_peer (DOT FH._device) _ _ (JMeq_refl _)) by reflexivity.
  erewrite (@field_at_change_composite CSk Noise.CS _ shp t_peer (DOT FH._is_dead) _ _ (JMeq_refl _)) by reflexivity.
  erewrite (@field_at_change_composite CSk Noise.CS _ shp t_peer (DOT FH._keypairs) _ _ (JMeq_refl _)) by reflexivity.
  erewrite (@field_at_change_composite CSk Noise.CS _ shp t_peer (DOT FH._last_sent_handshake) _ _ (JMeq_refl _))
    by reflexivity.
  erewrite (@field_at_change_composite CSk Noise.CS _ shp t_peer (DOT FH._refcount) _ _ (JMeq_refl _)) by reflexivity.
  erewrite (@field_at_change_composite CSk Noise.CS _ shp t_peer (DOT FH._internal_id) _ _ (JMeq_refl _)) by reflexivity.
  erewrite (@field_at_change_composite CSk Noise.CS _ shp t_peer (DOT FH._pubkey_next) _ _ (JMeq_refl _)) by reflexivity.
  erewrite (@field_at_change_composite CSk Noise.CS _ shd t_dev (DOT FH._peer_hashtable) _ _ (JMeq_refl _))
    by reflexivity.
  erewrite (@data_at_change_composite CSk Noise.CS _ shd t_ptab _ _ (JMeq_refl _)) by reflexivity.
  rewrite (hc3b_setup_peer_kps shp p _ FCp).
  replace (bytes_at sh PUB pp) with (hbytes sh PUB pp) by (unfold hbytes, bytes_at; apply hc3b_setup_data_at_cs).
  replace (if eq_dec pk nullval then emp else bytes_at sh PSK pk)
    with (if eq_dec pk nullval then emp else hbytes sh PSK pk)
    by (destruct (eq_dec pk nullval); [reflexivity | unfold hbytes, bytes_at; apply hc3b_setup_data_at_cs]).
  unfold peer_rep, device_rep, kps_rep, ptable, setup_peer_val.
  cbn [p_device p_dead p_cur p_prev p_next p_hs p_lsh p_cookie p_refs p_id p_pknext hs_rstatic hs_initial].
  Exists (snd (snd (snd (@default_val CSk (nested_field_type t_peer (DOT FH._keypairs)))))).
  change I._device with FH._device; change I._is_dead with FH._is_dead;
    change I._last_sent_handshake with FH._last_sent_handshake; change I._refcount with FH._refcount;
    change I._internal_id with FH._internal_id; change I._pubkey_next with FH._pubkey_next;
    change I._peer_hashtable with FH._peer_hashtable.
  replace (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval by reflexivity.
  change (Val.of_bool false) with (Vint Int.zero). change (Vlong Int64.zero) with nullval.
  change (Vint Int.one) with (Vint (Int.repr 1)).
  entailer!.
Qed.

(* With the spec fixed this is
   `exact hc3b_setup_peer_body_fix`. *)
Lemma hc3_body_setup_peer :
  @semax_body [] (hc3_G_setup_peer x25519) CSk FH.f_setup_peer (setup_peer_spec x25519).
Proof.
  exact hc3b_setup_peer_body_fix.
Qed.

(* the group *)
Theorem hc3_bodies_setup :
  (@semax_body [] (hc3_G_setup_device x25519) CSk FH.f_setup_device (setup_device_spec x25519)) /\
  (@semax_body [] (hc3_G_setup_peer x25519) CSk FH.f_setup_peer (setup_peer_spec x25519)).
Proof.
  exact (conj hc3_body_setup_device hc3_body_setup_peer).
Qed.

End Bodies.
