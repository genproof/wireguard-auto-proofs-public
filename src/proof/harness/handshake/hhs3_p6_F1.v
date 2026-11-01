(* law handshake, phase P6, segment F1 = blk 21..26: CHECK(rb), kb = next, the CHECKs of slots, role, remote index, keys, validity.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.handshake.hhs3_spec.
Require Import WgNoise.proof.harness.handshake.hhs3_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_conv.
Require Import WgNoise.proof.harness.handshake.hhs3_p6_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.
(* ---------------------------------------------------------------------- *)
(* Helpers                                                                 *)
(* ---------------------------------------------------------------------- *)
Local Open Scope logic.

#[local] Instance hhs3_p6_F1_cce : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.

Lemma hhs3_p6_F1_tuchar_cs {cs1 cs2: compspecs} sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible, size_compatible, align_compatible. destruct p; simpl; try tauto.
  assert (A: forall ce, align_compatible_rec ce (tarray tuchar n) (Ptrofs.unsigned i)).
  { intros ce. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  pose proof (A (@cenv_cs cs1)). pose proof (A (@cenv_cs cs2)). tauto.
Qed.

(* the response message at the world *)
Lemma hhs3_p6_F1_resp sh m M : resp_rep sh m M =
  !! rm_ok M && @data_at W_handshake sh t_resp
     (Vint (rm_type M), (Vint (rm_sender M), (Vint (rm_receiver M), (bytes (rm_eph M), (bytes (rm_encn M),
      (bytes (rm_mac1 M), bytes (rm_mac2 M))))))) m.
Proof.
  unfold resp_rep, resp_val. f_equal.
  apply equal_f, (@data_at_change_composite Noise.CS W_handshake _ sh t_resp); [apply JMeq_refl | prove_cs_preserve_type].
Qed.

(* the keypair slots of a peer, as a field of the peer at the world *)
Lemma hhs3_p6_F1_kps sh p c pr n : @field_compatible Noise.CS t_peer [] p ->
  kps_rep sh (kps_addr p) c pr n = EX lk: val, @field_at W_handshake sh t_peer (DOT HC._keypairs) (c, (pr, (n, lk))) p.
Proof.
  intros FC0. assert (FC: @field_compatible W_handshake t_peer [] p).
  { apply (@field_compatible_change_composite Noise.CS W_handshake _); [prove_cs_preserve_type | exact FC0]. }
  unfold kps_rep. apply pred_ext; Intros lk; Exists lk;
  rewrite field_at_data_at; rewrite field_address_offset by auto with field_compatible;
  unfold kps_addr; simpl nested_field_type; simpl nested_field_offset;
  erewrite <- (@data_at_change_composite Noise.CS W_handshake _ sh t_kps); try apply JMeq_refl; try prove_cs_preserve_type;
  apply derives_refl.
Qed.

(* the keypair's fields, from the unit's compspecs to the world *)
Lemma hhs3_p6_F1_ri sh k (v: val) :
  @field_at Noise.CS sh t_kp [StructField I._remote_index] v k = @field_at W_handshake sh t_kp [StructField HC._remote_index] v k.
Proof. apply equal_f, (@field_at_change_composite Noise.CS W_handshake _ sh t_kp); [apply JMeq_refl | prove_cs_preserve_type]. Qed.
Lemma hhs3_p6_F1_ini sh k (v: val) :
  @field_at Noise.CS sh t_kp [StructField I._i_am_the_initiator] v k =
  @field_at W_handshake sh t_kp [StructField HC._i_am_the_initiator] v k.
Proof. apply equal_f, (@field_at_change_composite Noise.CS W_handshake _ sh t_kp); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

(* a symmetric key of the keypair: its key bytes as a buffer, birthdate and validity at the world *)
Ltac hhs3_p6_F1_sym_tac fld :=
  let FC0 := fresh in let LK := fresh in let E := fresh in
  intros sh k S FC0 LK;
  assert (FC: @field_compatible W_handshake t_kp [] k)
    by (apply (@field_compatible_change_composite Noise.CS W_handshake _); [prove_cs_preserve_type | exact FC0]);
  assert (E: @field_at Noise.CS sh t_kp [StructField fld] (symkey_val S) = @field_at W_handshake sh t_kp [StructField fld] (symkey_val S))
   by (apply (@field_at_change_composite Noise.CS W_handshake _ sh t_kp); [apply JMeq_refl | prove_cs_preserve_type]);
  rewrite E;
  unfold_field_at (@field_at W_handshake _ t_kp [StructField _] _ _);
  rewrite (@field_at_data_at W_handshake _ t_kp [StructField _; StructField _]);
  rewrite field_address_offset by auto with field_compatible;
  simpl nested_field_type; simpl nested_field_offset; unfold symkey_val, hbytes; cbn [fst snd]; rewrite LK;
  change (Tarray (Tint I8 Unsigned _) 32 _) with (tarray tuchar 32);
  rewrite (hhs3_p6_F1_tuchar_cs (cs1 := W_handshake) (cs2 := HCS));
  apply pred_ext; cancel.

Lemma hhs3_p6_F1_send : forall sh k S, @field_compatible Noise.CS t_kp [] k -> Zlength (sk_key S) = 32 ->
  @field_at Noise.CS sh t_kp [StructField I._sending] (symkey_val S) k =
  hbytes sh (sk_key S) (offset_val 32 k) *
  @field_at W_handshake sh t_kp [StructField HC._birthdate; StructField HC._sending] (Vlong (sk_birth S)) k *
  @field_at W_handshake sh t_kp [StructField HC._is_valid; StructField HC._sending] (Val.of_bool (sk_valid S)) k *
  spacer sh 73 80 k.
Proof. hhs3_p6_F1_sym_tac I._sending. Qed.

Lemma hhs3_p6_F1_recv : forall sh k S, @field_compatible Noise.CS t_kp [] k -> Zlength (sk_key S) = 32 ->
  @field_at Noise.CS sh t_kp [StructField I._receiving] (symkey_val S) k =
  hbytes sh (sk_key S) (offset_val 88 k) *
  @field_at W_handshake sh t_kp [StructField HC._birthdate; StructField HC._receiving] (Vlong (sk_birth S)) k *
  @field_at W_handshake sh t_kp [StructField HC._is_valid; StructField HC._receiving] (Val.of_bool (sk_valid S)) k *
  spacer sh 129 136 k.
Proof. hhs3_p6_F1_sym_tac I._receiving. Qed.

Section KP.
#[local] Existing Instance Noise.CS.

(* the keypair without the fields F1 reads *)
Definition hhs3_p6_F1_kprest (k: val) (K: keypair) : mpred :=
  @malloc_token W_handshake Ews (tarray tuchar SIZEOF_KEYPAIR) k *
  field_at Ews t_kp [StructField I._sending_counter] (Vlong (kp_scounter K)) k *
  (EX lk: val, field_at Ews t_kp [StructField I._receiving_counter]
                  (Vlong (kp_rcounter K), (lk, map Vlong (kp_backtrack K))) k) *
  field_at Ews t_kp [StructField I._refcount] (Vint (kp_refs K)) k *
  (EX r: val, field_at Ews t_kp [StructField I._rcu] r k) *
  field_at Ews t_kp [StructField I._internal_id] (Vlong (kp_id K)) k *
  spacer Ews 1181 1184 k.

(* the fields F1 reads, at the world (keys as byte buffers) *)
Definition hhs3_p6_F1_kpread (k: val) (K: keypair) : mpred :=
  hbytes Ews (sk_key (kp_send K)) (offset_val 32 k) *
  @field_at W_handshake Ews t_kp [StructField HC._birthdate; StructField HC._sending] (Vlong (sk_birth (kp_send K))) k *
  @field_at W_handshake Ews t_kp [StructField HC._is_valid; StructField HC._sending] (Val.of_bool (sk_valid (kp_send K))) k *
  spacer Ews 73 80 k *
  hbytes Ews (sk_key (kp_recv K)) (offset_val 88 k) *
  @field_at W_handshake Ews t_kp [StructField HC._birthdate; StructField HC._receiving] (Vlong (sk_birth (kp_recv K))) k *
  @field_at W_handshake Ews t_kp [StructField HC._is_valid; StructField HC._receiving] (Val.of_bool (sk_valid (kp_recv K))) k *
  spacer Ews 129 136 k *
  @field_at W_handshake Ews t_kp [StructField HC._remote_index] (Vint (kp_rindex K)) k *
  @field_at W_handshake Ews t_kp [StructField HC._i_am_the_initiator] (Val.of_bool (kp_init K)) k.

End KP.

Lemma hhs3_p6_F1_kp_open k K :
  keypairs_rep W_handshake [(k, K)] =
  !! (@field_compatible Noise.CS t_kp [] k /\ kp_ok K) && (hhs3_p6_F1_kprest k K * hhs3_p6_F1_kpread k K).
Proof.
  unfold keypairs_rep, keypair_item_rep, keypair_rep, hhs3_p6_F1_kprest, hhs3_p6_F1_kpread.
  cbn [VST.msl.iter_sepcon.iter_sepcon]. rewrite sepcon_emp.
  apply pred_ext; Intros; rename H into FC; pose proof H0 as (L1 & L2 & L3);
  rewrite (hhs3_p6_F1_send Ews k (kp_send K) FC L1), (hhs3_p6_F1_recv Ews k (kp_recv K) FC L2),
          hhs3_p6_F1_ri, hhs3_p6_F1_ini;
  entailer!.
Qed.

(* the peer without its keypair slots *)
Section PR.
#[local] Existing Instance Noise.CS.
Definition hhs3_p6_F1_prest (sh: share) (p: val) (P: peer) : mpred :=
  !! field_compatible t_peer [] p &&
  (field_at sh t_peer [StructField I._device] (p_device P) p *
   field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   hs_rep sh (hs_addr p) (p_hs P) *
   field_at sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   field_at sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   field_at sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   field_at sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).
End PR.

Lemma hhs3_p6_F1_peer_split sh p P :
  peer_rep sh p P = hhs3_p6_F1_prest sh p P * kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P).
Proof. unfold peer_rep, hhs3_p6_F1_prest. apply pred_ext; Intros; entailer!. Qed.

(* the initiation message at the world *)
Lemma hhs3_p6_F1_init sh m M : init_rep sh m M =
  !! im_ok M && @data_at W_handshake sh t_init
     (Vint (im_type M), (Vint (im_sender M), (bytes (im_eph M), (bytes (im_encs M), (bytes (im_enct M),
      (bytes (im_mac1 M), bytes (im_mac2 M))))))) m.
Proof.
  unfold init_rep, init_val. f_equal.
  apply equal_f, (@data_at_change_composite Noise.CS W_handshake _ sh t_init); [apply JMeq_refl | prove_cs_preserve_type].
Qed.

(* the keypair begin_session made for B (responder) *)
Lemma hhs3_p6_F1_KB V : hs_state (w_H2 V) = HS_CREATED_RESPONSE -> hs_rindex (w_H2 V) = im_sender (w_M1 V) ->
  hs_ck (w_H2 V) = hhs3_p6_ck V ->
  hhs3_p6_KB V = mkKP (mkSym (kdf2 (hhs3_p6_ck V) []) (w_nowa V) true) Int64.zero
                      (mkSym (kdf1 (hhs3_p6_ck V) []) (w_nowa V) true) Int64.zero (Zrepeat Int64.zero 128)
                      (im_sender (w_M1 V)) false Int.one (Int64.repr 2).
Proof. intros E1 E2 E3. unfold hhs3_p6_KB, kp_new. rewrite E1, E2, E3. reflexivity. Qed.

(* kb's entry (at kb) is in B's table pool: kb is a valid pointer *)
Lemma hhs3_p6_F1_vp sh tab L V kb : itable sh tab (hhs3_p6_TB2 L V kb) |-- valid_pointer kb.
Proof.
  unfold itable, hhs3_p6_TB2, pool_item_rep, entry_at. cbn [t_D t_L VST.msl.iter_sepcon.iter_sepcon].
  Intros. entailer!.
Qed.
#[local] Hint Resolve hhs3_p6_F1_vp : valid_pointer.

Lemma hhs3_p6_F1_eqb_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

Ltac hhs3_p6_F1_absurd :=
  first [ discriminate | contradiction | exfalso; apply Int.one_not_zero; assumption
        | match goal with H: typed_false _ _ |- _ => inv H end ].

Local Open Scope Z_scope.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p6_F1_ok {Espec: OracleKind} gv L FR V :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hhs3_p6_pure x25519 aead_enc aead_dec -> hhs3_p6_free_stmt x25519 ->
  hhs3_p6_ctx x25519 aead_enc aead_dec L V ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p6_SE x25519 gv L FR V) hhs3_p6_F1
    (overridePost (hhs3_p6_SF x25519 gv L FR V) (hhs3_R gv)).
Proof.
  intros HH HP HF HC. unfold hhs3_p6_SE, hhs3_p6_SF, hhs3_p6_SEF, hhs3_Delta, hhs3_R, hhs3_p6_F1. simplify_func_tycontext. abbreviate_semax.
  Intros ka kb.
  destruct HH as (HX & HAE & _ & HCM & _). destruct HP as (_ & HFB & HCK & _).
  destruct (HFB HX HAE L V HC) as (Est & Eri & _ & _ & _).
  pose proof (HCK HCM HX HAE L V HC) as Eck.
  pose proof (hhs3_p6_F1_KB V Est Eri Eck) as EKB.
  (* CHECK(rb) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward_if. { exfalso; apply Int.one_not_zero; assumption. } forward. apply ENTAIL_refl. }
  { forward. apply ENTAIL_refl. }
  unfold hhs3_p6_sep, hhs3_globs, hhs3_setup_sep, hhs3_p6_locals, hhs3_lvars, hhs3_cnt_temps; cbn [app].
  assert_PROP (@field_compatible Noise.CS t_peer [] (l_pa L)) as FCpa by (unfold peer_rep; entailer!).
  rewrite (hhs3_p6_F1_peer_split Tsh (l_pa L)), (hhs3_p6_F1_kps Tsh (l_pa L) _ _ _ FCpa), (hhs3_p6_F1_kp_open kb).
  Intros lk. destruct H3 as [FCkb KOK].
  change (p_cur (hhs3_p6_PA4 x25519 V kb)) with nullval. change (p_prev (hhs3_p6_PA4 x25519 V kb)) with nullval.
  change (p_next (hhs3_p6_PA4 x25519 V kb)) with kb.
  forward.
  (* CHECK(kb != NULL && previous == NULL && current == NULL) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward_if (temp HC._t'182 (Vint Int.one)).
    { forward. forward. entailer!. }
    { contradiction. }
    forward_if (temp HC._t'183 (Vint Int.one)).
    { forward. forward. entailer!. }
    { discriminate. }
    forward_if. { discriminate. }
    forward. drop_LOCAL 0%nat. drop_LOCAL 0%nat. apply ENTAIL_refl. }
  { forward. apply ENTAIL_refl. }
  (* the keypair's fields *)
  assert (FI: kp_init (hhs3_p6_KB V) = false) by (rewrite EKB; reflexivity).
  assert (FRI: kp_rindex (hhs3_p6_KB V) = im_sender (w_M1 V)) by (rewrite EKB; reflexivity).
  assert (FS: sk_key (kp_send (hhs3_p6_KB V)) = kdf2 (hhs3_p6_ck V) []) by (rewrite EKB; reflexivity).
  assert (FR1: sk_key (kp_recv (hhs3_p6_KB V)) = kdf1 (hhs3_p6_ck V) []) by (rewrite EKB; reflexivity).
  assert (FSV: sk_valid (kp_send (hhs3_p6_KB V)) = true) by (rewrite EKB; reflexivity).
  assert (FRV: sk_valid (kp_recv (hhs3_p6_KB V)) = true) by (rewrite EKB; reflexivity).
  assert (EM1: im_sender (hhs3_M1m x25519 (w_R V) (w_M1 V)) = im_sender (w_M1 V)) by reflexivity.
  unfold hhs3_p6_F1_kpread. rewrite hhs3_p6_F1_init. Intros.
  (* CHECK(!initiator && remote_index == m1's sender) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward.
    1: (rewrite FI; entailer!).
    forward_if (temp HC._t'184 (Vint Int.one)).
    { forward. forward. forward. rewrite FRI, EM1, Int.eq_true. entailer!. }
    { match goal with H: typed_false _ _ |- _ =>
        unfold hhs3_p6_KB, kp_new in H; cbn [kp_init] in H; rewrite Est in H; vm_compute in H; discriminate end. }
    forward_if. { hhs3_p6_F1_absurd. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  (* CHECK(receiving = first && sending = second) *)
  unfold hhs3_p6_first, hhs3_p6_second.
  pose proof H4 as (LKS & LKR & _).
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward_call (Ews, offset_val 88 kb, sk_key (kp_recv (hhs3_p6_KB V)), Tsh, l_first L, kdf1 (hhs3_p6_ck V) []).
    { rewrite LKR. entailer!. destruct kb; try contradiction. destruct (l_first L); try contradiction. simpl. rewrite Ptrofs.add_zero. reflexivity. }
    replace (bytes_eqb (sk_key (kp_recv (hhs3_p6_KB V))) (kdf1 (hhs3_p6_ck V) [])) with true
      by (rewrite FR1; symmetry; apply hhs3_p6_F1_eqb_refl).
    forward_if (temp HC._t'186 (Vint Int.one)).
    { forward_call (Ews, offset_val 32 kb, sk_key (kp_send (hhs3_p6_KB V)), Tsh, l_second L, kdf2 (hhs3_p6_ck V) []).
      { rewrite LKS. entailer!. destruct kb; try contradiction. destruct (l_second L); try contradiction.
        simpl. rewrite Ptrofs.add_zero. reflexivity. }
      replace (bytes_eqb (sk_key (kp_send (hhs3_p6_KB V))) (kdf2 (hhs3_p6_ck V) [])) with true
        by (rewrite FS; symmetry; apply hhs3_p6_F1_eqb_refl).
      forward. entailer!. }
    { hhs3_p6_F1_absurd. }
    forward_if. { hhs3_p6_F1_absurd. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  (* CHECK(sending.is_valid && receiving.is_valid) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward. 1: try (rewrite FSV; entailer!).
    forward_if (temp HC._t'188 (Vint Int.one)).
    { forward. 1: try (rewrite FRV; entailer!). forward. rewrite FRV. entailer!. }
    { rewrite FSV in *. hhs3_p6_F1_absurd. }
    forward_if. { hhs3_p6_F1_absurd. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  (* the post: SF *)
  unfold POSTCONDITION, abbreviate. rewrite overridePost_normal'.
  Exists ka kb. unfold hhs3_p6_sep, hhs3_globs, hhs3_setup_sep, hhs3_p6_locals, hhs3_lvars, hhs3_cnt_temps; cbn [app].
  unfold hhs3_p6_first, hhs3_p6_second.
  rewrite hhs3_p6_F1_init, (hhs3_p6_F1_kp_open kb), (hhs3_p6_F1_peer_split Tsh (l_pa L)),
    (hhs3_p6_F1_kps Tsh (l_pa L) _ _ _ FCpa).
  change (p_cur (hhs3_p6_PA4 x25519 V kb)) with nullval. change (p_prev (hhs3_p6_PA4 x25519 V kb)) with nullval.
  change (p_next (hhs3_p6_PA4 x25519 V kb)) with kb.
  Exists lk. unfold hhs3_p6_F1_kpread. entailer!.
  exact (conj FCkb KOK).
Qed.

End Seg.
