(* law handshake, phase P6, segment C1 = blk 5..10: CHECK(ra), ka = current, the CHECKs of slots, role, remote index, keys, validity.
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

#[local] Instance hhs3_p6_C1_cce : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.

Lemma hhs3_p6_C1_tuchar_cs {cs1 cs2: compspecs} sh n (v: list val) p :
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
Lemma hhs3_p6_C1_resp sh m M : resp_rep sh m M =
  !! rm_ok M && @data_at W_handshake sh t_resp
     (Vint (rm_type M), (Vint (rm_sender M), (Vint (rm_receiver M), (bytes (rm_eph M), (bytes (rm_encn M),
      (bytes (rm_mac1 M), bytes (rm_mac2 M))))))) m.
Proof.
  unfold resp_rep, resp_val. f_equal.
  apply equal_f, (@data_at_change_composite Noise.CS W_handshake _ sh t_resp); [apply JMeq_refl | prove_cs_preserve_type].
Qed.

(* the keypair slots of a peer, as a field of the peer at the world *)
Lemma hhs3_p6_C1_kps sh p c pr n : @field_compatible Noise.CS t_peer [] p ->
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
Lemma hhs3_p6_C1_ri sh k (v: val) :
  @field_at Noise.CS sh t_kp [StructField I._remote_index] v k = @field_at W_handshake sh t_kp [StructField HC._remote_index] v k.
Proof. apply equal_f, (@field_at_change_composite Noise.CS W_handshake _ sh t_kp); [apply JMeq_refl | prove_cs_preserve_type]. Qed.
Lemma hhs3_p6_C1_ini sh k (v: val) :
  @field_at Noise.CS sh t_kp [StructField I._i_am_the_initiator] v k =
  @field_at W_handshake sh t_kp [StructField HC._i_am_the_initiator] v k.
Proof. apply equal_f, (@field_at_change_composite Noise.CS W_handshake _ sh t_kp); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

(* a symmetric key of the keypair: its key bytes as a buffer, birthdate and validity at the world *)
Ltac hhs3_p6_C1_sym_tac fld :=
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
  rewrite (hhs3_p6_C1_tuchar_cs (cs1 := W_handshake) (cs2 := HCS));
  apply pred_ext; cancel.

Lemma hhs3_p6_C1_send : forall sh k S, @field_compatible Noise.CS t_kp [] k -> Zlength (sk_key S) = 32 ->
  @field_at Noise.CS sh t_kp [StructField I._sending] (symkey_val S) k =
  hbytes sh (sk_key S) (offset_val 32 k) *
  @field_at W_handshake sh t_kp [StructField HC._birthdate; StructField HC._sending] (Vlong (sk_birth S)) k *
  @field_at W_handshake sh t_kp [StructField HC._is_valid; StructField HC._sending] (Val.of_bool (sk_valid S)) k *
  spacer sh 73 80 k.
Proof. hhs3_p6_C1_sym_tac I._sending. Qed.

Lemma hhs3_p6_C1_recv : forall sh k S, @field_compatible Noise.CS t_kp [] k -> Zlength (sk_key S) = 32 ->
  @field_at Noise.CS sh t_kp [StructField I._receiving] (symkey_val S) k =
  hbytes sh (sk_key S) (offset_val 88 k) *
  @field_at W_handshake sh t_kp [StructField HC._birthdate; StructField HC._receiving] (Vlong (sk_birth S)) k *
  @field_at W_handshake sh t_kp [StructField HC._is_valid; StructField HC._receiving] (Val.of_bool (sk_valid S)) k *
  spacer sh 129 136 k.
Proof. hhs3_p6_C1_sym_tac I._receiving. Qed.

Section KP.
#[local] Existing Instance Noise.CS.

(* the keypair without the fields C1 reads *)
Definition hhs3_p6_C1_kprest (k: val) (K: keypair) : mpred :=
  @malloc_token W_handshake Ews (tarray tuchar SIZEOF_KEYPAIR) k *
  field_at Ews t_kp [StructField I._sending_counter] (Vlong (kp_scounter K)) k *
  (EX lk: val, field_at Ews t_kp [StructField I._receiving_counter]
                  (Vlong (kp_rcounter K), (lk, map Vlong (kp_backtrack K))) k) *
  field_at Ews t_kp [StructField I._refcount] (Vint (kp_refs K)) k *
  (EX r: val, field_at Ews t_kp [StructField I._rcu] r k) *
  field_at Ews t_kp [StructField I._internal_id] (Vlong (kp_id K)) k *
  spacer Ews 1181 1184 k.

(* the fields C1 reads, at the world (keys as byte buffers) *)
Definition hhs3_p6_C1_kpread (k: val) (K: keypair) : mpred :=
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

Lemma hhs3_p6_C1_kp_open k K :
  keypairs_rep W_handshake [(k, K)] =
  !! (@field_compatible Noise.CS t_kp [] k /\ kp_ok K) && (hhs3_p6_C1_kprest k K * hhs3_p6_C1_kpread k K).
Proof.
  unfold keypairs_rep, keypair_item_rep, keypair_rep, hhs3_p6_C1_kprest, hhs3_p6_C1_kpread.
  cbn [VST.msl.iter_sepcon.iter_sepcon]. rewrite sepcon_emp.
  apply pred_ext; Intros; rename H into FC; pose proof H0 as (L1 & L2 & L3);
  rewrite (hhs3_p6_C1_send Ews k (kp_send K) FC L1), (hhs3_p6_C1_recv Ews k (kp_recv K) FC L2),
          hhs3_p6_C1_ri, hhs3_p6_C1_ini;
  entailer!.
Qed.

(* the peer without its keypair slots *)
Section PR.
#[local] Existing Instance Noise.CS.
Definition hhs3_p6_C1_prest (sh: share) (p: val) (P: peer) : mpred :=
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

Lemma hhs3_p6_C1_peer_split sh p P :
  peer_rep sh p P = hhs3_p6_C1_prest sh p P * kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P).
Proof. unfold peer_rep, hhs3_p6_C1_prest. apply pred_ext; Intros; entailer!. Qed.

(* the keypair begin_session made for A *)
Lemma hhs3_p6_C1_KA x L V : w_PB2 V = hhs3_p6_PB2n x L V ->
  hhs3_p6_KA V = mkKP (mkSym (kdf1 (hhs3_p6_ck V) []) (w_nowa V) true) Int64.zero
                      (mkSym (kdf2 (hhs3_p6_ck V) []) (w_nowa V) true) Int64.zero (Zrepeat Int64.zero 128)
                      (rm_sender (w_M2 V)) true Int.one Int64.one.
Proof.
  intros E. unfold hhs3_p6_KA, hhs3_p6_PBa, hhs3_p6_ck, kp_new. cbn [p_hs p_set_refs]. rewrite E.
  unfold hhs3_p6_PB2n. destruct (w_ST2 V) as [ck h]. cbv beta iota zeta.
  match goal with |- context [p_hs (p_set_hs ?P ?H)] => change (p_hs (p_set_hs P H)) with H end.
  cbn [hs_state hs_ck hs_rindex fst]. rewrite Int.eq_true. reflexivity.
Qed.

(* ka's entry (at ka) is in A's table pool: ka is a valid pointer *)
Lemma hhs3_p6_C1_vp sh tab L V ka : itable sh tab (hhs3_p6_TA2 L V ka) |-- valid_pointer ka.
Proof.
  unfold itable, hhs3_p6_TA2, pool_item_rep, entry_at. cbn [t_D t_L VST.msl.iter_sepcon.iter_sepcon].
  Intros. entailer!.
Qed.
#[local] Hint Resolve hhs3_p6_C1_vp : valid_pointer.

Lemma hhs3_p6_C1_eqb_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

Ltac hhs3_p6_C1_absurd :=
  first [ discriminate | contradiction | exfalso; apply Int.one_not_zero; assumption
        | match goal with H: typed_false _ _ |- _ => inv H end ].

Local Open Scope Z_scope.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p6_C1_ok {Espec: OracleKind} gv L FR V :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hhs3_p6_pure x25519 aead_enc aead_dec -> hhs3_p6_free_stmt x25519 ->
  hhs3_p6_ctx x25519 aead_enc aead_dec L V ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p6_SB x25519 gv L FR V) hhs3_p6_C1
    (overridePost (hhs3_p6_SC1 x25519 gv L FR V) (hhs3_R gv)).
Proof.
  intros HH HP HF HC. unfold hhs3_p6_SB, hhs3_p6_SC1, hhs3_p6_SBC, hhs3_Delta, hhs3_R, hhs3_p6_C1. simplify_func_tycontext. abbreviate_semax.
  Intros ka.
  destruct HH as (HX & HAE & _ & _ & _). destruct HP as (HFA & _).
  destruct (HFA HX HAE L V HC) as (EPB2 & Lck & _ & _ & _).
  pose proof (hhs3_p6_C1_KA x25519 L V EPB2) as EKA.
  (* CHECK(ra) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward_if. { exfalso; apply Int.one_not_zero; assumption. } forward. apply ENTAIL_refl. }
  { forward. apply ENTAIL_refl. }
  unfold hhs3_p6_sep, hhs3_globs, hhs3_setup_sep, hhs3_p6_locals, hhs3_lvars, hhs3_cnt_temps; cbn [app].
  assert_PROP (@field_compatible Noise.CS t_peer [] (l_pb L)) as FCpb by (unfold peer_rep; entailer!).
  rewrite (hhs3_p6_C1_peer_split Tsh (l_pb L)), (hhs3_p6_C1_kps Tsh (l_pb L) _ _ _ FCpb), hhs3_p6_C1_kp_open.
  Intros lk. destruct H1 as [FCka KOK].
  change (p_cur (hhs3_p6_PB3 V ka)) with ka. change (p_prev (hhs3_p6_PB3 V ka)) with nullval.
  change (p_next (hhs3_p6_PB3 V ka)) with nullval.
  forward.
  (* CHECK(ka != NULL && previous == NULL && next == NULL) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward_if (temp HC._t'161 (Vint Int.one)).
    { forward. forward. entailer!. }
    { contradiction. }
    forward_if (temp HC._t'162 (Vint Int.one)).
    { forward. forward. entailer!. }
    { discriminate. }
    forward_if. { discriminate. }
    forward. drop_LOCAL 0%nat. drop_LOCAL 0%nat. apply ENTAIL_refl. }
  { forward. apply ENTAIL_refl. }
  (* the keypair's fields *)
  assert (FI: kp_init (hhs3_p6_KA V) = true) by (rewrite EKA; reflexivity).
  assert (FRI: kp_rindex (hhs3_p6_KA V) = rm_sender (w_M2 V)) by (rewrite EKA; reflexivity).
  assert (FS: sk_key (kp_send (hhs3_p6_KA V)) = kdf1 (hhs3_p6_ck V) []) by (rewrite EKA; reflexivity).
  assert (FR2: sk_key (kp_recv (hhs3_p6_KA V)) = kdf2 (hhs3_p6_ck V) []) by (rewrite EKA; reflexivity).
  assert (FSV: sk_valid (kp_send (hhs3_p6_KA V)) = true) by (rewrite EKA; reflexivity).
  assert (FRV: sk_valid (kp_recv (hhs3_p6_KA V)) = true) by (rewrite EKA; reflexivity).
  assert (EM2: rm_sender (hhs3_M2m x25519 (w_R V) (w_M2 V)) = rm_sender (w_M2 V)) by reflexivity.
  unfold hhs3_p6_C1_kpread. rewrite hhs3_p6_C1_resp. Intros.
  (* CHECK(initiator && remote_index == m2's sender) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward.
    1: (rewrite FI; entailer!).
    forward_if (temp HC._t'163 (Vint Int.one)).
    2: { pose proof FI as FI'. unfold hhs3_p6_KA, kp_new, hhs3_p6_PBa in FI'. cbn [kp_init p_hs p_set_refs] in FI'.
         rewrite FI' in H3. inv H3. }
    { forward. forward. forward. rewrite FRI, EM2, Int.eq_true. drop_LOCAL 1%nat. drop_LOCAL 1%nat. apply ENTAIL_refl. }
    forward_if. { discriminate. }
    forward. drop_LOCAL 0%nat. drop_LOCAL 0%nat. apply ENTAIL_refl. }
  { forward. apply ENTAIL_refl. }
  (* CHECK(keys = first / second) *)
  unfold hhs3_p6_first, hhs3_p6_second.
  pose proof H2 as (LKS & LKR & _).
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward_call (Ews, offset_val 32 ka, sk_key (kp_send (hhs3_p6_KA V)), Tsh, l_first L, kdf1 (hhs3_p6_ck V) []).
    { rewrite LKS. entailer!. destruct ka; try contradiction. destruct (l_first L); try contradiction. simpl. rewrite Ptrofs.add_zero. reflexivity. }
    replace (bytes_eqb (sk_key (kp_send (hhs3_p6_KA V))) (kdf1 (hhs3_p6_ck V) [])) with true
      by (rewrite FS; symmetry; apply hhs3_p6_C1_eqb_refl).
    forward_if (temp HC._t'165 (Vint Int.one)).
    { forward_call (Ews, offset_val 88 ka, sk_key (kp_recv (hhs3_p6_KA V)), Tsh, l_second L, kdf2 (hhs3_p6_ck V) []).
      { rewrite LKR. entailer!. destruct ka; try contradiction. destruct (l_second L); try contradiction.
        simpl. rewrite Ptrofs.add_zero. reflexivity. }
      replace (bytes_eqb (sk_key (kp_recv (hhs3_p6_KA V))) (kdf2 (hhs3_p6_ck V) [])) with true
        by (rewrite FR2; symmetry; apply hhs3_p6_C1_eqb_refl).
      forward. entailer!. }
    { hhs3_p6_C1_absurd. }
    forward_if. { hhs3_p6_C1_absurd. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  (* CHECK(sending.is_valid && receiving.is_valid) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward. 1: try (rewrite FSV; entailer!).
    forward_if (temp HC._t'167 (Vint Int.one)).
    { forward. 1: try (rewrite FRV; entailer!). forward. rewrite FRV. entailer!. }
    { rewrite FSV in *. hhs3_p6_C1_absurd. }
    forward_if. { hhs3_p6_C1_absurd. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  (* the post: SC1 *)
  unfold POSTCONDITION, abbreviate. rewrite overridePost_normal'.
  Exists ka. unfold hhs3_p6_sep, hhs3_globs, hhs3_setup_sep, hhs3_p6_locals, hhs3_lvars, hhs3_cnt_temps; cbn [app].
  unfold hhs3_p6_first, hhs3_p6_second.
  rewrite hhs3_p6_C1_resp, hhs3_p6_C1_kp_open, (hhs3_p6_C1_peer_split Tsh (l_pb L)),
    (hhs3_p6_C1_kps Tsh (l_pb L) _ _ _ FCpb).
  change (p_cur (hhs3_p6_PB3 V ka)) with ka. change (p_prev (hhs3_p6_PB3 V ka)) with nullval.
  change (p_next (hhs3_p6_PB3 V ka)) with nullval.
  Exists lk. unfold hhs3_p6_C1_kpread. entailer!.
  exact (conj FCka KOK).
Qed.

End Seg.
