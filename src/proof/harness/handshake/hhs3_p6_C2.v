(* law handshake, phase P6, segment C2 = blk 11..16: the CHECKs of birthdates, counters, refcount/entry, index/table, zeroed_from; id_a.
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
Local Open Scope logic.

#[local] Instance hhs3_p6_C2_cce : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.

(* the table after create_initiation *)
Lemma hhs3_p6_C2_TA1 L I : hhs3_TA1 L I =
  mkT [(hs_addr (l_pb L), Tsh, mkEntry (l_pb L) IDX_HANDSHAKE (i_idx I))] [hs_addr (l_pb L)].
Proof.
  unfold hhs3_TA1, t_insert, t_set_index, t_entry, t_upd, hhs3_TA0, hhs3_EB; cbn [t_D t_L sfind supd vremove].
  rewrite !if_true by auto. reflexivity.
Qed.

Lemma hhs3_p6_C2_ifs {A: Type} {P Q: Prop} (b: {P} + {Q}) (x: A) : (if b then x else x) = x.
Proof. destruct b; reflexivity. Qed.

(* the table TA2 opened: ka's entry as the keypair's field, pb's handshake entry as the peer's field *)
Lemma hhs3_p6_C2_open tab pb k idx : k <> hs_addr pb ->
  @field_compatible Noise.CS t_kp [] k -> @field_compatible Noise.CS t_peer [] pb ->
  itable Tsh tab (mkT [(k, Ews, mkEntry pb IDX_KEYPAIR idx); (hs_addr pb, Tsh, mkEntry pb IDX_HANDSHAKE idx)] [k]) =
  @data_at Noise.CS Tsh t_itab k tab *
  @field_at W_handshake Ews t_kp (DOT HC._entry) (pb, (nullval, (Vtrue, (Vint IDX_KEYPAIR, Vint idx)))) k *
  @field_at W_handshake Tsh t_peer (DOT HC._handshake DOT HC._entry)
    (pb, (nullval, (Vfalse, (Vint IDX_HANDSHAKE, Vint idx)))) pb.
Proof.
  intros Hne FCk0 FCp0.
  assert (FCk: @field_compatible W_handshake t_kp [] k).
  { apply (@field_compatible_change_composite Noise.CS W_handshake _); [prove_cs_preserve_type | exact FCk0]. }
  assert (FCp: @field_compatible W_handshake t_peer [] pb).
  { apply (@field_compatible_change_composite Noise.CS W_handshake _); [prove_cs_preserve_type | exact FCp0]. }
  unfold itable, pool_item_rep, entry_at, entry_val, vin. cbn [t_L t_D hd VST.msl.iter_sepcon.iter_sepcon succ_in].
  rewrite !hhs3_p6_C2_ifs.
  destruct (in_dec eq_dec k [k]) as [_|N]; [|exfalso; apply N; left; auto].
  destruct (in_dec eq_dec (hs_addr pb) [k]) as [[E|[]]|_]; [exfalso; apply Hne; exact E|].
  rewrite (@data_at_change_composite Noise.CS W_handshake _ Ews t_entry_s _ _ (JMeq_refl _)) by prove_cs_preserve_type.
  rewrite (@data_at_change_composite Noise.CS W_handshake _ Tsh t_entry_s _ _ (JMeq_refl _)) by prove_cs_preserve_type.
  rewrite !field_at_data_at. rewrite !field_address_offset by auto with field_compatible.
  replace (offset_val (nested_field_offset t_kp (DOT HC._entry)) k) with k
    by (simpl; rewrite isptr_offset_val_zero by (destruct FCk; auto); reflexivity).
  change (offset_val (nested_field_offset t_peer (DOT HC._handshake DOT HC._entry)) pb) with (hs_addr pb).
  rewrite prop_true_andp.
  2:{ unfold itable_wf; cbn [t_L t_D saddrs map]. split; [constructor; [intros []|constructor]|].
      split; [intros x [Hx|[]]; subst; left; auto|]. split.
      { constructor; [intros [E|[]]; apply Hne; symmetry; exact E | constructor; [intros []|constructor]]. }
      constructor; [apply writable_Ews | constructor; [apply writable_share_top | constructor]]. }
  rewrite sepcon_emp. rewrite sepcon_assoc. reflexivity.
Qed.

(* the keypair opened: the fields main loads at the world, the rest at Noise.CS *)
Definition hhs3_p6_C2_kprest (k: val) (K: keypair) : mpred :=
  @malloc_token W_handshake Ews (tarray tuchar SIZEOF_KEYPAIR) k *
  @field_at Noise.CS Ews t_kp [StructField I._remote_index] (Vint (kp_rindex K)) k *
  @field_at Noise.CS Ews t_kp [StructField I._i_am_the_initiator] (Val.of_bool (kp_init K)) k *
  (EX r: val, @field_at Noise.CS Ews t_kp [StructField I._rcu] r k) *
  spacer Ews 1181 1184 k.

Definition hhs3_p6_C2_kpw (k: val) (K: keypair) (lk: val) : mpred :=
  @field_at W_handshake Ews t_kp (DOT HC._sending)
    (bytes (sk_key (kp_send K)), (Vlong (sk_birth (kp_send K)), Val.of_bool (sk_valid (kp_send K)))) k *
  @field_at W_handshake Ews t_kp (DOT HC._sending_counter) (Vlong (kp_scounter K)) k *
  @field_at W_handshake Ews t_kp (DOT HC._receiving)
    (bytes (sk_key (kp_recv K)), (Vlong (sk_birth (kp_recv K)), Val.of_bool (sk_valid (kp_recv K)))) k *
  @field_at W_handshake Ews t_kp (DOT HC._receiving_counter)
    (Vlong (kp_rcounter K), (lk, map Vlong (kp_backtrack K))) k *
  @field_at W_handshake Ews t_kp (DOT HC._refcount) (Vint (kp_refs K)) k *
  @field_at W_handshake Ews t_kp (DOT HC._internal_id) (Vlong (kp_id K)) k.

Lemma hhs3_p6_C2_kp k K :
  keypairs_rep W_handshake [(k, K)] =
  !! (@field_compatible Noise.CS t_kp [] k /\ kp_ok K) &&
  (EX lk: val, hhs3_p6_C2_kpw k K lk) * hhs3_p6_C2_kprest k K.
Proof.
  unfold keypairs_rep, keypair_rep, hhs3_p6_C2_kpw, hhs3_p6_C2_kprest; cbn [VST.msl.iter_sepcon.iter_sepcon keypair_item_rep].
  rewrite sepcon_emp. unfold keypair_rep.
  rewrite (@field_at_change_composite Noise.CS W_handshake _ Ews t_kp [StructField I._sending] _ _ (JMeq_refl _)) by prove_cs_preserve_type.
  rewrite (@field_at_change_composite Noise.CS W_handshake _ Ews t_kp [StructField I._sending_counter] _ _ (JMeq_refl _)) by prove_cs_preserve_type.
  rewrite (@field_at_change_composite Noise.CS W_handshake _ Ews t_kp [StructField I._receiving] _ _ (JMeq_refl _)) by prove_cs_preserve_type.
  rewrite (@field_at_change_composite Noise.CS W_handshake _ Ews t_kp [StructField I._refcount] _ _ (JMeq_refl _)) by prove_cs_preserve_type.
  rewrite (@field_at_change_composite Noise.CS W_handshake _ Ews t_kp [StructField I._internal_id] _ _ (JMeq_refl _)) by prove_cs_preserve_type.
  apply pred_ext.
  - Intros lk r. Exists r lk.
    rewrite (@field_at_change_composite Noise.CS W_handshake _ Ews t_kp [StructField I._receiving_counter] _ _ (JMeq_refl _)) by prove_cs_preserve_type.
    unfold symkey_val. entailer!.
  - Intros lk r. Exists r lk.
    rewrite (@field_at_change_composite Noise.CS W_handshake _ Ews t_kp [StructField I._receiving_counter] _ _ (JMeq_refl _)) by prove_cs_preserve_type.
    unfold symkey_val. entailer!.
Qed.

Lemma hhs3_p6_C2_openA L V ka : ka <> hs_addr (l_pb L) ->
  @field_compatible Noise.CS t_kp [] ka -> @field_compatible Noise.CS t_peer [] (l_pb L) ->
  itable Tsh (l_ita L) (hhs3_p6_TA2 L V ka) =
  @data_at Noise.CS Tsh t_itab ka (l_ita L) *
  @field_at W_handshake Ews t_kp (DOT HC._entry)
    (l_pb L, (nullval, (Vtrue, (Vint IDX_KEYPAIR, Vint (i_idx (w_I V)))))) ka *
  @field_at W_handshake Tsh t_peer (DOT HC._handshake DOT HC._entry)
    (l_pb L, (nullval, (Vfalse, (Vint IDX_HANDSHAKE, Vint (i_idx (w_I V)))))) (l_pb L).
Proof. intros. unfold hhs3_p6_TA2, hhs3_p6_EB1. apply hhs3_p6_C2_open; auto. Qed.

Lemma hhs3_p6_C2_vp sh p P : sepalg.nonidentity sh -> peer_rep sh p P |-- valid_pointer p.
Proof.
  intros N. unfold peer_rep. apply andp_left2. repeat apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; auto; reflexivity.
Qed.

(* the message at the world *)
Lemma hhs3_p6_C2_init sh m M : init_rep sh m M =
  !! im_ok M && @data_at W_handshake sh t_init
     (Vint (im_type M), (Vint (im_sender M), (bytes (im_eph M), (bytes (im_encs M), (bytes (im_enct M),
      (bytes (im_mac1 M), bytes (im_mac2 M))))))) m.
Proof.
  unfold init_rep, init_val. f_equal.
  apply equal_f, (@data_at_change_composite Noise.CS W_handshake _ sh t_init); [apply JMeq_refl | prove_cs_preserve_type].
Qed.

(* hs_zeroed_from on the zeroed handshake *)
Lemma hhs3_p6_C2_zeroed T T' a E H :
  zeroed_from (snap_of T a E H) (snap_of T' a E (hs_zero H)) = true.
Proof.
  unfold zeroed_from, snap_of, hs_zero, is_zero, bytes_eqb;
    cbn [sn_hs sn_entry hs_state hs_rindex hs_eph hs_reph hs_hash hs_ck hs_lic hs_sid hs_rstatic hs_ss hs_psk hs_ts].
  rewrite !Int.eq_true, Int64.eq_true.
  repeat (rewrite if_true by (try reflexivity; try (rewrite Zlength_zeros; reflexivity))).
  reflexivity.
Qed.

Lemma hhs3_p6_C2_sid x L V : w_PB2 V = hhs3_p6_PB2n x L V -> hs_sid (w_H1 V) = id_addr (l_wa L) ->
  hs_sid (p_hs (hhs3_p6_PBa V)) = id_addr (l_wa L).
Proof.
  intros E1 E2. unfold hhs3_p6_PBa, p_set_refs; cbn [p_hs]. rewrite E1. unfold hhs3_p6_PB2n.
  destruct (w_ST2 V). cbn. exact E2.
Qed.

Lemma hhs3_p6_C2_cmp L V ka : ka <> hs_addr (l_pb L) -> hs_sid (p_hs (hhs3_p6_PBa V)) = id_addr (l_wa L) ->
  hs_cmp_pre (snap_of (hhs3_TA1 L (w_I V)) (hs_addr (l_pb L)) (hhs3_p6_EB1 L V) (p_hs (hhs3_p6_PBa V)))
    (hhs3_p6_TA2 L V ka) (l_pb L) (l_wa L) (hhs3_p6_PB3 V ka) (hhs3_p6_EB1 L V).
Proof.
  intros Hne Hsid. unfold hs_cmp_pre. rewrite hhs3_p6_C2_TA1.
  unfold hhs3_p6_TA2, t_entry, snap_of; cbn [t_D t_L sfind sn_entry sn_hs sn_next succ_in].
  rewrite if_false by (intro E; apply Hne; exact E). rewrite !if_true by reflexivity.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hsid|].
  split; [exact Hsid | left; reflexivity].
Qed.

Lemma hhs3_p6_C2_vinA L V ka : vin ka (t_L (hhs3_p6_TA2 L V ka)) = true.
Proof. unfold hhs3_p6_TA2, vin; cbn [t_L]. destruct (in_dec eq_dec ka [ka]) as [_|N]; [reflexivity | exfalso; apply N; left; auto]. Qed.

Lemma hhs3_p6_C2_lenA L V ka : Zlength (t_L (hhs3_p6_TA2 L V ka)) = 1.
Proof. reflexivity. Qed.

Lemma hhs3_p6_C2_zeroedA L V ka :
  zeroed_from (snap_of (hhs3_TA1 L (w_I V)) (hs_addr (l_pb L)) (hhs3_p6_EB1 L V) (p_hs (hhs3_p6_PBa V)))
    (snap_of (hhs3_p6_TA2 L V ka) (hs_addr (l_pb L)) (hhs3_p6_EB1 L V) (p_hs (hhs3_p6_PB3 V ka))) = true.
Proof. apply hhs3_p6_C2_zeroed. Qed.

Lemma hhs3_p6_C2_KA V :
  sk_birth (kp_send (hhs3_p6_KA V)) = w_nowa V /\ sk_birth (kp_recv (hhs3_p6_KA V)) = w_nowa V /\
  kp_scounter (hhs3_p6_KA V) = Int64.zero /\ kp_rcounter (hhs3_p6_KA V) = Int64.zero /\
  kp_refs (hhs3_p6_KA V) = Int.one /\ kp_id (hhs3_p6_KA V) = Int64.one.
Proof. unfold hhs3_p6_KA, kp_new; cbn. repeat split. Qed.

Local Open Scope Z_scope.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p6_C2_ok {Espec: OracleKind} gv L FR V :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hhs3_p6_pure x25519 aead_enc aead_dec -> hhs3_p6_free_stmt x25519 ->
  hhs3_p6_ctx x25519 aead_enc aead_dec L V ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p6_SC1 x25519 gv L FR V) hhs3_p6_C2
    (overridePost (hhs3_p6_SC x25519 gv L FR V) (hhs3_R gv)).
Proof.
  intros HH HP HF HC. unfold hhs3_p6_SC1, hhs3_p6_SBC, hhs3_Delta, hhs3_R, hhs3_p6_C2. simplify_func_tycontext. abbreviate_semax.
  Intros ka.
  unfold hhs3_p6_sep, hhs3_p6_locals, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
  destruct (hhs3_p6_C2_KA V) as (K1 & K2 & K3 & K4 & K5 & K6).
  rewrite hhs3_p6_C2_kp. unfold hhs3_p6_C2_kpw. rewrite K1, K2, K3, K4, K5, K6. Intros lk.
  (* CHECK(birthdates == now_a) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  - apply ENTAIL_refl.
  - forward. forward_if (temp HC._t'168 (Vint Int.one)).
    { forward. forward. entailer!. rewrite Int64.eq_true. reflexivity. }
    { match goal with Hn: w_nowa V <> w_nowa V |- _ => exfalso; apply Hn; reflexivity end. }
    forward_if.
    { discriminate. }
    forward. entailer!.
  - forward. apply ENTAIL_refl.
  - (* CHECK(counters == 0) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward. forward_if (temp HC._t'169 (Vint Int.one)).
    { forward. forward. entailer!. }
    { match goal with Hn: _ |- _ => exfalso; apply Hn; reflexivity end. }
    forward_if.
    { discriminate. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  assert_PROP (@field_compatible Noise.CS t_peer [] (l_pb L)) as FCpb by (unfold peer_rep; entailer!).
  match goal with Hk: field_compatible t_kp [] ka |- _ => rename Hk into FCka end.
  assert (Hne: ka <> hs_addr (l_pb L)).
  { intro E; apply H0. rewrite hhs3_p6_C2_TA1, E. left; reflexivity. }
  rewrite (hhs3_p6_C2_openA L V ka Hne FCka FCpb). Intros.
  (* CHECK(refcount == 1 && entry.type == KEYPAIR && entry.peer == &pb) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward. forward_if (temp HC._t'170 (Vint Int.one)).
    { forward. forward. entailer!. }
    { match goal with Hn: _ |- _ => exfalso; apply Hn; reflexivity end. }
    forward_if (temp HC._t'171 (Vint Int.one)).
    { forward. forward.
      2: { entailer!. rewrite if_true by auto. reflexivity. }
      entailer!.
      apply denote_tc_test_eq_split;
        (pull_left (peer_rep Tsh (l_pb L) (hhs3_p6_PB3 V ka));
         repeat apply sepcon_valid_pointer1; apply hhs3_p6_C2_vp; auto). }
    { discriminate. }
    forward_if.
    { discriminate. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  (* CHECK(entry.index == m1->sender_index && table_has && table_len == 1) *)
  destruct HH as (HX & HA & _ & _ & _).
  destruct HP as (HfA & _).
  destruct (HfA HX HA L V HC) as (EPB2 & _ & _ & Esnd & Hsid1).
  rewrite hhs3_p6_C2_init. Intros.
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward. forward.
    sep_apply (derives_refl' _ _ (eq_sym (hhs3_p6_C2_openA L V ka Hne FCka FCpb))).
    forward_if (temp HC._t'172 (Vint Int.one)).
    { forward_call (Tsh, l_ita L, hhs3_p6_TA2 L V ka, ka).
      { entailer!. unfold eval_field; simpl. rewrite isptr_offset_val_zero by (destruct FCka; auto). reflexivity. }
      { unfold hhs3_p6_TA2; cbn; left; reflexivity. }
      rewrite (hhs3_p6_C2_vinA L V ka).
      forward. entailer!. }
    { match goal with Hn: i_idx _ <> _ |- _ => exfalso; apply Hn; rewrite <- Esnd; reflexivity end. }
    forward_if (temp HC._t'174 (Vint Int.one)).
    { forward_call (Tsh, l_ita L, hhs3_p6_TA2 L V ka). rewrite (hhs3_p6_C2_lenA L V ka).
      forward. entailer!. }
    { discriminate. }
    forward_if.
    { discriminate. }
    forward. rewrite (hhs3_p6_C2_openA L V ka Hne FCka FCpb). entailer!. }
  { forward. apply ENTAIL_refl. }
  (* CHECK(!pb.handshake.entry.hashed && hs_zeroed_from(&snap, &pb.handshake)) *)
  unfold hhs3_p6_snapA.
  assert (Hsid: hs_sid (p_hs (hhs3_p6_PBa V)) = id_addr (l_wa L)) by (apply (hhs3_p6_C2_sid x25519); auto).
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward.
    sep_apply (derives_refl' _ _ (eq_sym (hhs3_p6_C2_openA L V ka Hne FCka FCpb))).
    forward_if (temp HC._t'176 (Vint Int.one)).
    { forward_call (Tsh, l_snap L,
        snap_of (hhs3_TA1 L (w_I V)) (hs_addr (l_pb L)) (hhs3_p6_EB1 L V) (p_hs (hhs3_p6_PBa V)),
        Tsh, l_pb L, hhs3_p6_PB3 V ka, Tsh, l_ita L, hhs3_p6_TA2 L V ka, hhs3_p6_EB1 L V,
        Tsh, l_wa L, hhs3_DA x25519 (w_R V) L).
      { apply hhs3_p6_C2_cmp; auto. }
      rewrite (hhs3_p6_C2_zeroedA L V ka).
      forward. entailer!. }
    { contradiction. }
    forward_if.
    { discriminate. }
    forward. rewrite (hhs3_p6_C2_openA L V ka Hne FCka FCpb). entailer!. }
  { forward. apply ENTAIL_refl. }
  (* id_a = ka->internal_id *)
  forward.
  unfold hhs3_p6_SC.
  Exists ka. unfold hhs3_p6_sep, hhs3_p6_locals, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
  rewrite hhs3_p6_C2_kp, hhs3_p6_C2_init, (hhs3_p6_C2_openA L V ka Hne FCka FCpb). unfold hhs3_p6_C2_kpw. rewrite K1, K2, K3, K4, K5, K6.
  Exists lk.
  sep_apply (@data_at_data_at_ HCS Tsh t_hsnap (hsnap_val (snap_of (hhs3_TA1 L (w_I V))
    (hs_addr (l_pb L)) (hhs3_p6_EB1 L V) (p_hs (hhs3_p6_PBa V)))) (l_snap L)).
  entailer!.
Qed.

End Seg.
