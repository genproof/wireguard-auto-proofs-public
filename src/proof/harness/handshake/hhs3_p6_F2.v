(* law handshake, phase P6, segment F2 = blk 27..32: the CHECKs of birthdates, refcount/entry, index/table, zeroed_from, internal id, cross-over.
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

(* ---------------------------------------------------------------------- *)
(* Helpers                                                                 *)
(* ---------------------------------------------------------------------- *)
Local Open Scope logic.

#[local] Instance hhs3_p6_F2_cce : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.

Lemma hhs3_p6_F2_tuchar_cs {cs1 cs2: compspecs} sh n (v: list val) p :
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
Lemma hhs3_p6_F2_resp sh m M : resp_rep sh m M =
  !! rm_ok M && @data_at W_handshake sh t_resp
     (Vint (rm_type M), (Vint (rm_sender M), (Vint (rm_receiver M), (bytes (rm_eph M), (bytes (rm_encn M),
      (bytes (rm_mac1 M), bytes (rm_mac2 M))))))) m.
Proof.
  unfold resp_rep, resp_val. f_equal.
  apply equal_f, (@data_at_change_composite Noise.CS W_handshake _ sh t_resp); [apply JMeq_refl | prove_cs_preserve_type].
Qed.

(* the keypair's fields, from the unit's compspecs to the world *)
Lemma hhs3_p6_F2_ri sh k (v: val) :
  @field_at Noise.CS sh t_kp [StructField I._remote_index] v k = @field_at W_handshake sh t_kp [StructField HC._remote_index] v k.
Proof. apply equal_f, (@field_at_change_composite Noise.CS W_handshake _ sh t_kp); [apply JMeq_refl | prove_cs_preserve_type]. Qed.
Lemma hhs3_p6_F2_ini sh k (v: val) :
  @field_at Noise.CS sh t_kp [StructField I._i_am_the_initiator] v k =
  @field_at W_handshake sh t_kp [StructField HC._i_am_the_initiator] v k.
Proof. apply equal_f, (@field_at_change_composite Noise.CS W_handshake _ sh t_kp); [apply JMeq_refl | prove_cs_preserve_type]. Qed.
Lemma hhs3_p6_F2_rc sh k (v: val) :
  @field_at Noise.CS sh t_kp [StructField I._refcount] v k =
  @field_at W_handshake sh t_kp [StructField HC._refcount] v k.
Proof. apply equal_f, (@field_at_change_composite Noise.CS W_handshake _ sh t_kp); [apply JMeq_refl | prove_cs_preserve_type]. Qed.
Lemma hhs3_p6_F2_iid sh k (v: val) :
  @field_at Noise.CS sh t_kp [StructField I._internal_id] v k =
  @field_at W_handshake sh t_kp [StructField HC._internal_id] v k.
Proof. apply equal_f, (@field_at_change_composite Noise.CS W_handshake _ sh t_kp); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

(* a symmetric key of the keypair: its key bytes as a buffer, birthdate and validity at the world *)
Ltac hhs3_p6_F2_sym_tac fld :=
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
  rewrite (hhs3_p6_F2_tuchar_cs (cs1 := W_handshake) (cs2 := HCS));
  apply pred_ext; cancel.

Lemma hhs3_p6_F2_send : forall sh k S, @field_compatible Noise.CS t_kp [] k -> Zlength (sk_key S) = 32 ->
  @field_at Noise.CS sh t_kp [StructField I._sending] (symkey_val S) k =
  hbytes sh (sk_key S) (offset_val 32 k) *
  @field_at W_handshake sh t_kp [StructField HC._birthdate; StructField HC._sending] (Vlong (sk_birth S)) k *
  @field_at W_handshake sh t_kp [StructField HC._is_valid; StructField HC._sending] (Val.of_bool (sk_valid S)) k *
  spacer sh 73 80 k.
Proof. hhs3_p6_F2_sym_tac I._sending. Qed.

Lemma hhs3_p6_F2_recv : forall sh k S, @field_compatible Noise.CS t_kp [] k -> Zlength (sk_key S) = 32 ->
  @field_at Noise.CS sh t_kp [StructField I._receiving] (symkey_val S) k =
  hbytes sh (sk_key S) (offset_val 88 k) *
  @field_at W_handshake sh t_kp [StructField HC._birthdate; StructField HC._receiving] (Vlong (sk_birth S)) k *
  @field_at W_handshake sh t_kp [StructField HC._is_valid; StructField HC._receiving] (Val.of_bool (sk_valid S)) k *
  spacer sh 129 136 k.
Proof. hhs3_p6_F2_sym_tac I._receiving. Qed.

Section KP.
#[local] Existing Instance Noise.CS.

(* the keypair without the fields F2 reads *)
Definition hhs3_p6_F2_kprest (k: val) (K: keypair) : mpred :=
  @malloc_token W_handshake Ews (tarray tuchar SIZEOF_KEYPAIR) k *
  field_at Ews t_kp [StructField I._sending_counter] (Vlong (kp_scounter K)) k *
  (EX lk: val, field_at Ews t_kp [StructField I._receiving_counter]
                  (Vlong (kp_rcounter K), (lk, map Vlong (kp_backtrack K))) k) *
  (EX r: val, field_at Ews t_kp [StructField I._rcu] r k) *
  spacer Ews 1181 1184 k.

(* the fields F2 reads, at the world (keys as byte buffers) *)
Definition hhs3_p6_F2_kpread (k: val) (K: keypair) : mpred :=
  hbytes Ews (sk_key (kp_send K)) (offset_val 32 k) *
  @field_at W_handshake Ews t_kp [StructField HC._birthdate; StructField HC._sending] (Vlong (sk_birth (kp_send K))) k *
  @field_at W_handshake Ews t_kp [StructField HC._is_valid; StructField HC._sending] (Val.of_bool (sk_valid (kp_send K))) k *
  spacer Ews 73 80 k *
  hbytes Ews (sk_key (kp_recv K)) (offset_val 88 k) *
  @field_at W_handshake Ews t_kp [StructField HC._birthdate; StructField HC._receiving] (Vlong (sk_birth (kp_recv K))) k *
  @field_at W_handshake Ews t_kp [StructField HC._is_valid; StructField HC._receiving] (Val.of_bool (sk_valid (kp_recv K))) k *
  spacer Ews 129 136 k *
  @field_at W_handshake Ews t_kp [StructField HC._remote_index] (Vint (kp_rindex K)) k *
  @field_at W_handshake Ews t_kp [StructField HC._i_am_the_initiator] (Val.of_bool (kp_init K)) k *
  @field_at W_handshake Ews t_kp [StructField HC._refcount] (Vint (kp_refs K)) k *
  @field_at W_handshake Ews t_kp [StructField HC._internal_id] (Vlong (kp_id K)) k.

End KP.

Lemma hhs3_p6_F2_kp_open k K :
  keypairs_rep W_handshake [(k, K)] =
  !! (@field_compatible Noise.CS t_kp [] k /\ kp_ok K) && (hhs3_p6_F2_kprest k K * hhs3_p6_F2_kpread k K).
Proof.
  unfold keypairs_rep, keypair_item_rep, keypair_rep, hhs3_p6_F2_kprest, hhs3_p6_F2_kpread.
  cbn [VST.msl.iter_sepcon.iter_sepcon]. rewrite sepcon_emp.
  apply pred_ext; Intros; rename H into FC; pose proof H0 as (L1 & L2 & L3);
  rewrite (hhs3_p6_F2_send Ews k (kp_send K) FC L1), (hhs3_p6_F2_recv Ews k (kp_recv K) FC L2),
          hhs3_p6_F2_ri, hhs3_p6_F2_ini, hhs3_p6_F2_rc, hhs3_p6_F2_iid;
  entailer!.
Qed.

(* the keypairs begin_session made *)
Lemma hhs3_p6_F2_KA x L V : w_PB2 V = hhs3_p6_PB2n x L V ->
  hhs3_p6_KA V = mkKP (mkSym (kdf1 (hhs3_p6_ck V) []) (w_nowa V) true) Int64.zero
                      (mkSym (kdf2 (hhs3_p6_ck V) []) (w_nowa V) true) Int64.zero (Zrepeat Int64.zero 128)
                      (rm_sender (w_M2 V)) true Int.one Int64.one.
Proof.
  intros E. unfold hhs3_p6_KA, hhs3_p6_PBa, hhs3_p6_ck, kp_new. cbn [p_hs p_set_refs]. rewrite E.
  unfold hhs3_p6_PB2n. destruct (w_ST2 V) as [ck h]. cbv beta iota zeta.
  match goal with |- context [p_hs (p_set_hs ?P ?H)] => change (p_hs (p_set_hs P H)) with H end.
  cbn [hs_state hs_ck hs_rindex fst]. rewrite Int.eq_true. reflexivity.
Qed.

Lemma hhs3_p6_F2_KB V : hs_state (w_H2 V) = HS_CREATED_RESPONSE -> hs_rindex (w_H2 V) = im_sender (w_M1 V) ->
  hs_ck (w_H2 V) = hhs3_p6_ck V ->
  hhs3_p6_KB V = mkKP (mkSym (kdf2 (hhs3_p6_ck V) []) (w_nowa V) true) Int64.zero
                      (mkSym (kdf1 (hhs3_p6_ck V) []) (w_nowa V) true) Int64.zero (Zrepeat Int64.zero 128)
                      (im_sender (w_M1 V)) false Int.one (Int64.repr 2).
Proof. intros E1 E2 E3. unfold hhs3_p6_KB, kp_new. rewrite E1, E2, E3. reflexivity. Qed.

(* the table after create_response *)
Lemma hhs3_p6_F2_TB1 L Q : hhs3_TB1 L Q =
  mkT [(hs_addr (l_pa L), Tsh, mkEntry (l_pa L) IDX_HANDSHAKE (s_idx Q))] [hs_addr (l_pa L)].
Proof.
  unfold hhs3_TB1, t_insert, t_set_index, t_entry, t_upd, hhs3_TB0, hhs3_EA; cbn [t_D t_L sfind supd vremove].
  rewrite !if_true by auto. reflexivity.
Qed.

Lemma hhs3_p6_F2_ifs {A: Type} {P Q: Prop} (b: {P} + {Q}) (x: A) : (if b then x else x) = x.
Proof. destruct b; reflexivity. Qed.

(* the table TB2 opened: kb's entry as the keypair's field, pa's handshake entry as the peer's field *)
Lemma hhs3_p6_F2_open tab pb k idx : k <> hs_addr pb ->
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
  rewrite !hhs3_p6_F2_ifs.
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

Lemma hhs3_p6_F2_openB L V kb : kb <> hs_addr (l_pa L) ->
  @field_compatible Noise.CS t_kp [] kb -> @field_compatible Noise.CS t_peer [] (l_pa L) ->
  itable Tsh (l_itb L) (hhs3_p6_TB2 L V kb) =
  @data_at Noise.CS Tsh t_itab kb (l_itb L) *
  @field_at W_handshake Ews t_kp (DOT HC._entry)
    (l_pa L, (nullval, (Vtrue, (Vint IDX_KEYPAIR, Vint (s_idx (w_Q V)))))) kb *
  @field_at W_handshake Tsh t_peer (DOT HC._handshake DOT HC._entry)
    (l_pa L, (nullval, (Vfalse, (Vint IDX_HANDSHAKE, Vint (s_idx (w_Q V)))))) (l_pa L).
Proof. intros. unfold hhs3_p6_TB2, hhs3_p6_EA1. apply hhs3_p6_F2_open; auto. Qed.

Lemma hhs3_p6_F2_vp sh p P : sepalg.nonidentity sh -> peer_rep sh p P |-- valid_pointer p.
Proof.
  intros N. unfold peer_rep. apply andp_left2. repeat apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; auto; reflexivity.
Qed.

(* hs_zeroed_from on the zeroed handshake *)
Lemma hhs3_p6_F2_zeroed T T' a E H :
  zeroed_from (snap_of T a E H) (snap_of T' a E (hs_zero H)) = true.
Proof.
  unfold zeroed_from, snap_of, hs_zero, is_zero, bytes_eqb;
    cbn [sn_hs sn_entry hs_state hs_rindex hs_eph hs_reph hs_hash hs_ck hs_lic hs_sid hs_rstatic hs_ss hs_psk hs_ts].
  rewrite !Int.eq_true, Int64.eq_true.
  repeat (rewrite if_true by (try reflexivity; try (rewrite Zlength_zeros; reflexivity))).
  reflexivity.
Qed.

Lemma hhs3_p6_F2_hsPA x V : p_hs (hhs3_p6_PAa x V) = w_H2 V.
Proof. reflexivity. Qed.

Lemma hhs3_p6_F2_hsPA4 x V kb : p_hs (hhs3_p6_PA4 x V kb) = hs_zero (w_H2 V).
Proof. reflexivity. Qed.

Lemma hhs3_p6_F2_zeroedB x L V kb :
  zeroed_from (snap_of (hhs3_TB1 L (w_Q V)) (hs_addr (l_pa L)) (hhs3_p6_EA1 L V) (p_hs (hhs3_p6_PAa x V)))
    (snap_of (hhs3_p6_TB2 L V kb) (hs_addr (l_pa L)) (hhs3_p6_EA1 L V) (p_hs (hhs3_p6_PA4 x V kb))) = true.
Proof. rewrite hhs3_p6_F2_hsPA, hhs3_p6_F2_hsPA4. apply hhs3_p6_F2_zeroed. Qed.

Lemma hhs3_p6_F2_cmp x L V kb : kb <> hs_addr (l_pa L) -> hs_sid (w_H2 V) = id_addr (l_wb L) ->
  hs_cmp_pre (snap_of (hhs3_TB1 L (w_Q V)) (hs_addr (l_pa L)) (hhs3_p6_EA1 L V) (p_hs (hhs3_p6_PAa x V)))
    (hhs3_p6_TB2 L V kb) (l_pa L) (l_wb L) (hhs3_p6_PA4 x V kb) (hhs3_p6_EA1 L V).
Proof.
  intros Hne Hsid. unfold hs_cmp_pre. rewrite hhs3_p6_F2_TB1, hhs3_p6_F2_hsPA, hhs3_p6_F2_hsPA4.
  unfold hhs3_p6_TB2, t_entry, snap_of; cbn [t_D t_L sfind sn_entry sn_hs sn_next succ_in].
  rewrite if_false by (intro E; apply Hne; exact E). rewrite !if_true by reflexivity.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hsid|].
  split; [exact Hsid | left; reflexivity].
Qed.

Lemma hhs3_p6_F2_vinB L V kb : vin kb (t_L (hhs3_p6_TB2 L V kb)) = true.
Proof. unfold hhs3_p6_TB2, vin; cbn [t_L]. destruct (in_dec eq_dec kb [kb]) as [_|N]; [reflexivity | exfalso; apply N; left; auto]. Qed.

Lemma hhs3_p6_F2_lenB L V kb : Zlength (t_L (hhs3_p6_TB2 L V kb)) = 1.
Proof. reflexivity. Qed.

Lemma hhs3_p6_F2_eqb_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

Ltac hhs3_p6_F2_absurd :=
  first [ discriminate | contradiction | exfalso; apply Int.one_not_zero; assumption
        | match goal with H: typed_false _ _ |- _ => inv H end ].

Local Open Scope Z_scope.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p6_F2_ok {Espec: OracleKind} gv L FR V :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hhs3_p6_pure x25519 aead_enc aead_dec -> hhs3_p6_free_stmt x25519 ->
  hhs3_p6_ctx x25519 aead_enc aead_dec L V ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p6_SF x25519 gv L FR V) hhs3_p6_F2
    (overridePost (hhs3_p6_SF x25519 gv L FR V) (hhs3_R gv)).
Proof.
  intros HH HP HF HC. unfold hhs3_p6_SF, hhs3_p6_SEF, hhs3_Delta, hhs3_R, hhs3_p6_F2. simplify_func_tycontext. abbreviate_semax.
  Intros ka kb.
  destruct HH as (HX & HAE & _ & HCM & _). destruct HP as (HFA & HFB & HCK & _).
  destruct (HFA HX HAE L V HC) as (EPB2 & _ & _ & _ & _).
  destruct (HFB HX HAE L V HC) as (Est & Eri & Esid & Esnd & _).
  pose proof (HCK HCM HX HAE L V HC) as Eck.
  pose proof (hhs3_p6_F2_KB V Est Eri Eck) as EKB.
  pose proof (hhs3_p6_F2_KA x25519 L V EPB2) as EKA.
  unfold hhs3_p6_sep, hhs3_globs, hhs3_setup_sep, hhs3_p6_locals, hhs3_lvars, hhs3_cnt_temps; cbn [app].
  assert_PROP (@field_compatible Noise.CS t_peer [] (l_pa L)) as FCpa by (unfold peer_rep; entailer!).
  rewrite (hhs3_p6_F2_kp_open ka), (hhs3_p6_F2_kp_open kb). Intros.
  match goal with Hk: field_compatible t_kp [] kb |- _ => rename Hk into FCkb end.
  match goal with Hk: field_compatible t_kp [] ka |- _ => rename Hk into FCka end.
  assert (Hne: kb <> hs_addr (l_pa L)).
  { intro E; match goal with Hn: ~ In kb _ |- _ => apply Hn end. rewrite hhs3_p6_F2_TB1, E. left; reflexivity. }
  rewrite (hhs3_p6_F2_openB L V kb Hne FCkb FCpa).
  unfold hhs3_p6_F2_kpread. rewrite EKA, EKB. cbn [kp_send kp_recv sk_key sk_birth sk_valid kp_refs kp_id kp_rindex kp_init].
  rewrite hhs3_p6_F2_resp. Intros.
  (* CHECK(birthdates == now_a) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  - apply ENTAIL_refl.
  - forward. forward_if (temp HC._t'189 (Vint Int.one)).
    { forward. forward. entailer!. rewrite Int64.eq_true. reflexivity. }
    { match goal with Hn: w_nowa V <> w_nowa V |- _ => exfalso; apply Hn; reflexivity end. }
    forward_if.
    { discriminate. }
    forward. entailer!.
  - forward. apply ENTAIL_refl.
  - (* CHECK(refcount == 1 && entry.type == KEYPAIR && entry.peer == &pa) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward. forward_if (temp HC._t'190 (Vint Int.one)).
    { forward. forward. entailer!. }
    { match goal with Hn: _ |- _ => exfalso; apply Hn; reflexivity end. }
    forward_if (temp HC._t'191 (Vint Int.one)).
    { forward. forward.
      2: { entailer!. rewrite if_true by auto. reflexivity. }
      entailer!.
      apply denote_tc_test_eq_split;
        (pull_left (peer_rep Tsh (l_pa L) (hhs3_p6_PA4 x25519 V kb));
         repeat apply sepcon_valid_pointer1; apply hhs3_p6_F2_vp; auto). }
    { discriminate. }
    forward_if.
    { discriminate. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  (* CHECK(entry.index == m2->sender_index && table_has && table_len == 1) *)
  assert (EM2: rm_sender (hhs3_M2m x25519 (w_R V) (w_M2 V)) = rm_sender (w_M2 V)) by reflexivity.
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward. forward.
    sep_apply (derives_refl' _ _ (eq_sym (hhs3_p6_F2_openB L V kb Hne FCkb FCpa))).
    forward_if (temp HC._t'192 (Vint Int.one)).
    { forward_call (Tsh, l_itb L, hhs3_p6_TB2 L V kb, kb).
      { entailer!. unfold eval_field; simpl. rewrite isptr_offset_val_zero by (destruct FCkb; auto). reflexivity. }
      { unfold hhs3_p6_TB2; cbn; left; reflexivity. }
      rewrite (hhs3_p6_F2_vinB L V kb).
      forward. entailer!. }
    { match goal with Hn: s_idx _ <> _ |- _ => exfalso; apply Hn; rewrite ?EM2, Esnd; reflexivity end. }
    forward_if (temp HC._t'194 (Vint Int.one)).
    { forward_call (Tsh, l_itb L, hhs3_p6_TB2 L V kb). rewrite (hhs3_p6_F2_lenB L V kb).
      forward. entailer!. }
    { discriminate. }
    forward_if.
    { discriminate. }
    forward. rewrite (hhs3_p6_F2_openB L V kb Hne FCkb FCpa). entailer!. }
  { forward. apply ENTAIL_refl. }
  (* CHECK(!pa.handshake.entry.hashed && hs_zeroed_from(&snap, &pa.handshake)) *)
  unfold hhs3_p6_snapB.
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward.
    sep_apply (derives_refl' _ _ (eq_sym (hhs3_p6_F2_openB L V kb Hne FCkb FCpa))).
    forward_if (temp HC._t'196 (Vint Int.one)).
    { forward_call (Tsh, l_snap L,
        snap_of (hhs3_TB1 L (w_Q V)) (hs_addr (l_pa L)) (hhs3_p6_EA1 L V) (p_hs (hhs3_p6_PAa x25519 V)),
        Tsh, l_pa L, hhs3_p6_PA4 x25519 V kb, Tsh, l_itb L, hhs3_p6_TB2 L V kb, hhs3_p6_EA1 L V,
        Tsh, l_wb L, hhs3_DB x25519 (w_R V) L).
      { apply hhs3_p6_F2_cmp; auto. }
      rewrite (hhs3_p6_F2_zeroedB x25519 L V kb).
      forward. entailer!. }
    { contradiction. }
    forward_if.
    { discriminate. }
    forward. rewrite (hhs3_p6_F2_openB L V kb Hne FCkb FCpa). entailer!. }
  { forward. apply ENTAIL_refl. }
  (* CHECK(kb->internal_id == id_a + 1) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward. forward_if.
    { match goal with Hn: Int.repr (Z.b2z (Int64.eq _ _)) = Int.zero |- _ => vm_compute in Hn; discriminate end. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  (* CHECK(ka's sending = kb's receiving && ka's receiving = kb's sending) *)
  pose proof H4 as (LK1 & LK2 & _). rewrite EKA in LK1, LK2. cbn [kp_send kp_recv sk_key] in LK1, LK2.
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward_call (Ews, offset_val 32 ka, kdf1 (hhs3_p6_ck V) [], Ews, offset_val 88 kb, kdf1 (hhs3_p6_ck V) []).
    rewrite hhs3_p6_F2_eqb_refl.
    forward_if (temp HC._t'199 (Vint Int.one)).
    { forward_call (Ews, offset_val 88 ka, kdf2 (hhs3_p6_ck V) [], Ews, offset_val 32 kb, kdf2 (hhs3_p6_ck V) []).
      rewrite hhs3_p6_F2_eqb_refl.
      forward. entailer!. }
    { hhs3_p6_F2_absurd. }
    forward_if. { hhs3_p6_F2_absurd. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  (* the post: SF *)
  unfold POSTCONDITION, abbreviate. rewrite overridePost_normal'.
  Exists ka kb. unfold hhs3_p6_sep, hhs3_globs, hhs3_setup_sep, hhs3_p6_locals, hhs3_lvars, hhs3_cnt_temps; cbn [app].
  unfold hhs3_p6_snapB.
  rewrite hhs3_p6_F2_resp, (hhs3_p6_F2_kp_open ka), (hhs3_p6_F2_kp_open kb), (hhs3_p6_F2_openB L V kb Hne FCkb FCpa).
  unfold hhs3_p6_F2_kpread. rewrite EKA, EKB. cbn [kp_send kp_recv sk_key sk_birth sk_valid kp_refs kp_id kp_rindex kp_init].
  rewrite <- EKA, <- EKB.
  entailer!.
Qed.

End Seg.
