(* law cookie_reply: segment C of phase P5 (statements 41..44: the header CHECK, xchacha20poly1305_encrypt, the enc CHECK, the CHECK msg == copy).  hcy5_p5_T2 -> hcy5_S5.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p5_defs.
Require Import WgNoise.proof.libc.libc_bytes.
Require WgNoise.harness.x_cookie_reply.code.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Helpers                                                                 *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hcy5_p5_c_cce_K : change_composite_env Cookie.CS W_cookie_reply.
Proof. make_cs_preserve Cookie.CS W_cookie_reply. Defined.

Lemma hcy5_p5_c_eqb_refl l : bytes_eqb l l = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec l l); congruence. Qed.

Lemma hcy5_p5_c_MAC_len k m : Zlength (MAC k m) = 16.
Proof. unfold MAC, blake2s, b2s_digest_stream, b2s_out. rewrite Zlength_map. reflexivity. Qed.

(* the reply at the world: the two loaded fields, the nonce (offset 8) and the encrypted cookie (offset 32) *)
Definition hcy5_p5_c_cm (sh: share) (rp: val) (CM: cookie_msg) : mpred :=
  (field_at sh t_cmsg (DOT HY._header DOT HY._type) (Vint (cm_type CM)) rp *
   field_at sh t_cmsg (DOT HY._receiver_index) (Vint (cm_receiver CM)) rp *
   hbytes sh (cm_nonce CM) (offset_val 8 rp) *
   hbytes sh (cm_enc CM) (offset_val 32 rp))%logic.

Lemma hcy5_p5_c_cm_open sh rp CM :
  cmsg_rep sh rp CM = (!! (cm_ok CM /\ field_compatible t_cmsg [] rp) && hcy5_p5_c_cm sh rp CM)%logic.
Proof.
  unfold cmsg_rep, hcy5_p5_c_cm, cmsg_val.
  erewrite (@data_at_change_composite Cookie.CS W_cookie_reply _ sh t_cmsg _ _ (JMeq_refl _))
    by prove_cs_preserve_type.
  apply pred_ext.
  - Intros. pose proof H as (L1 & L2).
    assert_PROP (field_compatible t_cmsg [] rp) as FC by entailer!.
    unfold hbytes. rewrite L1, L2. rewrite !(@data_at_tarray_tuchar_cs HCS W_cookie_reply).
    unfold_data_at (data_at _ t_cmsg _ rp).
    rewrite (field_at_data_at sh t_cmsg (DOT HY._nonce)), (field_at_data_at sh t_cmsg (DOT HY._encrypted_cookie)).
    rewrite !field_address_offset by (destruct FC as (?&?&?&?&?); repeat split; auto; compute; tauto).
    simpl nested_field_type. simpl nested_field_offset.
    unfold_field_at 1%nat.
    entailer!.
  - Intros. pose proof H as (L1 & L2).
    unfold hbytes. rewrite L1, L2. rewrite !(@data_at_tarray_tuchar_cs HCS W_cookie_reply).
    unfold_data_at (data_at _ t_cmsg _ rp).
    rewrite (field_at_data_at sh t_cmsg (DOT HY._nonce)), (field_at_data_at sh t_cmsg (DOT HY._encrypted_cookie)).
    rewrite !field_address_offset by (destruct H0 as (?&?&?&?&?); repeat split; auto; compute; tauto).
    simpl nested_field_type. simpl nested_field_offset.
    unfold_field_at 3%nat.
    entailer!.
Qed.

(* byte buffers: splits (template hcy5_p5_a_split, hck3_p5_fc_shrink) *)
Section HCSb.
#[local] Existing Instance HCS.

Lemma hcy5_p5_c_split sh l k p : 0 <= k <= Zlength l ->
  field_compatible (tarray tuchar (Zlength l)) [] p ->
  hbytes sh l p = (hbytes sh (sublist 0 k l) p * hbytes sh (sublist k (Zlength l) l) (offset_val k p))%logic.
Proof.
  intros Hk FC. unfold hbytes.
  rewrite (split2_data_at_Tarray_tuchar sh (Zlength l) k) by (unfold bytes; try rewrite Zlength_map; lia).
  rewrite !Zlength_sublist by lia. unfold bytes. rewrite !sublist_map.
  replace (k - 0) with k by lia.
  rewrite field_address0_offset.
  2: { apply field_compatible_field_compatible0 in FC.
       destruct FC as (?&?&?&?&?); repeat split; auto; simpl; lia. }
  simpl. rewrite Z.mul_1_l. reflexivity.
Qed.

Lemma hcy5_p5_c_fc_shrink k n p : 0 <= k <= n ->
  field_compatible (tarray tuchar n) [] p -> field_compatible (tarray tuchar k) [] p.
Proof.
  intros Hk (H1 & H2 & H3 & H4 & H5).
  assert (A: forall (ce: composite_env) z, align_compatible_rec ce (tarray tuchar k) z).
  { intros. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  repeat split; auto.
  - destruct p; try contradiction. unfold size_compatible in *. simpl sizeof in *.
    rewrite Z.max_r in * by lia. lia.
  - destruct p; try contradiction. apply A.
Qed.

Lemma hcy5_p5_c_split3 sh l a b p : 0 <= a <= b -> b <= Zlength l ->
  field_compatible (tarray tuchar (Zlength l)) [] p ->
  hbytes sh l p =
  (hbytes sh (sublist 0 a l) p * hbytes sh (sublist a b l) (offset_val a p) *
   hbytes sh (sublist b (Zlength l) l) (offset_val b p))%logic.
Proof.
  intros Ha Hb FC.
  rewrite (hcy5_p5_c_split sh l b p) by (auto; lia).
  assert (L0: Zlength (sublist 0 b l) = b) by (rewrite Zlength_sublist; lia).
  assert (FC0: field_compatible (tarray tuchar (Zlength (sublist 0 b l))) [] p)
    by (rewrite L0; apply (hcy5_p5_c_fc_shrink _ (Zlength l)); [lia | exact FC]).
  rewrite (hcy5_p5_c_split sh (sublist 0 b l) a p) by (auto; lia).
  rewrite L0, !sublist_sublist by lia. rewrite !Z.add_0_r. reflexivity.
Qed.

Lemma hcy5_p5_c_hbytes_fc sh l p : hbytes sh l p |-- !! field_compatible (tarray tuchar (Zlength l)) [] p.
Proof. unfold hbytes. entailer!. Qed.

Lemma hcy5_p5_c_hbytes_out sh bs p : hbytes sh bs p |-- hout sh (Zlength bs) p.
Proof. unfold hbytes, hout. apply data_at_data_at_. Qed.

End HCSb.

(* byte buffers at the world (the AEAD's specification is at W) *)
Lemma hcy5_p5_c_hW sh bs p :
  hbytes sh bs p = @data_at W_cookie_reply sh (tarray tuchar (Zlength bs)) (map Vubyte bs) p.
Proof. unfold hbytes, bytes. apply data_at_tarray_tuchar_cs. Qed.

Lemma hcy5_p5_c_hprim sh bs p : 0 < Zlength bs -> hbytes sh bs p = @prim_bytes W_cookie_reply sh bs p.
Proof.
  intros Hl. unfold prim_bytes. rewrite if_false by lia. apply hcy5_p5_c_hW.
Qed.

Lemma hcy5_p5_c_houtW sh n p : hout sh n p = @data_at_ W_cookie_reply sh (tarray tuchar n) p.
Proof. unfold hout. apply data_at__tarray_tuchar_cs. Qed.

Lemma hcy5_p5_c_zp gv : @zero_page Noise.CS gv = @zero_page W_cookie_reply gv.
Proof. unfold zero_page. apply data_at_tarray_tuchar_cs. Qed.

(* msg + len - 32 *)
Lemma hcy5_p5_c_ptr i n k : 0 <= n <= Int64.max_unsigned -> 0 <= k <= Int.max_signed ->
  Ptrofs.sub (Ptrofs.add i (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.repr n))))
    (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr k))) =
  Ptrofs.add i (Ptrofs.repr (n - k)).
Proof.
  intros Hn Hk. rewrite !(Ptrofs.mul_commut (Ptrofs.repr 1)), !Ptrofs.mul_one.
  rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc. f_equal.
  unfold Ptrofs.of_ints, Ptrofs.of_int64. rewrite Int.signed_repr by rep_lia.
  rewrite Int64.unsigned_repr by rep_lia.
  rewrite Ptrofs.neg_repr, ptrofs_add_repr. f_equal; lia.
Qed.

Ltac hcy5_p5_c_dead :=
  exfalso;
  match goal with
  | Hf: ?x <> ?x |- _ => exact (Hf eq_refl)
  | Hf: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hf)
  end.

Lemma hcy5_p5_c_ekey x R L Q rr : cc_ekey (hcy5_CC2 x R L Q rr) = cc_ekey (hcy5_CC1 x R L).
Proof. unfold hcy5_CC2, checker_rotate. destruct (birthdate_expired _ _ _); reflexivity. Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_p5_C_ok {Espec: OracleKind} gv L FR :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcy5_p5_T2 x25519 xaead_enc gv L FR) hcy5_p5_C
    (overridePost (hcy5_S5 x25519 xaead_enc gv L FR) (hcy5_R gv)).
Proof.
  intros HH. unfold hcy5_p5_T2, hcy5_Delta, hcy5_R, hcy5_p5_C. simplify_func_tycontext. abbreviate_semax.
  Intros R S m c rp. Intros Q nonce rr CK CM.
  unfold hcy5_aside0, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_globs, hcy5_lvars. simpl app.
  pose proof H as (HR & HQ & HN & HRR & HCK & HCM).
  pose proof HH as (_ & _ & HX).
  pose proof HQ as (Hn & Hmsg & _).
  set (EK := fst (checker_keys (setup_identity x25519 (r_rawb R)))).
  assert (LCK: Zlength CK = 16)
    by (unfold hcy5_is in HCK; rewrite HCK; unfold hcy5_CK, cookie_of; apply hcy5_p5_c_MAC_len).
  assert_PROP (cc_ok (hcy5_CC2 x25519 R L Q rr)) as Hcc by (unfold checker_rep; entailer!).
  assert (LEK: Zlength EK = 32).
  { destruct Hcc as (_ & L2 & _). rewrite hcy5_p5_c_ekey in L2. exact L2. }
  assert (ECM: cm_type CM = Int.repr 3 /\ cm_receiver CM = q_index Q /\ cm_nonce CM = nonce /\
               cm_enc CM = xaead_enc EK nonce (hcy5_mac1 Q) CK).
  { unfold hcy5_is in HCM. rewrite HCM. repeat split. }
  destruct ECM as (Ety & Erc & Eno & Een).
  rewrite hcy5_p5_c_cm_open. Intros. rename H0 into HCMok, H1 into FCrp. unfold hcy5_p5_c_cm. rewrite Ety, Erc, Eno.
  repeat flatten_sepcon_in_SEP.
  freeze [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;19;20;21;22;23;24;25;26;27;28;29;30;31;32;33;34;35;36;37;38] FA.
  (* CHECK(reply->header.type == MESSAGE_HANDSHAKE_COOKIE && reply->receiver_index == index) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward.
    forward_if (temp HY._t'26 (Vint Int.one)).
    { forward. forward. entailer!. rewrite Int.eq_true. reflexivity. }
    { hcy5_p5_c_dead. }
    forward_if. { hcy5_p5_c_dead. }
    forward. entailer!. }
  { forward. entailer!. }
  thaw FA.
  (* xchacha20poly1305_encrypt(enc, cookie, 16, msg + len - 32, 16, reply->nonce, k) *)
  assert_PROP (@field_compatible HCS (tarray tuchar (Zlength (q_msg Q))) [] m) as FCm.
  { sep_apply (hcy5_p5_c_hbytes_fc Ews (q_msg Q) m). entailer!. }
  rewrite (hcy5_p5_c_split3 Ews (q_msg Q) (q_n Q - 32) (q_n Q - 16) m) by (lia || exact FCm).
  fold (hcy5_mac1 Q).
  assert (LM1: Zlength (hcy5_mac1 Q) = 16) by (unfold hcy5_mac1; rewrite Zlength_sublist; lia).
  unfold wg_consts. rewrite hcy5_p5_c_zp.
  rewrite (hcy5_p5_c_hprim Tsh CK (l_cookie L)) by lia.
  rewrite (hcy5_p5_c_hprim Ews (hcy5_mac1 Q)) by lia.
  rewrite (hcy5_p5_c_hW Ews nonce), (hcy5_p5_c_hW Tsh EK), HN, LEK.
  replace (hout Tsh 32 (l_enc L)) with (hout Tsh (Zlength CK + 16) (l_enc L)) by (rewrite LCK; reflexivity).
  rewrite (hcy5_p5_c_houtW Tsh (Zlength CK + 16)).
  repeat flatten_sepcon_in_SEP.
  forward_call (Tsh, l_enc L, Tsh, l_cookie L, CK, Ews, offset_val (q_n Q - 32) m, hcy5_mac1 Q,
                Ews, offset_val 8 rp, nonce, Tsh, l_k L, EK, gv).
  { destruct FCm as [Pm _]. destruct m; try contradiction. split; exact I. }
  { entailer!. rewrite LCK, LM1. destruct FCm as [Pm _]. destruct m; try contradiction. simpl.
    rewrite hcy5_p5_c_ptr by rep_lia. reflexivity. }
  set (ENC := xaead_enc EK nonce (hcy5_mac1 Q) CK) in *.
  assert (LENC: Zlength ENC = 32) by (unfold ENC; rewrite (xaead_enc_length _ _ HX); lia).
  replace (data_at Tsh (tarray tuchar (Zlength CK + 16)) (map Vubyte ENC) (l_enc L))
    with (hbytes Tsh ENC (l_enc L)) by (rewrite hcy5_p5_c_hW, LENC, LCK; reflexivity).
  rewrite <- (hcy5_p5_c_hprim Tsh CK (l_cookie L)) by lia.
  rewrite <- (hcy5_p5_c_hprim Ews (hcy5_mac1 Q)) by lia.
  replace (data_at Ews (tarray tuchar 24) (map Vubyte nonce) (offset_val 8 rp))
    with (hbytes Ews nonce (offset_val 8 rp)) by (rewrite hcy5_p5_c_hW, HN; reflexivity).
  replace (data_at Tsh (tarray tuchar 32) (map Vubyte EK) (l_k L))
    with (hbytes Tsh EK (l_k L)) by (rewrite hcy5_p5_c_hW, LEK; reflexivity).
  rewrite <- hcy5_p5_c_zp.
  change (hbytes Ews (hcy5_mac1 Q) (offset_val (q_n Q - 32) m))
    with (hbytes Ews (sublist (q_n Q - 32) (q_n Q - 16) (q_msg Q)) (offset_val (q_n Q - 32) m)).
  sep_apply (derives_refl' _ _ (eq_sym (hcy5_p5_c_split3 Ews (q_msg Q) (q_n Q - 32) (q_n Q - 16) m
                                          ltac:(lia) ltac:(lia) FCm))).
  (* CHECK(bytes_eq(reply->encrypted_cookie, enc, 32)) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward_call (Ews, offset_val 32 rp, cm_enc CM, Tsh, l_enc L, ENC).
    { entailer!. destruct HCMok as (_ & L2). rewrite L2. simpl. reflexivity. }
    { destruct HCMok as (_ & L2). rewrite L2. rep_lia. }
    replace (bytes_eqb (cm_enc CM) ENC) with true by (rewrite Een; symmetry; apply hcy5_p5_c_eqb_refl).
    forward_if. { hcy5_p5_c_dead. }
    forward. entailer!. }
  { forward. entailer!. }
  (* CHECK(bytes_eq(msg, copy, len)) *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward_call (Ews, m, q_msg Q, Ews, c, q_msg Q).
    { entailer!. rewrite Hmsg. reflexivity. }
    rewrite hcy5_p5_c_eqb_refl.
    forward_if. { hcy5_p5_c_dead. }
    forward. entailer!. }
  { forward. entailer!. }
  (* the post S5 *)
  unfold POSTCONDITION, abbreviate.
  match goal with |- context [RA_normal (overridePost ?Q ?R')] => change (RA_normal (overridePost Q R')) with Q end.
  unfold hcy5_S5. Exists R S m c rp. Exists Q nonce rr CK CM.
  unfold hcy5_aside0, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrC, hcy5_globs, hcy5_lvars, wg_consts. simpl app.
  rewrite hcy5_p5_c_cm_open. unfold hcy5_p5_c_cm. rewrite Ety, Erc, Eno.
  sep_apply (hcy5_p5_c_hbytes_out Tsh EK (l_k L)). sep_apply (hcy5_p5_c_hbytes_out Tsh ENC (l_enc L)).
  rewrite LEK, LENC.
  entailer!.
Qed.

End Seg.
