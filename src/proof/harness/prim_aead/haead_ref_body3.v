(* law prim_aead: the reference AEADs ref_aead_encrypt/decrypt, ref_xaead_encrypt/decrypt of common.h. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.harness.prim_aead.haead_spec3.
Require Import WgNoise.proof.harness.prim_aead.haead_lemmas3.
Require WgNoise.harness.x_prim_aead.code.

#[local] Existing Instance W_prim_aead.
Local Open Scope Z_scope.

Module HRC := WgNoise.harness.x_prim_aead.code.

(* splitting a byte array for exact-size callees (as hat_split of haead_tag_body3.v) *)
Lemma har_split sh n n1 n2 (l1 l2: list val) p : Zlength l1 = n1 -> Zlength l2 = n2 -> n = n1 + n2 ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) (l1 ++ l2) p =
  (data_at sh (tarray tuchar n1) l1 p * data_at sh (tarray tuchar n2) l2 (offset_val n1 p))%logic.
Proof.
  intros H1 H2 Hn Hf. subst n1 n2 n.
  rewrite (split2_data_at_Tarray_app (Zlength l1) (Zlength l1 + Zlength l2) sh tuchar l1 l2);
    [| reflexivity | exact (ltac:(lia) : Zlength (A:=val) l2 = Zlength l1 + Zlength l2 - Zlength l1)].
  replace (Zlength l1 + Zlength l2 - Zlength l1) with (Zlength l2) by lia.
  rewrite field_address0_offset.
  2: { pose proof (Zlength_nonneg l1); pose proof (Zlength_nonneg l2). auto with field_compatible. }
  simpl nested_field_offset. f_equal. f_equal. f_equal. simpl. lia.
Qed.

Lemma har_aead_st_len key n : Zlength (aead_st key n) = 16.
Proof. reflexivity. Qed.

Lemma har_xor_len (HH: haead_hyps) key n m : Zlength (chacha_xor 10 (chacha_advance (aead_st key n) 1) m) = Zlength m.
Proof.
  destruct HH as (_ & (_ & H & _) & _). apply H. apply haead_advance_length. apply har_aead_st_len.
Qed.

Lemma har_le64_range (HH: haead_hyps) bs : Zlength bs = 8 -> 0 <= le_Z bs <= Int64.max_unsigned.
Proof. destruct HH as (_ & (_ & _ & _ & _ & _ & H & _) & _). apply H. Qed.

Lemma har_encrypt (HH: haead_hyps) :
  semax_body haead_V haead_Gprog HRC.f_ref_aead_encrypt ref_aead_encrypt_spec.
Proof.
  start_function.
  assert_PROP (field_compatible (tarray tuchar (Zlength m + 16)) [] dst) by entailer!.
  pose proof (Zlength_nonneg m).
  unfold data_at_ at 1, field_at_.
  change (default_val (nested_field_type (tarray tuchar (Zlength m + 16)) [])) with
    (Zrepeat Vundef (Zlength m + 16)).
  rewrite <- (Zrepeat_app (Zlength m) 16) by lia.
  fold (data_at dsh (tarray tuchar (Zlength m + 16)) (Zrepeat Vundef (Zlength m) ++ Zrepeat Vundef 16) dst).
  rewrite (har_split dsh (Zlength m + 16) (Zlength m) 16) by (auto; list_solve).
  forward_call (dsh, dst, ssh, src, m, ksh, kp, key, nonce).
  { cancel. }
  remember (chacha_xor 10 (chacha_advance (aead_st key nonce) 1) m) as ct eqn:Hcteq.
  assert (Hct: Zlength ct = Zlength m) by (subst ct; apply har_xor_len, HH).
  rewrite <- Hct.
  forward_call (dsh, offset_val (Zlength ct) dst, ksh, kp, key, nonce, ash, ad, a, dsh, dst, ct, gv).
  rewrite Hct. with_strategy opaque [aead_enc poly1305_tag chacha_xor aead_otk aead_mac_data] entailer!.
  unfold aead_enc, aead_enc_st. cbv zeta. rewrite map_app.
  rewrite (har_split dsh (Zlength m + 16) (Zlength m) 16); [cancel | exact H15 | exact H6 | lia | auto].
Qed.

Lemma har_dec_short key nonce a c : Zlength c < 16 -> aead_dec key nonce a c = None.
Proof. intros. unfold aead_dec, aead_dec_st. destruct (Z_lt_dec (Zlength c) 16); [reflexivity | lia]. Qed.

Lemma har_dec_long key nonce a c : 16 <= Zlength c ->
  aead_dec key nonce a c =
  if list_eq_dec Byte.eq_dec (poly1305_tag (aead_otk (aead_st key nonce)) (aead_mac_data a (sublist 0 (Zlength c - 16) c)))
       (sublist (Zlength c - 16) (Zlength c) c)
  then Some (chacha_xor 10 (chacha_advance (aead_st key nonce) 1) (sublist 0 (Zlength c - 16) c)) else None.
Proof. intros. unfold aead_dec, aead_dec_st. destruct (Z_lt_dec (Zlength c) 16); [lia | reflexivity]. Qed.

Lemma har_len_eq sh n (l: list byte) p : Zlength l = n ->
  data_at sh (tarray tuchar n) (map Vubyte l) p = data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p.
Proof. intros; subst; reflexivity. Qed.

Lemma har_split_c sh (c: list byte) n p : 0 <= n <= Zlength c ->
  field_compatible (tarray tuchar (Zlength c)) [] p ->
  data_at sh (tarray tuchar (Zlength c)) (map Vubyte c) p =
  (data_at sh (tarray tuchar (Zlength (sublist 0 n c))) (map Vubyte (sublist 0 n c)) p *
   data_at sh (tarray tuchar (Zlength (sublist n (Zlength c) c))) (map Vubyte (sublist n (Zlength c) c))
     (offset_val n p))%logic.
Proof.
  intros Hn Hf.
  transitivity (data_at sh (tarray tuchar (Zlength c))
    (map Vubyte (sublist 0 n c) ++ map Vubyte (sublist n (Zlength c) c)) p).
  { rewrite <- map_app, sublist_rejoin, sublist_same by lia. reflexivity. }
  replace (offset_val n p) with (offset_val (Zlength (sublist 0 n c)) p) by (f_equal; list_solve).
  apply har_split; [list_solve | list_solve | list_solve | auto].
Qed.

(* an equation entailer! does not substitute (keeps model terms out of the entailments) *)
Definition har_eq {A: Type} (x y: A) : Prop := x = y.

Ltac har_opaque t := with_strategy opaque [aead_dec aead_enc poly1305_tag chacha_xor aead_otk aead_mac_data aead_st har_eq] t.

Ltac har_ent := with_strategy opaque [aead_dec aead_enc poly1305_tag chacha_xor aead_otk aead_mac_data aead_st] entailer!.

Lemma har_decrypt (HH: haead_hyps) :
  semax_body haead_V haead_Gprog HRC.f_ref_aead_decrypt ref_aead_decrypt_spec.
Proof.
  start_function.
  forward_if (PROP (16 <= Zlength c)
    LOCAL (lvar HRC._tag (tarray tuchar 16) v_tag; gvars gv; temp HRC._dst dst; temp HRC._src src;
      temp HRC._len (Vlong (Int64.repr (Zlength c))); temp HRC._ad ad;
      temp HRC._adlen (Vlong (Int64.repr (Zlength a))); temp HRC._nonce (Vlong (Int64.repr nonce));
      temp HRC._key kp)
    SEP (data_at_ Tsh (tarray tuchar 16) v_tag; data_at dsh (tarray tuchar (Zlength old)) old dst;
      data_at ssh (tarray tuchar (Zlength c)) (map Vubyte c) src;
      data_at ash (tarray tuchar (Zlength a)) (map Vubyte a) ad;
      data_at ksh (tarray tuchar 32) (map Vubyte key) kp; haead_globals gv)).
  { rewrite !Int64.unsigned_repr in H4 by rep_lia.
    forward. rewrite har_dec_short by lia. har_ent. }
  { rewrite !Int64.unsigned_repr in H4 by rep_lia.
    forward. har_ent. }
  Intros.
  assert_PROP (field_compatible (tarray tuchar (Zlength c)) [] src) by har_ent.
  rewrite (har_split_c ssh c (Zlength c - 16)) by (auto; lia).
  flatten_sepcon_in_SEP.
  remember (sublist 0 (Zlength c - 16) c) as ct eqn:Hct.
  remember (sublist (Zlength c - 16) (Zlength c) c) as tg eqn:Htg.
  assert (Hctl: Zlength ct = Zlength c - 16) by (subst ct; list_solve).
  assert (Htgl: Zlength tg = 16) by (subst tg; list_solve).
  change (har_eq ct (sublist 0 (Zlength c - 16) c)) in Hct.
  change (har_eq tg (sublist (Zlength c - 16) (Zlength c) c)) in Htg.
  forward_call (Tsh, v_tag, ksh, kp, key, nonce, ash, ad, a, ssh, src, ct, gv).
  { rewrite Hctl. har_ent. }
  remember (poly1305_tag (aead_otk (aead_st key nonce)) (aead_mac_data a ct)) as T eqn:HT.
  change (har_eq T (poly1305_tag (aead_otk (aead_st key nonce)) (aead_mac_data a ct))) in HT.
  assert_PROP (Zlength T = 16) by (har_ent; rewrite Zlength_map in *; auto).
  rewrite (har_len_eq Tsh 16 T) by auto.
  assert_PROP (isptr src) by har_ent.
  remember (offset_val (Zlength c - 16) src) as q eqn:Hq.
  change (har_eq q (offset_val (Zlength c - 16) src)) in Hq.
  har_opaque ltac:(forward_call (Tsh, v_tag, T, ssh, q, tg)).
  { go_lower; apply prop_right; unfold har_eq in Hq; subst q; rewrite H6; destruct src; try contradiction; cbn.
    f_equal. f_equal. f_equal. unfold Ptrofs.of_int64, Ptrofs.of_ints.
    rewrite Int64.unsigned_repr by rep_lia. rewrite Int.signed_repr by rep_lia.
    rewrite !(Ptrofs.mul_commut (Ptrofs.repr 1)), !Ptrofs.mul_one.
    rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc. f_equal. rewrite <- Ptrofs.sub_add_opp.
    unfold Ptrofs.sub. rewrite !Ptrofs.unsigned_repr by rep_lia. reflexivity. }
  forward_if (PROP (T = tg)
    LOCAL (lvar HRC._tag (tarray tuchar 16) v_tag; gvars gv; temp HRC._dst dst; temp HRC._src src;
      temp HRC._len (Vlong (Int64.repr (Zlength c))); temp HRC._ad ad;
      temp HRC._adlen (Vlong (Int64.repr (Zlength a))); temp HRC._nonce (Vlong (Int64.repr nonce));
      temp HRC._key kp)
    SEP (data_at Tsh (tarray tuchar (Zlength T)) (map Vubyte T) v_tag;
      data_at ssh (tarray tuchar (Zlength tg)) (map Vubyte tg) q;
      data_at ksh (tarray tuchar 32) (map Vubyte key) kp;
      data_at ash (tarray tuchar (Zlength a)) (map Vubyte a) ad;
      data_at ssh (tarray tuchar (Zlength ct)) (map Vubyte ct) src;
      haead_globals gv; data_at dsh (tarray tuchar (Zlength old)) old dst)).
  { destruct (list_eq_dec Byte.eq_dec T tg) as [E | E]; [inv H8 |].
    assert (Hdec: aead_dec key nonce a c = None).
    { rewrite har_dec_long by lia. unfold har_eq in Hct, Htg, HT.
      rewrite <- Hct, <- Htg, <- HT. destruct list_eq_dec; [contradiction | reflexivity]. }
    rewrite H6. sep_apply (data_at_data_at_ Tsh (tarray tuchar 16) (map Vubyte T) v_tag).
    gather_SEP (data_at ssh _ _ src) (data_at ssh _ _ q).
    replace_SEP 0 (data_at ssh (tarray tuchar (Zlength c)) (map Vubyte c) src).
    { go_lower. unfold har_eq in Hct, Htg, Hq. rewrite (har_split_c ssh c (Zlength c - 16)) by (auto; lia).
      rewrite <- Hct, <- Htg, <- Hq. cancel. }
    clear Hct Htg HT Hq.
    subst POSTCONDITION; unfold abbreviate; rewrite Hdec.
    forward. cancel. }
  { destruct (list_eq_dec Byte.eq_dec T tg) as [E | E]; [| contradiction].
    forward. har_ent. }
  Intros. subst tg.
  assert (Hdec: aead_dec key nonce a c = Some (chacha_xor 10 (chacha_advance (aead_st key nonce) 1) ct)).
  { rewrite har_dec_long by lia. unfold har_eq in Hct, Htg, HT.
    rewrite <- Hct, <- Htg, <- HT. destruct list_eq_dec; [reflexivity | contradiction]. }
  clear HT.
  rewrite H6. sep_apply (data_at_data_at_ Tsh (tarray tuchar 16) (map Vubyte T) v_tag).
  replace (Zlength old) with (Zlength ct) by lia.
  forward_call (dsh, dst, ssh, src, ct, ksh, kp, key, nonce).
  { rewrite Hctl. har_ent. }
  gather_SEP (data_at ssh _ _ src) (data_at ssh _ _ q).
  replace_SEP 0 (data_at ssh (tarray tuchar (Zlength c)) (map Vubyte c) src).
  { go_lower. unfold har_eq in Hct, Htg, Hq. rewrite (har_split_c ssh c (Zlength c - 16)) by (auto; lia).
    rewrite <- Hct, <- Htg, <- Hq, H6. cancel. }
  clear Hct Htg Hq.
  subst POSTCONDITION; unfold abbreviate; rewrite Hdec.
  replace (Zlength old) with (Zlength ct) by lia.
  forward. cancel.
Qed.

Lemma har_xencrypt (HH: haead_hyps) :
  semax_body haead_V haead_Gprog HRC.f_ref_xaead_encrypt ref_xaead_encrypt_spec.
Proof.
  start_function.
  assert (HX: haead_facts) by (destruct HH as (_ & HX & _); exact HX).
  rewrite (har_len_eq nsh 24 nonce) by auto.
  forward_call (Tsh, v_sub, ksh, kp, key, nsh, np, nonce).
  assert (He: aead_enc (words_bytes (hchacha_words 10 (chacha_init_st (le32_words 8 key) (sublist 0 16 nonce))))
    (le_Z (sublist 16 24 nonce)) a m = xaead_enc key nonce a m) by (apply haead_xaead_enc; auto).
  change (har_eq (aead_enc (words_bytes (hchacha_words 10 (chacha_init_st (le32_words 8 key) (sublist 0 16 nonce))))
    (le_Z (sublist 16 24 nonce)) a m) (xaead_enc key nonce a m)) in He.
  remember (words_bytes (hchacha_words 10 (chacha_init_st (le32_words 8 key) (sublist 0 16 nonce)))) as sk eqn:Hsk.
  clear Hsk HX.
  assert_PROP (Zlength sk = 32) by (har_ent; rewrite Zlength_map in *; auto).
  assert_PROP (isptr np) by har_ent.
  forward_call (nsh, np, 16, nonce).
  assert (Hn: 0 <= le_Z (sublist 16 24 nonce) <= Int64.max_unsigned) by (apply har_le64_range; auto; list_solve).
  forward_call (dsh, dst, ssh, src, m, ash, ad, a, le_Z (sublist 16 24 nonce), Tsh, v_sub, sk, gv).
  unfold har_eq in He; rewrite He; clear He.
  rewrite H0. har_ent.
Qed.

Lemma har_xdecrypt (HH: haead_hyps) :
  semax_body haead_V haead_Gprog HRC.f_ref_xaead_decrypt ref_xaead_decrypt_spec.
Proof.
  start_function.
  assert (HX: haead_facts) by (destruct HH as (_ & HX & _); exact HX).
  rewrite (har_len_eq nsh 24 nonce) by auto.
  forward_call (Tsh, v_sub, ksh, kp, key, nsh, np, nonce).
  assert (He: aead_dec (words_bytes (hchacha_words 10 (chacha_init_st (le32_words 8 key) (sublist 0 16 nonce))))
    (le_Z (sublist 16 24 nonce)) a c = xaead_dec key nonce a c) by (apply haead_xaead_dec; auto).
  change (har_eq (aead_dec (words_bytes (hchacha_words 10 (chacha_init_st (le32_words 8 key) (sublist 0 16 nonce))))
    (le_Z (sublist 16 24 nonce)) a c) (xaead_dec key nonce a c)) in He.
  remember (words_bytes (hchacha_words 10 (chacha_init_st (le32_words 8 key) (sublist 0 16 nonce)))) as sk eqn:Hsk.
  clear Hsk HX.
  assert_PROP (Zlength sk = 32) by (har_ent; rewrite Zlength_map in *; auto).
  assert_PROP (isptr np) by har_ent.
  forward_call (nsh, np, 16, nonce).
  assert (Hn: 0 <= le_Z (sublist 16 24 nonce) <= Int64.max_unsigned) by (apply har_le64_range; auto; list_solve).
  forward_call (dsh, dst, old, ssh, src, c, ash, ad, a, le_Z (sublist 16 24 nonce), Tsh, v_sub, sk, gv).
  unfold har_eq in He; rewrite He; clear He.
  forward. rewrite H0. har_ent.
Qed.

Lemma haead_ref_bodies3 : haead_hyps ->
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_ref_aead_encrypt ref_aead_encrypt_spec /\
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_ref_aead_decrypt ref_aead_decrypt_spec /\
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_ref_xaead_encrypt ref_xaead_encrypt_spec /\
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_ref_xaead_decrypt ref_xaead_decrypt_spec.
Proof.
  intros HH. split; [| split; [| split]].
  - apply har_encrypt; auto.
  - apply har_decrypt; auto.
  - apply har_xencrypt; auto.
  - apply har_xdecrypt; auto.
Qed.
