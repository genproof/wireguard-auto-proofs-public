(* law prim_aead: a copy of proof of aead_models_props3.aead_models_ok3: the AEAD models have prim_api's properties. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.aead.aead_model.

Local Open Scope Z_scope.

Lemma hpp3_xor_bytes_inv : forall a b, (length a <= length b)%nat -> xor_bytes (xor_bytes a b) b = a.
Proof.
  unfold xor_bytes; induction a; destruct b; simpl; intros; try lia; auto.
  f_equal.
  - rewrite Byte.xor_assoc, Byte.xor_idem, Byte.xor_zero; auto.
  - apply IHa; lia.
Qed.

Lemma hpp3_xor_bytes_length : forall a b, (length a <= length b)%nat -> length (xor_bytes a b) = length a.
Proof.
  unfold xor_bytes; induction a; destruct b; simpl; intros; try lia; auto.
  f_equal; apply IHa; lia.
Qed.

Lemma hpp3_qround_len : forall x a b c d, Zlength (chacha_qround x a b c d) = Zlength x.
Proof.
  intros; unfold chacha_qround; cbv zeta; rewrite !Zlength_upd_Znth; reflexivity.
Qed.

Lemma hpp3_dround_len : forall x, Zlength (chacha_dround x) = Zlength x.
Proof.
  intros; unfold chacha_dround; do 8 (etransitivity; [apply hpp3_qround_len|]); reflexivity.
Qed.

(* chacha_rounds is unfolded before any conversion (aead_permute_model.v's rounds_S1): the kernel would
   otherwise compare chacha_rounds (S n) x with chacha_rounds n (chacha_dround x) argument by argument and
   evaluate chacha_dround x symbolically (exponential) *)
Lemma hpp3_rounds_S : forall n x, chacha_rounds (S n) x = chacha_rounds n (chacha_dround x).
Proof. intros. unfold chacha_rounds. reflexivity. Qed.

Lemma hpp3_rounds_len : forall n x, Zlength (chacha_rounds n x) = Zlength x.
Proof.
  induction n; intros; [reflexivity|].
  rewrite hpp3_rounds_S, IHn, hpp3_dround_len; reflexivity.
Qed.

Lemma hpp3_words_bytes_len : forall ws, Zlength (words_bytes ws) = 4 * Zlength ws.
Proof.
  induction ws; [reflexivity|].
  unfold words_bytes in *; simpl map; simpl concat.
  rewrite !Zlength_cons, IHws; lia.
Qed.

Lemma hpp3_add_words_len : forall a b, length a = length b -> length (add_words a b) = length a.
Proof.
  unfold add_words; induction a; destruct b; simpl; intros; try lia; auto.
Qed.

Lemma hpp3_block_len : forall n st, Zlength st = 16 -> Zlength (chacha_block_bytes n st) = 64.
Proof.
  intros; unfold chacha_block_bytes, chacha_block_words.
  rewrite hpp3_words_bytes_len.
  rewrite Zlength_correct, hpp3_add_words_len, <- Zlength_correct, hpp3_rounds_len; [lia|].
  rewrite <- !ZtoNat_Zlength, hpp3_rounds_len; reflexivity.
Qed.

Lemma hpp3_advance_len : forall st k, Zlength (chacha_advance st k) = Zlength st.
Proof. intros; unfold chacha_advance; apply Zlength_upd_Znth. Qed.

Lemma hpp3_stream_len : forall n nb st, Zlength st = 16 -> Zlength (chacha_stream n st nb) = 64 * Z.of_nat nb.
Proof.
  induction nb; intros; [reflexivity|]; cbn [chacha_stream].
  rewrite Zlength_app, hpp3_block_len, IHnb by (rewrite ?hpp3_advance_len; auto). lia.
Qed.

Lemma hpp3_nblocks : forall x, 0 <= x -> x <= 64 * Z.of_nat (Z.to_nat (chacha_nblocks x)).
Proof.
  intros; unfold chacha_nblocks.
  assert (0 <= (x + 63) / 64) by (apply Z.div_pos; lia).
  rewrite Z2Nat.id by lia.
  pose proof (Z_div_mod_eq_full (x + 63) 64); pose proof (Z.mod_pos_bound (x + 63) 64). lia.
Qed.

Lemma hpp3_xor_len : forall n st m, Zlength st = 16 -> Zlength (chacha_xor n st m) = Zlength m.
Proof.
  intros; unfold chacha_xor.
  rewrite !Zlength_correct, hpp3_xor_bytes_length; auto.
  apply Nat2Z.inj_le; rewrite <- !Zlength_correct, hpp3_stream_len by auto.
  apply hpp3_nblocks, Zlength_nonneg.
Qed.

Lemma hpp3_xor_inv : forall n st m, Zlength st = 16 -> chacha_xor n st (chacha_xor n st m) = m.
Proof.
  intros.
  unfold chacha_xor at 1; rewrite hpp3_xor_len by auto.
  unfold chacha_xor; apply hpp3_xor_bytes_inv.
  apply Nat2Z.inj_le; rewrite <- !Zlength_correct, hpp3_stream_len by auto.
  apply hpp3_nblocks, Zlength_nonneg.
Qed.

Lemma hpp3_le_bytes_len : forall n z, length (le_bytes n z) = n.
Proof. induction n; simpl; intros; auto. Qed.

Lemma hpp3_tag_len : forall k d, Zlength (poly1305_tag k d) = 16.
Proof. intros; unfold poly1305_tag; rewrite Zlength_correct, hpp3_le_bytes_len; reflexivity. Qed.

Lemma hpp3_enc_len : forall st ad m, Zlength st = 16 -> Zlength (aead_enc_st st ad m) = Zlength m + 16.
Proof.
  intros; unfold aead_enc_st.
  rewrite Zlength_app, hpp3_tag_len, hpp3_xor_len by (rewrite ?hpp3_advance_len; auto). lia.
Qed.

Lemma hpp3_dec_enc : forall st ad m, Zlength st = 16 -> aead_dec_st st ad (aead_enc_st st ad m) = Some m.
Proof.
  intros.
  assert (Hl := hpp3_enc_len st ad m H).
  unfold aead_dec_st; rewrite Hl.
  destruct (Z_lt_dec (Zlength m + 16) 16) as [Hlt|_]; [pose proof (Zlength_nonneg m); lia|].
  unfold aead_enc_st.
  assert (Hc: Zlength (chacha_xor 10 (chacha_advance st 1) m) = Zlength m)
    by (apply hpp3_xor_len; rewrite hpp3_advance_len; auto).
  replace (Zlength m + 16 - 16) with (Zlength (chacha_xor 10 (chacha_advance st 1) m)) by lia.
  rewrite sublist_app1 by (rewrite ?Hc; pose proof (Zlength_nonneg m); lia).
  rewrite sublist_same by lia.
  rewrite sublist_app2 by (rewrite ?Hc; pose proof (Zlength_nonneg m); lia).
  rewrite sublist_same by (rewrite ?hpp3_tag_len; lia).
  match goal with |- context [list_eq_dec ?f ?a ?b] => destruct (list_eq_dec f a b) as [_|Hne]; [|congruence] end.
  f_equal; apply hpp3_xor_inv; rewrite hpp3_advance_len; auto.
Qed.

Lemma hpp3_dec_len : forall st ad c m, Zlength st = 16 -> aead_dec_st st ad c = Some m -> Zlength m = Zlength c - 16.
Proof.
  intros st ad c m H Hd; unfold aead_dec_st in Hd.
  destruct (Z_lt_dec (Zlength c) 16); [discriminate|].
  match type of Hd with context [list_eq_dec ?f ?a ?b] => destruct (list_eq_dec f a b); [|discriminate] end.
  inversion Hd; subst.
  rewrite hpp3_xor_len by (rewrite hpp3_advance_len; auto).
  rewrite Zlength_sublist by lia; lia.
Qed.

Lemma hpp3_dec_short : forall st ad c, Zlength c < 16 -> aead_dec_st st ad c = None.
Proof. intros; unfold aead_dec_st; destruct (Z_lt_dec (Zlength c) 16); [reflexivity|lia]. Qed.

Lemma hpp3_init_len : forall k iv, Zlength (chacha_init_st k iv) = 8 + Zlength k.
Proof.
  intros; unfold chacha_init_st, chacha_consts; rewrite !Zlength_app; rewrite !Zlength_cons, Zlength_nil; lia.
Qed.

Lemma hpp3_le32_words_len : forall bs, Zlength (le32_words 8 bs) = 8.
Proof. intros; unfold le32_words; rewrite Zlength_map; reflexivity. Qed.

Lemma hpp3_aead_st_len : forall k n, Zlength (aead_st k n) = 16.
Proof. intros; unfold aead_st; rewrite hpp3_init_len, hpp3_le32_words_len; reflexivity. Qed.

Lemma hpp3_xaead_st_len : forall k n, Zlength (xaead_st k n) = 16.
Proof.
  intros; unfold xaead_st; rewrite hpp3_init_len.
  unfold xaead_subkey, hchacha_words.
  assert (Zlength (chacha_rounds 10 (chacha_init_st (le32_words 8 k) (sublist 0 16 n))) = 16)
    by (rewrite hpp3_rounds_len, hpp3_init_len, hpp3_le32_words_len; reflexivity).
  rewrite Zlength_app, !Zlength_sublist by lia; lia.
Qed.

Theorem haead_props3_ok : aead_props aead_enc aead_dec /\ xaead_props xaead_enc xaead_dec.
Proof.
  split; constructor; intros.
  - apply hpp3_enc_len, hpp3_aead_st_len.
  - apply hpp3_dec_enc, hpp3_aead_st_len.
  - exact (hpp3_dec_len (aead_st k n) ad c m (hpp3_aead_st_len k n) H).
  - apply hpp3_dec_short; auto.
  - apply hpp3_enc_len, hpp3_xaead_st_len.
  - apply hpp3_dec_enc, hpp3_xaead_st_len.
  - exact (hpp3_dec_len (xaead_st k n) ad c m (hpp3_xaead_st_len k n) H).
  - apply hpp3_dec_short; auto.
Qed.
