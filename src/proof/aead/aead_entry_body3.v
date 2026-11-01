(* body proof of xchacha_init and the four AEAD entry points (size_t lengths), against aead_spec3.aead_G3. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.chacha.code WgNoise.chacha_block.code WgNoise.poly1305.code WgNoise.poly1305_donna32.code
        WgNoise.chacha20poly1305.code WgNoise.shim.code.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.common.wg3_iface.
Require Import WgNoise.proof.aead.aead_spec3.
Require Import WgNoise.proof.aead.aead_cce.
Require Import WgNoise.proof.aead.aead_bytes.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* helpers                                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma ae3_Zlength_le32_words n bs : Zlength (le32_words n bs) = Z.of_nat n.
Proof. unfold le32_words. rewrite !Zlength_map, Zlength_correct, seq_length. reflexivity. Qed.

Lemma ae3_Zlength_qround x a b c d : Zlength (chacha_qround x a b c d) = Zlength x.
Proof. unfold chacha_qround. rewrite !Zlength_upd_Znth. reflexivity. Qed.

Lemma ae3_Zlength_dround x : Zlength (chacha_dround x) = Zlength x.
Proof. unfold chacha_dround. rewrite !ae3_Zlength_qround. reflexivity. Qed.

Lemma ae3_Zlength_rounds n x : Zlength (chacha_rounds n x) = Zlength x.
Proof.
  revert x; induction n; intros x; [reflexivity |].
  change (Zlength ((fix rounds (n : nat) (x : list int) {struct n} : list int :=
                      match n with O => x | S k => rounds k (chacha_dround x) end) n (chacha_dround x))
          = Zlength x).
  transitivity (Zlength (chacha_dround x)).
  - exact (IHn (chacha_dround x)).
  - apply ae3_Zlength_dround.
Qed.

Lemma ae3_Zlength_hchacha_words n st : Zlength st = 16 -> Zlength (hchacha_words n st) = 8.
Proof.
  intros H. unfold hchacha_words. pose proof (ae3_Zlength_rounds n st).
  rewrite Zlength_app, !Zlength_sublist by lia. lia.
Qed.

Lemma ae3_Zlength_init_st k iv : Zlength k = 8 -> Zlength (chacha_init_st k iv) = 16.
Proof. intros H. unfold chacha_init_st. rewrite !Zlength_app, H. reflexivity. Qed.

Lemma ae3_le32_at_prefix bs i : 0 <= i -> i + 4 <= 16 -> 16 <= Zlength bs ->
  le32_at bs i = le32_at (sublist 0 16 bs) i.
Proof. intros. unfold le32_at. rewrite !Znth_sublist by lia. rewrite !Z.add_0_r. reflexivity. Qed.

Lemma ae3_init_st_prefix k iv : 16 <= Zlength iv -> chacha_init_st k iv = chacha_init_st k (sublist 0 16 iv).
Proof.
  intros. unfold chacha_init_st.
  rewrite <- !ae3_le32_at_prefix by lia. reflexivity.
Qed.

Section Ae3Words.
Context {cs: compspecs}.

(* the u32 key words as bytes, for memzero_explicit, and back *)
Lemma ae3_words_to_bytes sh p :
  data_at_ sh (tarray tuint 8) p |-- data_at_ sh (tarray tuchar 32) p.
Proof.
  rewrite data_at__memory_block. Intros. simpl sizeof.
  rewrite (memory_block_data_at_ sh (tarray tuchar 32)); [simpl sizeof; apply derives_refl |].
  destruct H as (? & ? & ? & ? & ?). destruct p; try contradiction. repeat split; auto.
  hnf. apply align_compatible_rec_Tarray. intros. econstructor; [reflexivity |]. simpl. apply Z.divide_1_l.
Qed.

Lemma ae3_bytes_to_words sh p (v: list val) :
  field_compatible (tarray tuint 8) [] p ->
  data_at sh (tarray tuchar 32) v p |-- data_at_ sh (tarray tuint 8) p.
Proof.
  intros Hf. sep_apply data_at_data_at_. rewrite data_at__memory_block. Intros. simpl sizeof.
  rewrite (memory_block_data_at_ sh (tarray tuint 8)); [simpl sizeof; apply derives_refl | auto].
Qed.

Lemma ae3_join_bytes sh n1 n2 (a b: list byte) p :
  Zlength a = n1 -> Zlength b = n2 -> field_compatible (tarray tuchar (n1 + n2)) [] p ->
  data_at sh (tarray tuchar n1) (map Vubyte a) p * data_at sh (tarray tuchar n2) (map Vubyte b) (offset_val n1 p)
  |-- data_at sh (tarray tuchar (n1 + n2)) (map Vubyte (a ++ b)) p.
Proof.
  intros Ha Hb Hf.
  rewrite (split2_data_at_Tarray_tuchar sh (n1 + n2) n1) by list_solve.
  rewrite field_address0_offset.
  2: { apply field_compatible0_cons; simpl; split; [list_solve | auto with field_compatible]. }
  simpl nested_field_offset.
  replace (n1 + n2 - n1) with n2 by lia. rewrite Z.add_0_l, Z.mul_1_l.
  rewrite map_app, sublist_app1, sublist_app2 by list_solve.
  rewrite !Zlength_map, Ha, Z.sub_diag. autorewrite with sublist.
  apply derives_refl.
Qed.

End Ae3Words.

Lemma ae3_xaead_st_eq key nonce :
  chacha_init_st (hchacha_words 10 (chacha_init_st (le32_words 8 key) (sublist 0 16 nonce)))
    (Zrepeat Byte.zero 8 ++ sublist 16 24 nonce) = xaead_st key nonce.
Proof. unfold xaead_st, xaead_subkey. reflexivity. Qed.

Lemma ae3_to_nat_10 : Z.to_nat (20 / 2) = 10%nat.
Proof. reflexivity. Qed.

Lemma ae3_Zlength_le64 v : Zlength (le64_bytes v) = 8.
Proof. reflexivity. Qed.

(* the iv of chacha20poly1305_encrypt/decrypt after put_unaligned_le64(0, iv), put_unaligned_le64(nonce, iv + 8) *)
Definition ae3_iv1 : list val :=
  sublist 0 0 (Zrepeat Vundef 16) ++ map Vubyte (le64_bytes 0) ++
  sublist (0 + 8) (Zlength (Zrepeat Vundef 16)) (Zrepeat Vundef 16).

Lemma ae3_Zlength_iv1 : Zlength ae3_iv1 = 16.
Proof. reflexivity. Qed.

Lemma ae3_iv2 nonce :
  sublist 0 8 ae3_iv1 ++ map Vubyte (le64_bytes nonce) ++ sublist (8 + 8) (Zlength ae3_iv1) ae3_iv1 =
  map Vubyte (aead_iv nonce).
Proof.
  unfold aead_iv. rewrite map_app. rewrite ae3_Zlength_iv1. rewrite sublist_nil. rewrite app_nil_r.
  f_equal.
Qed.

Lemma ae3_Zlength_xaead_st k nonce : Zlength (xaead_st k nonce) = 16.
Proof.
  unfold xaead_st. apply ae3_Zlength_init_st. unfold xaead_subkey. apply ae3_Zlength_hchacha_words.
  apply ae3_Zlength_init_st. apply ae3_Zlength_le32_words.
Qed.

Section EntryBodies3.
#[local] Existing Instance Chacha20poly1305.CS.

Lemma body_xchacha_init3 :
  @semax_body (QPvarspecs Chacha20poly1305.qp) (aead_imports3 Chacha20poly1305.CS ++ aead_G3) Chacha20poly1305.CS
    WgNoise.chacha20poly1305.code.f_xchacha_init xchacha_init_spec.
Proof.
  start_function.
  assert_PROP (field_compatible (tarray tuchar 16) [] v_iv) by entailer!.
  assert_PROP (field_compatible (tarray tuint 8) [] v_k) by entailer!.
  assert_PROP (field_compatible (tarray tuchar 24) [] np) by entailer!.
  rewrite (split2_data_at__Tarray_tuchar Tsh 16 8) by (auto; lia).
  rewrite field_address0_offset by auto with field_compatible. simpl nested_field_offset.
  rewrite (split2_data_at_Tarray_tuchar nsh 24 16) by list_solve.
  rewrite field_address0_offset by auto with field_compatible. simpl nested_field_offset.
  change (16 - 8) with 8. change (24 - 16) with 8. rewrite !sublist_map. Intros.
  forward_call (Tsh, v_iv, 0, 8).
  forward_call (Tsh, nsh, offset_val 8 v_iv, offset_val 16 np, 8, sublist 16 24 nonce). { list_solve. }
  forward_call (Tsh, v_k, ksh, kp, key).
  assert (Hz: Zlength (sublist 0 16 nonce) = 16) by list_solve.
  assert (Hk: Zlength (le32_words 8 key) = 8) by apply ae3_Zlength_le32_words.
  forward_call (sh, state, Tsh, v_k, le32_words 8 key, nsh, np, sublist 0 16 nonce). { rewrite Hz. cancel. }
  rewrite Hz.
  assert (Hs: Zlength (chacha_init_st (le32_words 8 key) (sublist 0 16 nonce)) = 16)
    by (apply ae3_Zlength_init_st; auto).
  remember (chacha_init_st (le32_words 8 key) (sublist 0 16 nonce)) as st0 eqn:Hst0.
  forward_call (sh, state, st0, Tsh, v_k, 20).
  assert (Hsk: Zlength (hchacha_words (Z.to_nat (20 / 2)) st0) = 8) by (apply ae3_Zlength_hchacha_words; auto).
  remember (hchacha_words (Z.to_nat (20 / 2)) st0) as subk eqn:Hsubk.
  sep_apply (ae3_join_bytes Tsh 8 8 (Zrepeat Byte.zero 8) (sublist 16 24 nonce) v_iv). { list_solve. }
  change (8 + 8) with 16.
  assert (Hiv: Zlength (Zrepeat Byte.zero 8 ++ sublist 16 24 nonce) = 16) by list_solve.
  remember (Zrepeat Byte.zero 8 ++ sublist 16 24 nonce) as ivb eqn:Hivb.
  forward_call (sh, state, Tsh, v_k, subk, Tsh, v_iv, ivb).
  { rewrite Hiv. cancel. }
  rewrite Hiv.
  sep_apply (data_at_data_at_ Tsh (tarray tuint 8) (map Vint subk) v_k).
  sep_apply (ae3_words_to_bytes Tsh v_k).
  remember (chacha_init_st subk ivb) as stf eqn:Hstf.
  forward_call (Tsh, v_k, 32).
  sep_apply (ae3_bytes_to_words Tsh v_k); auto.
  sep_apply (ae3_join_bytes nsh 16 8 (sublist 0 16 nonce) (sublist 16 24 nonce) np). { list_solve. }
  change (16 + 8) with 24. rewrite sublist_rejoin, sublist_same by lia.
  assert (Hx: stf = xaead_st key nonce).
  { rewrite Hstf, Hsubk, Hst0, Hivb, ae3_to_nat_10. apply ae3_xaead_st_eq. }
  forward_call (Tsh, v_iv, 16).
  rewrite <- Hx. clear Hx Hstf Hsubk Hst0 Hivb. entailer!.
Qed.

Lemma body_chacha20poly1305_encrypt3 :
  @semax_body (QPvarspecs Chacha20poly1305.qp) (aead_imports3 Chacha20poly1305.CS ++ aead_G3) Chacha20poly1305.CS
    WgNoise.chacha20poly1305.code.f_chacha20poly1305_encrypt chacha20poly1305_encrypt_spec3.
Proof.
  start_function.
  assert_PROP (field_compatible (tarray tuint 8) [] v_k) by entailer!.
  forward_call (Tsh, v_k, ksh, key, k).
  forward_call (0, Tsh, v_iv, 0, Zrepeat Vundef 16). { list_solve. }
  fold ae3_iv1. change (Zlength (Zrepeat Vundef 16)) with 16.
  forward_call (nonce, Tsh, v_iv, 8, ae3_iv1). { rewrite ae3_Zlength_iv1. lia. }
  rewrite ae3_iv2, ae3_Zlength_iv1.
  assert (Hzi: Zlength (aead_iv nonce) = 16) by reflexivity.
  assert (Hk: Zlength (le32_words 8 k) = 8) by apply ae3_Zlength_le32_words.
  remember (le32_words 8 k) as kw eqn:Hkw.
  forward_call (Tsh, v_chacha_state__1, Tsh, v_k, kw, Tsh, v_iv, aead_iv nonce).
  rewrite Hzi.
  assert (Hs: Zlength (chacha_init_st kw (aead_iv nonce)) = 16) by (apply ae3_Zlength_init_st; auto).
  remember (chacha_init_st kw (aead_iv nonce)) as st eqn:Hst.
  forward_call (dsh, dst, ssh, src, m, ash, ad, a, Tsh, v_chacha_state__1, st, gv).
  remember (aead_enc_st st a m) as ct eqn:Hct.
  forward_call (Tsh, v_iv, 16).
  sep_apply (data_at_data_at_ Tsh (tarray tuint 8) (map Vint kw) v_k).
  sep_apply (ae3_words_to_bytes Tsh v_k).
  forward_call (Tsh, v_k, 32).
  sep_apply (ae3_bytes_to_words Tsh v_k); auto.
  assert (Hx: ct = aead_enc k nonce a m) by (rewrite Hct, Hst, Hkw; reflexivity).
  rewrite <- Hx. clear Hx Hct Hst Hkw.
  entailer!.
Qed.

Lemma body_chacha20poly1305_decrypt3 :
  @semax_body (QPvarspecs Chacha20poly1305.qp) (aead_imports3 Chacha20poly1305.CS ++ aead_G3) Chacha20poly1305.CS
    WgNoise.chacha20poly1305.code.f_chacha20poly1305_decrypt chacha20poly1305_decrypt_spec3.
Proof.
  start_function.
  assert_PROP (field_compatible (tarray tuint 8) [] v_k) by entailer!.
  forward_call (Tsh, v_k, ksh, key, k).
  forward_call (0, Tsh, v_iv, 0, Zrepeat Vundef 16). { list_solve. }
  fold ae3_iv1. change (Zlength (Zrepeat Vundef 16)) with 16.
  forward_call (nonce, Tsh, v_iv, 8, ae3_iv1). { rewrite ae3_Zlength_iv1. lia. }
  rewrite ae3_iv2, ae3_Zlength_iv1.
  assert (Hzi: Zlength (aead_iv nonce) = 16) by reflexivity.
  assert (Hk: Zlength (le32_words 8 k) = 8) by apply ae3_Zlength_le32_words.
  remember (le32_words 8 k) as kw eqn:Hkw.
  forward_call (Tsh, v_chacha_state__1, Tsh, v_k, kw, Tsh, v_iv, aead_iv nonce).
  rewrite Hzi.
  assert (Hs: Zlength (chacha_init_st kw (aead_iv nonce)) = 16) by (apply ae3_Zlength_init_st; auto).
  remember (chacha_init_st kw (aead_iv nonce)) as st eqn:Hst.
  forward_call (dsh, dst, old, ssh, src, c, ash, ad, a, Tsh, v_chacha_state__1, st, gv).
  remember (aead_dec_st st a c) as r eqn:Hr.
  forward_call (Tsh, v_chacha_state__1).
  forward_call (Tsh, v_iv, 16).
  sep_apply (data_at_data_at_ Tsh (tarray tuint 8) (map Vint kw) v_k).
  sep_apply (ae3_words_to_bytes Tsh v_k).
  forward_call (Tsh, v_k, 32).
  sep_apply (ae3_bytes_to_words Tsh v_k); auto.
  assert (Hx: r = aead_dec k nonce a c) by (rewrite Hr, Hst, Hkw; reflexivity).
  forward.
  rewrite <- Hx. clear Hx.
  entailer!.
  destruct (aead_dec_st _ a c); reflexivity.
Qed.

Lemma body_xchacha20poly1305_encrypt3 :
  @semax_body (QPvarspecs Chacha20poly1305.qp) (aead_imports3 Chacha20poly1305.CS ++ aead_G3) Chacha20poly1305.CS
    WgNoise.chacha20poly1305.code.f_xchacha20poly1305_encrypt xchacha20poly1305_encrypt_spec3.
Proof.
  start_function.
  forward_call (Tsh, v_chacha_state__1, ksh, key, k, nsh, np, nonce).
  pose proof (ae3_Zlength_xaead_st k nonce) as Hs.
  remember (xaead_st k nonce) as st eqn:Hst.
  forward_call (dsh, dst, ssh, src, m, ash, ad, a, Tsh, v_chacha_state__1, st, gv).
  remember (aead_enc_st st a m) as ct eqn:Hct.
  assert (Hx: ct = xaead_enc k nonce a m) by (rewrite Hct, Hst; reflexivity).
  rewrite <- Hx. clear Hx Hct Hst.
  entailer!.
Qed.

Lemma body_xchacha20poly1305_decrypt3 :
  @semax_body (QPvarspecs Chacha20poly1305.qp) (aead_imports3 Chacha20poly1305.CS ++ aead_G3) Chacha20poly1305.CS
    WgNoise.chacha20poly1305.code.f_xchacha20poly1305_decrypt xchacha20poly1305_decrypt_spec3.
Proof.
  start_function.
  forward_call (Tsh, v_chacha_state__1, ksh, key, k, nsh, np, nonce).
  pose proof (ae3_Zlength_xaead_st k nonce) as Hs.
  remember (xaead_st k nonce) as st eqn:Hst.
  forward_call (dsh, dst, old, ssh, src, c, ash, ad, a, Tsh, v_chacha_state__1, st, gv).
  remember (aead_dec_st st a c) as r eqn:Hr.
  assert (Hx: r = xaead_dec k nonce a c) by (rewrite Hr, Hst; reflexivity).
  clear Hr Hst. subst r.
  forward.
  destruct (xaead_dec k nonce a c); entailer!.
Qed.

End EntryBodies3.

Theorem aead_entry_bodies3 :
  @semax_body (QPvarspecs Chacha20poly1305.qp) (aead_imports3 Chacha20poly1305.CS ++ aead_G3) Chacha20poly1305.CS
    WgNoise.chacha20poly1305.code.f_xchacha_init xchacha_init_spec /\
  @semax_body (QPvarspecs Chacha20poly1305.qp) (aead_imports3 Chacha20poly1305.CS ++ aead_G3) Chacha20poly1305.CS
    WgNoise.chacha20poly1305.code.f_chacha20poly1305_encrypt chacha20poly1305_encrypt_spec3 /\
  @semax_body (QPvarspecs Chacha20poly1305.qp) (aead_imports3 Chacha20poly1305.CS ++ aead_G3) Chacha20poly1305.CS
    WgNoise.chacha20poly1305.code.f_chacha20poly1305_decrypt chacha20poly1305_decrypt_spec3 /\
  @semax_body (QPvarspecs Chacha20poly1305.qp) (aead_imports3 Chacha20poly1305.CS ++ aead_G3) Chacha20poly1305.CS
    WgNoise.chacha20poly1305.code.f_xchacha20poly1305_encrypt xchacha20poly1305_encrypt_spec3 /\
  @semax_body (QPvarspecs Chacha20poly1305.qp) (aead_imports3 Chacha20poly1305.CS ++ aead_G3) Chacha20poly1305.CS
    WgNoise.chacha20poly1305.code.f_xchacha20poly1305_decrypt xchacha20poly1305_decrypt_spec3.
Proof.
  exact (conj body_xchacha_init3 (conj body_chacha20poly1305_encrypt3 (conj body_chacha20poly1305_decrypt3
    (conj body_xchacha20poly1305_encrypt3 body_xchacha20poly1305_decrypt3)))).
Qed.
