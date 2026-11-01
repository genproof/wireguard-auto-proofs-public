(* A context zeroed byte by byte (memzero_explicit(ctx, sizeof *ctx) in blake2s_final) is the all-zero struct. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.spec.

#[local] Existing Instance Blake2s.CS.

Lemma b2s_zero_bytes sh b :
  readable_share sh ->
  forall (n: nat) i, 0 <= i -> i + Z.of_nat n < Ptrofs.modulus ->
  data_at sh (tarray tuchar (Z.of_nat n)) (Zrepeat (Vint Int.zero) (Z.of_nat n)) (Vptr b (Ptrofs.repr i)) |--
  mapsto_memory_block.address_mapsto_zeros sh n (b, i).
Proof.
  intros Hsh n. induction n; intros i Hi Hn.
  - simpl. rewrite data_at_zero_array_eq; auto. apply derives_refl. exact I.
  - assert_PROP (field_compatible (tarray tuchar (Z.of_nat (S n))) [] (Vptr b (Ptrofs.repr i))) as FC by entailer!.
    replace (Zrepeat (Vint Int.zero) (Z.of_nat (S n)))
      with ([Vint Int.zero] ++ Zrepeat (Vint Int.zero) (Z.of_nat n))
      by (unfold Zrepeat; rewrite !Nat2Z.id; reflexivity).
    rewrite (split2_data_at_Tarray_app 1 (Z.of_nat (S n))) by (try reflexivity; rewrite Zlength_Zrepeat; lia).
    rewrite field_address0_offset by auto with field_compatible.
    rewrite (data_at_singleton_array_eq _ tuchar (Vint Int.zero)) by reflexivity.
    replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia.
    simpl offset_val. rewrite ptrofs_add_repr.
    simpl mapsto_memory_block.address_mapsto_zeros.
    change (predicates_sl.sepcon ?A ?B) with (sepcon A B).
    apply sepcon_derives.
    + erewrite <- (mapsto_data_at' sh tuchar (Vint Int.zero));
        [ | reflexivity | reflexivity | | apply JMeq_refl]; swap 1 2.
      { clear - Hi Hn. repeat split; simpl; auto.
        - rewrite Ptrofs.unsigned_repr by rep_lia; lia.
        - apply align_compatible_rec_by_value with Mint8unsigned; [reflexivity | apply Z.divide_1_l]. }
      unfold mapsto; simpl. rewrite if_true by auto.
      rewrite Ptrofs.unsigned_repr by rep_lia.
      apply orp_left.
      * apply andp_left2. apply derives_refl.
      * apply derives_extract_prop. intros; discriminate.
    + simpl. apply IHn; lia.
Qed.

Lemma b2s_zero_ctx sh p :
  readable_share sh ->
  field_compatible t_blake2s_ctx [] p ->
  data_at sh (tarray tuchar 120) (Zrepeat (Vubyte Byte.zero) 120) p |--
  data_at sh t_blake2s_ctx b2s_ctx_zero p.
Proof.
  intros Hsh FC.
  assert (E: zero_val t_blake2s_ctx = b2s_ctx_zero).
  { apply JMeq_eq. eapply JMeq_trans; [apply JMeq_zero_val_zero_val' | apply JMeq_refl]. }
  rewrite <- E.
  eapply derives_trans; [ | apply mapsto_zero_data_at_zero; auto ].
  destruct FC as [Hp [_ [Hsz _]]]. destruct p; try contradiction.
  simpl in Hsz.
  change (sizeof t_blake2s_ctx) with 120.
  change (mapsto_zeros 120 sh (Vptr b i)) with
    (!! (0 <= Ptrofs.unsigned i /\ 120 + Ptrofs.unsigned i < Ptrofs.modulus) &&
     mapsto_memory_block.address_mapsto_zeros sh (Z.to_nat 120) (b, Ptrofs.unsigned i)).
  rewrite prop_true_andp by (split; rep_lia).
  rewrite <- (Ptrofs.repr_unsigned i) at 1.
  apply (b2s_zero_bytes sh b Hsh 120 (Ptrofs.unsigned i)); rep_lia.
Qed.
