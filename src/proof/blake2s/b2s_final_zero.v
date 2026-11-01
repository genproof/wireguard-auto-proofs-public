(* A context zeroed byte by byte (memzero_explicit(ctx, sizeof *ctx) in blake2s_final) is the all-zero
   struct: the statement of b2s_zero_ctx (b2s_zero_ctx.v), proved here for body_blake2s_final. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.spec.

#[local] Existing Instance Blake2s.CS.

(* k zero bytes at (b, ofs) are k one-byte zero mappings *)
Lemma b2s_final_zero_bytes sh b (k: nat) :
  readable_share sh ->
  forall ofs, 0 <= ofs -> ofs + Z.of_nat k <= Ptrofs.max_unsigned ->
  data_at sh (tarray tuchar (Z.of_nat k)) (Zrepeat (Vint Int.zero) (Z.of_nat k)) (Vptr b (Ptrofs.repr ofs))
  |-- mapsto_memory_block.address_mapsto_zeros sh k (b, ofs).
Proof.
  intros Hsh. induction k; intros ofs Hofs Hk.
  - simpl. apply data_at_zero_array_inv; reflexivity.
  - assert_PROP (field_compatible (tarray tuchar (Z.of_nat (S k))) [] (Vptr b (Ptrofs.repr ofs)))
      as Hfc by entailer!.
    rewrite (split2_data_at_Tarray_tuchar sh (Z.of_nat (S k)) 1) by (rewrite ?Zlength_Zrepeat; lia).
    replace (sublist 0 1 (Zrepeat (Vint Int.zero) (Z.of_nat (S k)))) with [Vint Int.zero] by list_solve.
    replace (sublist 1 (Z.of_nat (S k)) (Zrepeat (Vint Int.zero) (Z.of_nat (S k))))
      with (Zrepeat (Vint Int.zero) (Z.of_nat k)) by list_solve.
    replace (Z.of_nat (S k) - 1) with (Z.of_nat k) by lia.
    rewrite field_address0_offset.
    2: { apply field_compatible0_cons. split; [lia | exact Hfc]. }
    simpl offset_val. rewrite Ptrofs.add_unsigned.
    rewrite Ptrofs.unsigned_repr by rep_lia.
    change (nested_field_offset (Tarray tuchar (Z.of_nat (S k)) noattr) (SUB 1)) with 1.
    rewrite (Ptrofs.unsigned_repr 1) by rep_lia.
    simpl mapsto_memory_block.address_mapsto_zeros.
    change (predicates_sl.sepcon ?A ?B) with (A * B)%logic.
    apply sepcon_derives.
    + rewrite (data_at_singleton_array_eq sh tuchar (Vint Int.zero)) by reflexivity.
      rewrite <- (mapsto_data_at' sh tuchar (Vint Int.zero) (Vint Int.zero)); auto.
      2: { destruct Hfc as (Hp & Hl & Hsz & Hal & _). split; auto. split; [reflexivity|].
           split. { hnf. rewrite Ptrofs.unsigned_repr by rep_lia.
                    change (sizeof tuchar) with 1. apply Z.compare_lt_iff. rep_lia. }
           split; [|exact I]. eapply align_compatible_rec_by_value; [reflexivity|]. apply Z.divide_1_l. }
      unfold mapsto. simpl. rewrite if_true by auto.
      rewrite Ptrofs.unsigned_repr by rep_lia.
      apply orp_left.
      * apply andp_left2. apply derives_refl.
      * normalize. discriminate.
    + unfold Z.succ. apply IHk; lia.
Qed.

Lemma b2s_final_zero_ctx sh p :
  readable_share sh ->
  field_compatible t_blake2s_ctx [] p ->
  data_at sh (tarray tuchar 120) (Zrepeat (Vubyte Byte.zero) 120) p |--
  data_at sh t_blake2s_ctx b2s_ctx_zero p.
Proof.
  intros Hsh Hfc.
  assert (E: b2s_ctx_zero = zero_val t_blake2s_ctx).
  { symmetry. apply JMeq_eq. eapply JMeq_trans; [apply JMeq_zero_val_zero_val'|].
    apply JMeq_refl. }
  rewrite E.
  eapply derives_trans; [| apply mapsto_zero_data_at_zero; auto].
  destruct Hfc as (Hp & _ & Hsz & _ & _).
  destruct p; try contradiction.
  hnf in Hsz. change (Ptrofs.unsigned i + 120 < Ptrofs.modulus) in Hsz.
  Transparent mapsto_zeros. unfold mapsto_zeros, mapsto_memory_block.mapsto_zeros. Opaque mapsto_zeros.
  pose proof (Ptrofs.unsigned_range i).
  change (sizeof t_blake2s_ctx) with 120.
  apply andp_right; [apply prop_right; split; lia|].
  rewrite <- (Ptrofs.repr_unsigned i) at 1.
  change 120 with (Z.of_nat 120) at 1 2.
  change (Vubyte Byte.zero) with (Vint Int.zero).
  change (Z.to_nat 120) with 120%nat.
  apply b2s_final_zero_bytes; auto; rep_lia.
Qed.
