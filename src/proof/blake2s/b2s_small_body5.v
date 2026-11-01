(* the small functions of lib/crypto/blake2s.c in the context b2s_Gprog5 (the helper lemmas are
   those of b2s_small_body3.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.b2s_prog5.
Require WgNoise.blake2s.code.
Require Import WgNoise.proof.blake2s.b2s_small_body3.

#[local] Existing Instance Blake2s.CS.
Local Open Scope Z_scope.

Lemma b2s_small_body_ror32 :
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog5 WgNoise.blake2s.code.f_ror32 ror32_spec.
Proof.
  start_function.
  forward.
  - entailer!. rewrite !b2s_small_and31. change (Int.unsigned Int.iwordsize) with 32.
    pose proof (Z.mod_pos_bound (Int.unsigned s) 32 ltac:(lia)).
    pose proof (Z.mod_pos_bound (Int.unsigned (Int.neg s)) 32 ltac:(lia)). lia.
  - entailer!. rewrite b2s_small_ror32_eq. reflexivity.
Qed.

Lemma b2s_small_body_increment_counter :
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog5 WgNoise.blake2s.code.f_blake2s_increment_counter
    blake2s_increment_counter_spec.
Proof.
  start_function.
  forward. forward. forward. forward. forward.
  rewrite b2s_small_carry by auto.
  replace (Int.add (b2s_t0 t) (Int.repr inc)) with (b2s_t0 (t + inc))
    by (unfold b2s_t0; rewrite add_repr; reflexivity).
  entailer!.
Qed.

Lemma b2s_small_body_set_lastblock :
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog5 WgNoise.blake2s.code.f_blake2s_set_lastblock
    blake2s_set_lastblock_spec.
Proof.
  start_function.
  forward.
  entailer!.
Qed.

Lemma b2s_small_body_get_unaligned_le32 :
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog5 WgNoise.blake2s.code.f_get_unaligned_le32
    (@get_unaligned_le32_spec Blake2s.CS).
Proof.
  start_function.
  assert_PROP (field_compatible (tarray tuchar (Zlength bs)) [] p) by entailer!.
  rewrite (split2_data_at_Tarray_tuchar sh (Zlength bs) i) by (rewrite ?Zlength_map; lia).
  change (Tarray tuchar (Zlength bs) noattr) with (tarray tuchar (Zlength bs)).
  rewrite arr_field_address0 by (auto; lia). simpl sizeof. rewrite Z.mul_1_l.
  rewrite !sublist_map. Intros.
  forward.
  forward; [entailer!; try rewrite Znth_map by list_solve; apply b2s_small_is_int_Vubyte|].
  forward; [entailer!; try rewrite Znth_map by list_solve; apply b2s_small_is_int_Vubyte|].
  forward; [entailer!; try rewrite Znth_map by list_solve; apply b2s_small_is_int_Vubyte|].
  forward; [entailer!; try rewrite Znth_map by list_solve; apply b2s_small_is_int_Vubyte|].
  rewrite !Znth_map by list_solve. rewrite !Znth_sublist by list_solve.
  forward.
  apply andp_right.
  - apply prop_right. unfold le32_at, le32_of, Vubyte. simpl. rewrite !(Z.add_comm _ i). reflexivity.
  - rewrite (split2_data_at_Tarray_tuchar sh (Zlength bs) i) by list_solve.
    change (Tarray tuchar (Zlength bs) noattr) with (tarray tuchar (Zlength bs)).
    rewrite arr_field_address0 by (auto; lia). simpl sizeof. rewrite Z.mul_1_l, !sublist_map. cancel.
Qed.

Lemma b2s_small_body_memzero_explicit :
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog5 WgNoise.blake2s.code.f_memzero_explicit
    (@memzero_explicit_spec Blake2s.CS).
Proof.
  start_function.
  forward_call (sh, p, 0, n).
  forward.
Qed.

(* the small functions of lib/crypto/blake2s.c and the shared inlines (blake2s.c's copies) *)
Lemma b2s_small_bodies :
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog5 WgNoise.blake2s.code.f_ror32 ror32_spec /\
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog5 WgNoise.blake2s.code.f_blake2s_increment_counter
    blake2s_increment_counter_spec /\
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog5 WgNoise.blake2s.code.f_blake2s_set_lastblock
    blake2s_set_lastblock_spec /\
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog5 WgNoise.blake2s.code.f_get_unaligned_le32
    (@get_unaligned_le32_spec Blake2s.CS) /\
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog5 WgNoise.blake2s.code.f_memzero_explicit
    (@memzero_explicit_spec Blake2s.CS).
Proof.
  split; [|split; [|split; [|split]]].
  - apply b2s_small_body_ror32.
  - apply b2s_small_body_increment_counter.
  - apply b2s_small_body_set_lastblock.
  - apply b2s_small_body_get_unaligned_le32.
  - apply b2s_small_body_memzero_explicit.
Qed.
