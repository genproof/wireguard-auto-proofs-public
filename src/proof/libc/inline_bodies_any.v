(* The shared byte inlines memzero_explicit and get_unaligned_le32 (static inline in the kernel headers, the same
   Clight in every unit that compiles them), proved for ANY compspecs.  The earlier proofs (b2s_small_body3.v)
   are under Blake2s.CS, which a per-law program without blake2s.c (the AEAD and ChaCha20/Poly1305 laws) does not
   contain; these move into every program by asm_lib's asm_body_lift. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.chacha20poly1305.code.

Local Open Scope Z_scope.

Section InlinesAny.
Context {cs: compspecs}.

(* memzero_explicit(p, n) = memset(p, 0, n) *)
Lemma inl_body_memzero_explicit :
  semax_body nil [@memset_spec cs] WgNoise.chacha20poly1305.code.f_memzero_explicit (@memzero_explicit_spec cs).
Proof.
  start_function.
  forward_call (sh, p, 0, n).
  forward.
Qed.

(* A byte stored as a value is an unsigned char, as a load from a tuchar cell requires. *)
Lemma inl_is_int_Vubyte (b: byte) : is_int I8 Unsigned (Vubyte b).
Proof.
  simpl. unfold Vubyte. simpl. rewrite Int.unsigned_repr; pose proof (Byte.unsigned_range_2 b); rep_lia.
Qed.

(* get_unaligned_le32(p + i): the little-endian word at byte offset i *)
Lemma inl_body_get_unaligned_le32 :
  semax_body nil nil WgNoise.chacha20poly1305.code.f_get_unaligned_le32 (@get_unaligned_le32_spec cs).
Proof.
  start_function.
  assert_PROP (field_compatible (tarray tuchar (Zlength bs)) [] p) by entailer!.
  rewrite (split2_data_at_Tarray_tuchar sh (Zlength bs) i) by (rewrite ?Zlength_map; lia).
  change (Tarray tuchar (Zlength bs) noattr) with (tarray tuchar (Zlength bs)).
  rewrite arr_field_address0 by (auto; lia). simpl sizeof. rewrite Z.mul_1_l.
  rewrite !sublist_map. Intros.
  forward.
  forward; [entailer!; try rewrite Znth_map by list_solve; apply inl_is_int_Vubyte|].
  forward; [entailer!; try rewrite Znth_map by list_solve; apply inl_is_int_Vubyte|].
  forward; [entailer!; try rewrite Znth_map by list_solve; apply inl_is_int_Vubyte|].
  forward; [entailer!; try rewrite Znth_map by list_solve; apply inl_is_int_Vubyte|].
  rewrite !Znth_map by list_solve. rewrite !Znth_sublist by list_solve.
  forward.
  apply andp_right.
  - apply prop_right. unfold le32_at, le32_of, Vubyte. simpl. rewrite !(Z.add_comm _ i). reflexivity.
  - rewrite (split2_data_at_Tarray_tuchar sh (Zlength bs) i) by list_solve.
    change (Tarray tuchar (Zlength bs) noattr) with (tarray tuchar (Zlength bs)).
    rewrite arr_field_address0 by (auto; lia). simpl sizeof. rewrite Z.mul_1_l, !sublist_map. cancel.
Qed.

End InlinesAny.
