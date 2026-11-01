(* The bodies of lib/crypto/chacha-block-generic.c reached by chacha_crypt (rol32, put_unaligned_le32,
   chacha_zeroize_state, chacha_block_generic), each with a context of its callees only: the same specifications
   (aead_spec.v) and the same proofs as aead_small_body3.v and aead_block_body.v, whose context is the whole AEAD
   piece (with the poly1305 and chacha20poly1305.c functions).  A body moves into a per-law program only if every
   function of its context is in the program: these move into every program that links chacha-block-generic.c
   (chacha_permute: chacha_permute_ctx.v; memzero_explicit: the shared inline bodies of any compspecs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.chacha.code WgNoise.chacha_block.code WgNoise.shim.code.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.aead.aead_spec3.
Require Import WgNoise.proof.aead.aead_cce.
Require Import WgNoise.proof.aead.aead_bytes.
Require Import WgNoise.proof.aead.aead_small_body3.
Require Import WgNoise.proof.aead.aead_block_body.

Local Open Scope Z_scope.

Local Notation _state := WgNoise.chacha_block.code._state.
Local Notation _out := WgNoise.chacha_block.code._out.
Local Notation _nrounds := WgNoise.chacha_block.code._nrounds.
Local Notation _permuted_state := WgNoise.chacha_block.code._permuted_state.
Local Notation _i := WgNoise.chacha_block.code._i.

Section ChachaBlockBodiesCtx.
#[local] Existing Instance ChachaBlock.CS.

Lemma body_rol32_ctx :
  @semax_body (QPvarspecs ChachaBlock.qp) nil ChachaBlock.CS
    WgNoise.chacha_block.code.f_rol32 rol32_spec.
Proof.
  start_function.
  forward.
  - entailer!. change 31 with (Z.ones 5). rewrite !Z.land_ones by lia. change (2 ^ 5) with 32.
    change (Int.unsigned Int.iwordsize) with 32.
    pose proof (Z.mod_pos_bound s 32). pose proof (Z.mod_pos_bound (- s) 32).
    rewrite !Int.unsigned_repr by rep_lia. lia.
  - entailer!. rewrite as3_rol by lia. reflexivity.
Qed.

Lemma body_put_unaligned_le32_ctx :
  @semax_body (QPvarspecs ChachaBlock.qp) nil ChachaBlock.CS
    WgNoise.chacha_block.code.f_put_unaligned_le32 put_unaligned_le32_spec.
Proof.
  start_function.
  assert_PROP (field_compatible (tarray tuchar (Zlength old)) [] p) by entailer!.
  rewrite (as3_split3 sh (Zlength old) i 4 old p) by (auto; lia). Intros.
  forward. forward. forward. forward. forward.
  rewrite !Int.zero_ext_idem by lia. rewrite !as3_byte_of, !as3_shru_unsigned by lia.
  rewrite as3_upd4 by list_solve.
  entailer!.
  rewrite (as3_split3 sh (Zlength old) i 4 _ p) by (auto; list_solve).
  autorewrite with sublist.
  apply sepcon_derives; [apply sepcon_derives; [apply derives_refl | ] | ]; apply derives_refl'; f_equal; list_solve.
Qed.

Lemma body_chacha_zeroize_state_ctx :
  @semax_body (QPvarspecs ChachaBlock.qp) [@memzero_explicit_spec ChachaBlock.CS] ChachaBlock.CS
    WgNoise.chacha_block.code.f_chacha_zeroize_state chacha_zeroize_state_spec.
Proof.
  start_function.
  assert_PROP (field_compatible t_chacha_state [] state) as FC by entailer!.
  forward_call (sh, state, 64).
  { rewrite data_at__memory_block, prop_true_andp by auto. change (sizeof t_chacha_state) with 64.
    rewrite memory_block_data_at__tarray_tuchar_eq by rep_lia. cancel. }
  entailer!. sep_apply data_at_data_at_. rewrite <- memory_block_data_at__tarray_tuchar_eq by rep_lia.
  rewrite <- (memory_block_data_at_ sh t_chacha_state state FC). change (sizeof t_chacha_state) with 64. cancel.
Qed.

Lemma body_chacha_block_generic_ctx :
  @semax_body (QPvarspecs ChachaBlock.qp) [chacha_permute_spec; put_unaligned_le32_spec; chacha_zeroize_state_spec]
    ChachaBlock.CS WgNoise.chacha_block.code.f_chacha_block_generic chacha_block_generic_spec.
Proof.
  start_function.
  forward_for_simple_bound 16 (EX i:Z,
    PROP () LOCAL (temp _state state; temp _out out; temp _nrounds (Vint (Int.repr nr));
                   lvar _permuted_state t_chacha_state v_permuted_state)
    SEP (data_at Tsh t_chacha_state (map Vint (sublist 0 i st) ++ Zrepeat Vundef (16 - i)) v_permuted_state;
         data_at ssh t_chacha_state (map Vint st) state; data_at_ osh (tarray tuchar 64) out))%assert.
  { entailer!. }
  { forward. forward. entailer!. apply derives_refl'. f_equal. list_solve. }
  rewrite sublist_same, Zrepeat_0, app_nil_r by lia.
  forward_call (Tsh, v_permuted_state, st, nr).
  remember (chacha_rounds (Z.to_nat (nr / 2)) st) as x eqn:Hx.
  assert_PROP (Zlength x = 16) as Hlx.
  { entailer!. clear - H2. destruct H2 as [H2 _].
    change (Zlength (map Vint (chacha_rounds (Z.to_nat (nr / 2)) st)) = Z.max 0 16) in H2.
    rewrite Zlength_map in H2. auto. }
  forward_for_simple_bound 16 (EX i:Z,
    PROP () LOCAL (temp _state state; temp _out out; temp _nrounds (Vint (Int.repr nr));
                   lvar _permuted_state t_chacha_state v_permuted_state)
    SEP (data_at Tsh t_chacha_state (map Vint x) v_permuted_state;
         data_at ssh t_chacha_state (map Vint st) state;
         data_at osh (tarray tuchar 64)
           (map Vubyte (words_bytes (sublist 0 i (add_words x st))) ++ Zrepeat Vundef (64 - 4 * i)) out))%assert.
  { entailer!. }
  { forward. forward.
    assert (Hlw: Zlength (words_bytes (sublist 0 i (add_words x st))) = 4 * i).
    { rewrite aead_block_Zlength_words_bytes, Zlength_sublist; rewrite ?aead_block_Zlength_add_words; lia. }
    set (old := map Vubyte (words_bytes (sublist 0 i (add_words x st))) ++ Zrepeat Vundef (64 - 4 * i)).
    assert (Hlo: Zlength old = 64) by (subst old; list_solve).
    forward_call (Int.add (Znth i x) (Znth i st), osh, out, 4 * i, old).
    { entailer!. rewrite (Z.mul_comm i 4). apply field_compatible_isptr in H6.
      destruct out; try contradiction. reflexivity. }
    { rewrite Hlo. cancel. }
    rewrite Hlo.
    entailer!. apply derives_refl'. f_equal.
    rewrite aead_block_words_bytes_snoc by (rewrite aead_block_Zlength_add_words; lia).
    rewrite aead_block_Znth_add_words by lia.
    subst old. list_solve. }
  rewrite sublist_same by (rewrite ?aead_block_Zlength_add_words; lia).
  rewrite Zrepeat_0, app_nil_r by lia.
  forward. forward.
  sep_apply (data_at_data_at_ Tsh t_chacha_state (map Vint x) v_permuted_state).
  forward_call (Tsh, v_permuted_state).
  entailer!.
  apply derives_refl'. f_equal. unfold chacha_advance. rewrite upd_Znth_map. reflexivity.
Qed.

End ChachaBlockBodiesCtx.
