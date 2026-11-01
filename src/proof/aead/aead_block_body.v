(* Body proofs of the ChaCha block functions. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.chacha_block.code.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.aead.aead_spec.
Require Import WgNoise.proof.aead.aead_cce.
Require Import WgNoise.proof.aead.aead_bytes.

Local Open Scope Z_scope.

Local Notation _state := WgNoise.chacha_block.code._state.
Local Notation _out := WgNoise.chacha_block.code._out.
Local Notation _nrounds := WgNoise.chacha_block.code._nrounds.
Local Notation _permuted_state := WgNoise.chacha_block.code._permuted_state.
Local Notation _i := WgNoise.chacha_block.code._i.

Lemma aead_block_Zlength_words_bytes ws : Zlength (words_bytes ws) = 4 * Zlength ws.
Proof.
  induction ws as [|w ws IH]; [reflexivity|].
  unfold words_bytes in *. simpl map. rewrite concat_cons.
  rewrite Zlength_app, IH, Zlength_cons. unfold le32_bytes. rewrite !Zlength_cons, Zlength_nil. lia.
Qed.

Lemma aead_block_words_bytes_snoc (l: list int) i : 0 <= i < Zlength l ->
  words_bytes (sublist 0 (i + 1) l) = words_bytes (sublist 0 i l) ++ le32_bytes (Znth i l).
Proof.
  intros. rewrite (sublist_split 0 i (i + 1)) by lia. rewrite sublist_len_1 by lia.
  unfold words_bytes. rewrite map_app, concat_app. cbn [map concat]. rewrite app_nil_r. reflexivity.
Qed.

Lemma aead_block_Zlength_add_words a b : Zlength a = Zlength b -> Zlength (add_words a b) = Zlength a.
Proof.
  intros. unfold add_words. rewrite Zlength_map.
  rewrite !Zlength_correct in *. rewrite combine_length. lia.
Qed.

Lemma aead_block_Znth_add_words a b i : Zlength a = Zlength b -> 0 <= i < Zlength a ->
  Znth i (add_words a b) = Int.add (Znth i a) (Znth i b).
Proof.
  intros. unfold add_words. rewrite Znth_map.
  - rewrite Znth_combine by auto. reflexivity.
  - rewrite !Zlength_correct in *. rewrite combine_length. lia.
Qed.

Theorem aead_block_bodies :
  @semax_body (QPvarspecs ChachaBlock.qp) (aead_imports_def ChachaBlock.CS ++ aead_G_def) ChachaBlock.CS
    WgNoise.chacha_block.code.f_chacha_block_generic chacha_block_generic_spec /\
  @semax_body (QPvarspecs ChachaBlock.qp) (aead_imports_def ChachaBlock.CS ++ aead_G_def) ChachaBlock.CS
    WgNoise.chacha_block.code.f_hchacha_block_generic hchacha_block_generic_spec.
Proof.
#[local] Existing Instance ChachaBlock.CS.
split.
- start_function.
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
- start_function.
  forward_for_simple_bound 16 (EX i:Z,
    PROP () LOCAL (temp _state state; temp _out out; temp _nrounds (Vint (Int.repr nr));
                   lvar _permuted_state t_chacha_state v_permuted_state)
    SEP (data_at Tsh t_chacha_state (map Vint (sublist 0 i st) ++ Zrepeat Vundef (16 - i)) v_permuted_state;
         data_at ssh t_chacha_state (map Vint st) state; data_at_ osh (tarray tuint 8) out))%assert.
  { entailer!. }
  { forward. forward. entailer!. apply derives_refl'. f_equal. list_solve. }
  rewrite sublist_same, Zrepeat_0, app_nil_r by lia.
  forward_call (Tsh, v_permuted_state, st, nr).
  remember (chacha_rounds (Z.to_nat (nr / 2)) st) as x eqn:Hx.
  assert_PROP (Zlength x = 16) as Hlx.
  { entailer!. clear - H2. destruct H2 as [H2 _].
    change (Zlength (map Vint (chacha_rounds (Z.to_nat (nr / 2)) st)) = Z.max 0 16) in H2.
    rewrite Zlength_map in H2. auto. }
  forward_for_simple_bound 4 (EX i:Z,
    PROP () LOCAL (temp _state state; temp _out out; temp _nrounds (Vint (Int.repr nr));
                   lvar _permuted_state t_chacha_state v_permuted_state)
    SEP (data_at Tsh t_chacha_state (map Vint x) v_permuted_state;
         data_at ssh t_chacha_state (map Vint st) state;
         data_at osh (tarray tuint 8)
           (map Vint (sublist 0 i x) ++ Zrepeat Vundef (4 - i) ++
            map Vint (sublist 12 (12 + i) x) ++ Zrepeat Vundef (4 - i)) out))%assert.
  { entailer!. rewrite sublist_nil. apply derives_refl. }
  { forward. forward. forward. forward.
    entailer!. apply derives_refl'. f_equal. list_solve. }
  sep_apply (data_at_data_at_ Tsh t_chacha_state (map Vint x) v_permuted_state).
  forward_call (Tsh, v_permuted_state).
  entailer!.
  apply derives_refl'. f_equal. unfold hchacha_words. list_solve.
Qed.
