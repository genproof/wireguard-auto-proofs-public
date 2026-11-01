(* body proof of chacha_crypt against aead_spec3.aead_G3: the loop of
   the series patch P23 ("lib/crypto: chacha: Take a size_t length in chacha_crypt()"), chunks of
   round_down(UINT_MAX, 64) = 2^32 - 64 bytes to chacha_crypt_generic while more than UINT_MAX bytes remain, then
   the rest in one call; NULL-tolerant destination.  Follows an earlier proof of the P23 helper
   chacha20_crypt_long (same chunk size).  aead_chacha_body3.v has chacha_crypt_generic and chacha20_crypt. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.chacha.code WgNoise.chacha20poly1305.code.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.common.wg3_iface.
Require Import WgNoise.proof.aead.aead_spec3.
Require Import WgNoise.proof.aead.aead_cce.
Require Import WgNoise.proof.aead.aead_bytes.
Require Import WgNoise.proof.aead.aead_long3_model.
Require Import WgNoise.proof.aead.aead_chacha_body3.

Local Open Scope Z_scope.

Section ChachaCrypt3.
#[local] Existing Instance Chacha.CS.

(* chacha_crypt: the series' loop.  Invariant: k bytes done (a multiple of 64, every chunk being 2^32 - 64),
   the state advanced by k / 64 blocks, dst[0..k) = the keystream XOR of m[0..k). *)
Lemma body_chacha_crypt3 :
  @semax_body (QPvarspecs Chacha.qp) (aead_imports3 Chacha.CS ++ aead_G3) Chacha.CS
    WgNoise.chacha.code.f_chacha_crypt chacha_crypt_spec3.
Proof.
  start_function.
  pose proof (Zlength_nonneg m) as Hm0.
  set (nn := Z.to_nat (nr / 2)).
  destruct (Z.eq_dec (Zlength m) 0) as [Hz | Hnz].
  { (* empty: the loop test fails at once; chacha_crypt_generic(state, dst, src, 0, nrounds) *)
    forward_while (@exp (environ -> mpred) _ unit (fun _ =>
      PROP ()
      LOCAL (temp WgNoise.chacha.code._state state; temp WgNoise.chacha.code._dst dst;
             temp WgNoise.chacha.code._src src;
             temp WgNoise.chacha.code._bytes (Vlong (Int64.repr (Zlength m)));
             temp WgNoise.chacha.code._nrounds (Vint (Int.repr nr)))
      SEP (data_at ssh t_chacha_state (map Vint st) state; prim_out dsh (Zrepeat Vundef (Zlength m)) dst;
           prim_bytes msh m src))).
    - Exists tt. entailer!.
    - entailer!.
    - rewrite Hz in HRE. pose proof (Int.unsigned_range (Int.not (Int.repr 0))). lia.
    - forward_call (ssh, state, st, dsh, dst, msh, src, m, nr).
      { rewrite Hz. go_lower. apply prop_right. reflexivity. }
      entailer!. }
  unfold prim_bytes. rewrite if_false by auto.
  rewrite (cb3_out_nz dsh (Zrepeat Vundef (Zlength m)) dst) by (rewrite Zlength_Zrepeat; lia).
  rewrite Zlength_Zrepeat by lia.
  assert_PROP (field_compatible (tarray tuchar (Zlength m)) [] dst) as FCd by entailer!.
  assert_PROP (field_compatible (tarray tuchar (Zlength m)) [] src) as FCs by entailer!.
  pose proof (proj1 FCd) as Pd. pose proof (proj1 FCs) as Ps.
  set (n := Zlength m) in *.
  forward_while (@exp (environ -> mpred) _ Z (fun k =>
    PROP (0 <= k < n; k mod 64 = 0)
    LOCAL (temp WgNoise.chacha.code._state state;
           temp WgNoise.chacha.code._dst (offset_val k dst); temp WgNoise.chacha.code._src (offset_val k src);
           temp WgNoise.chacha.code._bytes (Vlong (Int64.repr (n - k)));
           temp WgNoise.chacha.code._nrounds (Vint (Int.repr nr)))
    SEP (data_at ssh t_chacha_state (map Vint (chacha_advance st (chacha_nblocks k))) state;
         data_at dsh (tarray tuchar n) (map Vubyte (chacha_xor nn st (sublist 0 k m)) ++ Zrepeat Vundef (n - k)) dst;
         data_at msh (tarray tuchar n) (map Vubyte m) src))).
  - Exists 0. entailer!.
    change (chacha_nblocks 0) with 0. rewrite lg3_advance_0 by auto. rewrite app_nil_l. cancel.
  - entailer!.
  - (* a chunk of l = 2^32 - 64 bytes: more than UINT_MAX bytes remain *)
    assert (Hk: 4294967295 < n - k).
    { unfold Int64.ltu in HRE. change (Int.unsigned (Int.not (Int.repr 0))) with 4294967295 in HRE.
      rewrite !Int64.unsigned_repr in HRE by rep_lia. destruct (zlt _ _); [lia | discriminate]. }
    forward.
    (* the chunk, kept symbolic: a numeral 2^32 - 64 here makes Coq reduce Z.to_nat (chacha_nblocks _) in unary *)
    set (l := Z.min 4294967232 (n - k)).
    assert (Hl: 0 < l /\ k + l < n) by (subst l; lia).
    assert (Hl64: l mod 64 = 0) by (subst l; rewrite Z.min_l by lia; reflexivity).
    assert (Hl32: 0 <= l <= Int.max_unsigned) by (subst l; rep_lia).
    replace (Int.and (Int.not (Int.repr 0)) (Int.not (Int.sub (Int.repr 64) (Int.repr 1)))) with (Int.repr l)
      by (subst l; rewrite Z.min_l by lia; reflexivity).
    set (c := sublist k (k + l) m).
    assert (Hc: Zlength c = l) by (subst c; rewrite Zlength_sublist; lia).
    assert (Hx: Zlength (chacha_xor nn st (sublist 0 k m)) = k)
      by (rewrite lg3_Zlength_chacha_xor, Zlength_sublist; lia).
    rewrite (lg3_split3 dsh n k l _ dst) by (auto; try lia; rewrite Zlength_app, Zlength_map, Zlength_Zrepeat; lia).
    rewrite (lg3_split3 msh n k l _ src) by (auto; try lia; rewrite Zlength_map; lia).
    replace (sublist k (k + l) (map Vubyte (chacha_xor nn st (sublist 0 k m)) ++ Zrepeat Vundef (n - k)))
      with (Zrepeat Vundef l) by list_solve.
    rewrite (sublist_map _ k (k + l)). fold c.
    assert (E: data_at msh (tarray tuchar l) (map Vubyte c) (offset_val k src) = prim_bytes msh c (offset_val k src))
      by (unfold prim_bytes; rewrite if_false by lia; rewrite Hc; auto).
    assert (E2: data_at dsh (tarray tuchar l) (Zrepeat Vundef l) (offset_val k dst) =
                prim_out dsh (Zrepeat Vundef (Zlength c)) (offset_val k dst))
      by (rewrite cb3_out_nz by (rewrite Zlength_Zrepeat; lia); rewrite Zlength_Zrepeat, Hc by lia; auto).
    rewrite E, E2.
    forward_call (ssh, state, chacha_advance st (chacha_nblocks k), dsh, offset_val k dst, msh, offset_val k src, c, nr).
    { go_lower. apply prop_right. simpl. rewrite Hc. reflexivity. }
    { rewrite ?Hc. cancel. }
    { rewrite lg3_Zlength_advance; auto. }
    rewrite Hc. fold nn.
    rewrite cb3_out_nz by (rewrite Zlength_map, lg3_Zlength_chacha_xor by (rewrite lg3_Zlength_advance; auto); lia).
    rewrite Zlength_map, lg3_Zlength_chacha_xor by (rewrite lg3_Zlength_advance; auto).
    forward. forward. forward.
    rewrite Int.unsigned_repr by rep_lia.
    Exists (k + l).
    assert (Hn: chacha_nblocks (k + l) = chacha_nblocks k + chacha_nblocks l).
    { assert (Hq: k = 64 * (k / 64)) by (pose proof (Z.div_mod k 64); lia).
      rewrite Hq, lg3_nblocks_add, lg3_nblocks_full; try lia; apply Z.div_pos; lia. }
    rewrite Hn, <- lg3_advance_advance by auto.
    rewrite (sublist_split 0 k (k + l) m) by lia. fold c.
    rewrite lg3_chacha_xor_app by (auto; rewrite Zlength_sublist by lia; rewrite Z.sub_0_r; auto).
    rewrite Zlength_sublist by lia. rewrite Z.sub_0_r.
    rewrite Hc.
    set (S := chacha_advance (chacha_advance st (chacha_nblocks k)) (chacha_nblocks l)) in *.
    set (X := chacha_xor nn st (sublist 0 k m)) in *.
    set (Y := chacha_xor nn (chacha_advance st (chacha_nblocks k)) c) in *.
    assert (HY: Zlength Y = l) by (subst Y; rewrite lg3_Zlength_chacha_xor by (rewrite lg3_Zlength_advance; auto); auto).
    clearbody S X Y.
    rewrite (lg3_split3 dsh n k l _ dst)
      by (auto; try lia; rewrite Zlength_app, Zlength_map, Zlength_app, Zlength_Zrepeat; lia).
    rewrite (lg3_split3 msh n k l _ src) by (auto; try lia; rewrite Zlength_map; lia).
    rewrite (sublist_map _ k (k + l) m). fold c. rewrite E.
    clear E E2 Hn. clearbody c. subst n.
    replace (sublist k (k + l) (map Vubyte (X ++ Y) ++ Zrepeat Vundef (Zlength m - (k + l))))
      with (map Vubyte Y) by list_solve.
    replace (sublist 0 k (map Vubyte (X ++ Y) ++ Zrepeat Vundef (Zlength m - (k + l))))
      with (sublist 0 k (map Vubyte X ++ Zrepeat Vundef (Zlength m - k))) by list_solve.
    replace (sublist (k + l) (Zlength m) (map Vubyte (X ++ Y) ++ Zrepeat Vundef (Zlength m - (k + l))))
      with (sublist (k + l) (Zlength m) (map Vubyte X ++ Zrepeat Vundef (Zlength m - k))) by list_solve.
    replace (Zlength m - k - l) with (Zlength m - (k + l)) by lia.
    rewrite (cb3_add_ptr_uint dst k l Pd Hl32), (cb3_add_ptr_uint src k l Ps Hl32).
    assert (Hmod: (k + l) mod 64 = 0).
    { match goal with H: k mod 64 = 0 |- _ => rewrite Z.add_mod, H, Hl64 by lia end. reflexivity. }
    entailer!.
    all: try (repeat match goal with |- _ /\ _ => split end;
              first [assumption | lia | (f_equal; f_equal; lia)]).
  - (* the rest: 1 .. UINT_MAX bytes in one call *)
    assert (Hk: n - k <= 4294967295).
    { unfold Int64.ltu in HRE. change (Int.unsigned (Int.not (Int.repr 0))) with 4294967295 in HRE.
      rewrite !Int64.unsigned_repr in HRE by rep_lia. destruct (zlt _ _); [discriminate | lia]. }
    set (r := n - k) in *.
    set (c := sublist k n m).
    assert (Hc: Zlength c = r) by (subst c; rewrite Zlength_sublist; lia).
    assert (Hx: Zlength (chacha_xor nn st (sublist 0 k m)) = k)
      by (rewrite lg3_Zlength_chacha_xor, Zlength_sublist; lia).
    rewrite (lg3_split2 dsh n k _ dst) by (auto; try lia; rewrite Zlength_app, Zlength_map, Zlength_Zrepeat; lia).
    rewrite (lg3_split2 msh n k _ src) by (auto; try lia; rewrite Zlength_map; lia).
    replace (sublist k n (map Vubyte (chacha_xor nn st (sublist 0 k m)) ++ Zrepeat Vundef r))
      with (Zrepeat Vundef r) by list_solve.
    replace (sublist 0 k (map Vubyte (chacha_xor nn st (sublist 0 k m)) ++ Zrepeat Vundef r))
      with (map Vubyte (chacha_xor nn st (sublist 0 k m))) by list_solve.
    rewrite (sublist_map _ k n). fold c.
    assert (E: data_at msh (tarray tuchar (n - k)) (map Vubyte c) (offset_val k src) = prim_bytes msh c (offset_val k src))
      by (unfold prim_bytes; rewrite if_false by lia; rewrite Hc; auto).
    assert (E2: data_at dsh (tarray tuchar (n - k)) (Zrepeat Vundef r) (offset_val k dst) =
                prim_out dsh (Zrepeat Vundef (Zlength c)) (offset_val k dst))
      by (rewrite cb3_out_nz by (rewrite Zlength_Zrepeat; lia); rewrite Zlength_Zrepeat, Hc by lia; auto).
    rewrite E, E2.
    forward_call (ssh, state, chacha_advance st (chacha_nblocks k), dsh, offset_val k dst, msh, offset_val k src, c, nr).
    { go_lower. apply prop_right. simpl. rewrite Hc.
      try rewrite Int64.unsigned_repr by rep_lia. try rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia.
      reflexivity. }
    { rewrite ?Hc. cancel. }
    { rewrite lg3_Zlength_advance; auto. }
    fold nn.
    rewrite cb3_out_nz by (rewrite Zlength_map, lg3_Zlength_chacha_xor by (rewrite lg3_Zlength_advance; auto); lia).
    rewrite Zlength_map, lg3_Zlength_chacha_xor by (rewrite lg3_Zlength_advance; auto).
    rewrite cb3_out_nz by (rewrite Zlength_map, lg3_Zlength_chacha_xor; auto).
    rewrite Zlength_map, lg3_Zlength_chacha_xor by auto.
    assert (Hn: chacha_nblocks n = chacha_nblocks k + chacha_nblocks r).
    { assert (Hq: k = 64 * (k / 64)) by (pose proof (Z.div_mod k 64); lia).
      replace n with (k + r) by lia. rewrite Hq, lg3_nblocks_add, lg3_nblocks_full; try lia; apply Z.div_pos; lia. }
    rewrite Hn, <- lg3_advance_advance by auto.
    assert (Hm: m = sublist 0 k m ++ c) by (subst c; rewrite sublist_rejoin, sublist_same; auto; lia).
    unfold prim_bytes. rewrite !if_false by (try rewrite Hc; lia).
    rewrite (lg3_split2 msh n k (map Vubyte m) src) by (auto; try lia; rewrite Zlength_map; lia).
    rewrite (sublist_map _ k n m). fold c. rewrite Hc.
    assert (Exor: chacha_xor nn st m =
                  chacha_xor nn st (sublist 0 k m) ++ chacha_xor nn (chacha_advance st (chacha_nblocks k)) c).
    { rewrite Hm at 1. rewrite lg3_chacha_xor_app by (auto; rewrite Zlength_sublist by lia; rewrite Z.sub_0_r; auto).
      rewrite Zlength_sublist by lia. rewrite Z.sub_0_r. reflexivity. }
    rewrite Exor. clear Exor Hm.
    set (X := chacha_xor nn st (sublist 0 k m)) in *.
    set (Y := chacha_xor nn (chacha_advance st (chacha_nblocks k)) c) in *.
    assert (HY: Zlength Y = r) by (subst Y; rewrite lg3_Zlength_chacha_xor by (rewrite lg3_Zlength_advance; auto); auto).
    assert (HX: Zlength X = k) by (subst X; rewrite lg3_Zlength_chacha_xor, Zlength_sublist by (auto; lia); lia).
    clearbody X Y.
    change (Zlength m) with n.
    rewrite (lg3_split2 dsh n k (map Vubyte (X ++ Y)) dst) by (auto; try lia; rewrite Zlength_map, Zlength_app; lia).
    replace (sublist 0 k (map Vubyte (X ++ Y))) with (map Vubyte X) by list_solve.
    replace (sublist k n (map Vubyte (X ++ Y))) with (map Vubyte Y) by list_solve.
    change (n - k) with r.
    entailer!.
Qed.

End ChachaCrypt3.

Theorem aead_chacha_bodies3 :
  @semax_body (QPvarspecs Chacha.qp) (aead_imports3 Chacha.CS ++ aead_G3) Chacha.CS
    WgNoise.chacha.code.f_chacha_crypt_generic chacha_crypt_generic_spec3 /\
  @semax_body (QPvarspecs Chacha.qp) (aead_imports3 Chacha.CS ++ aead_G3) Chacha.CS
    WgNoise.chacha.code.f_chacha_crypt chacha_crypt_spec3 /\
  @semax_body (QPvarspecs Chacha20poly1305.qp) (aead_imports3 Chacha20poly1305.CS ++ aead_G3)
    Chacha20poly1305.CS WgNoise.chacha20poly1305.code.f_chacha20_crypt chacha20_crypt_spec3.
Proof.
  exact (conj body_chacha_crypt_generic3 (conj body_chacha_crypt3 body_chacha20_crypt3)).
Qed.
