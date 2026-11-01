(* The bodies of poly1305-donna32.c (poly1305_core_setkey, poly1305_core_blocks, poly1305_core_emit and the
   file's copy of the inline put_unaligned_le32) with a context of their callees only, against the specifications
   of aead_spec.v (the same as aead_donna_blocks_body3.v / aead_donna_emit_body3.v, whose context is the whole
   AEAD piece).  A program that links poly1305-donna32.c without the ChaCha20 and AEAD units (law
   ae_split_poly1305) can take these bodies: every function of their contexts is in it. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.poly1305.code WgNoise.poly1305_donna32.code.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.aead.aead_spec3.
Require Import WgNoise.proof.aead.aead_bytes.
Require Import WgNoise.proof.aead.aead_model.
Require Import WgNoise.proof.aead.aead_donna3_math.
Require Import WgNoise.proof.aead.aead_donna3_msg.
Require Import WgNoise.proof.aead.aead_donna_emit3_reduce.
Require Import WgNoise.proof.aead.aead_donna_emit3_keymath.
(* the helper lemmas of the scripts with the whole AEAD context, reused as they are *)
Require Import WgNoise.proof.aead.aead_small_body3.
Require Import WgNoise.proof.aead.aead_donna_emit_body3.
Require Import WgNoise.proof.aead.aead_donna_blocks_body3.

Local Open Scope Z_scope.

Module C := WgNoise.poly1305_donna32.code.
Local Definition _input := WgNoise.poly1305_donna32.code._input.
Local Definition _state := WgNoise.poly1305_donna32.code._state.
Local Definition _key := WgNoise.poly1305_donna32.code._key.
Local Definition _src := WgNoise.poly1305_donna32.code._src.
Local Definition _nblocks := WgNoise.poly1305_donna32.code._nblocks.
Local Definition _hibit := WgNoise.poly1305_donna32.code._hibit.

#[local] Existing Instance Poly1305Donna32.CS.

(* poly1305-donna32.c's copy of put_unaligned_le32 (the same Clight as chacha-block-generic.c's) *)
Lemma body_put_unaligned_le32_donna :
  @semax_body (QPvarspecs Poly1305Donna32.qp) nil Poly1305Donna32.CS
    WgNoise.poly1305_donna32.code.f_put_unaligned_le32 put_unaligned_le32_spec.
Proof.
  start_function.
  rewrite (@aead_data_at_tuchar_cs ChachaBlock.CS Poly1305Donna32.CS).
  assert_PROP (field_compatible (tarray tuchar (Zlength old)) [] p) by entailer!.
  rewrite (as3_split3 sh (Zlength old) i 4 old p) by (auto; lia). Intros.
  forward. forward. forward. forward. forward.
  rewrite !Int.zero_ext_idem by lia. rewrite !as3_byte_of, !as3_shru_unsigned by lia.
  rewrite as3_upd4 by list_solve.
  entailer!.
  rewrite (@aead_data_at_tuchar_cs ChachaBlock.CS Poly1305Donna32.CS).
  rewrite (as3_split3 sh (Zlength old) i 4 _ p) by (auto; list_solve).
  autorewrite with sublist.
  apply sepcon_derives; [apply sepcon_derives; [apply derives_refl | ] | ]; apply derives_refl'; f_equal; list_solve.
Qed.

Lemma body_poly1305_core_setkey_callee :
  @semax_body (QPvarspecs Poly1305Donna32.qp) [@get_unaligned_le32_spec Poly1305Donna32.CS] Poly1305Donna32.CS
    WgNoise.poly1305_donna32.code.f_poly1305_core_setkey poly1305_core_setkey_spec.
Proof.
  start_function.
  assert_PROP (isptr raw) by entailer!.
  forward_call (rsh, raw, 0, rk).
  forward.
  forward_call (rsh, raw, 3, rk).
  forward.
  forward_call (rsh, raw, 6, rk).
  forward.
  forward_call (rsh, raw, 9, rk).
  forward.
  forward_call (rsh, raw, 12, rk).
  forward.
  rewrite (key3_r0 rk H), (key3_r1 rk H), (key3_r2 rk H), (key3_r3 rk H), (key3_r4 rk H).
  set (r0 := Int.repr (p1305_r rk mod 2 ^ 26)).
  set (r1 := Int.repr (p1305_r rk / 2 ^ 26 mod 2 ^ 26)).
  set (r2 := Int.repr (p1305_r rk / 2 ^ 52 mod 2 ^ 26)).
  set (r3 := Int.repr (p1305_r rk / 2 ^ 78 mod 2 ^ 26)).
  set (r4 := Int.repr (p1305_r rk / 2 ^ 104)).
  simpl default_val. simpl upd_Znth.
  do 8 forward.
  rewrite key3_kval_eq. unfold p1305_r_limbs.
  subst r0 r1 r2 r3 r4.
  set (z0 := p1305_r rk mod 2 ^ 26). set (z1 := p1305_r rk / 2 ^ 26 mod 2 ^ 26).
  set (z2 := p1305_r rk / 2 ^ 52 mod 2 ^ 26). set (z3 := p1305_r rk / 2 ^ 78 mod 2 ^ 26).
  set (z4 := p1305_r rk / 2 ^ 104). clearbody z0 z1 z2 z3 z4.
  rewrite !key3_mul5.
  entailer!.
Qed.

Lemma body_poly1305_core_blocks_callee :
  @semax_body (QPvarspecs Poly1305Donna32.qp) [@get_unaligned_le32_spec Poly1305Donna32.CS] Poly1305Donna32.CS
    WgNoise.poly1305_donna32.code.f_poly1305_core_blocks poly1305_core_blocks_spec.
Proof.
start_function.
forward.
forward_if (PROP (nb <> 0) LOCAL (temp _input src; temp _state hp; temp _key kp; temp _src src;
   temp _nblocks (Vint (Int.repr nb)); temp _hibit (Vint (Int.repr hibit)))
   SEP (data_at hsh t_p1305_state (p1305_h_val h) hp; data_at ksh t_p1305_core_key (p1305_key_val r) kp;
        prim_bytes msh bs src)).
{ forward. Exists h.
  assert (nb = 0) by (apply (f_equal Int.unsigned) in H4; rewrite Int.unsigned_repr in H4 by rep_lia; exact H4).
  subst nb. assert (bs = []) by (apply Zlength_nil_inv; lia). subst bs.
  entailer!. }
{ forward. entailer!. }
Intros.
rewrite adb3_h_cs, adb3_key_cs, adb3_key_val_eq.
unfold adb3_h_val. rewrite (adb3_h_list h) by (destruct H; auto).
assert (Hbs: Zlength bs > 0) by lia.
unfold prim_bytes. rewrite if_false by lia.
unfold adb3_key_val'.
remember (r mod 2 ^ 26) as r0 eqn:Hr0. remember ((r / 2 ^ 26) mod 2 ^ 26) as r1 eqn:Hr1.
remember ((r / 2 ^ 52) mod 2 ^ 26) as r2 eqn:Hr2. remember ((r / 2 ^ 78) mod 2 ^ 26) as r3 eqn:Hr3.
remember (r / 2 ^ 104) as r4 eqn:Hr4.
forward.
forward. forward. forward. forward. forward.
forward. forward. forward. forward.
forward. forward. forward. forward. forward.
forward_loop
 (EX k: Z, EX hk: list Z,
  PROP (0 <= k < nb; p1305_limbs_ok hk;
        p1305_limbs_val hk mod p1305_p = p1305_core_blocks r hibit (p1305_limbs_val h) (sublist 0 (16 * k) bs) mod p1305_p)
  LOCAL (temp _input (offset_val (16 * k) src); temp _nblocks (Vint (Int.repr (nb - k)));
         temp C._h0 (Vint (Int.repr (Znth 0 hk))); temp C._h1 (Vint (Int.repr (Znth 1 hk)));
         temp C._h2 (Vint (Int.repr (Znth 2 hk))); temp C._h3 (Vint (Int.repr (Znth 3 hk)));
         temp C._h4 (Vint (Int.repr (Znth 4 hk)));
         temp C._r0 (Vint (Int.repr r0)); temp C._r1 (Vint (Int.repr r1)); temp C._r2 (Vint (Int.repr r2));
         temp C._r3 (Vint (Int.repr r3)); temp C._r4 (Vint (Int.repr r4));
         temp C._s1 (Vint (Int.repr (5 * r1))); temp C._s2 (Vint (Int.repr (5 * r2)));
         temp C._s3 (Vint (Int.repr (5 * r3))); temp C._s4 (Vint (Int.repr (5 * r4)));
         temp _hibit (Vint (Int.repr (hibit * 2 ^ 24))); temp _state hp)
  SEP (data_at hsh t_p1305_state (inl (map Vint (map Int.repr [Znth 0 h; Znth 1 h; Znth 2 h; Znth 3 h; Znth 4 h]))) hp;
       data_at ksh t_p1305_core_key
         (inl [Vint (Int.repr r0); Vint (Int.repr r1); Vint (Int.repr r2); Vint (Int.repr r3); Vint (Int.repr r4)],
          inl [Vint (Int.repr (5 * r1)); Vint (Int.repr (5 * r2)); Vint (Int.repr (5 * r3)); Vint (Int.repr (5 * r4));
               Vundef]) kp;
       data_at msh (tarray tuchar (Zlength bs)) (map Vubyte bs) src))%assert
 continue:
 (EX k: Z, EX hk: list Z,
  PROP (0 <= k < nb; p1305_limbs_ok hk;
        p1305_limbs_val hk mod p1305_p = p1305_core_blocks r hibit (p1305_limbs_val h) (sublist 0 (16 * (k + 1)) bs) mod p1305_p)
  LOCAL (temp _input (offset_val (16 * (k + 1)) src); temp _nblocks (Vint (Int.repr (nb - k)));
         temp C._h0 (Vint (Int.repr (Znth 0 hk))); temp C._h1 (Vint (Int.repr (Znth 1 hk)));
         temp C._h2 (Vint (Int.repr (Znth 2 hk))); temp C._h3 (Vint (Int.repr (Znth 3 hk)));
         temp C._h4 (Vint (Int.repr (Znth 4 hk)));
         temp C._r0 (Vint (Int.repr r0)); temp C._r1 (Vint (Int.repr r1)); temp C._r2 (Vint (Int.repr r2));
         temp C._r3 (Vint (Int.repr r3)); temp C._r4 (Vint (Int.repr r4));
         temp C._s1 (Vint (Int.repr (5 * r1))); temp C._s2 (Vint (Int.repr (5 * r2)));
         temp C._s3 (Vint (Int.repr (5 * r3))); temp C._s4 (Vint (Int.repr (5 * r4)));
         temp _hibit (Vint (Int.repr (hibit * 2 ^ 24))); temp _state hp)
  SEP (data_at hsh t_p1305_state (inl (map Vint (map Int.repr [Znth 0 h; Znth 1 h; Znth 2 h; Znth 3 h; Znth 4 h]))) hp;
       data_at ksh t_p1305_core_key
         (inl [Vint (Int.repr r0); Vint (Int.repr r1); Vint (Int.repr r2); Vint (Int.repr r3); Vint (Int.repr r4)],
          inl [Vint (Int.repr (5 * r1)); Vint (Int.repr (5 * r2)); Vint (Int.repr (5 * r3)); Vint (Int.repr (5 * r4));
               Vundef]) kp;
       data_at msh (tarray tuchar (Zlength bs)) (map Vubyte bs) src))%assert
 break:
 (EX hk: list Z,
  PROP (p1305_limbs_ok hk;
        p1305_limbs_val hk mod p1305_p = p1305_core_blocks r hibit (p1305_limbs_val h) bs mod p1305_p)
  LOCAL (temp C._h0 (Vint (Int.repr (Znth 0 hk))); temp C._h1 (Vint (Int.repr (Znth 1 hk)));
         temp C._h2 (Vint (Int.repr (Znth 2 hk))); temp C._h3 (Vint (Int.repr (Znth 3 hk)));
         temp C._h4 (Vint (Int.repr (Znth 4 hk))); temp _state hp)
  SEP (data_at hsh t_p1305_state (inl (map Vint (map Int.repr [Znth 0 h; Znth 1 h; Znth 2 h; Znth 3 h; Znth 4 h]))) hp;
       data_at ksh t_p1305_core_key
         (inl [Vint (Int.repr r0); Vint (Int.repr r1); Vint (Int.repr r2); Vint (Int.repr r3); Vint (Int.repr r4)],
          inl [Vint (Int.repr (5 * r1)); Vint (Int.repr (5 * r2)); Vint (Int.repr (5 * r3)); Vint (Int.repr (5 * r4));
               Vundef]) kp;
       data_at msh (tarray tuchar (Zlength bs)) (map Vubyte bs) src))%assert.
{ Exists 0 h. entailer!. destruct H3; subst; reflexivity. }
{ Intros k hk.
  forward_call (msh, src, 16 * k, bs). { entailer!. }
  forward.
  forward_call (msh, src, 16 * k + 3, bs). { entailer!. }
  forward.
  forward_call (msh, src, 16 * k + 6, bs). { entailer!. }
  forward.
  forward_call (msh, src, 16 * k + 9, bs). { entailer!. }
  forward.
  forward_call (msh, src, 16 * k + 12, bs). { entailer!. }
  forward.
  forward. forward. forward. forward. forward.
  forward. forward. forward. forward. forward.
  forward. forward. forward. forward. forward.
  forward. forward. forward. forward. forward.
  forward. forward. forward. forward.
  pose proof (adb3_c_ok hk r hibit (le32_at bs (16 * k)) (le32_at bs (16 * k + 3)) (le32_at bs (16 * k + 6))
    (le32_at bs (16 * k + 9)) (le32_at bs (16 * k + 12)) H6 H0 H3) as HC.
  cbv zeta in HC.
  change (Znth 0 (p1305_r_limbs r)) with (r mod 2 ^ 26) in HC.
  change (Znth 1 (p1305_r_limbs r)) with ((r / 2 ^ 26) mod 2 ^ 26) in HC.
  change (Znth 2 (p1305_r_limbs r)) with ((r / 2 ^ 52) mod 2 ^ 26) in HC.
  change (Znth 3 (p1305_r_limbs r)) with ((r / 2 ^ 78) mod 2 ^ 26) in HC.
  change (Znth 4 (p1305_r_limbs r)) with (r / 2 ^ 104) in HC.
  rewrite <- Hr0, <- Hr1, <- Hr2, <- Hr3, <- Hr4 in HC.
  set (L := adb3_c (Int.repr (Znth 0 hk)) (Int.repr (Znth 1 hk)) (Int.repr (Znth 2 hk))
    (Int.repr (Znth 3 hk)) (Int.repr (Znth 4 hk)) (Int.repr r0) (Int.repr r1) (Int.repr r2) (Int.repr r3)
    (Int.repr r4) (Int.repr (5 * r1)) (Int.repr (5 * r2)) (Int.repr (5 * r3)) (Int.repr (5 * r4))
    (le32_at bs (16 * k)) (le32_at bs (16 * k + 3)) (le32_at bs (16 * k + 6)) (le32_at bs (16 * k + 9))
    (le32_at bs (16 * k + 12)) (Int.repr (hibit * 2 ^ 24))) in HC.
  destruct HC as [Hok Hval].
  assert (HL: Zlength L = 5) by reflexivity.
  match goal with |- context [LOCALx (temp _ _ :: temp _ (Vint ?X1) :: temp _ (Vint ?X0) :: temp _ _ ::
        temp _ (Vint ?X4) :: temp _ _ :: temp _ (Vint ?X3) :: temp _ _ :: temp _ (Vint ?X2) :: _) _] =>
    change X0 with (Znth 0 L); change X1 with (Znth 1 L); change X2 with (Znth 2 L);
    change X3 with (Znth 3 L); change X4 with (Znth 4 L)
  end.
  clearbody L.
  Exists k (map Int.unsigned L).
  rewrite !adb3_repr_znth by lia.
  entailer!.
  split; [ | f_equal; lia].
  assert (Hk1: 16 * k + 16 <= Zlength bs) by lia.
  rewrite Hval.
  rewrite <- (adb3_le32_sublist bs (16 * k) 3), <- (adb3_le32_sublist bs (16 * k) 6),
    <- (adb3_le32_sublist bs (16 * k) 9), <- (adb3_le32_sublist bs (16 * k) 12) by lia.
  replace (le32_at bs (16 * k)) with (le32_at (sublist (16 * k) (16 * k + 16) bs) 0)
    by (rewrite adb3_le32_sublist by lia; f_equal; lia).
  rewrite adb3_m_le by (rewrite Zlength_sublist by lia; lia).
  rewrite adb3_core_blocks_snoc by lia.
  change ((p1305_limbs_val hk + le_Z (sublist (16 * k) (16 * k + 16) bs) + hibit * 2 ^ 128) * r mod p1305_p)
    with (p1305_core_step r hibit (p1305_limbs_val hk) (sublist (16 * k) (16 * k + 16) bs)).
  rewrite (adb3_step_mod _ _ _ _ _ H7).
  unfold p1305_core_step. rewrite Zmod_mod. reflexivity.
}
{ Intros k hk.
  forward. forward.
  forward_if.
  - forward. Exists (k + 1) hk. entailer!.
    rewrite !Int.unsigned_repr in H8' by rep_lia. split; [lia | f_equal; f_equal; lia].
  - forward. Exists hk. entailer!.
    assert (nb - k - 1 = 0) by (apply (f_equal Int.unsigned) in H8; rewrite Int.unsigned_repr in H8 by rep_lia; exact H8).
    replace (16 * (k + 1)) with (Zlength bs) in H7 by lia. rewrite sublist_same in H7 by lia. exact H7. }
Intros hk.
forward. forward. forward. forward. forward.
Exists hk.
rewrite adb3_upd5 by (destruct H; destruct H5; auto).
rewrite adb3_h_cs, adb3_key_cs, adb3_key_val_eq. unfold adb3_key_val', adb3_h_val.
subst r0 r1 r2 r3 r4.
unfold prim_bytes. rewrite if_false by lia.
entailer!.
Qed.

Lemma body_poly1305_core_emit_callee :
  @semax_body (QPvarspecs Poly1305Donna32.qp) [put_unaligned_le32_spec] Poly1305Donna32.CS
    WgNoise.poly1305_donna32.code.f_poly1305_core_emit poly1305_core_emit_spec.
Proof.
  start_function.
  destruct H as [Hlen Hb].
  rewrite emit3_hval_eq.
  destruct h as [|a0 [|a1 [|a2 [|a3 [|a4 [|]]]]]]; try list_solve. clear Hlen.
  destruct s as [|n0 [|n1 [|n2 [|n3 [|]]]]]; try list_solve. clear H0.
  simpl in Hb. unfold Znth in Hb; simpl in Hb.
  simpl map.
  forward.
  do 5 forward.
  unfold Znth; simpl.
  do 44 (forward; emit3_abbrev).
  forward_if (EX x0: int, EX x1: int, EX x2: int, EX x3: int,
    PROP (words_Z [x0; x1; x2; x3] = (words_Z [w39; w40; w41; w42] + words_Z [n0; n1; n2; n3]) mod 2 ^ 128)
    LOCAL (temp WgNoise.poly1305_donna32.code._h0 (Vint x0); temp WgNoise.poly1305_donna32.code._h1 (Vint x1);
           temp WgNoise.poly1305_donna32.code._h2 (Vint x2); temp WgNoise.poly1305_donna32.code._h3 (Vint x3);
           temp WgNoise.poly1305_donna32.code._mac dst)
    SEP (data_at hsh t_p1305_state
          (@inl (list val) (list val) [Vint (Int.repr a0); Vint (Int.repr a1); Vint (Int.repr a2); Vint (Int.repr a3); Vint (Int.repr a4)]) hp;
         data_at nsh (tarray tuint 4) [Vint n0; Vint n1; Vint n2; Vint n3] np;
         data_at_ dsh (tarray tuchar 16) dst))%assert.
  { do 4 (forward; unfold Znth; simpl; forward; emit3_abbrev; forward; emit3_abbrev).
    pose proof (emit3_nonce_ok _ _ _ _ _ _ _ _ _ _ _ _ Ef Ef0 Ef1 Ef2) as HN.
    subst w43 w44 w45. revert HN.
    repeat match goal with Hx: ?x = _ |- _ => is_var x; clear Hx end. intros HN.
    Exists (Int.repr (Int64.unsigned f)) (Int.repr (Int64.unsigned f0)) (Int.repr (Int64.unsigned f1))
      (Int.repr (Int64.unsigned f2)).
    entailer!. }
  { assert_PROP (isptr np) by entailer!. subst np. contradiction. }
  Intros x0 x1 x2 x3.
  rewrite emit3_mask_shift in Ew27.
  destruct Hb as (Hb0 & Hb1 & Hb2 & Hb3 & Hb4).
  pose proof (emit3_reduce_ok a0 a1 a2 a3 a4 w w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
    w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42
    Hb0 Hb1 Hb2 Hb3 Hb4 Ew Ew0 Ew1 Ew2 Ew3 Ew4 Ew5 Ew6 Ew7 Ew8 Ew9 Ew10 Ew11 Ew12 Ew13 Ew14 Ew15 Ew16 Ew17
    Ew18 Ew19 Ew20 Ew21 Ew22 Ew23 Ew24 Ew25 Ew26 Ew27 Ew28 Ew29 Ew30 Ew31 Ew32 Ew33 Ew34 Ew35 Ew36 Ew37 Ew38
    Ew39 Ew40 Ew41 Ew42) as HR.
  rewrite HR, Zplus_mod_idemp_l in H.
  clear - SH SH0 SH1 H.
  rewrite (@aead_data_at__tuchar_cs Poly1305Donna32.CS ChachaBlock.CS).
  change (@data_at_ ChachaBlock.CS dsh (tarray tuchar 16) dst)
    with (@data_at ChachaBlock.CS dsh (tarray tuchar 16) (Zrepeat Vundef 16) dst).
  assert_PROP (isptr dst)
    by (entailer!; match goal with Hf: field_compatible _ _ dst |- _ => destruct Hf; auto end).
  change (@data_at ChachaBlock.CS dsh (tarray tuchar 16) (Zrepeat Vundef 16) dst) with
    (@data_at ChachaBlock.CS dsh (tarray tuchar (Zlength (map Vubyte [] ++ Zrepeat Vundef (16 - 0))))
       (map Vubyte [] ++ Zrepeat Vundef (16 - 0)) dst).
  forward_call (x0, dsh, dst, 0, map Vubyte [] ++ Zrepeat Vundef (16 - 0)).
  { unfold le32_bytes; list_solve. }
  rewrite emit3_put_norm by (try reflexivity; lia).
  forward_call (x1, dsh, dst, 4, map Vubyte ([] ++ le32_bytes x0) ++ Zrepeat Vundef (16 - (0 + 4))).
  { unfold le32_bytes; list_solve. }
  rewrite emit3_put_norm by (try reflexivity; lia).
  forward_call (x2, dsh, dst, 8, map Vubyte (([] ++ le32_bytes x0) ++ le32_bytes x1) ++ Zrepeat Vundef (16 - (4 + 4))).
  { unfold le32_bytes; list_solve. }
  rewrite emit3_put_norm by (try reflexivity; lia).
  forward_call (x3, dsh, dst, 12,
    map Vubyte ((([] ++ le32_bytes x0) ++ le32_bytes x1) ++ le32_bytes x2) ++ Zrepeat Vundef (16 - (8 + 4))).
  { unfold le32_bytes; list_solve. }
  rewrite emit3_put_norm by (try reflexivity; lia).
  change (Zrepeat Vundef (16 - (8 + 4 + 4))) with (@nil val). rewrite app_nil_r.
  match goal with |- context [tarray tuchar (Zlength ?l)] =>
    replace (Zlength l) with 16 by (unfold le32_bytes; list_solve) end.
  assert (EB: ((([] ++ le32_bytes x0) ++ le32_bytes x1) ++ le32_bytes x2) ++ le32_bytes x3 =
              le_bytes 16 ((p1305_limbs_val [a0; a1; a2; a3; a4] mod p1305_p + words_Z [n0; n1; n2; n3]) mod 2 ^ 128)).
  { rewrite <- H. change 16%nat with (4 * length [x0; x1; x2; x3])%nat. rewrite <- emit3_words_bytes.
    reflexivity. }
  rewrite EB. clear EB H.
  rewrite (@aead_data_at_tuchar_cs ChachaBlock.CS Poly1305Donna32.CS).
  rewrite emit3_hval_eq.
  entailer!.
  Unshelve. all: exact 0.
Qed.

(* all of them *)
Theorem p1305_donna_callee_bodies :
  (@semax_body (QPvarspecs Poly1305Donna32.qp) nil Poly1305Donna32.CS WgNoise.poly1305_donna32.code.f_put_unaligned_le32 put_unaligned_le32_spec)
  /\ (@semax_body (QPvarspecs Poly1305Donna32.qp) [@get_unaligned_le32_spec Poly1305Donna32.CS] Poly1305Donna32.CS WgNoise.poly1305_donna32.code.f_poly1305_core_setkey poly1305_core_setkey_spec)
  /\ (@semax_body (QPvarspecs Poly1305Donna32.qp) [@get_unaligned_le32_spec Poly1305Donna32.CS] Poly1305Donna32.CS WgNoise.poly1305_donna32.code.f_poly1305_core_blocks poly1305_core_blocks_spec)
  /\ (@semax_body (QPvarspecs Poly1305Donna32.qp) [put_unaligned_le32_spec] Poly1305Donna32.CS WgNoise.poly1305_donna32.code.f_poly1305_core_emit poly1305_core_emit_spec).
Proof. exact (conj body_put_unaligned_le32_donna (conj body_poly1305_core_setkey_callee (conj body_poly1305_core_blocks_callee body_poly1305_core_emit_callee))). Qed.
