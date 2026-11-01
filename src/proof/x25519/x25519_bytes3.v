(* part of x25519_part3: the bodies of fe_frombytes_impl, fe_freeze, fe_tobytes.
   Specifications: x25519_spec.v, model: x25519_model.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.x25519.x25519_spec.

#[local] Existing Instance Curve25519Fiat32.CS.

Lemma body_fe_frombytes_impl3 : semax_body x25_V x25_Gprog F.f_fe_frombytes_impl fe_frombytes_impl_spec.
Proof.
  start_function.
  assert_PROP (isptr s) by entailer!.
  forward_call (ssh, s, 0, bs). { entailer!. rewrite H; cancel. }
  forward_call (ssh, s, 4, bs). forward_call (ssh, s, 8, bs). forward_call (ssh, s, 12, bs).
  forward_call (ssh, s, 16, bs). forward_call (ssh, s, 20, bs). forward_call (ssh, s, 24, bs).
  forward_call (ssh, s, 28, bs).
  rewrite H. do 10 forward. entailer!.
Qed.

Lemma carry_bit_ze3 (x: int) :
  Int.unsigned x <= 1 -> Int.zero_ext 8 x = x /\ Int.unsigned x <= Byte.max_unsigned.
Proof.
  intros. split. apply zero_ext_inrange. simpl. lia. rep_lia.
Qed.

Lemma subborrow_snd3 (n: Z) (c a b: int) : Int.unsigned (snd (subborrow_m n c a b)) <= 1.
Proof.
  unfold subborrow_m; simpl. rewrite Int.shru_div_two_p.
  change (two_p (Int.unsigned (Int.repr 31))) with 2147483648.
  pose proof (Int.unsigned_range (Int.sub (Int.sub a b) c)).
  rewrite Int.unsigned_repr; [ | split; [apply Z.div_pos | apply Z.div_le_upper_bound]; rep_lia].
  assert (Int.unsigned (Int.sub (Int.sub a b) c) / 2147483648 < 2) by (apply Z.div_lt_upper_bound; rep_lia).
  lia.
Qed.

Lemma addcarryx_snd3 (n: Z) (c a b: int) : Int.unsigned (snd (addcarryx_m n c a b)) <= 1.
Proof.
  unfold addcarryx_m; simpl. rewrite Int.and_commut.
  pose proof (Int.and_le Int.one (Int.shru (Int.add (Int.add a b) c) (Int.repr n))).
  rewrite Int.unsigned_one in *. lia.
Qed.

Lemma mone_repr3 : Int.repr (-1) = Int.repr 4294967295.
Proof. apply Int.eqm_samerepr. exists (-1). reflexivity. Qed.

Lemma body_fe_freeze3 : semax_body x25_V x25_Gprog F.f_fe_freeze fe_freeze_spec.
Proof.
  start_function.
  do 10 forward.
  forward_call (Int.zero, Znth 0 f, Int.repr 67108845, Tsh, v_x20).
  destruct (subborrow_m 26 Int.zero (Znth 0 f) (Int.repr 67108845)) as [x20 x21] eqn:E1.
  cbn [fst snd].
  assert (B1: Int.unsigned x21 <= 1) by (change x21 with (snd (x20, x21)); rewrite <- E1; apply subborrow_snd3).
  forward_call (x21, Znth 1 f, Int.repr 33554431, Tsh, v_x23).
  destruct (subborrow_m 25 x21 (Znth 1 f) (Int.repr 33554431)) as [x23 x24] eqn:E2.
  cbn [fst snd].
  assert (B2: Int.unsigned x24 <= 1) by (change x24 with (snd (x23, x24)); rewrite <- E2; apply subborrow_snd3).
  forward_call (x24, Znth 2 f, Int.repr 67108863, Tsh, v_x26).
  destruct (subborrow_m 26 x24 (Znth 2 f) (Int.repr 67108863)) as [x26 x27] eqn:E3.
  cbn [fst snd].
  assert (B3: Int.unsigned x27 <= 1) by (change x27 with (snd (x26, x27)); rewrite <- E3; apply subborrow_snd3).
  forward_call (x27, Znth 3 f, Int.repr 33554431, Tsh, v_x29).
  destruct (subborrow_m 25 x27 (Znth 3 f) (Int.repr 33554431)) as [x29 x30] eqn:E4.
  cbn [fst snd].
  assert (B4: Int.unsigned x30 <= 1) by (change x30 with (snd (x29, x30)); rewrite <- E4; apply subborrow_snd3).
  forward_call (x30, Znth 4 f, Int.repr 67108863, Tsh, v_x32).
  destruct (subborrow_m 26 x30 (Znth 4 f) (Int.repr 67108863)) as [x32 x33] eqn:E5.
  cbn [fst snd].
  assert (B5: Int.unsigned x33 <= 1) by (change x33 with (snd (x32, x33)); rewrite <- E5; apply subborrow_snd3).
  forward_call (x33, Znth 5 f, Int.repr 33554431, Tsh, v_x35).
  destruct (subborrow_m 25 x33 (Znth 5 f) (Int.repr 33554431)) as [x35 x36] eqn:E6.
  cbn [fst snd].
  assert (B6: Int.unsigned x36 <= 1) by (change x36 with (snd (x35, x36)); rewrite <- E6; apply subborrow_snd3).
  forward_call (x36, Znth 6 f, Int.repr 67108863, Tsh, v_x38).
  destruct (subborrow_m 26 x36 (Znth 6 f) (Int.repr 67108863)) as [x38 x39] eqn:E7.
  cbn [fst snd].
  assert (B7: Int.unsigned x39 <= 1) by (change x39 with (snd (x38, x39)); rewrite <- E7; apply subborrow_snd3).
  forward_call (x39, Znth 7 f, Int.repr 33554431, Tsh, v_x41).
  destruct (subborrow_m 25 x39 (Znth 7 f) (Int.repr 33554431)) as [x41 x42] eqn:E8.
  cbn [fst snd].
  assert (B8: Int.unsigned x42 <= 1) by (change x42 with (snd (x41, x42)); rewrite <- E8; apply subborrow_snd3).
  forward_call (x42, Znth 8 f, Int.repr 67108863, Tsh, v_x44).
  destruct (subborrow_m 26 x42 (Znth 8 f) (Int.repr 67108863)) as [x44 x45] eqn:E9.
  cbn [fst snd].
  assert (B9: Int.unsigned x45 <= 1) by (change x45 with (snd (x44, x45)); rewrite <- E9; apply subborrow_snd3).
  forward_call (x45, Znth 9 f, Int.repr 33554431, Tsh, v_x47).
  destruct (subborrow_m 25 x45 (Znth 9 f) (Int.repr 33554431)) as [x47 x48] eqn:E10.
  cbn [fst snd].
  assert (B10: Int.unsigned x48 <= 1) by (change x48 with (snd (x47, x48)); rewrite <- E10; apply subborrow_snd3).
  forward_call (x48, Int.zero, Int.repr (-1)).
  rewrite mone_repr3.
  remember (cmovznz32_m x48 Int.zero (Int.repr 4294967295)) as x49 eqn:E49.
  forward. forward.
  forward_call (Int.zero, x20, Int.and x49 (Int.repr 67108845), Tsh, v_x52).
  destruct (addcarryx_m 26 Int.zero x20 (Int.and x49 (Int.repr 67108845))) as [x52 x53] eqn:E11.
  cbn [fst snd].
  assert (B11: Int.unsigned x53 <= 1) by (change x53 with (snd (x52, x53)); rewrite <- E11; apply addcarryx_snd3).
  forward. rewrite (proj1 (carry_bit_ze3 _ B11)).
  forward. forward.
  forward_call (x53, x23, Int.and x49 (Int.repr 33554431), Tsh, v_x56).
  destruct (addcarryx_m 25 x53 x23 (Int.and x49 (Int.repr 33554431))) as [x56 x57] eqn:E12.
  cbn [fst snd].
  assert (B12: Int.unsigned x57 <= 1) by (change x57 with (snd (x56, x57)); rewrite <- E12; apply addcarryx_snd3).
  forward. rewrite (proj1 (carry_bit_ze3 _ B12)).
  forward. forward.
  forward_call (x57, x26, Int.and x49 (Int.repr 67108863), Tsh, v_x60).
  destruct (addcarryx_m 26 x57 x26 (Int.and x49 (Int.repr 67108863))) as [x60 x61] eqn:E13.
  cbn [fst snd].
  assert (B13: Int.unsigned x61 <= 1) by (change x61 with (snd (x60, x61)); rewrite <- E13; apply addcarryx_snd3).
  forward. rewrite (proj1 (carry_bit_ze3 _ B13)).
  forward. forward.
  forward_call (x61, x29, Int.and x49 (Int.repr 33554431), Tsh, v_x64).
  destruct (addcarryx_m 25 x61 x29 (Int.and x49 (Int.repr 33554431))) as [x64 x65] eqn:E14.
  cbn [fst snd].
  assert (B14: Int.unsigned x65 <= 1) by (change x65 with (snd (x64, x65)); rewrite <- E14; apply addcarryx_snd3).
  forward. rewrite (proj1 (carry_bit_ze3 _ B14)).
  forward. forward.
  forward_call (x65, x32, Int.and x49 (Int.repr 67108863), Tsh, v_x68).
  destruct (addcarryx_m 26 x65 x32 (Int.and x49 (Int.repr 67108863))) as [x68 x69] eqn:E15.
  cbn [fst snd].
  assert (B15: Int.unsigned x69 <= 1) by (change x69 with (snd (x68, x69)); rewrite <- E15; apply addcarryx_snd3).
  forward. rewrite (proj1 (carry_bit_ze3 _ B15)).
  forward. forward.
  forward_call (x69, x35, Int.and x49 (Int.repr 33554431), Tsh, v_x72).
  destruct (addcarryx_m 25 x69 x35 (Int.and x49 (Int.repr 33554431))) as [x72 x73] eqn:E16.
  cbn [fst snd].
  assert (B16: Int.unsigned x73 <= 1) by (change x73 with (snd (x72, x73)); rewrite <- E16; apply addcarryx_snd3).
  forward. rewrite (proj1 (carry_bit_ze3 _ B16)).
  forward. forward.
  forward_call (x73, x38, Int.and x49 (Int.repr 67108863), Tsh, v_x76).
  destruct (addcarryx_m 26 x73 x38 (Int.and x49 (Int.repr 67108863))) as [x76 x77] eqn:E17.
  cbn [fst snd].
  assert (B17: Int.unsigned x77 <= 1) by (change x77 with (snd (x76, x77)); rewrite <- E17; apply addcarryx_snd3).
  forward. rewrite (proj1 (carry_bit_ze3 _ B17)).
  forward. forward.
  forward_call (x77, x41, Int.and x49 (Int.repr 33554431), Tsh, v_x80).
  destruct (addcarryx_m 25 x77 x41 (Int.and x49 (Int.repr 33554431))) as [x80 x81] eqn:E18.
  cbn [fst snd].
  assert (B18: Int.unsigned x81 <= 1) by (change x81 with (snd (x80, x81)); rewrite <- E18; apply addcarryx_snd3).
  forward. rewrite (proj1 (carry_bit_ze3 _ B18)).
  forward. forward.
  forward_call (x81, x44, Int.and x49 (Int.repr 67108863), Tsh, v_x84).
  destruct (addcarryx_m 26 x81 x44 (Int.and x49 (Int.repr 67108863))) as [x84 x85] eqn:E19.
  cbn [fst snd].
  assert (B19: Int.unsigned x85 <= 1) by (change x85 with (snd (x84, x85)); rewrite <- E19; apply addcarryx_snd3).
  forward. rewrite (proj1 (carry_bit_ze3 _ B19)).
  forward. forward.
  forward_call (x85, x47, Int.and x49 (Int.repr 33554431), Tsh, v_x88).
  destruct (addcarryx_m 25 x85 x47 (Int.and x49 (Int.repr 33554431))) as [x88 x89] eqn:E20.
  cbn [fst snd].
  assert (B20: Int.unsigned x89 <= 1) by (change x89 with (snd (x88, x89)); rewrite <- E20; apply addcarryx_snd3).
  assert (EF: fe_freeze_m f = [x52; x56; x60; x64; x68; x72; x76; x80; x84; x88]).
  { unfold fe_freeze_m. cbv zeta. rewrite E1; cbv beta iota zeta. rewrite E2; cbv beta iota zeta. rewrite E3; cbv beta iota zeta. rewrite E4; cbv beta iota zeta. rewrite E5; cbv beta iota zeta. rewrite E6; cbv beta iota zeta. rewrite E7; cbv beta iota zeta. rewrite E8; cbv beta iota zeta. rewrite E9; cbv beta iota zeta. rewrite E10; cbv beta iota zeta. rewrite <- E49. rewrite E11; cbv beta iota zeta. rewrite E12; cbv beta iota zeta. rewrite E13; cbv beta iota zeta. rewrite E14; cbv beta iota zeta. rewrite E15; cbv beta iota zeta. rewrite E16; cbv beta iota zeta. rewrite E17; cbv beta iota zeta. rewrite E18; cbv beta iota zeta. rewrite E19; cbv beta iota zeta. rewrite E20; cbv beta iota zeta. reflexivity. }
  do 4 forward. do 4 forward. do 4 forward. do 4 forward. do 4 forward.
  rewrite EF. clear EF. entailer!.
Qed.

Lemma fe_freeze_len3 (f: list int) : Zlength (fe_freeze_m f) = 10.
Proof.
  unfold fe_freeze_m.
  repeat match goal with
  | |- context [subborrow_m ?a ?b ?c ?d] => destruct (subborrow_m a b c d)
  | |- context [addcarryx_m ?a ?b ?c ?d] => destruct (addcarryx_m a b c d)
  end.
  reflexivity.
Qed.

Lemma upd32_3 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31: val) :
  (upd_Znth 31 (upd_Znth 30 (upd_Znth 29 (upd_Znth 28 (upd_Znth 27 (upd_Znth 26 (upd_Znth 25 (upd_Znth 24 (upd_Znth 23 (upd_Znth 22 (upd_Znth 21 (upd_Znth 20 (upd_Znth 19 (upd_Znth 18 (upd_Znth 17 (upd_Znth 16 (upd_Znth 15 (upd_Znth 14 (upd_Znth 13 (upd_Znth 12 (upd_Znth 11 (upd_Znth 10 (upd_Znth 9 (upd_Znth 8 (upd_Znth 7 (upd_Znth 6 (upd_Znth 5 (upd_Znth 4 (upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 (default_val (tarray tuchar 32)) v0) v1) v2) v3) v4) v5) v6) v7) v8) v9) v10) v11) v12) v13) v14) v15) v16) v17) v18) v19) v20) v21) v22) v23) v24) v25) v26) v27) v28) v29) v30) v31) =
  [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14; v15; v16; v17; v18; v19; v20; v21; v22; v23; v24; v25; v26; v27; v28; v29; v30; v31].
Proof. reflexivity. Qed.

Lemma zext_u8_3 (x: int) : Vint (Int.zero_ext 8 x) = Vubyte (u8_of x).
Proof.
  unfold u8_of, Vubyte. f_equal. rewrite Byte.unsigned_repr_eq.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 x)). rewrite Int.zero_ext_mod by (cbn; lia).
  reflexivity.
Qed.

Lemma body_fe_tobytes3 : semax_body x25_V x25_Gprog F.f_fe_tobytes fe_tobytes_spec.
Proof.
  start_function.
  forward_call (Tsh, v_h, fsh, fp, f).
  { entailer!. simpl. rewrite isptr_offset_val_zero by auto. reflexivity. }
  pose proof (fe_freeze_len3 f) as HL.
  destruct (fe_freeze_m f) as [|h0 [|h1 [|h2 [|h3 [|h4 [|h5 [|h6 [|h7 [|h8 [|h9 [|]]]]]]]]]]] eqn:EH;
    try (list_simplify; fail).
  do 8 forward. do 8 forward. do 8 forward. do 8 forward. do 8 forward. do 8 forward.
  do 8 forward. do 8 forward. do 8 forward.
  entailer!.
  rewrite upd32_3. apply derives_refl'. f_equal.
  unfold fe_tobytes_m. rewrite EH. cbv zeta. cbn [map]. rewrite !zext_u8_3. reflexivity.
Qed.

Theorem x25519_bytes3 :
  semax_body x25_V x25_Gprog F.f_fe_frombytes_impl fe_frombytes_impl_spec /\
  semax_body x25_V x25_Gprog F.f_fe_freeze fe_freeze_spec /\
  semax_body x25_V x25_Gprog F.f_fe_tobytes fe_tobytes_spec.
Proof.
  split; [ | split ].
  - apply body_fe_frombytes_impl3.
  - apply body_fe_freeze3.
  - apply body_fe_tobytes3.
Qed.
