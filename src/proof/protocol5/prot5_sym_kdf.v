(* The body of noise.c's kdf against its v5 specification (prot_specs5.v kdf_spec: wg_consts5) in the
   context Gprot5 (prot_prog5.v).  The script is v4's (prot4_noise_kdf_kdf.v), whose helper lemmas on the
   output buffers and the aliasing of the first output with the chaining key are reused. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.protocol4.prot4_noise_kdf_hmac.
Require Import WgNoise.proof.protocol4.prot4_noise_kdf_kdf.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require Import WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.blake2s.b2s_spec3.
Require WgNoise.proof.libc.libc_piece.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

#[local] Instance CCE_kdf5_n2b : change_composite_env Noise.CS Blake2s.CS.
Proof. make_cs_preserve Noise.CS Blake2s.CS. Defined.
#[local] Instance CCE_kdf5_b2n : change_composite_env Blake2s.CS Noise.CS.
Proof. make_cs_preserve Blake2s.CS Noise.CS. Defined.

Local Open Scope logic.
#[local] Existing Instance Noise.CS.

Section Bodies.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

Lemma prot5_body_kdf : semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS)
  WgNoise.noise.code.f_kdf kdf_spec.
Proof.
start_function.
forward.
assert (Rc: readable_share shc) by (destruct alias; auto).
sep_apply (prot4_kdf_ck alias shc ck ckp sh1 d1).
forward_call (gv, false, Tsh, v_secret, shd, dp, @nil val, data, shc, ckp, ck).
{ rewrite H0; entailer!. }
{ cancel. }
sep_apply (wand_frame_elim (bytes_at shc ck ckp)).
assert_PROP (isptr d1) as Pd1. { destruct alias; [rewrite (H6 eq_refl); unfold bytes_at |]; entailer!. }
forward_if (temp WgNoise.noise.code._t'11 (Vint Int.one)).
{ apply denote_tc_test_eq_split; [| auto with valid_pointer].
  repeat apply sepcon_valid_pointer1. apply (prot4_kdf_R1_valid alias shc ck ckp sh1 d1 Rc SH H0 H6). }
{ forward. entailer!. }
{ subst d1. contradiction. }
assert (Hprk: Zlength (hmac ck data) = 32) by apply prot4_kdf_hmac_len.
prot4_kdf_hide (hmac ck data) prk.
forward_if (PROP () LOCAL (lvar WgNoise.noise.code._secret (tarray tuchar 32) v_secret;
  lvar WgNoise.noise.code._output (tarray tuchar 33) v_output; gvars gv)
  SEP (data_at_ Tsh (tarray tuchar 33) v_output; bytes_at Tsh prk v_secret;
       if alias then bytes_at shc (kdf1 ck data) ckp
       else (bytes_at shc ck ckp * bytes_at sh1 (kdf1 ck data) d1);
       if eq_dec d2 nullval then emp else bytes_at sh2 (kdf2 ck data) d2;
       if eq_dec d2 nullval then emp else if eq_dec d3 nullval then emp
       else bytes_at sh3 (kdf3 ck data) d3;
       b2s_bytes shd data dp; wg_consts5 gv)).
2: { inv H7. }
forward.
match goal with |- context [data_at Tsh _ ?l v_output] =>
  replace l with (bytes [Byte.one] ++ Zrepeat Vundef 32) by reflexivity end.
set (b0 := bytes [Byte.one] ++ Zrepeat Vundef 32).
assert (Hb0: Zlength b0 = 33) by reflexivity.
forward_call (gv, true, Tsh, v_output, Tsh, v_output, b0, [Byte.one], Tsh, v_secret, prk).
{ rewrite Hprk; entailer!. }
{ change (Zlength [Byte.one]) with 1. rewrite Hb0. split; [rep_lia |]. intros _. split3; [auto | lia |]. split; [rep_lia | reflexivity]. }
rewrite Hb0.
replace (sublist 32 33 b0) with [Vundef] by reflexivity.
assert (Hk1l: Zlength (hmac prk [Byte.one]) = 32) by apply prot4_kdf_hmac_len.
prot4_kdf_hide (hmac prk [Byte.one]) k1.
sep_apply (prot4_kdf_src32 Tsh k1 Vundef v_output Hk1l).
sep_apply (prot4_kdf_d1 alias shc ck ckp sh1 d1 k1 Hk1l H0 H6).
assert (W1: writable_share (if alias then shc else sh1)) by (destruct alias; auto).
remember (if alias then shc else sh1) as s1 eqn:Hs1.
remember (if alias then bytes_at shc k1 ckp else bytes_at shc ck ckp * bytes_at sh1 k1 d1)
  as Q1 eqn:HQ1.
forward_call (s1, Tsh, d1, v_output, 32, k1).
{ subst s1. cancel. }
change (map Vubyte k1) with (bytes k1).
subst s1.
sep_apply (wand_frame_elim (data_at (if alias then shc else sh1) (tarray tuchar 32) (bytes k1) d1) Q1).
sep_apply (wand_frame_elim (data_at Tsh (tarray tuchar 32) (bytes k1) v_output)).
subst Q1.
destruct (eq_dec d2 nullval) as [Hd2 | Hd2].
- (* no second output *)
  forward_if (temp WgNoise.noise.code._t'10 (Vint Int.zero)).
  { subst d2. contradiction. }
  { forward. entailer!. }
  forward_if.
  { contradiction. }
  forward.
  unfold prot4_eqk in *. subst k1 prk. clear Hb0. subst d2.
  change (hmac (hmac ck data) [Byte.one]) with (kdf1 ck data) in *.
  generalize (kdf1 ck data). intros K. entailer!.
- (* the second output *)
  assert (Hl2: l2 = 32) by (apply H4; auto). subst l2.
  assert_PROP (isptr d2) as Pd2. { entailer!. }
  forward_if (temp WgNoise.noise.code._t'10 (Vint Int.one)).
  { forward. entailer!. }
  { subst d2. contradiction. }
  forward_if.
  2: { inv H8. }
  forward.
  match goal with |- context [data_at Tsh _ ?l v_output] =>
    replace l with (bytes (k1 ++ [Byte.repr 2])) by (symmetry; apply prot4_kdf_out32; auto; lia) end.
  assert (Hd1l: Zlength (k1 ++ [Byte.repr 2]) = 33) by (rewrite Zlength_app, Hk1l; reflexivity).
  forward_call (gv, true, Tsh, v_output, Tsh, v_output, bytes (k1 ++ [Byte.repr 2]), k1 ++ [Byte.repr 2],
    Tsh, v_secret, prk).
  { rewrite Hprk, Hd1l. entailer!. }
  { unfold bytes. rewrite Zlength_map, Hd1l. cancel. }
  { unfold bytes. rewrite Zlength_map, Hd1l. split3; [auto | lia |].
    split; [lia | rewrite sublist_same by (rewrite ?Zlength_map; lia); reflexivity]. }
  assert (Hk2l: Zlength (hmac prk (k1 ++ [Byte.repr 2])) = 32) by apply prot4_kdf_hmac_len.
  prot4_kdf_hide (hmac prk (k1 ++ [Byte.repr 2])) k2.
  replace (Zlength (bytes (k1 ++ [Byte.repr 2]))) with 33 by (unfold bytes; rewrite Zlength_map; auto).
  replace (sublist 32 33 (bytes (k1 ++ [Byte.repr 2]))) with [Vubyte (Byte.repr 2)]
    by (unfold bytes; rewrite map_app, sublist_app2 by (rewrite Zlength_map; lia);
        rewrite Zlength_map, Hk1l; reflexivity).
  forward_call (sh2, Tsh, d2, v_output, 32, k2).
  { sep_apply (prot4_kdf_src32 Tsh k2 (Vubyte (Byte.repr 2)) v_output Hk2l). cancel. }
  change (map Vubyte k2) with (bytes k2).
  sep_apply (wand_frame_elim (data_at Tsh (tarray tuchar 32) (bytes k2) v_output)).
  destruct (eq_dec d3 nullval) as [Hd3 | Hd3].
  + (* no third output *)
    forward_if (temp WgNoise.noise.code._t'9 (Vint Int.zero)).
    { subst d3. contradiction. }
    { forward. entailer!. }
    forward_if.
    { contradiction. }
    forward.
    unfold prot4_eqk in *. subst k2 k1 prk. clear Hb0. subst d3.
    change (hmac (hmac ck data) (hmac (hmac ck data) [Byte.one] ++ [Byte.repr 2])) with (kdf2 ck data) in *.
    change (hmac (hmac ck data) [Byte.one]) with (kdf1 ck data) in *.
    unfold bytes_at. rewrite ?Hk1l, ?Hk2l, ?Hprk.
    generalize (kdf2 ck data). intros K2. generalize (kdf1 ck data). intros K1. entailer!.
  + (* the third output *)
    assert (Hl3: l3 = 32) by (apply H5; auto). subst l3.
    assert_PROP (isptr d3) as Pd3. { entailer!. }
    forward_if (temp WgNoise.noise.code._t'9 (Vint Int.one)).
    { forward. entailer!. }
    { subst d3. contradiction. }
    forward_if.
    2: { inv H9. }
    forward.
    match goal with |- context [data_at Tsh _ ?l v_output] =>
      replace l with (bytes (k2 ++ [Byte.repr 3])) by (symmetry; apply prot4_kdf_out32; auto; lia) end.
    assert (Hd2l: Zlength (k2 ++ [Byte.repr 3]) = 33) by (rewrite Zlength_app, Hk2l; reflexivity).
    forward_call (gv, true, Tsh, v_output, Tsh, v_output, bytes (k2 ++ [Byte.repr 3]), k2 ++ [Byte.repr 3],
      Tsh, v_secret, prk).
    { rewrite Hprk, Hd2l. entailer!. }
    { unfold bytes. rewrite Zlength_map, Hd2l. cancel. }
    { unfold bytes. rewrite Zlength_map, Hd2l. split3; [auto | lia |].
      split; [lia | rewrite sublist_same by (rewrite ?Zlength_map; lia); reflexivity]. }
    assert (Hk3l: Zlength (hmac prk (k2 ++ [Byte.repr 3])) = 32) by apply prot4_kdf_hmac_len.
    prot4_kdf_hide (hmac prk (k2 ++ [Byte.repr 3])) k3.
    replace (Zlength (bytes (k2 ++ [Byte.repr 3]))) with 33 by (unfold bytes; rewrite Zlength_map; auto).
    replace (sublist 32 33 (bytes (k2 ++ [Byte.repr 3]))) with [Vubyte (Byte.repr 3)]
      by (unfold bytes; rewrite map_app, sublist_app2 by (rewrite Zlength_map; lia);
          rewrite Zlength_map, Hk2l; reflexivity).
    forward_call (sh3, Tsh, d3, v_output, 32, k3).
    { sep_apply (prot4_kdf_src32 Tsh k3 (Vubyte (Byte.repr 3)) v_output Hk3l). cancel. }
    change (map Vubyte k3) with (bytes k3).
    sep_apply (wand_frame_elim (data_at Tsh (tarray tuchar 32) (bytes k3) v_output)).
    unfold prot4_eqk in *. subst k3 k2 k1 prk. clear Hb0.
    change (hmac (hmac ck data) (hmac (hmac ck data) (hmac (hmac ck data) [Byte.one] ++ [Byte.repr 2]) ++ [Byte.repr 3]))
      with (kdf3 ck data) in *.
    change (hmac (hmac ck data) (hmac (hmac ck data) [Byte.one] ++ [Byte.repr 2])) with (kdf2 ck data) in *.
    change (hmac (hmac ck data) [Byte.one]) with (kdf1 ck data) in *.
    unfold bytes_at. rewrite ?Hk1l, ?Hk2l, ?Hk3l, ?Hprk.
    generalize (kdf3 ck data). intros K3. generalize (kdf2 ck data). intros K2.
    generalize (kdf1 ck data). intros K1. entailer!.
- (* after the expansion: clear the secrets *)
sep_apply (prot4_kdf_clear32 Tsh prk v_secret Hprk).
forward_call (Tsh, v_secret, 32).
rewrite (@data_at__tarray_tuchar_cs Noise.CS Blake2s.CS Tsh 33).
forward_call (Tsh, v_output, 33).
sep_apply (@data_at_data_at_ Blake2s.CS Tsh (tarray tuchar 32) (Zrepeat (Vubyte Byte.zero) 32) v_secret).
sep_apply (@data_at_data_at_ Blake2s.CS Tsh (tarray tuchar 33) (Zrepeat (Vubyte Byte.zero) 33) v_output).
rewrite !(@data_at__tarray_tuchar_cs Blake2s.CS Noise.CS).
generalize (kdf3 ck data). intros K3. generalize (kdf2 ck data). intros K2.
generalize (kdf1 ck data). intros K1. entailer!.
Qed.

End Bodies.
