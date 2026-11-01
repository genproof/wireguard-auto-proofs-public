(* The body of noise.c's hmac against its v5 specification (prot_specs5.v hmac_spec: wg_consts5) in the
   context Gprot5 (prot_prog5.v).  The script is v4's (prot4_noise_kdf_hmac.v), whose helper lemmas on the
   key padding and the buffers of the alias mode are reused; only the constants differ (no cookie labels). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.protocol4.prot4_noise_kdf_hmac.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require Import WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.blake2s.b2s_spec3.
Require WgNoise.proof.libc.libc_piece.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

#[local] Instance CCE_hmac5_n2b : change_composite_env Noise.CS Blake2s.CS.
Proof. make_cs_preserve Noise.CS Blake2s.CS. Defined.
#[local] Instance CCE_hmac5_b2n : change_composite_env Blake2s.CS Noise.CS.
Proof. make_cs_preserve Blake2s.CS Noise.CS. Defined.

Section Bodies.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

(* the key buffer after the first k bytes are zeroed *)
Ltac prot5_hmac_norm_xkey k :=
  match goal with |- context [data_at Tsh (tarray tuchar 64) ?l ?x] =>
    let H := fresh in
    assert (H: l = Zrepeat (Vubyte Byte.zero) k ++ Zrepeat Vundef (64 - k)) by (vm_compute; reflexivity);
    rewrite H; clear H
  end.

Lemma prot5_body_hmac : semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS)
  WgNoise.noise.code.f_hmac hmac_spec.
Proof.
start_function.
do 8 forward. prot5_hmac_norm_xkey 8.
do 8 forward. prot5_hmac_norm_xkey 16.
do 8 forward. prot5_hmac_norm_xkey 24.
do 8 forward. prot5_hmac_norm_xkey 32.
do 8 forward. prot5_hmac_norm_xkey 40.
do 8 forward. prot5_hmac_norm_xkey 48.
do 8 forward. prot5_hmac_norm_xkey 56.
do 8 forward. prot5_hmac_norm_xkey 64.
change (Zrepeat (Vubyte Byte.zero) 64 ++ Zrepeat Vundef (64 - 64)) with (bytes (zeros 64)).
unfold wg_consts5; Intros.
forward_if (PROP () LOCAL (lvar code._i_hash (tarray tuchar 32) v_i_hash;
   lvar code._x_key (tarray tuchar 64) v_x_key;
   lvar noise.code._blake (Tstruct noise.code._blake2s_ctx noattr) v_blake;
   gvars gv; temp noise.code._out out; temp noise.code._in inp;
   temp noise.code._key kp;
   temp noise.code._inlen (Vlong (Int64.repr (Zlength data)));
   temp noise.code._keylen (Vlong (Int64.repr (Zlength key))))
   SEP (data_at_ Tsh (tarray tuchar 32) v_i_hash;
   data_at Tsh (tarray tuchar 64) (bytes (hmac_xkey key)) v_x_key;
   data_at_ Tsh (Tstruct noise.code._blake2s_ctx noattr) v_blake;
   if alias then data_at osh (tarray tuchar (Zlength buf)) buf out
   else data_at_ osh (tarray tuchar 32) out * spec.b2s_bytes ish data inp;
   bytes_at ksh key kp; blake2s_globals gv; @curve25519_globals Noise.CS gv; @zero_page Noise.CS gv)).
- assert (Hk: 64 < Zlength key) by (rewrite !Int64.unsigned_repr in H2 by rep_lia; lia).
  erewrite (@data_at__change_composite Noise.CS Blake2s.CS _ Tsh); [| prove_cs_preserve_type].
  forward_call (Tsh, v_blake, 32).
  rewrite (prot4_kdf_bytes_at_b2s ksh key kp) by lia.
  forward_call (Tsh, v_blake, @nil byte, 32, @nil byte, ksh, kp, key, gv).
  rewrite app_nil_l.
  rewrite (split2_data_at_Tarray_tuchar Tsh 64 32) by (unfold bytes; list_solve).
  Intros.
  rewrite (@data_at_tarray_tuchar_cs Noise.CS Blake2s.CS Tsh 32).
  forward_call (Tsh, v_blake, @nil byte, 32, key, Tsh, v_x_key, gv).
  sep_apply (@data_at_data_at_ Blake2s.CS Tsh t_blake2s_ctx b2s_ctx_zero v_blake).
  erewrite (@data_at__change_composite Blake2s.CS Noise.CS _ Tsh t_blake2s_ctx); [| prove_cs_preserve_type].
  rewrite <- (prot4_kdf_bytes_at_b2s ksh key kp) by lia.
  rewrite (@data_at_tarray_tuchar_cs Blake2s.CS Noise.CS Tsh 32).
  rewrite prot4_kdf_xkey_long by auto.
  pose proof (prot4_kdf_blake2s_len [] key).
  rewrite (split2_data_at_Tarray_tuchar Tsh 64 32 (bytes (blake2s [] 32 key ++ zeros 32)))
    by (unfold bytes, zeros; list_solve).
  replace (sublist 0 32 (bytes (blake2s [] 32 key ++ zeros 32))) with (map Vubyte (blake2s [] 32 key))
    by (unfold bytes, zeros; list_solve).
  replace (sublist 32 64 (bytes (blake2s [] 32 key ++ zeros 32))) with (sublist 32 64 (bytes (zeros 64)))
    by (unfold bytes, zeros; list_solve).
  entailer!.
- assert (Hk: Zlength key <= 64) by (rewrite !Int64.unsigned_repr in H2 by rep_lia; lia).
  pose proof (Zlength_nonneg key).
  rewrite (split2_data_at_Tarray_tuchar Tsh 64 (Zlength key)) by (unfold bytes; list_solve).
  Intros.
  unfold bytes_at.
  forward_call (Tsh, ksh, v_x_key, kp, Zlength key, key).
  rewrite prot4_kdf_xkey_short by auto.
  rewrite (split2_data_at_Tarray_tuchar Tsh 64 (Zlength key) (bytes (key ++ zeros (64 - Zlength key))))
    by (unfold bytes, zeros; list_solve).
  replace (sublist 0 (Zlength key) (bytes (key ++ zeros (64 - Zlength key)))) with (map Vubyte key)
    by (unfold bytes, zeros; list_solve).
  replace (sublist (Zlength key) 64 (bytes (key ++ zeros (64 - Zlength key)))) with
    (sublist (Zlength key) 64 (bytes (zeros 64))) by (unfold bytes, zeros; list_solve).
  unfold bytes_at, bytes. entailer!.
- pose proof (prot4_kdf_xkey_len key) as Hxl.
  set (xk := hmac_xkey key) in *.
  forward_for_simple_bound 64 (EX i: Z, PROP () LOCAL (lvar code._i_hash (tarray tuchar 32) v_i_hash;
   lvar code._x_key (tarray tuchar 64) v_x_key;
   lvar noise.code._blake (Tstruct noise.code._blake2s_ctx noattr) v_blake;
   gvars gv; temp noise.code._out out; temp noise.code._in inp;
   temp noise.code._key kp;
   temp noise.code._inlen (Vlong (Int64.repr (Zlength data)));
   temp noise.code._keylen (Vlong (Int64.repr (Zlength key))))
   SEP (data_at_ Tsh (tarray tuchar 32) v_i_hash;
   data_at Tsh (tarray tuchar 64) (bytes (map (Byte.xor (Byte.repr 54)) (sublist 0 i xk) ++ sublist i 64 xk)) v_x_key;
   data_at_ Tsh (Tstruct noise.code._blake2s_ctx noattr) v_blake;
   if alias then data_at osh (tarray tuchar (Zlength buf)) buf out
   else data_at_ osh (tarray tuchar 32) out * spec.b2s_bytes ish data inp;
   bytes_at ksh key kp; blake2s_globals gv; @curve25519_globals Noise.CS gv; @zero_page Noise.CS gv)).
  + entailer!. rewrite app_nil_l, sublist_same by auto. apply derives_refl.
  + assert (Hz: Znth i (bytes (map (Byte.xor (Byte.repr 54)) (sublist 0 i xk) ++ sublist i 64 xk)) =
                Vubyte (Znth i xk)) by (unfold bytes; list_solve).
    forward.
    { entailer!. rewrite Hz. apply WgNoise.proof.libc.libc_piece.is_int_Vubyte. }
    forward.
    assert (Hb: Znth i (map (Byte.xor (Byte.repr 54)) (sublist 0 i xk) ++ sublist i 64 xk) = Znth i xk)
      by list_solve.
    match goal with |- context [@Znth val ?d i (bytes ?l)] =>
      replace (@Znth val d i (bytes l)) with (Vubyte (Znth i xk)) by (unfold bytes; list_solve) end.
    rewrite prot4_kdf_xor_val by (rewrite Int.unsigned_repr by rep_lia; lia).
    rewrite Int.unsigned_repr by rep_lia.
    rewrite prot4_kdf_xor_step by lia.
    entailer!.
  + (* after the first xor loop *)
    set (ik := map (Byte.xor (Byte.repr 54)) xk).
    assert (Hik: Zlength ik = 64) by (unfold ik; rewrite Zlength_map; auto).
    replace (map (Byte.xor (Byte.repr 54)) (sublist 0 64 xk) ++ sublist 64 64 xk) with ik
      by (unfold ik; rewrite sublist_same by auto; rewrite sublist_nil, app_nil_r; auto).
    erewrite (@data_at__change_composite Noise.CS Blake2s.CS _ Tsh); [| prove_cs_preserve_type].
    forward_call (Tsh, v_blake, 32).
    rewrite (prot4_kdf_data_at_b2s Tsh 64 ik v_x_key) by lia.
    forward_call (Tsh, v_blake, @nil byte, 32, @nil byte, Tsh, v_x_key, ik, gv).
    { entailer!. rewrite Hik. reflexivity. }
    sep_apply (prot4_kdf_in_v alias osh ish out inp buf data SH H1).
    assert (Rd: readable_share (if alias then osh else ish)) by (destruct alias; auto).
    remember (if alias then osh else ish) as dsh eqn:Hdsh.
    remember (if alias then data_at osh (tarray tuchar (Zlength buf)) buf out
              else data_at_ osh (tarray tuchar 32) out * spec.b2s_bytes ish data inp) as IO eqn:HIO.
    forward_call (Tsh, v_blake, @nil byte, 32, [] ++ ik, dsh, inp, data, gv).
    { cancel. }
    sep_apply (wand_frame_elim (spec.b2s_bytes dsh data inp) IO).
    forward_call (Tsh, v_blake, @nil byte, 32, ([] ++ ik) ++ data, Tsh, v_i_hash, gv).
    rewrite app_nil_l.
    set (ih := blake2s [] 32 (ik ++ data)).
    assert (Hih: Zlength ih = 32) by apply prot4_kdf_blake2s_len.
    sep_apply (@data_at_data_at_ Blake2s.CS Tsh t_blake2s_ctx b2s_ctx_zero v_blake).
    rewrite <- (prot4_kdf_data_at_b2s Tsh 64 ik v_x_key) by lia.
    forward_for_simple_bound 64 (EX i: Z, PROP () LOCAL (lvar code._i_hash (tarray tuchar 32) v_i_hash;
      lvar code._x_key (tarray tuchar 64) v_x_key;
      lvar noise.code._blake (Tstruct noise.code._blake2s_ctx noattr) v_blake;
      gvars gv; temp noise.code._out out; temp noise.code._in inp;
      temp noise.code._key kp;
      temp noise.code._inlen (Vlong (Int64.repr (Zlength data)));
      temp noise.code._keylen (Vlong (Int64.repr (Zlength key))))
      SEP (@data_at_ Blake2s.CS Tsh t_blake2s_ctx v_blake;
      @data_at Blake2s.CS Tsh (tarray tuchar 32) (map Vubyte ih) v_i_hash;
      data_at Tsh (tarray tuchar 64) (bytes (map (Byte.xor (Byte.repr 106)) (sublist 0 i ik) ++ sublist i 64 ik)) v_x_key;
      IO; bytes_at ksh key kp; blake2s_globals gv; @curve25519_globals Noise.CS gv; @zero_page Noise.CS gv)).
    * entailer!. rewrite app_nil_l, sublist_same by auto. apply derives_refl.
    * forward.
      { entailer!. apply WgNoise.proof.libc.libc_piece.is_int_Vubyte. }
      forward.
      match goal with |- context [@Znth val ?d i (bytes ?l)] =>
        replace (@Znth val d i (bytes l)) with (Vubyte (Znth i ik)) by (unfold bytes; list_solve) end.
      rewrite prot4_kdf_xor_val by (compute; split; congruence).
      replace (Int.unsigned (Int.xor (Int.repr 92) (Int.repr 54))) with 106 by reflexivity.
      rewrite prot4_kdf_xor_step by lia.
      entailer!.
    * set (ok := map (Byte.xor (Byte.repr 92)) xk).
      assert (Hok: map (Byte.xor (Byte.repr 106)) (sublist 0 64 ik) ++ sublist 64 64 ik = ok).
      { rewrite sublist_same by auto. rewrite sublist_nil, app_nil_r. unfold ik, ok. rewrite map_map.
        apply map_ext. intros; apply prot4_kdf_xor_xor. }
      rewrite Hok.
      assert (Hokl: Zlength ok = 64) by (unfold ok; rewrite Zlength_map; auto).
      forward_call (Tsh, v_blake, 32).
      rewrite (prot4_kdf_data_at_b2s Tsh 64 ok v_x_key) by lia.
      forward_call (Tsh, v_blake, @nil byte, 32, @nil byte, Tsh, v_x_key, ok, gv).
      { entailer!. rewrite Hokl. reflexivity. }
      replace (@data_at Blake2s.CS Tsh (tarray tuchar 32) (map Vubyte ih) v_i_hash)
        with (spec.b2s_bytes Tsh ih v_i_hash)
        by (rewrite spec.b2s_bytes_nonempty by lia; rewrite Hih; reflexivity).
      forward_call (Tsh, v_blake, @nil byte, 32, [] ++ ok, Tsh, v_i_hash, ih, gv).
      rewrite spec.b2s_bytes_nonempty by lia. rewrite Hih.
      sep_apply (@data_at_data_at_ Blake2s.CS Tsh (tarray tuchar 32) (map Vubyte ih) v_i_hash).
      forward_call (Tsh, v_blake, @nil byte, 32, ([] ++ ok) ++ ih, Tsh, v_i_hash, gv).
      rewrite !app_nil_l.
      replace (blake2s [] 32 (ok ++ ih)) with (hmac key data) by reflexivity.
      rewrite HIO.
      sep_apply (prot4_kdf_out_v alias osh ish out inp buf data (hmac key data) (prot4_kdf_hmac_len _ _) H1).
      rewrite (@data_at_tarray_tuchar_cs Blake2s.CS Noise.CS Tsh 32).
      forward_call (osh, Tsh, out, v_i_hash, 32, hmac key data).
      { cancel. }
      sep_apply (wand_frame_elim (data_at osh (tarray tuchar 32) (bytes (hmac key data)) out)).
      rewrite <- (prot4_kdf_data_at_b2s Tsh 64 ok v_x_key) by lia.
      rewrite (@data_at_tarray_tuchar_cs Noise.CS Blake2s.CS Tsh 64).
      sep_apply (@data_at_data_at_ Blake2s.CS Tsh (tarray tuchar 64) (bytes ok) v_x_key).
      forward_call (Tsh, v_x_key, 64).
      rewrite (@data_at_tarray_tuchar_cs Noise.CS Blake2s.CS Tsh 32).
      sep_apply (@data_at_data_at_ Blake2s.CS Tsh (tarray tuchar 32) (map Vubyte (hmac key data)) v_i_hash).
      forward_call (Tsh, v_i_hash, 32).
      sep_apply (@data_at_data_at_ Blake2s.CS Tsh t_blake2s_ctx b2s_ctx_zero v_blake).
      erewrite (@data_at__change_composite Blake2s.CS Noise.CS _ Tsh t_blake2s_ctx); [| prove_cs_preserve_type].
      sep_apply (@data_at_data_at_ Blake2s.CS Tsh (tarray tuchar 64) (Zrepeat (Vubyte Byte.zero) 64) v_x_key).
      sep_apply (@data_at_data_at_ Blake2s.CS Tsh (tarray tuchar 32) (Zrepeat (Vubyte Byte.zero) 32) v_i_hash).
      rewrite !(@data_at__tarray_tuchar_cs Blake2s.CS Noise.CS).
      unfold wg_consts5. entailer!.
      apply derives_refl.
Qed.

End Bodies.
