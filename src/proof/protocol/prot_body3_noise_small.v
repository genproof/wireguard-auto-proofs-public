(* Body proofs of the protocol piece, group noise_small.
   Target: prot_bodies3_noise_small.  Prove each function's body against its specification (prot_specs3.v) in the
   compspecs of its unit, with the context Gprot3 (prot_prog3.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_prog3.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

Section NoiseSmall.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

Definition Gn := Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS.

(* the bytes of put_unaligned_be32 as the stored values *)
Lemma prot3_noise_small_vubyte_shru (v: int) (n: Z) :
  0 <= n < 32 ->
  Vubyte (Byte.repr (Int.unsigned v / 2 ^ n)) = Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.shru v (Int.repr n)))).
Proof.
  intros Hn. unfold Vubyte. f_equal. rewrite Int.zero_ext_idem by lia.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 _)).
  rewrite Int.zero_ext_mod by (cbn; lia).
  rewrite Int.shru_div_two_p. rewrite (Int.unsigned_repr n) by (cbn; lia).
  rewrite Byte.unsigned_repr_eq. rewrite two_p_correct.
  rewrite Int.unsigned_repr. reflexivity.
  pose proof (Int.unsigned_range v). assert (0 < 2 ^ n) by (apply Z.pow_pos_nonneg; lia).
  split. apply Z.div_pos; lia.
  apply Z.le_trans with (Int.unsigned v); [apply Z.div_le_upper_bound; nia | unfold Int.max_unsigned; lia].
Qed.

Lemma prot3_noise_small_be32_vals (v: int) :
  bytes (be32 v) =
  [Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.shru v (Int.repr 24))));
   Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.shru v (Int.repr 16))));
   Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.shru v (Int.repr 8))));
   Vint (Int.zero_ext 8 (Int.zero_ext 8 v))].
Proof.
  unfold bytes, be32. cbn [map].
  replace (Int.zero_ext 8 (Int.zero_ext 8 v)) with (Int.zero_ext 8 (Int.zero_ext 8 (Int.shru v (Int.repr 0))))
    by (rewrite Int.shru_zero; reflexivity).
  rewrite <- !prot3_noise_small_vubyte_shru by lia. reflexivity.
Qed.

Lemma prot3_noise_small_be32_len (v: int) : Zlength (be32 v) = 4.
Proof. reflexivity. Qed.

Lemma prot3_noise_small_body_rounddown :
  @semax_body (QPvarspecs Noise.qp) Gn Noise.CS
    WgNoise.noise.code.f_quickproof_rounddown_pow_of_two quickproof_rounddown_pow_of_two_spec.
Proof.
  start_function. forward.
  forward_while (EX k: Z, PROP (0 <= k; 2 ^ k <= n)
    LOCAL (temp WgNoise.noise.code._r (Vlong (Int64.repr (2 ^ k)));
           temp WgNoise.noise.code._n (Vlong (Int64.repr n))) SEP ()).
  - Exists 0. entailer!.
  - entailer!.
  - forward.
    assert (0 <= n / 2 <= n)%Z by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    rewrite Int64.unsigned_repr in HRE by rep_lia.
    assert (2 * 2 ^ k <= n)%Z by (pose proof (Z.mul_div_le n 2); lia).
    assert (E: (2 ^ (k + 1) = 2 ^ k * 2)%Z) by (rewrite Z.pow_add_r by lia; reflexivity).
    Exists (k + 1). entailer!. rewrite E. reflexivity.
  - forward.
    assert (0 <= n / 2 <= n)%Z by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    rewrite Int64.unsigned_repr in HRE by rep_lia.
    assert (E: (2 ^ Z.succ k = 2 ^ k * 2)%Z) by (rewrite Z.pow_succ_r by lia; lia).
    assert (n < 2 ^ Z.succ k)%Z by (pose proof (Z.mod_pos_bound n 2); pose proof (Z.div_mod n 2); lia).
    rewrite (Z.log2_unique n k) by lia. entailer!.
Qed.

Lemma prot3_noise_small_body_be32 :
  @semax_body (QPvarspecs Noise.qp) Gn Noise.CS
    WgNoise.noise.code.f_put_unaligned_be32 put_unaligned_be32_spec.
Proof.
  start_function. forward. forward. forward. forward. forward.
  unfold bytes_at. rewrite prot3_noise_small_be32_len, prot3_noise_small_be32_vals. entailer!.
Qed.

Lemma prot3_noise_small_shru32 (v: int64) :
  Int64.unsigned (Int64.shru' v (Int.repr 32)) = Int64.unsigned v / 2 ^ 32.
Proof.
  unfold Int64.shru'. change (Int.unsigned (Int.repr 32)) with 32.
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Int64.unsigned_range v).
  apply Int64.unsigned_repr. split; [apply Z.div_pos; lia|].
  apply Z.le_trans with (Int64.unsigned v); [apply Z.div_le_upper_bound; lia | unfold Int64.max_unsigned; lia].
Qed.

(* the call put_unaligned_be32((u32)(v >> 32), p): VST's simpl must not unfold the shift *)
Local Opaque Int64.shru' Int64.shru.

Lemma prot3_noise_small_body_be64 :
  @semax_body (QPvarspecs Noise.qp) Gn Noise.CS
    WgNoise.noise.code.f_put_unaligned_be64 put_unaligned_be64_spec.
Proof.
  start_function. assert_PROP (field_compatible (tarray tuchar 8) [] p) by entailer!.
  rewrite (split2_data_at__Tarray_tuchar sh 8 4) by (first [lia | exact H | destruct H; assumption]).
  rewrite field_address0_offset by (apply arr_field_compatible0; [exact H | lia]).
  change (nested_field_offset (Tarray tuchar 8 noattr) (SUB 4)) with 4.
  replace (8 - 4) with 4 by lia. fold (tarray tuchar 4).
  forward_call (Int.repr (Int64.unsigned (Int64.shru' v (Int.repr 32))), sh, p).
  { cancel. }
  forward_call (Int.repr (Int64.unsigned v), sh, offset_val 4 p).
  rewrite prot3_noise_small_shru32.
  unfold bytes_at, be64, bytes. rewrite map_app, Zlength_app, !prot3_noise_small_be32_len.
  rewrite (split2_data_at_Tarray_app 4 8 sh tuchar)
    by (rewrite Zlength_map, prot3_noise_small_be32_len; reflexivity).
  rewrite field_address0_offset by (apply arr_field_compatible0; [exact H | lia]).
  change (nested_field_offset (Tarray tuchar 8 noattr) (SUB 4)) with 4.
  replace (8 - 4) with 4 by lia. entailer!.
Qed.

(* noise.c's static inline kref_get_unless_zero is gone (quickproof_kref.h: the shim's
   wg_shim_refcount_inc_not_zero, specified in prot_specs3.v and proved in prot_body3_shim_rc.v) *)

Lemma prot3_noise_small_body_gensecret :
  @semax_body (QPvarspecs Noise.qp) Gn Noise.CS
    WgNoise.noise.code.f_curve25519_generate_secret curve25519_generate_secret_spec.
Proof.
  start_function. forward_call (gv, S, sh, p, 32). Intros r. unfold bytes_at. rewrite H.
  forward_call (sh, p, r). Exists r.
  assert (Zlength (clamp r) = 32) by (unfold clamp; list_solve).
  unfold bytes_at, bytes. rewrite H0. entailer!.
Qed.

Lemma prot3_noise_small_body_reset_lsh :
  @semax_body (QPvarspecs Noise.qp) Gn Noise.CS
    WgNoise.noise.code.f_wg_noise_reset_last_sent_handshake wg_noise_reset_last_sent_handshake_spec.
Proof.
  start_function. forward_call (gv, S). unfold t_atomic64. forward. entailer!.
Qed.

Lemma prot3_noise_small_body_hs_zero :
  @semax_body (QPvarspecs Noise.qp) Gn Noise.CS
    WgNoise.noise.code.f_handshake_zero handshake_zero_spec.
Proof.
  start_function. unfold hs_rep. Intros lk. unfold t_hs.
  assert_PROP (field_compatible (Tstruct I._noise_handshake noattr) (DOT I._ephemeral_private) h /\
    field_compatible (Tstruct I._noise_handshake noattr) (DOT I._remote_ephemeral) h /\
    field_compatible (Tstruct I._noise_handshake noattr) (DOT I._hash) h /\
    field_compatible (Tstruct I._noise_handshake noattr) (DOT I._chaining_key) h) as FC.
  { entailer!. }
  destruct FC as (FC1 & FC2 & FC3 & FC4).
  rewrite (field_at_data_at sh (Tstruct I._noise_handshake noattr) [StructField I._ephemeral_private]).
  forward_call (sh, field_address (Tstruct I._noise_handshake noattr) [StructField I._ephemeral_private] h, 0, 32).
  rewrite (field_at_data_at sh (Tstruct I._noise_handshake noattr) [StructField I._remote_ephemeral]).
  forward_call (sh, field_address (Tstruct I._noise_handshake noattr) [StructField I._remote_ephemeral] h, 0, 32).
  rewrite (field_at_data_at sh (Tstruct I._noise_handshake noattr) [StructField I._hash]).
  forward_call (sh, field_address (Tstruct I._noise_handshake noattr) [StructField I._hash] h, 0, 32).
  rewrite (field_at_data_at sh (Tstruct I._noise_handshake noattr) [StructField I._chaining_key]).
  forward_call (sh, field_address (Tstruct I._noise_handshake noattr) [StructField I._chaining_key] h, 0, 32).
  forward. forward.
  assert (Z0: bytes (zeros 32) = Zrepeat (Vubyte (Byte.repr 0)) 32) by reflexivity.
  unfold hs_rep, hs_zero.
  cbn [hs_state hs_lic hs_sid hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts hs_rindex].
  rewrite Z0.
  rewrite (field_at_data_at sh (Tstruct I._noise_handshake noattr) [StructField I._ephemeral_private]).
  rewrite (field_at_data_at sh (Tstruct I._noise_handshake noattr) [StructField I._remote_ephemeral]).
  rewrite (field_at_data_at sh (Tstruct I._noise_handshake noattr) [StructField I._hash]).
  rewrite (field_at_data_at sh (Tstruct I._noise_handshake noattr) [StructField I._chaining_key]).
  Exists lk. entailer!.
  unfold hs_ok in *; simpl; tauto.
Qed.

Lemma prot3_noise_small_body_tai64n :
  @semax_body (QPvarspecs Noise.qp) Gn Noise.CS
    WgNoise.noise.code.f_tai64n_now tai64n_now_spec.
Proof.
  start_function.
  forward_call (gv, S, Tsh, v_now).
  forward_call 20000000.
  change (2 ^ Z.log2 20000000) with 16777216.
  unfold t_timespec. forward. forward. forward.
  replace (Int64.not (Int64.sub (Int64.repr 16777216) (Int64.repr (Int.signed (Int.repr 1)))))
    with (Int64.not (Int64.repr 16777215)) by reflexivity.
  assert_PROP (field_compatible (tarray tuchar 12) [] p) as FC by entailer!.
  rewrite (split2_data_at__Tarray_tuchar sh 12 8) by (first [lia | exact FC | destruct FC; assumption]).
  rewrite field_address0_offset by (apply arr_field_compatible0; [exact FC | lia]).
  change (nested_field_offset (Tarray tuchar 12 noattr) (SUB 8)) with 8.
  replace (12 - 8) with 4 by lia. fold (tarray tuchar 4). fold (tarray tuchar 8).
  forward_call (Int64.add (Int64.repr 4611686018427387914) (s_rsec S), sh, p).
  { cancel. }
  forward.
  forward_call (Int.repr (Int64.unsigned (Int64.and (s_rnsec S) (Int64.not (Int64.repr 16777215)))),
                sh, offset_val 8 p).
  unfold tai64n, bytes_at, bytes. rewrite map_app, Zlength_app, !prot3_noise_small_be32_len.
  assert (L8: forall w, Zlength (be64 w) = 8) by reflexivity. rewrite L8.
  rewrite (split2_data_at_Tarray_app 8 12 sh tuchar)
    by (rewrite Zlength_map; first [apply L8 | apply prot3_noise_small_be32_len]).
  rewrite field_address0_offset by (apply arr_field_compatible0; [exact FC | lia]).
  change (nested_field_offset (Tarray tuchar 12 noattr) (SUB 8)) with 8.
  replace (12 - 8) with 4 by lia. entailer!.
Qed.

End NoiseSmall.

Theorem prot_bodies3_noise_small :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body (QPvarspecs Noise.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_quickproof_rounddown_pow_of_two quickproof_rounddown_pow_of_two_spec) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_put_unaligned_be32 put_unaligned_be32_spec) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_put_unaligned_be64 put_unaligned_be64_spec) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_curve25519_generate_secret curve25519_generate_secret_spec) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_wg_noise_reset_last_sent_handshake wg_noise_reset_last_sent_handshake_spec) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_handshake_zero handshake_zero_spec) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_tai64n_now tai64n_now_spec).
Proof.
  intros. repeat match goal with |- _ /\ _ => split end; first [apply prot3_noise_small_body_rounddown | apply prot3_noise_small_body_be32 | apply prot3_noise_small_body_be64 | apply prot3_noise_small_body_gensecret | apply prot3_noise_small_body_reset_lsh | apply prot3_noise_small_body_hs_zero | apply prot3_noise_small_body_tai64n].
Qed.
