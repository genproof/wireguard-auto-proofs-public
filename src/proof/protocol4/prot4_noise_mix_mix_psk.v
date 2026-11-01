(* group noise_mix: the body of noise.c's mix_psk against its specification
   (prot_specs4.v) in the context Gprot4 (prot_prog4.v), for ANY primitive models with their properties. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require WgNoise.proof.libc.libc_bytes WgNoise.proof.blake2s.spec.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

Lemma prot4_noise_mix_mix_psk_b2s sh bs p : Zlength bs <> 0 ->
  bytes_at sh bs p = WgNoise.proof.blake2s.spec.b2s_bytes sh bs p.
Proof.
  intros. unfold bytes_at, bytes. rewrite WgNoise.proof.blake2s.spec.b2s_bytes_nonempty by auto.
  apply WgNoise.proof.libc.libc_bytes.data_at_tarray_tuchar_cs.
Qed.

Lemma prot4_noise_mix_mix_psk_forget sh bs p : Zlength bs = 32 ->
  bytes_at sh bs p |-- @data_at_ Noise.CS sh (tarray tuchar 32) p.
Proof.
  intros. unfold bytes_at, bytes. rewrite H. apply data_at_data_at_.
Qed.

Lemma prot4_noise_mix_mix_psk_hmac_len key m : Zlength (hmac key m) = 32.
Proof.
  unfold hmac, HASH, WgNoise.proof.blake2s.model.blake2s, WgNoise.proof.blake2s.model.b2s_digest_stream, WgNoise.proof.blake2s.model.b2s_out. rewrite Zlength_map. reflexivity.
Qed.

Section Body.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.

Lemma prot4_noise_mix_body_mix_psk :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_mix_psk mix_psk_spec.
Proof.
intros _ _ _.
start_function.
assert (L2: Zlength (kdf2 ck psk) = 32) by apply prot4_noise_mix_mix_psk_hmac_len.
assert_PROP (isptr v_temp_hash) by entailer!.
assert_PROP (isptr kp) by entailer!.
rewrite (prot4_noise_mix_mix_psk_b2s shp psk pp) by lia.
forward_call (gv, true, ckp, v_temp_hash, kp, 32, 32, shc, Tsh, shk, shp, pp, psk, shc, ckp, ck).
{ apply prop_right; simpl; rewrite H1; reflexivity. }
{ destruct (eq_dec v_temp_hash nullval) as [E|_]; [subst; contradiction|].
  destruct (eq_dec kp nullval) as [E|_]; [subst; contradiction|]. cancel. }
destruct (eq_dec v_temp_hash nullval) as [E|_]; [subst; contradiction|].
destruct (eq_dec kp nullval) as [E|_]; [subst; contradiction|].
rewrite (prot4_noise_mix_mix_psk_b2s Tsh (kdf2 ck psk) v_temp_hash) by lia.
forward_call (gv, shh, hp, h, Tsh, v_temp_hash, kdf2 ck psk).
rewrite <- (prot4_noise_mix_mix_psk_b2s Tsh (kdf2 ck psk) v_temp_hash) by lia.
sep_apply (prot4_noise_mix_mix_psk_forget Tsh (kdf2 ck psk) v_temp_hash L2).
forward_call (Tsh, v_temp_hash, 32).
sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (Zrepeat (Vubyte Byte.zero) 32) v_temp_hash).
rewrite <- (prot4_noise_mix_mix_psk_b2s shp psk pp) by lia.
entailer!.
Qed.

End Body.
