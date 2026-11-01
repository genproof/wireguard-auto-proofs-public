(* group noise_mix: the body of noise.c's mix_hash against its specification
   (prot_specs4.v) in the context Gprot4 (prot_prog4.v), for ANY primitive models with their properties. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require Import WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.blake2s.b2s_spec3.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

#[local] Instance prot4_noise_mix_mix_hash_n2b : change_composite_env Noise.CS Blake2s.CS.
Proof. make_cs_preserve Noise.CS Blake2s.CS. Defined.
#[local] Instance prot4_noise_mix_mix_hash_b2n : change_composite_env Blake2s.CS Noise.CS.
Proof. make_cs_preserve Blake2s.CS Noise.CS. Defined.

Lemma prot4_noise_mix_mix_hash_b2s sh bs p : Zlength bs <> 0 ->
  bytes_at sh bs p = spec.b2s_bytes sh bs p.
Proof.
  intros. unfold bytes_at, bytes. rewrite spec.b2s_bytes_nonempty by auto.
  apply data_at_tarray_tuchar_cs.
Qed.

Lemma prot4_noise_mix_mix_hash_len h d : Zlength (mix_hash h d) = 32.
Proof.
  unfold mix_hash, HASH, blake2s, b2s_digest_stream, b2s_out. rewrite Zlength_map. reflexivity.
Qed.

Section Body.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.

Lemma prot4_noise_mix_body_mix_hash :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_mix_hash mix_hash_spec.
Proof.
intros _ _ _.
start_function.
unfold wg_consts; Intros.
erewrite (@data_at__change_composite Noise.CS Blake2s.CS _ Tsh); [| prove_cs_preserve_type].
forward_call (Tsh, v_blake, 32).
rewrite (prot4_noise_mix_mix_hash_b2s shh h hp) by lia.
forward_call (Tsh, v_blake, @nil byte, 32, @nil byte, shh, hp, h, gv).
{ entailer!. rewrite H. reflexivity. }
forward_call (Tsh, v_blake, @nil byte, 32, [] ++ h, shs, sp, src, gv).
rewrite (spec.b2s_bytes_nonempty shh h hp) by lia. rewrite H.
sep_apply (@data_at_data_at_ Blake2s.CS shh (tarray tuchar 32) (map Vubyte h) hp).
forward_call (Tsh, v_blake, @nil byte, 32, ([] ++ h) ++ src, shh, hp, gv).
sep_apply (@data_at_data_at_ Blake2s.CS Tsh t_blake2s_ctx b2s_ctx_zero v_blake).
erewrite (@data_at__change_composite Blake2s.CS Noise.CS _ Tsh t_blake2s_ctx); [| prove_cs_preserve_type].
rewrite app_nil_l.
change (blake2s [] 32 (h ++ src)) with (mix_hash h src).
pose proof (prot4_noise_mix_mix_hash_len h src) as Hl.
generalize (mix_hash h src) Hl; intros mh Hmh.
forward.
unfold wg_consts, bytes_at, bytes. rewrite Hmh.
rewrite (@data_at_tarray_tuchar_cs Blake2s.CS Noise.CS).
entailer!.
Qed.

End Body.
