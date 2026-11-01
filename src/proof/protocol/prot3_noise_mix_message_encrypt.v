(* group noise_mix: the body of noise.c's message_encrypt against its specification
   (prot_specs3.v) in the context Gprot3 (prot_prog3.v), for ANY primitive models with their properties. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_prog3.
Require WgNoise.proof.libc.libc_bytes WgNoise.proof.blake2s.spec.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

Lemma prot3_noise_mix_message_encrypt_b2s sh bs p : Zlength bs <> 0 ->
  @data_at Noise.CS sh (tarray tuchar (Zlength bs)) (map Vubyte bs) p = WgNoise.proof.blake2s.spec.b2s_bytes sh bs p.
Proof.
  intros. rewrite WgNoise.proof.blake2s.spec.b2s_bytes_nonempty by auto.
  apply WgNoise.proof.libc.libc_bytes.data_at_tarray_tuchar_cs.
Qed.

Lemma prot3_noise_mix_message_encrypt_prim sh bs p : Zlength bs <> 0 ->
  bytes_at sh bs p = @prim_bytes Noise.CS sh bs p.
Proof.
  intros. unfold bytes_at, bytes, prim_bytes. rewrite if_false by auto. reflexivity.
Qed.

Section Body.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.

Lemma prot3_noise_mix_body_message_encrypt :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body (QPvarspecs Noise.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_message_encrypt (message_encrypt_spec aead_enc).
Proof.
intros _ Ha _.
start_function.
unfold wg_consts; Intros.
rewrite (prot3_noise_mix_message_encrypt_prim shh h hp) by lia.
unfold bytes_at, bytes. rewrite H0.
forward_call (shd, dp, shs, sp, m, shh, hp, h, 0, shk, kp, key, gv).
{ entailer!. rewrite H1. reflexivity. }
pose proof (aead_enc_length _ _ Ha key 0 h m) as HL.
remember (aead_enc key 0 h m) as c eqn:Ec.
pose proof (Zlength_nonneg m) as Hm0.
rewrite <- HL.
rewrite (prot3_noise_mix_message_encrypt_b2s shd c dp) by lia.
rewrite <- (prot3_noise_mix_message_encrypt_prim shh h hp) by lia.
forward_call (gv, shh, hp, h, shd, dp, c).
{ entailer!. rewrite HL. simpl. f_equal. }
{ unfold wg_consts. cancel. }
rewrite <- (prot3_noise_mix_message_encrypt_b2s shd c dp) by lia.
replace (data_at shk (tarray tuchar 32) (map Vubyte key) kp) with (bytes_at shk key kp)
  by (unfold bytes_at, bytes; rewrite H0; reflexivity).
generalize (mix_hash h c); intros mh.
rewrite <- HL. unfold bytes.
entailer!.
Qed.

End Body.
