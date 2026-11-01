(* group noise_mix: the body of noise.c's message_decrypt against its specification
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

Lemma prot4_noise_mix_message_decrypt_prim_b2s sh bs p :
  @prim_bytes Noise.CS sh bs p = spec.b2s_bytes sh bs p.
Proof.
  unfold prim_bytes, spec.b2s_bytes. if_tac; [reflexivity|]. apply data_at_tarray_tuchar_cs.
Qed.

Lemma prot4_noise_mix_message_decrypt_bytes_prim sh bs p : Zlength bs <> 0 ->
  bytes_at sh bs p = @prim_bytes Noise.CS sh bs p.
Proof.
  intros. unfold bytes_at, bytes, prim_bytes. rewrite if_false by auto. reflexivity.
Qed.

Lemma prot4_noise_mix_message_decrypt_bytes32 sh bs p : Zlength bs = 32 ->
  bytes_at sh bs p = @data_at Noise.CS sh (tarray tuchar 32) (map Vubyte bs) p.
Proof.
  intros. unfold bytes_at, bytes. rewrite H. reflexivity.
Qed.

Section Body.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.

Lemma prot4_noise_mix_body_message_decrypt :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_message_decrypt (message_decrypt_spec aead_dec).
Proof.
intros _ Ha _.
start_function.
unfold wg_consts; Intros.
rewrite (prot4_noise_mix_message_decrypt_bytes32 shk key kp H0).
rewrite (prot4_noise_mix_message_decrypt_bytes_prim shh h hp) by lia.
change (out_bytes shd old dp) with (@prim_out Noise.CS shd old dp).
forward_call (shd, dp, old, shs, sp, c, shh, hp, h, 0, shk, kp, key, gv).
{ entailer!. rewrite H1. reflexivity. }
destruct (aead_dec key 0 h c) as [pt|] eqn:Hd.
- forward_if.
  { exfalso. apply Int.one_not_zero. assumption. }
  rewrite <- (prot4_noise_mix_message_decrypt_bytes_prim shh h hp) by lia.
  rewrite prot4_noise_mix_message_decrypt_prim_b2s.
  forward_call (gv, shh, hp, h, shs, sp, c).
  { unfold wg_consts. cancel. }
  rewrite <- prot4_noise_mix_message_decrypt_prim_b2s.
  forward.
  rewrite (prot4_noise_mix_message_decrypt_bytes32 shk key kp H0).
  unfold wg_consts. entailer!. apply derives_refl.
- forward_if.
  2: { exfalso; apply H3; reflexivity. }
  forward.
  rewrite <- (prot4_noise_mix_message_decrypt_bytes_prim shh h hp) by lia.
  rewrite (prot4_noise_mix_message_decrypt_bytes32 shk key kp H0).
  unfold wg_consts. entailer!. apply derives_refl.
Qed.

End Body.
