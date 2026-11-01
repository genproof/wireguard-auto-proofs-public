(* group noise_mix: the body of noise.c's handshake_init against its specification
   (prot_specs3.v) in the context Gprot3 (prot_prog3.v), for ANY primitive models with their properties. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_prog3.
Require WgNoise.proof.libc.libc_bytes WgNoise.proof.blake2s.spec.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

Lemma prot3_noise_mix_handshake_init_b2s sh bs p : Zlength bs <> 0 ->
  bytes_at sh bs p = WgNoise.proof.blake2s.spec.b2s_bytes sh bs p.
Proof.
  intros. unfold bytes_at, bytes. rewrite WgNoise.proof.blake2s.spec.b2s_bytes_nonempty by auto.
  apply WgNoise.proof.libc.libc_bytes.data_at_tarray_tuchar_cs.
Qed.

Section Body.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.

Lemma prot3_noise_mix_body_handshake_init :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body (QPvarspecs Noise.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_handshake_init handshake_init_spec.
Proof.
intros _ _ _.
start_function.
unfold noise_globals, noise_globals_raw. Intros.
(* never let the unifier see the BLAKE2s terms init_hash / init_ck *)
remember init_hash as IH eqn:EIH. remember init_ck as ICK eqn:EICK.
remember handshake_name as HN eqn:EHN. remember identifier_name as IN eqn:EIN.
rewrite (prot3_noise_mix_handshake_init_b2s shr rs rp) by lia.
unfold bytes_at.
forward_call (shh, Ews, hp, gv I._handshake_init_hash, 32, IH).
forward_call (shc, Ews, ckp, gv I._handshake_init_chaining_key, 32, ICK).
forward_call (gv, shh, hp, IH, shr, rp, rs).
{ apply prop_right; simpl; rewrite H; reflexivity. }
{ unfold bytes_at, bytes. rewrite H0. cancel. }
rewrite <- (prot3_noise_mix_handshake_init_b2s shr rs rp) by lia.
unfold noise_globals, noise_globals_raw. rewrite <- EIH, <- EICK, <- EHN, <- EIN. clear EIH EICK EHN EIN.
entailer!.
unfold bytes_at, bytes. rewrite H1. cancel.
Qed.

End Body.
