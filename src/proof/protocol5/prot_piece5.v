(* The protocol piece v5: every function of prot_G5 (noise.c and the shim, the functions the hs_ laws reach)
   against its specification of prot_specs5.v, for ANY functional models of the primitives satisfying
   prim_api's properties and ANY world compspecs CSw; from the body groups prot_body5_*.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require WgNoise.proof.protocol5.prot_body5_shim WgNoise.proof.protocol5.prot_body5_small
  WgNoise.proof.protocol5.prot_body5_sym WgNoise.proof.protocol5.prot_body5_kp
  WgNoise.proof.protocol5.prot_body5_create_init WgNoise.proof.protocol5.prot_body5_consume_init
  WgNoise.proof.protocol5.prot_body5_create_resp WgNoise.proof.protocol5.prot_body5_consume_resp
  WgNoise.proof.protocol5.prot_body5_begin_session.

Theorem protocol_piece5 :
  forall x25519 aead_enc aead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  piece_ok [u_noise; u_shim] (prot_imports5 x25519 aead_enc aead_dec CSw) (prot_G5 x25519 aead_enc aead_dec CSw).
Proof.
  intros x25519 aead_enc aead_dec CSw Hx Ha.
  pose proof (prot_body5_shim.prot_bodies5_shim x25519 aead_enc aead_dec CSw Hx Ha) as B1.
  pose proof (prot_body5_small.prot_bodies5_small x25519 aead_enc aead_dec CSw Hx Ha) as B2.
  pose proof (prot_body5_sym.prot_bodies5_sym x25519 aead_enc aead_dec CSw Hx Ha) as B3.
  pose proof (prot_body5_kp.prot_bodies5_kp x25519 aead_enc aead_dec CSw Hx Ha) as B4.
  pose proof (prot_body5_create_init.prot_bodies5_create_init x25519 aead_enc aead_dec CSw Hx Ha) as B5.
  pose proof (prot_body5_consume_init.prot_bodies5_consume_init x25519 aead_enc aead_dec CSw Hx Ha) as B6.
  pose proof (prot_body5_create_resp.prot_bodies5_create_resp x25519 aead_enc aead_dec CSw Hx Ha) as B7.
  pose proof (prot_body5_consume_resp.prot_bodies5_consume_resp x25519 aead_enc aead_dec CSw Hx Ha) as B8.
  pose proof (prot_body5_begin_session.prot_bodies5_begin_session x25519 aead_enc aead_dec CSw Hx Ha) as B9.
  repeat match goal with H: _ /\ _ |- _ => destruct H end.
  split; [unfold prot_G5; apply compute_list_norepet_e; reflexivity |].
  unfold prot_G5. repeat apply Forall_cons; try apply Forall_nil.
  all: first [ exists u_noise; split; [simpl; auto |]; eexists; split; [reflexivity | assumption]
             | exists u_shim; split; [simpl; auto |]; eexists; split; [reflexivity | assumption] ].
Qed.
