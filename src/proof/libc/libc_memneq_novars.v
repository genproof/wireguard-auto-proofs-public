(* The inline crypto_memneq of crypto/utils.h, on the copy compiled into chacha20poly1305.c, with no global
   variables in its context.

   libc_piece.v proves the copy of curve25519.c with the varspecs of curve25519.c (its two static points).  A
   program that does not link curve25519.c (the AEAD laws: chacha20poly1305.c and the primitives only) has
   neither those globals nor that unit, so that body does not move into it (asm_body_lift needs every varspec
   of the body's context in the program).  This is the same specification (crypto_memneq_spec at
   Curve25519.CS, the entry of libc_G) and the same context of functions, for chacha20poly1305.c's copy (the
   same Clight), proved under Chacha20poly1305.CS with no varspecs; it moves into every program that links
   chacha20poly1305.c and the shim. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Shim.
Require WgNoise.chacha20poly1305.code.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.libc.libc_piece.

(* chacha20poly1305.c's copy is the Clight of curve25519.c's *)
Lemma crypto_memneq_c20p_eq :
  WgNoise.chacha20poly1305.code.f_crypto_memneq = WgNoise.curve25519.code.f_crypto_memneq.
Proof. reflexivity. Qed.

Section Bodies.
Variable CSw: compspecs.
#[local] Existing Instance Chacha20poly1305.CS.

Lemma body_crypto_memneq_c20p:
  semax_body nil (libc_imports CSw Chacha20poly1305.CS ++ libc_G CSw)
    WgNoise.chacha20poly1305.code.f_crypto_memneq (@crypto_memneq_spec Curve25519.CS).
Proof.
  start_function.
  rewrite (@data_at_tarray_tuchar_cs Curve25519.CS Shim.CS sh1), (@data_at_tarray_tuchar_cs Curve25519.CS Shim.CS sh2).
  forward_call (sh1, sh2, p1, p2, n, a, b).
  rewrite (@data_at_tarray_tuchar_cs Shim.CS Curve25519.CS sh1), (@data_at_tarray_tuchar_cs Shim.CS Curve25519.CS sh2).
  pose proof (memneq_Z_range a b).
  pose proof (memneq_Z_zero a b ltac:(lia)).
  forward_if (PROP ()
    LOCAL (temp WgNoise.chacha20poly1305.code._t'2 (Vint (if memneq_bool a b then Int.one else Int.zero)))
    SEP (@data_at Curve25519.CS sh1 (tarray tuchar n) (map Vubyte a) p1;
         @data_at Curve25519.CS sh2 (tarray tuchar n) (map Vubyte b) p2)).
  - forward. entailer!. unfold memneq_bool.
    destruct (list_eq_dec Byte.eq_dec a b) as [E|E]; auto.
    exfalso. apply H4. rewrite (proj2 H3 E). auto.
  - forward. entailer!.
    assert (memneq_Z a b = 0) by (apply repr_inj_unsigned64; auto; rep_lia).
    unfold memneq_bool. destruct (list_eq_dec Byte.eq_dec a b) as [E|E]; auto.
    exfalso. apply E, H3. auto.
  - forward.
Qed.

End Bodies.
