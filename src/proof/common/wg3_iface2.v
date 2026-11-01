(* the strengthened interfaces of the AEAD and Curve25519 pieces, as the protocol laws need them.  wg3_iface.v stays as it is (the finished subtrees are proved against it).

   - aead3b_ok: aead3_ok with the NULL-tolerant decryption templates of prot_dec3.v (an empty destination is emp:
     noise.c's consume_response calls chacha20poly1305_decrypt(NULL, src, 16, ...)), and cc_default for every entry
     of G (asm_harness_safe needs it for the internal entries too).
   - x25519_ok3b: x25519_ok3 with cc_default for every entry of G.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Export WgNoise.proof.common.wg3_iface.

Definition cc_default_all (G: funspecs) : Prop :=
  Forall (fun ix => callingconvention_of_funspec (snd ix) = cc_default) G.

Definition aead_iface3b
  (enc: list byte -> Z -> list byte -> list byte -> list byte)
  (dec: list byte -> Z -> list byte -> list byte -> option (list byte))
  (xenc: list byte -> list byte -> list byte -> list byte -> list byte)
  (xdec: list byte -> list byte -> list byte -> list byte -> option (list byte)) : funspecs :=
  [@chacha20poly1305_encrypt_spec_of Chacha20poly1305.CS enc;
   @chacha20poly1305_decrypt_spec_of3 Chacha20poly1305.CS dec;
   @xchacha20poly1305_encrypt_spec_of Chacha20poly1305.CS xenc;
   @xchacha20poly1305_decrypt_spec_of3 Chacha20poly1305.CS xdec].

Definition aead3b_ok : Prop :=
  exists (G: funspecs)
         (enc: list byte -> Z -> list byte -> list byte -> list byte)
         (dec: list byte -> Z -> list byte -> list byte -> option (list byte))
         (xenc: list byte -> list byte -> list byte -> list byte -> list byte)
         (xdec: list byte -> list byte -> list byte -> list byte -> option (list byte)),
    aead_props enc dec /\ xaead_props xenc xdec /\
    piece_ok aead_units3 aead_imports3 G /\
    map fst G = aead_idents3 /\
    asm_covers G (aead_iface3b enc dec xenc xdec) /\
    cc_default_all G.

Definition x25519_ok3b : Prop :=
  exists (G: funspecs) (x: list byte -> list byte -> list byte),
    x25519_props x /\
    piece_ok x25519_units3 x25519_imports3 G /\
    map fst G = x25519_idents3 /\
    asm_covers G (x25519_iface3 x) /\
    cc_default_all G.
