(* the NULL-tolerant specifications of the reference AEAD of
   common.h that the transport harnesses call as ref_aead_decrypt(ref_pt, pkt + 16, enc_len, NULL, 0, nonce, key).

   prim_aead's specifications (haead_spec3.v) describe every byte buffer by `data_at sh (tarray tuchar n) ..`, which
   implies a pointer even when n = 0: unsatisfiable for ad = NULL (and for a NULL ref_pt = malloc(0) in law
   transport_keepalive).  Here, as in prot_dec3.v / prim_api.v: an input buffer is `prim_bytes` and the output of
   ref_aead_decrypt / ref_chacha20_xor is `prim_out` (emp when empty, any pointer then).  Four functions change:
   rp_padded (its input), ref_aead_tag (ad and ct), ref_chacha20_xor (dst and src), ref_aead_decrypt (dst, src, ad).

   Conventions of the shared transport layer: compspecs W_prim_aead (every transport world
   includes it), varspecs [] (none of these functions reads a global), the static `minusp` of rp_final is a
   parameter `mp` (its identifier is transport_<law>__minusp), the Clight functions are prim_aead's (byte-identical
   in the four transport harnesses).  Each law lifts the bodies into its whole program (asm_lib's asm_piece_lift). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Export WgNoise.proof.harness.prim_aead.haead_spec3.
Require Export WgNoise.proof.harness.common4t.ht4c_spec.
Require WgNoise.harness.x_prim_aead.code.

#[local] Existing Instance W_prim_aead.
Local Open Scope Z_scope.

(* rp_padded(p, in, len): as haead_spec3's rp_padded_spec, the input `prim_bytes` *)
Definition rp_padded_spec_n :=
  DECLARE HA._rp_padded
  WITH sh: share, p: val, r: list int, h: list int, s: list byte, ish: share, ip: val, buf: list byte
  PRE [ tptr t_rpoly, tptr tuchar, tulong ]
    PROP (writable_share sh; readable_share ish; Zlength r = 17; Zlength h = 17;
          Zlength buf <= Int64.max_signed)
    PARAMS (p; ip; Vlong (Int64.repr (Zlength buf)))
    SEP (data_at sh t_rpoly (rpoly_val r h s) p; prim_bytes ish buf ip)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh t_rpoly (rpoly_val r (haead_padded r h buf) s) p; prim_bytes ish buf ip).

(* ref_aead_tag(tag, key, nonce, ad, adlen, ct, ctlen): ad and ct `prim_bytes` *)
Definition ref_aead_tag_spec_n (mp: ident) :=
  DECLARE HA._ref_aead_tag
  WITH tsh: share, tag: val, ksh: share, kp: val, key: list byte, nonce: Z, ash: share, ad: val,
       a: list byte, csh: share, cp: val, ct: list byte, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong, tptr tuchar, tulong ]
    PROP (writable_share tsh; readable_share ksh; readable_share ash; readable_share csh; Zlength key = 32;
          0 <= nonce <= Int64.max_unsigned; Zlength a <= Int64.max_signed; Zlength ct <= Int64.max_signed)
    PARAMS (tag; kp; Vlong (Int64.repr nonce); ad; Vlong (Int64.repr (Zlength a)); cp;
            Vlong (Int64.repr (Zlength ct))) GLOBALS (gv)
    SEP (data_at_ tsh (tarray tuchar 16) tag; data_at ksh (tarray tuchar 32) (map Vubyte key) kp;
         prim_bytes ash a ad; prim_bytes csh ct cp; ht4_minusp mp gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at tsh (tarray tuchar 16) (map Vubyte (poly1305_tag (aead_otk (aead_st key nonce)) (aead_mac_data a ct))) tag;
         data_at ksh (tarray tuchar 32) (map Vubyte key) kp;
         prim_bytes ash a ad; prim_bytes csh ct cp; ht4_minusp mp gv).

(* ref_chacha20_xor(dst, src, len, key, nonce): the keystream from block 1; dst `prim_out`, src `prim_bytes` *)
Definition ref_chacha20_xor_spec_n :=
  DECLARE HA._ref_chacha20_xor
  WITH dsh: share, dst: val, ssh: share, src: val, m: list byte, ksh: share, kp: val, key: list byte, nonce: Z
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong ]
    PROP (writable_share dsh; readable_share ssh; readable_share ksh; Zlength key = 32;
          0 <= nonce <= Int64.max_unsigned; Zlength m <= Int64.max_signed)
    PARAMS (dst; src; Vlong (Int64.repr (Zlength m)); kp; Vlong (Int64.repr nonce))
    SEP (prim_out dsh (Zrepeat Vundef (Zlength m)) dst; prim_bytes ssh m src;
         data_at ksh (tarray tuchar 32) (map Vubyte key) kp)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (prim_out dsh (map Vubyte (chacha_xor 10 (chacha_advance (aead_st key nonce) 1) m)) dst;
         prim_bytes ssh m src; data_at ksh (tarray tuchar 32) (map Vubyte key) kp).

(* ref_aead_decrypt(dst, src, len, ad, adlen, nonce, key): 1 and the plaintext iff aead_dec succeeds; dst `prim_out`
   (any prior contents `old`, max(len - 16, 0) of them), src and ad `prim_bytes`.  Byte arrays only: stated for ANY
   compspecs cs (the body at W_prim_aead, a law's main imports it at its world; byte arrays do not depend on cs) *)
Section Dec.
Context (cs: compspecs).

Definition ref_aead_decrypt_spec_n (mp: ident) :=
  DECLARE HA._ref_aead_decrypt
  WITH dsh: share, dst: val, old: list val, ssh: share, src: val, c: list byte, ash: share, ad: val,
       a: list byte, nonce: Z, ksh: share, kp: val, key: list byte, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong, tulong, tptr tuchar ]
    PROP (writable_share dsh; readable_share ssh; readable_share ash; readable_share ksh; Zlength key = 32;
          0 <= nonce <= Int64.max_unsigned; Zlength c <= Int64.max_signed; Zlength a <= Int64.max_signed;
          Zlength old = Z.max 0 (Zlength c - 16))
    PARAMS (dst; src; Vlong (Int64.repr (Zlength c)); ad; Vlong (Int64.repr (Zlength a));
            Vlong (Int64.repr nonce); kp) GLOBALS (gv)
    SEP (@prim_out cs dsh old dst; @prim_bytes cs ssh c src; @prim_bytes cs ash a ad;
         @data_at cs ksh (tarray tuchar 32) (map Vubyte key) kp; @ht4_minusp cs mp gv)
  POST [ tint ]
    PROP ()
    RETURN (Vint (match aead_dec key nonce a c with Some _ => Int.one | None => Int.zero end))
    SEP (@prim_out cs dsh (match aead_dec key nonce a c with Some pt => map Vubyte pt | None => old end) dst;
         @prim_bytes cs ssh c src; @prim_bytes cs ash a ad;
         @data_at cs ksh (tarray tuchar 32) (map Vubyte key) kp; @ht4_minusp cs mp gv).

End Dec.

(* the four NULL-tolerant entries; the context of their bodies *)
Definition ht4r_G (mp: ident) : funspecs :=
  [rp_padded_spec_n; ref_aead_tag_spec_n mp; ref_chacha20_xor_spec_n; ref_aead_decrypt_spec_n W_prim_aead mp].

Definition ht4r_Gprog (mp: ident) : funspecs := ht4c_G0 mp ++ ht4r_G mp.

(* the unit of the bodies: prim_aead's Clight of these four functions (byte-identical in every transport harness),
   in W_prim_aead, without varspecs *)
Definition u_ht4r : unit_ctx := mk_unit W_prim_aead [] WgNoise.harness.x_prim_aead.code.prog.
