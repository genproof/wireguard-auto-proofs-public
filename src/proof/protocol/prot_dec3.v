(* the AEAD decryption templates as the protocol calls them.

   prim_api.v's chacha20poly1305_decrypt_spec_of requires `data_at dsh (tarray tuchar (Zlength old)) old dst`,
   which implies isptr dst even when the plaintext is empty; noise.c's consume_response calls
   message_decrypt(NULL, encrypted_nothing, 16, ...) -> chacha20poly1305_decrypt(NULL, src, 16, ...).
   These templates are the same except that an empty destination is `emp` (any pointer, NULL included),
   as prim_bytes does for the inputs. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import WgNoise.proof.prims.prim_api.

Local Open Scope Z_scope.

Section Specs.
Context {cs: compspecs}.

(* an output buffer holding v: nothing when empty (the pointer may then be anything, NULL included) *)
Definition prim_out (sh: share) (v: list val) (p: val) : mpred :=
  if Z.eq_dec (Zlength v) 0 then emp else data_at sh (tarray tuchar (Zlength v)) v p.

Section AEAD.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Definition chacha20poly1305_decrypt_spec_of3 :=
  DECLARE _chacha20poly1305_decrypt
  WITH dsh: share, dst: val, old: list val, ssh: share, src: val, c: list byte, ash: share, ad: val,
       a: list byte, nonce: Z, ksh: share, key: val, k: list byte, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong, tulong, tptr tuchar ]
    PROP (writable_share dsh; readable_share ssh; readable_share ash; readable_share ksh;
          Zlength c <= Int.max_unsigned; Zlength a <= Int.max_unsigned; 0 <= nonce <= Int64.max_unsigned;
          Zlength k = 32; Zlength old = Z.max 0 (Zlength c - 16))
    PARAMS (dst; src; Vlong (Int64.repr (Zlength c)); ad; Vlong (Int64.repr (Zlength a));
            Vlong (Int64.repr nonce); key) GLOBALS (gv)
    SEP (prim_out dsh old dst; prim_bytes ssh c src; prim_bytes ash a ad;
         data_at ksh (tarray tuchar 32) (map Vubyte k) key; zero_page gv)
  POST [ tbool ]
    PROP ()
    RETURN (Val.of_bool (match aead_dec k nonce a c with Some _ => true | None => false end))
    SEP (prim_out dsh (match aead_dec k nonce a c with Some pt => map Vubyte pt | None => old end) dst;
         prim_bytes ssh c src; prim_bytes ash a ad;
         data_at ksh (tarray tuchar 32) (map Vubyte k) key; zero_page gv).

Definition xchacha20poly1305_decrypt_spec_of3 :=
  DECLARE _xchacha20poly1305_decrypt
  WITH dsh: share, dst: val, old: list val, ssh: share, src: val, c: list byte, ash: share, ad: val,
       a: list byte, nsh: share, np: val, nonce: list byte, ksh: share, key: val, k: list byte, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong, tptr tuchar, tptr tuchar ]
    PROP (writable_share dsh; readable_share ssh; readable_share ash; readable_share nsh; readable_share ksh;
          Zlength c <= Int.max_unsigned; Zlength a <= Int.max_unsigned; Zlength nonce = 24;
          Zlength k = 32; Zlength old = Z.max 0 (Zlength c - 16))
    PARAMS (dst; src; Vlong (Int64.repr (Zlength c)); ad; Vlong (Int64.repr (Zlength a)); np; key)
    GLOBALS (gv)
    SEP (prim_out dsh old dst; prim_bytes ssh c src; prim_bytes ash a ad;
         data_at nsh (tarray tuchar 24) (map Vubyte nonce) np;
         data_at ksh (tarray tuchar 32) (map Vubyte k) key; zero_page gv)
  POST [ tbool ]
    PROP ()
    RETURN (Val.of_bool (match xaead_dec k nonce a c with Some _ => true | None => false end))
    SEP (prim_out dsh (match xaead_dec k nonce a c with Some pt => map Vubyte pt | None => old end) dst;
         prim_bytes ssh c src; prim_bytes ash a ad;
         data_at nsh (tarray tuchar 24) (map Vubyte nonce) np;
         data_at ksh (tarray tuchar 32) (map Vubyte k) key; zero_page gv).

End AEAD.
End Specs.
