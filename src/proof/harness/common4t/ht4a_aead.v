(* the kernel AEAD entry points
   chacha20poly1305_encrypt / chacha20poly1305_decrypt as the transport harnesses call them, for ANY length up to
   2^64 - 1 (the harnesses' packets go up to PTRDIFF_MAX), at ANY compspecs (a law's main imports them at its
   world W_transport_<x>).

   They are text copies of the CONCRETE AEAD piece's entries (aead_piece3b.aead_piece3b: aead_spec3's
   chacha20poly1305_encrypt_spec3 and aead_spec3b's NULL-tolerant chacha20poly1305_decrypt_spec3b, at
   Chacha20poly1305.CS, with aead_model's aead_enc / aead_dec, the model the reference ref_aead_decrypt computes).
   The theorem's hypothesis aead3b_ok cannot serve here: its templates bound lengths by 2^32 - 1 and its
   decryption is an abstract function, which the harness compares with the reference.
   Only byte arrays are involved (prim_bytes, prim_out, zero_page: cs-generic), so the piece's entries cover
   these copies (ht4_encrypt_sub, ht4_decrypt_sub) by aead_bytes.aead_data_at_tuchar_cs. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.subsume_funspec.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.aead.aead_bytes.
Require Import WgNoise.proof.aead.aead_spec3b.

Local Open Scope Z_scope.

Section HT4A.
Context {cs: compspecs}.

Definition ht4_encrypt_spec :=
  DECLARE _chacha20poly1305_encrypt
  WITH dsh: share, dst: val, ssh: share, src: val, m: list byte, ash: share, ad: val, a: list byte,
       nonce: Z, ksh: share, key: val, k: list byte, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong, tulong, tptr tuchar ]
    PROP (writable_share dsh; readable_share ssh; readable_share ash; readable_share ksh;
          Zlength m + 16 <= Int64.max_unsigned; Zlength a <= Int64.max_unsigned;
          0 <= nonce <= Int64.max_unsigned; Zlength k = 32)
    PARAMS (dst; src; Vlong (Int64.repr (Zlength m)); ad; Vlong (Int64.repr (Zlength a));
            Vlong (Int64.repr nonce); key) GLOBALS (gv)
    SEP (data_at_ dsh (tarray tuchar (Zlength m + 16)) dst; prim_bytes ssh m src; prim_bytes ash a ad;
         data_at ksh (tarray tuchar 32) (map Vubyte k) key; zero_page gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at dsh (tarray tuchar (Zlength m + 16)) (map Vubyte (aead_enc k nonce a m)) dst;
         prim_bytes ssh m src; prim_bytes ash a ad;
         data_at ksh (tarray tuchar 32) (map Vubyte k) key; zero_page gv).

Definition ht4_decrypt_spec :=
  DECLARE _chacha20poly1305_decrypt
  WITH dsh: share, dst: val, old: list val, ssh: share, src: val, c: list byte, ash: share, ad: val,
       a: list byte, nonce: Z, ksh: share, key: val, k: list byte, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong, tulong, tptr tuchar ]
    PROP (writable_share dsh; readable_share ssh; readable_share ash; readable_share ksh;
          Zlength c <= Int64.max_unsigned; Zlength a <= Int64.max_unsigned;
          0 <= nonce <= Int64.max_unsigned;
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

End HT4A.

(* ---------------------------------------------------------------------- *)
(* The piece's entries (Chacha20poly1305.CS) cover the copies at any cs    *)
(* ---------------------------------------------------------------------- *)

Lemma ht4a_prim_bytes {cs1 cs2: compspecs} sh bs p : @prim_bytes cs1 sh bs p = @prim_bytes cs2 sh bs p.
Proof. unfold prim_bytes. destruct (Z.eq_dec _ 0); auto. apply aead_data_at_tuchar_cs. Qed.

Lemma ht4a_prim_out {cs1 cs2: compspecs} sh v p : @prim_out cs1 sh v p = @prim_out cs2 sh v p.
Proof. unfold prim_out. destruct (Z.eq_dec _ 0); auto. apply aead_data_at_tuchar_cs. Qed.

Lemma ht4a_zero_page {cs1 cs2: compspecs} gv : @zero_page cs1 gv = @zero_page cs2 gv.
Proof. unfold zero_page. apply aead_data_at_tuchar_cs. Qed.

Ltac ht4a_conv cs :=
  repeat first
    [ rewrite (@aead_data_at_tuchar_cs Chacha20poly1305.CS cs)
    | rewrite (@aead_data_at__tuchar_cs Chacha20poly1305.CS cs)
    | rewrite (@ht4a_prim_bytes Chacha20poly1305.CS cs)
    | rewrite (@ht4a_prim_out Chacha20poly1305.CS cs)
    | rewrite (@ht4a_zero_page Chacha20poly1305.CS cs) ].

Ltac ht4a_sub cs :=
  apply NDsubsume_subsume; [split; reflexivity |];
  split; [split; reflexivity |];
  let x := fresh "x" in let g := fresh "gargs" in
  intros x g; Exists x (@emp mpred _ _); repeat (destruct x as [x ?]); simpl;
  rewrite emp_sepcon; ht4a_conv cs;
  apply andp_right; [apply andp_left2; auto |];
  apply prop_right; let r := fresh "rho" in intros r; rewrite emp_sepcon; apply andp_left2; ht4a_conv cs;
  first [apply derives_refl | auto].

Lemma ht4_encrypt_sub (cs: compspecs) :
  funspec_sub (snd chacha20poly1305_encrypt_spec3) (snd (@ht4_encrypt_spec cs)).
Proof. ht4a_sub cs. Qed.

Lemma ht4_decrypt_sub (cs: compspecs) :
  funspec_sub (snd chacha20poly1305_decrypt_spec3b) (snd (@ht4_decrypt_spec cs)).
Proof. ht4a_sub cs. Qed.
