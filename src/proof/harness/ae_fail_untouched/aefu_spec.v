(* Law ae_fail_untouched: the specifications main is proved against, in the world compspecs W_ae_fail_untouched.

   - main: QPmain_spec_ext' of the whole program, postcondition anything (the law is the absence of failing
     checks: gp_assert's precondition).
   - main's context: the externals it calls (QuickProof.Env, asm_env's nondet_bytes), the helpers of wg_laws.h
     (wl_spec.v, wl_copy_of.v) and the kernel's four AEAD functions, as clones at the world of aead_spec3.v's
     chacha20poly1305_encrypt_spec3 / xchacha20poly1305_encrypt_spec3 and of aead_spec3b.v's NULL-tolerant
     chacha20poly1305_decrypt_spec3b / xchacha20poly1305_decrypt_spec3b (the same text; they mention byte arrays
     only, which are the same in every compspecs: the assembly relates them by funspec_sub, aefu_*_sub below).
     The decryptions return whether the model's decryption succeeds and, when it fails, leave their output as it
     was: this is the law. *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.floyd.subsume_funspec.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Chacha20poly1305.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.aead.aead_bytes.
Require Import WgNoise.proof.aead.aead_spec3b.
Require Import WgNoise.proof.harness.wg_laws.wl_spec.
Require Import WgNoise.proof.harness.wg_laws.wl_copy_of.
Require Import WgNoise.proof.harness.ae_fail_untouched.aefu_world.
Require WgNoise.contracts.ae_fail_untouched.
Require WgNoise.harness.ae_fail_untouched.code.

#[local] Existing Instance W_ae_fail_untouched.
Local Open Scope Z_scope.

(* the varspecs of the whole program (literal) *)
Definition aefu_V : varspecs :=
  ltac:(let x := eval vm_compute in (QPvarspecs WgNoise.contracts.ae_fail_untouched.whole_prog) in exact x).

Definition aefu_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition aefu_main_spec : ident * funspec :=
  (WgNoise.harness.ae_fail_untouched.code._main,
   QPmain_spec_ext' WgNoise.contracts.ae_fail_untouched.whole_prog tt aefu_post).

(* chacha20poly1305_encrypt: aead_spec3.chacha20poly1305_encrypt_spec3 at the world *)
Definition aefu_encrypt_spec :=
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

(* chacha20poly1305_decrypt: aead_spec3b.chacha20poly1305_decrypt_spec3b at the world *)
Definition aefu_decrypt_spec :=
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

(* xchacha20poly1305_encrypt: aead_spec3.xchacha20poly1305_encrypt_spec3 at the world *)
Definition aefu_xencrypt_spec :=
  DECLARE _xchacha20poly1305_encrypt
  WITH dsh: share, dst: val, ssh: share, src: val, m: list byte, ash: share, ad: val, a: list byte,
       nsh: share, np: val, nonce: list byte, ksh: share, key: val, k: list byte, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong, tptr tuchar, tptr tuchar ]
    PROP (writable_share dsh; readable_share ssh; readable_share ash; readable_share nsh; readable_share ksh;
          Zlength m + 16 <= Int64.max_unsigned; Zlength a <= Int64.max_unsigned; Zlength nonce = 24;
          Zlength k = 32)
    PARAMS (dst; src; Vlong (Int64.repr (Zlength m)); ad; Vlong (Int64.repr (Zlength a)); np; key)
    GLOBALS (gv)
    SEP (data_at_ dsh (tarray tuchar (Zlength m + 16)) dst; prim_bytes ssh m src; prim_bytes ash a ad;
         data_at nsh (tarray tuchar 24) (map Vubyte nonce) np;
         data_at ksh (tarray tuchar 32) (map Vubyte k) key; zero_page gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at dsh (tarray tuchar (Zlength m + 16)) (map Vubyte (xaead_enc k nonce a m)) dst;
         prim_bytes ssh m src; prim_bytes ash a ad;
         data_at nsh (tarray tuchar 24) (map Vubyte nonce) np;
         data_at ksh (tarray tuchar 32) (map Vubyte k) key; zero_page gv).

(* xchacha20poly1305_decrypt: aead_spec3b.xchacha20poly1305_decrypt_spec3b at the world *)
Definition aefu_xdecrypt_spec :=
  DECLARE _xchacha20poly1305_decrypt
  WITH dsh: share, dst: val, old: list val, ssh: share, src: val, c: list byte, ash: share, ad: val,
       a: list byte, nsh: share, np: val, nonce: list byte, ksh: share, key: val, k: list byte, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong, tptr tuchar, tptr tuchar ]
    PROP (writable_share dsh; readable_share ssh; readable_share ash; readable_share nsh; readable_share ksh;
          Zlength c <= Int64.max_unsigned; Zlength a <= Int64.max_unsigned; Zlength nonce = 24;
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

(* the externals main calls *)
Definition aefu_env : funspecs :=
  [(_quickproof_malloc, malloc_spec'); asm_env.nondet_bytes_spec; nondet_u8_spec; gp_assert_spec].

(* main's context *)
Definition aefu_Gmain : funspecs :=
  aefu_env ++ [aefu_encrypt_spec; aefu_decrypt_spec; aefu_xencrypt_spec; aefu_xdecrypt_spec;
               upto_spec; any_u64_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec].

(* ---------------------------------------------------------------------- *)
(* the kernel's specifications cover the clones                            *)
(* ---------------------------------------------------------------------- *)

Lemma aefu_prim_bytes_cs {cs1 cs2: compspecs} sh bs p : @prim_bytes cs1 sh bs p = @prim_bytes cs2 sh bs p.
Proof. unfold prim_bytes. destruct (Z.eq_dec _ 0); auto. apply aead_data_at_tuchar_cs. Qed.

Lemma aefu_prim_out_cs {cs1 cs2: compspecs} sh v p : @prim_out cs1 sh v p = @prim_out cs2 sh v p.
Proof. unfold prim_out. destruct (Z.eq_dec _ 0); auto. apply aead_data_at_tuchar_cs. Qed.

Lemma aefu_zero_page_cs {cs1 cs2: compspecs} gv : @zero_page cs1 gv = @zero_page cs2 gv.
Proof. unfold zero_page. apply aead_data_at_tuchar_cs. Qed.

Ltac aefu_conv :=
  repeat first
    [ rewrite (@aead_data_at_tuchar_cs Chacha20poly1305.CS W_ae_fail_untouched)
    | rewrite (@aead_data_at__tuchar_cs Chacha20poly1305.CS W_ae_fail_untouched)
    | rewrite (@aefu_prim_bytes_cs Chacha20poly1305.CS W_ae_fail_untouched)
    | rewrite (@aefu_prim_out_cs Chacha20poly1305.CS W_ae_fail_untouched)
    | rewrite (@aefu_zero_page_cs Chacha20poly1305.CS W_ae_fail_untouched) ].

Ltac aefu_sub :=
  apply NDsubsume_subsume; [split; reflexivity |];
  split; [split; reflexivity |];
  let x := fresh "x" in let g := fresh "gargs" in
  intros x g; Exists x (@emp mpred _ _); repeat (destruct x as [x ?]); simpl;
  rewrite emp_sepcon; aefu_conv;
  apply andp_right; [apply andp_left2; auto |];
  apply prop_right; let r := fresh "rho" in intros r; rewrite emp_sepcon; apply andp_left2; aefu_conv;
  first [apply derives_refl | auto].

Lemma aefu_encrypt_sub : funspec_sub (snd chacha20poly1305_encrypt_spec3) (snd aefu_encrypt_spec).
Proof. aefu_sub. Qed.

Lemma aefu_decrypt_sub : funspec_sub (snd chacha20poly1305_decrypt_spec3b) (snd aefu_decrypt_spec).
Proof. aefu_sub. Qed.

Lemma aefu_xencrypt_sub : funspec_sub (snd xchacha20poly1305_encrypt_spec3) (snd aefu_xencrypt_spec).
Proof. aefu_sub. Qed.

Lemma aefu_xdecrypt_sub : funspec_sub (snd xchacha20poly1305_decrypt_spec3b) (snd aefu_xdecrypt_spec).
Proof. aefu_sub. Qed.
