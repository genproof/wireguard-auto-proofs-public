(* Law ae_roundtrip: the specifications main is proved against, in the world compspecs W_ae_roundtrip.

   - main: QPmain_spec_ext' of the whole program, postcondition anything (the law is the absence of failing
     checks: gp_assert's precondition).
   - main's context: the externals it calls (QuickProof.Env, asm_env's nondet_bytes), the helpers of wg_laws.h
     (wl_spec.v) and the kernel's chacha20poly1305_encrypt / chacha20poly1305_decrypt, as clones at
     W_ae_roundtrip of aead_spec3.v's chacha20poly1305_encrypt_spec3 / chacha20poly1305_decrypt_spec3 (lengths
     up to 2^64 - 1; the same text, only byte arrays, which are the same in every compspecs: ar_encrypt_sub,
     ar_decrypt_sub). *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.floyd.subsume_funspec.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Chacha20poly1305.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.aead.aead_bytes.
Require Import WgNoise.proof.aead.aead_spec3.
Require Import WgNoise.proof.harness.wg_laws.wl_spec.
Require Import WgNoise.proof.harness.ae_roundtrip.ae_roundtrip_world.
Require WgNoise.contracts.ae_roundtrip.
Require WgNoise.harness.ae_roundtrip.code.

#[local] Existing Instance W_ae_roundtrip.
Local Open Scope Z_scope.

(* the varspecs of the whole program (literal) *)
Definition ar_V : varspecs :=
  ltac:(let x := eval vm_compute in (QPvarspecs WgNoise.contracts.ae_roundtrip.whole_prog) in exact x).

Definition ar_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition ar_main_spec : ident * funspec :=
  (WgNoise.harness.ae_roundtrip.code._main, QPmain_spec_ext' WgNoise.contracts.ae_roundtrip.whole_prog tt ar_post).

Definition ar_encrypt_spec :=
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

Definition ar_decrypt_spec :=
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
    SEP (data_at dsh (tarray tuchar (Zlength old)) old dst; prim_bytes ssh c src; prim_bytes ash a ad;
         data_at ksh (tarray tuchar 32) (map Vubyte k) key; zero_page gv)
  POST [ tbool ]
    PROP ()
    RETURN (Val.of_bool (match aead_dec k nonce a c with Some _ => true | None => false end))
    SEP (data_at dsh (tarray tuchar (Zlength old))
           (match aead_dec k nonce a c with Some pt => map Vubyte pt | None => old end) dst;
         prim_bytes ssh c src; prim_bytes ash a ad;
         data_at ksh (tarray tuchar 32) (map Vubyte k) key; zero_page gv).

(* the externals main calls *)
Definition ar_env : funspecs :=
  [(_quickproof_malloc, malloc_spec'); asm_env.nondet_bytes_spec; gp_assert_spec].

(* main's context *)
Definition ar_Gmain : funspecs :=
  ar_env ++ [ar_encrypt_spec; ar_decrypt_spec; upto_spec; any_u64_spec; any_bytes_spec; bytes_eq_spec].

(* ---------------------------------------------------------------------- *)
(* the kernel's specifications cover the clones                            *)
(* ---------------------------------------------------------------------- *)

Lemma ar_prim_bytes_cs {cs1 cs2: compspecs} sh bs p : @prim_bytes cs1 sh bs p = @prim_bytes cs2 sh bs p.
Proof. unfold prim_bytes. destruct (Z.eq_dec _ 0); auto. apply aead_data_at_tuchar_cs. Qed.

Lemma ar_zero_page_cs {cs1 cs2: compspecs} gv : @zero_page cs1 gv = @zero_page cs2 gv.
Proof. unfold zero_page. apply aead_data_at_tuchar_cs. Qed.

Ltac ar_conv :=
  repeat first
    [ rewrite (@aead_data_at_tuchar_cs Chacha20poly1305.CS W_ae_roundtrip)
    | rewrite (@aead_data_at__tuchar_cs Chacha20poly1305.CS W_ae_roundtrip)
    | rewrite (@ar_prim_bytes_cs Chacha20poly1305.CS W_ae_roundtrip)
    | rewrite (@ar_zero_page_cs Chacha20poly1305.CS W_ae_roundtrip) ].

Ltac ar_sub :=
  apply NDsubsume_subsume; [split; reflexivity |];
  split; [split; reflexivity |];
  let x := fresh "x" in let g := fresh "gargs" in
  intros x g; Exists x (@emp mpred _ _); repeat (destruct x as [x ?]); simpl;
  rewrite emp_sepcon; ar_conv;
  apply andp_right; [apply andp_left2; auto |];
  apply prop_right; let r := fresh "rho" in intros r; rewrite emp_sepcon; apply andp_left2; ar_conv;
  first [apply derives_refl | auto].

Lemma ar_encrypt_sub : funspec_sub (snd chacha20poly1305_encrypt_spec3) (snd ar_encrypt_spec).
Proof. ar_sub. Qed.

Lemma ar_decrypt_sub : funspec_sub (snd chacha20poly1305_decrypt_spec3) (snd ar_decrypt_spec).
Proof. ar_sub. Qed.
