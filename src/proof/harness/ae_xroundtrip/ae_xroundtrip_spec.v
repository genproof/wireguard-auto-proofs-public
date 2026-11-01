(* The harness piece of law ae_xroundtrip (harness/ae_xroundtrip.c): the unit, main's specification and the
   body-proof context of main.

   - Everything is in the world compspecs W_ae_xroundtrip (ae_xroundtrip_world.v).  The varspecs of the unit are
     those of the whole program: main's precondition describes every global, among them the shim's
     quickproof_zero_page, which the AEAD reads (zero_page gv).
   - The helpers of wg_laws.h (upto, any_bytes, bytes_eq) have the shared specifications of wl_spec.v.
   - The two AEAD functions are imported as clones at the world of aead_spec3.v's
     xchacha20poly1305_encrypt_spec3 and aead_spec3b.v's xchacha20poly1305_decrypt_spec3b (same text; they
     mention byte arrays only, which are the same in every compspecs: the assembly relates them by funspec_sub,
     axr_xencrypt_sub and axr_xdecrypt_sub below). *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.floyd.subsume_funspec.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.aead.aead_bytes.
Require Import WgNoise.proof.aead.aead_spec3b.
Require Import WgNoise.proof.harness.wg_laws.wl_spec.
Require Import WgNoise.proof.harness.ae_xroundtrip.ae_xroundtrip_world.
Require WgNoise.contracts.ae_xroundtrip.
Require WgNoise.harness.ae_xroundtrip.code.

#[local] Existing Instance W_ae_xroundtrip.
Local Open Scope Z_scope.

Definition _axr_main : ident := WgNoise.harness.ae_xroundtrip.code._main.

(* the varspecs of the whole program (literal) *)
Definition axr_V : varspecs :=
  ltac:(let x := eval vm_compute in (QPvarspecs WgNoise.contracts.ae_xroundtrip.whole_prog) in exact x).

(* the harness unit, in the world compspecs, with the whole program's varspecs *)
Definition u_axr : unit_ctx := mk_unit W_ae_xroundtrip axr_V WgNoise.harness.ae_xroundtrip.code.prog.

(* main: the precondition is fixed (main_pre of the whole program), the postcondition anything *)
Definition axr_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition axr_main_spec : ident * funspec :=
  (_axr_main, QPmain_spec_ext' WgNoise.contracts.ae_xroundtrip.whole_prog tt axr_post).

(* xchacha20poly1305_encrypt: aead_spec3.xchacha20poly1305_encrypt_spec3 at the world *)
Definition axr_xencrypt_spec :=
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
Definition axr_xdecrypt_spec :=
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

(* imports of the harness piece: the externals the program calls and the two AEAD functions *)
Definition axr_imports (cs: compspecs) : funspecs :=
  [(_quickproof_malloc, @malloc_spec' W_ae_xroundtrip); @asm_env.nondet_bytes_spec W_ae_xroundtrip;
   nondet_size_spec; gp_assert_spec; axr_xencrypt_spec; axr_xdecrypt_spec].

(* the harness's functions *)
Definition axr_G : funspecs := [upto_spec; any_bytes_spec; bytes_eq_spec; axr_main_spec].

(* the context of main's body proof *)
Definition axr_Gprog : funspecs := axr_imports W_ae_xroundtrip ++ axr_G.

(* ---------------------------------------------------------------------- *)
(* The clones are covered by the AEAD piece's entries                      *)
(* ---------------------------------------------------------------------- *)

Lemma axr_prim_bytes {cs1 cs2: compspecs} sh bs p : @prim_bytes cs1 sh bs p = @prim_bytes cs2 sh bs p.
Proof. unfold prim_bytes. destruct (Z.eq_dec _ 0); auto. apply aead_data_at_tuchar_cs. Qed.

Lemma axr_prim_out {cs1 cs2: compspecs} sh v p : @prim_out cs1 sh v p = @prim_out cs2 sh v p.
Proof. unfold prim_out. destruct (Z.eq_dec _ 0); auto. apply aead_data_at_tuchar_cs. Qed.

Lemma axr_zero_page {cs1 cs2: compspecs} gv : @zero_page cs1 gv = @zero_page cs2 gv.
Proof. unfold zero_page. apply aead_data_at_tuchar_cs. Qed.

Ltac axr_conv :=
  repeat first
    [ rewrite (@aead_data_at_tuchar_cs Chacha20poly1305.CS W_ae_xroundtrip)
    | rewrite (@aead_data_at__tuchar_cs Chacha20poly1305.CS W_ae_xroundtrip)
    | rewrite (@axr_prim_bytes Chacha20poly1305.CS W_ae_xroundtrip)
    | rewrite (@axr_prim_out Chacha20poly1305.CS W_ae_xroundtrip)
    | rewrite (@axr_zero_page Chacha20poly1305.CS W_ae_xroundtrip) ].

Ltac axr_sub :=
  apply NDsubsume_subsume; [split; reflexivity |];
  split; [split; reflexivity |];
  let x := fresh "x" in let g := fresh "gargs" in
  intros x g; Exists x (@emp mpred _ _); repeat (destruct x as [x ?]); simpl;
  rewrite emp_sepcon; axr_conv;
  apply andp_right; [apply andp_left2; auto |];
  apply prop_right; let r := fresh "rho" in intros r; rewrite emp_sepcon; apply andp_left2; axr_conv;
  first [apply derives_refl | auto].

Lemma axr_xencrypt_sub : funspec_sub (snd xchacha20poly1305_encrypt_spec3) (snd axr_xencrypt_spec).
Proof. axr_sub. Qed.

Lemma axr_xdecrypt_sub : funspec_sub (snd xchacha20poly1305_decrypt_spec3b) (snd axr_xdecrypt_spec).
Proof. axr_sub. Qed.
