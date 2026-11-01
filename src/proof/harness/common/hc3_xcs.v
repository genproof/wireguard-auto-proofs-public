(* hc_pieces3: the compspecs-polymorphic imports of the common.h bodies (curve25519_generic,
   chacha20poly1305_encrypt / decrypt, nondet_bytes) are the same specifications at any two compspecs
   (byte arrays only): funspec_sub between the instances. *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.

Section X.
Context {cs1 cs2: compspecs}.

Lemma hc3_prim_bytes_cs: forall sh bs p, @prim_bytes cs1 sh bs p = @prim_bytes cs2 sh bs p.
Proof. intros. unfold prim_bytes. if_tac; auto. apply data_at_tarray_tuchar_cs. Qed.

Lemma hc3_prim_out_cs: forall sh v p, @prim_out cs1 sh v p = @prim_out cs2 sh v p.
Proof. intros. unfold prim_out. if_tac; auto. apply data_at_tarray_tuchar_cs. Qed.

Lemma hc3_zero_page_cs: forall gv, @zero_page cs1 gv = @zero_page cs2 gv.
Proof. intros. unfold zero_page. apply data_at_tarray_tuchar_cs. Qed.

Ltac hc3_cs_rw :=
  repeat first [ rewrite (@data_at_tarray_tuchar_cs cs1 cs2)
               | rewrite (@data_at__tarray_tuchar_cs cs1 cs2)
               | rewrite hc3_prim_bytes_cs | rewrite hc3_prim_out_cs | rewrite hc3_zero_page_cs ].

Lemma hc3_curve25519_generic_xcs: forall x25519,
  funspec_sub (snd (@curve25519_generic_spec_of cs1 x25519)) (snd (@curve25519_generic_spec_of cs2 x25519)).
Proof.
  intros. do_funspec_sub. destruct w as [[[[[[[osh out] ssh] s] sc] psh] p] pt].
  Exists (osh, out, ssh, s, sc, psh, p, pt) emp. hc3_cs_rw. entailer!.
  all: intros; hc3_cs_rw; entailer!.
Qed.

Lemma hc3_chacha_enc_xcs: forall aead_enc,
  funspec_sub (snd (@chacha20poly1305_encrypt_spec_of cs1 aead_enc))
              (snd (@chacha20poly1305_encrypt_spec_of cs2 aead_enc)).
Proof.
  intros. do_funspec_sub. destruct w as [[[[[[[[[[[[dsh dst] ssh] src] m] ash] ad] a] nonce] ksh] key] k] gv].
  Exists (dsh, dst, ssh, src, m, ash, ad, a, nonce, ksh, key, k, gv) emp. hc3_cs_rw. entailer!.
  all: intros; hc3_cs_rw; entailer!.
Qed.

Lemma hc3_chacha_dec3_xcs: forall aead_dec,
  funspec_sub (snd (@chacha20poly1305_decrypt_spec_of3 cs1 aead_dec))
              (snd (@chacha20poly1305_decrypt_spec_of3 cs2 aead_dec)).
Proof.
  intros. do_funspec_sub.
  destruct w as [[[[[[[[[[[[[dsh dst] old] ssh] src] c] ash] ad] a] nonce] ksh] key] k] gv].
  Exists (dsh, dst, old, ssh, src, c, ash, ad, a, nonce, ksh, key, k, gv) emp. hc3_cs_rw. entailer!.
  all: intros; hc3_cs_rw; entailer!.
Qed.

Lemma hc3_nondet_bytes_xcs:
  funspec_sub (snd (@asm_env.nondet_bytes_spec cs1)) (snd (@asm_env.nondet_bytes_spec cs2)).
Proof.
  do_funspec_sub. destruct w as [[buf n] sh].
  Exists (buf, n, sh) emp. hc3_cs_rw. entailer!.
  all: intros; Exists x0; hc3_cs_rw; entailer!.
Qed.

End X.
