(* body proofs of chacha20poly1305_decrypt and xchacha20poly1305_decrypt with a
   NULL-tolerant destination (aead_spec3b: dst is prot_dec3.prim_out, passed through to
   __chacha20poly1305_decrypt_spec3b), against aead_spec3b.aead_G3b.  Adapted from aead_entry_body3.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.chacha.code WgNoise.chacha_block.code WgNoise.poly1305.code WgNoise.poly1305_donna32.code
        WgNoise.chacha20poly1305.code WgNoise.shim.code.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.common.wg3_iface.
Require Import WgNoise.proof.aead.aead_spec3b.
Require Import WgNoise.proof.aead.aead_cce.
Require Import WgNoise.proof.aead.aead_bytes.
Require Import WgNoise.proof.aead.aead_entry_body3.

Local Open Scope Z_scope.

Section EntryBodies3b.
#[local] Existing Instance Chacha20poly1305.CS.

Lemma body_chacha20poly1305_decrypt3b :
  @semax_body (QPvarspecs Chacha20poly1305.qp) (aead_imports3 Chacha20poly1305.CS ++ aead_G3b) Chacha20poly1305.CS
    WgNoise.chacha20poly1305.code.f_chacha20poly1305_decrypt chacha20poly1305_decrypt_spec3b.
Proof.
  start_function.
  assert_PROP (field_compatible (tarray tuint 8) [] v_k) by entailer!.
  forward_call (Tsh, v_k, ksh, key, k).
  forward_call (0, Tsh, v_iv, 0, Zrepeat Vundef 16). { list_solve. }
  fold ae3_iv1. change (Zlength (Zrepeat Vundef 16)) with 16.
  forward_call (nonce, Tsh, v_iv, 8, ae3_iv1). { rewrite ae3_Zlength_iv1. lia. }
  rewrite ae3_iv2, ae3_Zlength_iv1.
  assert (Hzi: Zlength (aead_iv nonce) = 16) by reflexivity.
  assert (Hk: Zlength (le32_words 8 k) = 8) by apply ae3_Zlength_le32_words.
  remember (le32_words 8 k) as kw eqn:Hkw.
  forward_call (Tsh, v_chacha_state__1, Tsh, v_k, kw, Tsh, v_iv, aead_iv nonce).
  rewrite Hzi.
  assert (Hs: Zlength (chacha_init_st kw (aead_iv nonce)) = 16) by (apply ae3_Zlength_init_st; auto).
  remember (chacha_init_st kw (aead_iv nonce)) as st eqn:Hst.
  forward_call (dsh, dst, old, ssh, src, c, ash, ad, a, Tsh, v_chacha_state__1, st, gv).
  remember (aead_dec_st st a c) as r eqn:Hr.
  forward_call (Tsh, v_chacha_state__1).
  forward_call (Tsh, v_iv, 16).
  sep_apply (data_at_data_at_ Tsh (tarray tuint 8) (map Vint kw) v_k).
  sep_apply (ae3_words_to_bytes Tsh v_k).
  forward_call (Tsh, v_k, 32).
  sep_apply (ae3_bytes_to_words Tsh v_k); auto.
  assert (Hx: r = aead_dec k nonce a c) by (rewrite Hr, Hst, Hkw; reflexivity).
  forward.
  rewrite <- Hx. clear Hx.
  entailer!.
  destruct (aead_dec_st _ a c); reflexivity.
Qed.

Lemma body_xchacha20poly1305_decrypt3b :
  @semax_body (QPvarspecs Chacha20poly1305.qp) (aead_imports3 Chacha20poly1305.CS ++ aead_G3b) Chacha20poly1305.CS
    WgNoise.chacha20poly1305.code.f_xchacha20poly1305_decrypt xchacha20poly1305_decrypt_spec3b.
Proof.
  start_function.
  forward_call (Tsh, v_chacha_state__1, ksh, key, k, nsh, np, nonce).
  pose proof (ae3_Zlength_xaead_st k nonce) as Hs.
  remember (xaead_st k nonce) as st eqn:Hst.
  forward_call (dsh, dst, old, ssh, src, c, ash, ad, a, Tsh, v_chacha_state__1, st, gv).
  remember (aead_dec_st st a c) as r eqn:Hr.
  assert (Hx: r = xaead_dec k nonce a c) by (rewrite Hr, Hst; reflexivity).
  clear Hr Hst. subst r.
  forward.
  destruct (xaead_dec k nonce a c); entailer!.
Qed.

End EntryBodies3b.

Theorem aead_entry_bodies3b :
  @semax_body (QPvarspecs Chacha20poly1305.qp) (aead_imports3 Chacha20poly1305.CS ++ aead_G3b) Chacha20poly1305.CS
    WgNoise.chacha20poly1305.code.f_chacha20poly1305_decrypt chacha20poly1305_decrypt_spec3b /\
  @semax_body (QPvarspecs Chacha20poly1305.qp) (aead_imports3 Chacha20poly1305.CS ++ aead_G3b) Chacha20poly1305.CS
    WgNoise.chacha20poly1305.code.f_xchacha20poly1305_decrypt xchacha20poly1305_decrypt_spec3b.
Proof. exact (conj body_chacha20poly1305_decrypt3b body_xchacha20poly1305_decrypt3b). Qed.
