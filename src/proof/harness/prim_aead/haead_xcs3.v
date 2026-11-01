(* law prim_aead: the four kernel AEAD entry points of aead_G3 (at Chacha20poly1305.CS) cover the
   harness's imported clones at W_prim_aead (haead_spec3.v): the specifications only mention byte arrays,
   which are the same in every compspecs (aead_bytes.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.subsume_funspec.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.aead.aead_bytes.
Require Import WgNoise.proof.aead.aead_spec3.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.harness.prim_aead.haead_spec3.

Lemma hx3_prim_bytes {cs1 cs2: compspecs} sh bs p : @prim_bytes cs1 sh bs p = @prim_bytes cs2 sh bs p.
Proof. unfold prim_bytes. destruct (Z.eq_dec _ 0); auto. apply aead_data_at_tuchar_cs. Qed.

Lemma hx3_zero_page {cs1 cs2: compspecs} gv : @zero_page cs1 gv = @zero_page cs2 gv.
Proof. unfold zero_page. apply aead_data_at_tuchar_cs. Qed.

Ltac hx3_conv :=
  repeat first
    [ rewrite (@aead_data_at_tuchar_cs Chacha20poly1305.CS W_prim_aead)
    | rewrite (@aead_data_at__tuchar_cs Chacha20poly1305.CS W_prim_aead)
    | rewrite (@hx3_prim_bytes Chacha20poly1305.CS W_prim_aead)
    | rewrite (@hx3_zero_page Chacha20poly1305.CS W_prim_aead) ].

Lemma hx3_encrypt_sub : funspec_sub (snd chacha20poly1305_encrypt_spec3) (snd haead_encrypt_spec).
Proof.
  apply NDsubsume_subsume; [split; reflexivity |].
  split; [split; reflexivity |].
  intros x gargs. destruct x as [[[[[[[[[[[[dsh dst] ssh] src] m] ash] ad] a] nonce] ksh] key] k] gv]. simpl.
  Exists (dsh, dst, ssh, src, m, ash, ad, a, nonce, ksh, key, k, gv) (@emp mpred _ _).
  rewrite emp_sepcon. hx3_conv.
  apply andp_right; [apply andp_left2; auto |].
  apply prop_right. intros rho'. rewrite emp_sepcon. apply andp_left2. hx3_conv. auto.
Qed.

Ltac hx3_sub :=
  apply NDsubsume_subsume; [split; reflexivity |];
  split; [split; reflexivity |];
  let x := fresh "x" in let g := fresh "gargs" in
  intros x g; Exists x (@emp mpred _ _); repeat (destruct x as [x ?]); simpl;
  rewrite emp_sepcon; hx3_conv;
  apply andp_right; [apply andp_left2; auto |];
  apply prop_right; let r := fresh "rho" in intros r; rewrite emp_sepcon; apply andp_left2; hx3_conv; first [apply derives_refl | auto].

Lemma hx3_decrypt_sub : funspec_sub (snd chacha20poly1305_decrypt_spec3) (snd haead_decrypt_spec).
Proof. hx3_sub. Qed.

Lemma hx3_xencrypt_sub : funspec_sub (snd xchacha20poly1305_encrypt_spec3) (snd haead_xencrypt_spec).
Proof. hx3_sub. Qed.

Lemma hx3_xdecrypt_sub : funspec_sub (snd xchacha20poly1305_decrypt_spec3) (snd haead_xdecrypt_spec).
Proof. hx3_sub. Qed.
