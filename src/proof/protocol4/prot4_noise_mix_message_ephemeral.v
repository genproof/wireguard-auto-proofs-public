(* group noise_mix: the body of noise.c's message_ephemeral against its specification
   (prot_specs4.v) in the context Gprot4 (prot_prog4.v), for ANY primitive models with their properties. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require WgNoise.proof.libc.libc_bytes WgNoise.proof.blake2s.spec.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

Lemma prot4_noise_mix_message_ephemeral_b2s sh bs p : Zlength bs <> 0 ->
  bytes_at sh bs p = WgNoise.proof.blake2s.spec.b2s_bytes sh bs p.
Proof.
  intros. unfold bytes_at, bytes. rewrite WgNoise.proof.blake2s.spec.b2s_bytes_nonempty by auto.
  apply WgNoise.proof.libc.libc_bytes.data_at_tarray_tuchar_cs.
Qed.

Lemma prot4_noise_mix_message_ephemeral_bytes32 sh bs p : Zlength bs = 32 ->
  bytes_at sh bs p = @data_at Noise.CS sh (tarray tuchar 32) (map Vubyte bs) p.
Proof.
  intros. unfold bytes_at, bytes. rewrite H. reflexivity.
Qed.

Lemma prot4_noise_mix_message_ephemeral_glb shd shs :
  writable_share shd -> readable_share shs -> sepalg.nonidentity (Share.glb shd shs).
Proof.
  intros [_ HW] HR N.
  apply HR.
  apply leq_join_sub, Share.ord_spec1 in HW.
  apply identity_share_bot in N.
  rewrite HW, Share.glb_assoc, N, Share.glb_bot.
  apply bot_identity.
Qed.

Lemma prot4_noise_mix_message_ephemeral_conflict shd shs bs p :
  writable_share shd -> readable_share shs ->
  @data_at_ Noise.CS shd (tarray tuchar 32) p * @data_at Noise.CS shs (tarray tuchar 32) (map Vubyte bs) p |-- FF.
Proof.
  intros. unfold data_at_. apply data_at_conflict_glb.
  - apply prot4_noise_mix_message_ephemeral_glb; auto.
  - simpl. lia.
Qed.

Section Body.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.

Lemma prot4_noise_mix_body_message_ephemeral :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_message_ephemeral message_ephemeral_spec.
Proof.
intros _ _ _.
start_function.
unfold wg_consts; Intros.
destruct alias.
- specialize (H2 eq_refl); subst dp.
  rewrite (prot4_noise_mix_message_ephemeral_bytes32 shs e sp H).
  forward_if (PROP () LOCAL (gvars gv; temp WgNoise.noise.code._ephemeral_dst sp;
      temp WgNoise.noise.code._ephemeral_src sp; temp WgNoise.noise.code._chaining_key ckp;
      temp WgNoise.noise.code._hash hp)
    SEP (data_at shs (tarray tuchar 32) (map Vubyte e) sp; bytes_at shc ck ckp; bytes_at shh h hp;
      WgNoise.proof.blake2s.spec.blake2s_globals gv; curve25519_globals gv; zero_page gv; cookie_globals gv)).
  { exfalso; apply H2; reflexivity. }
  { forward. entailer!. }
  rewrite <- (prot4_noise_mix_message_ephemeral_bytes32 shs e sp H).
  rewrite (prot4_noise_mix_message_ephemeral_b2s shs e sp) by lia.
  forward_call (gv, shh, hp, h, shs, sp, e).
  { apply prop_right; simpl; rewrite H; reflexivity. }
  { unfold wg_consts. cancel. }
  remember (mix_hash h e) as MH eqn:EMH.
  forward_call (gv, true, ckp, nullval, nullval, 0, 0, Tsh, Tsh, Tsh, shs, sp, e, shc, ckp, ck).
  { apply prop_right; simpl; rewrite H; reflexivity. }
  { destruct (eq_dec nullval nullval) as [_|NN]; [|congruence]. cancel. }
  destruct (eq_dec nullval nullval) as [_|NN]; [|congruence].
  rewrite <- (prot4_noise_mix_message_ephemeral_b2s shs e sp) by lia.
  remember (kdf1 ck e) as K eqn:EK. clear EK EMH.
  entailer!.
- Intros.
  rewrite (prot4_noise_mix_message_ephemeral_bytes32 shs e sp H).
  assert_PROP (dp <> sp).
  { destruct (eq_dec dp sp) as [E|NE]; [subst dp| apply prop_right; auto].
    sep_apply (prot4_noise_mix_message_ephemeral_conflict shd shs e sp SH SH0).
    entailer!. }
  forward_if (PROP () LOCAL (gvars gv; temp WgNoise.noise.code._ephemeral_dst dp;
      temp WgNoise.noise.code._ephemeral_src sp; temp WgNoise.noise.code._chaining_key ckp;
      temp WgNoise.noise.code._hash hp)
    SEP (data_at shd (tarray tuchar 32) (map Vubyte e) dp;
      data_at shs (tarray tuchar 32) (map Vubyte e) sp; bytes_at shc ck ckp; bytes_at shh h hp;
      WgNoise.proof.blake2s.spec.blake2s_globals gv; curve25519_globals gv; zero_page gv; cookie_globals gv)).
  { forward_call (shd, shs, dp, sp, 32, e).
    entailer!. }
  { contradiction. }
  rewrite <- (prot4_noise_mix_message_ephemeral_bytes32 shs e sp H).
  rewrite <- (prot4_noise_mix_message_ephemeral_bytes32 shd e dp H).
  rewrite (prot4_noise_mix_message_ephemeral_b2s shs e sp) by lia.
  forward_call (gv, shh, hp, h, shs, sp, e).
  { apply prop_right; simpl; rewrite H; reflexivity. }
  { unfold wg_consts. cancel. }
  remember (mix_hash h e) as MH eqn:EMH.
  forward_call (gv, true, ckp, nullval, nullval, 0, 0, Tsh, Tsh, Tsh, shs, sp, e, shc, ckp, ck).
  { apply prop_right; simpl; rewrite H; reflexivity. }
  { destruct (eq_dec nullval nullval) as [_|NN]; [|congruence]. cancel. }
  destruct (eq_dec nullval nullval) as [_|NN]; [|congruence].
  rewrite <- (prot4_noise_mix_message_ephemeral_b2s shs e sp) by lia.
  remember (kdf1 ck e) as K eqn:EK. clear EK EMH.
  entailer!.
Qed.

End Body.
