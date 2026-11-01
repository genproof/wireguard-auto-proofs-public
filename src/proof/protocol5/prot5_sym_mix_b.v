(* The bodies of noise.c's mix_psk, handshake_init, message_encrypt, message_decrypt and message_ephemeral against
   their v5 specifications (prot_specs5.v: wg_consts5) in the context Gprot5 (prot_prog5.v), for any primitive
   models with their properties.  The scripts are v4's (prot4_noise_mix_*.v), whose helper lemmas are reused. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.protocol4.prot4_noise_mix_mix_psk.
Require Import WgNoise.proof.protocol4.prot4_noise_mix_handshake_init.
Require Import WgNoise.proof.protocol4.prot4_noise_mix_message_encrypt.
Require Import WgNoise.proof.protocol4.prot4_noise_mix_message_decrypt.
Require Import WgNoise.proof.protocol4.prot4_noise_mix_message_ephemeral.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require Import WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.blake2s.b2s_spec3.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

#[local] Instance CCE_sym5_n2b : change_composite_env Noise.CS Blake2s.CS.
Proof. make_cs_preserve Noise.CS Blake2s.CS. Defined.
#[local] Instance CCE_sym5_b2n : change_composite_env Blake2s.CS Noise.CS.
Proof. make_cs_preserve Blake2s.CS Noise.CS. Defined.

Section Body.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.

Lemma prot5_sym_body_mix_psk :
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_mix_psk mix_psk_spec.
Proof.
intros _ _.
start_function.
assert (L2: Zlength (kdf2 ck psk) = 32) by apply prot4_noise_mix_mix_psk_hmac_len.
assert_PROP (isptr v_temp_hash) by entailer!.
assert_PROP (isptr kp) by entailer!.
rewrite (prot4_noise_mix_mix_psk_b2s shp psk pp) by lia.
forward_call (gv, true, ckp, v_temp_hash, kp, 32, 32, shc, Tsh, shk, shp, pp, psk, shc, ckp, ck).
{ apply prop_right; simpl; rewrite H1; reflexivity. }
{ destruct (eq_dec v_temp_hash nullval) as [E|_]; [subst; contradiction|].
  destruct (eq_dec kp nullval) as [E|_]; [subst; contradiction|]. cancel. }
destruct (eq_dec v_temp_hash nullval) as [E|_]; [subst; contradiction|].
destruct (eq_dec kp nullval) as [E|_]; [subst; contradiction|].
rewrite (prot4_noise_mix_mix_psk_b2s Tsh (kdf2 ck psk) v_temp_hash) by lia.
forward_call (gv, shh, hp, h, Tsh, v_temp_hash, kdf2 ck psk).
rewrite <- (prot4_noise_mix_mix_psk_b2s Tsh (kdf2 ck psk) v_temp_hash) by lia.
sep_apply (prot4_noise_mix_mix_psk_forget Tsh (kdf2 ck psk) v_temp_hash L2).
forward_call (Tsh, v_temp_hash, 32).
sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (Zrepeat (Vubyte Byte.zero) 32) v_temp_hash).
rewrite <- (prot4_noise_mix_mix_psk_b2s shp psk pp) by lia.
entailer!.
Qed.

Lemma prot5_sym_body_handshake_init :
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_handshake_init handshake_init_spec.
Proof.
intros _ _.
start_function.
unfold noise_globals, noise_globals_raw. Intros.
(* never let the unifier see the BLAKE2s terms init_hash / init_ck *)
remember init_hash as IH eqn:EIH. remember init_ck as ICK eqn:EICK.
remember handshake_name as HN eqn:EHN. remember identifier_name as IN eqn:EIN.
rewrite (prot4_noise_mix_handshake_init_b2s shr rs rp) by lia.
unfold bytes_at.
forward_call (shh, Ews, hp, gv I._handshake_init_hash, 32, IH).
forward_call (shc, Ews, ckp, gv I._handshake_init_chaining_key, 32, ICK).
forward_call (gv, shh, hp, IH, shr, rp, rs).
{ apply prop_right; simpl; rewrite H; reflexivity. }
{ unfold bytes_at, bytes. rewrite H0. cancel. }
rewrite <- (prot4_noise_mix_handshake_init_b2s shr rs rp) by lia.
unfold noise_globals, noise_globals_raw. rewrite <- EIH, <- EICK, <- EHN, <- EIN. clear EIH EICK EHN EIN.
entailer!.
unfold bytes_at, bytes. rewrite H1. cancel.
Qed.

Lemma prot5_sym_body_message_encrypt :
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_message_encrypt (message_encrypt_spec aead_enc).
Proof.
intros _ Ha.
start_function.
unfold wg_consts5; Intros.
rewrite (prot4_noise_mix_message_encrypt_prim shh h hp) by lia.
unfold bytes_at, bytes. rewrite H0.
forward_call (shd, dp, shs, sp, m, shh, hp, h, 0, shk, kp, key, gv).
{ entailer!. rewrite H1. reflexivity. }
pose proof (aead_enc_length _ _ Ha key 0 h m) as HL.
remember (aead_enc key 0 h m) as c eqn:Ec.
pose proof (Zlength_nonneg m) as Hm0.
rewrite <- HL.
rewrite (prot4_noise_mix_message_encrypt_b2s shd c dp) by lia.
rewrite <- (prot4_noise_mix_message_encrypt_prim shh h hp) by lia.
forward_call (gv, shh, hp, h, shd, dp, c).
{ entailer!. rewrite HL. simpl. f_equal. }
{ unfold wg_consts5. cancel. }
rewrite <- (prot4_noise_mix_message_encrypt_b2s shd c dp) by lia.
replace (data_at shk (tarray tuchar 32) (map Vubyte key) kp) with (bytes_at shk key kp)
  by (unfold bytes_at, bytes; rewrite H0; reflexivity).
generalize (mix_hash h c); intros mh.
rewrite <- HL. unfold bytes.
entailer!.
Qed.

Lemma prot5_sym_body_message_decrypt :
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_message_decrypt (message_decrypt_spec aead_dec).
Proof.
intros _ Ha.
start_function.
unfold wg_consts5; Intros.
rewrite (prot4_noise_mix_message_decrypt_bytes32 shk key kp H0).
rewrite (prot4_noise_mix_message_decrypt_bytes_prim shh h hp) by lia.
change (out_bytes shd old dp) with (@prim_out Noise.CS shd old dp).
forward_call (shd, dp, old, shs, sp, c, shh, hp, h, 0, shk, kp, key, gv).
{ entailer!. rewrite H1. reflexivity. }
destruct (aead_dec key 0 h c) as [pt|] eqn:Hd.
- forward_if.
  { exfalso. apply Int.one_not_zero. assumption. }
  rewrite <- (prot4_noise_mix_message_decrypt_bytes_prim shh h hp) by lia.
  rewrite prot4_noise_mix_message_decrypt_prim_b2s.
  forward_call (gv, shh, hp, h, shs, sp, c).
  { unfold wg_consts5. cancel. }
  rewrite <- prot4_noise_mix_message_decrypt_prim_b2s.
  forward.
  rewrite (prot4_noise_mix_message_decrypt_bytes32 shk key kp H0).
  unfold wg_consts5. entailer!. apply derives_refl.
- forward_if.
  2: { exfalso; apply H3; reflexivity. }
  forward.
  rewrite <- (prot4_noise_mix_message_decrypt_bytes_prim shh h hp) by lia.
  rewrite (prot4_noise_mix_message_decrypt_bytes32 shk key kp H0).
  unfold wg_consts5. entailer!. apply derives_refl.
Qed.

Lemma prot5_sym_body_message_ephemeral :
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_message_ephemeral message_ephemeral_spec.
Proof.
intros _ _.
start_function.
unfold wg_consts5; Intros.
destruct alias.
- specialize (H2 eq_refl); subst dp.
  rewrite (prot4_noise_mix_message_ephemeral_bytes32 shs e sp H).
  forward_if (PROP () LOCAL (gvars gv; temp WgNoise.noise.code._ephemeral_dst sp;
      temp WgNoise.noise.code._ephemeral_src sp; temp WgNoise.noise.code._chaining_key ckp;
      temp WgNoise.noise.code._hash hp)
    SEP (data_at shs (tarray tuchar 32) (map Vubyte e) sp; bytes_at shc ck ckp; bytes_at shh h hp;
      WgNoise.proof.blake2s.spec.blake2s_globals gv; curve25519_globals gv; zero_page gv)).
  { exfalso; apply H2; reflexivity. }
  { forward. entailer!. }
  rewrite <- (prot4_noise_mix_message_ephemeral_bytes32 shs e sp H).
  rewrite (prot4_noise_mix_message_ephemeral_b2s shs e sp) by lia.
  forward_call (gv, shh, hp, h, shs, sp, e).
  { apply prop_right; simpl; rewrite H; reflexivity. }
  { unfold wg_consts5. cancel. }
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
      WgNoise.proof.blake2s.spec.blake2s_globals gv; curve25519_globals gv; zero_page gv)).
  { forward_call (shd, shs, dp, sp, 32, e).
    entailer!. }
  { contradiction. }
  rewrite <- (prot4_noise_mix_message_ephemeral_bytes32 shs e sp H).
  rewrite <- (prot4_noise_mix_message_ephemeral_bytes32 shd e dp H).
  rewrite (prot4_noise_mix_message_ephemeral_b2s shs e sp) by lia.
  forward_call (gv, shh, hp, h, shs, sp, e).
  { apply prop_right; simpl; rewrite H; reflexivity. }
  { unfold wg_consts5. cancel. }
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
