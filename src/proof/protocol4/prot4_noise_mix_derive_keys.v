(* group noise_mix: the body of noise.c's derive_keys against its specification
   (prot_specs4.v) in the context Gprot4 (prot_prog4.v), for ANY primitive models with their properties. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

Section Body.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.

Lemma prot4_noise_mix_derive_keys_split sh (k: list val) (b v p: val) :
  data_at sh t_sym (k, (b, v)) p =
  (field_at sh t_sym (DOT WgNoise.noise.code._key) k p *
  field_at sh t_sym (DOT WgNoise.noise.code._birthdate) b p *
  field_at sh t_sym (DOT WgNoise.noise.code._is_valid) v p * spacer sh 41 48 p)%logic.
Proof.
  unfold_data_at (data_at _ _ _ p).
  rewrite !sepcon_assoc; reflexivity.
Qed.

Lemma prot4_noise_mix_derive_keys_out32 h : Zlength (WgNoise.proof.blake2s.model.b2s_out 32 h) = 32.
Proof.
  unfold WgNoise.proof.blake2s.model.b2s_out. rewrite Zlength_map, Zlength_correct.
  reflexivity.
Qed.

Lemma prot4_noise_mix_derive_keys_hmac32 k d : Zlength (hmac k d) = 32.
Proof.
  unfold hmac, HASH, WgNoise.proof.blake2s.model.blake2s, WgNoise.proof.blake2s.model.b2s_digest_stream.
  apply prot4_noise_mix_derive_keys_out32.
Qed.

Lemma prot4_noise_mix_body_derive_keys :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_derive_keys derive_keys_spec.
Proof.
intros Hx Ha Hxa.
start_function.
forward_call (gv, S, w).
assert_PROP (field_compatible t_sym [] f) by entailer!.
assert_PROP (field_compatible t_sym [] s) by entailer!.
change (data_at_ sh1 t_sym f) with (data_at sh1 t_sym (Zrepeat Vundef 32, (Vundef, Vundef)) f).
change (data_at_ sh2 t_sym s) with (data_at sh2 t_sym (Zrepeat Vundef 32, (Vundef, Vundef)) s).
rewrite !prot4_noise_mix_derive_keys_split.
rewrite !(field_at_data_at _ t_sym (DOT WgNoise.noise.code._key)).
assert (Ef: field_address t_sym (DOT WgNoise.noise.code._key) f = f).
{ unfold field_address; rewrite if_true by auto with field_compatible. simpl. destruct H0 as [Pf _]. destruct f; try contradiction. simpl. rewrite Ptrofs.add_zero. reflexivity. }
assert (Es: field_address t_sym (DOT WgNoise.noise.code._key) s = s).
{ unfold field_address; rewrite if_true by auto with field_compatible. simpl. destruct H1 as [Ps _]. destruct s; try contradiction. simpl. rewrite Ptrofs.add_zero. reflexivity. }
rewrite Ef, Es. simpl nested_field_type. Intros.
assert (Pf: isptr f) by (destruct H0; auto).
assert (Ps: isptr s) by (destruct H1; auto).
assert (NEs: s <> nullval) by (destruct s; try contradiction; discriminate).
forward_call (gv, false, f, s, nullval, 32, 0, sh1, sh2, Tsh, Ews, nullval, @nil byte, shc, ckp, ck).
{ destruct (eq_dec s nullval) as [E|_]; [contradiction|]. destruct (eq_dec nullval nullval) as [_|NN]; [|congruence].
  rewrite spec.b2s_bytes_nil. cancel. }
{ rewrite Zlength_nil. computable. }
destruct (eq_dec s nullval) as [E|_]; [contradiction|]. destruct (eq_dec nullval nullval) as [_|NN]; [|congruence].
rewrite spec.b2s_bytes_nil. Intros.
remember (kdf1 ck []) as K1 eqn:E1. remember (kdf2 ck []) as K2 eqn:E2.
assert (L1: Zlength K1 = 32) by (subst K1; apply prot4_noise_mix_derive_keys_hmac32).
assert (L2: Zlength K2 = 32) by (subst K2; apply prot4_noise_mix_derive_keys_hmac32).
clear E1 E2.
repeat forward.
unfold symkey_rep, symkey_val. simpl sk_key; simpl sk_birth; simpl sk_valid.
rewrite !prot4_noise_mix_derive_keys_split.
rewrite !(field_at_data_at _ t_sym (DOT WgNoise.noise.code._key)).
rewrite Ef, Es. simpl nested_field_type.
unfold bytes_at at 2 3. rewrite L1, L2.
entailer!.
Qed.

End Body.
