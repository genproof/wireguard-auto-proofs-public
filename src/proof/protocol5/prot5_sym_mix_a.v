(* The bodies of noise.c's wg_noise_init, derive_keys, mix_dh, mix_precomputed_dh and mix_hash against their v5
   specifications (prot_specs5.v: wg_consts5) in the context Gprot5 (prot_prog5.v), for any primitive models with
   their properties.  The scripts are v4's (prot4_noise_mix_*.v), whose helper lemmas are reused. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.protocol4.prot4_noise_mix_wg_noise_init.
Require Import WgNoise.proof.protocol4.prot4_noise_mix_derive_keys.
Require Import WgNoise.proof.protocol4.prot4_noise_mix_mix_dh.
Require Import WgNoise.proof.protocol4.prot4_noise_mix_mix_precomputed_dh.
Require Import WgNoise.proof.protocol4.prot4_noise_mix_mix_hash.
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

Lemma prot5_sym_body_wg_noise_init :
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_wg_noise_init wg_noise_init_spec.
Proof.
intros _ _.
start_function.
unfold noise_globals_raw, wg_consts5. Intros.
assert (LHN: Zlength handshake_name = 37) by reflexivity.
assert (LIN: Zlength identifier_name = 34) by reflexivity.
remember handshake_name as HN eqn:EHN.
remember identifier_name as IN eqn:EIN.
rewrite (prot4_noise_mix_wg_noise_init_data_at_b2s Ers 37 HN) by lia.
sep_apply (data_at_data_at_ Ews (tarray tuchar 32) (bytes ck) (gv WgNoise.noise.code._handshake_init_chaining_key)).
rewrite (@data_at__tarray_tuchar_cs Noise.CS Blake2s.CS Ews 32).
forward_call (Ers, nullval, @nil byte, Ers, gv WgNoise.noise.code._handshake_name, HN, Ews, gv WgNoise.noise.code._handshake_init_chaining_key, 32, gv).
{ entailer!. }
{ rewrite spec.b2s_bytes_nil. cancel. }
{ rewrite Zlength_nil; lia. }
rewrite spec.b2s_bytes_nil.
assert (LCK: Zlength (blake2s [] 32 HN) = 32) by apply prot4_noise_mix_wg_noise_init_b2s_len.
remember (blake2s [] 32 HN) as CK eqn:ECK.
rewrite (prot4_noise_mix_wg_noise_init_map_b2s _ Ews 32 CK) by lia.
erewrite (@data_at__change_composite Noise.CS Blake2s.CS _ Tsh); [| prove_cs_preserve_type].
forward_call (Tsh, v_blake, 32).
forward_call (Tsh, v_blake, @nil byte, 32, @nil byte, Ews, gv WgNoise.noise.code._handshake_init_chaining_key, CK, gv).
{ entailer!. }
rewrite (prot4_noise_mix_wg_noise_init_data_at_b2s Ers 34 IN) by lia.
forward_call (Tsh, v_blake, @nil byte, 32, [] ++ CK, Ers, gv WgNoise.noise.code._identifier_name, IN, gv).
{ entailer!. }
sep_apply (data_at_data_at_ Ews (tarray tuchar 32) (bytes h) (gv WgNoise.noise.code._handshake_init_hash)).
rewrite (@data_at__tarray_tuchar_cs Noise.CS Blake2s.CS Ews 32).
forward_call (Tsh, v_blake, @nil byte, 32, ([] ++ CK) ++ IN, Ews, gv WgNoise.noise.code._handshake_init_hash, gv).
rewrite app_nil_l.
assert (LIH: Zlength (blake2s [] 32 (CK ++ IN)) = 32) by apply prot4_noise_mix_wg_noise_init_b2s_len.
assert (Eck: init_ck = CK) by (subst; reflexivity).
assert (Eih: init_hash = blake2s [] 32 (CK ++ IN)) by (unfold init_hash; rewrite Eck; subst; reflexivity).
remember (blake2s [] 32 (CK ++ IN)) as IH eqn:EIH.
rewrite <- (prot4_noise_mix_wg_noise_init_data_at_b2s Ers 34 IN) by lia.
rewrite <- (prot4_noise_mix_wg_noise_init_data_at_b2s Ews 32 CK) by lia.
rewrite <- (prot4_noise_mix_wg_noise_init_data_at_b2s Ers 37 HN) by lia.
rewrite (@data_at_tarray_tuchar_cs Blake2s.CS Noise.CS Ews 32).
sep_apply (@data_at_data_at_ Blake2s.CS Tsh t_blake2s_ctx b2s_ctx_zero v_blake).
erewrite (@data_at__change_composite Blake2s.CS Noise.CS _ Tsh t_blake2s_ctx); [| prove_cs_preserve_type].
unfold noise_globals. rewrite Eck, Eih. unfold noise_globals_raw, wg_consts5. rewrite <- EHN, <- EIN.
clear ECK EIH EHN EIN Eck Eih.
change (map Vubyte IH) with (bytes IH).
entailer!.
Qed.

Lemma prot5_sym_body_derive_keys :
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_derive_keys derive_keys_spec.
Proof.
intros Hx Ha.
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

Lemma prot5_sym_body_mix_dh :
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_mix_dh (mix_dh_spec x25519).
Proof.
intros Hx _.
start_function.
unfold wg_consts5; Intros.
unfold bytes_at, bytes. rewrite H0, H1.
forward_call (Tsh, v_dh_calculation, shv, pv, priv, shb, pb, pub, gv).
pose proof (Hx priv pub) as HX.
unfold dh_ok.
destruct (memneq_bool (x25519 priv pub) zeros32) eqn:Hm.
- forward_if.
  { exfalso; apply Int.one_not_zero; assumption. }
  replace_SEP 0 (WgNoise.proof.blake2s.spec.b2s_bytes Tsh (x25519 priv pub) v_dh_calculation).
  { rewrite <- prot4_noise_mix_mix_dh_b2s by lia. unfold bytes_at, bytes. rewrite HX. entailer!. }
  fold (bytes_at shc ck ckp).
  forward_call (gv, true, ckp, kp, nullval, 32, 0, shc, shk, shk, Tsh, v_dh_calculation, x25519 priv pub, shc, ckp, ck).
  { apply prop_right; simpl; rewrite HX; reflexivity. }
  { unfold wg_consts5. cancel. destruct (eq_dec kp nullval); [cancel|].
    destruct (eq_dec nullval nullval) as [_|NN]; [|congruence]. cancel. }
  rewrite <- (prot4_noise_mix_mix_dh_b2s Tsh (x25519 priv pub) v_dh_calculation) by lia.
  sep_apply (prot4_noise_mix_mix_dh_forget Tsh (x25519 priv pub) v_dh_calculation HX).
  forward_call (Tsh, v_dh_calculation, 32).
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (Zrepeat (Vubyte Byte.zero) 32) v_dh_calculation).
  forward.
  unfold dh_ok; rewrite Hm.
  rewrite (prot4_noise_mix_mix_dh_bytes32 shv priv pv H0), (prot4_noise_mix_mix_dh_bytes32 shb pub pb H1).
  destruct (eq_dec kp nullval) as [E|NE].
  + unfold wg_consts5. entailer!.
  + destruct (eq_dec nullval nullval) as [_|NN]; [|congruence].
    unfold wg_consts5. entailer!.
- forward_if.
  2: { exfalso; apply H2; reflexivity. }
  forward.
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (map Vubyte (x25519 priv pub)) v_dh_calculation).
  unfold dh_ok; rewrite Hm.
  rewrite (prot4_noise_mix_mix_dh_bytes32 shv priv pv H0), (prot4_noise_mix_mix_dh_bytes32 shb pub pb H1).
  unfold wg_consts5. entailer!.
Qed.

Lemma prot5_sym_body_mix_precomputed_dh :
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_mix_precomputed_dh mix_precomputed_dh_spec.
Proof.
intros _ _.
start_function.
unfold noise_globals, noise_globals_raw. Intros.
(* never let the unifier see the BLAKE2s terms init_hash / init_ck *)
remember init_hash as IH eqn:EIH. remember init_ck as ICK eqn:EICK.
remember handshake_name as HN eqn:EHN. remember identifier_name as IN eqn:EIN.
unfold bytes_at. rewrite H0.
forward_call (shp, Ews, pp, gv I._zero_point, 32, pre, zeros32).
destruct (memneq_bool pre zeros32) eqn:Hm.
- forward_if.
  { exfalso; apply Int.one_not_zero; assumption. }
  assert_PROP (isptr kp) by entailer!.
  replace_SEP 0 (WgNoise.proof.blake2s.spec.b2s_bytes shp pre pp).
  { rewrite <- prot4_noise_mix_mix_precomputed_dh_b2s by lia. unfold bytes_at, bytes. rewrite H0. entailer!. }
  fold (bytes_at shc ck ckp).
  forward_call (gv, true, ckp, kp, nullval, 32, 0, shc, shk, shk, shp, pp, pre, shc, ckp, ck).
  { apply prop_right; simpl; rewrite H0; reflexivity. }
  { destruct (eq_dec kp nullval) as [E|NE]; [subst kp; simpl in H4; contradiction |]; destruct (eq_dec nullval nullval) as [_|NN]; [|congruence].
    cancel. }
  destruct (eq_dec kp nullval) as [E|NE]; [subst kp; simpl in H4; contradiction |]; destruct (eq_dec nullval nullval) as [_|NN]; [|congruence].
  forward.
  rewrite <- (prot4_noise_mix_mix_precomputed_dh_b2s shp pre pp) by lia.
  unfold noise_globals, noise_globals_raw.
  remember init_hash as IH eqn:EIH. remember init_ck as ICK eqn:EICK.
  remember handshake_name as HN eqn:EHN. remember identifier_name as IN eqn:EIN.
  assert (Zlength IH = 32) by (subst IH; auto). assert (Zlength ICK = 32) by (subst ICK; auto).
  clear EIH EICK EHN EIN.
  entailer!.
- forward_if.
  2: { exfalso; apply H3; reflexivity. }
  forward.
  unfold noise_globals, noise_globals_raw.
  remember init_hash as IH eqn:EIH. remember init_ck as ICK eqn:EICK.
  remember handshake_name as HN eqn:EHN. remember identifier_name as IN eqn:EIN.
  assert (Zlength IH = 32) by (subst IH; auto). assert (Zlength ICK = 32) by (subst ICK; auto).
  clear EIH EICK EHN EIN.
  unfold bytes_at, bytes. rewrite H0. entailer!.
Qed.

Lemma prot5_sym_body_mix_hash :
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_mix_hash mix_hash_spec.
Proof.
intros _ _.
start_function.
unfold wg_consts5; Intros.
erewrite (@data_at__change_composite Noise.CS Blake2s.CS _ Tsh); [| prove_cs_preserve_type].
forward_call (Tsh, v_blake, 32).
rewrite (prot4_noise_mix_mix_hash_b2s shh h hp) by lia.
forward_call (Tsh, v_blake, @nil byte, 32, @nil byte, shh, hp, h, gv).
{ entailer!. rewrite H. reflexivity. }
forward_call (Tsh, v_blake, @nil byte, 32, [] ++ h, shs, sp, src, gv).
rewrite (spec.b2s_bytes_nonempty shh h hp) by lia. rewrite H.
sep_apply (@data_at_data_at_ Blake2s.CS shh (tarray tuchar 32) (map Vubyte h) hp).
forward_call (Tsh, v_blake, @nil byte, 32, ([] ++ h) ++ src, shh, hp, gv).
sep_apply (@data_at_data_at_ Blake2s.CS Tsh t_blake2s_ctx b2s_ctx_zero v_blake).
erewrite (@data_at__change_composite Blake2s.CS Noise.CS _ Tsh t_blake2s_ctx); [| prove_cs_preserve_type].
rewrite app_nil_l.
change (blake2s [] 32 (h ++ src)) with (mix_hash h src).
pose proof (prot4_noise_mix_mix_hash_len h src) as Hl.
generalize (mix_hash h src) Hl; intros mh Hmh.
forward.
unfold wg_consts5, bytes_at, bytes. rewrite Hmh.
rewrite (@data_at_tarray_tuchar_cs Blake2s.CS Noise.CS).
entailer!.
Qed.

End Body.
