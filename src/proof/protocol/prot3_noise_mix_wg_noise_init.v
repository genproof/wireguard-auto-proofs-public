(* group noise_mix: the body of noise.c's wg_noise_init against its specification
   (prot_specs3.v) in the context Gprot3 (prot_prog3.v), for ANY primitive models with their properties. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_prog3.
Require Import WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.blake2s.b2s_spec3.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

#[local] Instance prot3_noise_mix_wg_noise_init_n2b : change_composite_env Noise.CS Blake2s.CS.
Proof. make_cs_preserve Noise.CS Blake2s.CS. Defined.
#[local] Instance prot3_noise_mix_wg_noise_init_b2n : change_composite_env Blake2s.CS Noise.CS.
Proof. make_cs_preserve Blake2s.CS Noise.CS. Defined.

Lemma prot3_noise_mix_wg_noise_init_b2s_len key m : Zlength (blake2s key 32 m) = 32.
Proof.
  unfold blake2s, b2s_digest_stream, b2s_out. rewrite Zlength_map. reflexivity.
Qed.

Lemma prot3_noise_mix_wg_noise_init_data_at_b2s sh n bs p : Zlength bs = n -> n <> 0 ->
  @data_at Noise.CS sh (tarray tuchar n) (bytes bs) p = spec.b2s_bytes sh bs p.
Proof.
  intros. subst n. unfold bytes. rewrite spec.b2s_bytes_nonempty by auto.
  apply data_at_tarray_tuchar_cs.
Qed.

Lemma prot3_noise_mix_wg_noise_init_map_b2s (cs: compspecs) sh n bs p : Zlength bs = n -> n <> 0 ->
  @data_at cs sh (tarray tuchar n) (map Vubyte bs) p = spec.b2s_bytes sh bs p.
Proof.
  intros. subst n. rewrite spec.b2s_bytes_nonempty by auto.
  apply data_at_tarray_tuchar_cs.
Qed.

Section Body.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.

Lemma prot3_noise_mix_body_wg_noise_init :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body (QPvarspecs Noise.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_wg_noise_init wg_noise_init_spec.
Proof.
intros _ _ _.
start_function.
unfold noise_globals_raw, wg_consts. Intros.
assert (LHN: Zlength handshake_name = 37) by reflexivity.
assert (LIN: Zlength identifier_name = 34) by reflexivity.
remember handshake_name as HN eqn:EHN.
remember identifier_name as IN eqn:EIN.
rewrite (prot3_noise_mix_wg_noise_init_data_at_b2s Ers 37 HN) by lia.
sep_apply (data_at_data_at_ Ews (tarray tuchar 32) (bytes ck) (gv WgNoise.noise.code._handshake_init_chaining_key)).
rewrite (@data_at__tarray_tuchar_cs Noise.CS Blake2s.CS Ews 32).
forward_call (Ers, nullval, @nil byte, Ers, gv WgNoise.noise.code._handshake_name, HN, Ews, gv WgNoise.noise.code._handshake_init_chaining_key, 32, gv).
{ entailer!. }
{ rewrite spec.b2s_bytes_nil. cancel. }
{ rewrite Zlength_nil; lia. }
rewrite spec.b2s_bytes_nil.
assert (LCK: Zlength (blake2s [] 32 HN) = 32) by apply prot3_noise_mix_wg_noise_init_b2s_len.
remember (blake2s [] 32 HN) as CK eqn:ECK.
rewrite (prot3_noise_mix_wg_noise_init_map_b2s _ Ews 32 CK) by lia.
erewrite (@data_at__change_composite Noise.CS Blake2s.CS _ Tsh); [| prove_cs_preserve_type].
forward_call (Tsh, v_blake, 32).
forward_call (Tsh, v_blake, @nil byte, 32, @nil byte, Ews, gv WgNoise.noise.code._handshake_init_chaining_key, CK, gv).
{ entailer!. }
rewrite (prot3_noise_mix_wg_noise_init_data_at_b2s Ers 34 IN) by lia.
forward_call (Tsh, v_blake, @nil byte, 32, [] ++ CK, Ers, gv WgNoise.noise.code._identifier_name, IN, gv).
{ entailer!. }
sep_apply (data_at_data_at_ Ews (tarray tuchar 32) (bytes h) (gv WgNoise.noise.code._handshake_init_hash)).
rewrite (@data_at__tarray_tuchar_cs Noise.CS Blake2s.CS Ews 32).
forward_call (Tsh, v_blake, @nil byte, 32, ([] ++ CK) ++ IN, Ews, gv WgNoise.noise.code._handshake_init_hash, gv).
rewrite app_nil_l.
assert (LIH: Zlength (blake2s [] 32 (CK ++ IN)) = 32) by apply prot3_noise_mix_wg_noise_init_b2s_len.
assert (Eck: init_ck = CK) by (subst; reflexivity).
assert (Eih: init_hash = blake2s [] 32 (CK ++ IN)) by (unfold init_hash; rewrite Eck; subst; reflexivity).
remember (blake2s [] 32 (CK ++ IN)) as IH eqn:EIH.
rewrite <- (prot3_noise_mix_wg_noise_init_data_at_b2s Ers 34 IN) by lia.
rewrite <- (prot3_noise_mix_wg_noise_init_data_at_b2s Ews 32 CK) by lia.
rewrite <- (prot3_noise_mix_wg_noise_init_data_at_b2s Ers 37 HN) by lia.
rewrite (@data_at_tarray_tuchar_cs Blake2s.CS Noise.CS Ews 32).
sep_apply (@data_at_data_at_ Blake2s.CS Tsh t_blake2s_ctx b2s_ctx_zero v_blake).
erewrite (@data_at__change_composite Blake2s.CS Noise.CS _ Tsh t_blake2s_ctx); [| prove_cs_preserve_type].
unfold noise_globals. rewrite Eck, Eih. unfold noise_globals_raw, wg_consts. rewrite <- EHN, <- EIN.
clear ECK EIH EHN EIN Eck Eih.
change (map Vubyte IH) with (bytes IH).
entailer!.
Qed.

End Body.
