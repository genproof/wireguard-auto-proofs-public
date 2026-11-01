(* group noise_mix: the body of noise.c's mix_precomputed_dh against its specification
   (prot_specs4.v) in the context Gprot4 (prot_prog4.v), for ANY primitive models with their properties. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require WgNoise.proof.libc.libc_bytes WgNoise.proof.blake2s.spec.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

Lemma prot4_noise_mix_mix_precomputed_dh_b2s sh bs p : Zlength bs <> 0 ->
  bytes_at sh bs p = WgNoise.proof.blake2s.spec.b2s_bytes sh bs p.
Proof.
  intros. unfold bytes_at, bytes. rewrite WgNoise.proof.blake2s.spec.b2s_bytes_nonempty by auto.
  apply WgNoise.proof.libc.libc_bytes.data_at_tarray_tuchar_cs.
Qed.

Section Body.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.

Lemma prot4_noise_mix_body_mix_precomputed_dh :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_mix_precomputed_dh mix_precomputed_dh_spec.
Proof.
intros _ _ _.
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

End Body.
