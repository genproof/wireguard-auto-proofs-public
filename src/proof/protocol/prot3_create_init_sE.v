(* create_initiation, stage E (ci_B10, ci_B11): tai64n_now(timestamp); message_encrypt(dst->encrypted_timestamp, timestamp, 12, key, hash);
   See
   prot3_create_init_defs.v for ci_A (the state) and prot3_create_init_sA.v for a proved example
   (proof recipe: destruct R; simplify_func_tycontext; unfold ci_A, ci_B..; abbreviate_semax; forward ...). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_prog3.
Require Import WgNoise.proof.protocol.prot3_create_init_defs.

Section CI.
Context {Espec: OracleKind}.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.
#[local] Existing Instance Noise.CS.

Lemma prot3_create_init_sE_tai64n_len: forall a b, Zlength (tai64n a b) = 12.
Proof. intros. unfold tai64n, be64, be32. rewrite !Zlength_app, !Zlength_map. reflexivity. Qed.

Lemma prot3_create_init_sE_hash_len: forall a b, Zlength (mix_hash a b) = 32.
Proof.
intros. unfold mix_hash, HASH, WgNoise.proof.blake2s.model.blake2s, WgNoise.proof.blake2s.model.b2s_digest_stream, WgNoise.proof.blake2s.model.b2s_out. cbv zeta. rewrite Zlength_map. reflexivity.
Qed.

Lemma prot3_create_init_sE:
  forall gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
         ret mt ms me mes met hst he hc tv S T (Qc: environ -> mpred) (R: ret_assert) h k ts ct h3,
  writable_share shm -> writable_share shp -> readable_share shd -> writable_share sht ->
  Zlength h = 32 -> Zlength k = 32 ->
  ts = tai64n (s_rsec S) (s_rnsec S) -> ct = aead_enc k 0 h ts -> h3 = mix_hash h ct ->
  semax (ci_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
    (ci_A gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
       True ret mt ms me mes met hst he (bytes h) hc (bytes k) tv S T)
    (Ssequence ci_B10 ci_B11)
    (overridePost
      (ci_A gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
       True ret mt ms me mes (bytes ct) hst he (bytes h3) hc (bytes k) (bytes ts) S T)
      (loop1_ret_assert Qc R)).
Proof.
intros until h3. intros SHm SHp SHd SHt Lh Lk Ets Ect Eh3.
destruct R as [Rn Rb Rc Rr].
unfold ci_Delta. simplify_func_tycontext. unfold ci_A, ci_B10, ci_B11. abbreviate_semax.
assert (LTS: Zlength ts = 12) by (rewrite Ets; apply prot3_create_init_sE_tai64n_len).
forward_call (gv, S, Tsh, tp).
rewrite <- Ets. clear Ets.
assert_PROP (field_compatible t_hs (DOT I._hash) (hs_addr p)) as FCh by entailer!.
assert_PROP (field_compatible t_init (DOT I._encrypted_timestamp) m) as FCm by entailer!.
replace (bytes_at Tsh ts tp) with (prim_bytes Tsh ts tp)
  by (unfold prim_bytes, bytes_at; rewrite if_false by lia; reflexivity).
replace (data_at Tsh (tarray tuchar 32) (bytes k) kp) with (bytes_at Tsh k kp)
  by (unfold bytes_at; rewrite Lk; reflexivity).
rewrite (field_at_data_at shp t_hs (DOT I._hash)), (field_at_data_at shm t_init (DOT I._encrypted_timestamp)).
simpl nested_field_type.
replace (data_at shp (tarray tuchar 32) (bytes h)) with (bytes_at shp h)
  by (unfold bytes_at; rewrite Lh; reflexivity).
forward_call (gv, shm, field_address t_init (DOT I._encrypted_timestamp) m, Tsh, tp, ts, Tsh, kp, k, shp,
              field_address t_hs (DOT I._hash) (hs_addr p), h).
{ entailer!. simpl. rewrite LTS, !field_address_offset by auto. reflexivity. }
{ rewrite LTS. simpl (12 + 16). cancel. }
{ assert (L3: Zlength h3 = 32) by (rewrite Eh3; apply prot3_create_init_sE_hash_len).
  rewrite <- Ect, <- Eh3. clear Ect Eh3.
  rewrite (field_at_data_at shp t_hs (DOT I._hash)), (field_at_data_at shm t_init (DOT I._encrypted_timestamp)).
  simpl nested_field_type.
  unfold prim_bytes, bytes_at. rewrite if_false by lia. rewrite LTS, L3, Lk. simpl (12 + 16).
  entailer!. }
Qed.
End CI.
