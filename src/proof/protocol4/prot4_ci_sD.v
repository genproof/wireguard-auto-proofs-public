(* create_initiation, stage D (ci_B8, ci_B9): message_encrypt(dst->encrypted_static, static_identity->static_public, 32, key, hash); if (!mix_precomputed_dh(ck, key, precomputed_static_static)) break;
   See
   prot4_ci_defs.v for ci_A (the state) and prot4_ci_sA.v for a proved example
   (proof recipe: destruct R; simplify_func_tycontext; unfold ci_A, ci_B..; abbreviate_semax; forward ...). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require Import WgNoise.proof.protocol4.prot4_ci_defs.

Section CI.
Context {Espec: OracleKind}.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.
#[local] Existing Instance Noise.CS.

Lemma prot4_ci_sD_hash_len: forall d, Zlength (HASH d) = 32.
Proof.
intros. unfold HASH, WgNoise.proof.blake2s.model.blake2s, WgNoise.proof.blake2s.model.b2s_digest_stream,
  WgNoise.proof.blake2s.model.b2s_out.
cbv zeta. rewrite Zlength_map. reflexivity.
Qed.

Lemma prot4_ci_sD_kdf1_len: forall a b, Zlength (kdf1 a b) = 32.
Proof. intros. unfold kdf1, hmac. cbv zeta. apply prot4_ci_sD_hash_len. Qed.

Lemma prot4_ci_sD_kdf2_len: forall a b, Zlength (kdf2 a b) = 32.
Proof. intros. unfold kdf2, hmac. cbv zeta. apply prot4_ci_sD_hash_len. Qed.

Lemma prot4_ci_sD_mix_hash_len: forall a b, Zlength (mix_hash a b) = 32.
Proof. intros. unfold mix_hash. apply prot4_ci_sD_hash_len. Qed.

Lemma prot4_ci_sD:
  forall gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
         ret mt ms me mes met hst he tv S w T (Qc: environ -> mpred) (R: ret_assert) h ck k c h2 ck3 k3,
  writable_share shm -> writable_share shp -> readable_share shd -> writable_share sht ->
  Zlength pub = 32 -> Zlength ss = 32 -> Zlength h = 32 -> Zlength ck = 32 -> Zlength k = 32 ->
  c = aead_enc k 0 h pub -> h2 = mix_hash h c -> ck3 = kdf1 ck ss -> k3 = kdf2 ck ss ->
  (forall kv', memneq_bool ss zeros32 = false ->
   ci_A gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
       True ret mt ms me (bytes c) met hst he (bytes h2) (bytes ck) kv' tv S w T |-- RA_normal R) ->
  semax (ci_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
    (ci_A gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
       True ret mt ms me mes met hst he (bytes h) (bytes ck) (bytes k) tv S w T)
    (Ssequence ci_B8 ci_B9)
    (overridePost
      (ci_A gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
       (memneq_bool ss zeros32 = true) ret mt ms me (bytes c) met hst he (bytes h2) (bytes ck3) (bytes k3) tv S w T)
      (loop1_ret_assert Qc R)).
Proof.
intros until k3. intros SHm SHp SHd SHt Lpub Lss Lh Lck Lk Ec Eh2 Eck3 Ek3 HF.
destruct R as [Rn Rb Rc Rr]; simpl RA_normal in HF.
unfold ci_Delta. simplify_func_tycontext. unfold ci_A, ci_B8, ci_B9. abbreviate_semax.
forward.
assert_PROP (field_compatible t_hs (DOT I._chaining_key) (hs_addr p) /\ field_compatible t_hs (DOT I._hash) (hs_addr p) /\
  field_compatible t_hs (DOT I._precomputed_static_static) (hs_addr p) /\ field_compatible t_sid (DOT I._static_public) sid /\
  field_compatible t_init (DOT I._encrypted_static) m) as FC by entailer!.
destruct FC as (FC1 & FC2 & FC3 & FC4 & FC5).
rewrite (field_at_data_at shp t_hs (DOT I._chaining_key)), (field_at_data_at shp t_hs (DOT I._hash)),
  (field_at_data_at shp t_hs (DOT I._precomputed_static_static)), (field_at_data_at shd t_sid (DOT I._static_public)),
  (field_at_data_at shm t_init (DOT I._encrypted_static)).
simpl nested_field_type.
assert (Bpub: data_at shd (tarray tuchar 32) (bytes pub) (field_address t_sid (DOT I._static_public) sid) =
  prim_bytes shd pub (field_address t_sid (DOT I._static_public) sid)) by (unfold prim_bytes; rewrite Lpub; reflexivity).
assert (Bk: data_at Tsh (tarray tuchar 32) (bytes k) kp = bytes_at Tsh k kp) by (unfold bytes_at; rewrite Lk; reflexivity).
assert (Bh: data_at shp (tarray tuchar 32) (bytes h) (field_address t_hs (DOT I._hash) (hs_addr p)) =
  bytes_at shp h (field_address t_hs (DOT I._hash) (hs_addr p))) by (unfold bytes_at; rewrite Lh; reflexivity).
rewrite Bpub, Bk, Bh.
sep_apply (data_at_data_at_ shm (tarray tuchar 48) mes).
forward_call (gv, shm, field_address t_init (DOT I._encrypted_static) m, shd, field_address t_sid (DOT I._static_public) sid, pub,
  Tsh, kp, k, shp, field_address t_hs (DOT I._hash) (hs_addr p), h).
2: { rewrite Lpub. cancel. }
{ rewrite Lpub. apply prop_right. simpl. rewrite !field_address_offset by auto with field_compatible. reflexivity. }
assert (Lh2: Zlength h2 = 32) by (rewrite Eh2; apply prot4_ci_sD_mix_hash_len).
rewrite <- Ec, <- Eh2, <- Bpub, Lpub. clear Ec Eh2 Bpub Bh.
assert (Bck: data_at shp (tarray tuchar 32) (bytes ck) (field_address t_hs (DOT I._chaining_key) (hs_addr p)) =
  bytes_at shp ck (field_address t_hs (DOT I._chaining_key) (hs_addr p))) by (unfold bytes_at; rewrite Lck; reflexivity).
assert (Bss: data_at shp (tarray tuchar 32) (bytes ss) (field_address t_hs (DOT I._precomputed_static_static) (hs_addr p)) =
  bytes_at shp ss (field_address t_hs (DOT I._precomputed_static_static) (hs_addr p))) by (unfold bytes_at; rewrite Lss; reflexivity).
rewrite Bck, Bss, <- Bk.
sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (bytes k) kp).
forward_call (gv, kc, shp, field_address t_hs (DOT I._chaining_key) (hs_addr p), ck, Tsh, kp, shp,
  field_address t_hs (DOT I._precomputed_static_static) (hs_addr p), ss).
change (32 + 16) with 48.
destruct (memneq_bool ss zeros32) eqn:Hb.
- rewrite <- Eck3, <- Ek3.
  assert (Lck3: Zlength ck3 = 32) by (rewrite Eck3; apply prot4_ci_sD_kdf1_len).
  assert (Lk3: Zlength k3 = 32) by (rewrite Ek3; apply prot4_ci_sD_kdf2_len).
  clear Eck3 Ek3.
  forward_if.
  { exfalso; apply Int.one_not_zero; auto. }
  forward.
  unfold ci_A, bytes_at. rewrite Lh2, Lck3, Lk3, Lss.
  rewrite (field_at_data_at shp t_hs (DOT I._chaining_key)), (field_at_data_at shp t_hs (DOT I._hash)),
    (field_at_data_at shp t_hs (DOT I._precomputed_static_static)), (field_at_data_at shd t_sid (DOT I._static_public)),
    (field_at_data_at shm t_init (DOT I._encrypted_static)).
  simpl nested_field_type.
  entailer!.
- forward_if.
  2: { exfalso; apply H; reflexivity. }
  forward.
  eapply derives_trans; [|apply (HF (default_val (tarray tuchar 32)) eq_refl)].
  unfold ci_A, bytes_at, data_at_. rewrite Lh2, Lck, Lss.
  rewrite (field_at_data_at shp t_hs (DOT I._chaining_key)), (field_at_data_at shp t_hs (DOT I._hash)),
    (field_at_data_at shp t_hs (DOT I._precomputed_static_static)), (field_at_data_at shd t_sid (DOT I._static_public)),
    (field_at_data_at shm t_init (DOT I._encrypted_static)).
  simpl nested_field_type.
  entailer!.
Qed.
End CI.
