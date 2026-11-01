(* create_initiation, stage C (ci_B6, ci_B7): message_ephemeral(dst->eph, dst->eph, ck, hash); if (!mix_dh(ck, key, eph, remote_static)) break;
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

Lemma prot3_create_init_sC_hash_len: forall d, Zlength (HASH d) = 32.
Proof.
intros. unfold HASH, WgNoise.proof.blake2s.model.blake2s, WgNoise.proof.blake2s.model.b2s_digest_stream,
  WgNoise.proof.blake2s.model.b2s_out.
cbv zeta. rewrite Zlength_map. reflexivity.
Qed.

Lemma prot3_create_init_sC_hmac_len: forall k d, Zlength (hmac k d) = 32.
Proof. intros. unfold hmac. cbv zeta. apply prot3_create_init_sC_hash_len. Qed.

Lemma prot3_create_init_sC_ba: forall sh bs p, Zlength bs = 32 ->
  data_at sh (tarray tuchar 32) (bytes bs) p = bytes_at sh bs p.
Proof. intros. unfold bytes_at. rewrite H. reflexivity. Qed.

Lemma prot3_create_init_sC:
  forall gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
         ret mt ms mes met hst kv tv S T (Qc: environ -> mpred) (R: ret_assert) E e h ck ck1 h1 ck2 k2,
  writable_share shm -> writable_share shp -> readable_share shd -> writable_share sht ->
  Zlength rs = 32 -> Zlength E = 32 -> Zlength e = 32 -> Zlength h = 32 -> Zlength ck = 32 ->
  ck1 = kdf1 ck E -> h1 = mix_hash h E ->
  ck2 = kdf1 ck1 (x25519 e rs) -> k2 = kdf2 ck1 (x25519 e rs) ->
  (forall kv', dh_ok x25519 e rs = false ->
   ci_A gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
       True ret mt ms (bytes E) mes met hst (bytes e) (bytes h1) (bytes ck1) kv' tv S T |-- RA_normal R) ->
  semax (ci_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
    (ci_A gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
       True ret mt ms (bytes E) mes met hst (bytes e) (bytes h) (bytes ck) kv tv S T)
    (Ssequence ci_B6 ci_B7)
    (overridePost
      (ci_A gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
       (dh_ok x25519 e rs = true) ret mt ms (bytes E) mes met hst (bytes e) (bytes h1) (bytes ck2) (bytes k2) tv S T)
      (loop1_ret_assert Qc R)).
Proof.
intros until k2. intros SHm SHp SHd SHt Lrs LE Le Lh Lck Eck1 Eh1 Eck2 Ek2 HF.
destruct R as [Rn Rb Rc Rr]; simpl RA_normal in HF.
unfold ci_Delta. simplify_func_tycontext. unfold ci_A, ci_B6, ci_B7. abbreviate_semax.
assert (Lck1: Zlength ck1 = 32) by (rewrite Eck1; unfold kdf1; apply prot3_create_init_sC_hmac_len).
assert (Lh1: Zlength h1 = 32) by (rewrite Eh1; unfold mix_hash; apply prot3_create_init_sC_hash_len).
assert (Lck2: Zlength ck2 = 32) by (rewrite Eck2; unfold kdf1; apply prot3_create_init_sC_hmac_len).
assert (Lk2: Zlength k2 = 32) by (rewrite Ek2; unfold kdf2; apply prot3_create_init_sC_hmac_len).
assert_PROP (field_compatible t_hs (DOT I._chaining_key) (hs_addr p) /\ field_compatible t_hs (DOT I._hash) (hs_addr p) /\
  field_compatible t_hs (DOT I._remote_static) (hs_addr p) /\ field_compatible t_hs (DOT I._ephemeral_private) (hs_addr p) /\
  field_compatible t_init (DOT I._unencrypted_ephemeral) m) as FC by entailer!.
destruct FC as (FC1 & FC2 & FC3 & FC4 & FC5).
rewrite (field_at_data_at shp t_hs (DOT I._chaining_key)), (field_at_data_at shp t_hs (DOT I._hash)),
  (field_at_data_at shp t_hs (DOT I._remote_static)), (field_at_data_at shp t_hs (DOT I._ephemeral_private)),
  (field_at_data_at shm t_init (DOT I._unencrypted_ephemeral)).
simpl nested_field_type.
rewrite (prot3_create_init_sC_ba shp ck) by exact Lck. rewrite (prot3_create_init_sC_ba shp h) by exact Lh.
rewrite (prot3_create_init_sC_ba shp rs) by exact Lrs. rewrite (prot3_create_init_sC_ba shp e) by exact Le.
rewrite (prot3_create_init_sC_ba shm E) by exact LE.
forward_call (gv, true, shm, field_address t_init (DOT I._unencrypted_ephemeral) m, shm,
  field_address t_init (DOT I._unencrypted_ephemeral) m, E, shp, field_address t_hs (DOT I._chaining_key) (hs_addr p), ck,
  shp, field_address t_hs (DOT I._hash) (hs_addr p), h).
rewrite <- Eck1, <- Eh1. clear Eck1 Eh1.
assert_PROP (isptr kp) as Pk by entailer!.
sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) kv kp).
forward_call (gv, shp, field_address t_hs (DOT I._chaining_key) (hs_addr p), ck1, Tsh, kp, shp,
  field_address t_hs (DOT I._ephemeral_private) (hs_addr p), e, shp,
  field_address t_hs (DOT I._remote_static) (hs_addr p), rs).
{ destruct (eq_dec kp nullval); [subst kp; contradiction|]. cancel. }
destruct (eq_dec kp nullval); [subst kp; contradiction|].
destruct (dh_ok x25519 e rs) eqn:Hd.
- rewrite <- Eck2, <- Ek2. clear Eck2 Ek2.
  forward_if.
  { exfalso; apply Int.one_not_zero; auto. }
  forward.
  unfold ci_A.
  rewrite (field_at_data_at shp t_hs (DOT I._chaining_key)), (field_at_data_at shp t_hs (DOT I._hash)),
    (field_at_data_at shp t_hs (DOT I._remote_static)), (field_at_data_at shp t_hs (DOT I._ephemeral_private)),
    (field_at_data_at shm t_init (DOT I._unencrypted_ephemeral)).
  simpl nested_field_type.
  rewrite (prot3_create_init_sC_ba shp ck2) by exact Lck2. rewrite (prot3_create_init_sC_ba shp h1) by exact Lh1.
  rewrite (prot3_create_init_sC_ba shp rs) by exact Lrs. rewrite (prot3_create_init_sC_ba shp e) by exact Le.
  rewrite (prot3_create_init_sC_ba shm E) by exact LE. rewrite (prot3_create_init_sC_ba Tsh k2) by exact Lk2.
  entailer!.
- clear Eck2 Ek2.
  forward_if.
  2: { exfalso; apply H0; reflexivity. }
  forward.
  eapply derives_trans; [|apply (HF (default_val (tarray tuchar 32)) eq_refl)].
  unfold ci_A.
  rewrite (field_at_data_at shp t_hs (DOT I._chaining_key)), (field_at_data_at shp t_hs (DOT I._hash)),
    (field_at_data_at shp t_hs (DOT I._remote_static)), (field_at_data_at shp t_hs (DOT I._ephemeral_private)),
    (field_at_data_at shm t_init (DOT I._unencrypted_ephemeral)).
  simpl nested_field_type.
  rewrite (prot3_create_init_sC_ba shp ck1) by exact Lck1. rewrite (prot3_create_init_sC_ba shp h1) by exact Lh1.
  rewrite (prot3_create_init_sC_ba shp rs) by exact Lrs. rewrite (prot3_create_init_sC_ba shp e) by exact Le.
  rewrite (prot3_create_init_sC_ba shm E) by exact LE.
  unfold data_at_. entailer!.
Qed.
End CI.
