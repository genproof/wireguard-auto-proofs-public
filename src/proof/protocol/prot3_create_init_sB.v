(* create_initiation, stage B (ci_B2 .. ci_B5): dst->header.type = 1; handshake_init; curve25519_generate_secret; if (!curve25519_generate_public(..)) break;
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

Lemma prot3_create_init_sB_hash_len: forall d, Zlength (HASH d) = 32.
Proof.
intros. unfold HASH, WgNoise.proof.blake2s.model.blake2s, WgNoise.proof.blake2s.model.b2s_digest_stream,
  WgNoise.proof.blake2s.model.b2s_out.
cbv zeta. rewrite Zlength_map. reflexivity.
Qed.

Lemma prot3_create_init_sB_clamp_len: forall r, Zlength r = 32 -> Zlength (clamp r) = 32.
Proof. intros. unfold clamp. rewrite !Zlength_upd_Znth. auto. Qed.

Lemma prot3_create_init_sB:
  forall gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
         ret mt ms me mes met hst he hh hc kv tv S T (Qc: environ -> mpred) (R: ret_assert) ck0 h0,
  writable_share shm -> writable_share shp -> readable_share shd -> writable_share sht ->
  Zlength rs = 32 -> Zlength me = 32 ->
  ck0 = init_ck -> h0 = mix_hash init_hash rs ->
  (forall r, Zlength r = 32 ->
   (memneq_bool (clamp r) zeros32 && memneq_bool (x25519 (clamp r) basepoint9) zeros32)%bool = false ->
   ci_A gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
       True ret (Vint (Int.repr 1)) ms (if memneq_bool (clamp r) zeros32 then bytes (x25519 (clamp r) basepoint9) else me)
       mes met hst (bytes (clamp r)) (bytes h0) (bytes ck0) kv tv (shim_draw S r) T |-- RA_normal R) ->
  semax (ci_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
    (ci_A gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
       True ret mt ms me mes met hst he hh hc kv tv S T)
    (Ssequence ci_B2 (Ssequence ci_B3 (Ssequence ci_B4 ci_B5)))
    (overridePost
      (EX r: list byte,
       ci_A gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
       (Zlength r = 32 /\ memneq_bool (clamp r) zeros32 = true /\ memneq_bool (x25519 (clamp r) basepoint9) zeros32 = true)
         ret (Vint (Int.repr 1)) ms (bytes (x25519 (clamp r) basepoint9)) mes met hst (bytes (clamp r))
         (bytes h0) (bytes ck0) kv tv (shim_draw S r) T)
      (loop1_ret_assert Qc R)).
Proof.
intros until h0. intros SHm SHp SHd SHt Lrs Lme Eck Eh HF.
destruct R as [Rn Rb Rc Rr]; simpl RA_normal in HF.
unfold ci_Delta. simplify_func_tycontext. unfold ci_A, ci_B2, ci_B3, ci_B4, ci_B5. abbreviate_semax.
forward.
assert (Lck0: Zlength ck0 = 32) by (rewrite Eck; unfold init_ck; apply prot3_create_init_sB_hash_len).
assert (Lh0: Zlength h0 = 32) by (rewrite Eh; unfold mix_hash; apply prot3_create_init_sB_hash_len).
assert_PROP (field_compatible t_hs (DOT I._chaining_key) (hs_addr p) /\ field_compatible t_hs (DOT I._hash) (hs_addr p) /\
  field_compatible t_hs (DOT I._remote_static) (hs_addr p) /\ field_compatible t_hs (DOT I._ephemeral_private) (hs_addr p) /\
  field_compatible t_init (DOT I._unencrypted_ephemeral) m) as FC by entailer!.
destruct FC as (FC1 & FC2 & FC3 & FC4 & FC5).
rewrite (field_at_data_at shp t_hs (DOT I._chaining_key)), (field_at_data_at shp t_hs (DOT I._hash)),
  (field_at_data_at shp t_hs (DOT I._remote_static)).
simpl nested_field_type.
assert (Bk: data_at shp (tarray tuchar 32) (bytes rs) (field_address t_hs (DOT I._remote_static) (hs_addr p)) =
  bytes_at shp rs (field_address t_hs (DOT I._remote_static) (hs_addr p))) by (unfold bytes_at; rewrite Lrs; reflexivity).
rewrite Bk.
forward_call (gv, kc, shp, field_address t_hs (DOT I._chaining_key) (hs_addr p), shp, field_address t_hs (DOT I._hash) (hs_addr p),
  shp, field_address t_hs (DOT I._remote_static) (hs_addr p), rs).
rewrite <- Eh, <- Eck, <- Bk. clear Eh Eck Bk.
unfold bytes_at. rewrite Lh0, Lck0.
rewrite (field_at_data_at shp t_hs (DOT I._ephemeral_private)), (field_at_data_at shm t_init (DOT I._unencrypted_ephemeral)).
simpl nested_field_type.
sep_apply (data_at_data_at_ shp (tarray tuchar 32) he).
forward_call (gv, S, shp, field_address t_hs (DOT I._ephemeral_private) (hs_addr p)).
Intros r.
assert (Lc: Zlength (clamp r) = 32) by (apply prot3_create_init_sB_clamp_len; auto).
unfold bytes_at. rewrite Lc.
unfold wg_consts. Intros.
forward_call (shm, field_address t_init (DOT I._unencrypted_ephemeral) m, me, shp,
  field_address t_hs (DOT I._ephemeral_private) (hs_addr p), clamp r, gv).
destruct (memneq_bool (clamp r) zeros32 && memneq_bool (x25519 (clamp r) basepoint9) zeros32)%bool eqn:Hb.
- apply andb_prop in Hb. destruct Hb as [Hb1 Hb2]. rewrite Hb1.
  forward_if.
  { exfalso; apply Int.one_not_zero; auto. }
  forward.
  Exists r.
  unfold ci_A, wg_consts.
  rewrite (field_at_data_at shp t_hs (DOT I._chaining_key)), (field_at_data_at shp t_hs (DOT I._hash)),
    (field_at_data_at shp t_hs (DOT I._remote_static)), (field_at_data_at shp t_hs (DOT I._ephemeral_private)),
    (field_at_data_at shm t_init (DOT I._unencrypted_ephemeral)).
  simpl nested_field_type.
  entailer!.
- forward_if.
  2: { exfalso; apply H0; reflexivity. }
  forward.
  eapply derives_trans; [|apply (HF r H Hb)].
  unfold ci_A, wg_consts.
  rewrite (field_at_data_at shp t_hs (DOT I._chaining_key)), (field_at_data_at shp t_hs (DOT I._hash)),
    (field_at_data_at shp t_hs (DOT I._remote_static)), (field_at_data_at shp t_hs (DOT I._ephemeral_private)),
    (field_at_data_at shm t_init (DOT I._unencrypted_ephemeral)).
  simpl nested_field_type.
  entailer!.
Qed.
End CI.
