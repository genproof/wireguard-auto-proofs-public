(* create_initiation, stage F (ci_B12, ci_B13): dst->sender_index = wg_index_hashtable_insert(handshake->entry.peer->device->index_hashtable, &handshake->entry); handshake->state = HANDSHAKE_CREATED_INITIATION; ret = true;
   v4's stage lemma (prot4_ci_sF.v) re-proved over the v5 context and state (prot5_ci_defs.v); its
   helper lemmas are v4's. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require Import WgNoise.proof.protocol5.prot5_ci_defs.
Require Import WgNoise.proof.protocol4.prot4_ci_sF.

Section CI.
Context {Espec: OracleKind}.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.
#[local] Existing Instance Noise.CS.

Lemma prot5_ci_sF:
  forall gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
         ret mt ms me mes met hst he hh hc kv tv S w T (Qc: environ -> mpred) (R: ret_assert),
  writable_share shm -> writable_share shp -> readable_share shd -> writable_share sht ->
  hs_in_pool T p ->
  semax (ci5_Delta x25519 aead_enc aead_dec CSw)
    (ci5_A gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
       True ret mt ms me mes met hst he hh hc kv tv S w T)
    (Ssequence ci_B12 ci_B13)
    (overridePost
      (EX idx: int,
       ci5_A gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
       (t_fresh T (hs_addr p) idx) (Vint Int.one) mt (Vint idx) me mes met (Vint HS_CREATED_INITIATION) he hh hc kv tv
         (shim_u32 S idx) w (t_insert T (hs_addr p) idx))
      (loop1_ret_assert Qc R)).
Proof.
intros until R. intros SHm SHp SHd SHt HP.
unfold ci5_Delta. simplify_func_tycontext. unfold ci5_A, ci_B12, ci_B13. abbreviate_semax.
destruct R as [Rn Rb Rc Rr].
assert_PROP (field_compatible t_hs [] (hs_addr p)) as FC.
{ entailer!. clear - H11. destruct H11 as (A&B&C&D&_); repeat split; auto. }
assert_PROP (isptr tab) as Ptab. { unfold itable. Intros. entailer!. }
(* t'5 = handshake->entry.peer: the entry lives in the table's pool *)
sep_apply (prot4_ci_sF_open sht tab T p HP FC). Intros she E nx hd. rename H into RS, H0 into HPE.
unfold entry_val. forward.
sep_apply modus_ponens_wand. rewrite HPE.
forward. forward.
assert (HIn := prot4_ci_sF_in_saddrs T p HP).
forward_call (gv, S, w, sht, tab, T, hs_addr p, @None (share * entry)).
{ change (prot_specs4.raw_rep (hs_addr p) None) with emp. rewrite emp_sepcon. cancel. }
change (prot_specs4.raw_add T (hs_addr p) None) with T. Intros idx.
forward. forward. forward.
Exists idx. entailer!.
Qed.
End CI.
