(* The bodies of the protocol piece v5, group `shim`: the shim (patch/wg_shim.c): clocks, randomness, allocation, refcount_t, peer references and the two tables; port of prot4_shim_small.v, prot4_shim_rc.v, prot4_shim_table1.v, prot4_shim_table2*.v (the two lookups over peers_rep5).
   Each function against its v5 specification (prot_specs5.v) in its unit's compspecs, with the context
   Gprot5 (prot_prog5.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require WgNoise.noise.code WgNoise.shim.code.
Require WgNoise.proof.protocol5.prot5_shim_small WgNoise.proof.protocol5.prot5_shim_table
  WgNoise.proof.protocol5.prot5_shim_lookup.

Theorem prot_bodies5_shim :
  forall x25519 aead_enc aead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  @semax_body (QPvarspecs Shim.qp) (Gprot5 x25519 aead_enc aead_dec CSw Shim.CS) Shim.CS
    WgNoise.shim.code.f_ktime_get_coarse_boottime_ns (ktime_get_coarse_boottime_ns_spec) /\
  @semax_body (QPvarspecs Shim.qp) (Gprot5 x25519 aead_enc aead_dec CSw Shim.CS) Shim.CS
    WgNoise.shim.code.f_ktime_get_real_ts64 (ktime_get_real_ts64_spec) /\
  @semax_body (QPvarspecs Shim.qp) (Gprot5 x25519 aead_enc aead_dec CSw Shim.CS) Shim.CS
    WgNoise.shim.code.f_get_random_bytes (get_random_bytes_spec) /\
  @semax_body (QPvarspecs Shim.qp) (Gprot5 x25519 aead_enc aead_dec CSw Shim.CS) Shim.CS
    WgNoise.shim.code.f_get_random_bytes_wait (get_random_bytes_wait_spec) /\
  @semax_body (QPvarspecs Shim.qp) (Gprot5 x25519 aead_enc aead_dec CSw Shim.CS) Shim.CS
    WgNoise.shim.code.f_get_random_u32 (get_random_u32_spec) /\
  @semax_body (QPvarspecs Shim.qp) (Gprot5 x25519 aead_enc aead_dec CSw Shim.CS) Shim.CS
    WgNoise.shim.code.f_kzalloc (kzalloc_spec CSw) /\
  @semax_body (QPvarspecs Shim.qp) (Gprot5 x25519 aead_enc aead_dec CSw Shim.CS) Shim.CS
    WgNoise.shim.code.f_kfree (kfree_spec CSw) /\
  @semax_body (QPvarspecs Shim.qp) (Gprot5 x25519 aead_enc aead_dec CSw Shim.CS) Shim.CS
    WgNoise.shim.code.f_kfree_sensitive (kfree_sensitive_spec CSw) /\
  @semax_body (QPvarspecs Shim.qp) (Gprot5 x25519 aead_enc aead_dec CSw Shim.CS) Shim.CS
    WgNoise.shim.code.f_wg_shim_refcount_warn_saturate (wg_shim_refcount_warn_saturate_spec) /\
  @semax_body (QPvarspecs Shim.qp) (Gprot5 x25519 aead_enc aead_dec CSw Shim.CS) Shim.CS
    WgNoise.shim.code.f_wg_shim_refcount_neg (wg_shim_refcount_neg_spec) /\
  @semax_body (QPvarspecs Shim.qp) (Gprot5 x25519 aead_enc aead_dec CSw Shim.CS) Shim.CS
    WgNoise.shim.code.f_wg_shim_refcount_inc_not_zero (wg_shim_refcount_inc_not_zero_spec) /\
  @semax_body (QPvarspecs Shim.qp) (Gprot5 x25519 aead_enc aead_dec CSw Shim.CS) Shim.CS
    WgNoise.shim.code.f_wg_shim_refcount_dec_and_test (wg_shim_refcount_dec_and_test_spec) /\
  @semax_body (QPvarspecs Shim.qp) (Gprot5 x25519 aead_enc aead_dec CSw Shim.CS) Shim.CS
    WgNoise.shim.code.f_wg_peer_get_maybe_zero (wg_peer_get_maybe_zero_spec) /\
  @semax_body (QPvarspecs Shim.qp) (Gprot5 x25519 aead_enc aead_dec CSw Shim.CS) Shim.CS
    WgNoise.shim.code.f_wg_shim_peer_release (wg_shim_peer_release_spec) /\
  @semax_body (QPvarspecs Shim.qp) (Gprot5 x25519 aead_enc aead_dec CSw Shim.CS) Shim.CS
    WgNoise.shim.code.f_wg_peer_put (wg_peer_put_spec) /\
  @semax_body (QPvarspecs Shim.qp) (Gprot5 x25519 aead_enc aead_dec CSw Shim.CS) Shim.CS
    WgNoise.shim.code.f_wg_pubkey_hashtable_lookup (wg_pubkey_hashtable_lookup_spec) /\
  @semax_body (QPvarspecs Shim.qp) (Gprot5 x25519 aead_enc aead_dec CSw Shim.CS) Shim.CS
    WgNoise.shim.code.f_wg_index_hashtable_remove (wg_index_hashtable_remove_spec) /\
  @semax_body (QPvarspecs Shim.qp) (Gprot5 x25519 aead_enc aead_dec CSw Shim.CS) Shim.CS
    WgNoise.shim.code.f_wg_shim_index_in_use (wg_shim_index_in_use_spec) /\
  @semax_body (QPvarspecs Shim.qp) (Gprot5 x25519 aead_enc aead_dec CSw Shim.CS) Shim.CS
    WgNoise.shim.code.f_wg_index_hashtable_insert (wg_index_hashtable_insert_spec) /\
  @semax_body (QPvarspecs Shim.qp) (Gprot5 x25519 aead_enc aead_dec CSw Shim.CS) Shim.CS
    WgNoise.shim.code.f_wg_index_hashtable_replace (wg_index_hashtable_replace_spec) /\
  @semax_body (QPvarspecs Shim.qp) (Gprot5 x25519 aead_enc aead_dec CSw Shim.CS) Shim.CS
    WgNoise.shim.code.f_wg_index_hashtable_lookup (wg_index_hashtable_lookup_spec).
Proof.
  intros.
  split; [apply prot5_shim_small.prot5_shim_body_ktime_get_coarse_boottime_ns |].
  split; [apply prot5_shim_small.prot5_shim_body_ktime_get_real_ts64 |].
  split; [apply prot5_shim_small.prot5_shim_body_get_random_bytes |].
  split; [apply prot5_shim_small.prot5_shim_body_get_random_bytes_wait |].
  split; [apply prot5_shim_small.prot5_shim_body_get_random_u32 |].
  split; [apply prot5_shim_small.prot5_shim_body_kzalloc |].
  split; [apply prot5_shim_small.prot5_shim_body_kfree |].
  split; [apply prot5_shim_small.prot5_shim_body_kfree_sensitive |].
  split; [apply prot5_shim_small.prot5_shim_body_warn_saturate |].
  split; [apply prot5_shim_small.prot5_shim_body_neg |].
  split; [apply prot5_shim_small.prot5_shim_body_inc_not_zero |].
  split; [apply prot5_shim_small.prot5_shim_body_dec_and_test |].
  split; [apply prot5_shim_small.prot5_shim_body_wg_peer_get_maybe_zero |].
  split; [apply prot5_shim_small.prot5_shim_body_wg_shim_peer_release |].
  split; [apply prot5_shim_small.prot5_shim_body_wg_peer_put |].
  split; [apply prot5_shim_lookup.prot5_shim_body_pklookup |].
  split; [apply prot5_shim_table.prot5_shim_body_remove |].
  split; [apply prot5_shim_table.prot5_shim_body_in_use |].
  split; [apply prot5_shim_table.prot5_shim_body_insert |].
  split; [apply prot5_shim_table.prot5_shim_body_replace |].
  apply prot5_shim_lookup.prot5_shim_body_ilookup.
Qed.
