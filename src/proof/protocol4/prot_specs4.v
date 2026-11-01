(* the specifications of the protocol piece v4 = prot_specs3.v (same
   names, same model and representation: prot_model3 / prot_repr3) with the shim's refcount_t WARNINGS EXACT:
   every `shim_state gv S` of v3 is `shim_state4 gv S w` here (prot_repr4.v; `w` in the WITH clause right after
   S), and the post states the warnings after the call: unchanged, except
   - the five wg_shim_refcount_* functions (refwarn4 gv w; warn_bump / rc_inz_warn / rc_inc_warn / rc_dec_warn),
   - wg_peer_get_maybe_zero / wg_peer_put (rc_inz_warn / rc_dec_warn of the peer's count unless NULL),
   - the keypair functions (prot_model4.v: kp_get_warn, kp_put_warn and the chains of keypairs_clear,
     add_new_keypair, received_with_keypair, begin_session, in the v3 models' kp_put order).
   Generalised (v2 laws): the two table lookups require peers_refs_ok PS (all their callers have it; then no
   lookup warns); wg_noise_received_with_keypair takes k = NULL or ANY keypair whose entry is in the table's pool
   (another peer's too: the pointer comparison's valid_pointer comes from the pool); keypair_create and
   begin_session have no bound on keypair_counter.
   v3's text follows. *)
(* The specifications of the protocol piece: every function of noise.c, cookie.c
   and patch/wg_shim.c listed in protocol_idents (protocol_piece.v).  ONE specification per function, for
   every client that uses it correctly; shared by the 8 protocol laws.  Model: prot_model.v;
   representation: prot_repr.v.

   Parameterised by the functional models of the primitives (x25519, aead_enc/dec, xaead_enc/dec) and by the world
   compspecs CSw (malloc tokens, mem_mgr).  The object predicates are in Noise.CS (Cookie.CS for sk_buff
   and the cookie message); byte arrays are the same in every compspecs.

   buffers hashed by BLAKE2s are bounded by
   PTRDIFF_MAX (Int64.max_signed, b2s_spec3.v) instead of 2^64 - 1.

   Common shape: every function that reads a shim global (clocks, randomness, allocation counters, rate
   limiter) carries `shim_state gv S` (S -> S'); every function that reaches BLAKE2s, Curve25519 or the
   AEAD carries `wg_consts gv` (the read-only tables); noise.c's own globals are `noise_globals gv kc`
   (after wg_noise_init; kc = keypair_counter). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import QuickProof.Env.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.
Local Open Scope logic.

Module N := WgNoise.noise.code.
Module C := WgNoise.cookie.code.
Module Sh := WgNoise.shim.code.

Section Specs.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.

Definition t_rcu := Tstruct N._rcu_head noattr.

(* ================================================================================================ *)
(* patch/wg_shim.c                                                                                  *)
(* ================================================================================================ *)

Definition ktime_get_coarse_boottime_ns_spec :=
  DECLARE Sh._ktime_get_coarse_boottime_ns
  WITH gv: globals, S: shim, w: list int64
  PRE [ ]
    PROP () PARAMS () GLOBALS (gv) SEP (shim_state4 gv S w)
  POST [ tulong ]
    PROP () RETURN (Vlong (s_boot S)) SEP (shim_state4 gv S w).

Definition ktime_get_real_ts64_spec :=
  DECLARE Sh._ktime_get_real_ts64
  WITH gv: globals, S: shim, w: list int64, sh: share, ts: val
  PRE [ tptr t_timespec ]
    PROP (writable_share sh) PARAMS (ts) GLOBALS (gv)
    SEP (shim_state4 gv S w; data_at_ sh t_timespec ts)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (shim_state4 gv S w; data_at sh t_timespec (Vlong (s_rsec S), Vlong (s_rnsec S)) ts).

(* get_random_bytes(buf, n): n arbitrary bytes bs; the log keeps the first 32 (shim_draw) *)
Definition get_random_bytes_spec :=
  DECLARE Sh._get_random_bytes
  WITH gv: globals, S: shim, w: list int64, sh: share, buf: val, n: Z
  PRE [ tptr tvoid, tulong ]
    PROP (writable_share sh; 0 <= n <= Int64.max_unsigned) PARAMS (buf; Vlong (Int64.repr n)) GLOBALS (gv)
    SEP (shim_state4 gv S w; data_at_ sh (tarray tuchar n) buf)
  POST [ tvoid ] EX bs: list byte,
    PROP (Zlength bs = n) RETURN ()
    SEP (shim_state4 gv (shim_draw S bs) w; bytes_at sh bs buf).

Definition get_random_bytes_wait_spec :=
  DECLARE Sh._get_random_bytes_wait
  WITH gv: globals, S: shim, w: list int64, sh: share, buf: val, n: Z
  PRE [ tptr tvoid, tulong ]
    PROP (writable_share sh; 0 <= n <= Int64.max_unsigned) PARAMS (buf; Vlong (Int64.repr n)) GLOBALS (gv)
    SEP (shim_state4 gv S w; data_at_ sh (tarray tuchar n) buf)
  POST [ tvoid ] EX bs: list byte,
    PROP (Zlength bs = n) RETURN ()
    SEP (shim_state4 gv (shim_draw S bs) w; bytes_at sh bs buf).

Definition get_random_u32_spec :=
  DECLARE Sh._get_random_u32
  WITH gv: globals, S: shim, w: list int64
  PRE [ ]
    PROP () PARAMS () GLOBALS (gv) SEP (shim_state4 gv S w)
  POST [ tuint ] EX n: int,
    PROP () RETURN (Vint n) SEP (shim_state4 gv (shim_u32 S n) w).

(* kzalloc(n, flags): NULL (always when the test knob is set) or n zero bytes with a malloc token *)
Definition kzalloc_spec :=
  DECLARE Sh._kzalloc
  WITH gv: globals, S: shim, w: list int64, n: Z, fl: int
  PRE [ tulong, tuint ]
    PROP (0 <= n <= Int64.max_unsigned) PARAMS (Vlong (Int64.repr n); Vint fl) GLOBALS (gv)
    SEP (mem_mgr gv; shim_state4 gv S w)
  POST [ tptr tvoid ] EX p: val,
    PROP (s_failnext S = true -> p = nullval) RETURN (p)
    SEP (mem_mgr gv;
         shim_state4 gv (if eq_dec p nullval then shim_alloc_fail S else shim_alloc_ok S) w;
         if eq_dec p nullval then emp
         else (@malloc_token CSw Ews (tarray tuchar n) p * bytes_at Ews (zeros n) p)).

Definition kfree_spec :=
  DECLARE Sh._kfree
  WITH gv: globals, S: shim, w: list int64, p: val, n: Z
  PRE [ tptr tvoid ]
    PROP (0 <= n) PARAMS (p) GLOBALS (gv)
    SEP (mem_mgr gv; shim_state4 gv S w;
         if eq_dec p nullval then emp
         else (@malloc_token CSw Ews (tarray tuchar n) p * data_at_ Ews (tarray tuchar n) p))
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (mem_mgr gv; shim_state4 gv (if eq_dec p nullval then S else shim_free S) w).

Definition kfree_sensitive_spec :=
  DECLARE Sh._kfree_sensitive
  WITH gv: globals, S: shim, w: list int64, p: val, n: Z
  PRE [ tptr tvoid ]
    PROP (0 <= n) PARAMS (p) GLOBALS (gv)
    SEP (mem_mgr gv; shim_state4 gv S w;
         if eq_dec p nullval then emp
         else (@malloc_token CSw Ews (tarray tuchar n) p * data_at_ Ews (tarray tuchar n) p))
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (mem_mgr gv; shim_state4 gv (if eq_dec p nullval then S else shim_free S) w).

(* the kernel's refcount_t (include/linux/refcount.h, lib/refcount.c, one thread) in the shim:
   wg_shim_refcount_* of patch/wg_shim.c, called by kref_get / kref_get_unless_zero / kref_put
   (patch/include/quickproof_kref.h).  Counts exact (rc_add1 / rc_sub1, saturation included); the warnings
   wg_shim_refcount_warn are kept existentially (refwarn, part of shim_state). *)
Definition wg_shim_refcount_warn_saturate_spec :=
  DECLARE Sh._wg_shim_refcount_warn_saturate
  WITH gv: globals, w: list int64, sh: share, r: val, v: int, t: Z
  PRE [ tptr tuint, tint ]
    PROP (writable_share sh; 0 <= t < 5) PARAMS (r; Vint (Int.repr t)) GLOBALS (gv)
    SEP (data_at sh tuint (Vint v) r; refwarn4 gv w)
  POST [ tvoid ]
    PROP () RETURN () SEP (data_at sh tuint (Vint REFCOUNT_SATURATED) r; refwarn4 gv (warn_bump w t)).

Definition wg_shim_refcount_neg_spec :=
  DECLARE Sh._wg_shim_refcount_neg
  WITH v: int
  PRE [ tuint ] PROP () PARAMS (Vint v) SEP ()
  POST [ tbool ] PROP () RETURN (Val.of_bool (rc_neg v)) SEP ().

(* refcount_inc_not_zero *)
Definition wg_shim_refcount_inc_not_zero_spec :=
  DECLARE Sh._wg_shim_refcount_inc_not_zero
  WITH gv: globals, w: list int64, sh: share, r: val, v: int
  PRE [ tptr tuint ]
    PROP (writable_share sh) PARAMS (r) GLOBALS (gv)
    SEP (data_at sh tuint (Vint v) r; refwarn4 gv w)
  POST [ tbool ]
    PROP () RETURN (Val.of_bool (negb (Int.eq v Int.zero)))
    SEP (data_at sh tuint (Vint (if Int.eq v Int.zero then v else rc_add1 v)) r; refwarn4 gv (rc_inz_warn v w)).

(* refcount_inc (kref_get): an increment of 0 saturates too (use after free) *)
Definition wg_shim_refcount_inc_spec :=
  DECLARE Sh._wg_shim_refcount_inc
  WITH gv: globals, w: list int64, sh: share, r: val, v: int
  PRE [ tptr tuint ]
    PROP (writable_share sh) PARAMS (r) GLOBALS (gv)
    SEP (data_at sh tuint (Vint v) r; refwarn4 gv w)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh tuint (Vint (if Int.eq v Int.zero then REFCOUNT_SATURATED else rc_add1 v)) r; refwarn4 gv (rc_inc_warn v w)).

(* refcount_dec_and_test (kref_put): true exactly at the release (the count goes from 1 to 0) *)
Definition wg_shim_refcount_dec_and_test_spec :=
  DECLARE Sh._wg_shim_refcount_dec_and_test
  WITH gv: globals, w: list int64, sh: share, r: val, v: int
  PRE [ tptr tuint ]
    PROP (writable_share sh) PARAMS (r) GLOBALS (gv)
    SEP (data_at sh tuint (Vint v) r; refwarn4 gv w)
  POST [ tbool ]
    PROP () RETURN (Val.of_bool (Int.eq (rc_sub1 v) Int.zero))
    SEP (data_at sh tuint (Vint (rc_sub1 v)) r; refwarn4 gv (rc_dec_warn v w)).

(* `if (!peer)` needs a resource at offset 0 of the peer (VST: weak_valid_pointer): the device field d *)
Definition wg_peer_get_maybe_zero_spec :=
  DECLARE Sh._wg_peer_get_maybe_zero
  WITH gv: globals, S: shim, w: list int64, sh: share, p: val, r: int, d: val
  PRE [ tptr t_peer ]
    PROP (writable_share sh) PARAMS (p) GLOBALS (gv)
    SEP (shim_state4 gv S w;
         if eq_dec p nullval then emp
         else (peer_refs_rep sh p r * field_at sh t_peer [StructField I._device] d p))
  POST [ tptr t_peer ]
    PROP ()
    RETURN (if eq_dec p nullval then nullval else if Int.eq r Int.zero then nullval else p)
    SEP (shim_state4 gv S (if eq_dec p nullval then w else rc_inz_warn r w);
         if eq_dec p nullval then emp
         else (peer_refs_rep sh p (if Int.eq r Int.zero then r else rc_add1 r) *
               field_at sh t_peer [StructField I._device] d p)).

Definition wg_shim_peer_release_spec :=
  DECLARE Sh._wg_shim_peer_release
  WITH gv: globals, S: shim, w: list int64, k: val
  PRE [ tptr t_kref ]
    PROP () PARAMS (k) GLOBALS (gv) SEP (shim_state4 gv S w)
  POST [ tvoid ]
    PROP () RETURN () SEP (shim_state4 gv (shim_release S) w).

(* wg_peer_put: kref_put, one reference less (refcount_t: rc_sub1); reaching 0 is counted (peers are never freed:
   S12) *)
Definition wg_peer_put_spec :=
  DECLARE Sh._wg_peer_put
  WITH gv: globals, S: shim, w: list int64, sh: share, p: val, r: int, d: val
  PRE [ tptr t_peer ]
    PROP (writable_share sh) PARAMS (p) GLOBALS (gv)
    SEP (shim_state4 gv S w;
         if eq_dec p nullval then emp
         else (peer_refs_rep sh p r * field_at sh t_peer [StructField I._device] d p))
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (shim_state4 gv (if eq_dec p nullval then S
                        else if Int.eq (rc_sub1 r) Int.zero then shim_release S else S) (if eq_dec p nullval then w else rc_dec_warn r w);
         if eq_dec p nullval then emp
         else (peer_refs_rep sh p (rc_sub1 r) * field_at sh t_peer [StructField I._device] d p)).

(* the public-key table: the chain from its head is the peer list PS *)
Definition wg_pubkey_hashtable_lookup_spec :=
  DECLARE Sh._wg_pubkey_hashtable_lookup
  WITH gv: globals, S: shim, w: list int64, sht: share, tab: val, head: val, PS: list (val * share * peer), shk: share, pk: val,
       pub: list byte
  PRE [ tptr t_ptab, tptr tuchar ]
    PROP (readable_share sht; readable_share shk; peers_wf PS; Zlength pub = 32; pk_chain head PS;
          peers_refs_ok PS)
    PARAMS (tab; pk) GLOBALS (gv)
    SEP (ptable sht tab head; peers_rep PS; bytes_at shk pub pk; shim_state4 gv S w)
  POST [ tptr t_peer ]
    PROP () RETURN (fst (pk_lookup PS pub))
    SEP (ptable sht tab head; peers_rep (snd (pk_lookup PS pub)); bytes_at shk pub pk; shim_state4 gv S w).

(* the index table *)
(* A RAW entry: not (yet) in the table's pool, with its index never written (the harnesses' struct kentry:
   peer and type set, next = NULL, hashed = false, index uninitialized).  remove / insert accept it
   (raw = Some (sh, E)); entries of the pool: raw = None. *)
Definition raw_entry (sh: share) (e: val) (E: entry) : mpred :=
  data_at sh t_entry_s (e_peer E, (nullval, (Val.of_bool false, (Vint (e_type E), Vundef)))) e.
Definition raw_ok (T: tstate) (e: val) (raw: option (share * entry)) : Prop :=
  match raw with
  | None => In e (saddrs (t_D T))
  | Some (sh, _) => writable_share sh /\ ~ In e (saddrs (t_D T))
  end.
Definition raw_rep (e: val) (raw: option (share * entry)) : mpred :=
  match raw with None => emp | Some (sh, E) => raw_entry sh e E end.
(* the table with a raw entry added to its pool (insert puts it there) *)
Definition raw_add (T: tstate) (e: val) (raw: option (share * entry)) : tstate :=
  match raw with None => T | Some (sh, E) => t_add T e sh E end.

Definition wg_index_hashtable_remove_spec :=
  DECLARE Sh._wg_index_hashtable_remove
  WITH sht: share, tab: val, T: tstate, e: val, raw: option (share * entry)
  PRE [ tptr t_itab, tptr t_entry_s ]
    PROP (writable_share sht; raw_ok T e raw) PARAMS (tab; e)
    SEP (itable sht tab T; raw_rep e raw)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (itable sht tab (match raw with None => t_remove T e | Some _ => T end); raw_rep e raw).

Definition wg_shim_index_in_use_spec :=
  DECLARE Sh._wg_shim_index_in_use
  WITH sht: share, tab: val, T: tstate, idx: int
  PRE [ tptr t_itab, tuint ]
    PROP (readable_share sht) PARAMS (tab; Vint idx)
    SEP (itable sht tab T)
  POST [ tbool ]
    PROP () RETURN (Val.of_bool (int_inb idx (t_indices T (t_L T))))
    SEP (itable sht tab T).

(* insert: the entry (of the pool, or a raw entry that joins it) goes to the head with a fresh random index;
   the last draw is logged *)
Definition wg_index_hashtable_insert_spec :=
  DECLARE Sh._wg_index_hashtable_insert
  WITH gv: globals, S: shim, w: list int64, sht: share, tab: val, T: tstate, e: val, raw: option (share * entry)
  PRE [ tptr t_itab, tptr t_entry_s ]
    PROP (writable_share sht; raw_ok T e raw) PARAMS (tab; e) GLOBALS (gv)
    SEP (itable sht tab T; raw_rep e raw; shim_state4 gv S w)
  POST [ tuint ] EX idx: int,
    PROP (t_fresh (raw_add T e raw) e idx) RETURN (Vint idx)
    SEP (itable sht tab (t_insert (raw_add T e raw) e idx); shim_state4 gv (shim_u32 S idx) w).

Definition wg_index_hashtable_replace_spec :=
  DECLARE Sh._wg_index_hashtable_replace
  WITH sht: share, tab: val, T: tstate, old: val, new: val
  PRE [ tptr t_itab, tptr t_entry_s, tptr t_entry_s ]
    PROP (writable_share sht; In old (saddrs (t_D T)); In new (saddrs (t_D T)); old <> new;
          ~ In new (t_L T))
    PARAMS (tab; old; new)
    SEP (itable sht tab T)
  POST [ tbool ]
    PROP () RETURN (Val.of_bool (fst (t_replace T old new)))
    SEP (itable sht tab (snd (t_replace T old new))).

(* lookup(mask, idx, &peer): every pool entry's peer is one of PS with a reference (pool_peers_ok) *)
Definition wg_index_hashtable_lookup_spec :=
  DECLARE Sh._wg_index_hashtable_lookup
  WITH gv: globals, S: shim, w: list int64, sht: share, tab: val, T: tstate, PS: list (val * share * peer), mask: int, idx: int,
       shq: share, q: val, oldq: val
  PRE [ tptr t_itab, tint, tuint, tptr (tptr t_peer) ]
    PROP (readable_share sht; writable_share shq; pool_peers_ok T PS; peers_wf PS; peers_refs_ok PS)
    PARAMS (tab; Vint mask; Vint idx; q) GLOBALS (gv)
    SEP (itable sht tab T; peers_rep PS; data_at shq (tptr t_peer) oldq q; shim_state4 gv S w)
  POST [ tptr t_entry_s ]
    PROP ()
    RETURN (match t_lookup T mask idx with Some (a, _) => a | None => nullval end)
    SEP (itable sht tab T;
         peers_rep (match t_lookup T mask idx with Some (_, E) => peers_ref PS (e_peer E) | None => PS end);
         data_at shq (tptr t_peer) (match t_lookup T mask idx with Some (_, E) => e_peer E | None => oldq end) q;
         shim_state4 gv S w).

Definition wg_ratelimiter_allow_spec :=
  DECLARE Sh._wg_ratelimiter_allow
  WITH gv: globals, S: shim, w: list int64, s: val, n: val
  PRE [ tptr t_skb, tptr (Tstruct Sh._net noattr) ]
    PROP () PARAMS (s; n) GLOBALS (gv) SEP (shim_state4 gv S w)
  POST [ tbool ]
    PROP () RETURN (Val.of_bool (s_rlallow S)) SEP (shim_state4 gv S w).

Definition wg_birthdate_has_expired_spec :=
  DECLARE Sh._wg_birthdate_has_expired
  WITH gv: globals, S: shim, w: list int64, b: int64, e: int64
  PRE [ tulong, tulong ]
    PROP () PARAMS (Vlong b; Vlong e) GLOBALS (gv) SEP (shim_state4 gv S w)
  POST [ tbool ]
    PROP () RETURN (Val.of_bool (birthdate_expired b e (s_boot S))) SEP (shim_state4 gv S w).

(* ================================================================================================ *)
(* noise.c: small functions and static inlines                                                      *)
(* ================================================================================================ *)

Definition quickproof_rounddown_pow_of_two_spec :=
  DECLARE N._quickproof_rounddown_pow_of_two
  WITH n: Z
  PRE [ tulong ]
    PROP (1 <= n <= Int64.max_unsigned) PARAMS (Vlong (Int64.repr n)) SEP ()
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (2 ^ Z.log2 n))) SEP ().

Definition put_unaligned_be32_spec :=
  DECLARE N._put_unaligned_be32
  WITH v: int, sh: share, p: val
  PRE [ tuint, tptr tvoid ]
    PROP (writable_share sh) PARAMS (Vint v; p)
    SEP (data_at_ sh (tarray tuchar 4) p)
  POST [ tvoid ]
    PROP () RETURN () SEP (bytes_at sh (be32 v) p).

Definition put_unaligned_be64_spec :=
  DECLARE N._put_unaligned_be64
  WITH v: int64, sh: share, p: val
  PRE [ tulong, tptr tvoid ]
    PROP (writable_share sh) PARAMS (Vlong v; p)
    SEP (data_at_ sh (tarray tuchar 8) p)
  POST [ tvoid ]
    PROP () RETURN () SEP (bytes_at sh (be64 v) p).

(* curve25519_generate_secret (curve25519.h): 32 random bytes, clamped *)
Definition curve25519_generate_secret_spec :=
  DECLARE N._curve25519_generate_secret
  WITH gv: globals, S: shim, w: list int64, sh: share, p: val
  PRE [ tptr tuchar ]
    PROP (writable_share sh) PARAMS (p) GLOBALS (gv)
    SEP (shim_state4 gv S w; data_at_ sh (tarray tuchar 32) p)
  POST [ tvoid ] EX r: list byte,
    PROP (Zlength r = 32) RETURN ()
    SEP (shim_state4 gv (shim_draw S r) w; bytes_at sh (clamp r) p).

Definition wg_noise_reset_last_sent_handshake_spec :=
  DECLARE N._wg_noise_reset_last_sent_handshake
  WITH gv: globals, S: shim, w: list int64, sh: share, p: val
  PRE [ tptr t_atomic64 ]
    PROP (writable_share sh) PARAMS (p) GLOBALS (gv)
    SEP (shim_state4 gv S w; data_at_ sh t_atomic64 p)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (shim_state4 gv S w; data_at sh t_atomic64 (Vlong (reset_lsh (s_boot S))) p).

(* ================================================================================================ *)
(* noise.c: the symmetric primitives of the handshake                                               *)
(* ================================================================================================ *)

Definition wg_noise_init_spec :=
  DECLARE N._wg_noise_init
  WITH gv: globals, h: list byte, ck: list byte, kc: int64
  PRE [ ]
    PROP () PARAMS () GLOBALS (gv)
    SEP (noise_globals_raw gv h ck kc; wg_consts gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (noise_globals gv kc; wg_consts gv).

(* hmac(out, in, key, inlen, keylen) (static, called by kdf).  alias = false: out is a separate 32-byte
   buffer and in holds data (NULL allowed when empty).  alias = true: out = in, a buffer of n >= 32 bytes
   buf whose first inlen bytes are the data; the first 32 bytes are overwritten. *)
Definition hmac_spec :=
  DECLARE N._hmac
  WITH gv: globals, alias: bool, osh: share, out: val, ish: share, inp: val, buf: list val,
       data: list byte, ksh: share, kp: val, key: list byte
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tulong, tulong ]
    PROP (writable_share osh; readable_share ish; readable_share ksh;
          Zlength data <= Int64.max_signed; Zlength key <= Int64.max_signed;
          alias = true -> (out = inp /\ 32 <= Zlength buf /\ Zlength data <= Zlength buf /\
                           sublist 0 (Zlength data) buf = bytes data))
    PARAMS (out; inp; kp; Vlong (Int64.repr (Zlength data)); Vlong (Int64.repr (Zlength key))) GLOBALS (gv)
    SEP (if alias then data_at osh (tarray tuchar (Zlength buf)) buf out
         else (data_at_ osh (tarray tuchar 32) out * b2s_bytes ish data inp);
         bytes_at ksh key kp; wg_consts gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (if alias then data_at osh (tarray tuchar (Zlength buf)) (bytes (hmac key data) ++ sublist 32 (Zlength buf) buf) out
         else (bytes_at osh (hmac key data) out * b2s_bytes ish data inp);
         bytes_at ksh key kp; wg_consts gv).

(* kdf(d1, d2, d3, data, 32, l2, l3, |data|, ck): d1 always written (alias: d1 = ck, the chaining key
   buffer itself); d2 if not NULL; d3 if d2 and d3 are not NULL.  Non-NULL outputs are 32 bytes. *)
Definition kdf_spec :=
  DECLARE N._kdf
  WITH gv: globals, alias: bool, d1: val, d2: val, d3: val, l2: Z, l3: Z, sh1: share, sh2: share,
       sh3: share, shd: share, dp: val, data: list byte, shc: share, ckp: val, ck: list byte
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar, tulong, tulong, tulong, tulong, tptr tuchar ]
    PROP (writable_share sh1; writable_share sh2; writable_share sh3; readable_share shd;
          if alias then writable_share shc else readable_share shc;
          Zlength ck = 32; Zlength data <= Int64.max_signed;
          0 <= l2 <= Int64.max_unsigned; 0 <= l3 <= Int64.max_unsigned;
          d2 <> nullval -> l2 = 32; d3 <> nullval -> l3 = 32; alias = true -> d1 = ckp)
    PARAMS (d1; d2; d3; dp; Vlong (Int64.repr 32); Vlong (Int64.repr l2); Vlong (Int64.repr l3);
            Vlong (Int64.repr (Zlength data)); ckp) GLOBALS (gv)
    SEP (if alias then bytes_at shc ck ckp
         else (bytes_at shc ck ckp * data_at_ sh1 (tarray tuchar 32) d1);
         if eq_dec d2 nullval then emp else data_at_ sh2 (tarray tuchar 32) d2;
         if eq_dec d2 nullval then emp else if eq_dec d3 nullval then emp
         else data_at_ sh3 (tarray tuchar 32) d3;
         b2s_bytes shd data dp; wg_consts gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (if alias then bytes_at shc (kdf1 ck data) ckp
         else (bytes_at shc ck ckp * bytes_at sh1 (kdf1 ck data) d1);
         if eq_dec d2 nullval then emp else bytes_at sh2 (kdf2 ck data) d2;
         if eq_dec d2 nullval then emp else if eq_dec d3 nullval then emp
         else bytes_at sh3 (kdf3 ck data) d3;
         b2s_bytes shd data dp; wg_consts gv).

(* derive_keys(first, second, ck): (T1, T2) = KDF2(ck, empty), born now, valid *)
Definition derive_keys_spec :=
  DECLARE N._derive_keys
  WITH gv: globals, S: shim, w: list int64, sh1: share, f: val, sh2: share, s: val, shc: share, ckp: val, ck: list byte
  PRE [ tptr t_sym, tptr t_sym, tptr tuchar ]
    PROP (writable_share sh1; writable_share sh2; readable_share shc; Zlength ck = 32)
    PARAMS (f; s; ckp) GLOBALS (gv)
    SEP (data_at_ sh1 t_sym f; data_at_ sh2 t_sym s; bytes_at shc ck ckp; shim_state4 gv S w; wg_consts gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (symkey_rep sh1 f (mkSym (kdf1 ck []) (s_boot S) true);
         symkey_rep sh2 s (mkSym (kdf2 ck []) (s_boot S) true);
         bytes_at shc ck ckp; shim_state4 gv S w; wg_consts gv).

(* mix_dh(ck, key, priv, pub): false and nothing written if DH(priv, pub) is zero; else
   (ck, key) = KDF2(ck, DH) (key may be NULL) *)
Definition mix_dh_spec :=
  DECLARE N._mix_dh
  WITH gv: globals, shc: share, ckp: val, ck: list byte, shk: share, kp: val, shv: share, pv: val,
       priv: list byte, shb: share, pb: val, pub: list byte
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share shc; writable_share shk; readable_share shv; readable_share shb;
          Zlength ck = 32; Zlength priv = 32; Zlength pub = 32)
    PARAMS (ckp; kp; pv; pb) GLOBALS (gv)
    SEP (bytes_at shc ck ckp; if eq_dec kp nullval then emp else data_at_ shk (tarray tuchar 32) kp;
         bytes_at shv priv pv; bytes_at shb pub pb; wg_consts gv)
  POST [ tbool ]
    PROP () RETURN (Val.of_bool (dh_ok x25519 priv pub))
    SEP (bytes_at shc (if dh_ok x25519 priv pub then kdf1 ck (x25519 priv pub) else ck) ckp;
         if eq_dec kp nullval then emp
         else if dh_ok x25519 priv pub then bytes_at shk (kdf2 ck (x25519 priv pub)) kp
         else data_at_ shk (tarray tuchar 32) kp;
         bytes_at shv priv pv; bytes_at shb pub pb; wg_consts gv).

(* mix_precomputed_dh(ck, key, pre): false if pre is zero, else (ck, key) = KDF2(ck, pre) *)
Definition mix_precomputed_dh_spec :=
  DECLARE N._mix_precomputed_dh
  WITH gv: globals, kc: int64, shc: share, ckp: val, ck: list byte, shk: share, kp: val, shp: share,
       pp: val, pre: list byte
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share shc; writable_share shk; readable_share shp; Zlength ck = 32; Zlength pre = 32)
    PARAMS (ckp; kp; pp) GLOBALS (gv)
    SEP (bytes_at shc ck ckp; data_at_ shk (tarray tuchar 32) kp; bytes_at shp pre pp;
         noise_globals gv kc; wg_consts gv)
  POST [ tbool ]
    PROP () RETURN (Val.of_bool (memneq_bool pre zeros32))
    SEP (bytes_at shc (if memneq_bool pre zeros32 then kdf1 ck pre else ck) ckp;
         if memneq_bool pre zeros32 then bytes_at shk (kdf2 ck pre) kp else data_at_ shk (tarray tuchar 32) kp;
         bytes_at shp pre pp; noise_globals gv kc; wg_consts gv).

Definition mix_hash_spec :=
  DECLARE N._mix_hash
  WITH gv: globals, shh: share, hp: val, h: list byte, shs: share, sp: val, src: list byte
  PRE [ tptr tuchar, tptr tuchar, tulong ]
    PROP (writable_share shh; readable_share shs; Zlength h = 32; Zlength src <= Int64.max_signed)
    PARAMS (hp; sp; Vlong (Int64.repr (Zlength src))) GLOBALS (gv)
    SEP (bytes_at shh h hp; b2s_bytes shs src sp; wg_consts gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (bytes_at shh (mix_hash h src) hp; b2s_bytes shs src sp; wg_consts gv).

(* mix_psk(ck, hash, key, psk): (ck, tau, key) = KDF3(ck, psk); hash = HASH(hash || tau) *)
Definition mix_psk_spec :=
  DECLARE N._mix_psk
  WITH gv: globals, shc: share, ckp: val, ck: list byte, shh: share, hp: val, h: list byte,
       shk: share, kp: val, shp: share, pp: val, psk: list byte
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share shc; writable_share shh; writable_share shk; readable_share shp;
          Zlength ck = 32; Zlength h = 32; Zlength psk = 32)
    PARAMS (ckp; hp; kp; pp) GLOBALS (gv)
    SEP (bytes_at shc ck ckp; bytes_at shh h hp; data_at_ shk (tarray tuchar 32) kp; bytes_at shp psk pp;
         wg_consts gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (bytes_at shc (kdf1 ck psk) ckp; bytes_at shh (mix_hash h (kdf2 ck psk)) hp;
         bytes_at shk (kdf3 ck psk) kp; bytes_at shp psk pp; wg_consts gv).

Definition handshake_init_spec :=
  DECLARE N._handshake_init
  WITH gv: globals, kc: int64, shc: share, ckp: val, shh: share, hp: val, shr: share, rp: val,
       rs: list byte
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share shc; writable_share shh; readable_share shr; Zlength rs = 32)
    PARAMS (ckp; hp; rp) GLOBALS (gv)
    SEP (data_at_ shc (tarray tuchar 32) ckp; data_at_ shh (tarray tuchar 32) hp; bytes_at shr rs rp;
         noise_globals gv kc; wg_consts gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (bytes_at shc init_ck ckp; bytes_at shh (mix_hash init_hash rs) hp; bytes_at shr rs rp;
         noise_globals gv kc; wg_consts gv).

(* message_encrypt(dst, src, |m|, key, hash): dst = AEAD(key, 0, m, hash); hash = HASH(hash || dst) *)
Definition message_encrypt_spec :=
  DECLARE N._message_encrypt
  WITH gv: globals, shd: share, dp: val, shs: share, sp: val, m: list byte, shk: share, kp: val,
       key: list byte, shh: share, hp: val, h: list byte
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tptr tuchar ]
    PROP (writable_share shd; readable_share shs; readable_share shk; writable_share shh;
          Zlength m <= Int.max_unsigned - 16; Zlength key = 32; Zlength h = 32)
    PARAMS (dp; sp; Vlong (Int64.repr (Zlength m)); kp; hp) GLOBALS (gv)
    SEP (data_at_ shd (tarray tuchar (Zlength m + 16)) dp; prim_bytes shs m sp; bytes_at shk key kp;
         bytes_at shh h hp; wg_consts gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at shd (tarray tuchar (Zlength m + 16)) (bytes (aead_enc key 0 h m)) dp;
         prim_bytes shs m sp; bytes_at shk key kp;
         bytes_at shh (mix_hash h (aead_enc key 0 h m)) hp; wg_consts gv).

(* message_decrypt(dst, src, |c|, key, hash): true, dst = plaintext, hash = HASH(hash || c) if the tag
   verifies; else false and nothing written.  dst has max(|c| - 16, 0) bytes (NULL allowed when 0). *)
Definition message_decrypt_spec :=
  DECLARE N._message_decrypt
  WITH gv: globals, shd: share, dp: val, old: list val, shs: share, sp: val, c: list byte, shk: share,
       kp: val, key: list byte, shh: share, hp: val, h: list byte
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tptr tuchar ]
    PROP (writable_share shd; readable_share shs; readable_share shk; writable_share shh;
          Zlength c <= Int.max_unsigned; Zlength key = 32; Zlength h = 32;
          Zlength old = Z.max 0 (Zlength c - 16))
    PARAMS (dp; sp; Vlong (Int64.repr (Zlength c)); kp; hp) GLOBALS (gv)
    SEP (out_bytes shd old dp; prim_bytes shs c sp; bytes_at shk key kp; bytes_at shh h hp; wg_consts gv)
  POST [ tbool ]
    PROP ()
    RETURN (Val.of_bool (match aead_dec key 0 h c with Some _ => true | None => false end))
    SEP (out_bytes shd (match aead_dec key 0 h c with Some pt => bytes pt | None => old end) dp;
         prim_bytes shs c sp; bytes_at shk key kp;
         bytes_at shh (match aead_dec key 0 h c with Some _ => mix_hash h c | None => h end) hp;
         wg_consts gv).

(* message_ephemeral(dst, src, ck, hash): dst = src (alias: the same buffer); hash = HASH(hash || src);
   ck = KDF1(ck, src) *)
Definition message_ephemeral_spec :=
  DECLARE N._message_ephemeral
  WITH gv: globals, alias: bool, shd: share, dp: val, shs: share, sp: val, e: list byte, shc: share,
       ckp: val, ck: list byte, shh: share, hp: val, h: list byte
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share shd; readable_share shs; writable_share shc; writable_share shh;
          Zlength e = 32; Zlength ck = 32; Zlength h = 32; alias = true -> dp = sp)
    PARAMS (dp; sp; ckp; hp) GLOBALS (gv)
    SEP (if alias then bytes_at shs e sp else (data_at_ shd (tarray tuchar 32) dp * bytes_at shs e sp);
         bytes_at shc ck ckp; bytes_at shh h hp; wg_consts gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (if alias then bytes_at shs e sp else (bytes_at shd e dp * bytes_at shs e sp);
         bytes_at shc (kdf1 ck e) ckp; bytes_at shh (mix_hash h e) hp; wg_consts gv).

Definition tai64n_now_spec :=
  DECLARE N._tai64n_now
  WITH gv: globals, S: shim, w: list int64, sh: share, p: val
  PRE [ tptr tuchar ]
    PROP (writable_share sh) PARAMS (p) GLOBALS (gv)
    SEP (shim_state4 gv S w; data_at_ sh (tarray tuchar 12) p)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (shim_state4 gv S w; bytes_at sh (tai64n (s_rsec S) (s_rnsec S)) p).

(* ================================================================================================ *)
(* noise.c: identities, handshakes, keypairs                                                        *)
(* ================================================================================================ *)

Definition wg_noise_set_static_identity_private_key_spec :=
  DECLARE N._wg_noise_set_static_identity_private_key
  WITH gv: globals, sh: share, sid: val, ID: identity, shk: share, pk: val, raw: list byte
  PRE [ tptr t_sid, tptr tuchar ]
    PROP (writable_share sh; readable_share shk; Zlength raw = 32) PARAMS (sid; pk) GLOBALS (gv)
    SEP (identity_rep sh sid ID; bytes_at shk raw pk; wg_consts gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (identity_rep sh sid (identity_of x25519 ID raw); bytes_at shk raw pk; wg_consts gv).

(* wg_noise_precompute_static_static(peer): the handshake's precomputed DH from the identity at its
   static_identity pointer *)
Definition wg_noise_precompute_static_static_spec :=
  DECLARE N._wg_noise_precompute_static_static
  WITH gv: globals, sh: share, p: val, H: handshake, shi: share, ID: identity
  PRE [ tptr t_peer ]
    PROP (writable_share sh; readable_share shi; field_compatible t_peer [] p) PARAMS (p) GLOBALS (gv)
    SEP (hs_rep sh (hs_addr p) H; identity_rep shi (hs_sid H) ID; wg_consts gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (hs_rep sh (hs_addr p) (hs_set_ss H (precomputed x25519 ID (hs_rstatic H)));
         identity_rep shi (hs_sid H) ID; wg_consts gv).

(* wg_noise_handshake_init(&peer->handshake, sid, pub, psk or NULL, peer): the whole handshake memory
   (any contents, its entry included) becomes the zeroed handshake and an unhashed entry of the peer
   (to be added to the device's pool) *)
Definition hs_initial (ID: identity) (sid: val) (pub psk: list byte) : handshake :=
  mkHS HS_ZEROED Int64.zero sid zeros32 pub zeros32 (precomputed x25519 ID pub) psk zeros32 zeros32
       (zeros 12) Int.zero.

Definition wg_noise_handshake_init_spec :=
  DECLARE N._wg_noise_handshake_init
  WITH gv: globals, sh: share, p: val, shi: share, sid: val, ID: identity, shk: share, pubp: val,
       pub: list byte, shq: share, pskp: val, psk: list byte
  PRE [ tptr t_hs, tptr t_sid, tptr tuchar, tptr tuchar, tptr t_peer ]
    PROP (writable_share sh; readable_share shi; readable_share shk; readable_share shq;
          field_compatible t_peer [] p; Zlength pub = 32; pskp <> nullval -> Zlength psk = 32)
    PARAMS (hs_addr p; sid; pubp; pskp; p) GLOBALS (gv)
    SEP (data_at_ sh t_hs (hs_addr p); identity_rep shi sid ID; bytes_at shk pub pubp;
         if eq_dec pskp nullval then emp else bytes_at shq psk pskp; wg_consts gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (hs_rep sh (hs_addr p) (hs_initial ID sid pub (if eq_dec pskp nullval then zeros32 else psk));
         entry_out sh (hs_addr p) (mkEntry p IDX_HANDSHAKE Int.zero);
         identity_rep shi sid ID; bytes_at shk pub pubp;
         if eq_dec pskp nullval then emp else bytes_at shq psk pskp; wg_consts gv).

Definition handshake_zero_spec :=
  DECLARE N._handshake_zero
  WITH sh: share, h: val, H: handshake
  PRE [ tptr t_hs ]
    PROP (writable_share sh) PARAMS (h)
    SEP (hs_rep sh h H)
  POST [ tvoid ]
    PROP () RETURN () SEP (hs_rep sh h (hs_zero H)).

(* wg_noise_handshake_clear(&peer->handshake): unhashed and zeroed *)
Definition wg_noise_handshake_clear_spec :=
  DECLARE N._wg_noise_handshake_clear
  WITH shp: share, p: val, P: peer, shd: share, wg: val, D: device, sht: share, T: tstate
  PRE [ tptr t_hs ]
    PROP (writable_share shp; readable_share shd; writable_share sht; p_device P = wg; hs_in_pool T p)
    PARAMS (hs_addr p)
    SEP (peer_rep shp p P; device_rep shd wg D; itable sht (d_itab D) T)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (peer_rep shp p (p_set_hs P (hs_zero (p_hs P))); device_rep shd wg D;
         itable sht (d_itab D) (t_remove T (hs_addr p))).

(* keypair_create(peer) (v4: atomic64_inc_return wraps, kc any): NULL, or a fresh keypair with the next internal id and its unhashed entry *)
Definition keypair_create_spec :=
  DECLARE N._keypair_create
  WITH gv: globals, S: shim, w: list int64, kc: int64, pv: val
  PRE [ tptr t_peer ]
    PROP () PARAMS (pv) GLOBALS (gv)
    SEP (mem_mgr gv; shim_state4 gv S w; noise_globals gv kc)
  POST [ tptr t_kp ] EX k: val,
    PROP (s_failnext S = true -> k = nullval) RETURN (k)
    SEP (mem_mgr gv;
         if eq_dec k nullval then (shim_state4 gv (shim_alloc_fail S) w * noise_globals gv kc)
         else (shim_state4 gv (shim_alloc_ok S) w * noise_globals gv (Int64.add kc Int64.one) *
               keypair_rep CSw k (kp_fresh (Int64.add kc Int64.one)) *
               entry_out Ews k (mkEntry pv IDX_KEYPAIR Int.zero))).

(* keypair_free_rcu(&k->rcu): the whole keypair memory is freed *)
Definition keypair_free_rcu_spec :=
  DECLARE N._keypair_free_rcu
  WITH gv: globals, S: shim, w: list int64, k: val
  PRE [ tptr t_rcu ]
    PROP () PARAMS (offset_val OFS_KP_RCU k) GLOBALS (gv)
    SEP (mem_mgr gv; shim_state4 gv S w;
         @malloc_token CSw Ews (tarray tuchar SIZEOF_KEYPAIR) k; data_at_ Ews (tarray tuchar SIZEOF_KEYPAIR) k)
  POST [ tvoid ]
    PROP () RETURN () SEP (mem_mgr gv; shim_state4 gv (shim_free S) w).

(* keypair_free_kref(&k->refcount): unhashed, out of the pool, freed *)
Definition keypair_free_kref_spec :=
  DECLARE N._keypair_free_kref
  WITH gv: globals, S: shim, w: list int64, k: val, K: keypair, E: entry, shp: share, p: val, P: peer, shd: share,
       wg: val, D: device, sht: share, T: tstate
  PRE [ tptr t_kref ]
    PROP (readable_share shp; readable_share shd; writable_share sht; p_device P = wg;
          sfind (t_D T) k = Some (Ews, E); e_peer E = p)
    PARAMS (offset_val OFS_KP_REFCOUNT k) GLOBALS (gv)
    SEP (mem_mgr gv; shim_state4 gv S w; keypair_rep CSw k K; peer_rep shp p P; device_rep shd wg D;
         itable sht (d_itab D) T)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (mem_mgr gv; shim_state4 gv (shim_free S) w; peer_rep shp p P; device_rep shd wg D;
         itable sht (d_itab D) (t_free T k)).

(* The keypair operations act on the keypair world of ONE peer p (its live keypairs KS, all with their
   entry in the pool of p's device table T and e_peer = p). *)
Definition wg_noise_keypair_put_spec :=
  DECLARE N._wg_noise_keypair_put
  WITH gv: globals, S: shim, w: list int64, KS: list (val * keypair), T: tstate, k: val, unref: bool, shp: share,
       p: val, P: peer, shd: share, wg: val, D: device, sht: share
  PRE [ tptr t_kp, tbool ]
    PROP (readable_share shp; readable_share shd; writable_share sht; p_device P = wg;
          kps_in_pool T p KS; k = nullval \/ In k (map fst KS))
    PARAMS (k; Val.of_bool unref) GLOBALS (gv)
    SEP (mem_mgr gv; shim_state4 gv S w; keypairs_rep CSw KS; peer_rep shp p P; device_rep shd wg D;
         itable sht (d_itab D) T)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (mem_mgr gv; shim_state4 gv (kw_S (kp_put k unref (mkKW KS T S))) (kp_put_warn k KS w);
         keypairs_rep CSw (kw_KS (kp_put k unref (mkKW KS T S)));
         peer_rep shp p P; device_rep shd wg D; itable sht (d_itab D) (kw_T (kp_put k unref (mkKW KS T S)))).

(* `if (!keypair)` needs a resource at offset 0 of the keypair: its entry, in the pool of the table T *)
Definition wg_noise_keypair_get_spec :=
  DECLARE N._wg_noise_keypair_get
  WITH gv: globals, S: shim, w: list int64, KS: list (val * keypair), k: val, sht: share, tab: val, T: tstate, p: val
  PRE [ tptr t_kp ]
    PROP (k = nullval \/ In k (map fst KS); readable_share sht; kps_in_pool T p KS) PARAMS (k) GLOBALS (gv)
    SEP (keypairs_rep CSw KS; itable sht tab T; shim_state4 gv S w)
  POST [ tptr t_kp ]
    PROP () RETURN (fst (kp_get k KS))
    SEP (keypairs_rep CSw (snd (kp_get k KS)); itable sht tab T; shim_state4 gv S (kp_get_warn k KS w)).

Definition wg_noise_keypairs_clear_spec :=
  DECLARE N._wg_noise_keypairs_clear
  WITH gv: globals, S: shim, w: list int64, KS: list (val * keypair), T: tstate, shp: share, p: val, P: peer,
       shd: share, wg: val, D: device, sht: share
  PRE [ tptr t_kps ]
    PROP (writable_share shp; readable_share shd; writable_share sht; p_device P = wg;
          kps_in_pool T p KS; slots_ok P KS)
    PARAMS (kps_addr p) GLOBALS (gv)
    SEP (mem_mgr gv; shim_state4 gv S w; keypairs_rep CSw KS; peer_rep shp p P; device_rep shd wg D;
         itable sht (d_itab D) T)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (mem_mgr gv; shim_state4 gv (kw_S (snd (keypairs_clear_model P (mkKW KS T S)))) (keypairs_clear_warn P (mkKW KS T S) w);
         keypairs_rep CSw (kw_KS (snd (keypairs_clear_model P (mkKW KS T S))));
         peer_rep shp p (fst (keypairs_clear_model P (mkKW KS T S))); device_rep shd wg D;
         itable sht (d_itab D) (kw_T (snd (keypairs_clear_model P (mkKW KS T S))))).

Definition wg_noise_expire_current_peer_keypairs_spec :=
  DECLARE N._wg_noise_expire_current_peer_keypairs
  WITH gv: globals, S: shim, w: list int64, KS: list (val * keypair), T: tstate, shp: share, p: val, P: peer,
       shd: share, wg: val, D: device, sht: share
  PRE [ tptr t_peer ]
    PROP (writable_share shp; readable_share shd; writable_share sht; p_device P = wg;
          hs_in_pool T p; kps_in_pool T p KS; slots_ok P KS)
    PARAMS (p) GLOBALS (gv)
    SEP (shim_state4 gv S w; keypairs_rep CSw KS; peer_rep shp p P; device_rep shd wg D;
         itable sht (d_itab D) T)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (shim_state4 gv S w;
         keypairs_rep CSw (snd (fst (expire_model P (hs_addr p) KS T (s_boot S))));
         peer_rep shp p (fst (fst (expire_model P (hs_addr p) KS T (s_boot S))));
         device_rep shd wg D;
         itable sht (d_itab D) (snd (expire_model P (hs_addr p) KS T (s_boot S)))).

(* add_new_keypair(&p->keypairs, new): new is a live keypair of KS not in any slot *)
Definition add_new_keypair_spec :=
  DECLARE N._add_new_keypair
  WITH gv: globals, S: shim, w: list int64, KS: list (val * keypair), T: tstate, shp: share, p: val, P: peer,
       shd: share, wg: val, D: device, sht: share, new: val, K: keypair
  PRE [ tptr t_kps, tptr t_kp ]
    PROP (writable_share shp; readable_share shd; writable_share sht; p_device P = wg;
          kps_in_pool T p KS; slots_ok P KS; afind KS new = Some K;
          new <> p_cur P; new <> p_prev P; new <> p_next P)
    PARAMS (kps_addr p; new) GLOBALS (gv)
    SEP (mem_mgr gv; shim_state4 gv S w; keypairs_rep CSw KS; peer_rep shp p P; device_rep shd wg D;
         itable sht (d_itab D) T)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (mem_mgr gv; shim_state4 gv (kw_S (snd (add_new_keypair_model P new (kp_init K) (mkKW KS T S)))) (add_new_keypair_warn P new (kp_init K) (mkKW KS T S) w);
         keypairs_rep CSw (kw_KS (snd (add_new_keypair_model P new (kp_init K) (mkKW KS T S))));
         peer_rep shp p (fst (add_new_keypair_model P new (kp_init K) (mkKW KS T S)));
         device_rep shd wg D;
         itable sht (d_itab D) (kw_T (snd (add_new_keypair_model P new (kp_init K) (mkKW KS T S))))).

(* wg_noise_received_with_keypair(&p->keypairs, k): k NULL or any keypair with its entry in the pool (v4) *)
Definition wg_noise_received_with_keypair_spec :=
  DECLARE N._wg_noise_received_with_keypair
  WITH gv: globals, S: shim, w: list int64, KS: list (val * keypair), T: tstate, shp: share, p: val, P: peer,
       shd: share, wg: val, D: device, sht: share, k: val
  PRE [ tptr t_kps, tptr t_kp ]
    PROP (writable_share shp; readable_share shd; writable_share sht; p_device P = wg;
          kps_in_pool T p KS; slots_ok P KS; k = nullval \/ In k (saddrs (t_D T)))
    PARAMS (kps_addr p; k) GLOBALS (gv)
    SEP (mem_mgr gv; shim_state4 gv S w; keypairs_rep CSw KS; peer_rep shp p P; device_rep shd wg D;
         itable sht (d_itab D) T)
  POST [ tbool ]
    PROP ()
    RETURN (Val.of_bool (fst (fst (received_with_keypair_model P k (mkKW KS T S)))))
    SEP (mem_mgr gv; shim_state4 gv (kw_S (snd (received_with_keypair_model P k (mkKW KS T S)))) (received_with_keypair_warn P k (mkKW KS T S) w);
         keypairs_rep CSw (kw_KS (snd (received_with_keypair_model P k (mkKW KS T S))));
         peer_rep shp p (snd (fst (received_with_keypair_model P k (mkKW KS T S))));
         device_rep shd wg D;
         itable sht (d_itab D) (kw_T (snd (received_with_keypair_model P k (mkKW KS T S))))).

(* ================================================================================================ *)
(* noise.c: the handshake messages                                                                  *)
(* ================================================================================================ *)

(* create_initiation(m, &p->handshake): p's handshake points to its device's identity; r = the ephemeral
   random bytes, idx = the table's random index (fresh) *)
Definition ci_res (D: device) (P: peer) (M: init_msg) (S: shim) (r: list byte) (idx: int)
  : bool * init_msg * handshake :=
  create_initiation_model x25519 aead_enc (d_id D) (p_hs P) M r (tai64n (s_rsec S) (s_rnsec S)) idx.

Definition wg_noise_handshake_create_initiation_spec :=
  DECLARE N._wg_noise_handshake_create_initiation
  WITH gv: globals, S: shim, w: list int64, kc: int64, shm: share, m: val, M: init_msg, shp: share, p: val, P: peer,
       shd: share, wg: val, D: device, sht: share, T: tstate
  PRE [ tptr t_init, tptr t_hs ]
    PROP (writable_share shm; writable_share shp; readable_share shd; writable_share sht;
          p_device P = wg; hs_sid (p_hs P) = id_addr wg; hs_in_pool T p)
    PARAMS (m; hs_addr p) GLOBALS (gv)
    SEP (init_rep shm m M; peer_rep shp p P; device_rep shd wg D; itable sht (d_itab D) T;
         shim_state4 gv S w; noise_globals gv kc; wg_consts gv)
  POST [ tbool ] EX r: list byte, EX idx: int,
    PROP (Zlength r = 32; fst (fst (ci_res D P M S r idx)) = true -> t_fresh T (hs_addr p) idx)
    RETURN (Val.of_bool (fst (fst (ci_res D P M S r idx))))
    SEP (init_rep shm m (snd (fst (ci_res D P M S r idx)));
         peer_rep shp p (p_set_hs P (snd (ci_res D P M S r idx)));
         device_rep shd wg D;
         itable sht (d_itab D) (if fst (fst (ci_res D P M S r idx)) then t_insert T (hs_addr p) idx else T);
         shim_state4 gv (if id_has (d_id D)
                        then (if fst (fst (ci_res D P M S r idx)) then shim_u32 (shim_draw S r) idx
                              else shim_draw S r)
                        else S) w;
         noise_globals gv kc; wg_consts gv).

(* consume_initiation(m, wg): PS = the peers of wg's public-key table, in chain order *)
Definition cin_res (D: device) (PS: list (val * share * peer)) (M: init_msg) (S: shim) : option (val * peer) :=
  consume_initiation_model x25519 aead_dec (d_id D) PS M (s_boot S).

Definition wg_noise_handshake_consume_initiation_spec :=
  DECLARE N._wg_noise_handshake_consume_initiation
  WITH gv: globals, S: shim, w: list int64, kc: int64, shm: share, m: val, M: init_msg, shd: share, wg: val, D: device,
       shpt: share, head: val, PS: list (val * share * peer)
  PRE [ tptr t_init, tptr t_dev ]
    PROP (readable_share shm; readable_share shd; readable_share shpt; peers_wf PS; pk_chain head PS;
          (* (s64)last_initiation_consumption + 20 ms: a signed addition (VST checks no overflow) *)
          Forall (fun x => match x with (_, _, P) =>
                    Int64.signed (hs_lic (p_hs P)) <= Int64.max_signed - 20000000 end) PS;
          (* every peer holds fewer than INT_MAX references (L03), so the lookup's
             reference and its put on rejection leave the count as it was (no saturation) *)
          peers_refs_ok PS)
    PARAMS (m; wg) GLOBALS (gv)
    SEP (init_rep shm m M; device_rep shd wg D; ptable shpt (d_ptab D) head; peers_rep PS;
         shim_state4 gv S w; noise_globals gv kc; wg_consts gv)
  POST [ tptr t_peer ]
    PROP () RETURN (peer_result (cin_res D PS M S))
    SEP (init_rep shm m M; device_rep shd wg D; ptable shpt (d_ptab D) head;
         peers_rep (peers_after PS (cin_res D PS M S));
         shim_state4 gv S w; noise_globals gv kc; wg_consts gv).

Definition cr_res (P: peer) (M: resp_msg) (r: list byte) (idx: int) : bool * resp_msg * handshake :=
  create_response_model x25519 aead_enc (p_hs P) M r idx.

Definition wg_noise_handshake_create_response_spec :=
  DECLARE N._wg_noise_handshake_create_response
  WITH gv: globals, S: shim, w: list int64, shm: share, m: val, M: resp_msg, shp: share, p: val, P: peer,
       shd: share, wg: val, D: device, sht: share, T: tstate
  PRE [ tptr t_resp, tptr t_hs ]
    PROP (writable_share shm; writable_share shp; readable_share shd; writable_share sht;
          p_device P = wg; hs_in_pool T p)
    PARAMS (m; hs_addr p) GLOBALS (gv)
    SEP (resp_rep shm m M; peer_rep shp p P; device_rep shd wg D; itable sht (d_itab D) T;
         shim_state4 gv S w; wg_consts gv)
  POST [ tbool ] EX r: list byte, EX idx: int,
    PROP (Zlength r = 32; fst (fst (cr_res P M r idx)) = true -> t_fresh T (hs_addr p) idx)
    RETURN (Val.of_bool (fst (fst (cr_res P M r idx))))
    SEP (resp_rep shm m (snd (fst (cr_res P M r idx)));
         peer_rep shp p (p_set_hs P (snd (cr_res P M r idx)));
         device_rep shd wg D;
         itable sht (d_itab D) (if fst (fst (cr_res P M r idx)) then t_insert T (hs_addr p) idx else T);
         shim_state4 gv (if Int.eq (hs_state (p_hs P)) HS_CONSUMED_INITIATION
                        then (if fst (fst (cr_res P M r idx)) then shim_u32 (shim_draw S r) idx
                              else shim_draw S r)
                        else S) w;
         wg_consts gv).

(* consume_response(m, wg): the table's entry with the receiver index; every pool entry's peer in PS *)
Definition cre_res (D: device) (T: tstate) (PS: list (val * share * peer)) (M: resp_msg) : option (val * peer) :=
  consume_response_model x25519 aead_dec (d_id D) T PS M.

Definition wg_noise_handshake_consume_response_spec :=
  DECLARE N._wg_noise_handshake_consume_response
  WITH gv: globals, S: shim, w: list int64, shm: share, m: val, M: resp_msg, shd: share, wg: val, D: device,
       sht: share, T: tstate, PS: list (val * share * peer)
  PRE [ tptr t_resp, tptr t_dev ]
    PROP (readable_share shm; readable_share shd; writable_share sht; pool_peers_ok T PS; peers_wf PS;
          peers_refs_ok PS)
    PARAMS (m; wg) GLOBALS (gv)
    SEP (resp_rep shm m M; device_rep shd wg D; itable sht (d_itab D) T; peers_rep PS;
         shim_state4 gv S w; wg_consts gv)
  POST [ tptr t_peer ]
    PROP () RETURN (peer_result (cre_res D T PS M))
    SEP (resp_rep shm m M; device_rep shd wg D; itable sht (d_itab D) T;
         peers_rep (peers_after PS (cre_res D T PS M));
         shim_state4 gv S w; wg_consts gv).

(* begin_session(&p->handshake, &p->keypairs): k = the address kzalloc returned (NULL: failure) *)
Definition bs_res (P: peer) (p k: val) (kc: int64) (KS: list (val * keypair)) (T: tstate) (S: shim)
  : bool * peer * kworld * int64 :=
  begin_session_model P (hs_addr p) k kc (mkKW KS T S).

Definition wg_noise_handshake_begin_session_spec :=
  DECLARE N._wg_noise_handshake_begin_session
  WITH gv: globals, S: shim, w: list int64, kc: int64, KS: list (val * keypair), T: tstate, shp: share, p: val,
       P: peer, shd: share, wg: val, D: device, sht: share
  PRE [ tptr t_hs, tptr t_kps ]
    PROP (writable_share shp; readable_share shd; writable_share sht; p_device P = wg;
          field_compatible t_peer [] p; hs_in_pool T p; kps_in_pool T p KS; slots_ok P KS)
    PARAMS (hs_addr p; kps_addr p) GLOBALS (gv)
    SEP (mem_mgr gv; shim_state4 gv S w; noise_globals gv kc; wg_consts gv; keypairs_rep CSw KS;
         peer_rep shp p P; device_rep shd wg D; itable sht (d_itab D) T)
  POST [ tbool ] EX k: val,
    PROP (s_failnext S = true -> k = nullval;
          k <> nullval -> ~ In k (saddrs (t_D T)) /\ ~ In k (map fst KS))
    RETURN (Val.of_bool (fst (fst (fst (bs_res P p k kc KS T S)))))
    SEP (mem_mgr gv; shim_state4 gv (kw_S (snd (fst (bs_res P p k kc KS T S)))) (begin_session_warn P (hs_addr p) k kc (mkKW KS T S) w);
         noise_globals gv (snd (bs_res P p k kc KS T S)); wg_consts gv;
         keypairs_rep CSw (kw_KS (snd (fst (bs_res P p k kc KS T S))));
         peer_rep shp p (snd (fst (fst (bs_res P p k kc KS T S))));
         device_rep shd wg D;
         itable sht (d_itab D) (kw_T (snd (fst (bs_res P p k kc KS T S))))).

(* ================================================================================================ *)
(* cookie.c                                                                                         *)
(* ================================================================================================ *)

Definition quickproof_swab16_spec :=
  DECLARE C._quickproof_swab16
  WITH x: Z
  PRE [ tushort ]
    PROP (0 <= x <= 65535) PARAMS (Vint (Int.repr x)) SEP ()
  POST [ tushort ]
    PROP () RETURN (Vint (Int.repr (swab16 x))) SEP ().

(* wg_cookie_checker_init(checker, wg): birthdate now, secret random, device wg; the keys are kept *)
Definition wg_cookie_checker_init_spec :=
  DECLARE C._wg_cookie_checker_init
  WITH gv: globals, S: shim, w: list int64, sh: share, c: val, ek: list byte, mk: list byte, wg: val
  PRE [ tptr t_cc, tptr t_dev ]
    PROP (writable_share sh; Zlength ek = 32; Zlength mk = 32) PARAMS (c; wg) GLOBALS (gv)
    SEP (shim_state4 gv S w;
         field_at_ sh t_cc [StructField N._secret] c;
         field_at sh t_cc [StructField N._cookie_encryption_key] (bytes ek) c;
         field_at sh t_cc [StructField N._message_mac1_key] (bytes mk) c;
         field_at_ sh t_cc [StructField N._secret_birthdate] c;
         field_at_ sh t_cc [StructField N._secret_lock] c;
         spacer sh 108 112 c;   (* the struct's padding: checker_rep's data_at owns it *)
         field_at_ sh t_cc [StructField N._device] c)
  POST [ tvoid ] EX r: list byte,
    PROP (Zlength r = 32) RETURN ()
    SEP (shim_state4 gv (shim_draw S r) w; checker_rep sh c (mkChk r ek mk (s_boot S) wg)).

Definition precompute_key_spec :=
  DECLARE C._precompute_key
  WITH gv: globals, shk: share, kp: val, shp: share, pp: val, pub: list byte, shl: share, lp: val,
       label: list byte
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share shk; readable_share shp; readable_share shl; Zlength pub = 32; Zlength label = 8)
    PARAMS (kp; pp; lp) GLOBALS (gv)
    SEP (data_at_ shk (tarray tuchar 32) kp; bytes_at shp pub pp; bytes_at shl label lp; blake2s_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (bytes_at shk (label_key label pub) kp; bytes_at shp pub pp; bytes_at shl label lp; blake2s_globals gv).

Definition wg_cookie_checker_precompute_device_keys_spec :=
  DECLARE C._wg_cookie_checker_precompute_device_keys
  WITH gv: globals, sh: share, wg: val, D: device
  PRE [ tptr t_cc ]
    PROP (writable_share sh; cc_dev (d_cc D) = wg) PARAMS (cc_addr wg) GLOBALS (gv)
    SEP (device_rep sh wg D; wg_consts gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (device_rep sh wg (dev_set_cc D (checker_set_keys (d_cc D) (checker_keys (d_id D))));
         wg_consts gv).

Definition wg_cookie_checker_precompute_peer_keys_spec :=
  DECLARE C._wg_cookie_checker_precompute_peer_keys
  WITH gv: globals, sh: share, p: val, H: handshake, Ck: cookie
  PRE [ tptr t_peer ]
    PROP (writable_share sh; field_compatible t_peer [] p) PARAMS (p) GLOBALS (gv)
    SEP (hs_rep sh (hs_addr p) H; cookie_rep sh (cookie_addr p) Ck; wg_consts gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (hs_rep sh (hs_addr p) H; cookie_rep sh (cookie_addr p) (cookie_set_keys Ck (hs_rstatic H));
         wg_consts gv).

Definition wg_cookie_init_spec :=
  DECLARE C._wg_cookie_init
  WITH sh: share, c: val
  PRE [ tptr t_cookie ]
    PROP (writable_share sh) PARAMS (c)
    SEP (data_at_ sh t_cookie c)
  POST [ tvoid ]
    PROP () RETURN () SEP (cookie_rep sh c cookie_zero).

(* compute_mac1(out, m, len, key): out = MAC(key, m[0..len-32)); msg = those len - 32 bytes *)
Definition compute_mac1_spec :=
  DECLARE C._compute_mac1
  WITH gv: globals, sho: share, o: val, shm: share, mp: val, msg: list byte, shk: share, kp: val,
       key: list byte
  PRE [ tptr tuchar, tptr tvoid, tulong, tptr tuchar ]
    PROP (writable_share sho; readable_share shm; readable_share shk; Zlength key = 32;
          Zlength msg + 32 <= Int64.max_signed)
    PARAMS (o; mp; Vlong (Int64.repr (Zlength msg + 32)); kp) GLOBALS (gv)
    SEP (data_at_ sho (tarray tuchar 16) o; b2s_bytes shm msg mp; bytes_at shk key kp; wg_consts gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (bytes_at sho (MAC key msg) o; b2s_bytes shm msg mp; bytes_at shk key kp; wg_consts gv).

(* compute_mac2(out, m, len, cookie): out = MAC(cookie, m[0..len-16)); msg = those len - 16 bytes *)
Definition compute_mac2_spec :=
  DECLARE C._compute_mac2
  WITH gv: globals, sho: share, o: val, shm: share, mp: val, msg: list byte, shk: share, kp: val,
       ck: list byte
  PRE [ tptr tuchar, tptr tvoid, tulong, tptr tuchar ]
    PROP (writable_share sho; readable_share shm; readable_share shk; Zlength ck = 16;
          Zlength msg + 16 <= Int64.max_signed)
    PARAMS (o; mp; Vlong (Int64.repr (Zlength msg + 16)); kp) GLOBALS (gv)
    SEP (data_at_ sho (tarray tuchar 16) o; b2s_bytes shm msg mp; bytes_at shk ck kp; wg_consts gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (bytes_at sho (MAC ck msg) o; b2s_bytes shm msg mp; bytes_at shk ck kp; wg_consts gv).

(* make_cookie(out, skb, checker): the secret rotates (r drawn) when 120 s old *)
Definition make_cookie_spec :=
  DECLARE C._make_cookie
  WITH gv: globals, S: shim, w: list int64, sho: share, o: val, shs: share, sp: val, s: skb, shc: share, c: val,
       CC: checker
  PRE [ tptr tuchar, tptr t_skb, tptr t_cc ]
    PROP (writable_share sho; readable_share shs; writable_share shc) PARAMS (o; sp; c) GLOBALS (gv)
    SEP (data_at_ sho (tarray tuchar 16) o; skb_rep shs sp s; checker_rep shc c CC; shim_state4 gv S w;
         wg_consts gv)
  POST [ tvoid ] EX r: list byte,
    PROP (Zlength r = 32) RETURN ()
    SEP (bytes_at sho (cookie_of (cc_secret (checker_rotate CC (s_boot S) r)) s) o; skb_rep shs sp s;
         checker_rep shc c (checker_rotate CC (s_boot S) r);
         shim_state4 gv (if checker_rotates CC (s_boot S) then shim_draw S r else S) w; wg_consts gv).

(* validate(checker, skb, check_cookie): msg = the packet's bytes at skb->data, skb->len of them *)
Definition validate_rotates (CC: checker) (msg: list byte) (check_cookie: bool) (now: int64) : bool :=
  let n := Zlength msg in
  andb (bytes_eqb (mac1_of (cc_mkey CC) msg) (sublist (n - 32) (n - 16) msg))
       (andb check_cookie (checker_rotates CC now)).

Definition wg_cookie_validate_packet_spec :=
  DECLARE C._wg_cookie_validate_packet
  WITH gv: globals, S: shim, w: list int64, shc: share, c: val, CC: checker, shs: share, sp: val, s: skb, shm: share,
       msg: list byte, chk: bool
  PRE [ tptr t_cc, tptr t_skb, tbool ]
    PROP (writable_share shc; readable_share shs; readable_share shm; 32 <= Zlength msg;
          Zlength msg = Int.unsigned (sk_len s))
    PARAMS (c; sp; Val.of_bool chk) GLOBALS (gv)
    SEP (checker_rep shc c CC; skb_rep shs sp s; bytes_at shm msg (sk_data s); shim_state4 gv S w;
         wg_consts gv)
  POST [ tint ] EX r: list byte,
    PROP (Zlength r = 32)
    RETURN (Vint (Int.repr (fst (validate_model CC s msg chk (s_boot S) (s_rlallow S) r))))
    SEP (checker_rep shc c (snd (validate_model CC s msg chk (s_boot S) (s_rlallow S) r));
         skb_rep shs sp s; bytes_at shm msg (sk_data s);
         shim_state4 gv (if validate_rotates CC msg chk (s_boot S) then shim_draw S r else S) w;
         wg_consts gv).

(* add_mac(msg, len, peer): msg any buffer of len >= 32 bytes (a message struct: convert it to its byte
   image init_bytes / resp_bytes) *)
Definition wg_cookie_add_mac_to_packet_spec :=
  DECLARE C._wg_cookie_add_mac_to_packet
  WITH gv: globals, S: shim, w: list int64, shm: share, mp: val, msg: list byte, shp: share, p: val, Ck: cookie
  PRE [ tptr tvoid, tulong, tptr t_peer ]
    PROP (writable_share shm; writable_share shp; field_compatible t_peer [] p;
          32 <= Zlength msg <= Int64.max_signed)
    PARAMS (mp; Vlong (Int64.repr (Zlength msg)); p) GLOBALS (gv)
    SEP (bytes_at shm msg mp; cookie_rep shp (cookie_addr p) Ck; shim_state4 gv S w; wg_consts gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (bytes_at shm (fst (add_mac_model Ck msg (s_boot S))) mp;
         cookie_rep shp (cookie_addr p) (snd (add_mac_model Ck msg (s_boot S)));
         shim_state4 gv S w; wg_consts gv).

(* message_create(dst, skb, index, checker): nonce = 24 random bytes, then a rotation may draw r *)
Definition mc_res (CC: checker) (s: skb) (index: int) (nonce: list byte) (msg: list byte) (S: shim)
  (r: list byte) : cookie_msg * checker :=
  message_create_model xaead_enc CC s index nonce
    (sublist (Zlength msg - 32) (Zlength msg - 16) msg) (s_boot S) r.

Definition wg_cookie_message_create_spec :=
  DECLARE C._wg_cookie_message_create
  WITH gv: globals, S: shim, w: list int64, shd: share, dp: val, shs: share, sp: val, s: skb, shm: share,
       msg: list byte, index: int, shc: share, c: val, CC: checker
  PRE [ tptr t_cmsg, tptr t_skb, tuint, tptr t_cc ]
    PROP (writable_share shd; readable_share shs; readable_share shm; writable_share shc;
          32 <= Zlength msg; Zlength msg = Int.unsigned (sk_len s))
    PARAMS (dp; sp; Vint index; c) GLOBALS (gv)
    SEP (@data_at_ Cookie.CS shd t_cmsg dp; skb_rep shs sp s; bytes_at shm msg (sk_data s);
         checker_rep shc c CC; shim_state4 gv S w; wg_consts gv)
  POST [ tvoid ] EX nonce: list byte, EX r: list byte,
    PROP (Zlength nonce = 24; Zlength r = 32) RETURN ()
    SEP (cmsg_rep shd dp (fst (mc_res CC s index nonce msg S r));
         skb_rep shs sp s; bytes_at shm msg (sk_data s);
         checker_rep shc c (snd (mc_res CC s index nonce msg S r));
         shim_state4 gv (if checker_rotates CC (s_boot S) then shim_draw (shim_draw S nonce) r
                        else shim_draw S nonce) w;
         wg_consts gv).

Definition mcons_res (T: tstate) (PS: list (val * share * peer)) (M: cookie_msg) (S: shim) : option (val * peer) :=
  message_consume_model xaead_dec T PS M (s_boot S).

Definition wg_cookie_message_consume_spec :=
  DECLARE C._wg_cookie_message_consume
  WITH gv: globals, S: shim, w: list int64, shm: share, m: val, M: cookie_msg, shd: share, wg: val, D: device,
       sht: share, T: tstate, PS: list (val * share * peer)
  PRE [ tptr t_cmsg, tptr t_dev ]
    PROP (readable_share shm; readable_share shd; writable_share sht; pool_peers_ok T PS; peers_wf PS;
          peers_refs_ok PS)
    PARAMS (m; wg) GLOBALS (gv)
    SEP (cmsg_rep shm m M; device_rep shd wg D; itable sht (d_itab D) T; peers_rep PS;
         shim_state4 gv S w; wg_consts gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (cmsg_rep shm m M; device_rep shd wg D; itable sht (d_itab D) T;
         peers_rep (peers_after PS (mcons_res T PS M S));
         shim_state4 gv S w; wg_consts gv).

(* all the specifications, in the order of protocol_idents *)
Definition prot_G_list : funspecs :=
  [quickproof_rounddown_pow_of_two_spec;
   put_unaligned_be32_spec;
   put_unaligned_be64_spec;
   curve25519_generate_secret_spec;
   wg_noise_reset_last_sent_handshake_spec;
   wg_noise_init_spec;
   wg_noise_precompute_static_static_spec;
   wg_noise_handshake_init_spec;
   handshake_zero_spec;
   wg_noise_handshake_clear_spec;
   keypair_create_spec;
   keypair_free_rcu_spec;
   keypair_free_kref_spec;
   wg_noise_keypair_put_spec;
   wg_noise_keypair_get_spec;
   wg_noise_keypairs_clear_spec;
   wg_noise_expire_current_peer_keypairs_spec;
   add_new_keypair_spec;
   wg_noise_received_with_keypair_spec;
   wg_noise_set_static_identity_private_key_spec;
   hmac_spec;
   kdf_spec;
   derive_keys_spec;
   mix_dh_spec;
   mix_precomputed_dh_spec;
   mix_hash_spec;
   mix_psk_spec;
   handshake_init_spec;
   message_encrypt_spec;
   message_decrypt_spec;
   message_ephemeral_spec;
   tai64n_now_spec;
   wg_noise_handshake_create_initiation_spec;
   wg_noise_handshake_consume_initiation_spec;
   wg_noise_handshake_create_response_spec;
   wg_noise_handshake_consume_response_spec;
   wg_noise_handshake_begin_session_spec;
   quickproof_swab16_spec;
   wg_cookie_checker_init_spec;
   precompute_key_spec;
   wg_cookie_checker_precompute_device_keys_spec;
   wg_cookie_checker_precompute_peer_keys_spec;
   wg_cookie_init_spec;
   compute_mac1_spec;
   compute_mac2_spec;
   make_cookie_spec;
   wg_cookie_validate_packet_spec;
   wg_cookie_add_mac_to_packet_spec;
   wg_cookie_message_create_spec;
   wg_cookie_message_consume_spec;
   ktime_get_coarse_boottime_ns_spec;
   ktime_get_real_ts64_spec;
   get_random_bytes_spec;
   get_random_bytes_wait_spec;
   get_random_u32_spec;
   kzalloc_spec;
   kfree_spec;
   kfree_sensitive_spec;
   wg_shim_refcount_warn_saturate_spec;
   wg_shim_refcount_neg_spec;
   wg_shim_refcount_inc_not_zero_spec;
   wg_shim_refcount_inc_spec;
   wg_shim_refcount_dec_and_test_spec;
   wg_peer_get_maybe_zero_spec;
   wg_shim_peer_release_spec;
   wg_peer_put_spec;
   wg_pubkey_hashtable_lookup_spec;
   wg_index_hashtable_remove_spec;
   wg_shim_index_in_use_spec;
   wg_index_hashtable_insert_spec;
   wg_index_hashtable_replace_spec;
   wg_index_hashtable_lookup_spec;
   wg_ratelimiter_allow_spec;
   wg_birthdate_has_expired_spec].

End Specs.
