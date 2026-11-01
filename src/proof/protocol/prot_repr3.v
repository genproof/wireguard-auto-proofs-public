(* Representation of the protocol state in memory.

   Every object predicate is stated in ONE compspecs: Noise.CS (all composites of the handshake are in
   noise.c's unit), except the socket buffer and the cookie message (only in cookie.c / the shim): Cookie.CS.
   Body proofs in other units (shim, cookie) convert with data_at_change_composite / field_at_change_composite; harness pieces convert to their world W_<law> the same way.
   The malloc token of a keypair is at the world's compspecs CSw (the malloc specs are stated there).

   Ownership:
   - the index table owns its POOL: every entry that may be in the table (hashed or not), wherever it lives
     (a peer's handshake.entry, a keypair's entry, a harness struct).  Peers and keypairs are represented
     WITHOUT their entry field.  An entry's `next` and `hashed` fields follow from the table's list.
   - locks, rcu heads and other never-read fields: any value (existential).
   -: the field-wise representations (hs_rep, peer_rep, keypair_rep) include the struct's PADDING
     (`spacer`, as VST's unfold_data_at produces it): VST's logic is linear, data_at owns the padding.
   - the peer's public-key chain (pubkey_next) is a pure property of the peer list (pk_chain). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import QuickProof.Env.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.
Local Open Scope logic.

(* ------------------------------------------------------------------------------------------------ *)
(* Identifiers and types                                                                            *)
(* ------------------------------------------------------------------------------------------------ *)

Module I.
  Include WgNoise.noise.code.
End I.
Definition _sk_buff : ident := WgNoise.cookie.code._sk_buff.
Definition _message_handshake_cookie : ident := WgNoise.cookie.code._message_handshake_cookie.
Definition _mac1_key_label : ident := WgNoise.cookie.code._mac1_key_label.
Definition _cookie_key_label : ident := WgNoise.cookie.code._cookie_key_label.
Definition _wg_shim_boottime_ns : ident := WgNoise.shim.code._wg_shim_boottime_ns.
Definition _wg_shim_real_sec : ident := WgNoise.shim.code._wg_shim_real_sec.
Definition _wg_shim_real_nsec : ident := WgNoise.shim.code._wg_shim_real_nsec.
Definition _wg_shim_random_log : ident := WgNoise.shim.code._wg_shim_random_log.
Definition _wg_shim_random_log_prev : ident := WgNoise.shim.code._wg_shim_random_log_prev.
Definition _wg_shim_random_u32 : ident := WgNoise.shim.code._wg_shim_random_u32.
Definition _wg_shim_allocs : ident := WgNoise.shim.code._wg_shim_allocs.
Definition _wg_shim_alloc_failures : ident := WgNoise.shim.code._wg_shim_alloc_failures.
Definition _wg_shim_frees : ident := WgNoise.shim.code._wg_shim_frees.
Definition _wg_shim_fail_next_alloc : ident := WgNoise.shim.code._wg_shim_fail_next_alloc.
Definition _wg_shim_peer_released : ident := WgNoise.shim.code._wg_shim_peer_released.
Definition _wg_shim_ratelimit_allow : ident := WgNoise.shim.code._wg_shim_ratelimit_allow.
Definition _wg_shim_refcount_warn : ident := WgNoise.shim.code._wg_shim_refcount_warn.

Definition t_entry_s := Tstruct I._index_hashtable_entry noattr.
Definition t_itab := Tstruct I._index_hashtable noattr.
Definition t_ptab := Tstruct I._pubkey_hashtable noattr.
Definition t_hs := Tstruct I._noise_handshake noattr.
Definition t_peer := Tstruct I._wg_peer noattr.
Definition t_kps := Tstruct I._noise_keypairs noattr.
Definition t_kp := Tstruct I._noise_keypair noattr.
Definition t_sym := Tstruct I._noise_symmetric_key noattr.
Definition t_sid := Tstruct I._noise_static_identity noattr.
Definition t_cc := Tstruct I._cookie_checker noattr.
Definition t_cookie := Tstruct I._cookie noattr.
Definition t_dev := Tstruct I._wg_device noattr.
Definition t_init := Tstruct I._message_handshake_initiation noattr.
Definition t_resp := Tstruct I._message_handshake_response noattr.
Definition t_kref := Tstruct I._kref noattr.
Definition t_atomic64 := Tstruct I.___gp_atomic64_t noattr.
Definition t_timespec := Tstruct I._timespec64 noattr.
Definition t_skb := Tstruct _sk_buff noattr.
Definition t_cmsg := Tstruct _message_handshake_cookie noattr.

(* sizes and offsets (x86_64; the same in every unit) *)
Definition SIZEOF_KEYPAIR : Z := 1200.
Definition OFS_PEER_KEYPAIRS : Z := 16.
Definition OFS_PEER_HANDSHAKE : Z := 48.
Definition OFS_PEER_COOKIE : Z := 360.
Definition OFS_DEV_IDENTITY : Z := 8.
Definition OFS_DEV_CHECKER : Z := 80.
Definition OFS_KP_REFCOUNT : Z := 1184.
Definition OFS_KP_RCU : Z := 1188.

(* the address of a peer's keypairs / handshake (= its entry) / cookie; of a device's identity / checker *)
Definition kps_addr (p: val) : val := offset_val OFS_PEER_KEYPAIRS p.
Definition hs_addr (p: val) : val := offset_val OFS_PEER_HANDSHAKE p.
Definition cookie_addr (p: val) : val := offset_val OFS_PEER_COOKIE p.
Definition id_addr (wg: val) : val := offset_val OFS_DEV_IDENTITY wg.
Definition cc_addr (wg: val) : val := offset_val OFS_DEV_CHECKER wg.

Definition bytes (bs: list byte) : list val := map Vubyte bs.

(* ------------------------------------------------------------------------------------------------ *)
(* Well-formedness of the abstract objects (lengths)                                                *)
(* ------------------------------------------------------------------------------------------------ *)

Definition id_ok (ID: identity) : Prop := Zlength (id_pub ID) = 32 /\ Zlength (id_priv ID) = 32.
Definition cc_ok (CC: checker) : Prop :=
  Zlength (cc_secret CC) = 32 /\ Zlength (cc_ekey CC) = 32 /\ Zlength (cc_mkey CC) = 32.
Definition hs_ok (H: handshake) : Prop :=
  Zlength (hs_eph H) = 32 /\ Zlength (hs_rstatic H) = 32 /\ Zlength (hs_reph H) = 32 /\
  Zlength (hs_ss H) = 32 /\ Zlength (hs_psk H) = 32 /\ Zlength (hs_hash H) = 32 /\
  Zlength (hs_ck H) = 32 /\ Zlength (hs_ts H) = 12.
Definition cookie_ok (C: cookie) : Prop :=
  Zlength (ck_cookie C) = 16 /\ Zlength (ck_last_mac1 C) = 16 /\ Zlength (ck_dkey C) = 32 /\
  Zlength (ck_mkey C) = 32.
Definition kp_ok (K: keypair) : Prop :=
  Zlength (sk_key (kp_send K)) = 32 /\ Zlength (sk_key (kp_recv K)) = 32 /\ Zlength (kp_backtrack K) = 128.
Definition im_ok (M: init_msg) : Prop :=
  Zlength (im_eph M) = 32 /\ Zlength (im_encs M) = 48 /\ Zlength (im_enct M) = 28 /\
  Zlength (im_mac1 M) = 16 /\ Zlength (im_mac2 M) = 16.
Definition rm_ok (M: resp_msg) : Prop :=
  Zlength (rm_eph M) = 32 /\ Zlength (rm_encn M) = 16 /\ Zlength (rm_mac1 M) = 16 /\ Zlength (rm_mac2 M) = 16.
Definition cm_ok (M: cookie_msg) : Prop := Zlength (cm_nonce M) = 24 /\ Zlength (cm_enc M) = 32.
Definition skb_ok (s: skb) : Prop :=
  0 <= sk_proto s <= 65535 /\ Zlength (sk_ip4 s) = 4 /\ Zlength (sk_ip6 s) = 16 /\ Zlength (sk_port s) = 2.

(* ------------------------------------------------------------------------------------------------ *)
(* Objects of noise.c's compspecs                                                                   *)
(* ------------------------------------------------------------------------------------------------ *)

Section NoiseCS.
#[local] Existing Instance Noise.CS.

(* a byte buffer *)
Definition bytes_at (sh: share) (bs: list byte) (p: val) : mpred :=
  data_at sh (tarray tuchar (Zlength bs)) (bytes bs) p.

(* an output buffer of |v| bytes with contents v (any values): nothing when empty (the pointer may then be
   NULL, as message_decrypt(NULL, .., 16, ..) in consume_response) *)
Definition out_bytes (sh: share) (v: list val) (p: val) : mpred :=
  if Z.eq_dec (Zlength v) 0 then emp else data_at sh (tarray tuchar (Zlength v)) v p.

(* an index-table entry with its list fields *)
Definition entry_val (E: entry) (next: val) (hashed: bool) : reptype t_entry_s :=
  (e_peer E, (next, (Val.of_bool hashed, (Vint (e_type E), Vint (e_index E))))).
Definition entry_at (sh: share) (a: val) (E: entry) (next: val) (hashed: bool) : mpred :=
  data_at sh t_entry_s (entry_val E next hashed) a.
(* an entry outside any table (as after remove, or zeroed) *)
Definition entry_out (sh: share) (a: val) (E: entry) : mpred := entry_at sh a E nullval false.

(* The index table at tab with pool and list T. *)
Definition pool_item_rep (L: list val) (x: val * share * entry) : mpred :=
  match x with (a, sh, E) => entry_at sh a E (succ_in L a) (vin a L) end.
Definition itable_wf (T: tstate) : Prop :=
  NoDup (t_L T) /\ incl (t_L T) (saddrs (t_D T)) /\ NoDup (saddrs (t_D T)) /\
  Forall (fun x => match x with (_, sh, _) => writable_share sh end) (t_D T).
Definition itable (sht: share) (tab: val) (T: tstate) : mpred :=
  !! itable_wf T &&
  (data_at sht t_itab (hd nullval (t_L T)) tab *
   iter_sepcon (pool_item_rep (t_L T)) (t_D T)).

(* struct noise_static_identity *)
Definition identity_rep (sh: share) (a: val) (ID: identity) : mpred :=
  !! id_ok ID &&
  EX lk: val, data_at sh t_sid (bytes (id_pub ID), (bytes (id_priv ID), (lk, Val.of_bool (id_has ID)))) a.

(* struct cookie_checker *)
Definition checker_rep (sh: share) (a: val) (CC: checker) : mpred :=
  !! cc_ok CC &&
  EX lk: val, data_at sh t_cc (bytes (cc_secret CC), (bytes (cc_ekey CC), (bytes (cc_mkey CC),
                                  (Vlong (cc_birth CC), (lk, cc_dev CC))))) a.

(* struct wg_device *)
Definition device_rep (sh: share) (wg: val) (D: device) : mpred :=
  !! field_compatible t_dev [] wg &&
  (field_at sh t_dev [StructField I._dev] (d_dev D) wg *
   identity_rep sh (id_addr wg) (d_id D) *
   checker_rep sh (cc_addr wg) (d_cc D) *
   field_at sh t_dev [StructField I._peer_hashtable] (d_ptab D) wg *
   field_at sh t_dev [StructField I._index_hashtable] (d_itab D) wg).

(* struct noise_handshake at h, WITHOUT its entry (the entry is in the index table's pool) *)
Definition hs_rep (sh: share) (h: val) (H: handshake) : mpred :=
  !! hs_ok H &&
  (field_at sh t_hs [StructField I._state] (Vint (hs_state H)) h *
   field_at sh t_hs [StructField I._last_initiation_consumption] (Vlong (hs_lic H)) h *
   field_at sh t_hs [StructField I._static_identity] (hs_sid H) h *
   field_at sh t_hs [StructField I._ephemeral_private] (bytes (hs_eph H)) h *
   field_at sh t_hs [StructField I._remote_static] (bytes (hs_rstatic H)) h *
   field_at sh t_hs [StructField I._remote_ephemeral] (bytes (hs_reph H)) h *
   field_at sh t_hs [StructField I._precomputed_static_static] (bytes (hs_ss H)) h *
   field_at sh t_hs [StructField I._preshared_key] (bytes (hs_psk H)) h *
   field_at sh t_hs [StructField I._hash] (bytes (hs_hash H)) h *
   field_at sh t_hs [StructField I._chaining_key] (bytes (hs_ck H)) h *
   field_at sh t_hs [StructField I._latest_timestamp] (bytes (hs_ts H)) h *
   field_at sh t_hs [StructField I._remote_index] (Vint (hs_rindex H)) h *
   (EX lk: val, field_at sh t_hs [StructField I._lock] lk h) *
   (* the struct's padding (VST's logic is linear: data_at owns it): after state, at the end *)
   spacer sh 36 40 h * spacer sh 300 304 h).

(* struct cookie *)
Definition cookie_val (C: cookie) (lk: val) : reptype t_cookie :=
  (Vlong (ck_birth C), (Val.of_bool (ck_valid C), (bytes (ck_cookie C), (Val.of_bool (ck_sent C),
   (bytes (ck_last_mac1 C), (bytes (ck_dkey C), (bytes (ck_mkey C), lk))))))).
Definition cookie_rep (sh: share) (c: val) (C: cookie) : mpred :=
  !! cookie_ok C && EX lk: val, data_at sh t_cookie (cookie_val C lk) c.

(* struct noise_keypairs *)
Definition kps_rep (sh: share) (a: val) (cur prev next: val) : mpred :=
  EX lk: val, data_at sh t_kps (cur, (prev, (next, lk))) a.

(* struct wg_peer at p, WITHOUT its handshake's entry *)
Definition peer_rep (sh: share) (p: val) (P: peer) : mpred :=
  !! field_compatible t_peer [] p &&
  (field_at sh t_peer [StructField I._device] (p_device P) p *
   field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   field_at sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   field_at sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   field_at sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   field_at sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   (* the struct's padding: after is_dead, after refcount (the handshake's own is in hs_rep) *)
   spacer sh 9 16 p * spacer sh 476 480 p).

(* the reference count of a peer: the conjunct of peer_rep that wg_peer_get_maybe_zero / wg_peer_put use *)
Definition peer_refs_rep (sh: share) (p: val) (r: int) : mpred :=
  field_at sh t_peer [StructField I._refcount] (Vint r) p.

(* a list of peers (address, share, contents) *)
Definition peer_item_rep (x: val * share * peer) : mpred := match x with (a, sh, P) => peer_rep sh a P end.
Definition peers_rep (PS: list (val * share * peer)) : mpred := iter_sepcon peer_item_rep PS.

(* the public-key table's chain: head, then pubkey_next, visits exactly the peers of PS in order *)
Fixpoint pk_chain (head: val) (PS: list (val * share * peer)) : Prop :=
  match PS with
  | [] => head = nullval
  | (a, _, P) :: PS' => head = a /\ pk_chain (p_pknext P) PS'
  end.

Definition ptable (sh: share) (tab: val) (head: val) : mpred := data_at sh t_ptab head tab.

(* struct noise_symmetric_key *)
Definition symkey_val (K: symkey) : reptype t_sym :=
  (bytes (sk_key K), (Vlong (sk_birth K), Val.of_bool (sk_valid K))).
Definition symkey_rep (sh: share) (a: val) (K: symkey) : mpred := data_at sh t_sym (symkey_val K) a.

(* the messages *)
Definition init_val (M: init_msg) : reptype t_init :=
  (Vint (im_type M), (Vint (im_sender M), (bytes (im_eph M), (bytes (im_encs M), (bytes (im_enct M),
   (bytes (im_mac1 M), bytes (im_mac2 M))))))).
Definition init_rep (sh: share) (m: val) (M: init_msg) : mpred := !! im_ok M && data_at sh t_init (init_val M) m.
Definition resp_val (M: resp_msg) : reptype t_resp :=
  (Vint (rm_type M), (Vint (rm_sender M), (Vint (rm_receiver M), (bytes (rm_eph M), (bytes (rm_encn M),
   (bytes (rm_mac1 M), bytes (rm_mac2 M))))))).
Definition resp_rep (sh: share) (m: val) (M: resp_msg) : mpred := !! rm_ok M && data_at sh t_resp (resp_val M) m.

(* ------------------------------------------------------------------------------------------------ *)
(* Globals                                                                                          *)
(* ------------------------------------------------------------------------------------------------ *)

(* the shim's refcount_t warnings wg_shim_refcount_warn[5] (unsigned long, by
   enum refcount_saturation_type).  Kept existentially: the specifications state the reference counts exactly
   (saturation included, rc_add1 / rc_sub1 of prot_model3.v) but not the warning counters. *)
Definition refwarn (gv: globals) : mpred :=
  EX w: list int64, !! (Zlength w = 5) && data_at Ews (tarray tulong 5) (map Vlong w) (gv _wg_shim_refcount_warn).

(* the shim's state *)
Definition shim_state (gv: globals) (S: shim) : mpred :=
  !! shim_ok S &&
  (data_at Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
   data_at Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
   data_at Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
   data_at Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
   data_at Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
   data_at Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
   data_at Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   data_at Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
   data_at Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   data_at Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   data_at Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
   data_at Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow) *
   refwarn gv).

(* the globals alone, and shim_state split into them and refwarn *)
Definition shim_core (gv: globals) (S: shim) : mpred :=
  !! shim_ok S &&
  (data_at Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
   data_at Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
   data_at Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
   data_at Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
   data_at Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
   data_at Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
   data_at Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   data_at Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
   data_at Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   data_at Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   data_at Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
   data_at Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow)).

Lemma shim_state_split gv S : shim_state gv S = shim_core gv S * refwarn gv.
Proof. unfold shim_state, shim_core. rewrite sepcon_andp_prop'. reflexivity. Qed.

(* noise.c's globals: the constant names, the initial hash and chaining key (h, ck), keypair_counter kc,
   mix_precomputed_dh's zero_point *)
Definition noise_globals_raw (gv: globals) (h ck: list byte) (kc: int64) : mpred :=
  !! (Zlength h = 32 /\ Zlength ck = 32) &&
  (data_at Ers (tarray tuchar 37) (bytes handshake_name) (gv I._handshake_name) *
   data_at Ers (tarray tuchar 34) (bytes identifier_name) (gv I._identifier_name) *
   data_at Ews (tarray tuchar 32) (bytes h) (gv I._handshake_init_hash) *
   data_at Ews (tarray tuchar 32) (bytes ck) (gv I._handshake_init_chaining_key) *
   data_at Ews t_atomic64 (Vlong kc) (gv I._keypair_counter) *
   data_at Ews (tarray tuchar 32) (bytes zeros32) (gv I._zero_point)).

End NoiseCS.

(* after wg_noise_init *)
Definition noise_globals (gv: globals) (kc: int64) : mpred := noise_globals_raw gv init_hash init_ck kc.

(* the read-only globals of the primitives and of cookie.c *)
Definition cookie_globals (gv: globals) : mpred :=
  @data_at Noise.CS Ers (tarray tuchar 8) (bytes mac1_label) (gv _mac1_key_label) *
  @data_at Noise.CS Ers (tarray tuchar 8) (bytes cookie_label) (gv _cookie_key_label).
Definition wg_consts (gv: globals) : mpred :=
  blake2s_globals gv * @curve25519_globals Noise.CS gv * @zero_page Noise.CS gv * cookie_globals gv.

(* ------------------------------------------------------------------------------------------------ *)
(* Objects of cookie.c's compspecs                                                                  *)
(* ------------------------------------------------------------------------------------------------ *)

Section CookieCS.
#[local] Existing Instance Cookie.CS.

(* struct sk_buff (quickproof_net.h); the message bytes at sk_data are a separate buffer *)
Definition skb_val (s: skb) : reptype t_skb :=
  (sk_data s, (Vint (sk_len s), (Vint (Int.repr (sk_proto s)), (bytes (sk_ip4 s), (bytes (sk_ip6 s),
   bytes (sk_port s)))))).
Definition skb_rep (sh: share) (p: val) (s: skb) : mpred := !! skb_ok s && data_at sh t_skb (skb_val s) p.

(* struct message_handshake_cookie *)
Definition cmsg_val (M: cookie_msg) : reptype t_cmsg :=
  (Vint (cm_type M), (Vint (cm_receiver M), (bytes (cm_nonce M), bytes (cm_enc M)))).
Definition cmsg_rep (sh: share) (m: val) (M: cookie_msg) : mpred := !! cm_ok M && data_at sh t_cmsg (cmsg_val M) m.

End CookieCS.

(* ------------------------------------------------------------------------------------------------ *)
(* Keypairs (malloc'd by kzalloc: token at the world's compspecs)                                   *)
(* ------------------------------------------------------------------------------------------------ *)

Section Keypairs.
Variable CSw: compspecs.
#[local] Existing Instance Noise.CS.

(* struct noise_keypair at k, WITHOUT its entry (in the pool, at address k), with its malloc token *)
Definition keypair_rep (k: val) (K: keypair) : mpred :=
  !! (field_compatible t_kp [] k /\ kp_ok K) &&
  (@malloc_token CSw Ews (tarray tuchar SIZEOF_KEYPAIR) k *
   field_at Ews t_kp [StructField I._sending] (symkey_val (kp_send K)) k *
   field_at Ews t_kp [StructField I._sending_counter] (Vlong (kp_scounter K)) k *
   field_at Ews t_kp [StructField I._receiving] (symkey_val (kp_recv K)) k *
   (EX lk: val, field_at Ews t_kp [StructField I._receiving_counter]
                   (Vlong (kp_rcounter K), (lk, map Vlong (kp_backtrack K))) k) *
   field_at Ews t_kp [StructField I._remote_index] (Vint (kp_rindex K)) k *
   field_at Ews t_kp [StructField I._i_am_the_initiator] (Val.of_bool (kp_init K)) k *
   field_at Ews t_kp [StructField I._refcount] (Vint (kp_refs K)) k *
   (EX r: val, field_at Ews t_kp [StructField I._rcu] r k) *
   field_at Ews t_kp [StructField I._internal_id] (Vlong (kp_id K)) k *
   (* the struct's padding: after i_am_the_initiator *)
   spacer Ews 1181 1184 k).

Definition keypair_item_rep (x: val * keypair) : mpred := match x with (k, K) => keypair_rep k K end.
Definition keypairs_rep (KS: list (val * keypair)) : mpred := iter_sepcon keypair_item_rep KS.

End Keypairs.

(* ------------------------------------------------------------------------------------------------ *)
(* Pure invariants used by the specifications                                                       *)
(* ------------------------------------------------------------------------------------------------ *)

(* every pool entry's peer is a peer of PS with at least one reference (L03), and a handshake-type entry
   is its peer's handshake entry; the other entries are keypair entries *)
Definition pool_peers_ok (T: tstate) (PS: list (val * share * peer)) : Prop :=
  Forall (fun x => match x with (a, _, E) =>
            (exists sh P, sfind PS (e_peer E) = Some (sh, P) /\ p_refs P <> Int.zero) /\
            ((e_type E = IDX_HANDSHAKE /\ a = hs_addr (e_peer E)) \/ e_type E = IDX_KEYPAIR) end) (t_D T).

(* the peer at p has its handshake entry in the pool with e_peer = p *)
Definition hs_in_pool (T: tstate) (p: val) : Prop :=
  exists E, t_entry T (hs_addr p) = Some E /\ e_peer E = p.

(* the keypairs KS of peer p: each has its entry (at its own address) in the pool, with e_peer = p *)
Definition kps_in_pool (T: tstate) (p: val) (KS: list (val * keypair)) : Prop :=
  NoDup (map fst KS) /\
  Forall (fun x => exists E, sfind (t_D T) (fst x) = Some (Ews, E) /\ e_peer E = p) KS.

(* the peers' shares are writable *)
Definition peers_wf (PS: list (val * share * peer)) : Prop :=
  Forall (fun x => match x with (_, sh, _) => writable_share sh end) PS.

(* every peer holds 1 .. INT_MAX - 1 references, so that one more reference
   (a lookup) and its put leave the count as it was (rc_sub1 (rc_add1 r) = r, prot_model3.v) *)
Definition peers_refs_ok (PS: list (val * share * peer)) : Prop :=
  Forall (fun x => match x with (_, _, P) => 0 < Int.unsigned (p_refs P) < 2147483647 end) PS.

(* the peer's slots: NULL or live keypairs, the non-NULL ones pairwise distinct *)
Definition slots_ok (P: peer) (KS: list (val * keypair)) : Prop :=
  let sl := [p_cur P; p_prev P; p_next P] in
  Forall (fun k => k = nullval \/ In k (map fst KS)) sl /\
  NoDup (filter (fun k => if eq_dec k nullval then false else true) sl).
