(* The specifications of the helpers shared by the hs_ laws: harness/hs_laws.h (any_u64, bytes_eq,
   any_clocks, new_device, new_peer, new_pair) and harness/hs_unchanged.h (copy_peer, same_peer).

   Every hs_ harness contains its own copy of these static functions; the copies are the same Clight
   functions (identifiers are names), so each body is proved once, in the compspecs CSh of the harness
   hs_reject_initiation (which has the composites of every hs_ harness: struct pair and the structs of
   noise.c), and lifted into each law's unit.  The state they build is described with the v5 representation
   (prot_repr5.v): the harness writes only the fields noise.c reads. *)
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
Require Import WgNoise.proof.protocol5.prot_repr5.
Require Import WgNoise.proof.protocol5.prot_specs5.
Require WgNoise.contracts.hs_reject_initiation.
Require WgNoise.harness.hs_reject_initiation.code.
Local Open Scope logic.

Module H := WgNoise.harness.hs_reject_initiation.code.

(* the compspecs of the helpers' body proofs *)
Definition CSh : compspecs := WgNoise.contracts.hs_reject_initiation.Harness.CS.

Definition t_pair := Tstruct H._pair noattr.

(* ------------------------------------------------------------------------------------------------ *)
(* The model of the pair of devices new_pair builds                                                 *)
(* ------------------------------------------------------------------------------------------------ *)

(* the shim's state after any_clocks: boot clock b, real-time clock (rs, rn) *)
Definition shim_clocks (S: shim) (b rs rn: int64) : shim :=
  mkShim b rs rn (s_log S) (s_logprev S) (s_u32 S) (s_allocs S) (s_fails S) (s_frees S) (s_failnext S)
         (s_released S) (s_rlallow S).

(* a device of hs_laws.h: its identity, its public-key table and index table (dev and cookie checker are
   not represented by device_rep5: any values here) *)
Definition hs_dev (ID: identity) (ptab itab: val) : device :=
  mkDev nullval ID (mkChk zeros32 zeros32 zeros32 Int64.zero nullval) ptab itab.

(* a peer of hs_laws.h's new_peer: device wg, one reference, no keypairs, handshake H, next in the public-key
   chain pknext (last_sent_handshake, cookie and internal id are not represented by peer_rep5) *)
Definition hs_peer0 (wg: val) (H: handshake) (pknext: val) : peer :=
  mkPeer wg false nullval nullval nullval H Int64.zero cookie_zero Int.one Int64.zero pknext.

(* an index table with one entry in its pool, the unhashed handshake entry of the peer at pa *)
Definition hs_table (sh: share) (pa: val) : tstate :=
  mkT [(hs_addr pa, sh, mkEntry pa IDX_HANDSHAKE Int.zero)] [].

Section Pair.
Variable x25519: list byte -> list byte -> list byte.

(* the identity set from a private key raw over a zeroed public key (new_device) *)
Definition hs_id (raw: list byte) : identity := identity_of x25519 (mkId zeros32 zeros32 false) raw.

(* the addresses of the members of struct pair at p *)
Definition pair_a (p: val) : val := @field_address CSh t_pair [StructField H._a] p.
Definition pair_b (p: val) : val := @field_address CSh t_pair [StructField H._b] p.
Definition pair_ai (p: val) : val := @field_address CSh t_pair [StructField H._a_indices] p.
Definition pair_bi (p: val) : val := @field_address CSh t_pair [StructField H._b_indices] p.
Definition pair_ak (p: val) : val := @field_address CSh t_pair [StructField H._a_keys] p.
Definition pair_bk (p: val) : val := @field_address CSh t_pair [StructField H._b_keys] p.
Definition pair_ap (p: val) : val := @field_address CSh t_pair [StructField H._a_peer] p.
Definition pair_bp (p: val) : val := @field_address CSh t_pair [StructField H._b_peer] p.

(* the devices and peers of new_pair with private keys araw, braw and preshared key psk *)
Definition pair_devA (p: val) (araw: list byte) : device := hs_dev (hs_id araw) (pair_ak p) (pair_ai p).
Definition pair_devB (p: val) (braw: list byte) : device := hs_dev (hs_id braw) (pair_bk p) (pair_bi p).
Definition pair_peerA (p: val) (araw braw psk: list byte) : peer :=
  hs_peer0 (pair_a p) (hs_initial x25519 (hs_id araw) (id_addr (pair_a p)) (id_pub (hs_id braw)) psk) nullval.
Definition pair_peerB (p: val) (araw braw psk: list byte) : peer :=
  hs_peer0 (pair_b p) (hs_initial x25519 (hs_id braw) (id_addr (pair_b p)) (id_pub (hs_id araw)) psk) nullval.

(* struct pair at p after new_pair: A and B, each with its tables, A's peer for B (a_peer) in A's tables, B's
   peer for A (b_peer) in B's *)
Definition hs_pair (sh: share) (p: val) (araw braw psk: list byte) : mpred :=
  !! (@field_compatible CSh t_pair [] p) &&
  (device_rep5 sh (pair_a p) (pair_devA p araw) *
   device_rep5 sh (pair_b p) (pair_devB p braw) *
   itable sh (pair_ai p) (hs_table sh (pair_ap p)) *
   itable sh (pair_bi p) (hs_table sh (pair_bp p)) *
   ptable sh (pair_ak p) (pair_ap p) *
   ptable sh (pair_bk p) (pair_bp p) *
   peer_rep5 sh (pair_ap p) (pair_peerA p araw braw psk) *
   peer_rep5 sh (pair_bp p) (pair_peerB p araw braw psk)).

End Pair.

(* ------------------------------------------------------------------------------------------------ *)
(* A copy of a peer's state (hs_unchanged.h's copy_peer)                                             *)
(* ------------------------------------------------------------------------------------------------ *)

Section Snap.
#[local] Existing Instance Noise.CS.

(* struct wg_peer at q holding copy_peer's copy of a peer in state P whose handshake entry is E (with list
   fields next, hashed); the fields copy_peer does not copy are any.  The padding is owned (after is_dead, after
   the keypairs' lock, in the handshake, at the end), so that the copy is again data_at_ of the struct. *)
Definition snap_rep (sh: share) (q: val) (P: peer) (E: entry) (next: val) (hashed: bool) : mpred :=
  let H := p_hs P in
  !! (field_compatible t_peer [] q /\ hs_ok H) &&
  (field_at_ sh t_peer (DOT I._device) q *
   field_at_ sh t_peer (DOT I._is_dead) q *
   field_at sh t_peer (DOT I._keypairs DOT I._current_keypair) (p_cur P) q *
   field_at sh t_peer (DOT I._keypairs DOT I._previous_keypair) (p_prev P) q *
   field_at sh t_peer (DOT I._keypairs DOT I._next_keypair) (p_next P) q *
   field_at_ sh t_peer (DOT I._keypairs DOT I._keypair_update_lock) q *
   field_at sh t_peer (DOT I._handshake DOT I._entry) (entry_val E next hashed) q *
   field_at sh t_peer (DOT I._handshake DOT I._state) (Vint (hs_state H)) q *
   field_at sh t_peer (DOT I._handshake DOT I._last_initiation_consumption) (Vlong (hs_lic H)) q *
   field_at sh t_peer (DOT I._handshake DOT I._static_identity) (hs_sid H) q *
   field_at sh t_peer (DOT I._handshake DOT I._ephemeral_private) (bytes (hs_eph H)) q *
   field_at sh t_peer (DOT I._handshake DOT I._remote_static) (bytes (hs_rstatic H)) q *
   field_at sh t_peer (DOT I._handshake DOT I._remote_ephemeral) (bytes (hs_reph H)) q *
   field_at sh t_peer (DOT I._handshake DOT I._precomputed_static_static) (bytes (hs_ss H)) q *
   field_at sh t_peer (DOT I._handshake DOT I._preshared_key) (bytes (hs_psk H)) q *
   field_at sh t_peer (DOT I._handshake DOT I._hash) (bytes (hs_hash H)) q *
   field_at sh t_peer (DOT I._handshake DOT I._chaining_key) (bytes (hs_ck H)) q *
   field_at sh t_peer (DOT I._handshake DOT I._latest_timestamp) (bytes (hs_ts H)) q *
   field_at sh t_peer (DOT I._handshake DOT I._remote_index) (Vint (hs_rindex H)) q *
   field_at_ sh t_peer (DOT I._handshake DOT I._lock) q *
   field_at_ sh t_peer (DOT I._last_sent_handshake) q *
   field_at_ sh t_peer (DOT I._latest_cookie) q *
   field_at sh t_peer (DOT I._refcount) (Vint (p_refs P)) q *
   field_at_ sh t_peer (DOT I._internal_id) q *
   field_at_ sh t_peer (DOT I._pubkey_next) q *
   spacer sh 9 16 q * spacer sh (OFS_PEER_KEYPAIRS + 28) (OFS_PEER_KEYPAIRS + 32) q *
   spacer sh (OFS_PEER_HANDSHAKE + 36) (OFS_PEER_HANDSHAKE + 40) q *
   spacer sh (OFS_PEER_HANDSHAKE + 300) (OFS_PEER_HANDSHAKE + 304) q * spacer sh 476 480 q).

End Snap.

(* ------------------------------------------------------------------------------------------------ *)
(* The specifications                                                                               *)
(* ------------------------------------------------------------------------------------------------ *)

Section Specs.
Variable x25519: list byte -> list byte -> list byte.
#[local] Existing Instance CSh.

(* any_u64(): any value *)
Definition any_u64_spec :=
  DECLARE H._any_u64
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tulong ] EX v: int64, PROP () RETURN (Vlong v) SEP ().

(* bytes_eq(a, b, n): 1 if a[0..n-1] = b[0..n-1], else 0 *)
Definition bytes_eq_spec :=
  DECLARE H._bytes_eq
  WITH sha: share, a: val, la: list byte, shb: share, b: val, lb: list byte
  PRE [ tptr tuchar, tptr tuchar, tulong ]
    PROP (readable_share sha; readable_share shb; Zlength la = Zlength lb; Zlength la <= Int64.max_unsigned)
    PARAMS (a; b; Vlong (Int64.repr (Zlength la)))
    SEP (bytes_at sha la a; bytes_at shb lb b)
  POST [ tint ]
    PROP () RETURN (Vint (if bytes_eqb la lb then Int.one else Int.zero))
    SEP (bytes_at sha la a; bytes_at shb lb b).

(* any_clocks(): any boot clock below 2^62 ns, any real-time clock with nanoseconds below 10^9 *)
Definition any_clocks_spec :=
  DECLARE H._any_clocks
  WITH gv: globals, S: shim, w: list int64
  PRE [ ] PROP () PARAMS () GLOBALS (gv) SEP (shim_state4 gv S w)
  POST [ tvoid ] EX b: int64, EX rs: int64, EX rn: int64,
    PROP (Int64.unsigned b < 2 ^ 62; 0 <= Int64.signed rn < 1000000000) RETURN ()
    SEP (shim_state4 gv (shim_clocks S b rs rn) w).

(* new_device(wg, indices, keys, private_key): empty tables, the identity set from the private key *)
Definition new_device_spec :=
  DECLARE H._new_device
  WITH gv: globals, sh: share, wg: val, ti: val, tk: val, shk: share, pk: val, raw: list byte
  PRE [ tptr t_dev, tptr t_itab, tptr t_ptab, tptr tuchar ]
    PROP (writable_share sh; readable_share shk; Zlength raw = 32) PARAMS (wg; ti; tk; pk) GLOBALS (gv)
    SEP (@data_at_ Noise.CS sh t_dev wg; @data_at_ Noise.CS sh t_itab ti; @data_at_ Noise.CS sh t_ptab tk;
         bytes_at shk raw pk; wg_consts5 gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (device_rep5 sh wg (hs_dev (hs_id x25519 raw) tk ti); @data_at Noise.CS sh t_itab nullval ti;
         ptable sh tk nullval; bytes_at shk raw pk; wg_consts5 gv).

(* new_peer(peer, wg, public_key, psk): the peer of hs_peer0 with the initial handshake, at the head of the
   device's public-key table (whose old head, a pointer or NULL, becomes its pubkey_next), its handshake entry
   unhashed *)
Definition new_peer_spec :=
  DECLARE H._new_peer
  WITH gv: globals, sh: share, peer: val, shd: share, wg: val, D: device, sht: share, head: val,
       shk: share, pubp: val, pub: list byte, shq: share, pskp: val, psk: list byte
  PRE [ tptr t_peer, tptr t_dev, tptr tuchar, tptr tuchar ]
    PROP (writable_share sh; readable_share shd; writable_share sht; readable_share shk; readable_share shq;
          is_pointer_or_null head; Zlength pub = 32; Zlength psk = 32)
    PARAMS (peer; wg; pubp; pskp) GLOBALS (gv)
    SEP (@data_at_ Noise.CS sh t_peer peer; device_rep5 shd wg D; ptable sht (d_ptab D) head;
         bytes_at shk pub pubp; bytes_at shq psk pskp; wg_consts5 gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (peer_rep5 sh peer (hs_peer0 wg (hs_initial x25519 (d_id D) (id_addr wg) pub psk) head);
         entry_out sh (hs_addr peer) (mkEntry peer IDX_HANDSHAKE Int.zero);
         device_rep5 shd wg D; ptable sht (d_ptab D) peer;
         bytes_at shk pub pubp; bytes_at shq psk pskp; wg_consts5 gv).

(* new_pair(p): any private keys, any preshared key (nondet_bytes), noise.c's globals initialised *)
Definition new_pair_spec :=
  DECLARE H._new_pair
  WITH gv: globals, sh: share, p: val, h: list byte, ck: list byte, kc: int64
  PRE [ tptr t_pair ]
    PROP (writable_share sh) PARAMS (p) GLOBALS (gv)
    SEP (data_at_ sh t_pair p; noise_globals_raw gv h ck kc; wg_consts5 gv)
  POST [ tvoid ] EX araw: list byte, EX braw: list byte, EX psk: list byte,
    PROP (Zlength araw = 32; Zlength braw = 32; Zlength psk = 32) RETURN ()
    SEP (hs_pair x25519 sh p araw braw psk; noise_globals gv kc; wg_consts5 gv).

(* copy_peer(to, from): to holds snap_rep of from's state.  The pointers it copies pass through temporaries,
   so they must be pointers or NULL (a load of an undefined pointer is stuck) *)
Definition copy_peer_spec :=
  DECLARE H._copy_peer
  WITH shq: share, q: val, shp: share, p: val, P: peer, she: share, E: entry, next: val, hashed: bool
  PRE [ tptr t_peer, tptr t_peer ]
    PROP (writable_share shq; readable_share shp; readable_share she;
          is_pointer_or_null (e_peer E); is_pointer_or_null next; is_pointer_or_null (hs_sid (p_hs P));
          is_pointer_or_null (p_cur P); is_pointer_or_null (p_prev P); is_pointer_or_null (p_next P))
    PARAMS (q; p)
    SEP (@data_at_ Noise.CS shq t_peer q; peer_rep5 shp p P; entry_at she (hs_addr p) E next hashed)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (snap_rep shq q P E next hashed; peer_rep5 shp p P; entry_at she (hs_addr p) E next hashed).

(* same_peer(p, q) on a peer and an equal copy of it: nonzero.  The pointers it compares must be valid or
   NULL: the entry's peer is p, its next is NULL, the keypair slots are NULL, the static identity pointer
   is held (identity_rep) *)
Definition same_peer_spec :=
  DECLARE H._same_peer
  WITH shp: share, p: val, P: peer, she: share, E: entry, hashed: bool, shq: share, q: val,
       shi: share, ID: identity
  PRE [ tptr t_peer, tptr t_peer ]
    PROP (readable_share shp; readable_share she; readable_share shq; readable_share shi;
          e_peer E = p; p_cur P = nullval; p_prev P = nullval; p_next P = nullval)
    PARAMS (p; q)
    SEP (peer_rep5 shp p P; entry_at she (hs_addr p) E nullval hashed; snap_rep shq q P E nullval hashed;
         identity_rep shi (hs_sid (p_hs P)) ID)
  POST [ tint ] EX r: int,
    PROP (r <> Int.zero) RETURN (Vint r)
    SEP (peer_rep5 shp p P; entry_at she (hs_addr p) E nullval hashed; snap_rep shq q P E nullval hashed;
         identity_rep shi (hs_sid (p_hs P)) ID).

End Specs.
