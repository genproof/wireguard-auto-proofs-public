(* the PURE
   model of the whole-state helpers of harness/common.h (pr_snap, dev_snap, shim_snap, struct kent,
   hs_same_but_next, skb_snap, replay_counter_fresh, peer_randomize_rest, kents_add's draws).

   Every snapshot is modelled by the protocol record it copies (prot_model3.v): a pr_snap by a `peer` (its handshake
   and reference count ignored), a dev_snap by a `device` and the public-key table's first peer, a shim_snap by a
   `shim` (four counters) and the warnings `w` (prot_repr4.v), a kent's snapshot by `ksnap` (its entry, list fields
   and keypair).  Comparisons are boolean functions of the snapshot and the current state; the C's pointer
   comparisons are value equalities (`veqb`) under the specifications' valid-pointer conditions (`vp_ok`). *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_model3.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

Definition veqb (x y: val) : bool := if eq_dec x y then true else false.

(* a pointer compared by the C: NULL or one of the addresses `own` whose memory the specification's SEP holds
   (its own objects and the objects the caller lends it: hc4_specs.v's vobj) *)
Definition vp_ok (own: list val) (x: val) : Prop := x = nullval \/ In x own.

(* ------------------------------------------------------------------------------------------------ *)
(* pr_snap: the rest of a peer                                                                      *)
(* ------------------------------------------------------------------------------------------------ *)

(* pr_same_but_cookie(s, p) / pr_same(s, p), the snapshot being the peer P0's rest *)
Definition pr_eqb_nc (P0 P: peer) : bool :=
  veqb (p_device P0) (p_device P) && Bool.eqb (p_dead P0) (p_dead P) &&
  veqb (p_cur P0) (p_cur P) && veqb (p_prev P0) (p_prev P) && veqb (p_next P0) (p_next P) &&
  Int64.eq (p_lsh P0) (p_lsh P) && Int64.eq (p_id P0) (p_id P) && veqb (p_pknext P0) (p_pknext P).
Definition pr_eqb (P0 P: peer) : bool := pr_eqb_nc P0 P && cookie_eqb (p_cookie P0) (p_cookie P).

(* the pointers pr_same compares (snapshot and current) *)
Definition pr_ptrs (P0 P: peer) : list val :=
  [p_device P0; p_device P; p_cur P0; p_cur P; p_prev P0; p_prev P; p_next P0; p_next P;
   p_pknext P0; p_pknext P].

(* peer_randomize_rest(p): dead flag, last sent handshake, cookie validity, birthdate, cookie, have_sent_mac1,
   last_mac1_sent drawn; the cookie keys stay *)
Definition p_rest_randomized (P: peer) (dead: bool) (lsh: int64) (valid: bool) (birth: int64) (ck: list byte)
  (sent: bool) (mac1: list byte) : peer :=
  let C := p_cookie P in
  mkPeer (p_device P) dead (p_cur P) (p_prev P) (p_next P) (p_hs P) lsh
         (mkCookie birth valid ck sent mac1 (ck_dkey C) (ck_mkey C)) (p_refs P) (p_id P) (p_pknext P).

(* ------------------------------------------------------------------------------------------------ *)
(* dev_snap: a device and its public-key table's first peer                                        *)
(* ------------------------------------------------------------------------------------------------ *)

Definition dev_eqb (D0: device) (h0: val) (D: device) (h: val) : bool :=
  veqb (d_dev D0) (d_dev D) &&
  bytes_eqb (id_pub (d_id D0)) (id_pub (d_id D)) && bytes_eqb (id_priv (d_id D0)) (id_priv (d_id D)) &&
  Bool.eqb (id_has (d_id D0)) (id_has (d_id D)) &&
  bytes_eqb (cc_secret (d_cc D0)) (cc_secret (d_cc D)) && Int64.eq (cc_birth (d_cc D0)) (cc_birth (d_cc D)) &&
  bytes_eqb (cc_ekey (d_cc D0)) (cc_ekey (d_cc D)) && bytes_eqb (cc_mkey (d_cc D0)) (cc_mkey (d_cc D)) &&
  veqb (cc_dev (d_cc D0)) (cc_dev (d_cc D)) && veqb (d_ptab D0) (d_ptab D) && veqb (d_itab D0) (d_itab D) &&
  veqb h0 h.

Definition dev_ptrs (D0: device) (h0: val) (D: device) (h: val) : list val :=
  [d_dev D0; d_dev D; cc_dev (d_cc D0); cc_dev (d_cc D); d_ptab D0; d_ptab D; d_itab D0; d_itab D; h0; h].

(* ------------------------------------------------------------------------------------------------ *)
(* shim_snap: the allocation / release counters and the refcount_t warnings                        *)
(* ------------------------------------------------------------------------------------------------ *)

Definition warn_eqb (w0 w: list int64) : bool :=
  forallb (fun i => Int64.eq (Znth i w0) (Znth i w)) [0; 1; 2; 3; 4].
Definition shim_eqb (S0: shim) (w0: list int64) (S: shim) (w: list int64) : bool :=
  Int64.eq (s_allocs S0) (s_allocs S) && Int64.eq (s_fails S0) (s_fails S) &&
  Int64.eq (s_frees S0) (s_frees S) && Int64.eq (s_released S0) (s_released S) && warn_eqb w0 w.

(* ------------------------------------------------------------------------------------------------ *)
(* handshake snapshots: the current snapshot of p's handshake, hs_same_but_next                     *)
(* ------------------------------------------------------------------------------------------------ *)

(* the entry at a of T's pool (a default if there is none: the specifications require one) *)
Definition t_entry_d (T: tstate) (a: val) : entry :=
  match t_entry T a with Some E => E | None => mkEntry Vundef Int.zero Int.zero end.

(* what hs_take(s, &p->handshake) copies: p's handshake entry (from the pool of T) and handshake *)
Definition hs_snap_cur (T: tstate) (p: val) (P: peer) : hsnap :=
  snap_of T (hs_addr p) (t_entry_d T (hs_addr p)) (p_hs P).

(* hs_same_but_next(s, h): hs_same but the entry's list link *)
Definition snap_eqb_nn (s c: hsnap) : bool :=
  entry_eqb (sn_entry s) (sn_entry c) && Bool.eqb (sn_hashed s) (sn_hashed c) && hs_eqb (sn_hs s) (sn_hs c).

(* the pointers hs_same compares; hs_zeroed_from / hs_same_but_next compare all but the links *)
Definition hs_ptrs_nn (sn c: hsnap) : list val :=
  [e_peer (sn_entry sn); e_peer (sn_entry c); hs_sid (sn_hs sn); hs_sid (sn_hs c)].
Definition hs_ptrs (sn c: hsnap) : list val := sn_next sn :: sn_next c :: hs_ptrs_nn sn c.

(* ------------------------------------------------------------------------------------------------ *)
(* skb_snap, replay_counter_fresh                                                                   *)
(* ------------------------------------------------------------------------------------------------ *)

Definition skb_eqb (s0 s: skb) : bool :=
  veqb (sk_data s0) (sk_data s) && Int.eq (sk_len s0) (sk_len s) && Z.eqb (sk_proto s0) (sk_proto s) &&
  bytes_eqb (sk_ip4 s0) (sk_ip4 s) && bytes_eqb (sk_ip6 s0) (sk_ip6 s) && bytes_eqb (sk_port s0) (sk_port s).

(* le32_load(p) of the bytes bs = b0 b1 b2 b3 *)
Definition le32_val (bs: list byte) : int :=
  Int.repr (Byte.unsigned (Znth 0 bs) + Byte.unsigned (Znth 1 bs) * 2 ^ 8 + Byte.unsigned (Znth 2 bs) * 2 ^ 16 +
            Byte.unsigned (Znth 3 bs) * 2 ^ 24).

Definition rc_fresh (rc: int64) (bt: list int64) : bool :=
  Int64.eq rc Int64.zero && forallb (fun x => Int64.eq x Int64.zero) bt.

(* ------------------------------------------------------------------------------------------------ *)
(* struct kent: a keypair object of any content (its entry in the index table's pool) and a snapshot *)
(* ------------------------------------------------------------------------------------------------ *)

(* the snapshot fields peer0 .. id0: the entry (peer, type, index), its links (next, hashed), the keypair *)
Record ksnap := mkKs { ks_E: entry; ks_next: val; ks_hashed: bool; ks_K: keypair }.

Definition symkey_eqb (A B: symkey) : bool :=
  bytes_eqb (sk_key A) (sk_key B) && Int64.eq (sk_birth A) (sk_birth B) && Bool.eqb (sk_valid A) (sk_valid B).

Fixpoint int64s_eqb (a b: list int64) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => Int64.eq x y && int64s_eqb a' b'
  | _, _ => false
  end.

(* every field of the keypair *)
Definition kp_eqb (K0 K: keypair) : bool :=
  symkey_eqb (kp_send K0) (kp_send K) && symkey_eqb (kp_recv K0) (kp_recv K) &&
  Int64.eq (kp_scounter K0) (kp_scounter K) && Int64.eq (kp_rcounter K0) (kp_rcounter K) &&
  Int.eq (kp_rindex K0) (kp_rindex K) && Bool.eqb (kp_init K0) (kp_init K) && Int.eq (kp_refs K0) (kp_refs K) &&
  Int64.eq (kp_id K0) (kp_id K) && int64s_eqb (kp_backtrack K0) (kp_backtrack K).

(* kent_same_but_next(l): the current entry E, hashed-ness and keypair K against the snapshot *)
Definition kent_eqb_nn (s: ksnap) (E: entry) (hashed: bool) (K: keypair) : bool :=
  entry_eqb (ks_E s) E && Bool.eqb (ks_hashed s) hashed && kp_eqb (ks_K s) K.

(* a kent in the list: its address (= its keypair's = its entry's), its keypair, its snapshot (None: not yet
   taken, the fields undefined) *)
Record kent4 := mkKe { ke_addr: val; ke_K: keypair; ke_snap: option ksnap }.

(* kents_snap(l) *)
Definition kent_snapped (T: tstate) (e: kent4) : kent4 :=
  let k := ke_addr e in
  mkKe k (ke_K e) (Some (mkKs (t_entry_d T k) (succ_in (t_L T) k) (vin k (t_L T)) (ke_K e))).

(* kent_same_but_next(l) / kents_same(l) / kents_same_but_next(l, t): the current entry from the pool of T *)
Definition kent_eqb_cur (T: tstate) (e: kent4) : bool :=
  let k := ke_addr e in
  match ke_snap e with
  | Some s => kent_eqb_nn s (t_entry_d T k) (vin k (t_L T)) (ke_K e)
  | None => false
  end.
Definition kent_same (T: tstate) (e: kent4) : bool :=
  let k := ke_addr e in
  match ke_snap e with
  | Some s => kent_eqb_cur T e && veqb (ks_next s) (succ_in (t_L T) k)
  | None => false
  end.
Definition kent_same_bn (T: tstate) (e: kent4) : bool :=
  let k := ke_addr e in
  match ke_snap e with
  | Some s => kent_eqb_cur T e && (negb (ks_hashed s) || vin k (t_L T))
  | None => false
  end.
Definition kents_hashed_n (T: tstate) (KE: list kent4) : Z :=
  Zlength (filter (fun e => vin (ke_addr e) (t_L T)) KE).

(* the pointers kents_same compares for a kent *)
Definition kent_ptrs (T: tstate) (e: kent4) : list val :=
  match ke_snap e with
  | Some s => [e_peer (ks_E s); e_peer (t_entry_d T (ke_addr e)); ks_next s; succ_in (t_L T) (ke_addr e)]
  | None => []
  end.
Definition kent_ptrs_nn (T: tstate) (e: kent4) : list val :=
  match ke_snap e with
  | Some s => [e_peer (ks_E s); e_peer (t_entry_d T (ke_addr e))]
  | None => []
  end.

(* kents_add's draws, in LIST order (the head = the last one created): the kent's address, its owner (a peer),
   its keypair, the index the table drew for it, and the slot it may fill (0 current, 1 previous, 2 next, 3 none) *)
Record kdraw := mkKD { kd_addr: val; kd_owner: val; kd_K: keypair; kd_idx: int; kd_slot: Z }.

Definition kd_kent (d: kdraw) : kent4 := mkKe (kd_addr d) (kd_K d) None.

(* the entry of a new kent before its insertion (wg_index_hashtable_insert of a raw entry: raw_add) *)
Definition kd_entry (d: kdraw) : entry := mkEntry (kd_owner d) IDX_KEYPAIR Int.zero.

(* the table after the inserts (the first created first) *)
Fixpoint kents_T (T: tstate) (KD: list kdraw) : tstate :=
  match KD with
  | [] => T
  | d :: KD' => t_insert (t_add (kents_T T KD') (kd_addr d) Ews (kd_entry d)) (kd_addr d) (kd_idx d)
  end.

(* each drawn index was fresh when it was inserted *)
Fixpoint kents_fresh (T: tstate) (KD: list kdraw) : Prop :=
  match KD with
  | [] => True
  | d :: KD' => kents_fresh T KD' /\ t_fresh (t_add (kents_T T KD') (kd_addr d) Ews (kd_entry d)) (kd_addr d) (kd_idx d)
  end.

(* the shim after the inserts: the last draw is logged *)
Definition kents_S (S: shim) (KD: list kdraw) : shim :=
  match KD with [] => S | d :: _ => shim_u32 S (kd_idx d) end.

(* with fill: the owner's slot c takes the keypair k if it was empty *)
Definition fill_slot (P: peer) (k: val) (c: Z) : peer :=
  if Z.eq_dec c 0 then (if eq_dec (p_cur P) nullval then p_set_slots P k (p_prev P) (p_next P) else P)
  else if Z.eq_dec c 1 then (if eq_dec (p_prev P) nullval then p_set_slots P (p_cur P) k (p_next P) else P)
  else if Z.eq_dec c 2 then (if eq_dec (p_next P) nullval then p_set_slots P (p_cur P) (p_prev P) k else P)
  else P.

Definition fill_peers (PS: list (val * share * peer)) (d: kdraw) : list (val * share * peer) :=
  map (fun x => match x with (a, sh, P) =>
         if eq_dec a (kd_owner d) then (a, sh, fill_slot P (kd_addr d) (kd_slot d)) else (a, sh, P) end) PS.

Fixpoint kents_PS (fill: bool) (PS: list (val * share * peer)) (KD: list kdraw) : list (val * share * peer) :=
  match KD with
  | [] => PS
  | d :: KD' => if fill then fill_peers (kents_PS fill PS KD') d else kents_PS fill PS KD'
  end.

(* the drawn keypair: any keys, validity, counters, backtrack, remote index, role, id; birthdates below 2^62
   (draw_boottime); a reference count of draw_peer_refs (1 .. INT_MAX - 1) *)
Definition kd_K_ok (K: keypair) : Prop :=
  Zlength (sk_key (kp_send K)) = 32 /\ Zlength (sk_key (kp_recv K)) = 32 /\ Zlength (kp_backtrack K) = 128 /\
  0 <= Int64.unsigned (sk_birth (kp_send K)) < 2 ^ 62 /\ 0 <= Int64.unsigned (sk_birth (kp_recv K)) < 2 ^ 62 /\
  0 < Int.unsigned (kp_refs K) < 2147483647.

Definition peer_addr4 (x: val * share * peer) : val := match x with (a, _, _) => a end.

Definition kents_draws_ok (PS: list (val * share * peer)) (KD: list kdraw) : Prop :=
  Forall (fun d => In (kd_owner d) (map peer_addr4 PS) /\ kd_K_ok (kd_K d) /\ 0 <= kd_slot d <= 3) KD /\
  NoDup (map kd_addr KD).
