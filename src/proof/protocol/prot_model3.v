(* The protocol model: the abstract state of the WireGuard handshake as the C code
   (drivers/net/wireguard/noise.c, cookie.c, patch/wg_shim.c) implements it, and every step as a Coq function
   that follows the C statement by statement (where it stops, what it has written so far).

   Plain Coq over VST's value types; no separation logic here (representation: prot_repr.v, specifications:
   prot_specs_*.v).  Parameterised (Section) by the functional models of the primitives (prim_api.v):
   x25519, aead_enc/aead_dec (ChaCha20-Poly1305, 64-bit nonce), xaead_enc/xaead_dec (XChaCha20-Poly1305).
   BLAKE2s is the concrete model `blake2s key outlen msg` of src/proof/blake2s/model.v.

   Conventions: byte buffers are `list byte`; u32 fields are `int`, u64/s64 fields `int64` (exact machine
   values, no range side conditions); pointers are `val`; bool fields `bool`. *)
Require Import VST.floyd.proofauto.
Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import WgNoise.proof.blake2s.model.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.libc.spec.

Local Open Scope Z_scope.

(* ------------------------------------------------------------------------------------------------ *)
(* Constants                                                                                        *)
(* ------------------------------------------------------------------------------------------------ *)

Definition str_bytes (s: string) : list byte :=
  map (fun c => Byte.repr (Z.of_nat (nat_of_ascii c))) (list_ascii_of_string s).

Definition handshake_name : list byte := str_bytes "Noise_IKpsk2_25519_ChaChaPoly_BLAKE2s".   (* 37 *)
Definition identifier_name : list byte := str_bytes "WireGuard v1 zx2c4 Jason@zx2c4.com".     (* 34 *)
Definition mac1_label : list byte := str_bytes "mac1----".
Definition cookie_label : list byte := str_bytes "cookie--".

(* enum noise_handshake_state *)
Definition HS_ZEROED := Int.repr 0.
Definition HS_CREATED_INITIATION := Int.repr 1.
Definition HS_CONSUMED_INITIATION := Int.repr 2.
Definition HS_CREATED_RESPONSE := Int.repr 3.
Definition HS_CONSUMED_RESPONSE := Int.repr 4.

(* enum index_hashtable_type *)
Definition IDX_HANDSHAKE := Int.repr 1.
Definition IDX_KEYPAIR := Int.repr 2.

(* enum cookie_mac_state *)
Definition INVALID_MAC := 0.
Definition VALID_MAC_BUT_NO_COOKIE := 1.
Definition VALID_MAC_WITH_COOKIE_BUT_RATELIMITED := 2.
Definition VALID_MAC_WITH_COOKIE := 3.

Definition NSEC_PER_SEC := 1000000000.

(* ------------------------------------------------------------------------------------------------ *)
(* Byte helpers                                                                                     *)
(* ------------------------------------------------------------------------------------------------ *)

Definition zeros (n: Z) : list byte := Zrepeat Byte.zero n.

(* put_unaligned_be32 / be64 *)
Definition be32 (v: int) : list byte :=
  map (fun k => Byte.repr (Int.unsigned v / 2 ^ (8 * k))) [3; 2; 1; 0].
Definition be64 (v: int64) : list byte :=
  be32 (Int.repr (Int64.unsigned v / 2 ^ 32)) ++ be32 (Int.repr (Int64.unsigned v)).
(* little-endian image of a u32 (the message structs as bytes: x86_64) *)
Definition le32 (v: int) : list byte :=
  map (fun k => Byte.repr (Int.unsigned v / 2 ^ (8 * k))) [0; 1; 2; 3].

Definition bytes_eqb (a b: list byte) : bool := if list_eq_dec Byte.eq_dec a b then true else false.
Definition is_zero (a: list byte) : bool := bytes_eqb a (zeros (Zlength a)).

(* (s64)a <= (s64)b and friends: signed comparisons of u64 values *)
Definition s64_le (a b: int64) : bool := negb (Int64.lt b a).

(* ------------------------------------------------------------------------------------------------ *)
(* The shim's state (patch/wg_shim.c globals)                                                       *)
(* ------------------------------------------------------------------------------------------------ *)

Record shim := mkShim {
  s_boot: int64;          (* wg_shim_boottime_ns *)
  s_rsec: int64;          (* wg_shim_real_sec (s64) *)
  s_rnsec: int64;         (* wg_shim_real_nsec (long) *)
  s_log: list byte;       (* wg_shim_random_log[32] *)
  s_logprev: list byte;   (* wg_shim_random_log_prev[32] *)
  s_u32: int;             (* wg_shim_random_u32 *)
  s_allocs: int64;        (* wg_shim_allocs (unsigned long) *)
  s_fails: int64;         (* wg_shim_alloc_failures *)
  s_frees: int64;         (* wg_shim_frees *)
  s_failnext: bool;       (* wg_shim_fail_next_alloc *)
  s_released: int64;      (* wg_shim_peer_released *)
  s_rlallow: bool         (* wg_shim_ratelimit_allow *)
}.

Definition shim_ok (S: shim) : Prop := Zlength (s_log S) = 32 /\ Zlength (s_logprev S) = 32.

(* get_random_bytes(buf, len) with the drawn bytes bs (|bs| = len): the log keeps the first 32 bytes *)
Definition shim_draw (S: shim) (bs: list byte) : shim :=
  let n := Z.min (Zlength bs) 32 in
  mkShim (s_boot S) (s_rsec S) (s_rnsec S)
         (sublist 0 n bs ++ sublist n 32 (s_log S)) (s_log S)
         (s_u32 S) (s_allocs S) (s_fails S) (s_frees S) (s_failnext S) (s_released S) (s_rlallow S).

(* get_random_u32 drew n *)
Definition shim_u32 (S: shim) (n: int) : shim :=
  mkShim (s_boot S) (s_rsec S) (s_rnsec S) (s_log S) (s_logprev S)
         n (s_allocs S) (s_fails S) (s_frees S) (s_failnext S) (s_released S) (s_rlallow S).

(* kzalloc succeeded / failed *)
Definition shim_alloc_ok (S: shim) : shim :=
  mkShim (s_boot S) (s_rsec S) (s_rnsec S) (s_log S) (s_logprev S)
         (s_u32 S) (Int64.add (s_allocs S) Int64.one) (s_fails S) (s_frees S) (s_failnext S)
         (s_released S) (s_rlallow S).
Definition shim_alloc_fail (S: shim) : shim :=
  mkShim (s_boot S) (s_rsec S) (s_rnsec S) (s_log S) (s_logprev S)
         (s_u32 S) (s_allocs S) (Int64.add (s_fails S) Int64.one) (s_frees S) false
         (s_released S) (s_rlallow S).
(* kfree of a non-NULL pointer *)
Definition shim_free (S: shim) : shim :=
  mkShim (s_boot S) (s_rsec S) (s_rnsec S) (s_log S) (s_logprev S)
         (s_u32 S) (s_allocs S) (s_fails S) (Int64.add (s_frees S) Int64.one) (s_failnext S)
         (s_released S) (s_rlallow S).
(* wg_shim_peer_release *)
Definition shim_release (S: shim) : shim :=
  mkShim (s_boot S) (s_rsec S) (s_rnsec S) (s_log S) (s_logprev S)
         (s_u32 S) (s_allocs S) (s_fails S) (s_frees S) (s_failnext S)
         (Int64.add (s_released S) Int64.one) (s_rlallow S).

(* wg_birthdate_has_expired(birthday, seconds): (s64)(birthday + seconds * NSEC_PER_SEC) <= (s64)now *)
Definition birthdate_expired (birth secs now: int64) : bool :=
  s64_le (Int64.add birth (Int64.mul secs (Int64.repr NSEC_PER_SEC))) now.

(* ------------------------------------------------------------------------------------------------ *)
(* The objects                                                                                      *)
(* ------------------------------------------------------------------------------------------------ *)

(* struct noise_static_identity (the lock is not modelled: any value) *)
Record identity := mkId { id_pub: list byte; id_priv: list byte; id_has: bool }.

(* struct cookie_checker (lock: any) *)
Record checker := mkChk {
  cc_secret: list byte; cc_ekey: list byte; cc_mkey: list byte; cc_birth: int64; cc_dev: val }.

(* struct wg_device *)
Record device := mkDev {
  d_dev: val; d_id: identity; d_cc: checker; d_ptab: val; d_itab: val }.

(* struct index_hashtable_entry, without the list fields (next, hashed: they follow from the table) *)
Record entry := mkEntry { e_peer: val; e_type: int; e_index: int }.

(* struct noise_handshake, without its entry (the entry lives in the table's pool) and lock *)
Record handshake := mkHS {
  hs_state: int; hs_lic: int64; hs_sid: val;
  hs_eph: list byte; hs_rstatic: list byte; hs_reph: list byte; hs_ss: list byte; hs_psk: list byte;
  hs_hash: list byte; hs_ck: list byte; hs_ts: list byte; hs_rindex: int }.

(* struct cookie (lock: any) *)
Record cookie := mkCookie {
  ck_birth: int64; ck_valid: bool; ck_cookie: list byte; ck_sent: bool; ck_last_mac1: list byte;
  ck_dkey: list byte; ck_mkey: list byte }.

(* struct wg_peer (handshake without its entry; keypair_update_lock: any) *)
Record peer := mkPeer {
  p_device: val; p_dead: bool;
  p_cur: val; p_prev: val; p_next: val;       (* keypairs.current/previous/next_keypair *)
  p_hs: handshake;
  p_lsh: int64;                               (* last_sent_handshake.counter *)
  p_cookie: cookie;
  p_refs: int;                                (* refcount.refcount *)
  p_id: int64;
  p_pknext: val }.

(* struct noise_symmetric_key *)
Record symkey := mkSym { sk_key: list byte; sk_birth: int64; sk_valid: bool }.

(* struct noise_keypair without its entry (rcu, receiving_counter.lock: any) *)
Record keypair := mkKP {
  kp_send: symkey; kp_scounter: int64; kp_recv: symkey; kp_rcounter: int64; kp_backtrack: list int64;
  kp_rindex: int; kp_init: bool; kp_refs: int; kp_id: int64 }.

(* The index table of a device: the pool D of every entry that may be in the table (address, share,
   contents), and the table itself, the list L of the addresses in it, in list order.  An entry is hashed
   iff it is in L; its next field is its successor in L (NULL for the last and for unhashed entries). *)
Record tstate := mkT { t_D: list (val * share * entry); t_L: list val }.

(* messages *)
Record init_msg := mkIM {
  im_type: int; im_sender: int; im_eph: list byte; im_encs: list byte; im_enct: list byte;
  im_mac1: list byte; im_mac2: list byte }.
Record resp_msg := mkRM {
  rm_type: int; rm_sender: int; rm_receiver: int; rm_eph: list byte; rm_encn: list byte;
  rm_mac1: list byte; rm_mac2: list byte }.
Record cookie_msg := mkCM { cm_type: int; cm_receiver: int; cm_nonce: list byte; cm_enc: list byte }.

(* the byte images of the messages (x86_64, no padding: 148 / 92 / 64 bytes) *)
Definition init_bytes (m: init_msg) : list byte :=
  le32 (im_type m) ++ le32 (im_sender m) ++ im_eph m ++ im_encs m ++ im_enct m ++ im_mac1 m ++ im_mac2 m.
Definition resp_bytes (m: resp_msg) : list byte :=
  le32 (rm_type m) ++ le32 (rm_sender m) ++ le32 (rm_receiver m) ++ rm_eph m ++ rm_encn m ++
  rm_mac1 m ++ rm_mac2 m.
Definition cookie_msg_bytes (m: cookie_msg) : list byte :=
  le32 (cm_type m) ++ le32 (cm_receiver m) ++ cm_nonce m ++ cm_enc m.

(* struct sk_buff of the shim (quickproof_net.h); the message bytes at sk_data are separate *)
Record skb := mkSkb {
  sk_data: val; sk_len: int; sk_proto: Z (* u16 *); sk_ip4: list byte; sk_ip6: list byte;
  sk_port: list byte }.

(* ------------------------------------------------------------------------------------------------ *)
(* Record updates                                                                                   *)
(* ------------------------------------------------------------------------------------------------ *)

Definition hs_set_ckh (H: handshake) (ck h: list byte) : handshake :=
  mkHS (hs_state H) (hs_lic H) (hs_sid H) (hs_eph H) (hs_rstatic H) (hs_reph H) (hs_ss H) (hs_psk H)
       h ck (hs_ts H) (hs_rindex H).
Definition hs_set_eph (H: handshake) (e: list byte) : handshake :=
  mkHS (hs_state H) (hs_lic H) (hs_sid H) e (hs_rstatic H) (hs_reph H) (hs_ss H) (hs_psk H)
       (hs_hash H) (hs_ck H) (hs_ts H) (hs_rindex H).
Definition hs_set_state (H: handshake) (s: int) : handshake :=
  mkHS s (hs_lic H) (hs_sid H) (hs_eph H) (hs_rstatic H) (hs_reph H) (hs_ss H) (hs_psk H)
       (hs_hash H) (hs_ck H) (hs_ts H) (hs_rindex H).
Definition hs_set_ss (H: handshake) (ss: list byte) : handshake :=
  mkHS (hs_state H) (hs_lic H) (hs_sid H) (hs_eph H) (hs_rstatic H) (hs_reph H) ss (hs_psk H)
       (hs_hash H) (hs_ck H) (hs_ts H) (hs_rindex H).

(* handshake_zero *)
Definition hs_zero (H: handshake) : handshake :=
  mkHS HS_ZEROED (hs_lic H) (hs_sid H) (zeros 32) (hs_rstatic H) (zeros 32) (hs_ss H) (hs_psk H)
       (zeros 32) (zeros 32) (hs_ts H) Int.zero.

Definition p_set_hs (P: peer) (H: handshake) : peer :=
  mkPeer (p_device P) (p_dead P) (p_cur P) (p_prev P) (p_next P) H (p_lsh P) (p_cookie P) (p_refs P)
         (p_id P) (p_pknext P).
Definition p_set_refs (P: peer) (r: int) : peer :=
  mkPeer (p_device P) (p_dead P) (p_cur P) (p_prev P) (p_next P) (p_hs P) (p_lsh P) (p_cookie P) r
         (p_id P) (p_pknext P).
Definition p_set_cookie (P: peer) (c: cookie) : peer :=
  mkPeer (p_device P) (p_dead P) (p_cur P) (p_prev P) (p_next P) (p_hs P) (p_lsh P) c (p_refs P)
         (p_id P) (p_pknext P).
Definition p_set_slots (P: peer) (cur prev next: val) : peer :=
  mkPeer (p_device P) (p_dead P) cur prev next (p_hs P) (p_lsh P) (p_cookie P) (p_refs P)
         (p_id P) (p_pknext P).
Definition p_set_lsh (P: peer) (l: int64) : peer :=
  mkPeer (p_device P) (p_dead P) (p_cur P) (p_prev P) (p_next P) (p_hs P) l (p_cookie P) (p_refs P)
         (p_id P) (p_pknext P).

Definition kp_set_refs (K: keypair) (r: int) : keypair :=
  mkKP (kp_send K) (kp_scounter K) (kp_recv K) (kp_rcounter K) (kp_backtrack K) (kp_rindex K)
       (kp_init K) r (kp_id K).
Definition kp_invalidate_send (K: keypair) : keypair :=
  mkKP (mkSym (sk_key (kp_send K)) (sk_birth (kp_send K)) false) (kp_scounter K) (kp_recv K)
       (kp_rcounter K) (kp_backtrack K) (kp_rindex K) (kp_init K) (kp_refs K) (kp_id K).

(* association lists keyed by address *)
Section Assoc.
Context {A: Type}.
Fixpoint afind (l: list (val * A)) (a: val) : option A :=
  match l with
  | [] => None
  | (x, v) :: l' => if eq_dec x a then Some v else afind l' a
  end.
Fixpoint aupd (l: list (val * A)) (a: val) (v: A) : list (val * A) :=
  match l with
  | [] => []
  | (x, w) :: l' => if eq_dec x a then (x, v) :: l' else (x, w) :: aupd l' a v
  end.
Fixpoint adel (l: list (val * A)) (a: val) : list (val * A) :=
  match l with
  | [] => []
  | (x, w) :: l' => if eq_dec x a then l' else (x, w) :: adel l' a
  end.
End Assoc.

(* pool and peer lists carry a share: (address, share, contents) *)
Section Assoc3.
Context {A: Type}.
Fixpoint sfind (l: list (val * share * A)) (a: val) : option (share * A) :=
  match l with
  | [] => None
  | (x, sh, v) :: l' => if eq_dec x a then Some (sh, v) else sfind l' a
  end.
Fixpoint supd (l: list (val * share * A)) (a: val) (v: A) : list (val * share * A) :=
  match l with
  | [] => []
  | (x, sh, w) :: l' => if eq_dec x a then (x, sh, v) :: l' else (x, sh, w) :: supd l' a v
  end.
Fixpoint sdel (l: list (val * share * A)) (a: val) : list (val * share * A) :=
  match l with
  | [] => []
  | (x, sh, w) :: l' => if eq_dec x a then l' else (x, sh, w) :: sdel l' a
  end.
Definition saddrs (l: list (val * share * A)) : list val := map (fun '(x, _, _) => x) l.
End Assoc3.

Fixpoint vremove (a: val) (l: list val) : list val :=
  match l with [] => [] | x :: l' => if eq_dec x a then vremove a l' else x :: vremove a l' end.
Fixpoint vreplace (a b: val) (l: list val) : list val :=
  match l with [] => [] | x :: l' => if eq_dec x a then b :: l' else x :: vreplace a b l' end.
Definition vin (a: val) (l: list val) : bool := if in_dec eq_dec a l then true else false.
Fixpoint succ_in (L: list val) (a: val) : val :=
  match L with
  | [] => nullval
  | x :: L' => if eq_dec x a then hd nullval L' else succ_in L' a
  end.

(* ------------------------------------------------------------------------------------------------ *)
(* The index table (shim S15)                                                                       *)
(* ------------------------------------------------------------------------------------------------ *)

Definition t_entry (T: tstate) (a: val) : option entry :=
  match sfind (t_D T) a with Some (_, E) => Some E | None => None end.

Definition t_upd (T: tstate) (a: val) (E: entry) : tstate := mkT (supd (t_D T) a E) (t_L T).

(* the indices in use by the entries of a list of addresses *)
Definition t_indices (T: tstate) (L: list val) : list int :=
  map (fun a => match t_entry T a with Some E => e_index E | None => Int.zero end) L.

(* wg_index_hashtable_remove *)
Definition t_remove (T: tstate) (a: val) : tstate := mkT (t_D T) (vremove a (t_L T)).

(* wg_index_hashtable_insert with the drawn index idx (fresh: not an index of (t_L (t_remove T a))) *)
Definition t_set_index (T: tstate) (a: val) (idx: int) : tstate :=
  match t_entry T a with
  | Some E => t_upd T a (mkEntry (e_peer E) (e_type E) idx)
  | None => T
  end.
Definition t_insert (T: tstate) (a: val) (idx: int) : tstate :=
  let T1 := t_set_index T a idx in mkT (t_D T1) (a :: vremove a (t_L T1)).
Definition t_fresh (T: tstate) (a: val) (idx: int) : Prop :=
  ~ In idx (t_indices T (vremove a (t_L T))).

(* wg_index_hashtable_replace(old, new): (result, table) *)
Definition t_replace (T: tstate) (old new: val) : bool * tstate :=
  if vin old (t_L T) then
    let idx := match t_entry T old with Some E => e_index E | None => Int.zero end in
    (true, mkT (t_D (t_set_index T new idx)) (vreplace old new (t_L T)))
  else (false, T).

(* wg_index_hashtable_lookup: the first entry of the table with that index *)
Fixpoint t_find_index (T: tstate) (L: list val) (idx: int) : option (val * entry) :=
  match L with
  | [] => None
  | a :: L' =>
      match t_entry T a with
      | Some E => if Int.eq (e_index E) idx then Some (a, E) else t_find_index T L' idx
      | None => t_find_index T L' idx
      end
  end.

(* the entry found by lookup(mask, idx), if its type is in the mask *)
Definition t_lookup (T: tstate) (mask idx: int) : option (val * entry) :=
  match t_find_index T (t_L T) idx with
  | Some (a, E) => if Int.eq (Int.and (e_type E) mask) Int.zero then None else Some (a, E)
  | None => None
  end.

(* an entry leaves the pool (its memory is freed) *)
Definition t_free (T: tstate) (a: val) : tstate := mkT (sdel (t_D T) a) (vremove a (t_L T)).
(* an unhashed entry joins the pool *)
Definition t_add (T: tstate) (a: val) (sh: share) (E: entry) : tstate := mkT ((a, sh, E) :: t_D T) (t_L T).

(* ------------------------------------------------------------------------------------------------ *)
(* Peers                                                                                            *)
(* ------------------------------------------------------------------------------------------------ *)

(* kref is the kernel's refcount_t (patch/include/quickproof_kref.h; the functions
   wg_shim_refcount_inc_not_zero / _inc / _dec_and_test of wg_shim.c): the count is the bits of the
   kernel's int, read unsigned; `v < 0` of the kernel is rc_neg v.  An increment that finds a negative count or makes it negative, and a decrement that finds 0 or a
   negative count, SATURATE: the count becomes REFCOUNT_SATURATED and stays there (a warning is recorded in
   wg_shim_refcount_warn, which shim_state keeps existentially: the specifications do not track warnings).
   Below saturation these are the plain +1 / -1. *)
Definition rc_neg (v: int) : bool := negb (Int.ltu v (Int.repr 2147483648)).
Definition REFCOUNT_SATURATED : int := Int.repr 3221225472.
(* refcount_inc_not_zero / refcount_inc on a count that is not 0: the new count *)
Definition rc_add1 (r: int) : int :=
  if orb (rc_neg r) (rc_neg (Int.add r Int.one)) then REFCOUNT_SATURATED else Int.add r Int.one.
(* refcount_dec_and_test: the new count (0 exactly when r = 1, the release) *)
Definition rc_sub1 (r: int) : int :=
  if andb (negb (rc_neg r)) (Int.eq r Int.one) then Int.zero
  else if orb (Int.eq r Int.zero) (rc_neg r) then REFCOUNT_SATURATED
  else Int.sub r Int.one.

Lemma rc_add1_small (r: int) : Int.unsigned r < 2147483647 -> rc_add1 r = Int.add r Int.one.
Proof.
  intros H. pose proof (Int.unsigned_range r).
  assert (E: Int.unsigned (Int.add r Int.one) = Int.unsigned r + 1).
  { unfold Int.add. rewrite Int.unsigned_one, Int.unsigned_repr; [reflexivity | rep_lia]. }
  unfold rc_add1, rc_neg, Int.ltu. rewrite E, (Int.unsigned_repr 2147483648) by rep_lia.
  destruct (zlt (Int.unsigned r) 2147483648); [|lia].
  destruct (zlt (Int.unsigned r + 1) 2147483648); [|lia]. reflexivity.
Qed.

Lemma rc_sub1_small (r: int) : 0 < Int.unsigned r < 2147483648 -> rc_sub1 r = Int.sub r Int.one.
Proof.
  intros H. unfold rc_sub1, rc_neg, Int.ltu.
  rewrite (Int.unsigned_repr 2147483648) by rep_lia.
  destruct (zlt (Int.unsigned r) 2147483648); [|lia]. simpl.
  destruct (Int.eq r Int.one) eqn:E1.
  - apply Int.same_if_eq in E1. subst r. reflexivity.
  - destruct (Int.eq r Int.zero) eqn:E0; [|reflexivity].
    apply Int.same_if_eq in E0. subst r. rewrite Int.unsigned_zero in H. lia.
Qed.

Lemma rc_sub1_add1 (r: int) : 0 < Int.unsigned r < 2147483647 -> rc_sub1 (rc_add1 r) = r.
Proof.
  intros H. rewrite rc_add1_small by lia. rewrite rc_sub1_small.
  - rewrite Int.sub_add_opp, Int.add_assoc, Int.add_neg_zero, Int.add_zero. reflexivity.
  - unfold Int.add. rewrite Int.unsigned_one, Int.unsigned_repr; rep_lia.
Qed.

Lemma rc_add1_one : rc_add1 Int.one = Int.repr 2.
Proof. reflexivity. Qed.

Lemma rc_sub1_two : rc_sub1 (Int.repr 2) = Int.one.
Proof. reflexivity. Qed.

(* kref_get_unless_zero on a peer: None if the count is 0 *)
Definition peer_get (P: peer) : option peer :=
  if Int.eq (p_refs P) Int.zero then None else Some (p_set_refs P (rc_add1 (p_refs P))).

(* wg_peer_put: the new peer and whether the count reached 0 (wg_shim_peer_released++) *)
Definition peer_put (P: peer) : peer * bool :=
  let r := rc_sub1 (p_refs P) in (p_set_refs P r, Int.eq r Int.zero).

(* the public-key table's lookup: the first peer (in list order) with that remote static key *)
Fixpoint pk_find (PS: list (val * share * peer)) (pub: list byte) : option (val * peer) :=
  match PS with
  | [] => None
  | (a, _, P) :: PS' => if bytes_eqb (hs_rstatic (p_hs P)) pub then Some (a, P) else pk_find PS' pub
  end.

(* wg_pubkey_hashtable_lookup: (result, peers) *)
Definition pk_lookup (PS: list (val * share * peer)) (pub: list byte) : val * list (val * share * peer) :=
  match pk_find PS pub with
  | None => (nullval, PS)
  | Some (a, P) => match peer_get P with None => (nullval, PS) | Some P' => (a, supd PS a P') end
  end.

(* one more reference to the peer at a (wg_index_hashtable_lookup, count not 0) *)
Definition peers_ref (PS: list (val * share * peer)) (a: val) : list (val * share * peer) :=
  match sfind PS a with
  | Some (_, P) => supd PS a (p_set_refs P (rc_add1 (p_refs P)))
  | None => PS
  end.

(* the peers after a successful accept of the peer at a with new state P' *)
Definition peers_after (PS: list (val * share * peer)) (res: option (val * peer)) : list (val * share * peer) :=
  match res with Some (a, P') => supd PS a P' | None => PS end.
Definition peer_result (res: option (val * peer)) : val :=
  match res with Some (a, _) => a | None => nullval end.

Definition int_inb (i: int) (l: list int) : bool := existsb (Int.eq i) l.

(* quickproof_swab16 *)
Definition swab16 (x: Z) : Z := x / 256 + (x mod 256) * 256.

Definition dev_set_cc (D: device) (CC: checker) : device :=
  mkDev (d_dev D) (d_id D) CC (d_ptab D) (d_itab D).
Definition dev_set_id (D: device) (ID: identity) : device :=
  mkDev (d_dev D) ID (d_cc D) (d_ptab D) (d_itab D).

(* ------------------------------------------------------------------------------------------------ *)
(* The cryptographic layer                                                                          *)
(* ------------------------------------------------------------------------------------------------ *)

Section Protocol.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Definition HASH (m: list byte) : list byte := blake2s [] 32 m.
Definition MAC (key m: list byte) : list byte := blake2s key 16 m.

(* hmac: HMAC-BLAKE2s with block 64; a key longer than 64 bytes is hashed first *)
Definition hmac_xkey (key: list byte) : list byte :=
  let k := if Z.ltb 64 (Zlength key) then HASH key else key in
  k ++ zeros (64 - Zlength k).
Definition hmac (key data: list byte) : list byte :=
  let xk := hmac_xkey key in
  let ih := HASH (map (Byte.xor (Byte.repr 54)) xk ++ data) in
  HASH (map (Byte.xor (Byte.repr 92)) xk ++ ih).

(* kdf (HKDF): the three outputs T1, T2, T3 of KDF_n(ck, data) *)
Definition kdf_prk (ck data: list byte) : list byte := hmac ck data.
Definition kdf1 (ck data: list byte) : list byte := hmac (kdf_prk ck data) [Byte.one].
Definition kdf2 (ck data: list byte) : list byte :=
  hmac (kdf_prk ck data) (kdf1 ck data ++ [Byte.repr 2]).
Definition kdf3 (ck data: list byte) : list byte :=
  hmac (kdf_prk ck data) (kdf2 ck data ++ [Byte.repr 3]).

Definition mix_hash (h d: list byte) : list byte := HASH (h ++ d).

(* wg_noise_init *)
Definition init_ck : list byte := HASH handshake_name.
Definition init_hash : list byte := HASH (init_ck ++ identifier_name).

(* dh as curve25519() computes it, and its success *)
Definition dh_ok (priv pub: list byte) : bool := memneq_bool (x25519 priv pub) zeros32.

(* wg_noise_set_static_identity_private_key(raw) *)
Definition identity_of (old: identity) (raw: list byte) : identity :=
  mkId (if memneq_bool raw zeros32 then x25519 raw basepoint9 else id_pub old)
       (clamp raw)
       (andb (memneq_bool raw zeros32) (memneq_bool (x25519 raw basepoint9) zeros32)).

(* wg_noise_precompute_static_static *)
Definition precomputed (ID: identity) (rstatic: list byte) : list byte :=
  if andb (id_has ID) (dh_ok (id_priv ID) rstatic) then x25519 (id_priv ID) rstatic else zeros32.

(* precompute_key(label, pub) *)
Definition label_key (label pub: list byte) : list byte := blake2s [] 32 (label ++ pub).

(* TAI64N of the real clock (tai64n_now) *)
Definition tai64n (sec nsec: int64) : list byte :=
  be64 (Int64.add (Int64.repr 4611686018427387914) sec) ++
  be32 (Int.repr (Int64.unsigned (Int64.and nsec (Int64.not (Int64.repr 16777215))))).

(* ------------------------------------------------------------------------------------------------ *)
(* create_initiation (noise.c), step by step                                                       *)
(* ------------------------------------------------------------------------------------------------ *)

(* ID = the identity at handshake->static_identity; M = the message before; r = the 32 random bytes
   drawn by curve25519_generate_secret; ts = the timestamp (tai64n of the real clock); idx = the index
   drawn by the table.  Result: (success, message, handshake).  The table and shim effects are in the
   specification (insert at success). *)
Definition create_initiation_model (ID: identity) (H: handshake) (M: init_msg) (r ts: list byte)
  (idx: int) : bool * init_msg * handshake :=
  if negb (id_has ID) then (false, M, H) else
  let M1 := mkIM (Int.repr 1) (im_sender M) (im_eph M) (im_encs M) (im_enct M) (im_mac1 M) (im_mac2 M) in
  let ck0 := init_ck in
  let h0 := mix_hash init_hash (hs_rstatic H) in
  let eph := clamp r in
  let H1 := hs_set_eph (hs_set_ckh H ck0 h0) eph in
  if negb (memneq_bool eph zeros32) then (false, M1, H1) else
  let E := x25519 eph basepoint9 in
  let M2 := mkIM (im_type M1) (im_sender M1) E (im_encs M1) (im_enct M1) (im_mac1 M1) (im_mac2 M1) in
  if negb (memneq_bool E zeros32) then (false, M2, H1) else
  let h1 := mix_hash h0 E in
  let ck1 := kdf1 ck0 E in
  let H2 := hs_set_ckh H1 ck1 h1 in
  if negb (dh_ok eph (hs_rstatic H)) then (false, M2, H2) else
  let dh := x25519 eph (hs_rstatic H) in
  let ck2 := kdf1 ck1 dh in
  let key2 := kdf2 ck1 dh in
  let encs := aead_enc key2 0 h1 (id_pub ID) in
  let h2 := mix_hash h1 encs in
  let M3 := mkIM (im_type M2) (im_sender M2) (im_eph M2) encs (im_enct M2) (im_mac1 M2) (im_mac2 M2) in
  let H3 := hs_set_ckh H2 ck2 h2 in
  if negb (memneq_bool (hs_ss H) zeros32) then (false, M3, H3) else
  let ck3 := kdf1 ck2 (hs_ss H) in
  let key3 := kdf2 ck2 (hs_ss H) in
  let enct := aead_enc key3 0 h2 ts in
  let h3 := mix_hash h2 enct in
  (true, mkIM (im_type M3) idx (im_eph M3) (im_encs M3) enct (im_mac1 M3) (im_mac2 M3),
   hs_set_state (hs_set_ckh H3 ck3 h3) HS_CREATED_INITIATION).

(* ------------------------------------------------------------------------------------------------ *)
(* create_response                                                                                  *)
(* ------------------------------------------------------------------------------------------------ *)

Definition create_response_model (H: handshake) (M: resp_msg) (r: list byte) (idx: int)
  : bool * resp_msg * handshake :=
  if negb (Int.eq (hs_state H) HS_CONSUMED_INITIATION) then (false, M, H) else
  let M1 := mkRM (Int.repr 2) (rm_sender M) (hs_rindex H) (rm_eph M) (rm_encn M) (rm_mac1 M) (rm_mac2 M) in
  let eph := clamp r in
  let H1 := hs_set_eph H eph in
  if negb (memneq_bool eph zeros32) then (false, M1, H1) else
  let E := x25519 eph basepoint9 in
  let M2 := mkRM (rm_type M1) (rm_sender M1) (rm_receiver M1) E (rm_encn M1) (rm_mac1 M1) (rm_mac2 M1) in
  if negb (memneq_bool E zeros32) then (false, M2, H1) else
  let h1 := mix_hash (hs_hash H) E in
  let ck1 := kdf1 (hs_ck H) E in
  let H2 := hs_set_ckh H1 ck1 h1 in
  if negb (dh_ok eph (hs_reph H)) then (false, M2, H2) else
  let ck2 := kdf1 ck1 (x25519 eph (hs_reph H)) in
  let H3 := hs_set_ckh H2 ck2 h1 in
  if negb (dh_ok eph (hs_rstatic H)) then (false, M2, H3) else
  let ck3 := kdf1 ck2 (x25519 eph (hs_rstatic H)) in
  let ck4 := kdf1 ck3 (hs_psk H) in
  let tau := kdf2 ck3 (hs_psk H) in
  let key := kdf3 ck3 (hs_psk H) in
  let h2 := mix_hash h1 tau in
  let encn := aead_enc key 0 h2 [] in
  let h3 := mix_hash h2 encn in
  (true, mkRM (rm_type M2) idx (rm_receiver M2) (rm_eph M2) encn (rm_mac1 M2) (rm_mac2 M2),
   hs_set_state (hs_set_ckh H3 ck4 h3) HS_CREATED_RESPONSE).

(* ------------------------------------------------------------------------------------------------ *)
(* consume_initiation                                                                               *)
(* ------------------------------------------------------------------------------------------------ *)

(* The responder's side up to the peer lookup: Some (static key, key, ck, hash) if DH(S_priv, E) is not
   zero and the static decrypts. *)
Definition consume_init_stage1 (ID: identity) (M: init_msg)
  : option (list byte * list byte * list byte * list byte) :=
  let h0 := mix_hash (mix_hash init_hash (id_pub ID)) (im_eph M) in
  let ck0 := kdf1 init_ck (im_eph M) in
  if negb (dh_ok (id_priv ID) (im_eph M)) then None else
  let dh := x25519 (id_priv ID) (im_eph M) in
  let ck1 := kdf1 ck0 dh in
  let key1 := kdf2 ck0 dh in
  match aead_dec key1 0 h0 (im_encs M) with
  | None => None
  | Some s => Some (s, key1, ck1, mix_hash h0 (im_encs M))
  end.

(* From the peer's precomputed DH: Some (timestamp, ck, hash) if ss is not zero and the timestamp
   decrypts. *)
Definition consume_init_stage2 (ss ck h: list byte) (M: init_msg) : option (list byte * list byte * list byte) :=
  if negb (memneq_bool ss zeros32) then None else
  let ck2 := kdf1 ck ss in
  let key2 := kdf2 ck ss in
  match aead_dec key2 0 h (im_enct M) with
  | None => None
  | Some t => Some (t, ck2, mix_hash h (im_enct M))
  end.

(* The accepted peer (address, its new state, with one more reference) or None.  now = the boot clock.
   PS = the peers of the public-key table, in list order. *)
Definition consume_initiation_model (ID: identity) (PS: list (val * share * peer)) (M: init_msg) (now: int64)
  : option (val * peer) :=
  if negb (id_has ID) then None else
  match consume_init_stage1 ID M with
  | None => None
  | Some (s, _, ck1, h1) =>
    match pk_find PS s with
    | None => None
    | Some (a, P) =>
      match peer_get P with
      | None => None
      | Some P1 =>
        let H := p_hs P in
        match consume_init_stage2 (hs_ss H) ck1 h1 M with
        | None => None
        | Some (t, ck2, h2) =>
          let replay := Z.leb (memcmp_Z t (hs_ts H)) 0 in
          let flood := negb (s64_le (Int64.add (hs_lic H) (Int64.repr 20000000)) now) in
          if orb replay flood then None else
          let H' := mkHS HS_CONSUMED_INITIATION
                      (if Int64.lt (Int64.sub (hs_lic H) now) Int64.zero then now else hs_lic H)
                      (hs_sid H) (hs_eph H) (hs_rstatic H) (im_eph M) (hs_ss H) (hs_psk H)
                      h2 ck2 t (im_sender M) in
          Some (a, p_set_hs P1 H')
        end
      end
    end
  end.

(* ------------------------------------------------------------------------------------------------ *)
(* consume_response                                                                                 *)
(* ------------------------------------------------------------------------------------------------ *)

(* The initiator's computation from its handshake H and static private key: Some (ck, hash) *)
Definition consume_resp_crypto (spriv: list byte) (H: handshake) (M: resp_msg) : option (list byte * list byte) :=
  let e := rm_eph M in
  let h1 := mix_hash (hs_hash H) e in
  let ck1 := kdf1 (hs_ck H) e in
  if negb (dh_ok (hs_eph H) e) then None else
  let ck2 := kdf1 ck1 (x25519 (hs_eph H) e) in
  if negb (dh_ok spriv e) then None else
  let ck3 := kdf1 ck2 (x25519 spriv e) in
  let ck4 := kdf1 ck3 (hs_psk H) in
  let tau := kdf2 ck3 (hs_psk H) in
  let key := kdf3 ck3 (hs_psk H) in
  let h2 := mix_hash h1 tau in
  match aead_dec key 0 h2 (rm_encn M) with
  | None => None
  | Some _ => Some (ck4, mix_hash h2 (rm_encn M))
  end.

(* The accepted peer: the table's entry with the receiver index is a handshake entry (it is then the
   handshake of its peer), its peer is at state CREATED_INITIATION and the crypto succeeds. *)
Definition consume_response_model (ID: identity) (T: tstate) (PS: list (val * share * peer)) (M: resp_msg)
  : option (val * peer) :=
  if negb (id_has ID) then None else
  match t_lookup T IDX_HANDSHAKE (rm_receiver M) with
  | None => None
  | Some (_, E) =>
    match sfind PS (e_peer E) with
    | None => None
    | Some (_, P) =>
      match peer_get P with
      | None => None
      | Some P1 =>
        let H := p_hs P in
        if negb (Int.eq (hs_state H) HS_CREATED_INITIATION) then None else
        match consume_resp_crypto (id_priv ID) H M with
        | None => None
        | Some (ck, h) =>
          Some (e_peer E,
                p_set_hs P1 (mkHS HS_CONSUMED_RESPONSE (hs_lic H) (hs_sid H) (hs_eph H) (hs_rstatic H)
                               (rm_eph M) (hs_ss H) (hs_psk H) h ck (hs_ts H) (rm_sender M)))
        end
      end
    end
  end.

(* ------------------------------------------------------------------------------------------------ *)
(* Keypairs                                                                                         *)
(* ------------------------------------------------------------------------------------------------ *)

(* keypair_create: the zeroed keypair of kzalloc with its internal id, refcount 1 *)
Definition kp_fresh (id: int64) : keypair :=
  mkKP (mkSym (zeros 32) Int64.zero false) Int64.zero (mkSym (zeros 32) Int64.zero false) Int64.zero
       (Zrepeat Int64.zero 128) Int.zero false Int.one id.

(* begin_session's keypair (before add_new_keypair): derive_keys at boot time now *)
Definition kp_new (H: handshake) (id now: int64) : keypair :=
  let init := Int.eq (hs_state H) HS_CONSUMED_RESPONSE in
  let t1 := kdf1 (hs_ck H) [] in
  let t2 := kdf2 (hs_ck H) [] in
  mkKP (mkSym (if init then t1 else t2) now true) Int64.zero (mkSym (if init then t2 else t1) now true)
       Int64.zero (Zrepeat Int64.zero 128) (hs_rindex H) init Int.one id.

(* The keypair world of one peer: its live keypairs KS (address, contents; each entry at the keypair's
   address is in the pool of T), the table T and the shim S (frees). *)
Record kworld := mkKW { kw_KS: list (val * keypair); kw_T: tstate; kw_S: shim }.

(* wg_noise_keypair_put(k, unref) *)
Definition kp_put (k: val) (unref: bool) (W: kworld) : kworld :=
  if eq_dec k nullval then W else
  match afind (kw_KS W) k with
  | None => W
  | Some K =>
    let T1 := if unref then t_remove (kw_T W) k else kw_T W in
    let r := rc_sub1 (kp_refs K) in
    if Int.eq r Int.zero
    then mkKW (adel (kw_KS W) k) (t_free T1 k) (shim_free (kw_S W))
    else mkKW (aupd (kw_KS W) k (kp_set_refs K r)) T1 (kw_S W)
  end.

(* wg_noise_keypair_get(k): (result, keypairs) *)
Definition kp_get (k: val) (KS: list (val * keypair)) : val * list (val * keypair) :=
  if eq_dec k nullval then (nullval, KS) else
  match afind KS k with
  | None => (nullval, KS)
  | Some K => if Int.eq (kp_refs K) Int.zero then (nullval, KS)
              else (k, aupd KS k (kp_set_refs K (rc_add1 (kp_refs K))))
  end.

(* add_new_keypair(&P->keypairs, new), new of role init *)
Definition add_new_keypair_model (P: peer) (new: val) (init: bool) (W: kworld) : peer * kworld :=
  let prev := p_prev P in let next := p_next P in let cur := p_cur P in
  if init then
    if negb (eq_dec next nullval) then
      let W1 := kp_put cur true W in
      let W2 := kp_put prev true W1 in
      (p_set_slots P new next nullval, W2)
    else
      let W2 := kp_put prev true W in
      (p_set_slots P new cur next, W2)
  else
    let W1 := kp_put next true W in
    let W2 := kp_put prev true W1 in
    (p_set_slots P cur nullval new, W2).

(* wg_noise_received_with_keypair(&P->keypairs, k) *)
Definition received_with_keypair_model (P: peer) (k: val) (W: kworld) : bool * peer * kworld :=
  if eq_dec k (p_next P) then
    let W1 := kp_put (p_prev P) true W in
    (true, p_set_slots P k (p_cur P) nullval, W1)
  else (false, P, W).

(* wg_noise_keypairs_clear(&P->keypairs) *)
Definition keypairs_clear_model (P: peer) (W: kworld) : peer * kworld :=
  let W1 := kp_put (p_next P) true W in
  let W2 := kp_put (p_prev P) true W1 in
  let W3 := kp_put (p_cur P) true W2 in
  (p_set_slots P nullval nullval nullval, W3).

(* wg_noise_reset_last_sent_handshake: now - 6 s (u64 arithmetic) *)
Definition reset_lsh (now: int64) : int64 := Int64.sub now (Int64.repr (6 * NSEC_PER_SEC)).

(* wg_noise_expire_current_peer_keypairs(P): the handshake entry at hs (P's handshake address) *)
Definition expire_model (P: peer) (hs: val) (KS: list (val * keypair)) (T: tstate) (now: int64)
  : peer * list (val * keypair) * tstate :=
  let T1 := t_remove T hs in
  let P1 := p_set_lsh (p_set_hs P (hs_zero (p_hs P))) (reset_lsh now) in
  let inv (KS: list (val * keypair)) (k: val) :=
    if eq_dec k nullval then KS else
    match afind KS k with Some K => aupd KS k (kp_invalidate_send K) | None => KS end in
  (P1, inv (inv KS (p_next P)) (p_cur P), T1).

(* wg_noise_handshake_begin_session(&P->handshake, &P->keypairs).
   p = the peer's address, hs = its handshake address (= its entry's address);
   k = the address kzalloc returned (NULL: the allocation failed); kc = keypair_counter before.
   Result: (return value, peer, keypair world, keypair_counter).  (The shim's allocation counters: the
   kzalloc effect is applied first: shim_alloc_ok / shim_alloc_fail.) *)
Definition e_peer_of_hs (W: kworld) (hs: val) : val :=
  match t_entry (kw_T W) hs with Some E => e_peer E | None => nullval end.

Definition begin_session_model (P: peer) (hs k: val) (kc: int64) (W: kworld) : bool * peer * kworld * int64 :=
  let H := p_hs P in
  if negb (orb (Int.eq (hs_state H) HS_CREATED_RESPONSE) (Int.eq (hs_state H) HS_CONSUMED_RESPONSE))
  then (false, P, W, kc) else
  if eq_dec k nullval then (false, P, mkKW (kw_KS W) (kw_T W) (shim_alloc_fail (kw_S W)), kc) else
  let kc' := Int64.add kc Int64.one in
  let K := kp_new H kc' (s_boot (kw_S W)) in
  let P1 := p_set_hs P (hs_zero H) in
  let S1 := shim_alloc_ok (kw_S W) in
  if p_dead P then (false, P1, mkKW (kw_KS W) (kw_T W) (shim_free S1), kc') else
  let W1 := mkKW ((k, K) :: kw_KS W) (t_add (kw_T W) k Ews (mkEntry (e_peer_of_hs W hs) IDX_KEYPAIR Int.zero)) S1 in
  let '(P2, W2) := add_new_keypair_model P1 k (kp_init K) W1 in
  let '(ok, T3) := t_replace (kw_T W2) hs k in
  (ok, P2, mkKW (kw_KS W2) T3 (kw_S W2), kc').

(* ------------------------------------------------------------------------------------------------ *)
(* cookie.c                                                                                         *)
(* ------------------------------------------------------------------------------------------------ *)

(* wg_cookie_checker_precompute_device_keys: (cookie encryption key, mac1 key) *)
Definition checker_keys (ID: identity) : list byte * list byte :=
  if id_has ID then (label_key cookie_label (id_pub ID), label_key mac1_label (id_pub ID))
  else (zeros32, zeros32).

Definition checker_set_keys (CC: checker) (ks: list byte * list byte) : checker :=
  mkChk (cc_secret CC) (fst ks) (snd ks) (cc_birth CC) (cc_dev CC).

(* wg_cookie_checker_precompute_peer_keys *)
Definition cookie_set_keys (C: cookie) (rstatic: list byte) : cookie :=
  mkCookie (ck_birth C) (ck_valid C) (ck_cookie C) (ck_sent C) (ck_last_mac1 C)
           (label_key cookie_label rstatic) (label_key mac1_label rstatic).

Definition cookie_zero : cookie := mkCookie Int64.zero false (zeros 16) false (zeros 16) (zeros 32) (zeros 32).

(* htons(ETH_P_IP) = 0x0008, htons(ETH_P_IPV6) = 0xdd86 *)
Definition PROTO_IP := 8.
Definition PROTO_IPV6 := 56710.

(* the source bytes hashed into the cookie: address (4, 16 or 0 bytes) || port *)
Definition skb_source (s: skb) : list byte :=
  (if Z.eq_dec (sk_proto s) PROTO_IP then sk_ip4 s
   else if Z.eq_dec (sk_proto s) PROTO_IPV6 then sk_ip6 s else []) ++ sk_port s.

(* make_cookie's secret rotation: with the drawn bytes r when the secret is 120 s old *)
Definition checker_rotate (CC: checker) (now: int64) (r: list byte) : checker :=
  if birthdate_expired (cc_birth CC) (Int64.repr 120) now
  then mkChk r (cc_ekey CC) (cc_mkey CC) now (cc_dev CC) else CC.
Definition checker_rotates (CC: checker) (now: int64) : bool :=
  birthdate_expired (cc_birth CC) (Int64.repr 120) now.

(* make_cookie after the rotation *)
Definition cookie_of (secret: list byte) (s: skb) : list byte := MAC secret (skb_source s).

(* mac1 = MAC(key, m[0..len-32)), mac2 = MAC(cookie, m[0..len-16)) *)
Definition mac1_of (key msg: list byte) : list byte := MAC key (sublist 0 (Zlength msg - 32) msg).
Definition mac2_of (ck msg: list byte) : list byte := MAC ck (sublist 0 (Zlength msg - 16) msg).

(* wg_cookie_add_mac_to_packet(msg, len, P): the new message and cookie state *)
Definition add_mac_model (C: cookie) (msg: list byte) (now: int64) : list byte * cookie :=
  let n := Zlength msg in
  let m1 := mac1_of (ck_mkey C) msg in
  let msg1 := sublist 0 (n - 32) msg ++ m1 ++ sublist (n - 16) n msg in
  let m2 := if andb (ck_valid C) (negb (birthdate_expired (ck_birth C) (Int64.repr 115) now))
            then mac2_of (ck_cookie C) msg1 else zeros 16 in
  (sublist 0 (n - 16) msg1 ++ m2,
   mkCookie (ck_birth C) (ck_valid C) (ck_cookie C) true m1 (ck_dkey C) (ck_mkey C)).

(* wg_cookie_validate_packet: (verdict, checker after); r = the random bytes drawn at a rotation *)
Definition validate_model (CC: checker) (s: skb) (msg: list byte) (check_cookie: bool) (now: int64)
  (rlallow: bool) (r: list byte) : Z * checker :=
  let n := Zlength msg in
  if negb (bytes_eqb (mac1_of (cc_mkey CC) msg) (sublist (n - 32) (n - 16) msg)) then (INVALID_MAC, CC) else
  if negb check_cookie then (VALID_MAC_BUT_NO_COOKIE, CC) else
  let CC1 := checker_rotate CC now r in
  if negb (bytes_eqb (mac2_of (cookie_of (cc_secret CC1) s) msg) (sublist (n - 16) n msg))
  then (VALID_MAC_BUT_NO_COOKIE, CC1) else
  if negb rlallow then (VALID_MAC_WITH_COOKIE_BUT_RATELIMITED, CC1) else (VALID_MAC_WITH_COOKIE, CC1).

(* wg_cookie_message_create(dst, skb, index, checker): nonce = the 24 drawn bytes, r = the secret drawn at
   a rotation, mac1 = the packet's mac1 *)
Definition message_create_model (CC: checker) (s: skb) (index: int) (nonce: list byte) (mac1: list byte)
  (now: int64) (r: list byte) : cookie_msg * checker :=
  let CC1 := checker_rotate CC now r in
  (mkCM (Int.repr 3) index nonce (xaead_enc (cc_ekey CC) nonce mac1 (cookie_of (cc_secret CC1) s)), CC1).

(* wg_cookie_message_consume(src, wg): the peer whose cookie changes (address, new peer) or None.
   The lookup's reference is dropped again: reference counts are unchanged. *)
Definition message_consume_model (T: tstate) (PS: list (val * share * peer)) (M: cookie_msg) (now: int64)
  : option (val * peer) :=
  match t_lookup T (Int.or IDX_HANDSHAKE IDX_KEYPAIR) (cm_receiver M) with
  | None => None
  | Some (_, E) =>
    match sfind PS (e_peer E) with
    | None => None
    | Some (_, P) =>
      let C := p_cookie P in
      if negb (ck_sent C) then None else
      match xaead_dec (ck_dkey C) (cm_nonce M) (ck_last_mac1 C) (cm_enc M) with
      | None => None
      | Some pt => Some (e_peer E, p_set_cookie P (mkCookie now true pt false (ck_last_mac1 C) (ck_dkey C) (ck_mkey C)))
      end
    end
  end.

End Protocol.
