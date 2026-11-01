(* the harnesses' protocol model m_* of harness/common.h as Coq functions.

   common.h's model is written from the WireGuard paper, not from noise.c; over the same kernel primitives
   (curve25519_generic, BLAKE2s, the AEADs) it computes the same chaining keys and hashes as the C model of
   prot_model3.v.  Each function below follows its C counterpart statement by statement, written with the
   building blocks of prot_model3.v (HASH, hmac, kdf1/2/3, mix_hash, dh_ok, clamp, ...) where the C does the
   same computation; m_hmac / m_kdf / m_hash2 equal hmac / kdf1..3 / HASH (lemmas in hc_lemmas3.v).

   Parameterised (Section) by the primitive models x25519, aead_enc, aead_dec, as prot_model3.v. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.blake2s.model.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.protocol.prot_model3.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* m_identity {priv, pub, ok} *)
Record mident := mkMId { mi_priv: list byte; mi_pub: list byte; mi_ok: bool }.

(* the handshake snapshot struct hs_snap: an entry (peer, type, index), its list fields (next, hashed) and the
   handshake fields *)
Record hsnap := mkSnap { sn_entry: entry; sn_next: val; sn_hashed: bool; sn_hs: handshake }.

(* the cookie snapshot struct ck_snap = a cookie record (prot_model3.cookie) *)

(* m_tai64n(sec, nsec) = tai64n of prot_model3 *)

(* m_ts_newer(t, latest): t > latest, lexicographic over unsigned bytes *)
Fixpoint ts_newer (t l: list byte) : bool :=
  match t, l with
  | x :: t', y :: l' => if Byte.eq x y then ts_newer t' l' else Z.gtb (Byte.unsigned x) (Byte.unsigned y)
  | _, _ => false
  end.

(* m_not_flood(last, now): !((s64)last + 20000000 > (s64)now) *)
Definition not_flood (last now: int64) : bool := s64_le (Int64.add last (Int64.repr 20000000)) now.

(* m_last_consumption(last, now): now if (s64)(last - now) < 0, else last *)
Definition last_consumption (last now: int64) : int64 :=
  if Int64.lt (Int64.sub last now) Int64.zero then now else last.

(* m_expired(birthdate, seconds, now) of cookie_mac.c / cookie_reply.c = birthdate_expired *)

(* m_static_public_field(id, raw): X25519(raw, 9) unless raw is all zero (then zero) *)
Definition static_public_field (raw pub: list byte) : list byte :=
  if memneq_bool raw zeros32 then pub else zeros32.

(* the snapshot of a handshake whose entry E is at address a of the table T *)
Definition snap_of (T: tstate) (a: val) (E: entry) (H: handshake) : hsnap :=
  mkSnap E (succ_in (t_L T) a) (vin a (t_L T)) H.

Definition entry_eqb (E1 E2: entry) : bool :=
  (if eq_dec (e_peer E1) (e_peer E2) then true else false) && Int.eq (e_type E1) (e_type E2) &&
  Int.eq (e_index E1) (e_index E2).

Definition hs_eqb (H1 H2: handshake) : bool :=
  Int.eq (hs_state H1) (hs_state H2) && Int64.eq (hs_lic H1) (hs_lic H2) &&
  (if eq_dec (hs_sid H1) (hs_sid H2) then true else false) &&
  bytes_eqb (hs_eph H1) (hs_eph H2) && bytes_eqb (hs_rstatic H1) (hs_rstatic H2) &&
  bytes_eqb (hs_reph H1) (hs_reph H2) && bytes_eqb (hs_ss H1) (hs_ss H2) &&
  bytes_eqb (hs_psk H1) (hs_psk H2) && bytes_eqb (hs_hash H1) (hs_hash H2) &&
  bytes_eqb (hs_ck H1) (hs_ck H2) && bytes_eqb (hs_ts H1) (hs_ts H2) && Int.eq (hs_rindex H1) (hs_rindex H2).

(* hs_same(s, h): every field equal *)
Definition snap_eqb (s c: hsnap) : bool :=
  entry_eqb (sn_entry s) (sn_entry c) && (if eq_dec (sn_next s) (sn_next c) then true else false) &&
  Bool.eqb (sn_hashed s) (sn_hashed c) && hs_eqb (sn_hs s) (sn_hs c).

(* hs_zeroed_from(s, h): h is s's handshake zeroed (state ZEROED, remote index 0, ephemeral, remote
   ephemeral, hash, chaining key zero), its entry's peer and type and the other fields as in s *)
Definition zeroed_from (s c: hsnap) : bool :=
  let H := sn_hs c in let H0 := sn_hs s in
  Int.eq (hs_state H) HS_ZEROED && Int.eq (hs_rindex H) Int.zero &&
  is_zero (hs_eph H) && is_zero (hs_reph H) && is_zero (hs_hash H) && is_zero (hs_ck H) &&
  (if eq_dec (e_peer (sn_entry s)) (e_peer (sn_entry c)) then true else false) &&
  Int.eq (e_type (sn_entry s)) (e_type (sn_entry c)) &&
  Int64.eq (hs_lic H0) (hs_lic H) && (if eq_dec (hs_sid H0) (hs_sid H) then true else false) &&
  bytes_eqb (hs_rstatic H0) (hs_rstatic H) && bytes_eqb (hs_ss H0) (hs_ss H) &&
  bytes_eqb (hs_psk H0) (hs_psk H) && bytes_eqb (hs_ts H0) (hs_ts H).

(* ck_same(s, c) *)
Definition cookie_eqb (C1 C2: cookie) : bool :=
  Int64.eq (ck_birth C1) (ck_birth C2) && Bool.eqb (ck_valid C1) (ck_valid C2) &&
  bytes_eqb (ck_cookie C1) (ck_cookie C2) && Bool.eqb (ck_sent C1) (ck_sent C2) &&
  bytes_eqb (ck_last_mac1 C1) (ck_last_mac1 C2) && bytes_eqb (ck_dkey C1) (ck_dkey C2) &&
  bytes_eqb (ck_mkey C1) (ck_mkey C2).

(* table_has / table_index_unique / table_len over the table's list *)
Definition count_index (T: tstate) (idx: int) : Z :=
  Zlength (filter (fun i => Int.eq i idx) (t_indices T (t_L T))).

Section Model.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* m_identity_of(raw) *)
Definition mident_of (raw: list byte) : mident :=
  let pub := x25519 raw basepoint9 in
  mkMId (clamp raw) pub (memneq_bool raw zeros32 && memneq_bool pub zeros32).

(* m_precomputed(id, peer_pub) *)
Definition m_precomputed_model (I: mident) (pub: list byte) : list byte :=
  if mi_ok I && dh_ok x25519 (mi_priv I) pub then x25519 (mi_priv I) pub else zeros32.

(* m_create_initiation(spub, rpub, ss, eraw, ts): Some (ephemeral, enc_static, enc_timestamp, eph_priv,
   ck, h) iff every step succeeds *)
Definition m_create_initiation_model (spub rpub ss eraw ts: list byte)
  : option (list byte * list byte * list byte * list byte * list byte * list byte) :=
  let ck0 := init_ck in
  let h0 := mix_hash init_hash rpub in
  let ep := clamp eraw in
  if negb (dh_ok x25519 ep basepoint9) then None else
  let E := x25519 ep basepoint9 in
  let h1 := mix_hash h0 E in
  let ck1 := kdf1 ck0 E in
  if negb (dh_ok x25519 ep rpub) then None else
  let dh := x25519 ep rpub in
  let ck2 := kdf1 ck1 dh in
  let key2 := kdf2 ck1 dh in
  let encs := aead_enc key2 0 h1 spub in
  let h2 := mix_hash h1 encs in
  if is_zero ss then None else
  let ck3 := kdf1 ck2 ss in
  let key3 := kdf2 ck2 ss in
  let enct := aead_enc key3 0 h2 ts in
  Some (E, encs, enct, ep, ck3, mix_hash h2 enct).

(* m_consume_initiation_1(rid, ephemeral, enc_static): Some (spub, key, ck, h) = consume_init_stage1 *)
Definition m_consume_init1_model (I: mident) (eph encs: list byte)
  : option (list byte * list byte * list byte * list byte) :=
  consume_init_stage1 x25519 aead_dec (mkId (mi_pub I) (mi_priv I) (mi_ok I))
    (mkIM Int.zero Int.zero eph encs [] [] []).

(* m_consume_initiation_2(ss, enc_timestamp) from the state (ck, h): Some (ts, ck, h) = consume_init_stage2 *)
Definition m_consume_init2_model (ss ck h enct: list byte) : option (list byte * list byte * list byte) :=
  consume_init_stage2 aead_dec ss ck h (mkIM Int.zero Int.zero [] [] enct [] []).

(* m_create_response(st = (ck, h), ei, si, psk, eraw): Some (ephemeral, enc_nothing, eph_priv, ck, h) *)
Definition m_create_response_model (ck h ei si psk eraw: list byte)
  : option (list byte * list byte * list byte * list byte * list byte) :=
  let ep := clamp eraw in
  if negb (dh_ok x25519 ep basepoint9) then None else
  let E := x25519 ep basepoint9 in
  let h1 := mix_hash h E in
  let ck1 := kdf1 ck E in
  if negb (dh_ok x25519 ep ei) then None else
  let ck2 := kdf1 ck1 (x25519 ep ei) in
  if negb (dh_ok x25519 ep si) then None else
  let ck3 := kdf1 ck2 (x25519 ep si) in
  let ck4 := kdf1 ck3 psk in
  let key := kdf3 ck3 psk in
  let h2 := mix_hash h1 (kdf2 ck3 psk) in
  let encn := aead_enc key 0 h2 [] in
  Some (E, encn, ep, ck4, mix_hash h2 encn).

(* m_consume_response(st = (ck, h), eph_priv, spriv, psk, ephemeral, enc_nothing): Some (ck, h) *)
Definition m_consume_response_model (ck h eph spriv psk e encn: list byte) : option (list byte * list byte) :=
  consume_resp_crypto x25519 aead_dec spriv
    (mkHS HS_ZEROED Int64.zero nullval eph [] [] [] psk h ck [] Int.zero)
    (mkRM Int.zero Int.zero Int.zero e encn [] []).

End Model.

(* draw_real_clock(): the shim's real-time clock set to (sec, nsec) *)
Definition shim_set_real (S: shim) (sec nsec: int64) : shim :=
  mkShim (s_boot S) sec nsec (s_log S) (s_logprev S) (s_u32 S) (s_allocs S) (s_fails S) (s_frees S)
         (s_failnext S) (s_released S) (s_rlallow S).

(* the harness sets the boot clock (wg_shim_boottime_ns = now) and the rate limiter's answer *)
Definition shim_set_boot (S: shim) (now: int64) : shim :=
  mkShim now (s_rsec S) (s_rnsec S) (s_log S) (s_logprev S) (s_u32 S) (s_allocs S) (s_fails S) (s_frees S)
         (s_failnext S) (s_released S) (s_rlallow S).
Definition shim_set_rlallow (S: shim) (b: bool) : shim :=
  mkShim (s_boot S) (s_rsec S) (s_rnsec S) (s_log S) (s_logprev S) (s_u32 S) (s_allocs S) (s_fails S)
         (s_frees S) (s_failnext S) (s_released S) b.

(* hs_randomize(h): the mutable handshake fields replaced *)
Definition hs_randomized (H: handshake) (st: int) (lic: int64) (eph reph hash ck ts: list byte) (ri: int)
  : handshake :=
  mkHS st lic (hs_sid H) eph (hs_rstatic H) reph (hs_ss H) (hs_psk H) hash ck ts ri.

Definition hs_states : list int :=
  [HS_ZEROED; HS_CREATED_INITIATION; HS_CONSUMED_INITIATION; HS_CREATED_RESPONSE; HS_CONSUMED_RESPONSE].
