(* law handshake_receive:
   the PURE model of the extracted receive.c (patch/receive_handshake.c: validate_header_len,
   wg_receive_handshake_packet, and the recording shim S23 of send.c / socket.c / timers.c) and of the harness's
   dispatch().

   The model composes the protocol4 specifications (prot_specs4.v) of the calls exactly in the order of the C:
   - the message is its byte image `msg` (skb->len bytes at skb->data); its type word is msg[0..4) (x86_64:
     little-endian), the typed views im_of / rm_of / cm_of parse the image;
   - validate_header_len = vhl_model; dispatch forwards to wg_receive_handshake_packet iff hrx5_fwd msg;
   - a cookie reply (type 3) is consumed (wg_cookie_message_consume: mcons_res); nothing else;
   - an initiation / response (types 1 / 2): the load (load_model: receive.c's last_under_load hysteresis), the mac
     verdict and the checker's rotation (wg_cookie_validate_packet: validate_model, the draw r), then
       * consume (initiation: cin_res, then on acceptance the endpoint, the response, the rx statistics, the two
         timers and wg_peer_put; response: cre_res, then the endpoint, begin_session (bs_res, the keypair address
         k), on success the session timers and the keepalive, the rx statistics, the timers, wg_peer_put),
       * a cookie reply (wg_packet_send_handshake_cookie: wg_cookie_message_create, mc_res, the nonce and the draw
         r2), or
       * nothing (dropped);
   - the S23 calls are recorded in the global wg_shim_rx (struct wg_shim_rx_log): rxlog, its updates rx_*.
   The random draws of a call (r, nonce, r2) and kzalloc's result k are the model's inputs (rxdraw): the
   specifications quantify over them existentially. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common4.hc4_model.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* ------------------------------------------------------------------------------------------------ *)
(* the message image                                                                                 *)
(* ------------------------------------------------------------------------------------------------ *)

(* the type word (struct message_header's type) of a message of at least 4 bytes *)
Definition hrx5_tw (msg: list byte) : int := le32_val (sublist 0 4 msg).

(* the u32 at offset 4: the sender index of an initiation / response (the receiver index of a cookie reply) *)
Definition hrx5_w4 (msg: list byte) : int := le32_val (sublist 4 8 msg).

(* the typed views of an image of 148 / 92 / 64 bytes *)
Definition im_of (b: list byte) : init_msg :=
  mkIM (le32_val (sublist 0 4 b)) (le32_val (sublist 4 8 b)) (sublist 8 40 b) (sublist 40 88 b)
       (sublist 88 116 b) (sublist 116 132 b) (sublist 132 148 b).
Definition rm_of (b: list byte) : resp_msg :=
  mkRM (le32_val (sublist 0 4 b)) (le32_val (sublist 4 8 b)) (le32_val (sublist 8 12 b)) (sublist 12 44 b)
       (sublist 44 60 b) (sublist 60 76 b) (sublist 76 92 b).
Definition cm_of (b: list byte) : cookie_msg :=
  mkCM (le32_val (sublist 0 4 b)) (le32_val (sublist 4 8 b)) (sublist 8 32 b) (sublist 32 64 b).

(* validate_header_len(skb) (skb->len = |msg|): sizeof(struct message_data) = 16 for a data packet of at least
   MESSAGE_MINIMUM_LENGTH = 32 bytes, the exact sizes 148 / 92 / 64 of the handshake messages, else 0 *)
Definition vhl_model (msg: list byte) : Z :=
  let n := Zlength msg in
  if n <? 4 then 0 else
  let tw := hrx5_tw msg in
  if Int.eq tw (Int.repr 4) && (32 <=? n) then 16
  else if Int.eq tw Int.one && (n =? 148) then 148
  else if Int.eq tw (Int.repr 2) && (n =? 92) then 92
  else if Int.eq tw (Int.repr 3) && (n =? 64) then 64
  else 0.

(* dispatch() hands the packet to wg_receive_handshake_packet: the type word is exactly 1, 2 or 3 and the length
   exactly the message's *)
Definition hrx5_fwd (msg: list byte) : bool :=
  let n := Zlength msg in
  (4 <=? n) &&
  (let tw := hrx5_tw msg in
   (Int.eq tw Int.one && (n =? 148)) || (Int.eq tw (Int.repr 2) && (n =? 92)) ||
   (Int.eq tw (Int.repr 3) && (n =? 64))).

(* ------------------------------------------------------------------------------------------------ *)
(* the recording shim S23: struct wg_shim_rx_log                                                     *)
(* ------------------------------------------------------------------------------------------------ *)

Record rxlog := mkRx {
  rx_cookie: int;       (* wg_packet_send_handshake_cookie *)
  rx_cindex: int;       (* its sender_index argument *)
  rx_endpoint: int;     (* wg_socket_set_peer_endpoint_from_skb *)
  rx_eskb: val;         (* its skb *)
  rx_response: int;     (* wg_packet_send_handshake_response *)
  rx_session: int;      (* wg_timers_session_derived *)
  rx_complete: int;     (* wg_timers_handshake_complete *)
  rx_keepalive: int;    (* wg_packet_send_keepalive *)
  rx_stats: int;        (* update_rx_stats *)
  rx_len: int64;        (* its length argument (size_t) *)
  rx_received: int;     (* wg_timers_any_authenticated_packet_received *)
  rx_traversal: int;    (* wg_timers_any_authenticated_packet_traversal *)
  rx_peer: val;         (* the peer of the first peer call *)
  rx_other: bool }.     (* a later peer call had another peer *)

(* rx_reset() *)
Definition rx0 : rxlog :=
  mkRx Int.zero Int.zero Int.zero nullval Int.zero Int.zero Int.zero Int.zero Int.zero Int64.zero Int.zero
       Int.zero nullval false.

Definition inc (i: int) : int := Int.add i Int.one.

(* wg_shim_rx_peer(p) *)
Definition rx_note (X: rxlog) (p: val) : rxlog :=
  if eq_dec (rx_peer X) nullval then
    mkRx (rx_cookie X) (rx_cindex X) (rx_endpoint X) (rx_eskb X) (rx_response X) (rx_session X) (rx_complete X)
         (rx_keepalive X) (rx_stats X) (rx_len X) (rx_received X) (rx_traversal X) p (rx_other X)
  else if eq_dec (rx_peer X) p then X
  else
    mkRx (rx_cookie X) (rx_cindex X) (rx_endpoint X) (rx_eskb X) (rx_response X) (rx_session X) (rx_complete X)
         (rx_keepalive X) (rx_stats X) (rx_len X) (rx_received X) (rx_traversal X) (rx_peer X) true.

(* the S23 functions *)
Definition rx_send_cookie (X: rxlog) (idx: int) : rxlog :=
  mkRx (inc (rx_cookie X)) idx (rx_endpoint X) (rx_eskb X) (rx_response X) (rx_session X) (rx_complete X)
       (rx_keepalive X) (rx_stats X) (rx_len X) (rx_received X) (rx_traversal X) (rx_peer X) (rx_other X).
Definition rx_set_endpoint (X: rxlog) (p sk: val) : rxlog :=
  rx_note (mkRx (rx_cookie X) (rx_cindex X) (inc (rx_endpoint X)) sk (rx_response X) (rx_session X)
                (rx_complete X) (rx_keepalive X) (rx_stats X) (rx_len X) (rx_received X) (rx_traversal X)
                (rx_peer X) (rx_other X)) p.
Definition rx_send_response (X: rxlog) (p: val) : rxlog :=
  rx_note (mkRx (rx_cookie X) (rx_cindex X) (rx_endpoint X) (rx_eskb X) (inc (rx_response X)) (rx_session X)
                (rx_complete X) (rx_keepalive X) (rx_stats X) (rx_len X) (rx_received X) (rx_traversal X)
                (rx_peer X) (rx_other X)) p.
Definition rx_session_derived (X: rxlog) (p: val) : rxlog :=
  rx_note (mkRx (rx_cookie X) (rx_cindex X) (rx_endpoint X) (rx_eskb X) (rx_response X) (inc (rx_session X))
                (rx_complete X) (rx_keepalive X) (rx_stats X) (rx_len X) (rx_received X) (rx_traversal X)
                (rx_peer X) (rx_other X)) p.
Definition rx_handshake_complete (X: rxlog) (p: val) : rxlog :=
  rx_note (mkRx (rx_cookie X) (rx_cindex X) (rx_endpoint X) (rx_eskb X) (rx_response X) (rx_session X)
                (inc (rx_complete X)) (rx_keepalive X) (rx_stats X) (rx_len X) (rx_received X) (rx_traversal X)
                (rx_peer X) (rx_other X)) p.
Definition rx_send_keepalive (X: rxlog) (p: val) : rxlog :=
  rx_note (mkRx (rx_cookie X) (rx_cindex X) (rx_endpoint X) (rx_eskb X) (rx_response X) (rx_session X)
                (rx_complete X) (inc (rx_keepalive X)) (rx_stats X) (rx_len X) (rx_received X) (rx_traversal X)
                (rx_peer X) (rx_other X)) p.
Definition rx_update_stats (X: rxlog) (p: val) (len: int64) : rxlog :=
  rx_note (mkRx (rx_cookie X) (rx_cindex X) (rx_endpoint X) (rx_eskb X) (rx_response X) (rx_session X)
                (rx_complete X) (rx_keepalive X) (inc (rx_stats X)) len (rx_received X) (rx_traversal X)
                (rx_peer X) (rx_other X)) p.
Definition rx_auth_received (X: rxlog) (p: val) : rxlog :=
  rx_note (mkRx (rx_cookie X) (rx_cindex X) (rx_endpoint X) (rx_eskb X) (rx_response X) (rx_session X)
                (rx_complete X) (rx_keepalive X) (rx_stats X) (rx_len X) (inc (rx_received X)) (rx_traversal X)
                (rx_peer X) (rx_other X)) p.
Definition rx_auth_traversal (X: rxlog) (p: val) : rxlog :=
  rx_note (mkRx (rx_cookie X) (rx_cindex X) (rx_endpoint X) (rx_eskb X) (rx_response X) (rx_session X)
                (rx_complete X) (rx_keepalive X) (rx_stats X) (rx_len X) (rx_received X) (inc (rx_traversal X))
                (rx_peer X) (rx_other X)) p.

(* the tail of wg_receive_handshake_packet for an authenticated peer p: update_rx_stats(p, skb->len), the two
   timers *)
Definition rx_tail (X: rxlog) (p: val) (len: int) : rxlog :=
  rx_auth_traversal (rx_auth_received (rx_update_stats X p (Int64.repr (Int.unsigned len))) p) p.

(* the harness's checks of the log (rx_only_cookie(cookie), rx_authenticated(p, skb, response, session)) *)
Definition rx_only_cookie_b (X: rxlog) (c: int) : bool :=
  Int.eq (rx_cookie X) c && Int.eq (rx_endpoint X) Int.zero && Int.eq (rx_response X) Int.zero &&
  Int.eq (rx_session X) Int.zero && Int.eq (rx_complete X) Int.zero && Int.eq (rx_keepalive X) Int.zero &&
  Int.eq (rx_stats X) Int.zero && Int.eq (rx_received X) Int.zero && Int.eq (rx_traversal X) Int.zero &&
  (if eq_dec (rx_peer X) nullval then true else false) && negb (rx_other X).
Definition rx_authenticated_b (X: rxlog) (p sp: val) (len: int) (resp sess: int) : bool :=
  Int.eq (rx_cookie X) Int.zero && Int.eq (rx_endpoint X) Int.one &&
  (if eq_dec (rx_eskb X) sp then true else false) &&
  Int.eq (rx_response X) resp && Int.eq (rx_session X) sess && Int.eq (rx_complete X) sess &&
  Int.eq (rx_keepalive X) sess && Int.eq (rx_stats X) Int.one &&
  Int64.eq (rx_len X) (Int64.repr (Int.unsigned len)) && Int.eq (rx_received X) Int.one &&
  Int.eq (rx_traversal X) Int.one && (if eq_dec (rx_peer X) p then true else false) && negb (rx_other X).

(* ------------------------------------------------------------------------------------------------ *)
(* the load: receive.c's last_under_load                                                             *)
(* ------------------------------------------------------------------------------------------------ *)

(* under_load = queue_len >= MAX_QUEUED_INCOMING_HANDSHAKES / 8 (= 512, int); then last_under_load = now;
   else if last_under_load: under_load = !wg_birthdate_has_expired(last_under_load, 1), and 0 when expired.
   Result: (under_load, last_under_load after). *)
Definition load_model (q: int) (lul now: int64) : bool * int64 :=
  if negb (Int.lt q (Int.repr 512)) then (true, now)
  else if Int64.eq lul Int64.zero then (false, lul)
  else if birthdate_expired lul (Int64.repr 1) now then (false, Int64.zero)
  else (true, lul).

(* the mac verdict decides: consume (needs_cookie = false), a cookie reply (true), or the drop *)
Definition rx_consumes (ul: bool) (verdict: Z) : bool :=
  (ul && (verdict =? VALID_MAC_WITH_COOKIE)) || (negb ul && (verdict =? VALID_MAC_BUT_NO_COOKIE)).
Definition rx_needs_cookie (ul: bool) (verdict: Z) : bool :=
  ul && (verdict =? VALID_MAC_BUT_NO_COOKIE).

(* ------------------------------------------------------------------------------------------------ *)
(* the receive world and the model                                                                   *)
(* ------------------------------------------------------------------------------------------------ *)

(* what wg_receive_handshake_packet / dispatch read and write: the device D (its static identity, cookie checker,
   tables), the index table T, the peers PS (public-key chain order), the keypairs KS of the peers' slots, the shim
   S with the refcount_t warnings w, noise.c's keypair_counter kc, receive.c's last_under_load lul, the log X *)
Record rxw := mkRW {
  rw_D: device; rw_T: tstate; rw_PS: list (val * share * peer); rw_KS: list (val * keypair); rw_S: shim;
  rw_w: list int64; rw_kc: int64; rw_lul: int64; rw_rx: rxlog }.

(* the draws of one call: validate's rotation r (32 bytes), the cookie reply's nonce (24) and create's rotation
   r2 (32), the keypair kzalloc returned to begin_session (NULL: the allocation failed) *)
Record rxdraw := mkRD { rd_r: list byte; rd_nonce: list byte; rd_r2: list byte; rd_k: val }.

Section Rx.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* an initiation accepted by consume: the peer a, its state P1 (one more reference) *)
Definition rx_init_accepted (W: rxw) (D1: device) (S1: shim) (lul: int64) (a: val) (P1: peer) (sp: val)
  (len: int) : rxw :=
  let X1 := rx_send_response (rx_set_endpoint (rw_rx W) a sp) a in
  let X2 := rx_tail X1 a len in
  let r := p_refs P1 in
  mkRW D1 (rw_T W) (supd (rw_PS W) a (p_set_refs P1 (rc_sub1 r))) (rw_KS W)
       (if Int.eq (rc_sub1 r) Int.zero then shim_release S1 else S1) (rc_dec_warn r (rw_w W)) (rw_kc W) lul X2.

(* a response accepted by consume: the peer a, its state P1; then begin_session with the keypair k *)
Definition rx_resp_accepted (W: rxw) (D1: device) (S1: shim) (lul: int64) (a: val) (P1: peer) (k: val)
  (sp: val) (len: int) : rxw :=
  let X1 := rx_set_endpoint (rw_rx W) a sp in
  let B := bs_res P1 a k (rw_kc W) (rw_KS W) (rw_T W) S1 in
  let ok := fst (fst (fst B)) in
  let P2 := snd (fst (fst B)) in
  let W2 := snd (fst B) in
  let w2 := begin_session_warn P1 (hs_addr a) k (rw_kc W) (mkKW (rw_KS W) (rw_T W) S1) (rw_w W) in
  let X2 := if ok then rx_send_keepalive (rx_handshake_complete (rx_session_derived X1 a) a) a else X1 in
  let X3 := rx_tail X2 a len in
  let r := p_refs P2 in
  mkRW D1 (kw_T W2) (supd (rw_PS W) a (p_set_refs P2 (rc_sub1 r))) (kw_KS W2)
       (if Int.eq (rc_sub1 r) Int.zero then shim_release (kw_S W2) else kw_S W2) (rc_dec_warn r w2) (snd B) lul X3.

(* wg_receive_handshake_packet(wg, skb) on a forwarded packet: q = the queue length, s = the skb (at sp), msg =
   its bytes *)
Definition rx_packet (W: rxw) (q: int) (sp: val) (s: skb) (msg: list byte) (d: rxdraw) : rxw :=
  let D := rw_D W in let S := rw_S W in let now := s_boot S in
  let tw := hrx5_tw msg in
  if Int.eq tw (Int.repr 3) then
    mkRW D (rw_T W) (peers_after (rw_PS W) (mcons_res xaead_dec (rw_T W) (rw_PS W) (cm_of msg) S)) (rw_KS W) S
         (rw_w W) (rw_kc W) (rw_lul W) (rw_rx W)
  else
  let ul := fst (load_model q (rw_lul W) now) in
  let lul := snd (load_model q (rw_lul W) now) in
  let CC := d_cc D in
  let vm := validate_model CC s msg ul now (s_rlallow S) (rd_r d) in
  let D1 := dev_set_cc D (snd vm) in
  let S1 := if validate_rotates CC msg ul now then shim_draw S (rd_r d) else S in
  if rx_consumes ul (fst vm) then
    if Int.eq tw Int.one then
      match cin_res x25519 aead_dec D1 (rw_PS W) (im_of msg) S1 with
      | None => mkRW D1 (rw_T W) (rw_PS W) (rw_KS W) S1 (rw_w W) (rw_kc W) lul (rw_rx W)
      | Some (a, P1) => rx_init_accepted W D1 S1 lul a P1 sp (sk_len s)
      end
    else
      match cre_res x25519 aead_dec D1 (rw_T W) (rw_PS W) (rm_of msg) with
      | None => mkRW D1 (rw_T W) (rw_PS W) (rw_KS W) S1 (rw_w W) (rw_kc W) lul (rw_rx W)
      | Some (a, P1) => rx_resp_accepted W D1 S1 lul a P1 (rd_k d) sp (sk_len s)
      end
  else if rx_needs_cookie ul (fst vm) then
    let idx := hrx5_w4 msg in
    let CC1 := snd vm in
    let MC := mc_res xaead_enc CC1 s idx (rd_nonce d) msg S1 (rd_r2 d) in
    mkRW (dev_set_cc D (snd MC)) (rw_T W) (rw_PS W) (rw_KS W)
         (if checker_rotates CC1 now then shim_draw (shim_draw S1 (rd_nonce d)) (rd_r2 d) else shim_draw S1 (rd_nonce d))
         (rw_w W) (rw_kc W) lul (rx_send_cookie (rw_rx W) idx)
  else
    mkRW D1 (rw_T W) (rw_PS W) (rw_KS W) S1 (rw_w W) (rw_kc W) lul (rw_rx W).

(* dispatch(wg, skb): nothing unless forwarded *)
Definition rx_model (W: rxw) (q: int) (sp: val) (s: skb) (msg: list byte) (d: rxdraw) : rxw :=
  if hrx5_fwd msg then rx_packet W q sp s msg d else W.

End Rx.

(* the draws are well-formed; a keypair kzalloc returned is not in the table's pool *)
Definition rxdraw_ok (T: tstate) (d: rxdraw) : Prop :=
  Zlength (rd_r d) = 32 /\ Zlength (rd_nonce d) = 24 /\ Zlength (rd_r2 d) = 32 /\
  (rd_k d <> nullval -> ~ In (rd_k d) (saddrs (t_D T))).
