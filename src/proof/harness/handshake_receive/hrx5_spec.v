(* law handshake_receive:
   the specifications of the harness unit's OWN functions but main (the extracted receive.c of
   patch/receive_handshake.c with its recording shim S23, and the harness's helpers), and their context.

   - The local functions are proved at the harness's own compspecs HRX (unit u_hrx5l); main (hrx5_main*.v, later)
     at the world.  CSw (the world: malloc tokens, mem_mgr) is a parameter, as in protocol4 / common4.
   - Their imports: hrx5_imports cs = common4's hc4_imports (environment, lower pieces, protocol4's prot_G4) ++
     hc4_G_handshake_receive (the common.h functions of this unit).  Context of a body proof:
     hrx5_Gl cs = hrx5_imports cs ++ hrx5_G_local.
   - The objects: the protocol's (prot_repr3, Noise.CS / Cookie.CS) with the shim's state exact (shim_state4); the
     receive.c globals: wg_shim_rx (rxlog_rep, struct wg_shim_rx_log at HRX), last_under_load (lul_rep),
     wg_shim_handshake_queue_len (qlen_rep); a message = its byte image `msg` at skb->data (bytes_at) of skb->len
     bytes, malloc'd (malloc_compatible: aligned, so that the type word is a u32 load);
   - wg_receive_handshake_packet / dispatch: the model rx_packet / rx_model of hrx5_model.v over the receive world
     rxw (rxw_rep), the draws existential (rxdraw_ok). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require WgNoise.contracts.x_handshake_receive.
Require WgNoise.harness.x_handshake_receive.code.
Local Open Scope logic.

Module HRC := WgNoise.harness.x_handshake_receive.code.

(* the harness unit's compspecs *)
Definition HRX : compspecs := WgNoise.contracts.x_handshake_receive.Harness.CS.

Definition t_rxlog := Tstruct HRC._wg_shim_rx_log noattr.

(* ------------------------------------------------------------------------------------------------ *)
(* the globals of receive.c's extract and of the harness                                             *)
(* ------------------------------------------------------------------------------------------------ *)

Section HRXvals.
#[local] Existing Instance HRX.

Definition rxlog_val (X: rxlog) : reptype t_rxlog :=
  (Vint (rx_cookie X), (Vint (rx_cindex X), (Vint (rx_endpoint X), (rx_eskb X, (Vint (rx_response X),
   (Vint (rx_session X), (Vint (rx_complete X), (Vint (rx_keepalive X), (Vint (rx_stats X), (Vlong (rx_len X),
   (Vint (rx_received X), (Vint (rx_traversal X), (rx_peer X, Val.of_bool (rx_other X)))))))))))))).

(* wg_shim_rx, last_under_load, wg_shim_handshake_queue_len *)
Definition rxlog_rep (gv: globals) (X: rxlog) : mpred := data_at Ews t_rxlog (rxlog_val X) (gv HRC._wg_shim_rx).
Definition lul_rep (gv: globals) (lul: int64) : mpred :=
  data_at Ews tulong (Vlong lul) (gv HRC._last_under_load).
Definition qlen_rep (gv: globals) (q: int) : mpred :=
  data_at Ews tint (Vint q) (gv HRC._wg_shim_handshake_queue_len).

(* the harness's constants (common.h's, renamed for this unit) *)
Definition hrx5_consts (gv: globals) : mpred :=
  hc_const gv HRC._x_handshake_receive__M_BASEPOINT basepoint9 *
  hc_const gv HRC._x_handshake_receive__M_CONSTRUCTION construction_bytes *
  hc_const gv HRC._x_handshake_receive__M_IDENTIFIER identifier_bytes *
  hc_const gv HRC._x_handshake_receive__M_LABEL_MAC1 mac1_label.
End HRXvals.

(* ------------------------------------------------------------------------------------------------ *)
(* the receive world                                                                                 *)
(* ------------------------------------------------------------------------------------------------ *)

(* the device wg (share shd: also its tables'), its index table, its public-key table (chain from head), the peers,
   the slots' keypairs, the shim, noise.c's globals, last_under_load and the log *)
Definition rxw_rep (CSw: compspecs) (gv: globals) (shd: share) (wg head: val) (W: rxw) : mpred :=
  device_rep shd wg (rw_D W) * itable shd (d_itab (rw_D W)) (rw_T W) * ptable shd (d_ptab (rw_D W)) head *
  peers_rep (rw_PS W) * keypairs_rep CSw (rw_KS W) * shim_state4 gv (rw_S W) (rw_w W) *
  noise_globals gv (rw_kc W) * lul_rep gv (rw_lul W) * rxlog_rep gv (rw_rx W).

(* what the calls need of every peer: its device, empty keypair slots (the harness clears them after a session),
   its handshake entry in the table's pool, the 20 ms test's signed addition *)
Definition rx_peer_ok (wg: val) (T: tstate) (x: val * share * peer) : Prop :=
  match x with (p, _, P) =>
    p_device P = wg /\ p_cur P = nullval /\ p_prev P = nullval /\ p_next P = nullval /\ hs_in_pool T p /\
    Int64.signed (hs_lic (p_hs P)) <= Int64.max_signed - 20000000
  end.
Definition rx_peers_ok (wg: val) (T: tstate) (PS: list (val * share * peer)) : Prop :=
  peers_wf PS /\ peers_refs_ok PS /\ pool_peers_ok T PS /\ Forall (rx_peer_ok wg T) PS.

(* the message: msg = the bytes at skb->data, skb->len of them, in a malloc'd (aligned) buffer *)
Definition rx_msg_ok (s: skb) (msg: list byte) : Prop :=
  Zlength msg = Int.unsigned (sk_len s) /\ malloc_compatible (Zlength msg) (sk_data s).

(* the preconditions of wg_receive_handshake_packet / dispatch on the world *)
Definition rxw_ok (wg head: val) (W: rxw) : Prop :=
  pk_chain head (rw_PS W) /\ rx_peers_ok wg (rw_T W) (rw_PS W) /\ rw_KS W = [] /\ rx_peer (rw_rx W) = nullval.

(* ------------------------------------------------------------------------------------------------ *)
(* the specifications                                                                                *)
(* ------------------------------------------------------------------------------------------------ *)

(* the skb as m_cookie / draw_macs read it: only its protocol and source *)
Definition skb_src_rep (sh: share) (p dv lv: val) (s: skb) : mpred :=
  !! skb_ok s && @data_at Cookie.CS sh t_skb (dv, (lv, snd (snd (skb_val s)))) p.

Lemma skb_src_rep_full sh p s : skb_rep sh p s = skb_src_rep sh p (sk_data s) (Vint (sk_len s)) s.
Proof. reflexivity. Qed.

Section Specs.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.
#[local] Existing Instance HRX.

(* the first field of a peer: p is a valid pointer (for the S23 functions' pointer comparisons) *)
Definition rx_pfield (sh: share) (p d: val) : mpred :=
  @field_at Noise.CS sh t_peer [StructField I._device] d p.

(* ---- S23: the recording shim ---- *)

Definition hrx5_rx_peer_spec :=
  DECLARE HRC._wg_shim_rx_peer
  WITH gv: globals, X: rxlog, p: val, sh: share, d: val
  PRE [ tptr t_peer ]
    PROP (readable_share sh; rx_peer X = nullval \/ rx_peer X = p) PARAMS (p) GLOBALS (gv)
    SEP (rxlog_rep gv X; rx_pfield sh p d)
  POST [ tvoid ]
    PROP () RETURN () SEP (rxlog_rep gv (rx_note X p); rx_pfield sh p d).

(* wg_packet_send_handshake_cookie(wg, skb, index): send.c's body (wg_cookie_message_create into a local
   message) without the socket send; recorded *)
Definition hrx5_send_cookie_spec :=
  DECLARE HRC._wg_packet_send_handshake_cookie
  WITH gv: globals, S: shim, w: list int64, X: rxlog, shc: share, wg: val, CC: checker, shs: share, sp: val,
       s: skb, shm: share, msg: list byte, idx: int
  PRE [ tptr t_dev, tptr t_skb, tuint ]
    PROP (writable_share shc; readable_share shs; readable_share shm; 32 <= Zlength msg;
          Zlength msg = Int.unsigned (sk_len s); field_compatible t_dev [] wg)
    PARAMS (wg; sp; Vint idx) GLOBALS (gv)
    SEP (checker_rep shc (cc_addr wg) CC; skb_rep shs sp s; bytes_at shm msg (sk_data s);
         shim_state4 gv S w; wg_consts gv; rxlog_rep gv X)
  POST [ tvoid ] EX nonce: list byte, EX r: list byte,
    PROP (Zlength nonce = 24; Zlength r = 32) RETURN ()
    SEP (checker_rep shc (cc_addr wg) (snd (mc_res xaead_enc CC s idx nonce msg S r));
         skb_rep shs sp s; bytes_at shm msg (sk_data s);
         shim_state4 gv (if checker_rotates CC (s_boot S) then shim_draw (shim_draw S nonce) r
                        else shim_draw S nonce) w;
         wg_consts gv; rxlog_rep gv (rx_send_cookie X idx)).

Definition hrx5_set_endpoint_spec :=
  DECLARE HRC._wg_socket_set_peer_endpoint_from_skb
  WITH gv: globals, X: rxlog, p: val, sh: share, d: val, sk: val
  PRE [ tptr t_peer, tptr t_skb ]
    PROP (readable_share sh; rx_peer X = nullval \/ rx_peer X = p) PARAMS (p; sk) GLOBALS (gv)
    SEP (rxlog_rep gv X; rx_pfield sh p d)
  POST [ tvoid ]
    PROP () RETURN () SEP (rxlog_rep gv (rx_set_endpoint X p sk); rx_pfield sh p d).

Definition hrx5_send_response_spec :=
  DECLARE HRC._wg_packet_send_handshake_response
  WITH gv: globals, X: rxlog, p: val, sh: share, d: val
  PRE [ tptr t_peer ]
    PROP (readable_share sh; rx_peer X = nullval \/ rx_peer X = p) PARAMS (p) GLOBALS (gv)
    SEP (rxlog_rep gv X; rx_pfield sh p d)
  POST [ tvoid ]
    PROP () RETURN () SEP (rxlog_rep gv (rx_send_response X p); rx_pfield sh p d).

Definition hrx5_session_derived_spec :=
  DECLARE HRC._wg_timers_session_derived
  WITH gv: globals, X: rxlog, p: val, sh: share, d: val
  PRE [ tptr t_peer ]
    PROP (readable_share sh; rx_peer X = nullval \/ rx_peer X = p) PARAMS (p) GLOBALS (gv)
    SEP (rxlog_rep gv X; rx_pfield sh p d)
  POST [ tvoid ]
    PROP () RETURN () SEP (rxlog_rep gv (rx_session_derived X p); rx_pfield sh p d).

Definition hrx5_handshake_complete_spec :=
  DECLARE HRC._wg_timers_handshake_complete
  WITH gv: globals, X: rxlog, p: val, sh: share, d: val
  PRE [ tptr t_peer ]
    PROP (readable_share sh; rx_peer X = nullval \/ rx_peer X = p) PARAMS (p) GLOBALS (gv)
    SEP (rxlog_rep gv X; rx_pfield sh p d)
  POST [ tvoid ]
    PROP () RETURN () SEP (rxlog_rep gv (rx_handshake_complete X p); rx_pfield sh p d).

Definition hrx5_send_keepalive_spec :=
  DECLARE HRC._wg_packet_send_keepalive
  WITH gv: globals, X: rxlog, p: val, sh: share, d: val
  PRE [ tptr t_peer ]
    PROP (readable_share sh; rx_peer X = nullval \/ rx_peer X = p) PARAMS (p) GLOBALS (gv)
    SEP (rxlog_rep gv X; rx_pfield sh p d)
  POST [ tvoid ]
    PROP () RETURN () SEP (rxlog_rep gv (rx_send_keepalive X p); rx_pfield sh p d).

Definition hrx5_auth_received_spec :=
  DECLARE HRC._wg_timers_any_authenticated_packet_received
  WITH gv: globals, X: rxlog, p: val, sh: share, d: val
  PRE [ tptr t_peer ]
    PROP (readable_share sh; rx_peer X = nullval \/ rx_peer X = p) PARAMS (p) GLOBALS (gv)
    SEP (rxlog_rep gv X; rx_pfield sh p d)
  POST [ tvoid ]
    PROP () RETURN () SEP (rxlog_rep gv (rx_auth_received X p); rx_pfield sh p d).

Definition hrx5_auth_traversal_spec :=
  DECLARE HRC._wg_timers_any_authenticated_packet_traversal
  WITH gv: globals, X: rxlog, p: val, sh: share, d: val
  PRE [ tptr t_peer ]
    PROP (readable_share sh; rx_peer X = nullval \/ rx_peer X = p) PARAMS (p) GLOBALS (gv)
    SEP (rxlog_rep gv X; rx_pfield sh p d)
  POST [ tvoid ]
    PROP () RETURN () SEP (rxlog_rep gv (rx_auth_traversal X p); rx_pfield sh p d).

Definition hrx5_update_rx_stats_spec :=
  DECLARE HRC._update_rx_stats
  WITH gv: globals, X: rxlog, p: val, sh: share, d: val, len: int64
  PRE [ tptr t_peer, tulong ]
    PROP (readable_share sh; rx_peer X = nullval \/ rx_peer X = p) PARAMS (p; Vlong len) GLOBALS (gv)
    SEP (rxlog_rep gv X; rx_pfield sh p d)
  POST [ tvoid ]
    PROP () RETURN () SEP (rxlog_rep gv (rx_update_stats X p len); rx_pfield sh p d).

(* ---- receive.c ---- *)

Definition hrx5_vhl_spec :=
  DECLARE HRC._validate_header_len
  WITH shs: share, sp: val, s: skb, shm: share, msg: list byte
  PRE [ tptr t_skb ]
    PROP (readable_share shs; readable_share shm; rx_msg_ok s msg) PARAMS (sp)
    SEP (skb_rep shs sp s; bytes_at shm msg (sk_data s))
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (vhl_model msg)))
    SEP (skb_rep shs sp s; bytes_at shm msg (sk_data s)).

(* wg_receive_handshake_packet(wg, skb) of a forwarded packet (type word 1, 2 or 3, exact length) *)
Definition hrx5_receive_spec :=
  DECLARE HRC._wg_receive_handshake_packet
  WITH gv: globals, W: rxw, q: int, shd: share, wg: val, head: val, shs: share, sp: val, s: skb, shm: share,
       msg: list byte
  PRE [ tptr t_dev, tptr t_skb ]
    PROP (writable_share shd; readable_share shs; readable_share shm; hrx5_fwd msg = true; rx_msg_ok s msg;
          rxw_ok wg head W)
    PARAMS (wg; sp) GLOBALS (gv)
    SEP (rxw_rep CSw gv shd wg head W; qlen_rep gv q; skb_rep shs sp s; bytes_at shm msg (sk_data s);
         wg_consts gv; mem_mgr gv)
  POST [ tvoid ] EX d: rxdraw,
    PROP (rxdraw_ok (rw_T W) d) RETURN ()
    SEP (rxw_rep CSw gv shd wg head (rx_packet x25519 aead_dec xaead_enc xaead_dec W q sp s msg d);
         qlen_rep gv q; skb_rep shs sp s; bytes_at shm msg (sk_data s); wg_consts gv; mem_mgr gv).

(* dispatch(wg, skb): any packet *)
Definition hrx5_dispatch_spec :=
  DECLARE HRC._dispatch
  WITH gv: globals, W: rxw, q: int, shd: share, wg: val, head: val, shs: share, sp: val, s: skb, shm: share,
       msg: list byte
  PRE [ tptr t_dev, tptr t_skb ]
    PROP (writable_share shd; readable_share shs; readable_share shm; rx_msg_ok s msg; rxw_ok wg head W)
    PARAMS (wg; sp) GLOBALS (gv)
    SEP (rxw_rep CSw gv shd wg head W; qlen_rep gv q; skb_rep shs sp s; bytes_at shm msg (sk_data s);
         wg_consts gv; mem_mgr gv)
  POST [ tvoid ] EX d: rxdraw,
    PROP (rxdraw_ok (rw_T W) d) RETURN ()
    SEP (rxw_rep CSw gv shd wg head (rx_model x25519 aead_dec xaead_enc xaead_dec W q sp s msg d);
         qlen_rep gv q; skb_rep shs sp s; bytes_at shm msg (sk_data s); wg_consts gv; mem_mgr gv).

(* ---- the harness's helpers ---- *)

(* m_expired(birthdate, seconds, now) = wg_birthdate_has_expired as the model states it *)
Definition hrx5_m_expired_spec :=
  DECLARE HRC._m_expired
  WITH b: int64, sc: int64, n: int64
  PRE [ tulong, tulong, tulong ]
    PROP () PARAMS (Vlong b; Vlong sc; Vlong n) SEP ()
  POST [ tint ]
    PROP () RETURN (Vint (if birthdate_expired b sc n then Int.one else Int.zero)) SEP ().

(* m_cookie(out, secret, skb): D's cookie for the packet's source with the secret SECRET *)
Definition hrx5_m_cookie_spec :=
  DECLARE HRC._m_cookie
  WITH gv: globals, sho: share, o: val, shk: share, k: val, SECRET: list byte, shs: share, sp: val, s: skb,
       dv: val, lv: val
  PRE [ tptr tuchar, tptr tuchar, tptr t_skb ]
    PROP (writable_share sho; readable_share shk; readable_share shs; Zlength SECRET = 32)
    PARAMS (o; k; sp) GLOBALS (gv)
    SEP (hout sho 16 o; hbytes shk SECRET k; skb_src_rep shs sp dv lv s; blake2s_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (hbytes sho (cookie_of SECRET s) o; hbytes shk SECRET k; skb_src_rep shs sp dv lv s; blake2s_globals gv).

Definition hrx5_rx_reset_spec :=
  DECLARE HRC._rx_reset
  WITH gv: globals
  PRE [ ] PROP () PARAMS () GLOBALS (gv) SEP (data_at_ Ews t_rxlog (gv HRC._wg_shim_rx))
  POST [ tvoid ] PROP () RETURN () SEP (rxlog_rep gv rx0).

Definition hrx5_rx_only_cookie_spec :=
  DECLARE HRC._rx_only_cookie
  WITH gv: globals, X: rxlog, c: int
  PRE [ tuint ]
    PROP (rx_peer X = nullval) PARAMS (Vint c) GLOBALS (gv) SEP (rxlog_rep gv X)
  POST [ tint ]
    PROP () RETURN (Vint (if rx_only_cookie_b X c then Int.one else Int.zero)) SEP (rxlog_rep gv X).

Definition hrx5_rx_authenticated_spec :=
  DECLARE HRC._rx_authenticated
  WITH gv: globals, X: rxlog, p: val, sh: share, d: val, shs: share, sp: val, s: skb, resp: int, sess: int
  PRE [ tptr t_peer, tptr t_skb, tuint, tuint ]
    PROP (readable_share sh; readable_share shs; rx_peer X = nullval \/ rx_peer X = p;
          rx_eskb X = nullval \/ rx_eskb X = sp)
    PARAMS (p; sp; Vint resp; Vint sess) GLOBALS (gv)
    SEP (rxlog_rep gv X; rx_pfield sh p d; skb_rep shs sp s)
  POST [ tint ]
    PROP () RETURN (Vint (if rx_authenticated_b X p sp (sk_len s) resp sess then Int.one else Int.zero))
    SEP (rxlog_rep gv X; rx_pfield sh p d; skb_rep shs sp s).

(* draw_type(t): any word (t, t with nonzero reserved bytes, or any u32) *)
Definition hrx5_draw_type_spec :=
  DECLARE HRC._draw_type
  WITH t: int
  PRE [ tuint ] PROP () PARAMS (Vint t) SEP ()
  POST [ tuint ] EX r: int, PROP () RETURN (Vint r) SEP ().

(* draw_macs(img, len, mk1, secret, skb): the last 32 bytes of the image replaced (any bytes) *)
Definition hrx5_draw_macs_spec :=
  DECLARE HRC._draw_macs
  WITH gv: globals, shi: share, i: val, IMG: list byte, shk: share, k: val, MK1: list byte, shc: share, c: val,
       SEC: list byte, shs: share, sp: val, s: skb, dv: val, lv: val
  PRE [ tptr tuchar, tulong, tptr tuchar, tptr tuchar, tptr t_skb ]
    PROP (writable_share shi; readable_share shk; readable_share shc; readable_share shs;
          32 <= Zlength IMG <= Int64.max_signed; Zlength MK1 = 32; Zlength SEC = 32)
    PARAMS (i; Vlong (Int64.repr (Zlength IMG)); k; c; sp) GLOBALS (gv)
    SEP (hbytes shi IMG i; hbytes shk MK1 k; hbytes shc SEC c; skb_src_rep shs sp dv lv s; blake2s_globals gv)
  POST [ tvoid ] EX IMG': list byte,
    PROP (Zlength IMG' = Zlength IMG; sublist 0 (Zlength IMG - 32) IMG' = sublist 0 (Zlength IMG - 32) IMG)
    RETURN ()
    SEP (hbytes shi IMG' i; hbytes shk MK1 k; hbytes shc SEC c; skb_src_rep shs sp dv lv s; blake2s_globals gv).

(* k_initiation(m, ik, id, ss_k): some well-formed initiation (K's, as the model builds it, or the message as it
   was); the real-time clock drawn *)
Definition hrx5_k_initiation_spec :=
  DECLARE HRC._k_initiation
  WITH gv: globals, S: shim, w: list int64, shm: share, m: val, M: init_msg, shi: share, ik: val, IK: mident,
       id: val, ID: mident, shk: share, sk: val, SSK: list byte
  PRE [ tptr t_init, tptr t_mident, tptr t_mident, tptr tuchar ]
    PROP (writable_share shm; readable_share shi; writable_share shk; Zlength (mi_priv IK) = 32;
          Zlength (mi_pub IK) = 32; Zlength (mi_priv ID) = 32; Zlength (mi_pub ID) = 32; Zlength SSK = 32)
    PARAMS (m; ik; id; sk) GLOBALS (gv)
    SEP (init_rep shm m M; @data_at HCS shi t_mident (mident_val IK) ik;
         @data_at HCS shi t_mident (mident_val ID) id; hbytes shk SSK sk;
         shim_state4 gv S w; wg_consts gv; hrx5_consts gv)
  POST [ tvoid ] EX M': init_msg, EX sec: int64, EX ns: Z,
    PROP (im_ok M'; 0 <= ns < 1000000000) RETURN ()
    SEP (init_rep shm m M'; @data_at HCS shi t_mident (mident_val IK) ik;
         @data_at HCS shi t_mident (mident_val ID) id; hbytes shk SSK sk;
         shim_state4 gv (shim_set_real S sec (Int64.repr ns)) w; wg_consts gv; hrx5_consts gv).

(* k_response(m, &p->handshake, t, id): maybe p's handshake is made one that waits for a response (state
   CREATED_INITIATION, its entry inserted into t if it was not hashed), then some well-formed response *)
Definition hrx5_k_response_spec :=
  DECLARE HRC._k_response
  WITH gv: globals, S: shim, w: list int64, shm: share, m: val, M: resp_msg, shp: share, p: val, P: peer,
       sht: share, tab: val, T: tstate, shi: share, id: val, ID: mident
  PRE [ tptr t_resp, tptr t_hs, tptr t_itab, tptr t_mident ]
    PROP (writable_share shm; writable_share shp; writable_share sht; readable_share shi;
          In (hs_addr p) (saddrs (t_D T)); Zlength (mi_priv ID) = 32; Zlength (mi_pub ID) = 32)
    PARAMS (m; hs_addr p; tab; id) GLOBALS (gv)
    SEP (resp_rep shm m M; peer_rep shp p P; itable sht tab T; @data_at HCS shi t_mident (mident_val ID) id;
         shim_state4 gv S w; wg_consts gv; hrx5_consts gv)
  POST [ tvoid ] EX M': resp_msg, EX b: bool, EX idx: int,
    PROP (rm_ok M'; b = true -> ~ In (hs_addr p) (t_L T) -> t_fresh T (hs_addr p) idx) RETURN ()
    SEP (resp_rep shm m M';
         peer_rep shp p (if b then p_set_hs P (hs_set_state (p_hs P) HS_CREATED_INITIATION) else P);
         itable sht tab (if andb b (negb (vin (hs_addr p) (t_L T))) then t_insert T (hs_addr p) idx else T);
         @data_at HCS shi t_mident (mident_val ID) id;
         shim_state4 gv (if andb b (negb (vin (hs_addr p) (t_L T))) then shim_u32 S idx else S) w;
         wg_consts gv; hrx5_consts gv).

(* every local function but main, in the order of the unit *)
Definition hrx5_G_local : funspecs :=
  [hrx5_rx_peer_spec; hrx5_send_cookie_spec; hrx5_set_endpoint_spec; hrx5_send_response_spec;
   hrx5_session_derived_spec; hrx5_handshake_complete_spec; hrx5_send_keepalive_spec; hrx5_auth_received_spec;
   hrx5_auth_traversal_spec; hrx5_update_rx_stats_spec; hrx5_vhl_spec; hrx5_receive_spec; hrx5_m_expired_spec;
   hrx5_m_cookie_spec; hrx5_rx_reset_spec; hrx5_rx_only_cookie_spec; hrx5_rx_authenticated_spec;
   hrx5_dispatch_spec; hrx5_draw_type_spec; hrx5_k_initiation_spec; hrx5_k_response_spec; hrx5_draw_macs_spec].

(* the imports: environment, lower pieces, protocol4, and the unit's common.h functions (common4) *)
Definition hrx5_imports (cs: compspecs) : funspecs :=
  hc4_imports x25519 aead_enc aead_dec xaead_enc xaead_dec CSw cs ++
  hc4_G_handshake_receive x25519 aead_enc aead_dec CSw.

(* the context of a body proof at the unit's compspecs cs *)
Definition hrx5_Gl (cs: compspecs) : funspecs := hrx5_imports cs ++ hrx5_G_local.

End Specs.

(* the varspecs of the WHOLE program (literal) *)
Definition hrx5_V : varspecs :=
  ltac:(let x := eval vm_compute in (QPvarspecs WgNoise.contracts.x_handshake_receive.whole_prog) in exact x).

(* the unit of the local functions, at the harness's compspecs *)
Definition u_hrx5l : unit_ctx := mk_unit HRX hrx5_V HRC.prog.

(* the statement of the local piece (proved in hrx5_lpiece.v from the body lemmas) *)
Definition hrx5_lpiece_stmt : Prop :=
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  piece_ok [u_hrx5l] (hrx5_imports x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
    (hrx5_G_local x25519 aead_dec xaead_enc xaead_dec CSw).
