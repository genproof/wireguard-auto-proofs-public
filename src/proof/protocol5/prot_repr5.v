(* The representation of the protocol state for the per-law programs of the short handshake laws (hs_).

   Those programs link noise.c, the primitives, the shim and libc, but not cookie.c (per-law linking), and
   their harnesses (harness/hs_laws.h) set up devices and peers in uninitialised memory, writing only what
   noise.c reads.  The v4 representation (prot_repr3.v) cannot describe that state:
   - wg_consts includes cookie.c's read-only globals (mac1_key_label, cookie_key_label), absent here;
   - device_rep includes the cookie checker and the net_device pointer, never written by hs_laws.h;
   - peer_rep includes the latest cookie, last_sent_handshake and internal_id, never written by hs_laws.h;
   - init_rep / resp_rep include the macs, which the handshake functions of noise.c never write (cookie.c
     does), so a message created in uninitialised memory has undefined macs.
   This file keeps every other predicate of v3/v4 and gives the four variants with those parts "any value"
   (field_at_ / existential); the model (prot_model3.v) is unchanged and its corresponding fields are simply
   not represented.  Every v4 state satisfies the v5 predicates (v5 forgets information). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Local Open Scope logic.

Section NoiseCS5.
#[local] Existing Instance Noise.CS.

(* the read-only globals of the primitives (wg_consts without cookie.c's labels) *)
Definition wg_consts5 (gv: globals) : mpred :=
  blake2s_globals gv * @curve25519_globals Noise.CS gv * @zero_page Noise.CS gv.

(* struct wg_device: the identity and the two table pointers; dev and cookie_checker any *)
Definition device_rep5 (sh: share) (wg: val) (D: device) : mpred :=
  !! field_compatible t_dev [] wg &&
  (field_at_ sh t_dev [StructField I._dev] wg *
   identity_rep sh (id_addr wg) (d_id D) *
   field_at_ sh t_dev [StructField I._cookie_checker] wg *
   field_at sh t_dev [StructField I._peer_hashtable] (d_ptab D) wg *
   field_at sh t_dev [StructField I._index_hashtable] (d_itab D) wg).

(* struct wg_peer at p, without its handshake's entry; last_sent_handshake, latest_cookie and internal_id
   any (p_lsh, p_cookie, p_id of the model are not represented) *)
Definition peer_rep5 (sh: share) (p: val) (P: peer) : mpred :=
  !! field_compatible t_peer [] p &&
  (field_at sh t_peer [StructField I._device] (p_device P) p *
   field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   field_at_ sh t_peer [StructField I._last_sent_handshake] p *
   field_at_ sh t_peer [StructField I._latest_cookie] p *
   field_at sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   field_at_ sh t_peer [StructField I._internal_id] p *
   field_at sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Definition peer_item_rep5 (x: val * share * peer) : mpred := match x with (a, sh, P) => peer_rep5 sh a P end.
Definition peers_rep5 (PS: list (val * share * peer)) : mpred := iter_sepcon peer_item_rep5 PS.

(* the messages with their macs any (lengths of the other byte fields as im_ok / rm_ok) *)
Definition im_ok5 (M: init_msg) : Prop :=
  Zlength (im_eph M) = 32 /\ Zlength (im_encs M) = 48 /\ Zlength (im_enct M) = 28.
Definition rm_ok5 (M: resp_msg) : Prop :=
  Zlength (rm_eph M) = 32 /\ Zlength (rm_encn M) = 16.

Definition init_rep5 (sh: share) (m: val) (M: init_msg) : mpred :=
  !! im_ok5 M &&
  (field_at sh t_init [StructField I._header] (Vint (im_type M)) m *
   field_at sh t_init [StructField I._sender_index] (Vint (im_sender M)) m *
   field_at sh t_init [StructField I._unencrypted_ephemeral] (bytes (im_eph M)) m *
   field_at sh t_init [StructField I._encrypted_static] (bytes (im_encs M)) m *
   field_at sh t_init [StructField I._encrypted_timestamp] (bytes (im_enct M)) m *
   field_at_ sh t_init [StructField I._macs] m).

Definition resp_rep5 (sh: share) (m: val) (M: resp_msg) : mpred :=
  !! rm_ok5 M &&
  (field_at sh t_resp [StructField I._header] (Vint (rm_type M)) m *
   field_at sh t_resp [StructField I._sender_index] (Vint (rm_sender M)) m *
   field_at sh t_resp [StructField I._receiver_index] (Vint (rm_receiver M)) m *
   field_at sh t_resp [StructField I._unencrypted_ephemeral] (bytes (rm_eph M)) m *
   field_at sh t_resp [StructField I._encrypted_nothing] (bytes (rm_encn M)) m *
   field_at_ sh t_resp [StructField I._macs] m).

(* a message buffer before create_initiation / create_response: a message (Some M) or uninitialised memory
   (None) *)
Definition init_opt_rep (sh: share) (m: val) (Mo: option init_msg) : mpred :=
  match Mo with Some M => init_rep5 sh m M | None => data_at_ sh t_init m end.
Definition resp_opt_rep (sh: share) (m: val) (Mo: option resp_msg) : mpred :=
  match Mo with Some M => resp_rep5 sh m M | None => data_at_ sh t_resp m end.

End NoiseCS5.

(* the message a model step starts from when the buffer is uninitialised: create_initiation_model and
   create_response_model overwrite every field init_rep5 / resp_rep5 represent when they succeed *)
Definition init_msg0 : init_msg := mkIM Int.zero Int.zero (zeros 32) (zeros 48) (zeros 28) (zeros 16) (zeros 16).
Definition resp_msg0 : resp_msg := mkRM Int.zero Int.zero Int.zero (zeros 32) (zeros 16) (zeros 16) (zeros 16).
Definition init_of (Mo: option init_msg) : init_msg := match Mo with Some M => M | None => init_msg0 end.
Definition resp_of (Mo: option resp_msg) : resp_msg := match Mo with Some M => M | None => resp_msg0 end.

(* the buffer after a create step with result ok and model message M': defined if the step succeeded or the
   buffer was a message before *)
Definition opt_after {A: Type} (ok: bool) (Mo: option A) (M': A) : option A :=
  if ok then Some M' else match Mo with Some _ => Some M' | None => None end.
