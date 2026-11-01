(* ONE
   specification per function of the harness/common.h that the v1 layer (hc_specs3.v) does not cover or
   covers too weakly, for the any-state laws (config_any, consume_initiation_any, consume_response_any, cookie_mac,
   cookie_reply, create_any, handshake_clear, handshake_receive, keypairs).  The other common.h functions keep their
   hc_specs3.v specification (and body proofs, lifted with hc3_lift.v).

   - structs (pr_snap, dev_snap, shim_snap, struct kent, struct hnode with `rest`, skb_snap) at the
     compspecs CKS of law cookie_mac's unit (it has all of them); hs_snap at HCS as in hc_specs3.v; the protocol's
     objects at Noise.CS / Cookie.CS (prot_repr3.v) and the shim's state with EXACT warnings (`shim_state4 gv S w`,
     prot_repr4.v);
   - the harness's peer list: `hnodes_rep4 CSw l NS` (v1's hnodes_rep with the `rest` snapshot), the peers' memory
     is the protocol's peers_rep PS (same order, hnodes_peers4), their handshake entries are pool items of the index
     table T;
   - the kents: `kents_rep CSw l KE`, each a malloc'd struct kent whose keypair's ENTRY (at the kent's address) is a
     pool item of the index table T (owned by `itable`), the rest of the keypair `kp_body_rep` (keypair_rep without
     its kzalloc token), the snapshot fields `kent_snap_rep`, the list link and the struct's padding;
   - comparisons: pure boolean results (hc4_model.v); every compared pointer is NULL, one of the addresses whose
     memory the specification's own SEP holds, or an address of the objects VO the caller LENDS to the call
     (`vobjs CSw VO` in the SEP, given back unchanged: peers, a device, an index table, kents, keypairs, byte
     buffers, memory blocks, empty malloc'd objects; `vobjs_addrs VO`; v4.1: VKents /
     VKeypairs lend no address - their byte 0 is an index-table entry - lend the table VItab instead).  (A frame `R: mpred` in the WITH clause is impossible: universe
     inconsistency of NDmk_funspec.)
   - hs_take / hs_same / hs_zeroed_from / hs_same_but_next with a flag `whole`: the handshake inside a peer_rep
     (true) or only its hs_rep (false: a handshake whose peer's other fields are not a peer_rep, e.g. law config_any's
     stack peer q); hs_randomize with a flag `raw` (any memory of the handshake: data_at_). *)
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
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require WgNoise.contracts.x_cookie_mac.
Require WgNoise.harness.x_handshake.code WgNoise.harness.x_cookie_mac.code WgNoise.harness.x_consume_initiation_any.code
        WgNoise.harness.x_consume_response_any.code WgNoise.harness.x_keypairs.code
        WgNoise.harness.x_handshake_receive.code.
Local Open Scope logic.

Module HC := WgNoise.harness.x_cookie_mac.code.
Module HI := WgNoise.harness.x_consume_initiation_any.code.
Module HKP := WgNoise.harness.x_keypairs.code.
Module HH4 := WgNoise.harness.x_handshake.code.
Module HR4 := WgNoise.harness.x_consume_response_any.code.

Definition t_prsnap := Tstruct HC._pr_snap noattr.
Definition t_devsnap := Tstruct HC._dev_snap noattr.
Definition t_shimsnap := Tstruct HC._shim_snap noattr.
Definition t_kent := Tstruct HC._kent noattr.
Definition t_hnode4 := Tstruct HC._hnode noattr.
Definition t_skbsnap := Tstruct HC._skb_snap noattr.
Definition t_rcounter := Tstruct I._noise_replay_counter noattr.

(* ------------------------------------------------------------------------------------------------ *)
(* values of the structs (at CKS) *)
(* ------------------------------------------------------------------------------------------------ *)

Section CKSvals4.
#[local] Existing Instance CKS.

(* pr_snap: the rest of the peer P *)
Definition prsnap_val (P: peer) : reptype t_prsnap :=
  (p_device P, (Val.of_bool (p_dead P), (p_cur P, (p_prev P, (p_next P, (Vlong (p_lsh P),
   (cksnap_val (p_cookie P), (Vlong (p_id P), p_pknext P)))))))).

(* dev_snap: the device D and its public-key table's first peer h *)
Definition devsnap_val (D: device) (h: val) : reptype t_devsnap :=
  (d_dev D, (bytes (id_pub (d_id D)), (bytes (id_priv (d_id D)), (Val.of_bool (id_has (d_id D)),
   (bytes (cc_secret (d_cc D)), (Vlong (cc_birth (d_cc D)), (bytes (cc_ekey (d_cc D)), (bytes (cc_mkey (d_cc D)),
   (cc_dev (d_cc D), (d_ptab D, (d_itab D, h))))))))))).

(* shim_snap: the counters of S and the warnings w *)
Definition shimsnap_val (S: shim) (w: list int64) : reptype t_shimsnap :=
  (Vlong (s_allocs S), (Vlong (s_fails S), (Vlong (s_frees S), (Vlong (s_released S), map Vlong w)))).

(* skb_snap *)
Definition skbsnap_val (s: skb) : reptype t_skbsnap :=
  (sk_data s, (Vint (sk_len s), (Vint (Int.repr (sk_proto s)), (bytes (sk_ip4 s), (bytes (sk_ip6 s),
   bytes (sk_port s)))))).

(* a node of the harness's peer list (struct hnode): its address, its peer, its snapshots (any values) *)
Record hnode4 := mkHN4 { hn_addr: val; hn_p: val; hn_snap: reptype t_hsnap; hn_refs: val;
                         hn_rest: reptype t_prsnap }.

#[export] Instance hnode4_inh : Inhabitant hnode4 :=
  mkHN4 nullval nullval (default_val t_hsnap) Vundef (default_val t_prsnap).

(* the snapshot fields peer0 .. id0 of a kent: undefined (None) or the snapshot s *)
Definition kent_snap_rep (k: val) (s: option ksnap) : mpred :=
  match s with
  | None =>
      field_at_ Ews t_kent [StructField HC._peer0] k * field_at_ Ews t_kent [StructField HC._next0] k *
      field_at_ Ews t_kent [StructField HC._type0] k * field_at_ Ews t_kent [StructField HC._index0] k *
      field_at_ Ews t_kent [StructField HC._hashed0] k * field_at_ Ews t_kent [StructField HC._skey0] k *
      field_at_ Ews t_kent [StructField HC._rkey0] k * field_at_ Ews t_kent [StructField HC._sbirth0] k *
      field_at_ Ews t_kent [StructField HC._rbirth0] k * field_at_ Ews t_kent [StructField HC._svalid0] k *
      field_at_ Ews t_kent [StructField HC._rvalid0] k * field_at_ Ews t_kent [StructField HC._scnt0] k *
      field_at_ Ews t_kent [StructField HC._rcnt0] k * field_at_ Ews t_kent [StructField HC._bt0] k *
      field_at_ Ews t_kent [StructField HC._remote_index0] k *
      field_at_ Ews t_kent [StructField HC._initiator0] k *
      field_at_ Ews t_kent [StructField HC._refs0] k * field_at_ Ews t_kent [StructField HC._id0] k
  | Some s =>
      let E := ks_E s in let K := ks_K s in
      field_at Ews t_kent [StructField HC._peer0] (e_peer E) k *
      field_at Ews t_kent [StructField HC._next0] (ks_next s) k *
      field_at Ews t_kent [StructField HC._type0] (Vint (e_type E)) k *
      field_at Ews t_kent [StructField HC._index0] (Vint (e_index E)) k *
      field_at Ews t_kent [StructField HC._hashed0] (Val.of_bool (ks_hashed s)) k *
      field_at Ews t_kent [StructField HC._skey0] (bytes (sk_key (kp_send K))) k *
      field_at Ews t_kent [StructField HC._rkey0] (bytes (sk_key (kp_recv K))) k *
      field_at Ews t_kent [StructField HC._sbirth0] (Vlong (sk_birth (kp_send K))) k *
      field_at Ews t_kent [StructField HC._rbirth0] (Vlong (sk_birth (kp_recv K))) k *
      field_at Ews t_kent [StructField HC._svalid0] (Val.of_bool (sk_valid (kp_send K))) k *
      field_at Ews t_kent [StructField HC._rvalid0] (Val.of_bool (sk_valid (kp_recv K))) k *
      field_at Ews t_kent [StructField HC._scnt0] (Vlong (kp_scounter K)) k *
      field_at Ews t_kent [StructField HC._rcnt0] (Vlong (kp_rcounter K)) k *
      field_at Ews t_kent [StructField HC._bt0] (map Vlong (kp_backtrack K)) k *
      field_at Ews t_kent [StructField HC._remote_index0] (Vint (kp_rindex K)) k *
      field_at Ews t_kent [StructField HC._initiator0] (Val.of_bool (kp_init K)) k *
      field_at Ews t_kent [StructField HC._refs0] (Vint (kp_refs K)) k *
      field_at Ews t_kent [StructField HC._id0] (Vlong (kp_id K)) k
  end.

(* the padding of struct kent (after rkey0, after rvalid0, after initiator0, after refs0) *)
Definition kent_pads (k: val) : mpred :=
  spacer Ews 1289 1296 k * spacer Ews 1314 1320 k * spacer Ews 2365 2368 k * spacer Ews 2372 2376 k.

End CKSvals4.

(* the keypair of a kent at k WITHOUT its entry (in the index table's pool) and without a kzalloc token:
   keypair_rep (prot_repr3.v) but the token *)
Section NoiseCS4.
#[local] Existing Instance Noise.CS.
Definition kp_body_rep (k: val) (K: keypair) : mpred :=
  !! (field_compatible t_kp [] k /\ kp_ok K) &&
  (field_at Ews t_kp [StructField I._sending] (symkey_val (kp_send K)) k *
   field_at Ews t_kp [StructField I._sending_counter] (Vlong (kp_scounter K)) k *
   field_at Ews t_kp [StructField I._receiving] (symkey_val (kp_recv K)) k *
   (EX lk: val, field_at Ews t_kp [StructField I._receiving_counter]
                   (Vlong (kp_rcounter K), (lk, map Vlong (kp_backtrack K))) k) *
   field_at Ews t_kp [StructField I._remote_index] (Vint (kp_rindex K)) k *
   field_at Ews t_kp [StructField I._i_am_the_initiator] (Val.of_bool (kp_init K)) k *
   field_at Ews t_kp [StructField I._refcount] (Vint (kp_refs K)) k *
   (EX r: val, field_at Ews t_kp [StructField I._rcu] r k) *
   field_at Ews t_kp [StructField I._internal_id] (Vlong (kp_id K)) k *
   spacer Ews 1181 1184 k).

(* the handshake of p: inside the whole peer_rep (whole), or its hs_rep with only the peer's first field (any
   value: so that p is a valid pointer) *)
Definition hs_mem (whole: bool) (sh: share) (p: val) (P: peer) : mpred :=
  if whole then peer_rep sh p P
  else hs_rep sh (hs_addr p) (p_hs P) * field_at_ sh t_peer [StructField I._device] p.
End NoiseCS4.

(* ------------------------------------------------------------------------------------------------ *)
(* the lists (malloc tokens at the world's compspecs CSw)                                           *)
(* ------------------------------------------------------------------------------------------------ *)

Section Lists.
Variable CSw: compspecs.

(* one kent: token, keypair body, snapshot fields, list link, padding *)
Definition kent_cell (e: kent4) (nx: val) : mpred :=
  !! (@field_compatible CKS t_kent [] (ke_addr e)) &&
  (@malloc_token CSw Ews t_kent (ke_addr e) * kp_body_rep (ke_addr e) (ke_K e) *
   kent_snap_rep (ke_addr e) (ke_snap e) * @field_at CKS Ews t_kent [StructField HC._next] nx (ke_addr e) *
   kent_pads (ke_addr e)).

Fixpoint kents_rep (l: val) (KE: list kent4) : mpred :=
  match KE with
  | [] => !! (l = nullval) && emp
  | e :: KE' => !! (l = ke_addr e) && EX nx: val, kent_cell e nx * kents_rep nx KE'
  end.

(* the harness's peer list: node (token, struct hnode at CKS) and the peer's token; the peers' memory is the
   protocol's peers_rep, in the same order (hnodes_peers4) *)
Fixpoint hnodes_rep4 (l: val) (NS: list hnode4) : mpred :=
  match NS with
  | [] => !! (l = nullval) && emp
  | N :: NS' =>
      !! (l = hn_addr N) &&
      EX nx: val,
        @malloc_token CSw Ews t_hnode4 l *
        @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) l *
        @malloc_token CSw Ews t_peer (hn_p N) *
        hnodes_rep4 nx NS'
  end.
(* objects a caller LENDS to a comparison function (given back unchanged), whose addresses are then valid
   pointers: peers, a device, an index table, kents, keypairs (keypair_rep), byte buffers, memory blocks *)
Inductive vobj :=
| VPeer (sh: share) (p: val) (P: peer)
| VPeers (PS: list (val * share * peer))
| VDev (sh: share) (wg: val) (D: device)
| VItab (sh: share) (tab: val) (T: tstate)
| VKents (l: val) (KE: list kent4)
| VKeypairs (KS: list (val * keypair))
| VBytes (sh: share) (bs: list byte) (a: val)
| VBlock (sh: share) (n: Z) (a: val)
| VTok (sh: share) (ty: type) (a: val).   (* v4.1: a malloc token of an EMPTY object (malloc(0)) *)

Definition vobj_rep (o: vobj) : mpred :=
  match o with
  | VPeer sh p P => peer_rep sh p P
  | VPeers PS => peers_rep PS
  | VDev sh wg D => device_rep sh wg D
  | VItab sh tab T => itable sh tab T
  | VKents l KE => kents_rep l KE
  | VKeypairs KS => keypairs_rep CSw KS
  | VBytes sh bs a => bytes_at sh bs a
  | VBlock sh n a => memory_block sh n a
  | VTok sh ty a => @malloc_token CSw sh ty a
  end.

Definition vobjs (VO: list vobj) : mpred := iter_sepcon vobj_rep VO.
End Lists.

(* the addresses that are valid pointers in a lent object *)
Definition vobj_addrs (o: vobj) : list val :=
  match o with
  | VPeer _ p _ => [p]
  | VPeers PS => map peer_addr4 PS
  | VDev _ wg _ => [wg; id_addr wg; cc_addr wg]
  | VItab _ tab T => tab :: saddrs (t_D T)
  | VKents _ _ => []      (* v4.1: a kent's / keypair's address is its ENTRY, owned by the index table's pool *)
  | VKeypairs _ => []     (*       (lend the table: VItab), not by kents_rep / keypairs_rep *)
  | VBytes _ _ a => [a]
  | VBlock _ _ a => [a]
  | VTok _ _ a => [a]
  end.
Definition vobjs_addrs (VO: list vobj) : list val := concat (map vobj_addrs VO).

(* readable shares, non-empty buffers and blocks *)
Definition vobj_ok (o: vobj) : Prop :=
  match o with
  | VPeer sh _ _ | VDev sh _ _ | VItab sh _ _ => readable_share sh
  | VPeers PS => Forall (fun x => match x with (_, sh, _) => readable_share sh end) PS
  | VKents _ _ | VKeypairs _ => True
  | VBytes sh bs _ => readable_share sh /\ 0 < Zlength bs
  | VBlock sh n _ => readable_share sh /\ 0 < n
  | VTok _ ty _ => forall cs: compspecs, @sizeof cs ty <= 0   (* malloc_token_valid_pointer *)
  end.

Definition hnodes_peers4 (NS: list hnode4) (PS: list (val * share * peer)) : Prop :=
  map hn_p NS = map peer_addr4 PS.

(* hnodes_snap: each node's snapshots of its peer *)
Definition hn_snapshot4 (T: tstate) (N: hnode4) (x: val * share * peer) : hnode4 :=
  match x with (p, _, P) =>
    mkHN4 (hn_addr N) (hn_p N) (hsnap_val (hs_snap_cur T p P)) (Vint (p_refs P)) (prsnap_val P)
  end.
Definition hnodes_snapped4 (T: tstate) (NS: list hnode4) (PS: list (val * share * peer)) : list hnode4 :=
  map (fun '(N, x) => hn_snapshot4 T N x) (combine NS PS).

(* hnodes_same_except(l, except): the nodes hold the handshake snapshots sns, counts rs and rests prs *)
Fixpoint hnodes_same4 (T: tstate) (except: val) (sns: list hsnap) (rs: list int) (prs: list peer)
  (PS: list (val * share * peer)) : bool :=
  match sns, rs, prs, PS with
  | sn :: sns', r :: rs', P0 :: prs', (p, _, P) :: PS' =>
      (if eq_dec p except then true
       else snap_eqb sn (hs_snap_cur T p P) && Int.eq r (p_refs P) && pr_eqb P0 P) &&
      hnodes_same4 T except sns' rs' prs' PS'
  | _, _, _, _ => true
  end.

(* the pointers hnodes_same_except compares are NULL or valid (peers of the list, pool entries, lent objects) *)
Fixpoint hn4_cmp_ok (own: list val) (T: tstate) (sns: list hsnap) (prs: list peer)
  (PS: list (val * share * peer)) : Prop :=
  match sns, prs, PS with
  | sn :: sns', P0 :: prs', (p, _, P) :: PS' =>
      (In (hs_addr p) (saddrs (t_D T)) /\
       Forall (vp_ok own) (hs_ptrs sn (hs_snap_cur T p P) ++ pr_ptrs P0 P)) /\
      hn4_cmp_ok own T sns' prs' PS'
  | _, _, _ => True
  end.

(* kents_add's owners: those of the peer list `peers` (when not NULL), else p (when not NULL), else none *)
Definition kents_owners_ok (peers p: val) (NS: list hnode4) (PS: list (val * share * peer)) : Prop :=
  if eq_dec peers nullval then NS = [] /\ map peer_addr4 PS = (if eq_dec p nullval then [] else [p])
  else NS <> [] /\ hnodes_peers4 NS PS /\ p = nullval.

Definition kents_head (KD: list kdraw) : val := match KD with [] => nullval | d :: _ => kd_addr d end.

Section Specs.
Variable x25519: list byte -> list byte -> list byte.
Variable CSw: compspecs.
#[local] Existing Instance HCS.

(* ------------------------------------------------------------------------------------------------ *)
(* v4 versions of hc_specs3.v's specifications that carry the shim's state or are too narrow          *)
(* ------------------------------------------------------------------------------------------------ *)

(* setup_device (hc_specs3's setup_device_spec with the warnings exact) *)
Definition setup_device4_spec :=
  DECLARE HH4._setup_device
  WITH gv: globals, S: shim, w: list int64, sh: share, wg: val, itab: val, ptab: val, shr: share, r: val,
       RAW: list byte
  PRE [ tptr t_dev, tptr t_itab, tptr t_ptab, tptr tuchar ]
    PROP (writable_share sh; readable_share shr; Zlength RAW = 32)
    PARAMS (wg; itab; ptab; r) GLOBALS (gv)
    SEP (@data_at_ Noise.CS sh t_dev wg; @data_at_ Noise.CS sh t_itab itab; @data_at_ Noise.CS sh t_ptab ptab;
         hbytes shr RAW r; shim_state4 gv S w; wg_consts gv)
  POST [ tvoid ] EX sec: list byte,
    PROP (Zlength sec = 32) RETURN ()
    SEP (device_rep sh wg (setup_dev x25519 wg itab ptab RAW sec (s_boot S));
         itable sh itab (mkT [] []); ptable sh ptab nullval;
         hbytes shr RAW r; shim_state4 gv (shim_draw S sec) w; wg_consts gv).

(* draw_real_clock() *)
Definition draw_real_clock4_spec :=
  DECLARE HH4._draw_real_clock
  WITH gv: globals, S: shim, w: list int64
  PRE [ ] PROP () PARAMS () GLOBALS (gv) SEP (shim_state4 gv S w)
  POST [ tvoid ] EX sec: int64, EX ns: Z,
    PROP (0 <= ns < 1000000000) RETURN ()
    SEP (shim_state4 gv (shim_set_real S sec (Int64.repr ns)) w).

(* hs_take(s, &p->handshake): p's handshake entry from the pool of T *)
Definition hs_take4_spec :=
  DECLARE HH4._hs_take
  WITH shs: share, s: val, shp: share, p: val, P: peer, whole: bool, sht: share, tab: val, T: tstate
  PRE [ tptr t_hsnap, tptr t_hs ]
    PROP (writable_share shs; readable_share shp; readable_share sht; In (hs_addr p) (saddrs (t_D T));
          e_peer (t_entry_d T (hs_addr p)) <> Vundef; hs_sid (p_hs P) <> Vundef)
    PARAMS (s; hs_addr p)
    SEP (data_at_ shs t_hsnap s; hs_mem whole shp p P; itable sht tab T)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at shs t_hsnap (hsnap_val (hs_snap_cur T p P)) s; hs_mem whole shp p P; itable sht tab T).

(* the addresses whose memory hs_same's own SEP holds *)
Definition hs_own (p: val) (T: tstate) (VO: list vobj) : list val :=
  p :: saddrs (t_D T) ++ vobjs_addrs VO.

Definition hs_same4_spec :=
  DECLARE HH4._hs_same
  WITH shs: share, s: val, sn: hsnap, shp: share, p: val, P: peer, whole: bool, sht: share, tab: val,
       T: tstate, VO: list vobj
  PRE [ tptr t_hsnap, tptr t_hs ]
    PROP (Forall vobj_ok VO; readable_share shs; readable_share shp; readable_share sht; In (hs_addr p) (saddrs (t_D T));
          Forall (vp_ok (hs_own p T VO)) (hs_ptrs sn (hs_snap_cur T p P)))
    PARAMS (s; hs_addr p)
    SEP (data_at shs t_hsnap (hsnap_val sn) s; hs_mem whole shp p P; itable sht tab T; vobjs CSw VO)
  POST [ tint ]
    PROP ()
    RETURN (Vint (if snap_eqb sn (hs_snap_cur T p P) then Int.one else Int.zero))
    SEP (data_at shs t_hsnap (hsnap_val sn) s; hs_mem whole shp p P; itable sht tab T; vobjs CSw VO).

(* hs_zeroed_from / hs_same_but_next do not compare the entries' links *)
Definition hs_zeroed_from4_spec :=
  DECLARE HH4._hs_zeroed_from
  WITH shs: share, s: val, sn: hsnap, shp: share, p: val, P: peer, whole: bool, sht: share, tab: val,
       T: tstate, VO: list vobj
  PRE [ tptr t_hsnap, tptr t_hs ]
    PROP (Forall vobj_ok VO; readable_share shs; readable_share shp; readable_share sht; In (hs_addr p) (saddrs (t_D T));
          Forall (vp_ok (hs_own p T VO)) (hs_ptrs_nn sn (hs_snap_cur T p P)))
    PARAMS (s; hs_addr p)
    SEP (data_at shs t_hsnap (hsnap_val sn) s; hs_mem whole shp p P; itable sht tab T; vobjs CSw VO)
  POST [ tint ]
    PROP ()
    RETURN (Vint (if zeroed_from sn (hs_snap_cur T p P) then Int.one else Int.zero))
    SEP (data_at shs t_hsnap (hsnap_val sn) s; hs_mem whole shp p P; itable sht tab T; vobjs CSw VO).

Definition hs_same_but_next4_spec :=
  DECLARE HKP._hs_same_but_next
  WITH shs: share, s: val, sn: hsnap, shp: share, p: val, P: peer, whole: bool, sht: share, tab: val,
       T: tstate, VO: list vobj
  PRE [ tptr t_hsnap, tptr t_hs ]
    PROP (Forall vobj_ok VO; readable_share shs; readable_share shp; readable_share sht; In (hs_addr p) (saddrs (t_D T));
          Forall (vp_ok (hs_own p T VO)) (hs_ptrs_nn sn (hs_snap_cur T p P)))
    PARAMS (s; hs_addr p)
    SEP (data_at shs t_hsnap (hsnap_val sn) s; hs_mem whole shp p P; itable sht tab T; vobjs CSw VO)
  POST [ tint ]
    PROP ()
    RETURN (Vint (if snap_eqb_nn sn (hs_snap_cur T p P) then Int.one else Int.zero))
    SEP (data_at shs t_hsnap (hsnap_val sn) s; hs_mem whole shp p P; itable sht tab T; vobjs CSw VO).

(* hs_randomize(&p->handshake): in a peer_rep (raw = false: the v1 result), or over ANY memory of the handshake
   (raw = true: the fields written are drawn, nothing is claimed) *)
Definition hs_randomize4_spec :=
  DECLARE HR4._hs_randomize
  WITH shp: share, p: val, P: peer, raw: bool
  PRE [ tptr t_hs ]
    PROP (writable_share shp) PARAMS (hs_addr p)
    SEP (if raw then @data_at_ Noise.CS shp t_hs (hs_addr p) else peer_rep shp p P)
  POST [ tvoid ] EX st: int, EX lic: int64, EX eph: list byte, EX reph: list byte, EX hash: list byte,
                 EX ck: list byte, EX ts: list byte, EX ri: int,
    PROP (In st hs_states; 0 <= Int64.unsigned lic < 2 ^ 62; Zlength eph = 32; Zlength reph = 32;
          Zlength hash = 32; Zlength ck = 32; Zlength ts = 12)
    RETURN ()
    SEP (if raw then @data_at_ Noise.CS shp t_hs (hs_addr p)
         else peer_rep shp p (p_set_hs P (hs_randomized (p_hs P) st lic eph reph hash ck ts ri))).

(* ------------------------------------------------------------------------------------------------ *)
(* the rest of a peer (pr_snap at CKS)                                                              *)
(* ------------------------------------------------------------------------------------------------ *)

Definition pr_take4_spec :=
  DECLARE HC._pr_take
  WITH shs: share, s: val, shp: share, p: val, P: peer
  PRE [ tptr t_prsnap, tptr t_peer ]
    PROP (writable_share shs; readable_share shp;
          Forall (fun x => x <> Vundef) [p_device P; p_cur P; p_prev P; p_next P; p_pknext P])
    PARAMS (s; p)
    SEP (@data_at_ CKS shs t_prsnap s; peer_rep shp p P)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (@data_at CKS shs t_prsnap (prsnap_val P) s; peer_rep shp p P).

Definition pr_same_but_cookie4_spec :=
  DECLARE HC._pr_same_but_cookie
  WITH shs: share, s: val, P0: peer, shp: share, p: val, P: peer, VO: list vobj
  PRE [ tptr t_prsnap, tptr t_peer ]
    PROP (Forall vobj_ok VO; readable_share shs; readable_share shp; Forall (vp_ok (p :: vobjs_addrs VO)) (pr_ptrs P0 P))
    PARAMS (s; p)
    SEP (@data_at CKS shs t_prsnap (prsnap_val P0) s; peer_rep shp p P; vobjs CSw VO)
  POST [ tint ]
    PROP () RETURN (Vint (if pr_eqb_nc P0 P then Int.one else Int.zero))
    SEP (@data_at CKS shs t_prsnap (prsnap_val P0) s; peer_rep shp p P; vobjs CSw VO).

Definition pr_same4_spec :=
  DECLARE HC._pr_same
  WITH shs: share, s: val, P0: peer, shp: share, p: val, P: peer, VO: list vobj
  PRE [ tptr t_prsnap, tptr t_peer ]
    PROP (Forall vobj_ok VO; readable_share shs; readable_share shp; Forall (vp_ok (p :: vobjs_addrs VO)) (pr_ptrs P0 P))
    PARAMS (s; p)
    SEP (@data_at CKS shs t_prsnap (prsnap_val P0) s; peer_rep shp p P; vobjs CSw VO)
  POST [ tint ]
    PROP () RETURN (Vint (if pr_eqb P0 P then Int.one else Int.zero))
    SEP (@data_at CKS shs t_prsnap (prsnap_val P0) s; peer_rep shp p P; vobjs CSw VO).

(* peer_randomize_rest(p) *)
Definition peer_randomize_rest4_spec :=
  DECLARE HI._peer_randomize_rest
  WITH shp: share, p: val, P: peer
  PRE [ tptr t_peer ]
    PROP (writable_share shp) PARAMS (p)
    SEP (peer_rep shp p P)
  POST [ tvoid ] EX dead: bool, EX lsh: int64, EX valid: bool, EX birth: int64, EX ck: list byte,
                 EX sent: bool, EX mac1: list byte,
    PROP (0 <= Int64.unsigned birth < 2 ^ 62; Zlength ck = 16; Zlength mac1 = 16)
    RETURN ()
    SEP (peer_rep shp p (p_rest_randomized P dead lsh valid birth ck sent mac1)).

(* draw_peer_refs(): 1 .. INT_MAX - 1 *)
Definition draw_peer_refs4_spec :=
  DECLARE HC._draw_peer_refs
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tuint ] EX r: int,
    PROP (0 < Int.unsigned r < 2147483647) RETURN (Vint r) SEP ().

(* ------------------------------------------------------------------------------------------------ *)
(* the device and the shim                                                                          *)
(* ------------------------------------------------------------------------------------------------ *)

Definition dev_take4_spec :=
  DECLARE HC._dev_take
  WITH shs: share, s: val, shd: share, wg: val, D: device, shp: share, head: val
  PRE [ tptr t_devsnap, tptr t_dev ]
    PROP (writable_share shs; readable_share shd; readable_share shp;
          Forall (fun x => x <> Vundef) [d_dev D; cc_dev (d_cc D); d_ptab D; d_itab D; head])
    PARAMS (s; wg)
    SEP (@data_at_ CKS shs t_devsnap s; device_rep shd wg D; ptable shp (d_ptab D) head)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (@data_at CKS shs t_devsnap (devsnap_val D head) s; device_rep shd wg D; ptable shp (d_ptab D) head).

Definition dev_same4_spec :=
  DECLARE HC._dev_same
  WITH shs: share, s: val, D0: device, h0: val, shd: share, wg: val, D: device, shp: share, head: val,
       VO: list vobj
  PRE [ tptr t_devsnap, tptr t_dev ]
    PROP (Forall vobj_ok VO; readable_share shs; readable_share shd; readable_share shp;
          Forall (vp_ok ([wg; d_ptab D] ++ vobjs_addrs VO)) (dev_ptrs D0 h0 D head))
    PARAMS (s; wg)
    SEP (@data_at CKS shs t_devsnap (devsnap_val D0 h0) s; device_rep shd wg D; ptable shp (d_ptab D) head; vobjs CSw VO)
  POST [ tint ]
    PROP () RETURN (Vint (if dev_eqb D0 h0 D head then Int.one else Int.zero))
    SEP (@data_at CKS shs t_devsnap (devsnap_val D0 h0) s; device_rep shd wg D; ptable shp (d_ptab D) head; vobjs CSw VO).

Definition shim_take4_spec :=
  DECLARE HC._shim_take
  WITH gv: globals, shs: share, s: val, S: shim, w: list int64
  PRE [ tptr t_shimsnap ]
    PROP (writable_share shs) PARAMS (s) GLOBALS (gv)
    SEP (@data_at_ CKS shs t_shimsnap s; shim_state4 gv S w)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (@data_at CKS shs t_shimsnap (shimsnap_val S w) s; shim_state4 gv S w).

Definition shim_same4_spec :=
  DECLARE HC._shim_same
  WITH gv: globals, shs: share, s: val, S0: shim, w0: list int64, S: shim, w: list int64
  PRE [ tptr t_shimsnap ]
    PROP (readable_share shs) PARAMS (s) GLOBALS (gv)
    SEP (@data_at CKS shs t_shimsnap (shimsnap_val S0 w0) s; shim_state4 gv S w)
  POST [ tint ]
    PROP () RETURN (Vint (if shim_eqb S0 w0 S w then Int.one else Int.zero))
    SEP (@data_at CKS shs t_shimsnap (shimsnap_val S0 w0) s; shim_state4 gv S w).

Definition shim_no_warning4_spec :=
  DECLARE HC._shim_no_warning
  WITH gv: globals, shs: share, s: val, S0: shim, w0: list int64, S: shim, w: list int64
  PRE [ tptr t_shimsnap ]
    PROP (readable_share shs) PARAMS (s) GLOBALS (gv)
    SEP (@data_at CKS shs t_shimsnap (shimsnap_val S0 w0) s; shim_state4 gv S w)
  POST [ tint ]
    PROP () RETURN (Vint (if warn_eqb w0 w then Int.one else Int.zero))
    SEP (@data_at CKS shs t_shimsnap (shimsnap_val S0 w0) s; shim_state4 gv S w).

(* ------------------------------------------------------------------------------------------------ *)
(* socket buffers and replay counters                                                               *)
(* ------------------------------------------------------------------------------------------------ *)

Definition skb_take4_spec :=
  DECLARE HC._skb_take
  WITH shs: share, s: val, shk: share, sp: val, sk: skb
  PRE [ tptr t_skbsnap, tptr t_skb ]
    PROP (writable_share shs; readable_share shk; sk_data sk <> Vundef) PARAMS (s; sp)
    SEP (@data_at_ CKS shs t_skbsnap s; skb_rep shk sp sk)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (@data_at CKS shs t_skbsnap (skbsnap_val sk) s; skb_rep shk sp sk).

Definition skb_same4_spec :=
  DECLARE HC._skb_same
  WITH shs: share, s: val, sk0: skb, shk: share, sp: val, sk: skb, VO: list vobj
  PRE [ tptr t_skbsnap, tptr t_skb ]
    PROP (Forall vobj_ok VO; readable_share shs; readable_share shk; skb_ok sk0;
          Forall (vp_ok (vobjs_addrs VO)) [sk_data sk0; sk_data sk])
    PARAMS (s; sp)
    SEP (@data_at CKS shs t_skbsnap (skbsnap_val sk0) s; skb_rep shk sp sk; vobjs CSw VO)
  POST [ tint ]
    PROP () RETURN (Vint (if skb_eqb sk0 sk then Int.one else Int.zero))
    SEP (@data_at CKS shs t_skbsnap (skbsnap_val sk0) s; skb_rep shk sp sk; vobjs CSw VO).

(* replay_counter_fresh(&kp->receiving_counter) *)
Definition replay_counter_fresh4_spec :=
  DECLARE HKP._replay_counter_fresh
  WITH sh: share, c: val, rc: int64, lk: val, bt: list int64
  PRE [ tptr t_rcounter ]
    PROP (readable_share sh; Zlength bt = 128) PARAMS (c)
    SEP (@data_at Noise.CS sh t_rcounter (Vlong rc, (lk, map Vlong bt)) c)
  POST [ tint ]
    PROP () RETURN (Vint (if rc_fresh rc bt then Int.one else Int.zero))
    SEP (@data_at Noise.CS sh t_rcounter (Vlong rc, (lk, map Vlong bt)) c).

(* ------------------------------------------------------------------------------------------------ *)
(* the harness's peer list (struct hnode at CKS)                                                    *)
(* ------------------------------------------------------------------------------------------------ *)

(* hnodes_add(&l, wg, pub, id): NULL if a peer of the list has that public key, or an allocation fails (then
   nothing changes); else a new node and peer at the head of both lists: setup_peer's peer with any preshared key
   or none and draw_peer_refs's count; its handshake entry comes out unhashed (entry_out: add it to the pool) *)
Definition hnodes_add4_spec :=
  DECLARE HI._hnodes_add
  WITH gv: globals, shl: share, lp: val, l0: val, NS: list hnode4, PS: list (val * share * peer),
       shd: share, wg: val, D: device, head: val, shk: share, pk: val, PUB: list byte, id: int64
  PRE [ tptr (tptr t_hnode4), tptr t_dev, tptr tuchar, tulong ]
    PROP (writable_share shl; writable_share shd; readable_share shk; Zlength PUB = 32; hnodes_peers4 NS PS;
          peers_wf PS; is_pointer_or_null head)
    PARAMS (lp; wg; pk; Vlong id) GLOBALS (gv)
    SEP (@data_at CKS shl (tptr t_hnode4) l0 lp; hnodes_rep4 CSw l0 NS; peers_rep PS;
         device_rep shd wg D; ptable shd (d_ptab D) head; hbytes shk PUB pk; mem_mgr gv; wg_consts gv)
  POST [ tptr t_hnode4 ] EX n: val, EX p: val, EX PSK: list byte, EX r: int,
    PROP (pk_find PS PUB <> None -> n = nullval;
          n <> nullval -> Zlength PSK = 32 /\ 0 < Int.unsigned r < 2147483647)
    RETURN (n)
    SEP (if eq_dec n nullval then
           (@data_at CKS shl (tptr t_hnode4) l0 lp * hnodes_rep4 CSw l0 NS * peers_rep PS *
            device_rep shd wg D * ptable shd (d_ptab D) head)
         else
           (@data_at CKS shl (tptr t_hnode4) n lp *
            hnodes_rep4 CSw n (mkHN4 n p (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap) :: NS) *
            peers_rep ((p, Ews, p_set_refs (setup_peer_val x25519 D wg p head PUB PSK id) r) :: PS) *
            entry_out Ews (hs_addr p) (mkEntry p IDX_HANDSHAKE Int.zero) *
            device_rep shd wg D * ptable shd (d_ptab D) p);
         hbytes shk PUB pk; mem_mgr gv; wg_consts gv).

(* hnodes_snap(l): each node's hs_take, refcount, pr_take of its peer *)
Definition hnodes_snap4_spec :=
  DECLARE HI._hnodes_snap
  WITH l: val, NS: list hnode4, PS: list (val * share * peer), sht: share, tab: val, T: tstate
  PRE [ tptr t_hnode4 ]
    PROP (readable_share sht; hnodes_peers4 NS PS; peers_wf PS;
          Forall (fun x => match x with (p, _, P) =>
                    In (hs_addr p) (saddrs (t_D T)) /\ e_peer (t_entry_d T (hs_addr p)) <> Vundef /\
                    hs_sid (p_hs P) <> Vundef /\
                    Forall (fun v => v <> Vundef) [p_device P; p_cur P; p_prev P; p_next P; p_pknext P] end) PS)
    PARAMS (l)
    SEP (hnodes_rep4 CSw l NS; peers_rep PS; itable sht tab T)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (hnodes_rep4 CSw l (hnodes_snapped4 T NS PS); peers_rep PS; itable sht tab T).

(* hnodes_same_except(l, except): the nodes hold the snapshots sns, counts rs and rests prs of the peers PS *)
Definition hnodes_same_except4_spec :=
  DECLARE HI._hnodes_same_except
  WITH l: val, NS: list hnode4, PS: list (val * share * peer), sns: list hsnap, rs: list int, prs: list peer,
       except: val, sht: share, tab: val, T: tstate, VO: list vobj
  PRE [ tptr t_hnode4, tptr t_peer ]
    PROP (Forall vobj_ok VO; readable_share sht; hnodes_peers4 NS PS; peers_wf PS;
          Zlength sns = Zlength NS; Zlength rs = Zlength NS; Zlength prs = Zlength NS;
          map hn_snap NS = map hsnap_val sns; map hn_refs NS = map Vint rs; map hn_rest NS = map prsnap_val prs;
          hn4_cmp_ok (map peer_addr4 PS ++ saddrs (t_D T) ++ vobjs_addrs VO) T sns prs PS;
          except = nullval \/ In except (map peer_addr4 PS))
    PARAMS (l; except)
    SEP (hnodes_rep4 CSw l NS; peers_rep PS; itable sht tab T; vobjs CSw VO)
  POST [ tint ]
    PROP ()
    RETURN (Vint (if hnodes_same4 T except sns rs prs PS then Int.one else Int.zero))
    SEP (hnodes_rep4 CSw l NS; peers_rep PS; itable sht tab T; vobjs CSw VO).

(* hnodes_free(l): every node and every peer freed (the caller hands each peer's memory back as data_at_) *)
Definition hnodes_free4_spec :=
  DECLARE HI._hnodes_free
  WITH gv: globals, l: val, NS: list hnode4
  PRE [ tptr t_hnode4 ]
    PROP () PARAMS (l) GLOBALS (gv)
    SEP (hnodes_rep4 CSw l NS; iter_sepcon (fun N => @data_at_ CSw Ews t_peer (hn_p N)) NS; mem_mgr gv)
  POST [ tvoid ]
    PROP () RETURN () SEP (mem_mgr gv).

(* hnodes_pick(l): any node of a non-empty list *)
Definition hnodes_pick4_spec :=
  DECLARE HC._hnodes_pick
  WITH l: val, NS: list hnode4
  PRE [ tptr t_hnode4 ]
    PROP (NS <> []) PARAMS (l)
    SEP (hnodes_rep4 CSw l NS)
  POST [ tptr t_hnode4 ] EX i: Z,
    PROP (0 <= i < Zlength NS) RETURN (hn_addr (Znth i NS))
    SEP (hnodes_rep4 CSw l NS).

(* ------------------------------------------------------------------------------------------------ *)
(* the kents (struct kent at CKS; the keypairs' entries in the pool of the index table)             *)
(* ------------------------------------------------------------------------------------------------ *)

(* kents_add(t, peers, p, fill): the kents KD (list order), each inserted into the table (kents_T, fresh indices),
   each owned by a peer of PS, each possibly in an empty slot of its owner (fill) *)
Definition kents_add4_spec :=
  DECLARE HC._kents_add
  WITH gv: globals, sht: share, tab: val, T: tstate, peers: val, NS: list hnode4, p: val,
       PS: list (val * share * peer), fl: int, S: shim, w: list int64
  PRE [ tptr t_itab, tptr t_hnode4, tptr t_peer, tint ]
    PROP (writable_share sht; peers_wf PS; kents_owners_ok peers p NS PS;
          Forall (fun x => match x with (_, _, P) =>
                    Forall (vp_ok (saddrs (t_D T))) [p_cur P; p_prev P; p_next P] end) PS)
    PARAMS (tab; peers; p; Vint fl) GLOBALS (gv)
    SEP (itable sht tab T; hnodes_rep4 CSw peers NS; peers_rep PS; shim_state4 gv S w; mem_mgr gv)
  POST [ tptr t_kent ] EX KD: list kdraw,
    PROP (kents_draws_ok PS KD; kents_fresh T KD)
    RETURN (kents_head KD)
    SEP (kents_rep CSw (kents_head KD) (map kd_kent KD); itable sht tab (kents_T T KD);
         hnodes_rep4 CSw peers NS; peers_rep (kents_PS (negb (Int.eq fl Int.zero)) PS KD);
         shim_state4 gv (kents_S S KD) w; mem_mgr gv).

(* kents_snap(l) *)
Definition kents_snap4_spec :=
  DECLARE HC._kents_snap
  WITH l: val, KE: list kent4, sht: share, tab: val, T: tstate
  PRE [ tptr t_kent ]
    PROP (readable_share sht;
          Forall (fun e => In (ke_addr e) (saddrs (t_D T)) /\ e_peer (t_entry_d T (ke_addr e)) <> Vundef) KE)
    PARAMS (l)
    SEP (kents_rep CSw l KE; itable sht tab T)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (kents_rep CSw l (map (kent_snapped T) KE); itable sht tab T).

(* kent_same_but_next(l) of one kent *)
Definition kent_same_but_next4_spec :=
  DECLARE HC._kent_same_but_next
  WITH e: kent4, nx: val, sht: share, tab: val, T: tstate, VO: list vobj
  PRE [ tptr t_kent ]
    PROP (Forall vobj_ok VO; readable_share sht; In (ke_addr e) (saddrs (t_D T)); ke_snap e <> None;
          Forall (vp_ok (saddrs (t_D T) ++ vobjs_addrs VO)) (kent_ptrs_nn T e))
    PARAMS (ke_addr e)
    SEP (kent_cell CSw e nx; itable sht tab T; vobjs CSw VO)
  POST [ tint ]
    PROP () RETURN (Vint (if kent_eqb_cur T e then Int.one else Int.zero))
    SEP (kent_cell CSw e nx; itable sht tab T; vobjs CSw VO).

Definition kents_same4_spec :=
  DECLARE HC._kents_same
  WITH l: val, KE: list kent4, sht: share, tab: val, T: tstate, VO: list vobj
  PRE [ tptr t_kent ]
    PROP (Forall vobj_ok VO; readable_share sht;
          Forall (fun e => In (ke_addr e) (saddrs (t_D T)) /\ ke_snap e <> None /\
                           Forall (vp_ok (saddrs (t_D T) ++ vobjs_addrs VO)) (kent_ptrs T e)) KE)
    PARAMS (l)
    SEP (kents_rep CSw l KE; itable sht tab T; vobjs CSw VO)
  POST [ tint ]
    PROP () RETURN (Vint (if forallb (kent_same T) KE then Int.one else Int.zero))
    SEP (kents_rep CSw l KE; itable sht tab T; vobjs CSw VO).

Definition kents_same_but_next4_spec :=
  DECLARE HKP._kents_same_but_next
  WITH l: val, KE: list kent4, sht: share, tab: val, T: tstate, VO: list vobj
  PRE [ tptr t_kent, tptr t_itab ]
    PROP (Forall vobj_ok VO; readable_share sht;
          Forall (fun e => In (ke_addr e) (saddrs (t_D T)) /\ ke_snap e <> None /\
                           Forall (vp_ok (saddrs (t_D T) ++ vobjs_addrs VO)) (kent_ptrs_nn T e)) KE)
    PARAMS (l; tab)
    SEP (kents_rep CSw l KE; itable sht tab T; vobjs CSw VO)
  POST [ tint ]
    PROP () RETURN (Vint (if forallb (kent_same_bn T) KE then Int.one else Int.zero))
    SEP (kents_rep CSw l KE; itable sht tab T; vobjs CSw VO).

Definition kents_hashed4_spec :=
  DECLARE HKP._kents_hashed
  WITH l: val, KE: list kent4, sht: share, tab: val, T: tstate
  PRE [ tptr t_kent ]
    PROP (readable_share sht; Forall (fun e => In (ke_addr e) (saddrs (t_D T))) KE)
    PARAMS (l)
    SEP (kents_rep CSw l KE; itable sht tab T)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (kents_hashed_n T KE)))
    SEP (kents_rep CSw l KE; itable sht tab T).

(* kents_free(l): every kent freed (the caller hands each kent's entry back from the pool as data_at_) *)
Definition kents_free4_spec :=
  DECLARE HC._kents_free
  WITH gv: globals, l: val, KE: list kent4
  PRE [ tptr t_kent ]
    PROP () PARAMS (l) GLOBALS (gv)
    SEP (kents_rep CSw l KE; iter_sepcon (fun e => @data_at_ Noise.CS Ews t_entry_s (ke_addr e)) KE; mem_mgr gv)
  POST [ tvoid ]
    PROP () RETURN () SEP (mem_mgr gv).

(* le32_load(p) (law handshake_receive) *)
Definition le32_load4_spec :=
  DECLARE WgNoise.harness.x_handshake_receive.code._le32_load
  WITH sh: share, p: val, bs: list byte
  PRE [ tptr tuchar ]
    PROP (readable_share sh; Zlength bs = 4) PARAMS (p)
    SEP (hbytes sh bs p)
  POST [ tuint ]
    PROP () RETURN (Vint (le32_val bs)) SEP (hbytes sh bs p).

End Specs.
