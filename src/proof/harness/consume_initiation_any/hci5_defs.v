(* law consume_initiation_any: main's context and the
   states between its phases.

   Conventions (all phases):
   - main runs in the world compspecs W := W_consume_initiation_any (Delta hci5_Delta).  The SEP items are kept in
     the compspecs of the specifications that consume them: protocol objects through prot_repr3's predicates
     (device_rep, peers_rep, itable, ptable, init_rep: Noise.CS inside), the shim with EXACT warnings
     (shim_state4 gv S w, prot_repr4.v), harness structs m_identity / m_consumed_initiation / m_initiation as
     `@data_at(_) HCS`, the structs dev_snap / shim_snap as `@data_at(_) CKS` (hc4_specs.v), the local
     `peers` (struct hnode * ) as `@data_at(_) W` (hnodes_add4 wants it at CKS: convert), the node list as
     `hnodes_rep4 W`, the kents as `kents_rep W`, byte buffers as hbytes / hout (HCS).
   - main's body = S; return 0 with S = the 39 statements of hci5_stmts (hci5_cut.v): P1 0..8, P2 9..10, P3 11,
     PK 12, P4 13..14, P5 15..19, P6 20..28, P7 29..30, P8 31..38.
   - The states: hci5_S0 (prologue), hci5_SA (after P1, P2 and P3: the same invariant, T any table of the
     invariant), hci5_SK (after PK: the kents), hci5_S4 .. hci5_S7; P8 ends in FF (it returns); P4 may return.
   - The peers: PS (the protocol's list, in public-key-chain order = the node list's order, both pushed at the
     head), NS (the harness's nodes), KE (the kents).  The index table's pool is the kents' entries then the
     peers' handshake entries (hci5_T_ok), the peers' keypair slots are NULL or kents (hci5_slots_ok).  Every peer
     satisfies hci5_pok (device, static identity, lengths, the precomputed static-static of B's identity,
     1 .. INT_MAX - 1 references, last consumption below 2^62, its public-key link a pointer or NULL).
   - FR: an opaque frame (TT * has_ext), carried along. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_cut.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_ts.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_model.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_globals.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_spec.
Require WgNoise.contracts.x_consume_initiation_any.
Require WgNoise.harness.x_consume_initiation_any.code.
Local Open Scope logic.

Module HC := WgNoise.harness.x_consume_initiation_any.code.

Notation W := W_consume_initiation_any.

(* ---------------------------------------------------------------------- *)
(* The hypotheses of the phase lemmas                                      *)
(* ---------------------------------------------------------------------- *)

(* the statement of prot_rep_lemmas3 (a hypothesis here, discharged by the assembly) *)
Section Rep.
#[local] Existing Instance Noise.CS.
Definition hci5_rep : Prop :=
  (forall sh m M, init_rep sh m M |-- bytes_at sh (init_bytes M) m) /\
  (forall sh m M, field_compatible t_init [] m -> im_ok M ->
     bytes_at sh (init_bytes M) m |-- init_rep sh m M) /\
  (forall sh m M, resp_rep sh m M |-- bytes_at sh (resp_bytes M) m) /\
  (forall sh m M, field_compatible t_resp [] m -> rm_ok M ->
     bytes_at sh (resp_bytes M) m |-- resp_rep sh m M) /\
  (forall sht tab T a sh E, writable_share sh ->
     itable sht tab T * entry_out sh a E |-- itable sht tab (t_add T a sh E)) /\
  (forall sht tab T a sh E, sfind (t_D T) a = Some (sh, E) -> ~ In a (t_L T) ->
     itable sht tab T |-- itable sht tab (t_free T a) * entry_out sh a E) /\
  (forall sh p P E n h, peer_rep sh p P * entry_at sh (hs_addr p) E n h |-- @data_at_ Noise.CS sh t_peer p) /\
  (forall CSw k K E n h, keypair_rep CSw k K * entry_at Ews k E n h |--
     @malloc_token CSw Ews (tarray tuchar SIZEOF_KEYPAIR) k *
     @data_at_ Noise.CS Ews (tarray tuchar SIZEOF_KEYPAIR) k).
End Rep.

Section Defs.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Definition hci5_hyps : Prop :=
  x25519_props x25519 /\ aead_props aead_enc aead_dec /\ xaead_props xaead_enc xaead_dec /\ hci5_rep.

(* ---------------------------------------------------------------------- *)
(* main's context                                                          *)
(* ---------------------------------------------------------------------- *)

Definition hci5_Gprog : funspecs := hci5_imports x25519 aead_enc aead_dec W ++ hci5_G.
Definition hci5_Delta : tycontext := func_tycontext HC.f_main hci5_V hci5_Gprog [].

End Defs.

Definition hci5_R (gv: globals) : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (hci5_post gv)) (@stackframe_of W HC.f_main).

(* ---------------------------------------------------------------------- *)
(* The locals and the globals                                              *)
(* ---------------------------------------------------------------------- *)

(* the addresses of main's 19 local variables (ss1: A's precomputed value in the mode block, ss2: the model's
   in the target block; ds / ss: the device / shim snapshots) *)
Record hci5_loc := mkLoc5 {
  l_wb: val; l_itb: val; l_ptb: val; l_ia: val; l_ib: val; l_rawa: val; l_rawb: val; l_pub: val;
  l_ts: val; l_img: val; l_imga: val; l_peers: val; l_ds: val; l_ss: val; l_ci: val; l_mi: val; l_eraw: val;
  l_ss1: val; l_ss2: val }.

Definition t_dsnap := Tstruct HC._dev_snap noattr.
Definition t_ssnap := Tstruct HC._shim_snap noattr.

Definition hci5_lvars (gv: globals) (L: hci5_loc) : list localdef :=
  [lvar HC._wb t_dev (l_wb L); lvar HC._itb t_itab (l_itb L); lvar HC._ptb t_ptab (l_ptb L);
   lvar HC._ia t_mident (l_ia L); lvar HC._ib t_mident (l_ib L);
   lvar HC._raw_a (tarray tuchar 32) (l_rawa L); lvar HC._raw_b (tarray tuchar 32) (l_rawb L);
   lvar HC._pub (tarray tuchar 32) (l_pub L); lvar HC._ts (tarray tuchar 12) (l_ts L);
   lvar HC._img (tarray tuchar 148) (l_img L); lvar HC._img_after (tarray tuchar 148) (l_imga L);
   lvar HC._peers (tptr t_hnode4) (l_peers L);
   lvar HC._ds t_dsnap (l_ds L); lvar HC._ss t_ssnap (l_ss L);
   lvar HC._ci t_mcinit (l_ci L); lvar HC._mi t_minit (l_mi L);
   lvar HC._eraw (tarray tuchar 32) (l_eraw L); lvar HC._ss__1 (tarray tuchar 32) (l_ss1 L);
   lvar HC._ss__2 (tarray tuchar 32) (l_ss2 L);
   gvars gv].

(* the globals of a state: allocator, shim (exact warnings), noise.c's globals (no keypair is ever created:
   keypair_counter stays 0), the read-only tables, the harness's constants (hci5_globals.v), the frame *)
Definition hci5_globs (gv: globals) (S: shim) (w: list int64) (FR: mpred) : list mpred :=
  [mem_mgr gv; shim_state4 gv S w; noise_globals gv Int64.zero; wg_consts gv; hci5_consts gv; FR].

(* the snapshot locals ds, ss before the snapshots *)
Definition hci5_snaps0 (L: hci5_loc) : list mpred :=
  [@data_at_ CKS Tsh t_devsnap (l_ds L); @data_at_ CKS Tsh t_shimsnap (l_ss L)].

(* the scratch locals, any contents: pub, ts, img_after, ci, mi, eraw, ss1, ss2 (img, ds, ss are listed apart) *)
Definition hci5_scr (L: hci5_loc) : list mpred :=
  [hout Tsh 32 (l_pub L); hout Tsh 12 (l_ts L); hout Tsh 148 (l_imga L);
   @data_at_ HCS Tsh t_mcinit (l_ci L); @data_at_ HCS Tsh t_minit (l_mi L);
   hout Tsh 32 (l_eraw L); hout Tsh 32 (l_ss1 L); hout Tsh 32 (l_ss2 L)].

(* a malloc'd message (the token at the world, the contents at Noise.CS) *)
Definition hci5_tok (t: type) (p: val) : mpred := @malloc_token W Ews t p.

(* ---------------------------------------------------------------------- *)
(* The run: the setup's draws, and the objects they determine              *)
(* ---------------------------------------------------------------------- *)

Record hci5_run := mkRun5 {
  r_rawa: list byte;    (* raw_a *)
  r_rawb: list byte;    (* raw_b *)
  r_secb: list byte;    (* the cookie secret drawn by setup_device(&wb ..) *)
  r_boot0: int64 }.     (* the first boot clock *)

Definition hci5_run_ok (R: hci5_run) : Prop :=
  Zlength (r_rawa R) = 32 /\ Zlength (r_rawb R) = 32 /\ Zlength (r_secb R) = 32 /\
  0 <= Int64.unsigned (r_boot0 R) < 2 ^ 62.

(* the head of the node list, of the kent list *)
Definition hci5_head (NS: list hnode4) : val := match NS with [] => nullval | N :: _ => hn_addr N end.
Definition hci5_khead (KE: list kent4) : val := match KE with [] => nullval | e :: _ => ke_addr e end.

(* the node of the peer at a (the first one; the peers' addresses are distinct), or NULL *)
Fixpoint hci5_nfind (NS: list hnode4) (a: val) : val :=
  match NS with
  | [] => nullval
  | N :: NS' => if eq_dec (hn_p N) a then hn_addr N else hci5_nfind NS' a
  end.

(* the index table's pool: the kents' entries, then the peers' handshake entries (shares Ews), each peer's entry
   with peer = that peer, each kent's entry with a peer of PS (its owner) *)
Definition hci5_T_ok (PS: list (val * share * peer)) (KE: list kent4) (T: tstate) : Prop :=
  saddrs (t_D T) = map ke_addr KE ++ map (fun x => hs_addr (peer_addr4 x)) PS /\
  Forall (fun d => match d with (_, sh, _) => sh = Ews end) (t_D T) /\
  Forall (fun x => e_peer (t_entry_d T (hs_addr (peer_addr4 x))) = peer_addr4 x) PS /\
  Forall (fun e => In (e_peer (t_entry_d T (ke_addr e))) (map peer_addr4 PS)) KE.

(* the peers' keypair slots: NULL or kents *)
Definition hci5_slots_ok (KE: list kent4) (PS: list (val * share * peer)) : Prop :=
  Forall (fun x => match x with (_, _, P) =>
            Forall (fun k => k = nullval \/ In k (map ke_addr KE)) [p_cur P; p_prev P; p_next P] end) PS.

Section Run.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* the harness's model identities *)
Definition hci5_IA (R: hci5_run) : mident := mident_of x25519 (r_rawa R).
Definition hci5_IB (R: hci5_run) : mident := mident_of x25519 (r_rawb R).

(* B after setup_device *)
Definition hci5_DB (R: hci5_run) (L: hci5_loc) : device :=
  setup_dev x25519 (l_wb L) (l_itb L) (l_ptb L) (r_rawb R) (r_secb R) (r_boot0 R).

(* every peer of B *)
Definition hci5_pok (R: hci5_run) (L: hci5_loc) (x: val * share * peer) : Prop :=
  match x with (a, sh, P) =>
    sh = Ews /\ p_device P = l_wb L /\ hs_sid (p_hs P) = id_addr (l_wb L) /\ hs_ok (p_hs P) /\
    hs_ss (p_hs P) = precomputed x25519 (d_id (hci5_DB R L)) (hs_rstatic (p_hs P)) /\
    0 < Int.unsigned (p_refs P) < 2147483647 /\
    0 <= Int64.unsigned (hs_lic (p_hs P)) < 2 ^ 62 /\
    is_pointer_or_null (p_pknext P)
  end.

(* the lists: peers PS (chain from head), nodes NS (same peers, same order), kents KE, the table T,
   na = a node of the list (A's) or NULL *)
Definition hci5_inv (R: hci5_run) (L: hci5_loc) (NS: list hnode4) (PS: list (val * share * peer))
  (KE: list kent4) (T: tstate) (head na: val) : Prop :=
  Forall (hci5_pok R L) PS /\ peers_wf PS /\ pk_chain head PS /\ hnodes_peers4 NS PS /\
  (na = nullval \/ In na (map hn_addr NS)) /\ hci5_T_ok PS KE T /\ hci5_slots_ok KE PS.

(* the objects that live from the setup to the end: B's device and tables, the identities, the raw keys, the
   local `peers`, the node list (NS gives its order and head, NS' its contents: NS before the snapshots) *)
Definition hci5_world (R: hci5_run) (L: hci5_loc) (NS NS': list hnode4) (T: tstate) (head: val) : list mpred :=
  [device_rep Tsh (l_wb L) (hci5_DB R L); itable Tsh (l_itb L) T; ptable Tsh (l_ptb L) head;
   @data_at HCS Tsh t_mident (mident_val (hci5_IA R)) (l_ia L);
   @data_at HCS Tsh t_mident (mident_val (hci5_IB R)) (l_ib L);
   hbytes Tsh (r_rawa R) (l_rawa L); hbytes Tsh (r_rawb R) (l_rawb L);
   @data_at W Tsh (tptr t_hnode4) (hci5_head NS) (l_peers L);
   hnodes_rep4 W (hci5_head NS) NS'].

(* the harness's model's target node *)
Definition hci5_tnode (NS: list hnode4) (tg: option (val * peer * list byte * list byte * list byte)) : val :=
  match tg with Some (a, _, _, _, _) => hci5_nfind NS a | None => nullval end.

(* ci after the target block: on acceptance its state (ck2, h2) and timestamp t (key, spub: any) *)
Definition hci5_ci_rep (tg: option (val * peer * list byte * list byte * list byte)) (ci: val) : mpred :=
  match tg with
  | Some (_, _, t, ck2, h2) =>
      EX key: list val, EX spub: list val,
        !! (Zlength key = 32 /\ Zlength spub = 32) &&
        @data_at HCS Tsh t_mcinit (mcinit_val ck2 h2 key spub (bytes t)) ci
  | None => @data_at_ HCS Tsh t_mcinit ci
  end.

End Run.

(* the returns (P4, P8): the device, the index table, the peers and the kents' entries back to memory (pure
   separation logic: a hypothesis of P4 and P8, proved from hci5_rep in hci5_close.v) *)
Definition hci5_closeH : Prop :=
  (forall sh wg D, device_rep sh wg D |-- @data_at_ Noise.CS sh t_dev wg) /\
  (forall tab T PS0 PS KE NS,
     saddrs (t_D T) = map ke_addr KE ++ map (fun x => hs_addr (peer_addr4 x)) PS0 ->
     Forall (fun d => match d with (_, sh, _) => sh = Ews end) (t_D T) ->
     map peer_addr4 PS = map peer_addr4 PS0 ->
     Forall (fun x => match x with (_, sh, _) => sh = Ews end) PS -> hnodes_peers4 NS PS ->
     itable Tsh tab T * peers_rep PS |--
     @data_at_ Noise.CS Tsh t_itab tab * iter_sepcon (fun N => @data_at_ W Ews t_peer (hn_p N)) NS *
     iter_sepcon (fun e => @data_at_ Noise.CS Ews t_entry_s (ke_addr e)) KE).

(* ---------------------------------------------------------------------- *)
(* The states                                                              *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* after the prologue: the stack frame converted, the initial globals (the shim with the v3 predicate: P1
   introduces the warnings with prot_repr4's shim_state_ex4) *)
Definition hci5_S0 (gv: globals) (L: hci5_loc) (FR: mpred) : environ -> mpred :=
  PROPx []
  (LOCALx (hci5_lvars gv L)
  (SEPx ([@data_at_ Noise.CS Tsh t_dev (l_wb L); @data_at_ Noise.CS Tsh t_itab (l_itb L);
          @data_at_ Noise.CS Tsh t_ptab (l_ptb L);
          @data_at_ HCS Tsh t_mident (l_ia L); @data_at_ HCS Tsh t_mident (l_ib L);
          hout Tsh 32 (l_rawa L); hout Tsh 32 (l_rawb L); @data_at_ W Tsh (tptr t_hnode4) (l_peers L);
          hout Tsh 148 (l_img L);
          mem_mgr gv; shim_state gv hci5_shim0; noise_globals_raw gv zeros32 zeros32 Int64.zero;
          wg_consts gv; hci5_consts gv; FR] ++ hci5_snaps0 L ++ hci5_scr L))).

(* after P1 (and after P2, P3: the same invariant): B set up, its peers (A's first; any number of others,
   randomized and their entries hashed or not after P3), no kents yet, na = A's node or NULL *)
Definition hci5_SA (gv: globals) (L: hci5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hci5_run, EX S: shim, EX w: list int64, EX NS: list hnode4, EX PS: list (val * share * peer),
  EX T: tstate, EX head: val, EX na: val,
  PROPx [hci5_run_ok R; hci5_inv x25519 R L NS PS [] T head na]
  (LOCALx ([temp HC._na na] ++ hci5_lvars gv L)
  (SEPx (hci5_world x25519 R L NS NS T head ++
         [peers_rep PS; hout Tsh 148 (l_img L)] ++ hci5_globs gv S w FR ++ hci5_snaps0 L ++ hci5_scr L))).

(* after PK: the kents KE (no snapshot yet), kes = their head *)
Definition hci5_SK (gv: globals) (L: hci5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hci5_run, EX S: shim, EX w: list int64, EX NS: list hnode4, EX PS: list (val * share * peer),
  EX T: tstate, EX head: val, EX na: val, EX KE: list kent4,
  PROPx [hci5_run_ok R; hci5_inv x25519 R L NS PS KE T head na]
  (LOCALx ([temp HC._na na; temp HC._kes (hci5_khead KE)] ++ hci5_lvars gv L)
  (SEPx (hci5_world x25519 R L NS NS T head ++
         [peers_rep PS; kents_rep W (hci5_khead KE) KE; hout Tsh 148 (l_img L)] ++
         hci5_globs gv S w FR ++ hci5_snaps0 L ++ hci5_scr L))).

(* after P4: msg allocated (non-NULL, uninitialised) *)
Definition hci5_S4 (gv: globals) (L: hci5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hci5_run, EX S: shim, EX w: list int64, EX NS: list hnode4, EX PS: list (val * share * peer),
  EX T: tstate, EX head: val, EX na: val, EX KE: list kent4, EX m: val,
  PROPx [hci5_run_ok R; hci5_inv x25519 R L NS PS KE T head na]
  (LOCALx ([temp HC._na na; temp HC._kes (hci5_khead KE); temp HC._msg m] ++ hci5_lvars gv L)
  (SEPx (hci5_world x25519 R L NS NS T head ++
         [peers_rep PS; kents_rep W (hci5_khead KE) KE; hout Tsh 148 (l_img L);
          hci5_tok t_init m; @data_at_ Noise.CS Ews t_init m] ++
         hci5_globs gv S w FR ++ hci5_snaps0 L ++ hci5_scr L))).

(* after P5: msg holds ANY well-formed initiation M; img = its image; A's latest timestamp may have moved (the
   replay boundary: the peers PS are those after it) *)
Definition hci5_S5 (gv: globals) (L: hci5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hci5_run, EX S: shim, EX w: list int64, EX NS: list hnode4, EX PS: list (val * share * peer),
  EX T: tstate, EX head: val, EX na: val, EX KE: list kent4, EX m: val, EX M: init_msg,
  PROPx [hci5_run_ok R; hci5_inv x25519 R L NS PS KE T head na; im_ok M]
  (LOCALx ([temp HC._na na; temp HC._kes (hci5_khead KE); temp HC._msg m] ++ hci5_lvars gv L)
  (SEPx (hci5_world x25519 R L NS NS T head ++
         [peers_rep PS; kents_rep W (hci5_khead KE) KE; hbytes Tsh (init_bytes M) (l_img L);
          hci5_tok t_init m; init_rep Ews m M] ++
         hci5_globs gv S w FR ++ hci5_snaps0 L ++ hci5_scr L))).

(* after P6: the boot clock now; the nodes hold their peers' snapshots, the kents theirs, ds the device's, ss the
   shim's (all taken just before the call); head0 the table's first entry; the peers are the kernel's result;
   ret = the returned peer *)
Definition hci5_S6 (gv: globals) (L: hci5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hci5_run, EX S: shim, EX w: list int64, EX NS: list hnode4, EX PS: list (val * share * peer),
  EX T: tstate, EX head: val, EX na: val, EX KE: list kent4, EX m: val, EX M: init_msg,
  PROPx [hci5_run_ok R; hci5_inv x25519 R L NS PS KE T head na; im_ok M;
         0 <= Int64.unsigned (s_boot S) < 2 ^ 62]
  (LOCALx ([temp HC._kes (hci5_khead KE); temp HC._msg m; temp HC._now (Vlong (s_boot S));
            temp HC._head0 (hd nullval (t_L T));
            temp HC._ret (peer_result (cin_res x25519 aead_dec (hci5_DB x25519 R L) PS M S))] ++
           hci5_lvars gv L)
  (SEPx (hci5_world x25519 R L NS (hnodes_snapped4 T NS PS) T head ++
         [peers_rep (peers_after PS (cin_res x25519 aead_dec (hci5_DB x25519 R L) PS M S));
          kents_rep W (hci5_khead KE) (map (kent_snapped T) KE);
          @data_at CKS Tsh t_devsnap (devsnap_val (hci5_DB x25519 R L) head) (l_ds L);
          @data_at CKS Tsh t_shimsnap (shimsnap_val S w) (l_ss L);
          hbytes Tsh (init_bytes M) (l_img L); hci5_tok t_init m; init_rep Ews m M] ++
         hci5_globs gv S w FR ++ hci5_scr L))).

(* after P7: target = the harness's model's node; ci = its stages on acceptance *)
Definition hci5_S7 (gv: globals) (L: hci5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hci5_run, EX S: shim, EX w: list int64, EX NS: list hnode4, EX PS: list (val * share * peer),
  EX T: tstate, EX head: val, EX na: val, EX KE: list kent4, EX m: val, EX M: init_msg,
  PROPx [hci5_run_ok R; hci5_inv x25519 R L NS PS KE T head na; im_ok M;
         0 <= Int64.unsigned (s_boot S) < 2 ^ 62]
  (LOCALx ([temp HC._kes (hci5_khead KE); temp HC._msg m; temp HC._now (Vlong (s_boot S));
            temp HC._head0 (hd nullval (t_L T));
            temp HC._ret (peer_result (cin_res x25519 aead_dec (hci5_DB x25519 R L) PS M S));
            temp HC._target (hci5_tnode NS (hci5_tgt x25519 aead_dec (hci5_IB x25519 R) PS M (s_boot S)))] ++
           hci5_lvars gv L)
  (SEPx (hci5_world x25519 R L NS (hnodes_snapped4 T NS PS) T head ++
         [peers_rep (peers_after PS (cin_res x25519 aead_dec (hci5_DB x25519 R L) PS M S));
          kents_rep W (hci5_khead KE) (map (kent_snapped T) KE);
          @data_at CKS Tsh t_devsnap (devsnap_val (hci5_DB x25519 R L) head) (l_ds L);
          @data_at CKS Tsh t_shimsnap (shimsnap_val S w) (l_ss L);
          hbytes Tsh (init_bytes M) (l_img L); hci5_tok t_init m; init_rep Ews m M;
          hci5_ci_rep (hci5_tgt x25519 aead_dec (hci5_IB x25519 R) PS M (s_boot S)) (l_ci L)] ++
         hci5_globs gv S w FR ++
         [hout Tsh 32 (l_pub L); hout Tsh 12 (l_ts L); hout Tsh 148 (l_imga L);
          @data_at_ HCS Tsh t_minit (l_mi L); hout Tsh 32 (l_eraw L); hout Tsh 32 (l_ss1 L);
          hout Tsh 32 (l_ss2 L)]))).

End States.

(* main's post (TT) weakened to the canonical form forward needs for a return *)
Lemma hci5_post_canon {Espec: OracleKind} {cs: compspecs} Delta P c Q gv F :
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (PROP () LOCAL () SEP (TT))) F)) ->
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (hci5_post gv)) F)).
Proof.
  intros H. eapply semax_post; [| | | | apply H]; intros; simpl; intros rho; apply andp_left2;
    try apply derives_refl.
  apply sepcon_derives; [| apply derives_refl]. revert rho. apply bind_ret_derives. intros rho. apply TT_right.
Qed.
