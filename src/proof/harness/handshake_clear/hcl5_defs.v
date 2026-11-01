(* law handshake_clear: main's context and the states
   between its phases.

   Conventions (all phases):
   - main runs in the world compspecs W := W_handshake_clear (Delta hcl5_Delta).  The SEP items are kept in the
     compspecs of the specifications that consume them: protocol objects through prot_repr3's predicates
     (device_rep, peers_rep, itable, ptable: Noise.CS inside), the shim with EXACT warnings (shim_state4 gv S w,
     prot_repr4.v), the structs dev_snap / shim_snap as `@data_at(_) CKS` (hc4_specs.v), the local
     `peers` (struct hnode * ) as `@data_at(_) W` (hnodes_add4 wants it at CKS: convert, hcl5_conv.v), the node list
     as `hnodes_rep4 W`, the kents as `kents_rep W`, byte buffers as hbytes / hout (HCS).
   - main's body = S; return 0 with S = the 27 statements of hcl5_stmts (hcl5_cut.v): P1 0..3, P2 4..5, P3 6,
     P4 7, PK 8, P5 9..15, P6 16..18, P7 19..20, P8 21..26.
   - The states: hcl5_S0 (prologue), hcl5_SA (after P1 and after P2: the same invariant, no kents, T any table of
     the invariant), hcl5_SB (after P3 and after P4: SA with at least one peer), hcl5_SK (after PK: the kents),
     hcl5_S5 (after P5 and after P6: the snapshots taken, P's handshake cleared), hcl5_S7 (after P7: `hashed`);
     P8 ends in FF (it returns); P3 may return.
   - The peers: PS (the protocol's list, in public-key-chain order = the node list's order, both pushed at the
     head by hnodes_add), NS (the harness's nodes), KE (the kents).  The index table's pool is the kents' entries
     then the peers' handshake entries (hcl5_T_ok), the peers' keypair slots are NULL or kents (hcl5_slots_ok).
     Every peer satisfies hcl5_pok (share Ews, the device, the static identity, the handshake's lengths,
     1 .. INT_MAX - 1 references).
   - The target: the node of index i (hnodes_pick), its peer p = hn_p (Znth i NS) = the peer of index i of PS;
     after the clear: peers hcl5_clr i PS (that peer's handshake zeroed, hs_zero), table t_remove T (hs_addr p).
   - FR: an opaque frame (TT * has_ext), carried along. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_world.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_cut.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_globals.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_spec.
Require WgNoise.contracts.x_handshake_clear.
Require WgNoise.harness.x_handshake_clear.code.
Local Open Scope logic.

Module HC := WgNoise.harness.x_handshake_clear.code.

Notation W := W_handshake_clear.

(* ---------------------------------------------------------------------- *)
(* The hypotheses of the phase lemmas                                      *)
(* ---------------------------------------------------------------------- *)

(* the statement of prot_rep_lemmas3 (a hypothesis here, discharged by the assembly) *)
Section Rep.
#[local] Existing Instance Noise.CS.
Definition hcl5_rep : Prop :=
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

Definition hcl5_hyps : Prop := x25519_props x25519 /\ hcl5_rep.

(* ---------------------------------------------------------------------- *)
(* main's context                                                          *)
(* ---------------------------------------------------------------------- *)

Definition hcl5_Gprog : funspecs := hcl5_imports x25519 W ++ hcl5_G.
Definition hcl5_Delta : tycontext := func_tycontext HC.f_main hcl5_V hcl5_Gprog [].

End Defs.

Definition hcl5_R (gv: globals) : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (hcl5_post gv)) (@stackframe_of W HC.f_main).

(* ---------------------------------------------------------------------- *)
(* The locals and the globals                                              *)
(* ---------------------------------------------------------------------- *)

(* the addresses of main's 8 local variables *)
Record hcl5_loc := mkLoc5 {
  l_w: val; l_it: val; l_pt: val; l_raw: val; l_pub: val; l_peers: val; l_ds: val; l_ss: val }.

Definition t_dsnap := Tstruct HC._dev_snap noattr.
Definition t_ssnap := Tstruct HC._shim_snap noattr.

Definition hcl5_lvars (gv: globals) (L: hcl5_loc) : list localdef :=
  [lvar HC._w t_dev (l_w L); lvar HC._it t_itab (l_it L); lvar HC._pt t_ptab (l_pt L);
   lvar HC._raw (tarray tuchar 32) (l_raw L); lvar HC._pub (tarray tuchar 32) (l_pub L);
   lvar HC._peers (tptr t_hnode4) (l_peers L);
   lvar HC._ds t_dsnap (l_ds L); lvar HC._ss t_ssnap (l_ss L);
   gvars gv].

(* the globals of a state: allocator, shim (exact warnings), the read-only tables, the frame *)
Definition hcl5_globs (gv: globals) (S: shim) (w: list int64) (FR: mpred) : list mpred :=
  [mem_mgr gv; shim_state4 gv S w; wg_consts gv; FR].

(* the snapshot locals ds, ss before the snapshots *)
Definition hcl5_snaps0 (L: hcl5_loc) : list mpred :=
  [@data_at_ CKS Tsh t_devsnap (l_ds L); @data_at_ CKS Tsh t_shimsnap (l_ss L)].

(* the scratch local pub (any contents) *)
Definition hcl5_scr (L: hcl5_loc) : list mpred := [hout Tsh 32 (l_pub L)].

(* ---------------------------------------------------------------------- *)
(* The run: the setup's draws, and the objects they determine              *)
(* ---------------------------------------------------------------------- *)

Record hcl5_run := mkRun5 {
  r_raw: list byte;     (* raw: the device's private key *)
  r_sec: list byte;     (* the cookie secret drawn by setup_device *)
  r_boot0: int64 }.     (* the boot clock *)

Definition hcl5_run_ok (R: hcl5_run) : Prop :=
  Zlength (r_raw R) = 32 /\ Zlength (r_sec R) = 32 /\ 0 <= Int64.unsigned (r_boot0 R) < 2 ^ 62.

(* the head of the node list, of the kent list *)
Definition hcl5_head (NS: list hnode4) : val := match NS with [] => nullval | N :: _ => hn_addr N end.
Definition hcl5_khead (KE: list kent4) : val := match KE with [] => nullval | e :: _ => ke_addr e end.

(* the index table's pool: the kents' entries, then the peers' handshake entries (shares Ews), each peer's entry
   with peer = that peer, each kent's entry with a peer of PS (its owner) *)
Definition hcl5_T_ok (PS: list (val * share * peer)) (KE: list kent4) (T: tstate) : Prop :=
  saddrs (t_D T) = map ke_addr KE ++ map (fun x => hs_addr (peer_addr4 x)) PS /\
  Forall (fun d => match d with (_, sh, _) => sh = Ews end) (t_D T) /\
  Forall (fun x => e_peer (t_entry_d T (hs_addr (peer_addr4 x))) = peer_addr4 x) PS /\
  Forall (fun e => In (e_peer (t_entry_d T (ke_addr e))) (map peer_addr4 PS)) KE.

(* the peers' keypair slots: NULL or kents *)
Definition hcl5_slots_ok (KE: list kent4) (PS: list (val * share * peer)) : Prop :=
  Forall (fun x => match x with (_, _, P) =>
            Forall (fun k => k = nullval \/ In k (map ke_addr KE)) [p_cur P; p_prev P; p_next P] end) PS.

(* every peer of the device *)
Definition hcl5_pok (L: hcl5_loc) (x: val * share * peer) : Prop :=
  match x with (a, sh, P) =>
    sh = Ews /\ p_device P = l_w L /\ hs_sid (p_hs P) = id_addr (l_w L) /\ hs_ok (p_hs P) /\
    0 < Int.unsigned (p_refs P) < 2147483647
  end.

(* the lists: peers PS (chain from head), nodes NS (same peers, same order), kents KE, the table T *)
Definition hcl5_inv (L: hcl5_loc) (NS: list hnode4) (PS: list (val * share * peer)) (KE: list kent4)
  (T: tstate) (head: val) : Prop :=
  Forall (hcl5_pok L) PS /\ peers_wf PS /\ pk_chain head PS /\ hnodes_peers4 NS PS /\
  hcl5_T_ok PS KE T /\ hcl5_slots_ok KE PS.

(* a default peer item (Znth over peer lists) *)
Definition hcl5_hs0 : handshake :=
  mkHS Int.zero Int64.zero nullval [] [] [] [] [] [] [] [] Int.zero.
Definition hcl5_ck0 : cookie := mkCookie Int64.zero false [] false [] [] [].
#[export] Instance hcl5_pinh : Inhabitant (val * share * peer) :=
  (nullval, Ews, mkPeer nullval false nullval nullval nullval hcl5_hs0 Int64.zero hcl5_ck0 Int.zero Int64.zero
                        nullval).

(* the peers after wg_noise_handshake_clear of the handshake of the peer of index i *)
Definition hcl5_clr1 (x: val * share * peer) : val * share * peer :=
  match x with (a, sh, P) => (a, sh, p_set_hs P (hs_zero (p_hs P))) end.
Definition hcl5_clr (i: Z) (PS: list (val * share * peer)) : list (val * share * peer) :=
  upd_Znth i PS (hcl5_clr1 (Znth i PS)).

(* the number of the OTHER peers (not p) whose handshake entry was hashed in T (the loop's `hashed`) *)
Definition hcl5_nh (T: tstate) (p: val) (PS: list (val * share * peer)) : Z :=
  Zlength (filter (fun x => andb (negb (veqb (peer_addr4 x) p)) (vin (hs_addr (peer_addr4 x)) (t_L T))) PS).

Section Run.
Variable x25519: list byte -> list byte -> list byte.

(* the device after setup_device *)
Definition hcl5_D (R: hcl5_run) (L: hcl5_loc) : device :=
  setup_dev x25519 (l_w L) (l_it L) (l_pt L) (r_raw R) (r_sec R) (r_boot0 R).

(* the objects that live from the setup to the end: the device and its tables, the raw key, the local `peers`,
   the node list (NS gives its order and head, NS' its contents: NS before the snapshots) *)
Definition hcl5_world (R: hcl5_run) (L: hcl5_loc) (NS NS': list hnode4) (T: tstate) (head: val) : list mpred :=
  [device_rep Tsh (l_w L) (hcl5_D R L); itable Tsh (l_it L) T; ptable Tsh (l_pt L) head;
   hbytes Tsh (r_raw R) (l_raw L);
   @data_at W Tsh (tptr t_hnode4) (hcl5_head NS) (l_peers L);
   hnodes_rep4 W (hcl5_head NS) NS'].

End Run.

(* the returns (P3, P8): the device, the index table, the peers and the kents' entries back to memory (pure
   separation logic: a hypothesis of P3 and P8, proved from hcl5_rep in hcl5_close.v) *)
Definition hcl5_closeH : Prop :=
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

(* after the prologue: the stack frame converted, the initial globals (the shim with the v3 predicate: P1
   introduces the warnings with prot_repr4's shim_state_ex4) *)
Definition hcl5_S0 (gv: globals) (L: hcl5_loc) (FR: mpred) : environ -> mpred :=
  PROPx []
  (LOCALx (hcl5_lvars gv L)
  (SEPx ([@data_at_ Noise.CS Tsh t_dev (l_w L); @data_at_ Noise.CS Tsh t_itab (l_it L);
          @data_at_ Noise.CS Tsh t_ptab (l_pt L); hout Tsh 32 (l_raw L);
          @data_at_ W Tsh (tptr t_hnode4) (l_peers L);
          mem_mgr gv; shim_state gv hcl5_shim0; wg_consts gv; FR] ++ hcl5_snaps0 L ++ hcl5_scr L))).

(* after P1 (no peer) and after P2 (the peers added; their entries in the pool, none hashed is NOT claimed: T is
   any table of the invariant), no kents *)
Definition hcl5_SA (gv: globals) (L: hcl5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcl5_run, EX S: shim, EX w: list int64, EX NS: list hnode4, EX PS: list (val * share * peer),
  EX T: tstate, EX head: val,
  PROPx [hcl5_run_ok R; hcl5_inv L NS PS [] T head]
  (LOCALx (hcl5_lvars gv L)
  (SEPx (hcl5_world x25519 R L NS NS T head ++ [peers_rep PS] ++ hcl5_globs gv S w FR ++
         hcl5_snaps0 L ++ hcl5_scr L))).

(* after P3 (peers != NULL) and after P4 (the handshakes and the rest randomized, entries hashed or not) *)
Definition hcl5_SB (gv: globals) (L: hcl5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcl5_run, EX S: shim, EX w: list int64, EX NS: list hnode4, EX PS: list (val * share * peer),
  EX T: tstate, EX head: val,
  PROPx [hcl5_run_ok R; hcl5_inv L NS PS [] T head; NS <> []]
  (LOCALx (hcl5_lvars gv L)
  (SEPx (hcl5_world x25519 R L NS NS T head ++ [peers_rep PS] ++ hcl5_globs gv S w FR ++
         hcl5_snaps0 L ++ hcl5_scr L))).

(* after PK: the kents KE (no snapshot yet), kes = their head *)
Definition hcl5_SK (gv: globals) (L: hcl5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcl5_run, EX S: shim, EX w: list int64, EX NS: list hnode4, EX PS: list (val * share * peer),
  EX T: tstate, EX head: val, EX KE: list kent4,
  PROPx [hcl5_run_ok R; hcl5_inv L NS PS KE T head; NS <> []]
  (LOCALx ([temp HC._kes (hcl5_khead KE)] ++ hcl5_lvars gv L)
  (SEPx (hcl5_world x25519 R L NS NS T head ++ [peers_rep PS; kents_rep W (hcl5_khead KE) KE] ++
         hcl5_globs gv S w FR ++ hcl5_snaps0 L ++ hcl5_scr L))).

(* after P5 (and after P6, which only checks): the target = the node of index i; the nodes hold their peers'
   snapshots, the kents theirs, ds the device's, ss the shim's (all taken in T, just before the call); h = &p's
   handshake; the call done: p's handshake zeroed (hcl5_clr), its entry removed from the table *)
Definition hcl5_S5 (gv: globals) (L: hcl5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcl5_run, EX S: shim, EX w: list int64, EX NS: list hnode4, EX PS: list (val * share * peer),
  EX T: tstate, EX head: val, EX KE: list kent4, EX i: Z,
  PROPx [hcl5_run_ok R; hcl5_inv L NS PS KE T head; 0 <= i < Zlength NS]
  (LOCALx ([temp HC._kes (hcl5_khead KE); temp HC._target (hn_addr (Znth i NS));
            temp HC._h (hs_addr (hn_p (Znth i NS)))] ++ hcl5_lvars gv L)
  (SEPx (hcl5_world x25519 R L NS (hnodes_snapped4 T NS PS) (t_remove T (hs_addr (hn_p (Znth i NS)))) head ++
         [peers_rep (hcl5_clr i PS); kents_rep W (hcl5_khead KE) (map (kent_snapped T) KE);
          @data_at CKS Tsh t_devsnap (devsnap_val (hcl5_D x25519 R L) head) (l_ds L);
          @data_at CKS Tsh t_shimsnap (shimsnap_val S w) (l_ss L)] ++
         hcl5_globs gv S w FR ++ hcl5_scr L))).

(* after P7: hashed = the number of the other peers whose entry was hashed in T *)
Definition hcl5_S7 (gv: globals) (L: hcl5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcl5_run, EX S: shim, EX w: list int64, EX NS: list hnode4, EX PS: list (val * share * peer),
  EX T: tstate, EX head: val, EX KE: list kent4, EX i: Z,
  PROPx [hcl5_run_ok R; hcl5_inv L NS PS KE T head; 0 <= i < Zlength NS]
  (LOCALx ([temp HC._kes (hcl5_khead KE); temp HC._target (hn_addr (Znth i NS));
            temp HC._hashed (Vlong (Int64.repr (hcl5_nh T (hn_p (Znth i NS)) PS)))] ++ hcl5_lvars gv L)
  (SEPx (hcl5_world x25519 R L NS (hnodes_snapped4 T NS PS) (t_remove T (hs_addr (hn_p (Znth i NS)))) head ++
         [peers_rep (hcl5_clr i PS); kents_rep W (hcl5_khead KE) (map (kent_snapped T) KE);
          @data_at CKS Tsh t_devsnap (devsnap_val (hcl5_D x25519 R L) head) (l_ds L);
          @data_at CKS Tsh t_shimsnap (shimsnap_val S w) (l_ss L)] ++
         hcl5_globs gv S w FR ++ hcl5_scr L))).

End States.

(* main's post (TT) weakened to the canonical form forward needs for a return *)
Lemma hcl5_post_canon {Espec: OracleKind} {cs: compspecs} Delta P c Q gv F :
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (PROP () LOCAL () SEP (TT))) F)) ->
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (hcl5_post gv)) F)).
Proof.
  intros H. eapply semax_post; [| | | | apply H]; intros; simpl; intros rho; apply andp_left2;
    try apply derives_refl.
  apply sepcon_derives; [| apply derives_refl]. revert rho. apply bind_ret_derives. intros rho. apply TT_right.
Qed.
