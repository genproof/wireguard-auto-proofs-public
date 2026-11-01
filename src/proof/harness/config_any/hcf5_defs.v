(* law config_any: main's context and the states between its
   phases.

   Conventions (all phases):
   - main runs in the world compspecs W := W_config_any (hcf5_world.v; Delta hcf5_Delta).  SEP items are kept in the
     compspecs of the specifications that consume them: protocol objects through prot_repr3's predicates
     (device_rep, peer_rep, itable, ptable, hs_rep, cookie_rep, entry_at: Noise.CS inside), the shim with EXACT
     warnings (shim_state4 gv S w), m_identity / hs_snap as `@data_at(_) HCS`, dev_snap / pr_snap / shim_snap as
     `@data_at(_) CKS`, the kents as `kents_rep W`, byte buffers as hbytes / hout (HCS).
   - main's body = S; return 0 with S = the 96 statements of hcf5_stmts (hcf5_cut.v), phases
       PA1 S0 -> SA1, PA2 SA1 -> SA, PK SA -> SK, PS SK -> SX0, P1 SX0 -> SX1,
       C1 / P2 / C2 / P3 / C3 / P4 / C4: SX1 -> SX1,  P5a SX1 -> S5a, P5b S5a -> S5b, P5c S5b -> SX5,
       C5 / P6 / C6: SX5 -> SX5,  PE SX5 -> (return).
   - From PS on, every state is `hcf5_Fx`: the device D (device_rep of w), the index table T (itable of it), the
     public-key table (head p), the peer P (peer_rep of p), the kents KE (kents_rep), the four snapshots ds = D0,
     hs0 = sn0, ps0 = P0, ss = (S0, w0), the temps kes, head0 = h0, refs0 = r0, now, raw0 and pub, the globals; with
     PROP: a stage fact Px, the invariant hcf5_inv (pointers, the table's pool, the kents' snapshots) and the frame
     equalities hcf5_same (exactly what the frame CHECK computes: each comparison is true); X = the stage's other
     locals (one mpred).  The C1..C6 CHECKs go from a state to itself.
   - The index table's pool (hcf5_T_ok): q's handshake entry (from P5a on: qin = true), the kents' entries (Ews),
     p's handshake entry (Tsh, the stack peer p); the peers' memory without their entries.
   - q (the stack peer of step 5): data_at_ until P5a splits it (hcf5_sepH): its handshake (hs_mem false: hs_rep +
     the device field), its entry (in the pool), its cookie, the rest (hcf5_qrest).
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
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.config_any.hcf5_world.
Require Import WgNoise.proof.harness.config_any.hcf5_cut.
Require Import WgNoise.proof.harness.config_any.hcf5_globals.
Require Import WgNoise.proof.harness.config_any.hcf5_spec.
Require WgNoise.contracts.x_config_any.
Require WgNoise.harness.x_config_any.code.
Local Open Scope logic.

Module HF := WgNoise.harness.x_config_any.code.

Notation W := W_config_any.

(* ---------------------------------------------------------------------- *)
(* The hypotheses of the phase lemmas, main's context                      *)
(* ---------------------------------------------------------------------- *)

Definition hcf5_hyps (x25519: list byte -> list byte -> list byte) : Prop := x25519_props x25519.

Definition hcf5_Gprog x25519 : funspecs := hcf5_imports x25519 W ++ hcf5_G.
Definition hcf5_Delta x25519 : tycontext := func_tycontext HF.f_main hcf5_V (hcf5_Gprog x25519) [].

Definition hcf5_R (gv: globals) : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (hcf5_post gv)) (@stackframe_of W HF.f_main).

(* ---------------------------------------------------------------------- *)
(* The locals and the globals                                              *)
(* ---------------------------------------------------------------------- *)

(* the addresses of main's 17 local variables *)
Record hcf5_loc := mkLocF {
  l_w: val; l_it: val; l_pt: val; l_p: val; l_q: val; l_id: val; l_hs0: val; l_hq: val; l_ps0: val;
  l_ds: val; l_ss: val; l_raw0: val; l_raw: val; l_pub: val; l_qpub: val; l_psk: val; l_dh: val }.

Definition hcf5_lvars (gv: globals) (L: hcf5_loc) : list localdef :=
  [lvar HF._w t_dev (l_w L); lvar HF._it t_itab (l_it L); lvar HF._pt t_ptab (l_pt L);
   lvar HF._p t_peer (l_p L); lvar HF._q t_peer (l_q L); lvar HF._id t_mident (l_id L);
   lvar HF._hs0 t_hsnap (l_hs0 L); lvar HF._hq t_hsnap (l_hq L); lvar HF._ps0 t_prsnap (l_ps0 L);
   lvar HF._ds t_devsnap (l_ds L); lvar HF._ss t_shimsnap (l_ss L);
   lvar HF._raw0 (tarray tuchar 32) (l_raw0 L); lvar HF._raw (tarray tuchar 32) (l_raw L);
   lvar HF._pub (tarray tuchar 32) (l_pub L); lvar HF._qpub (tarray tuchar 32) (l_qpub L);
   lvar HF._psk (tarray tuchar 32) (l_psk L); lvar HF._dh (tarray tuchar 32) (l_dh L);
   gvars gv].

(* the globals of a state: allocator, shim (exact warnings), noise.c's globals (never initialised by this harness:
   all zero), the read-only tables, the harness's constants (hcf5_globals.v), the frame *)
Definition hcf5_globs (gv: globals) (S: shim) (w: list int64) (FR: mpred) : list mpred :=
  [mem_mgr gv; shim_state4 gv S w; noise_globals_raw gv zeros32 zeros32 Int64.zero; wg_consts gv; hcf5_consts gv; FR].

(* the four snapshot locals before the snapshots *)
Definition hcf5_pre (L: hcf5_loc) : list mpred :=
  [@data_at_ CKS Tsh t_devsnap (l_ds L); @data_at_ HCS Tsh t_hsnap (l_hs0 L);
   @data_at_ CKS Tsh t_prsnap (l_ps0 L); @data_at_ CKS Tsh t_shimsnap (l_ss L)].

(* the locals of steps 1..6 before they are used *)
Definition hcf5_X0 (L: hcf5_loc) : mpred :=
  @data_at_ HCS Tsh t_mident (l_id L) * hout Tsh 32 (l_raw L) * hout Tsh 32 (l_dh L) *
  @data_at_ HCS Tsh t_hsnap (l_hq L) * @data_at_ Noise.CS Tsh t_peer (l_q L) *
  hout Tsh 32 (l_qpub L) * hout Tsh 32 (l_psk L).

(* ---------------------------------------------------------------------- *)
(* The run and the objects                                                 *)
(* ---------------------------------------------------------------------- *)

(* the setup's draws: raw0, setup_device's cookie secret, the boot clock, P's public key *)
Record hcf5_run := mkRunF { r_raw0: list byte; r_sec0: list byte; r_now: int64; r_pub: list byte }.

Definition hcf5_run_ok (R: hcf5_run) : Prop :=
  Zlength (r_raw0 R) = 32 /\ Zlength (r_sec0 R) = 32 /\ 0 <= Int64.unsigned (r_now R) < 2 ^ 62 /\
  Zlength (r_pub R) = 32.

Definition hcf5_khead (KE: list kent4) : val := match KE with [] => nullval | e :: _ => ke_addr e end.

(* the share of the pool item at a *)
Definition hcf5_tsh (T: tstate) (a: val) : share :=
  match sfind (t_D T) a with Some (sh, _) => sh | None => Share.bot end.

(* q's entry in the pool (from step 5 on) *)
Definition hcf5_qs (L: hcf5_loc) (qin: bool) : list val := if qin then [hs_addr (l_q L)] else [].

(* the device: no net device, its checker's device is w, its tables it and pt *)
Definition hcf5_dok (L: hcf5_loc) (D: device) : Prop :=
  d_dev D = nullval /\ cc_dev (d_cc D) = l_w L /\ d_ptab D = l_pt L /\ d_itab D = l_it L.

(* the peer p: of w, last of the public-key chain, its handshake's identity w's, its public key pub *)
Definition hcf5_pok (R: hcf5_run) (L: hcf5_loc) (P: peer) : Prop :=
  p_device P = l_w L /\ p_pknext P = nullval /\ hs_sid (p_hs P) = id_addr (l_w L) /\
  hs_rstatic (p_hs P) = r_pub R.

(* p's keypair slots: NULL or kents *)
Definition hcf5_slots_ok (KE: list kent4) (P: peer) : Prop :=
  Forall (fun k => k = nullval \/ In k (map ke_addr KE)) [p_cur P; p_prev P; p_next P].

(* the pool: [q's entry,] the kents' entries (Ews, peer p), p's entry (Tsh, peer p); q's entry (Tsh) is the
   initial one, unhashed *)
Definition hcf5_T_ok (L: hcf5_loc) (KE: list kent4) (qin: bool) (T: tstate) : Prop :=
  saddrs (t_D T) = hcf5_qs L qin ++ map ke_addr KE ++ [hs_addr (l_p L)] /\
  Forall (fun e => hcf5_tsh T (ke_addr e) = Ews /\ e_peer (t_entry_d T (ke_addr e)) = l_p L) KE /\
  hcf5_tsh T (hs_addr (l_p L)) = Tsh /\ e_peer (t_entry_d T (hs_addr (l_p L))) = l_p L /\
  (qin = true -> hcf5_tsh T (hs_addr (l_q L)) = Tsh /\
                 t_entry_d T (hs_addr (l_q L)) = mkEntry (l_q L) IDX_HANDSHAKE Int.zero /\
                 ~ In (hs_addr (l_q L)) (t_L T)).

(* the kents carry snapshots whose pointers are NULL, p or pool entries *)
Definition hcf5_ksnap_ok (L: hcf5_loc) (T: tstate) (KE: list kent4) : Prop :=
  Forall (fun e => ke_snap e <> None /\ Forall (vp_ok (l_p L :: saddrs (t_D T))) (kent_ptrs T e)) KE.

Definition hcf5_inv (R: hcf5_run) (L: hcf5_loc) (S: shim) (w: list int64) (D: device) (P: peer) (T: tstate)
  (KE: list kent4) (qin: bool) : Prop :=
  hcf5_run_ok R /\ s_boot S = r_now R /\ Zlength w = 5 /\ hcf5_dok L D /\ hcf5_pok R L P /\
  hcf5_slots_ok KE P /\ hcf5_T_ok L KE qin T /\ hcf5_ksnap_ok L T KE.

(* the frame CHECK's comparisons, each true *)
Definition hcf5_same (L: hcf5_loc) (D: device) (P: peer) (T: tstate) (KE: list kent4) (S: shim) (w: list int64)
  (D0: device) (sn0: hsnap) (P0: peer) (r0: int) (S0: shim) (w0: list int64) (h0: val) : Prop :=
  dev_eqb D0 (l_p L) D (l_p L) = true /\ snap_eqb sn0 (hs_snap_cur T (l_p L) P) = true /\
  pr_eqb P0 P = true /\ r0 = p_refs P /\ shim_eqb S0 w0 S w = true /\ forallb (kent_same T) KE = true /\
  h0 = hd nullval (t_L T).

(* the objects of every state from PS on *)
Definition hcf5_core (gv: globals) (L: hcf5_loc) (FR: mpred) (R: hcf5_run) (S: shim) (w: list int64)
  (D: device) (P: peer) (T: tstate) (KE: list kent4) (D0: device) (sn0: hsnap) (P0: peer) (S0: shim)
  (w0: list int64) : list mpred :=
  [device_rep Tsh (l_w L) D; itable Tsh (l_it L) T; ptable Tsh (l_pt L) (l_p L); peer_rep Tsh (l_p L) P;
   kents_rep W (hcf5_khead KE) KE;
   @data_at CKS Tsh t_devsnap (devsnap_val D0 (l_p L)) (l_ds L);
   @data_at HCS Tsh t_hsnap (hsnap_val sn0) (l_hs0 L);
   @data_at CKS Tsh t_prsnap (prsnap_val P0) (l_ps0 L);
   @data_at CKS Tsh t_shimsnap (shimsnap_val S0 w0) (l_ss L);
   hbytes Tsh (r_raw0 R) (l_raw0 L); hbytes Tsh (r_pub R) (l_pub L)] ++ hcf5_globs gv S w FR.

Definition hcf5_Fx (gv: globals) (L: hcf5_loc) (FR: mpred) (QL: list localdef) (Px: Prop) (X: mpred)
  (R: hcf5_run) (S: shim) (w: list int64) (D: device) (P: peer) (T: tstate) (KE: list kent4) (qin: bool)
  (D0: device) (sn0: hsnap) (P0: peer) (r0: int) (S0: shim) (w0: list int64) (h0: val) : environ -> mpred :=
  PROPx [Px; hcf5_inv R L S w D P T KE qin; hcf5_same L D P T KE S w D0 sn0 P0 r0 S0 w0 h0]
  (LOCALx (QL ++ [temp HF._kes (hcf5_khead KE); temp HF._head0 h0; temp HF._refs0 (Vint r0);
                  temp HF._now (Vlong (r_now R))] ++ hcf5_lvars gv L)
  (SEPx (hcf5_core gv L FR R S w D P T KE D0 sn0 P0 S0 w0 ++ [X]))).

Definition hcf5_F (gv: globals) (L: hcf5_loc) (FR: mpred) (Px: Prop) (X: mpred)
  (R: hcf5_run) (S: shim) (w: list int64) (D: device) (P: peer) (T: tstate) (KE: list kent4) (qin: bool)
  (D0: device) (sn0: hsnap) (P0: peer) (r0: int) (S0: shim) (w0: list int64) (h0: val) : environ -> mpred :=
  hcf5_Fx gv L FR [] Px X R S w D P T KE qin D0 sn0 P0 r0 S0 w0 h0.

(* ---------------------------------------------------------------------- *)
(* q, the stack peer of step 5                                             *)
(* ---------------------------------------------------------------------- *)

Section NoiseQ.
#[local] Existing Instance Noise.CS.
(* the fields of q that no step touches (with the struct's padding) *)
Definition hcf5_qrest (q: val) : mpred :=
  field_at_ Tsh t_peer [StructField I._is_dead] q * field_at_ Tsh t_peer [StructField I._keypairs] q *
  field_at_ Tsh t_peer [StructField I._last_sent_handshake] q * field_at_ Tsh t_peer [StructField I._refcount] q *
  field_at_ Tsh t_peer [StructField I._internal_id] q * field_at_ Tsh t_peer [StructField I._pubkey_next] q *
  spacer Tsh 9 16 q * spacer Tsh 476 480 q.
End NoiseQ.

(* a peer record holding q's handshake H (hs_mem false reads only its handshake) *)
Definition hcf5_qpeer (H: handshake) : peer :=
  mkPeer nullval false nullval nullval nullval H Int64.zero cookie_zero Int.zero Int64.zero nullval.

Definition hcf5_qok (L: hcf5_loc) (H: handshake) : Prop := hs_ok H /\ hs_sid H = id_addr (l_w L).

(* the separation-logic facts of q and of the returns: a hypothesis of P5a and PE, proved in hcf5_sep.v *)
Definition hcf5_sepH : Prop :=
  (forall q, @data_at_ Noise.CS Tsh t_peer q =
             @field_at_ Noise.CS Tsh t_peer [StructField I._device] q * @data_at_ Noise.CS Tsh t_hs (hs_addr q) *
             @data_at_ Noise.CS Tsh t_cookie (cookie_addr q) * hcf5_qrest q) /\
  (forall q H E n h C, hs_mem false Tsh q (hcf5_qpeer H) * entry_at Tsh (hs_addr q) E n h *
                       cookie_rep Tsh (cookie_addr q) C * hcf5_qrest q |-- @data_at_ Noise.CS Tsh t_peer q) /\
  (forall sh wg D, device_rep sh wg D |-- @data_at_ Noise.CS sh t_dev wg) /\
  (forall L KE qin T, hcf5_T_ok L KE qin T ->
     itable Tsh (l_it L) T |--
     @data_at_ Noise.CS Tsh t_itab (l_it L) *
     iter_sepcon (fun e => @data_at_ Noise.CS Ews t_entry_s (ke_addr e)) KE *
     (EX E: entry, EX n: val, EX h: bool, entry_at Tsh (hs_addr (l_p L)) E n h) *
     (if qin then EX E: entry, EX n: val, EX h: bool, entry_at Tsh (hs_addr (l_q L)) E n h else emp)).

(* ---------------------------------------------------------------------- *)
(* The states                                                              *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.

(* w after setup_device, p after setup_peer *)
Definition hcf5_D0 (R: hcf5_run) (L: hcf5_loc) : device :=
  setup_dev x25519 (l_w L) (l_it L) (l_pt L) (r_raw0 R) (r_sec0 R) (r_now R).
Definition hcf5_P0 (R: hcf5_run) (L: hcf5_loc) : peer :=
  setup_peer_val x25519 (hcf5_D0 R L) (l_w L) (l_p L) nullval (r_pub R) zeros32 (Int64.repr 1).

(* step 1's identity: the device's identity is wg_noise_set_static_identity_private_key's of RAW over any prior
   identity; id holds m_identity_of(RAW) *)
Definition hcf5_Px1 (D: device) (RAW: list byte) : Prop :=
  Zlength RAW = 32 /\ exists ID0: identity, id_ok ID0 /\ d_id D = identity_of x25519 ID0 RAW.

Definition hcf5_X1 (L: hcf5_loc) (RAW: list byte) : mpred :=
  @data_at HCS Tsh t_mident (mident_val (mident_of x25519 RAW)) (l_id L) * hbytes Tsh RAW (l_raw L) *
  hout Tsh 32 (l_dh L) * @data_at_ HCS Tsh t_hsnap (l_hq L) * @data_at_ Noise.CS Tsh t_peer (l_q L) *
  hout Tsh 32 (l_qpub L) * hout Tsh 32 (l_psk L).

(* q's handshake after wg_noise_handshake_init *)
Definition hcf5_qhs (D: device) (L: hcf5_loc) (QPUB PSK: list byte) (ub: bool) : handshake :=
  hs_initial x25519 (d_id D) (id_addr (l_w L)) QPUB (if ub then PSK else zeros32).

Definition hcf5_X5a (L: hcf5_loc) (RAW: list byte) (H: handshake) (QPUB PSK: list byte) : mpred :=
  @data_at HCS Tsh t_mident (mident_val (mident_of x25519 RAW)) (l_id L) * hbytes Tsh RAW (l_raw L) *
  hout Tsh 32 (l_dh L) * @data_at_ HCS Tsh t_hsnap (l_hq L) *
  hs_mem false Tsh (l_q L) (hcf5_qpeer H) * @data_at_ Noise.CS Tsh t_cookie (cookie_addr (l_q L)) *
  hcf5_qrest (l_q L) * hbytes Tsh QPUB (l_qpub L) * hbytes Tsh PSK (l_psk L).

(* hq = the snapshot of q's handshake; q's cookie: any (X5b) or wg_cookie_init's (X5) *)
Definition hcf5_X5b (L: hcf5_loc) (RAW: list byte) (H: handshake) (T: tstate) : mpred :=
  @data_at HCS Tsh t_mident (mident_val (mident_of x25519 RAW)) (l_id L) * hbytes Tsh RAW (l_raw L) *
  hout Tsh 32 (l_dh L) * @data_at HCS Tsh t_hsnap (hsnap_val (hs_snap_cur T (l_q L) (hcf5_qpeer H))) (l_hq L) *
  hs_mem false Tsh (l_q L) (hcf5_qpeer H) * @data_at_ Noise.CS Tsh t_cookie (cookie_addr (l_q L)) *
  hcf5_qrest (l_q L) * hout Tsh 32 (l_qpub L) * hout Tsh 32 (l_psk L).

Definition hcf5_X5 (L: hcf5_loc) (RAW: list byte) (H: handshake) (T: tstate) : mpred :=
  @data_at HCS Tsh t_mident (mident_val (mident_of x25519 RAW)) (l_id L) * hbytes Tsh RAW (l_raw L) *
  hout Tsh 32 (l_dh L) * @data_at HCS Tsh t_hsnap (hsnap_val (hs_snap_cur T (l_q L) (hcf5_qpeer H))) (l_hq L) *
  hs_mem false Tsh (l_q L) (hcf5_qpeer H) * cookie_rep Tsh (cookie_addr (l_q L)) cookie_zero *
  hcf5_qrest (l_q L) * hout Tsh 32 (l_qpub L) * hout Tsh 32 (l_psk L).

(* after the prologue: the stack frame converted, the initial globals (the shim with the v3 predicate: PA1
   introduces the warnings with prot_repr4's shim_state_ex4) *)
Definition hcf5_S0 (gv: globals) (L: hcf5_loc) (FR: mpred) : environ -> mpred :=
  PROPx []
  (LOCALx (hcf5_lvars gv L)
  (SEPx ([@data_at_ Noise.CS Tsh t_dev (l_w L); @data_at_ Noise.CS Tsh t_itab (l_it L);
          @data_at_ Noise.CS Tsh t_ptab (l_pt L); @data_at_ Noise.CS Tsh t_peer (l_p L);
          hout Tsh 32 (l_raw0 L); hout Tsh 32 (l_pub L);
          mem_mgr gv; shim_state gv hcf5_shim0; noise_globals_raw gv zeros32 zeros32 Int64.zero;
          wg_consts gv; hcf5_consts gv; FR] ++ hcf5_pre L ++ [hcf5_X0 L]))).

(* after PA1 (0..5): w set up (setup_device), p set up (setup_peer), its entry outside the table *)
Definition hcf5_SA1 (gv: globals) (L: hcf5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcf5_run, EX S: shim, EX w: list int64,
  PROPx [hcf5_run_ok R; s_boot S = r_now R; Zlength w = 5]
  (LOCALx (temp HF._now (Vlong (r_now R)) :: hcf5_lvars gv L)
  (SEPx ([device_rep Tsh (l_w L) (hcf5_D0 R L); itable Tsh (l_it L) (mkT [] []); ptable Tsh (l_pt L) (l_p L);
          peer_rep Tsh (l_p L) (hcf5_P0 R L); entry_out Tsh (hs_addr (l_p L)) (mkEntry (l_p L) IDX_HANDSHAKE Int.zero);
          hbytes Tsh (r_raw0 R) (l_raw0 L); hbytes Tsh (r_pub R) (l_pub L)] ++
         hcf5_globs gv S w FR ++ hcf5_pre L ++ [hcf5_X0 L]))).

(* after PA2 (6..16): ANY prior contents of w's identity and checker keys, of p's precomputed DH, cookie keys,
   handshake (hs_randomize) and rest (peer_randomize_rest); p's entry in the pool, hashed or not *)
Definition hcf5_SA (gv: globals) (L: hcf5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcf5_run, EX S: shim, EX w: list int64, EX D: device, EX P: peer, EX T: tstate,
  PROPx [hcf5_run_ok R; s_boot S = r_now R; Zlength w = 5; hcf5_dok L D; hcf5_pok R L P;
         p_cur P = nullval /\ p_prev P = nullval /\ p_next P = nullval; hcf5_T_ok L [] false T]
  (LOCALx (temp HF._now (Vlong (r_now R)) :: hcf5_lvars gv L)
  (SEPx ([device_rep Tsh (l_w L) D; itable Tsh (l_it L) T; ptable Tsh (l_pt L) (l_p L); peer_rep Tsh (l_p L) P;
          hbytes Tsh (r_raw0 R) (l_raw0 L); hbytes Tsh (r_pub R) (l_pub L)] ++
         hcf5_globs gv S w FR ++ hcf5_pre L ++ [hcf5_X0 L]))).

(* after PK (17): the kents KE of p (no snapshot yet), kes = their head *)
Definition hcf5_SK (gv: globals) (L: hcf5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcf5_run, EX S: shim, EX w: list int64, EX D: device, EX P: peer, EX T: tstate, EX KE: list kent4,
  PROPx [hcf5_run_ok R; s_boot S = r_now R; Zlength w = 5; hcf5_dok L D; hcf5_pok R L P; hcf5_slots_ok KE P;
         hcf5_T_ok L KE false T]
  (LOCALx (temp HF._kes (hcf5_khead KE) :: temp HF._now (Vlong (r_now R)) :: hcf5_lvars gv L)
  (SEPx ([device_rep Tsh (l_w L) D; itable Tsh (l_it L) T; ptable Tsh (l_pt L) (l_p L); peer_rep Tsh (l_p L) P;
          kents_rep W (hcf5_khead KE) KE;
          hbytes Tsh (r_raw0 R) (l_raw0 L); hbytes Tsh (r_pub R) (l_pub L)] ++
         hcf5_globs gv S w FR ++ hcf5_pre L ++ [hcf5_X0 L]))).

(* after PS (18..24): the snapshots taken *)
Definition hcf5_SX0 (gv: globals) (L: hcf5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcf5_run, EX S: shim, EX w: list int64, EX D: device, EX P: peer, EX T: tstate, EX KE: list kent4,
  EX D0: device, EX sn0: hsnap, EX P0: peer, EX r0: int, EX S0: shim, EX w0: list int64, EX h0: val,
  hcf5_F gv L FR True (hcf5_X0 L) R S w D P T KE false D0 sn0 P0 r0 S0 w0 h0.

(* steps 1..4 (and their CHECKs): the identity of RAW *)
Definition hcf5_SX1 (gv: globals) (L: hcf5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcf5_run, EX S: shim, EX w: list int64, EX D: device, EX P: peer, EX T: tstate, EX KE: list kent4,
  EX D0: device, EX sn0: hsnap, EX P0: peer, EX r0: int, EX S0: shim, EX w0: list int64, EX h0: val,
  EX RAW: list byte,
  hcf5_F gv L FR (hcf5_Px1 D RAW) (hcf5_X1 L RAW) R S w D P T KE false D0 sn0 P0 r0 S0 w0 h0.

(* after P5a (43..56): q's handshake initialised (its entry joined the pool), use_psk = ub *)
Definition hcf5_S5a (gv: globals) (L: hcf5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcf5_run, EX S: shim, EX w: list int64, EX D: device, EX P: peer, EX T: tstate, EX KE: list kent4,
  EX D0: device, EX sn0: hsnap, EX P0: peer, EX r0: int, EX S0: shim, EX w0: list int64, EX h0: val,
  EX RAW: list byte, EX QPUB: list byte, EX PSK: list byte, EX ub: bool,
  hcf5_Fx gv L FR [temp HF._use_psk (Vint (if ub then Int.one else Int.zero))]
    (hcf5_Px1 D RAW /\ Zlength QPUB = 32 /\ Zlength PSK = 32)
    (hcf5_X5a L RAW (hcf5_qhs D L QPUB PSK ub) QPUB PSK) R S w D P T KE true D0 sn0 P0 r0 S0 w0 h0.

(* after P5b (57..74): hq = q's handshake's snapshot (the CHECK passed) *)
Definition hcf5_S5b (gv: globals) (L: hcf5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcf5_run, EX S: shim, EX w: list int64, EX D: device, EX P: peer, EX T: tstate, EX KE: list kent4,
  EX D0: device, EX sn0: hsnap, EX P0: peer, EX r0: int, EX S0: shim, EX w0: list int64, EX h0: val,
  EX RAW: list byte, EX H: handshake,
  hcf5_F gv L FR (hcf5_Px1 D RAW /\ hcf5_qok L H) (hcf5_X5b L RAW H T) R S w D P T KE true D0 sn0 P0 r0 S0 w0 h0.

(* after P5c (75..84), step 6 and the CHECKs C5, C6: q's cookie zero *)
Definition hcf5_SX5 (gv: globals) (L: hcf5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcf5_run, EX S: shim, EX w: list int64, EX D: device, EX P: peer, EX T: tstate, EX KE: list kent4,
  EX D0: device, EX sn0: hsnap, EX P0: peer, EX r0: int, EX S0: shim, EX w0: list int64, EX h0: val,
  EX RAW: list byte, EX H: handshake,
  hcf5_F gv L FR (hcf5_Px1 D RAW /\ hcf5_qok L H) (hcf5_X5 L RAW H T) R S w D P T KE true D0 sn0 P0 r0 S0 w0 h0.

End States.

(* main's post (TT) weakened to the canonical form forward needs for a return *)
Lemma hcf5_post_canon {Espec: OracleKind} {cs: compspecs} Delta P c Q gv F :
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (PROP () LOCAL () SEP (TT))) F)) ->
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (hcf5_post gv)) F)).
Proof.
  intros H. eapply semax_post; [| | | | apply H]; intros; simpl; intros rho; apply andp_left2;
    try apply derives_refl.
  apply sepcon_derives; [| apply derives_refl]. revert rho. apply bind_ret_derives. intros rho. apply TT_right.
Qed.
