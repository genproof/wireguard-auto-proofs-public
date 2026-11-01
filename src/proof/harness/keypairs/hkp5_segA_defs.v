(* law keypairs, prologue A: the cut of main's statements 0..28 and the
   states between the pieces.

   Pieces (all in main's prologue context hkp5_Delta (hkp5_G_A x25519)):
     A1  = 0..14   next_id, id_known, the harness's globals, m_warn loop, others = NULL, now, wg_noise_init, raw, pub,
                   setup_device, setup_peer(&p, &w, pub, NULL, 1), peer_randomize_rest(&p)      hkp5_P0 -> hkp5A_S2
     A2a = 15..16  n = draw_steps(); the loop adding the other peers (bytes_eq, hnodes_add)    hkp5A_S2 -> hkp5A_S2
     A2b = 17      the loop randomizing them (hs_randomize, peer_randomize_rest, maybe insert)  hkp5A_S2 -> hkp5A_S2
     A3a = 18      kes = kents_add(&t, others, NULL, 1)                                        hkp5A_S2 -> hkp5A_SK
     A3b = 19..20  hnodes_snap(others); kents_snap(kes)                                         hkp5A_SK -> hkp5A_S3
     A4  = 21..28  hs_take(&hsm), pr_take(&prm), prefs, dev_take(&dsm), allocs0, frees0, warn0, steps
                                                                                                hkp5A_S3 -> hkp5A_S4
     pure          hkp5A_inv -> hkp5_fix_ok / hkp5_inv / hkp5_oth_ok of the loop's entry (hkp5A_V / _Y / _O)
   The glue (hkp5_segA.v) composes them and weakens hkp5A_S4 to hkp5_PA.

   The invariant hkp5A_inv of the prologue: P (main's peer p) as setup_peer made it (slots and public-key link
   NULL, its handshake entry in the pool with share Tsh, index 0); the other peers PS (the node list NS, same
   order) with their properties; the kents KE (their addresses ka); the table's pool = the kents' entries, then the
   other peers' handshake entries, then P's entry; indices of the hashed entries unique. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.keypairs.hkp5_op1.
Require Export WgNoise.proof.harness.keypairs.hkp5_spec.

Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The cut                                                                 *)
(* ---------------------------------------------------------------------- *)

Definition hkp5A_s1 := ltac:(let x := eval cbv beta iota delta [hkp5_l hkp5_seql firstn skipn hkp5_stmts] in (hkp5_seql (hkp5_l 0 15)) in exact x).
Definition hkp5A_s2a := ltac:(let x := eval cbv beta iota delta [hkp5_l hkp5_seql firstn skipn hkp5_stmts] in (hkp5_seql (hkp5_l 15 2)) in exact x).
Definition hkp5A_s2b := ltac:(let x := eval cbv beta iota delta [hkp5_l hkp5_seql firstn skipn hkp5_stmts] in (hkp5_seql (hkp5_l 17 1)) in exact x).
Definition hkp5A_s3a := ltac:(let x := eval cbv beta iota delta [hkp5_l hkp5_seql firstn skipn hkp5_stmts] in (hkp5_seql (hkp5_l 18 1)) in exact x).
Definition hkp5A_s3b := ltac:(let x := eval cbv beta iota delta [hkp5_l hkp5_seql firstn skipn hkp5_stmts] in (hkp5_seql (hkp5_l 19 2)) in exact x).
Definition hkp5A_s4 := ltac:(let x := eval cbv beta iota delta [hkp5_l hkp5_seql firstn skipn hkp5_stmts] in (hkp5_seql (hkp5_l 21 8)) in exact x).

Lemma hkp5A_cut_eq :
  hkp5_l 0 29 = hkp5_l 0 15 ++ hkp5_l 15 2 ++ hkp5_l 17 1 ++ hkp5_l 18 1 ++ hkp5_l 19 2 ++ hkp5_l 21 8.
Proof. reflexivity. Qed.

Lemma hkp5A_s_eq :
  hkp5A_s1 = hkp5_seql (hkp5_l 0 15) /\ hkp5A_s2a = hkp5_seql (hkp5_l 15 2) /\
  hkp5A_s2b = hkp5_seql (hkp5_l 17 1) /\ hkp5A_s3a = hkp5_seql (hkp5_l 18 1) /\
  hkp5A_s3b = hkp5_seql (hkp5_l 19 2) /\ hkp5A_s4 = hkp5_seql (hkp5_l 21 8).
Proof. repeat split. Qed.

(* ---------------------------------------------------------------------- *)
(* The prologue's values and invariant                                     *)
(* ---------------------------------------------------------------------- *)

(* the draws of the setup: the device's raw key, P's public key, the cookie secret, the boot clock (now) *)
Record hkp5A_run := mkRA5 { a_RAW: list byte; a_PUB: list byte; a_sec: list byte; a_boot: int64 }.

Definition hkp5A_run_ok (R: hkp5A_run) : Prop :=
  Zlength (a_RAW R) = 32 /\ Zlength (a_PUB R) = 32 /\ Zlength (a_sec R) = 32 /\
  0 <= Int64.unsigned (a_boot R) < 2 ^ 62.

(* P's handshake entry as setup_peer made it (the table's first pool item, share Tsh) *)
Definition hkp5A_T1 (p: val) : tstate := t_add (mkT [] []) (hs_addr p) Tsh (mkEntry p IDX_HANDSHAKE Int.zero).

(* the heads of the node list and of the kent list *)
Definition hkp5A_nhead (NS: list hnode4) : val := match NS with [] => nullval | N :: _ => hn_addr N end.
Definition hkp5A_khead (KE: list kent4) : val := match KE with [] => nullval | e :: _ => ke_addr e end.

(* the shares: the other peers Ews, every pool item but P's entry Ews *)
Definition hkp5A_sh (F: hkp5_fix) (PS: list (val * share * peer)) (T: tstate) : Prop :=
  Forall (fun x => match x with (_, sh, _) => sh = Ews end) PS /\
  Forall (fun d => match d with (a, sh, _) => a = hs_addr (f_p F) \/ sh = Ews end) (t_D T).

Definition hkp5A_inv (F: hkp5_fix) (P: peer) (NS: list hnode4) (PS: list (val * share * peer)) (KE: list kent4)
  (T: tstate) (head: val) : Prop :=
  let p := f_p F in let pa := map peer_addr4 PS in let ka := map ke_addr KE in
  isptr p /\
  p_device P = f_w F /\ hs_sid (p_hs P) = id_addr (f_w F) /\
  p_cur P = nullval /\ p_prev P = nullval /\ p_next P = nullval /\ p_pknext P = nullval /\
  hnodes_peers4 NS PS /\ peers_wf PS /\ NoDup (p :: pa) /\ Forall isptr pa /\ Forall isptr ka /\
  Forall (fun x => match x with (q, _, Q) =>
     p_device Q = f_w F /\ hs_sid (p_hs Q) = id_addr (f_w F) /\ 0 < Int.unsigned (p_refs Q) < 2147483647 /\
     Forall (vp_ok ka) [p_cur Q; p_prev Q; p_next Q] /\ vp_ok (p :: pa) (p_pknext Q) end) PS /\
  (head = p \/ In head pa) /\
  saddrs (t_D T) = ka ++ map hs_addr pa ++ [hs_addr p] /\
  sfind (t_D T) (hs_addr p) = Some (Tsh, mkEntry p IDX_HANDSHAKE Int.zero) /\
  Forall (fun q => e_peer (t_entry_d T (hs_addr q)) = q /\ e_type (t_entry_d T (hs_addr q)) = IDX_HANDSHAKE) pa /\
  Forall (fun e => In (e_peer (t_entry_d T (ke_addr e))) pa) KE /\
  NoDup (t_indices T (t_L T)) /\ hkp5A_sh F PS T.

(* the harness's model at the start: no node, NULL slots, no free, no warning *)
Definition hkp5A_H0 : hk5_state := mkH5 [] nullval nullval nullval Int64.zero (Zrepeat Int64.zero 5).

(* the values of the loop's entry *)
Definition hkp5A_OD (p: val) (T: tstate) : list (val * share * entry) :=
  filter (fun d => negb (hk5_eqb (fst (fst d)) (hs_addr p))) (t_D T).

Definition hkp5A_V (F: hkp5_fix) (R: hkp5A_run) (S: shim) (w: list int64) (P: peer) (T: tstate) (head: val)
  : hkp5_val :=
  mkKV5 (a_RAW R) (a_PUB R) (a_sec R) (a_boot R) (s_allocs S) (s_frees S) w (hkp5A_OD (f_p F) T) (t_L T) head
        (p_refs P).

Definition hkp5A_Y (F: hkp5_fix) (R: hkp5A_run) (S: shim) (w: list int64) (P: peer) (T: tstate) : hkp5_dyn :=
  mkKY5 S w Int64.zero P [] T hkp5A_H0 (a_boot R) Int64.zero false (hs_snap_cur T (f_p F) P).

Definition hkp5A_O (NS: list hnode4) (PS: list (val * share * peer)) (KE: list kent4) (T: tstate) : hkp5_oth :=
  mkOth5 (hkp5A_nhead NS) (hnodes_snapped4 T NS PS) PS (hkp5A_khead KE) (map (kent_snapped T) KE) T.

(* the pure part of the loop's entry (child "pure") *)
Definition hkp5A_pure_stmt : Prop :=
  forall F R S w P NS PS KE T head,
  hkp5A_run_ok R -> Zlength w = 5 -> itable_wf T -> hkp5A_inv F P NS PS KE T head ->
  hkp5_fix_ok F (hkp5A_V F R S w P T head) /\
  hkp5_inv F (hkp5A_V F R S w P T head) (hkp5A_Y F R S w P T) /\
  hkp5_oth_ok F (hkp5A_V F R S w P T head) (hkp5A_O NS PS KE T).

(* ---------------------------------------------------------------------- *)
(* The states                                                              *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.
#[local] Existing Instance W_keypairs.

(* the device as setup_device made it *)
Definition hkp5A_D (F: hkp5_fix) (R: hkp5A_run) : device :=
  setup_dev x25519 (f_w F) (f_t F) (f_pt F) (a_RAW R) (a_sec R) (a_boot R).

(* the temps fixed by A1 *)
Definition hkp5A_temps (R: hkp5A_run) : list localdef :=
  [temp KC._now (Vlong (a_boot R)); temp KC._next_id (Vlong Int64.zero); temp KC._id_known (Vint Int.zero)].

(* main's locals and the kernel's objects (hkp5_world's shape, keypairs_rep [] omitted) *)
Definition hkp5A_world (F: hkp5_fix) (R: hkp5A_run) (P: peer) (T: tstate) (head: val) : list mpred :=
  [device_rep Tsh (f_w F) (hkp5A_D F R); itable Tsh (f_t F) T; ptable Tsh (f_pt F) head;
   peer_rep Tsh (f_p F) P; hbytes Tsh (a_RAW R) (f_raw F); hbytes Tsh (a_PUB R) (f_pub F);
   @data_at_ HCS Tsh t_hsnap (f_snap F); hout Tsh 32 (f_opub F); hout Tsh 32 (f_first F);
   hout Tsh 32 (f_second F)].

(* the snapshot globals before A4 (as in hkp5_P0) *)
Definition hkp5A_snaps0 (F: hkp5_fix) : list mpred :=
  [data_at_ Ews (Tstruct KC._hs_snap noattr) (f_gv F KC._hsm);
   data_at_ Ews (Tstruct KC._pr_snap noattr) (f_gv F KC._prm);
   data_at_ Ews (tarray tulong 5) (f_gv F KC._warn0);
   data_at_ Ews tuint (f_gv F KC._prefs);
   data_at_ Ews (Tstruct KC._dev_snap noattr) (f_gv F KC._dsm)].

(* the snapshot globals after A4 (hkp5_hglobs and dsm of hkp5_oth_rep) *)
Definition hkp5A_snaps (F: hkp5_fix) (R: hkp5A_run) (w: list int64) (P: peer) (T: tstate) (head: val)
  : list mpred :=
  [@data_at HCS Ews t_hsnap (hsnap_val (hs_snap_cur T (f_p F) P)) (f_gv F KC._hsm);
   data_at Ews (Tstruct KC._pr_snap noattr) (hk5_prsnap_val P) (f_gv F KC._prm);
   hk5_warr Ews w (f_gv F KC._warn0);
   data_at Ews tuint (Vint (p_refs P)) (f_gv F KC._prefs);
   @data_at CKS Ews t_devsnap (devsnap_val (hkp5A_D F R) head) (f_gv F KC._dsm)].

(* the other peers: the global others (head hd), the nodes NS, the peers PS *)
Definition hkp5A_oth (F: hkp5_fix) (hd: val) (NS: list hnode4) (PS: list (val * share * peer)) : list mpred :=
  [data_at Ews (tptr t_hnode4) hd (f_gv F KC._others); hnodes_rep4 W_keypairs hd NS; peers_rep PS].

(* the kents: the global kes (head kd), the kents KE *)
Definition hkp5A_kes (F: hkp5_fix) (kd: val) (KE: list kent4) : list mpred :=
  [data_at Ews (tptr t_kent) kd (f_gv F KC._kes); kents_rep W_keypairs kd KE].

Definition hkp5A_globs (gv: globals) (S: shim) (w: list int64) : list mpred :=
  [shim_state4 gv S w; noise_globals gv Int64.zero; wg_consts gv; mem_mgr gv].

(* after A1, A2a, A2b: P set up; the other peers added (randomized, entries hashed or not); no kent yet *)
Definition hkp5A_S2 (F: hkp5_fix) (FR: mpred) : environ -> mpred :=
  EX R: hkp5A_run, EX P: peer, EX S: shim, EX w: list int64, EX NS: list hnode4,
  EX PS: list (val * share * peer), EX T: tstate, EX head: val,
  PROPx [hkp5A_run_ok R; Zlength w = 5; hkp5A_inv F P NS PS [] T head]
  (LOCALx (hkp5A_temps R ++ hkp5_lvars F)
  (SEPx (hkp5A_world F R P T head ++ hk5_items (f_gv F) hkp5A_H0 ++ hkp5A_snaps0 F ++
         hkp5A_oth F (hkp5A_nhead NS) NS PS ++
         [data_at_ Ews (tptr (Tstruct KC._kent noattr)) (f_gv F KC._kes)] ++
         hkp5A_globs (f_gv F) S w ++ [FR]))).

(* after A3a: the kents *)
Definition hkp5A_SK (F: hkp5_fix) (FR: mpred) : environ -> mpred :=
  EX R: hkp5A_run, EX P: peer, EX S: shim, EX w: list int64, EX NS: list hnode4,
  EX PS: list (val * share * peer), EX KE: list kent4, EX T: tstate, EX head: val,
  PROPx [hkp5A_run_ok R; Zlength w = 5; hkp5A_inv F P NS PS KE T head]
  (LOCALx (hkp5A_temps R ++ hkp5_lvars F)
  (SEPx (hkp5A_world F R P T head ++ hk5_items (f_gv F) hkp5A_H0 ++ hkp5A_snaps0 F ++
         hkp5A_oth F (hkp5A_nhead NS) NS PS ++ hkp5A_kes F (hkp5A_khead KE) KE ++
         hkp5A_globs (f_gv F) S w ++ [FR]))).

(* after A3b: the nodes and the kents hold their snapshots *)
Definition hkp5A_S3 (F: hkp5_fix) (FR: mpred) : environ -> mpred :=
  EX R: hkp5A_run, EX P: peer, EX S: shim, EX w: list int64, EX NS: list hnode4,
  EX PS: list (val * share * peer), EX KE: list kent4, EX T: tstate, EX head: val,
  PROPx [hkp5A_run_ok R; Zlength w = 5; hkp5A_inv F P NS PS KE T head]
  (LOCALx (hkp5A_temps R ++ hkp5_lvars F)
  (SEPx (hkp5A_world F R P T head ++ hk5_items (f_gv F) hkp5A_H0 ++ hkp5A_snaps0 F ++
         hkp5A_oth F (hkp5A_nhead NS) (hnodes_snapped4 T NS PS) PS ++
         hkp5A_kes F (hkp5A_khead KE) (map (kent_snapped T) KE) ++
         hkp5A_globs (f_gv F) S w ++ [FR]))).

(* after A4: the snapshots of P, its count, the warnings, the device; allocs0, frees0, steps *)
Definition hkp5A_S4 (F: hkp5_fix) (FR: mpred) : environ -> mpred :=
  EX R: hkp5A_run, EX P: peer, EX S: shim, EX w: list int64, EX NS: list hnode4,
  EX PS: list (val * share * peer), EX KE: list kent4, EX T: tstate, EX head: val, EX steps: Z,
  PROPx [hkp5A_run_ok R; Zlength w = 5; hkp5A_inv F P NS PS KE T head; 0 <= steps <= Int64.max_unsigned]
  (LOCALx ([temp KC._steps (Vlong (Int64.repr steps)); temp KC._allocs0 (Vlong (s_allocs S));
            temp KC._frees0 (Vlong (s_frees S))] ++ hkp5A_temps R ++ hkp5_lvars F)
  (SEPx (hkp5A_world F R P T head ++ hk5_items (f_gv F) hkp5A_H0 ++ hkp5A_snaps F R w P T head ++
         hkp5A_oth F (hkp5A_nhead NS) (hnodes_snapped4 T NS PS) PS ++
         hkp5A_kes F (hkp5A_khead KE) (map (kent_snapped T) KE) ++
         hkp5A_globs (f_gv F) S w ++ [FR]))).

End States.
