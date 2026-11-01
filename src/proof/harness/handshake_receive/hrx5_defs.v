(* law handshake_receive: main's context and the states
   between its phases.

   Conventions (all phases):
   - main runs in the world compspecs W := W_handshake_receive (Delta hrx5_Delta).  The SEP items are kept in the
     compspecs of the specifications that consume them: protocol objects through prot_repr3's predicates
     (device_rep, peers_rep, itable, ptable, init_rep, resp_rep, cmsg_rep, skb_rep, bytes_at), the shim with EXACT
     warnings (shim_state4 gv S w), the structs dev_snap / shim_snap / skb_snap as `@data_at(_) CKS`, the
     harness structs m_identity / m_consumed_initiation / m_state as `@data_at(_) HCS`, the receive.c globals as
     hrx5_spec.v's lul_rep / qlen_rep / rxlog_rep (HRX), the local `peers` as `@data_at W`, the node list as
     `hnodes_rep4 W`, the kents as `kents_rep W`, byte buffers as hbytes / hout (HCS), malloc tokens at W.
   - main = 24 statements (hrx5_cut.v): PA 0..13, PB 14, PC 15..16, PD 17, PE 18..19, PL 20 (the packet loop:
     i = 0; for (; i < steps; i++) BODY, BODY = B1 .. B9), PZ 21..23.
   - The states: hrx5_S0 (prologue), hrx5_SA (after PA), hrx5_SB (after PB, PC and PD: the setup invariant with
     K's node nk), hrx5_SE (after PE: the kents, steps), hrx5_SL (the loop invariant, before the guard), hrx5_SX
     (the loop's exit), and in the body: hrx5_S1 .. hrx5_S6, hrx5_S8, hrx5_SC (the end of the body = the target of
     `continue`, before i++).  B7 goes from hrx5_S6 to hrx5_S6 (two CHECKs).
   - The peers PS (public-key chain order = the node list's order), the nodes NS, the kents KE; the index table's
     pool = the kents' entries then the peers' handshake entries (hrx5cr_pool, hrx5_mcr.v); every peer satisfies
     hrx5_pok (device, static identity, lengths, the precomputed static-static of D's identity, 1 .. INT_MAX - 1
     references, last consumption below 2^62, empty keypair slots).
   - D = hrx5_D R wd itd ptd sec birth (setup_device's device with ANY cookie secret sec and birthdate birth);
     the loop's world before dispatch is hrx5_W0 D T PS S w kc lul (no slot keypair, the log reset), after it
     rx_model ... (hrx5_model.v), with the draws d existential.
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
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_cut.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mspec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require WgNoise.contracts.x_handshake_receive.
Require WgNoise.harness.x_handshake_receive.code.
Local Open Scope logic.

Module HM := WgNoise.harness.x_handshake_receive.code.

Notation W := W_handshake_receive.

(* ---------------------------------------------------------------------- *)
(* main's context                                                          *)
(* ---------------------------------------------------------------------- *)

Section Defs.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* the hypotheses of the phase lemmas (the representation lemmas: prot_rep_lemmas3, proved, Require it) *)
Definition hrx5_hyps : Prop :=
  x25519_props x25519 /\ aead_props aead_enc aead_dec /\ xaead_props xaead_enc xaead_dec.

Definition hrx5_Gprog : funspecs := hrx5_mimports x25519 aead_dec xaead_enc xaead_dec W ++ hrx5_G.
Definition hrx5_Delta : tycontext := func_tycontext HM.f_main hrx5_V hrx5_Gprog [].

End Defs.

Definition hrx5_R (gv: globals) : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (hrx5_post gv)) (@stackframe_of W HM.f_main).

(* ---------------------------------------------------------------------- *)
(* The locals and the globals                                              *)
(* ---------------------------------------------------------------------- *)

(* the addresses of main's 26 local variables *)
Record hrx5_loc := mkLocR5 {
  l_wd: val; l_itd: val; l_ptd: val; l_id: val; l_ik: val; l_rawd: val; l_rawk: val; l_pub: val; l_mk1: val;
  l_ssk: val; l_peers: val; l_ds: val; l_ss: val; l_sks: val; l_skb: val; l_ci: val; l_st: val; l_secret: val;
  l_c: val; l_mac: val; l_pt: val; l_t: val; l_t1: val; l_ck: val; l_sst: val; l_before: val }.

Definition hrx5_lvars (gv: globals) (L: hrx5_loc) : list localdef :=
  [lvar HM._wd t_dev (l_wd L); lvar HM._itd t_itab (l_itd L); lvar HM._ptd t_ptab (l_ptd L);
   lvar HM._id t_mident (l_id L); lvar HM._ik t_mident (l_ik L);
   lvar HM._raw_d (tarray tuchar 32) (l_rawd L); lvar HM._raw_k (tarray tuchar 32) (l_rawk L);
   lvar HM._pub (tarray tuchar 32) (l_pub L); lvar HM._mk1 (tarray tuchar 32) (l_mk1 L);
   lvar HM._ss_k (tarray tuchar 32) (l_ssk L); lvar HM._peers (tptr t_hnode4) (l_peers L);
   lvar HM._ds t_devsnap (l_ds L); lvar HM._ss t_shimsnap (l_ss L); lvar HM._sks t_skbsnap (l_sks L);
   lvar HM._skb t_skb (l_skb L); lvar HM._ci t_mcinit (l_ci L); lvar HM._st t_mstate (l_st L);
   lvar HM._secret (tarray tuchar 32) (l_secret L); lvar HM._c (tarray tuchar 16) (l_c L);
   lvar HM._mac (tarray tuchar 16) (l_mac L); lvar HM._pt (tarray tuchar 16) (l_pt L);
   lvar HM._t t_init (l_t L); lvar HM._t__1 t_resp (l_t1 L); lvar HM._ck (tarray tuchar 16) (l_ck L);
   lvar HM._sst (tarray tuchar 32) (l_sst L); lvar HM._before t_mstate (l_before L);
   gvars gv].

(* the globals every state holds: allocator, shim (exact warnings), noise.c's globals (keypair_counter kc), the
   read-only tables, the harness's constants, the frame *)
Definition hrx5_globs (gv: globals) (S: shim) (w: list int64) (kc: int64) (FR: mpred) : list mpred :=
  [mem_mgr gv; shim_state4 gv S w; noise_globals gv kc; wg_consts gv; hrx5_consts gv; FR].

(* receive.c's globals between packets: last_under_load (= main's m_lul), the log and the queue length (any) *)
Definition hrx5_rglobs (gv: globals) (lul: int64) : list mpred :=
  [lul_rep gv lul; @data_at_ HRX Ews t_rxlog (gv HM._wg_shim_rx);
   @data_at_ HRX Ews tint (gv HM._wg_shim_handshake_queue_len)].

(* the scratch locals of the loop's body, any contents (skb is listed apart) *)
Definition hrx5_scr (L: hrx5_loc) : list mpred :=
  [hout Tsh 32 (l_pub L); @data_at_ CKS Tsh t_devsnap (l_ds L); @data_at_ CKS Tsh t_shimsnap (l_ss L);
   @data_at_ CKS Tsh t_skbsnap (l_sks L); @data_at_ HCS Tsh t_mcinit (l_ci L); @data_at_ HCS Tsh t_mstate (l_st L);
   hout Tsh 32 (l_secret L); hout Tsh 16 (l_c L); hout Tsh 16 (l_mac L); hout Tsh 16 (l_pt L);
   @data_at_ Noise.CS Tsh t_init (l_t L); @data_at_ Noise.CS Tsh t_resp (l_t1 L); hout Tsh 16 (l_ck L);
   hout Tsh 32 (l_sst L); @data_at_ HCS Tsh t_mstate (l_before L)].

(* the skb local before the packet: any contents *)
Definition hrx5_skb0 (L: hrx5_loc) : mpred := @data_at_ Cookie.CS Tsh t_skb (l_skb L).

(* the skb local with its protocol and source set (B2), data and len any *)
Definition hrx5_skb_part (L: hrx5_loc) (proto: Z) (ip4 ip6 port: list byte) : mpred :=
  !! (0 <= proto <= 65535 /\ Zlength ip4 = 4 /\ Zlength ip6 = 16 /\ Zlength port = 2) &&
  EX dv: val, EX lv: val,
    @data_at Cookie.CS Tsh t_skb (dv, (lv, (Vint (Int.repr proto), (bytes ip4, (bytes ip6, bytes port))))) (l_skb L).

(* the message object at skb->data and the image img (malloc'd, tokens at the world) *)
Definition obj_rep (dp: val) (o: hrx5_obj) : mpred :=
  match o with
  | OBuf b => @malloc_token W Ews (tarray tuchar (Zlength b)) dp * bytes_at Ews b dp
  | OInit M => @malloc_token W Ews t_init dp * init_rep Ews dp M
  | OResp M => @malloc_token W Ews t_resp dp * resp_rep Ews dp M
  | OCookie M => @malloc_token W Ews t_cmsg dp * cmsg_rep Ews dp M
  end.
Definition img_rep (img: val) (msg: list byte) : mpred :=
  @malloc_token W Ews (tarray tuchar (Zlength msg)) img * hbytes Ews msg img.

(* the skb of the packet *)
Definition hrx5_skb (dp: val) (o: hrx5_obj) (proto: Z) (ip4 ip6 port: list byte) : skb :=
  mkSkb dp (Int.repr (Zlength (obj_bytes o))) proto ip4 ip6 port.

(* the temps mi / mr / mc / buf after the packet: the object's pointer for its kind, NULL for the others *)
Definition hrx5_ptrs (dp: val) (o: hrx5_obj) : list localdef :=
  [temp HM._buf (match o with OBuf _ => dp | _ => nullval end);
   temp HM._mi (match o with OInit _ => dp | _ => nullval end);
   temp HM._mr (match o with OResp _ => dp | _ => nullval end);
   temp HM._mc (match o with OCookie _ => dp | _ => nullval end)].

(* ---------------------------------------------------------------------- *)
(* The invariants                                                          *)
(* ---------------------------------------------------------------------- *)

Section Inv.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* D at the locals L *)
Definition hrx5_DL (R: hrx5_run) (L: hrx5_loc) (sec: list byte) (birth: int64) : device :=
  hrx5_D x25519 R (l_wd L) (l_itd L) (l_ptd L) sec birth.

(* every peer of D *)
Definition hrx5_pok (R: hrx5_run) (L: hrx5_loc) (x: val * share * peer) : Prop :=
  match x with (a, sh, P) =>
    sh = Ews /\ p_device P = l_wd L /\ hs_sid (p_hs P) = id_addr (l_wd L) /\ hs_ok (p_hs P) /\
    hs_ss (p_hs P) = precomputed x25519 (hrx5_sid x25519 R) (hs_rstatic (p_hs P)) /\
    0 < Int.unsigned (p_refs P) < 2147483647 /\
    0 <= Int64.unsigned (hs_lic (p_hs P)) < 2 ^ 62 /\
    is_pointer_or_null (p_pknext P) /\
    p_cur P = nullval /\ p_prev P = nullval /\ p_next P = nullval
  end.

(* the lists: peers PS (chain from head), nodes NS (same peers, same order), kents KE, the table T (pool: the kents'
   entries, then the peers' handshake entries), nk = a node of the list (K's) or NULL *)
Definition hrx5_inv (R: hrx5_run) (L: hrx5_loc) (NS: list hnode4) (PS: list (val * share * peer))
  (KE: list kent4) (T: tstate) (head nk: val) : Prop :=
  Forall (hrx5_pok R L) PS /\ peers_wf PS /\ NoDup (map peer_addr4 PS) /\ pk_chain head PS /\
  hnodes_peers4 NS PS /\ (nk = nullval \/ In nk (map hn_addr NS)) /\ hrx5cr_pool (map ke_addr KE) PS T.

(* the pure facts of every state from SA on: the run, D's secret and birthdate, the clock *)
Definition hrx5_base_ok (R: hrx5_run) (sec: list byte) (birth: int64) (S: shim) : Prop :=
  hrx5_run_ok R /\ Zlength sec = 32 /\ 0 <= Int64.unsigned birth < 2 ^ 62 /\
  0 <= Int64.unsigned (s_boot S) < 2 ^ 62.

(* D's device and tables, with the peers (with hrx5_globs' shim and noise.c's globals and hrx5_rglobs' lul and
   log: rxw_rep of the world hrx5_W0) *)
Definition hrx5_wcore (R: hrx5_run) (L: hrx5_loc) (sec: list byte) (birth: int64) (T: tstate)
  (head: val) (PS: list (val * share * peer)) : list mpred :=
  [device_rep Tsh (l_wd L) (hrx5_DL R L sec birth); itable Tsh (l_itd L) T; ptable Tsh (l_ptd L) head;
   peers_rep PS].

(* the objects of main that live from the setup to the end (not in rxw_rep): the identities, the raw keys, mk1,
   ss_k, the local `peers`, the node list, the kents *)
Definition hrx5_rest (R: hrx5_run) (L: hrx5_loc) (NS: list hnode4) (KE: list kent4) : list mpred :=
  [@data_at HCS Tsh t_mident (mident_val (hrx5_ID x25519 R)) (l_id L);
   @data_at HCS Tsh t_mident (mident_val (hrx5_IK x25519 R)) (l_ik L);
   hbytes Tsh (rr_rawd R) (l_rawd L); hbytes Tsh (rr_rawk R) (l_rawk L);
   hbytes Tsh (hrx5_mk1 x25519 R) (l_mk1 L); hbytes Tsh (hrx5_ssk x25519 R) (l_ssk L);
   @data_at W Tsh (tptr t_hnode4) (hrx5_head NS) (l_peers L); hnodes_rep4 W (hrx5_head NS) NS;
   kents_rep W (hrx5_khead KE) KE].

(* the globals outside rxw_rep (after dispatch): allocator, read-only tables, the harness's constants, the frame *)
Definition hrx5_cglobs (gv: globals) (FR: mpred) : list mpred := [mem_mgr gv; wg_consts gv; hrx5_consts gv; FR].

(* the loop's temps that live across iterations *)
Definition hrx5_ltemps (nk: val) (KE: list kent4) (st i: Z) (S: shim) (lul: int64) : list localdef :=
  [temp HM._nk nk; temp HM._kes (hrx5_khead KE); temp HM._steps (Vlong (Int64.repr st));
   temp HM._i (Vlong (Int64.repr i)); temp HM._now (Vlong (s_boot S)); temp HM._m_lul (Vlong lul)].

(* ci / st / pt after the harness's model block (S4): on acceptance the model's values, else any *)
Definition hrx5_ci_rep (R: hrx5_run) (PS: list (val * share * peer)) (o: hrx5_obj) (now: int64) (ci: val)
  : mpred :=
  match o with
  | OInit M =>
      if hrx5_fwd (obj_bytes o) then
        match hrx5ci_tgt x25519 aead_dec (hrx5_ID x25519 R) PS M now with
        | Some (_, _, t, ck2, h2) =>
            EX key: list val, EX spub: list val,
              !! (Zlength key = 32 /\ Zlength spub = 32) &&
              @data_at HCS Tsh t_mcinit (mcinit_val ck2 h2 key spub (bytes t)) ci
        | None => @data_at_ HCS Tsh t_mcinit ci
        end
      else @data_at_ HCS Tsh t_mcinit ci
  | _ => @data_at_ HCS Tsh t_mcinit ci
  end.
Definition hrx5_st_rep (R: hrx5_run) (T: tstate) (PS: list (val * share * peer)) (o: hrx5_obj) (st: val) : mpred :=
  match o with
  | OResp M =>
      if hrx5_fwd (obj_bytes o) then
        match hrx5cr_tgt x25519 aead_dec (hrx5_ID x25519 R) T PS M with
        | Some (_, _, ck, h) => @data_at HCS Tsh t_mstate (mstate_val ck h) st
        | None => @data_at_ HCS Tsh t_mstate st
        end
      else @data_at_ HCS Tsh t_mstate st
  | _ => @data_at_ HCS Tsh t_mstate st
  end.
Definition hrx5_pt_rep (T: tstate) (PS: list (val * share * peer)) (o: hrx5_obj) (pt: val) : mpred :=
  match o with
  | OCookie M =>
      if hrx5_fwd (obj_bytes o) then
        match hrx5ck_tgt xaead_dec T PS M with
        | Some (_, _, p) => hbytes Tsh p pt
        | None => hout Tsh 16 pt
        end
      else hout Tsh 16 pt
  | _ => hout Tsh 16 pt
  end.

(* the scratch locals after the model block: ci, st, pt as computed, the others any *)
Definition hrx5_scr4 (R: hrx5_run) (L: hrx5_loc) (T: tstate) (PS: list (val * share * peer)) (o: hrx5_obj)
  (now: int64) : list mpred :=
  [hout Tsh 32 (l_pub L); @data_at_ CKS Tsh t_devsnap (l_ds L); @data_at_ CKS Tsh t_shimsnap (l_ss L);
   @data_at_ CKS Tsh t_skbsnap (l_sks L); hrx5_ci_rep R PS o now (l_ci L); hrx5_st_rep R T PS o (l_st L);
   hout Tsh 32 (l_secret L); hout Tsh 16 (l_c L); hout Tsh 16 (l_mac L); hrx5_pt_rep T PS o (l_pt L);
   @data_at_ Noise.CS Tsh t_init (l_t L); @data_at_ Noise.CS Tsh t_resp (l_t1 L); hout Tsh 16 (l_ck L);
   hout Tsh 32 (l_sst L); @data_at_ HCS Tsh t_mstate (l_before L)].

(* after dispatch (S5, S6): the snapshots ds (the device and the public-key table's head), ss, sks taken, secret
   = D's secret; ci, st, pt as computed *)
Definition hrx5_scr5 (R: hrx5_run) (L: hrx5_loc) (T: tstate) (PS: list (val * share * peer)) (o: hrx5_obj)
  (now: int64) (dsv: reptype t_devsnap) (S: shim) (w: list int64) (s: skb) (secv: mpred) : list mpred :=
  [hout Tsh 32 (l_pub L); @data_at CKS Tsh t_devsnap dsv (l_ds L);
   @data_at CKS Tsh t_shimsnap (shimsnap_val S w) (l_ss L); @data_at CKS Tsh t_skbsnap (skbsnap_val s) (l_sks L);
   hrx5_ci_rep R PS o now (l_ci L); hrx5_st_rep R T PS o (l_st L); secv; hout Tsh 16 (l_c L);
   hout Tsh 16 (l_mac L); hrx5_pt_rep T PS o (l_pt L); @data_at_ Noise.CS Tsh t_init (l_t L);
   @data_at_ Noise.CS Tsh t_resp (l_t1 L); hout Tsh 16 (l_ck L); hout Tsh 32 (l_sst L);
   @data_at_ HCS Tsh t_mstate (l_before L)].

End Inv.

(* ---------------------------------------------------------------------- *)
(* The states                                                              *)
(* ---------------------------------------------------------------------- *)

(* the shim's state at the start (all globals zero) *)
Definition hrx5_shim0 : shim :=
  mkShim Int64.zero Int64.zero Int64.zero zeros32 zeros32 Int.zero Int64.zero Int64.zero Int64.zero false
         Int64.zero false.

Section States.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* after the prologue: the stack frame converted, the initial globals (the shim with the v3 predicate: PA
   introduces the warnings with prot_repr4's shim_state_ex4) *)
Definition hrx5_S0 (gv: globals) (L: hrx5_loc) (FR: mpred) : environ -> mpred :=
  PROPx []
  (LOCALx (hrx5_lvars gv L)
  (SEPx ([@data_at_ Noise.CS Tsh t_dev (l_wd L); @data_at_ Noise.CS Tsh t_itab (l_itd L);
          @data_at_ Noise.CS Tsh t_ptab (l_ptd L);
          @data_at_ HCS Tsh t_mident (l_id L); @data_at_ HCS Tsh t_mident (l_ik L);
          hout Tsh 32 (l_rawd L); hout Tsh 32 (l_rawk L); hout Tsh 32 (l_mk1 L); hout Tsh 32 (l_ssk L);
          @data_at_ W Tsh (tptr t_hnode4) (l_peers L);
          mem_mgr gv; shim_state gv hrx5_shim0; noise_globals_raw gv zeros32 zeros32 Int64.zero;
          wg_consts gv; hrx5_consts gv; FR] ++ hrx5_rglobs gv Int64.zero ++ [hrx5_skb0 L] ++ hrx5_scr L))).

(* after PA: D set up with ANY cookie secret sec born at birth, the identities, mk1, ss_k; no peer yet *)
Definition hrx5_SA (gv: globals) (L: hrx5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hrx5_run, EX sec: list byte, EX birth: int64, EX S: shim, EX w: list int64,
  PROPx [hrx5_base_ok R sec birth S]
  (LOCALx ([temp HM._now (Vlong (s_boot S)); temp HM._m_lul (Vlong Int64.zero)] ++ hrx5_lvars gv L)
  (SEPx (hrx5_wcore x25519 R L sec birth (mkT [] []) nullval [] ++
         hrx5_rest x25519 R L [] [] ++ hrx5_globs gv S w Int64.zero FR ++
         hrx5_rglobs gv Int64.zero ++ [hrx5_skb0 L] ++ hrx5_scr L))).

(* after PB, PC and PD (the same invariant): K's node nk (or NULL), any number of other peers, randomized and their
   entries hashed or not after PD; no kents *)
Definition hrx5_SB (gv: globals) (L: hrx5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hrx5_run, EX sec: list byte, EX birth: int64, EX S: shim, EX w: list int64, EX NS: list hnode4,
  EX PS: list (val * share * peer), EX T: tstate, EX head: val, EX nk: val,
  PROPx [hrx5_base_ok R sec birth S; hrx5_inv x25519 R L NS PS [] T head nk]
  (LOCALx ([temp HM._nk nk; temp HM._now (Vlong (s_boot S)); temp HM._m_lul (Vlong Int64.zero)] ++
           hrx5_lvars gv L)
  (SEPx (hrx5_wcore x25519 R L sec birth T head PS ++
         hrx5_rest x25519 R L NS [] ++ hrx5_globs gv S w Int64.zero FR ++
         hrx5_rglobs gv Int64.zero ++ [hrx5_skb0 L] ++ hrx5_scr L))).

(* after PE: the kents KE (kents_add without fill), steps drawn *)
Definition hrx5_SE (gv: globals) (L: hrx5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hrx5_run, EX sec: list byte, EX birth: int64, EX S: shim, EX w: list int64, EX NS: list hnode4,
  EX PS: list (val * share * peer), EX T: tstate, EX head: val, EX nk: val, EX KE: list kent4, EX st: Z,
  PROPx [hrx5_base_ok R sec birth S; hrx5_inv x25519 R L NS PS KE T head nk; 0 <= st <= Int64.max_unsigned]
  (LOCALx ([temp HM._nk nk; temp HM._kes (hrx5_khead KE); temp HM._steps (Vlong (Int64.repr st));
            temp HM._now (Vlong (s_boot S)); temp HM._m_lul (Vlong Int64.zero)] ++ hrx5_lvars gv L)
  (SEPx (hrx5_wcore x25519 R L sec birth T head PS ++
         hrx5_rest x25519 R L NS KE ++ hrx5_globs gv S w Int64.zero FR ++
         hrx5_rglobs gv Int64.zero ++ [hrx5_skb0 L] ++ hrx5_scr L))).

(* the loop's state between packets, with the counter i and the condition on it (the loop invariant: i <= st;
   the end of the body: i < st; the exit: st <= i) *)
Definition hrx5_SLc (c: Z -> Z -> Prop) (gv: globals) (L: hrx5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hrx5_run, EX sec: list byte, EX birth: int64, EX S: shim, EX w: list int64, EX NS: list hnode4,
  EX PS: list (val * share * peer), EX T: tstate, EX head: val, EX nk: val, EX KE: list kent4, EX st: Z,
  EX i: Z, EX kc: int64, EX lul: int64,
  PROPx [hrx5_base_ok R sec birth S; hrx5_inv x25519 R L NS PS KE T head nk; 0 <= st <= Int64.max_unsigned;
         0 <= i <= st; c i st]
  (LOCALx (hrx5_ltemps nk KE st i S lul ++ hrx5_lvars gv L)
  (SEPx (hrx5_wcore x25519 R L sec birth T head PS ++
         hrx5_rest x25519 R L NS KE ++ hrx5_globs gv S w kc FR ++
         hrx5_rglobs gv lul ++ [hrx5_skb0 L] ++ hrx5_scr L))).

Definition hrx5_SL := hrx5_SLc (fun _ _ => True).
Definition hrx5_SC := hrx5_SLc (fun i st => i < st).
Definition hrx5_SX := hrx5_SLc (fun i st => st <= i).

(* the body's ret_assert: continue = the end of the body, break = the loop's exit, return = main's *)
Definition hrx5_RB (gv: globals) (L: hrx5_loc) (FR: mpred) : ret_assert :=
  loop1_ret_assert (hrx5_SC gv L FR) (overridePost (hrx5_SX gv L FR) (hrx5_R gv)).

(* after B1: the per-packet temps reset, the boot clock moved (any value below 2^62) *)
Definition hrx5_S1 (gv: globals) (L: hrx5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hrx5_run, EX sec: list byte, EX birth: int64, EX S: shim, EX w: list int64, EX NS: list hnode4,
  EX PS: list (val * share * peer), EX T: tstate, EX head: val, EX nk: val, EX KE: list kent4, EX st: Z,
  EX i: Z, EX kc: int64, EX lul: int64,
  PROPx [hrx5_base_ok R sec birth S; hrx5_inv x25519 R L NS PS KE T head nk; 0 <= st <= Int64.max_unsigned;
         0 <= i < st]
  (LOCALx (hrx5_ltemps nk KE st i S lul ++
           [temp HM._mi nullval; temp HM._mr nullval; temp HM._mc nullval; temp HM._buf nullval;
            temp HM._acc_init (Vint Int.zero); temp HM._acc_resp (Vint Int.zero); temp HM._target nullval] ++
           hrx5_lvars gv L)
  (SEPx (hrx5_wcore x25519 R L sec birth T head PS ++
         hrx5_rest x25519 R L NS KE ++ hrx5_globs gv S w kc FR ++
         hrx5_rglobs gv lul ++ [hrx5_skb0 L] ++ hrx5_scr L))).

(* after B2: the queue length q, the rate limiter's answer (in S), the skb's protocol and source *)
Definition hrx5_S2 (gv: globals) (L: hrx5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hrx5_run, EX sec: list byte, EX birth: int64, EX S: shim, EX w: list int64, EX NS: list hnode4,
  EX PS: list (val * share * peer), EX T: tstate, EX head: val, EX nk: val, EX KE: list kent4, EX st: Z,
  EX i: Z, EX kc: int64, EX lul: int64, EX q: int, EX proto: Z, EX ip4: list byte, EX ip6: list byte,
  EX port: list byte,
  PROPx [hrx5_base_ok R sec birth S; hrx5_inv x25519 R L NS PS KE T head nk; 0 <= st <= Int64.max_unsigned;
         0 <= i < st]
  (LOCALx (hrx5_ltemps nk KE st i S lul ++
           [temp HM._mi nullval; temp HM._mr nullval; temp HM._mc nullval; temp HM._buf nullval;
            temp HM._acc_init (Vint Int.zero); temp HM._acc_resp (Vint Int.zero); temp HM._target nullval] ++
           hrx5_lvars gv L)
  (SEPx (hrx5_wcore x25519 R L sec birth T head PS ++
         hrx5_rest x25519 R L NS KE ++ hrx5_globs gv S w kc FR ++
         [lul_rep gv lul; @data_at_ HRX Ews t_rxlog (gv HM._wg_shim_rx); qlen_rep gv q;
          hrx5_skb_part L proto ip4 ip6 port] ++ hrx5_scr L))).

(* after B3: the packet: its object o at dp (kind 0..3), the image img (a copy), skb.data = dp, skb.len = its
   length; the world may have changed (K's response: K's handshake waits for a response; a cookie reply: a peer's
   entry hashed and its have_sent_mac1 set): the invariant holds for the new one *)
Definition hrx5_S3 (gv: globals) (L: hrx5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hrx5_run, EX sec: list byte, EX birth: int64, EX S: shim, EX w: list int64, EX NS: list hnode4,
  EX PS: list (val * share * peer), EX T: tstate, EX head: val, EX nk: val, EX KE: list kent4, EX st: Z,
  EX i: Z, EX kc: int64, EX lul: int64, EX q: int, EX proto: Z, EX ip4: list byte, EX ip6: list byte,
  EX port: list byte, EX o: hrx5_obj, EX dp: val, EX img: val,
  PROPx [hrx5_base_ok R sec birth S; hrx5_inv x25519 R L NS PS KE T head nk; 0 <= st <= Int64.max_unsigned;
         0 <= i < st; obj_ok o; malloc_compatible (Zlength (obj_bytes o)) dp]
  (LOCALx (hrx5_ltemps nk KE st i S lul ++ hrx5_ptrs dp o ++
           [temp HM._img img; temp HM._len (Vlong (Int64.repr (Zlength (obj_bytes o))));
            temp HM._kind (Vint (Int.repr (obj_kind o)));
            temp HM._acc_init (Vint Int.zero); temp HM._acc_resp (Vint Int.zero); temp HM._target nullval] ++
           hrx5_lvars gv L)
  (SEPx (hrx5_wcore x25519 R L sec birth T head PS ++
         hrx5_rest x25519 R L NS KE ++ hrx5_globs gv S w kc FR ++
         [lul_rep gv lul; @data_at_ HRX Ews t_rxlog (gv HM._wg_shim_rx); qlen_rep gv q;
          skb_rep Tsh (l_skb L) (hrx5_skb dp o proto ip4 ip6 port); obj_rep dp o; img_rep img (obj_bytes o)] ++
         hrx5_scr L))).

(* after B4: tw, fwd; the nodes hold their peers' snapshots, the kents theirs (taken on T, PS); the harness's model
   block's results (hrx5_acc_ok) and ci / st / pt *)
Definition hrx5_S4 (gv: globals) (L: hrx5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hrx5_run, EX sec: list byte, EX birth: int64, EX S: shim, EX w: list int64, EX NS: list hnode4,
  EX PS: list (val * share * peer), EX T: tstate, EX head: val, EX nk: val, EX KE: list kent4, EX st: Z,
  EX i: Z, EX kc: int64, EX lul: int64, EX q: int, EX proto: Z, EX ip4: list byte, EX ip6: list byte,
  EX port: list byte, EX o: hrx5_obj, EX dp: val, EX img: val, EX tg: val, EX ai: Z, EX ar: Z,
  PROPx [hrx5_base_ok R sec birth S; hrx5_inv x25519 R L NS PS KE T head nk; 0 <= st <= Int64.max_unsigned;
         0 <= i < st; obj_ok o; malloc_compatible (Zlength (obj_bytes o)) dp;
         hrx5_acc_ok x25519 aead_dec xaead_dec R NS PS T o (s_boot S) tg ai ar]
  (LOCALx (hrx5_ltemps nk KE st i S lul ++ hrx5_ptrs dp o ++
           [temp HM._img img; temp HM._len (Vlong (Int64.repr (Zlength (obj_bytes o))));
            temp HM._kind (Vint (Int.repr (obj_kind o)));
            temp HM._tw (Vint (if Z.leb 4 (Zlength (obj_bytes o)) then hrx5_tw (obj_bytes o) else Int.zero));
            temp HM._fwd (Vint (if hrx5_fwd (obj_bytes o) then Int.one else Int.zero));
            temp HM._acc_init (Vint (Int.repr ai)); temp HM._acc_resp (Vint (Int.repr ar)); temp HM._target tg] ++
           hrx5_lvars gv L)
  (SEPx (hrx5_wcore x25519 R L sec birth T head PS ++
         hrx5_rest x25519 R L (hnodes_snapped4 T NS PS) (map (kent_snapped T) KE) ++
         hrx5_globs gv S w kc FR ++
         [lul_rep gv lul; @data_at_ HRX Ews t_rxlog (gv HM._wg_shim_rx); qlen_rep gv q;
          skb_rep Tsh (l_skb L) (hrx5_skb dp o proto ip4 ip6 port); obj_rep dp o; img_rep img (obj_bytes o)] ++
         hrx5_scr4 x25519 aead_dec xaead_dec R L T PS o (s_boot S)))).

(* after B5: the snapshots (ds = D and the head, ss = S and w, sks = the skb), head0, secret_birth / secret = D's,
   and dispatch: the receive world after the packet (the draws d) *)
Definition hrx5_S5 (gv: globals) (L: hrx5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hrx5_run, EX sec: list byte, EX birth: int64, EX S: shim, EX w: list int64, EX NS: list hnode4,
  EX PS: list (val * share * peer), EX T: tstate, EX head: val, EX nk: val, EX KE: list kent4, EX st: Z,
  EX i: Z, EX kc: int64, EX lul: int64, EX q: int, EX proto: Z, EX ip4: list byte, EX ip6: list byte,
  EX port: list byte, EX o: hrx5_obj, EX dp: val, EX img: val, EX tg: val, EX ai: Z, EX ar: Z, EX d: rxdraw,
  PROPx [hrx5_base_ok R sec birth S; hrx5_inv x25519 R L NS PS KE T head nk; 0 <= st <= Int64.max_unsigned;
         0 <= i < st; obj_ok o; malloc_compatible (Zlength (obj_bytes o)) dp;
         hrx5_acc_ok x25519 aead_dec xaead_dec R NS PS T o (s_boot S) tg ai ar; rxdraw_ok T d; itable_wf T]
  (LOCALx (hrx5_ltemps nk KE st i S lul ++ hrx5_ptrs dp o ++
           [temp HM._img img; temp HM._len (Vlong (Int64.repr (Zlength (obj_bytes o))));
            temp HM._kind (Vint (Int.repr (obj_kind o)));
            temp HM._tw (Vint (if Z.leb 4 (Zlength (obj_bytes o)) then hrx5_tw (obj_bytes o) else Int.zero));
            temp HM._fwd (Vint (if hrx5_fwd (obj_bytes o) then Int.one else Int.zero));
            temp HM._acc_init (Vint (Int.repr ai)); temp HM._acc_resp (Vint (Int.repr ar)); temp HM._target tg;
            temp HM._head0 (hd nullval (t_L T)); temp HM._secret_birth (Vlong birth)] ++
           hrx5_lvars gv L)
  (SEPx ([rxw_rep W gv Tsh (l_wd L) head
            (rx_model x25519 aead_dec xaead_enc xaead_dec
               (hrx5_W0 (hrx5_DL x25519 R L sec birth) T PS S w kc lul) q (l_skb L)
               (hrx5_skb dp o proto ip4 ip6 port) (obj_bytes o) d)] ++
         hrx5_rest x25519 R L (hnodes_snapped4 T NS PS) (map (kent_snapped T) KE) ++
         hrx5_cglobs gv FR ++
         [qlen_rep gv q; skb_rep Tsh (l_skb L) (hrx5_skb dp o proto ip4 ip6 port); obj_rep dp o;
          img_rep img (obj_bytes o)] ++
         hrx5_scr5 x25519 aead_dec xaead_dec R L T PS o (s_boot S)
           (devsnap_val (hrx5_DL x25519 R L sec birth) head) S w (hrx5_skb dp o proto ip4 ip6 port)
           (hbytes Tsh sec (l_secret L))))).

(* after B6 (and B7): path = the receive model's path (hrx5_path), m_lul = the world's last_under_load after the
   packet, ds = the device AFTER the packet (the snapshot's secret / birthdate replaced by the rotation's, as the
   harness does), secret any *)
Definition hrx5_S6 (gv: globals) (L: hrx5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hrx5_run, EX sec: list byte, EX birth: int64, EX S: shim, EX w: list int64, EX NS: list hnode4,
  EX PS: list (val * share * peer), EX T: tstate, EX head: val, EX nk: val, EX KE: list kent4, EX st: Z,
  EX i: Z, EX kc: int64, EX lul: int64, EX q: int, EX proto: Z, EX ip4: list byte, EX ip6: list byte,
  EX port: list byte, EX o: hrx5_obj, EX dp: val, EX img: val, EX tg: val, EX ai: Z, EX ar: Z, EX d: rxdraw,
  let W0 := hrx5_W0 (hrx5_DL x25519 R L sec birth) T PS S w kc lul in
  let s := hrx5_skb dp o proto ip4 ip6 port in
  let W1 := rx_model x25519 aead_dec xaead_enc xaead_dec W0 q (l_skb L) s (obj_bytes o) d in
  PROPx [hrx5_base_ok R sec birth S; hrx5_inv x25519 R L NS PS KE T head nk; 0 <= st <= Int64.max_unsigned;
         0 <= i < st; obj_ok o; malloc_compatible (Zlength (obj_bytes o)) dp;
         hrx5_acc_ok x25519 aead_dec xaead_dec R NS PS T o (s_boot S) tg ai ar; rxdraw_ok T d; itable_wf T]
  (LOCALx ([temp HM._nk nk; temp HM._kes (hrx5_khead KE); temp HM._steps (Vlong (Int64.repr st));
            temp HM._i (Vlong (Int64.repr i)); temp HM._now (Vlong (s_boot S));
            temp HM._m_lul (Vlong (rw_lul W1))] ++ hrx5_ptrs dp o ++
           [temp HM._img img; temp HM._len (Vlong (Int64.repr (Zlength (obj_bytes o))));
            temp HM._kind (Vint (Int.repr (obj_kind o)));
            temp HM._acc_init (Vint (Int.repr ai)); temp HM._acc_resp (Vint (Int.repr ar)); temp HM._target tg;
            temp HM._head0 (hd nullval (t_L T));
            temp HM._path (Vint (Int.repr (hrx5_path W0 q s (obj_bytes o) d)))] ++
           hrx5_lvars gv L)
  (SEPx ([rxw_rep W gv Tsh (l_wd L) head W1] ++
         hrx5_rest x25519 R L (hnodes_snapped4 T NS PS) (map (kent_snapped T) KE) ++
         hrx5_cglobs gv FR ++
         [qlen_rep gv q; skb_rep Tsh (l_skb L) s; obj_rep dp o; img_rep img (obj_bytes o)] ++
         hrx5_scr5 x25519 aead_dec xaead_dec R L T PS o (s_boot S) (devsnap_val (rw_D W1) head) S w s
           (hout Tsh 32 (l_secret L))))).

(* after B8 (the four cases of CHECKs; after a session the harness has cleared P's keypairs): the loop's state
   again (a new world: the invariant holds), the packet still allocated *)
Definition hrx5_S8 (gv: globals) (L: hrx5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hrx5_run, EX sec: list byte, EX birth: int64, EX S: shim, EX w: list int64, EX NS: list hnode4,
  EX PS: list (val * share * peer), EX T: tstate, EX head: val, EX nk: val, EX KE: list kent4, EX st: Z,
  EX i: Z, EX kc: int64, EX lul: int64, EX q: int, EX proto: Z, EX ip4: list byte, EX ip6: list byte,
  EX port: list byte, EX o: hrx5_obj, EX dp: val, EX img: val,
  PROPx [hrx5_base_ok R sec birth S; hrx5_inv x25519 R L NS PS KE T head nk; 0 <= st <= Int64.max_unsigned;
         0 <= i < st; obj_ok o; malloc_compatible (Zlength (obj_bytes o)) dp]
  (LOCALx (hrx5_ltemps nk KE st i S lul ++ [temp HM._img img] ++ hrx5_lvars gv L)
  (SEPx (hrx5_wcore x25519 R L sec birth T head PS ++
         hrx5_rest x25519 R L NS KE ++ hrx5_globs gv S w kc FR ++
         hrx5_rglobs gv lul ++
         [skb_rep Tsh (l_skb L) (hrx5_skb dp o proto ip4 ip6 port); obj_rep dp o; img_rep img (obj_bytes o)] ++
         hrx5_scr L))).

End States.

(* main's post (TT) weakened to the canonical form forward needs for a return *)
Lemma hrx5_post_canon {Espec: OracleKind} {cs: compspecs} Delta P c Q gv F :
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (PROP () LOCAL () SEP (TT))) F)) ->
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (hrx5_post gv)) F)).
Proof.
  intros H. eapply semax_post; [| | | | apply H]; intros; simpl; intros rho; apply andp_left2;
    try apply derives_refl.
  apply sepcon_derives; [| apply derives_refl]. revert rho. apply bind_ret_derives. intros rho. apply TT_right.
Qed.
