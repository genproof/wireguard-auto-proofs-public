(* law keypairs: the unit-level definitions of the law.
   - the other peers and their keypairs (`hkp5_oth`: constant during the loop; the frame FR of the loop segments
     is `hkp5_othR .. O * FR0`), their pure invariant `hkp5_oth_ok`;
   - check_all's specification (the loop state with the other peers: it returns 1);
   - main's context, main's start state hkp5_P0 and the loop's entry hkp5_PA. *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
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
Require WgNoise.proof.harness.common4.hc4_prog.
Require Export WgNoise.proof.harness.keypairs.hkp5_defs.
Require Export WgNoise.proof.harness.keypairs.hkp5_rest.
Require WgNoise.contracts.x_keypairs.

Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The other peers and their keypairs                                      *)
(* ---------------------------------------------------------------------- *)

(* the globals others (the hnode list's head) and kes (the kents' head), the node list NS (snapped), the peers PS
   (the protocol's list, same order), the kents KE (snapped), the table T0 of the snapshots *)
Record hkp5_oth := mkOth5 {
  o_hd: val; o_NS: list hnode4; o_PS: list (val * share * peer); o_kd: val; o_KE: list kent4; o_T0: tstate }.

Definition hk5_peer_of (x: val * share * peer) : peer := match x with (_, _, P) => P end.

Section Oth.
Variable x25519: list byte -> list byte -> list byte.
#[local] Existing Instance W_keypairs.

(* their memory (and dsm, the device's snapshot) *)
Definition hkp5_oth_rep (F: hkp5_fix) (V: hkp5_val) (O: hkp5_oth) : list mpred :=
  [data_at Ews (tptr t_hnode4) (o_hd O) (f_gv F KC._others); hnodes_rep4 W_keypairs (o_hd O) (o_NS O);
   peers_rep (o_PS O);
   data_at Ews (tptr t_kent) (o_kd O) (f_gv F KC._kes); kents_rep W_keypairs (o_kd O) (o_KE O);
   @data_at CKS Ews t_devsnap (devsnap_val (hkp5_D x25519 F V) (v_head V)) (f_gv F KC._dsm)].

Definition hkp5_othR (F: hkp5_fix) (V: hkp5_val) (O: hkp5_oth) : mpred :=
  fold_right_sepcon (hkp5_oth_rep F V O).

End Oth.

(* the pure invariant of the other peers (constant during the loop):
   - the node list and the peers (same order), writable shares, distinct addresses, not P;
   - the nodes hold the snapshots of the peers' handshakes in T0, their counts and rests; the kents are snapped
     in T0 (kent_snapped T0 e = e), distinct;
   - the other pool entries OD of V are exactly the peers' handshake entries and the kents' entries, as in T0
     (hk5_pool keeps them as they are in every later table), hashed exactly as in T0 (OH);
   - each peer: its handshake entry's peer is itself, its device and static identity those of P's device, its
     keypair slots NULL or kents, its public-key link NULL, P or a peer of the list, a count 1 .. INT_MAX - 1;
   - each kent's entry belongs to a peer of the list;
   - the public-key table's head (dsm's) is P or a peer of the list;
   - (added for check_all's table_len and the end's frees) the peers' handshake addresses and the kents' addresses
     are pairwise distinct, and the peers and the other pool entries have share Ews (hnodes_add4 / kents_add4). *)
Definition hkp5_oth_ok (F: hkp5_fix) (V: hkp5_val) (O: hkp5_oth) : Prop :=
  let PS := o_PS O in let KE := o_KE O in let T0 := o_T0 O in
  let pa := map peer_addr4 PS in let ka := map ke_addr KE in
  hnodes_peers4 (o_NS O) PS /\ peers_wf PS /\ NoDup (f_p F :: pa) /\
  Forall2 (fun N x => match x with (q, _, Q) =>
     hn_snap N = hsnap_val (hs_snap_cur T0 q Q) /\ hn_refs N = Vint (p_refs Q) /\ hn_rest N = prsnap_val Q end)
     (o_NS O) PS /\
  Forall (fun e => kent_snapped T0 e = e) KE /\ NoDup ka /\
  (forall a, In a (saddrs (v_OD V)) <-> In a (map hs_addr pa) \/ In a ka) /\ NoDup (saddrs (v_OD V)) /\
  Forall (fun x => match x with (a, sh, E) =>
     sfind (t_D T0) a = Some (sh, E) /\ vin a (v_OH V) = vin a (t_L T0) end) (v_OD V) /\
  Forall (fun x => match x with (q, _, Q) =>
     e_peer (t_entry_d T0 (hs_addr q)) = q /\ e_type (t_entry_d T0 (hs_addr q)) = IDX_HANDSHAKE /\
     p_device Q = f_w F /\ hs_sid (p_hs Q) = id_addr (f_w F) /\
     Forall (vp_ok ka) [p_cur Q; p_prev Q; p_next Q] /\ vp_ok (f_p F :: pa) (p_pknext Q) /\
     0 < Int.unsigned (p_refs Q) < 2147483647 end) PS /\
  Forall (fun e => In (e_peer (t_entry_d T0 (ke_addr e))) pa) KE /\
  (v_head V = f_p F \/ In (v_head V) pa) /\
  NoDup (map hs_addr pa ++ ka) /\
  Forall (fun x => match x with (_, sh, _) => sh = Ews end) PS /\
  Forall (fun x => match x with (_, sh, _) => sh = Ews end) (v_OD V).

(* ---------------------------------------------------------------------- *)
(* check_all                                                               *)
(* ---------------------------------------------------------------------- *)

Section Check.
Variable x25519: list byte -> list byte -> list byte.
#[local] Existing Instance W_keypairs.

(* check_all(&p, &t, &w) in the loop's state (and the other peers): every check passes *)
Definition hk5_check_all_spec :=
  DECLARE KC._check_all
  WITH F: hkp5_fix, V: hkp5_val, Y: hkp5_dyn, O: hkp5_oth
  PRE [ tptr (Tstruct KC._wg_peer noattr), tptr (Tstruct KC._index_hashtable noattr),
        tptr (Tstruct KC._wg_device noattr) ]
    PROP (hkp5_fix_ok F V; hkp5_inv F V Y; hkp5_oth_ok F V O)
    PARAMS (f_p F; f_t F; f_w F) GLOBALS (f_gv F)
    SEP (fold_right_sepcon (hkp5_SEP x25519 F V Y (hkp5_othR x25519 F V O)))
  POST [ tint ]
    PROP () RETURN (Vint Int.one)
    SEP (fold_right_sepcon (hkp5_SEP x25519 F V Y (hkp5_othR x25519 F V O))).

End Check.

(* check_all's callees *)
Definition hkp5_G_check : funspecs :=
  [hs_same_but_next4_spec W_keypairs; hk5_rest_same_spec; hk5_warn_same_spec; dev_same4_spec W_keypairs;
   table_has_spec; table_index_unique_spec; table_len_spec; pr_same4_spec W_keypairs;
   kents_same_but_next4_spec W_keypairs; kents_hashed4_spec W_keypairs].

(* ---------------------------------------------------------------------- *)
(* main's context                                                          *)
(* ---------------------------------------------------------------------- *)

Definition hkp5_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition hkp5_main_spec : ident * funspec :=
  (KC._main, QPmain_spec_ext' WgNoise.contracts.x_keypairs.whole_prog tt hkp5_post).

(* the law's own functions *)
Definition hkp5_G (x25519: list byte -> list byte -> list byte) : funspecs :=
  [hk5_mk_unlink_spec; hk5_m_get_spec; hk5_m_put_spec; hk5_rest_same_spec; hk5_warn_same_spec;
   hk5_check_all_spec x25519; hk5_pick_live_spec; hk5_pick_held_spec; hkp5_main_spec].

Section Main.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* the unit's imports: everything common.h's functions import, and common.h's functions (v4) *)
Definition hkp5_imports (cs: compspecs) : funspecs :=
  WgNoise.proof.harness.common4.hc4_prog.hc4_imports x25519 aead_enc aead_dec xaead_enc xaead_dec W_keypairs cs ++
  WgNoise.proof.harness.common4.hc4_prog.hc4_G_keypairs x25519 aead_enc aead_dec W_keypairs.

(* main's context *)
Definition hkp5_Gmain : funspecs := hkp5_imports W_keypairs ++ hkp5_G x25519.

End Main.

Definition hkp5_R (gv: globals) : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (hkp5_post gv)) (@stackframe_of W_keypairs KC.f_main).

(* ---------------------------------------------------------------------- *)
(* main's start and the loop's entry                                       *)
(* ---------------------------------------------------------------------- *)

(* the shim's globals at the start (all zero) *)
Definition hkp5_S0 : shim :=
  mkShim Int64.zero Int64.zero Int64.zero zeros32 zeros32 Int.zero Int64.zero Int64.zero Int64.zero false
         Int64.zero false.

Section States.
Variable x25519: list byte -> list byte -> list byte.
#[local] Existing Instance W_keypairs.

(* main's start: after main_pre's globals, the stack frame and create_mem_mgr *)
Definition hkp5_P0 (F: hkp5_fix) (FR: mpred) : environ -> mpred :=
  PROPx []
  (LOCALx (hkp5_lvars F)
  (SEPx [data_at_ Tsh (Tstruct KC._wg_device noattr) (f_w F);
         data_at_ Tsh (Tstruct KC._index_hashtable noattr) (f_t F);
         data_at_ Tsh (Tstruct KC._pubkey_hashtable noattr) (f_pt F);
         data_at_ Tsh (Tstruct KC._wg_peer noattr) (f_p F);
         data_at_ Tsh (tarray tuchar 32) (f_raw F); data_at_ Tsh (tarray tuchar 32) (f_pub F);
         data_at_ Tsh (Tstruct KC._hs_snap noattr) (f_snap F); data_at_ Tsh (tarray tuchar 32) (f_opub F);
         data_at_ Tsh (tarray tuchar 32) (f_first F); data_at_ Tsh (tarray tuchar 32) (f_second F);
         data_at_ Ews (tptr t_mk5) (f_gv F KC._live); data_at_ Ews (tptr t_mk5) (f_gv F KC._s_prev);
         data_at_ Ews (tptr t_mk5) (f_gv F KC._s_cur); data_at_ Ews (tptr t_mk5) (f_gv F KC._s_next);
         data_at_ Ews tulong (f_gv F KC._m_frees); data_at_ Ews (tarray tulong 5) (f_gv F KC._m_warn);
         data_at_ Ews (tarray tulong 5) (f_gv F KC._warn0);
         data_at_ Ews (Tstruct KC._hs_snap noattr) (f_gv F KC._hsm);
         data_at_ Ews (Tstruct KC._pr_snap noattr) (f_gv F KC._prm);
         data_at_ Ews tuint (f_gv F KC._prefs);
         data_at_ Ews (Tstruct KC._dev_snap noattr) (f_gv F KC._dsm);
         data_at_ Ews (tptr (Tstruct KC._hnode noattr)) (f_gv F KC._others);
         data_at_ Ews (tptr (Tstruct KC._kent noattr)) (f_gv F KC._kes);
         shim_state4 (f_gv F) hkp5_S0 (Zrepeat Int64.zero 5);
         noise_globals_raw (f_gv F) zeros32 zeros32 Int64.zero; wg_consts (f_gv F); mem_mgr (f_gv F); FR])).

(* the loop's entry (before i = 0): the prologue's values V, the loop state Y, the other peers O *)
Definition hkp5_PA (F: hkp5_fix) (FR: mpred) : environ -> mpred :=
  EX V: hkp5_val, EX Y: hkp5_dyn, EX steps: Z, EX O: hkp5_oth,
  PROPx [hkp5_fix_ok F V; hkp5_inv F V Y; hkp5_oth_ok F V O; 0 <= steps <= Int64.max_unsigned]
  (LOCALx (hkp5_temps V Y steps ++ hkp5_lvars F)
  (SEPx (hkp5_SEP x25519 F V Y (hkp5_othR x25519 F V O * FR)))).

End States.

(* ---------------------------------------------------------------------- *)
(* The remaining segments' statements and contexts                         *)
(* ---------------------------------------------------------------------- *)

(* the prologue A = statements 0..28 of main (A1 .. A4 of hkp5_cut.v) *)
Definition hkp5_segA : statement :=
  ltac:(let x := eval cbv beta iota delta [hkp5_l hkp5_seql firstn skipn hkp5_stmts] in (hkp5_seql (hkp5_l 0 29)) in
        exact x).

Lemma hkp5_segA_eq : hkp5_segA = hkp5_seql (hkp5_l 0 29).
Proof. reflexivity. Qed.

Section Ctxs.
Variable x25519: list byte -> list byte -> list byte.

Definition hkp5_G_LC : funspecs := [hk5_check_all_spec x25519; check_failed_spec].

Definition hkp5_G_Op1a : funspecs :=
  [nondet_u8_spec; nondet_size_spec; P4.wg_noise_received_with_keypair_spec W_keypairs; check_failed_spec;
   hk5_check_all_spec x25519].

Definition hkp5_G_A : funspecs :=
  [draw_boottime_spec; P4.wg_noise_init_spec; @asm_env.nondet_bytes_spec W_keypairs; setup_device4_spec x25519; setup_peer_spec x25519;
   peer_randomize_rest4_spec; draw_steps_spec; bytes_eq_spec; hnodes_add4_spec x25519 W_keypairs;
   hs_randomize4_spec; nondet_u8_spec; P4.wg_index_hashtable_insert_spec; kents_add4_spec W_keypairs;
   hnodes_snap4_spec W_keypairs; kents_snap4_spec W_keypairs; hs_take4_spec; pr_take4_spec; dev_take4_spec].

Definition hkp5_G_F : funspecs :=
  [P4.wg_noise_keypairs_clear_spec W_keypairs; hk5_m_put_spec; P4.wg_noise_keypair_put_spec W_keypairs;
   hk5_check_all_spec x25519; check_failed_spec; kents_free4_spec W_keypairs; hnodes_free4_spec W_keypairs].

End Ctxs.
