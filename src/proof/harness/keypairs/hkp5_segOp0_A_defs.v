(* law keypairs, segment Op0 part A: the cut of statements 0..12 of the
   op 0 branch (hkp5_o0_A) into three pieces and their states.
     A1 = statements 0..5  (a0 / f0 / fr0 = the shim's counters, dead = nondet_u8() % 8 == 0, k = malloc,
                            continue if k == NULL)                      : hkp5_PL0 .. 0 -> EX Y dead k, K
     A2 = statements 6..10 (hs_randomize(&p.handshake), st = p.handshake.state, the optional insert,
                            p.is_dead = dead, prm.is_dead = dead)       : K -> EX Y' E, N
     A3 = statements 11..12 (hs_take(&snap, ..), r = begin_session(..)) : N -> EX O, hkp5_o0_M O
   The pure fact hkp5_o0A_ins_fact (the insert keeps hk5_rel) is a hypothesis of A2. *)
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
Require Export WgNoise.proof.harness.keypairs.hkp5_defs.
Require Export WgNoise.proof.harness.keypairs.hkp5_segOp0_defs.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The cut                                                                 *)
(* ---------------------------------------------------------------------- *)

Definition hkp5_o0A_l1 : list statement :=
  ltac:(let x := eval cbv beta iota delta [firstn hkp5_op0_stmts] in (firstn 6 hkp5_op0_stmts) in exact x).
Definition hkp5_o0A_l2 : list statement :=
  ltac:(let x := eval cbv beta iota delta [firstn skipn hkp5_op0_stmts] in (firstn 5 (skipn 6 hkp5_op0_stmts)) in
        exact x).
Definition hkp5_o0A_l3 : list statement :=
  ltac:(let x := eval cbv beta iota delta [firstn skipn hkp5_op0_stmts] in (firstn 2 (skipn 11 hkp5_op0_stmts)) in
        exact x).

(* the three pieces *)
Definition hkp5_o0A_s1 := ltac:(let x := eval cbv beta iota delta [hkp5_seql hkp5_o0A_l1] in
  (hkp5_seql hkp5_o0A_l1) in exact x).
Definition hkp5_o0A_s2 := ltac:(let x := eval cbv beta iota delta [hkp5_seql hkp5_o0A_l2] in
  (hkp5_seql hkp5_o0A_l2) in exact x).
Definition hkp5_o0A_s3 := ltac:(let x := eval cbv beta iota delta [hkp5_seql hkp5_o0A_l3] in
  (hkp5_seql hkp5_o0A_l3) in exact x).

Lemma hkp5_o0A_shape :
  hkp5_o0_A = hkp5_seqs hkp5_o0A_l1 (hkp5_seqs hkp5_o0A_l2 (hkp5_seql hkp5_o0A_l3)) /\
  hkp5_o0A_s1 = hkp5_seql hkp5_o0A_l1 /\ hkp5_o0A_s2 = hkp5_seql hkp5_o0A_l2 /\
  hkp5_o0A_s3 = hkp5_seql hkp5_o0A_l3 /\
  hkp5_o0A_l1 <> [] /\ hkp5_o0A_l2 <> [].
Proof. repeat split; try reflexivity; discriminate. Qed.

(* ---------------------------------------------------------------------- *)
(* The states                                                              *)
(* ---------------------------------------------------------------------- *)

(* P with is_dead set *)
Definition hkp5_o0A_set_dead (P: peer) (d: bool) : peer :=
  mkPeer (p_device P) d (p_cur P) (p_prev P) (p_next P) (p_hs P) (p_lsh P) (p_cookie P) (p_refs P) (p_id P)
         (p_pknext P).

Section Ctx.
Variable x25519: list byte -> list byte -> list byte.

(* after A1 (statement 5, k != NULL): Y = the loop state of hkp5_PL0 (unchanged, the whole invariant); dead = the
   drawn is_dead, k = the harness's new node (malloc'd, uninitialized); a0 / f0 / fr0 = the shim's counters *)
Definition hkp5_o0A_K (F: hkp5_fix) (V: hkp5_val) (steps: Z) (FR: mpred) (i: Z) (Y: hkp5_dyn) (dead: bool)
  (k: val) : environ -> mpred :=
  PROPx [0 <= i < steps; hkp5_fix_ok F V; hkp5_inv F V Y; 0 <= steps <= Int64.max_unsigned;
         s_boot (y_S Y) = y_now Y; k <> nullval]
  (LOCALx (temp KC._k k :: temp KC._dead (Val.of_bool dead) ::
           temp KC._a0 (Vlong (s_allocs (y_S Y))) :: temp KC._f0 (Vlong (s_fails (y_S Y))) ::
           temp KC._fr0 (Vlong (s_frees (y_S Y))) ::
           temp KC._i (Vlong (Int64.repr i)) :: hkp5_temps V Y steps ++ hkp5_lvars F)
  (SEPx (hkp5_SEP x25519 F V Y FR ++ [malloc_token Ews t_mk5 k; data_at_ Ews t_mk5 k]))).

(* after A2 (statement 10): Y = the loop state just before hs_take (= o_Y of hkp5_o0_M: P with the randomized
   handshake and is_dead = dead (prm follows it), T and the shim after the optional insert, H and hsn unchanged:
   the invariant without hk5_hsm_ok); E = the handshake's entry in that table *)
Definition hkp5_o0A_N (F: hkp5_fix) (V: hkp5_val) (steps: Z) (FR: mpred) (i: Z) (Y: hkp5_dyn) (E: entry)
  (k: val) : environ -> mpred :=
  PROPx [0 <= i < steps; hkp5_fix_ok F V; hkp5_inv0 F V Y; 0 <= steps <= Int64.max_unsigned;
         s_boot (y_S Y) = y_now Y; In (hs_state (p_hs (y_P Y))) hs_states; hs_ok (p_hs (y_P Y));
         k <> nullval; t_entry (y_T Y) (hs_addr (f_p F)) = Some E]
  (LOCALx (temp KC._k k :: temp KC._dead (Val.of_bool (p_dead (y_P Y))) ::
           temp KC._st (Vint (hs_state (p_hs (y_P Y)))) ::
           temp KC._a0 (Vlong (s_allocs (y_S Y))) :: temp KC._f0 (Vlong (s_fails (y_S Y))) ::
           temp KC._fr0 (Vlong (s_frees (y_S Y))) ::
           temp KC._i (Vlong (Int64.repr i)) :: hkp5_temps V Y steps ++ hkp5_lvars F)
  (SEPx (hkp5_SEP x25519 F V Y FR ++ [malloc_token Ews t_mk5 k; data_at_ Ews t_mk5 k]))).

End Ctx.

(* ---------------------------------------------------------------------- *)
(* The pure fact of A2 (proved in hkp5_segOp0_A_ins.v)                     *)
(* ---------------------------------------------------------------------- *)

(* wg_index_hashtable_insert(&t, &p.handshake.entry) with a fresh index keeps the relation (the handshake's
   entry moves to the head of the table with the new index; the keypairs' and the other entries are untouched) *)
Definition hkp5_o0A_ins_fact : Prop :=
  forall (p: val) (OD: list (val * share * entry)) (OH: list val) (H: hk5_state) (P: peer)
         (KS: list (val * keypair)) (T: tstate) (idx: int),
  hk5_rel p OD OH H P KS T -> t_fresh T (hs_addr p) idx -> itable_wf (t_insert T (hs_addr p) idx) ->
  hk5_rel p OD OH H P KS (t_insert T (hs_addr p) idx).
