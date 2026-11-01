(* law keypairs, segment Op0, branch L: the cut of the live
   branch hkp5_o0_sL (keypairs.c lines 333-386) and its states. Port of v1's hkp4_segOp0_L_defs.v.

   hkp5_o0_sL = 24 statements (hkp5_o0L_stmts):
     0..2   (hkp5_o0L_s1):  initiator = st == 4; kp = initiator ? p.keypairs.current_keypair : next_keypair;
                            CHECK(kp != NULL)
     3      (hkp5_o0L_sC):  CHECK(kp->sending_counter.counter == 0 && replay_counter_fresh(&kp->receiving_counter))
     4..14  (hkp5_o0L_s2a): k->scnt, rcnt, kp, refs, held, initiator, remote_index (snap), birth,
                            recv_valid / send_valid, bytes_copy(k->send, ..), bytes_copy(k->recv, ..)
     15..21 (hkp5_o0L_s2b): if (!id_known) { next_id = kp->internal_id; id_known = 1; } k->id = next_id;
                            next_id++; k->next = live; live = k; k->hashed = snap.hashed; k->index = ..
     22     (hkp5_o0L_s3):  CHECK(r == snap.hashed && !p.handshake.entry.hashed)
     23     (hkp5_o0L_s4):  if (initiator) hkp5_o0L_s4i else hkp5_o0L_s4r   (the shadow add_new_keypair)
   States: M2 (hkp5_segOp0_defs.v) -s1-> L1 -sC-> L1 -s2a-> L1b -s2b-> L2 -s3-> L2 -s4-> L3, then L3 |-- Z.
   The facts of begin_session's result (hkp5_o0_live_fact instantiated) are the hypothesis hkp5_o0L_facts of
   every piece. *)
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
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* The cut                                                                 *)
(* ---------------------------------------------------------------------- *)

Definition hkp5_o0L_stmts : list statement :=
  ltac:(let x := eval cbv beta iota delta [hkp5_flat hkp5_o0_sL] in (hkp5_flat hkp5_o0_sL) in exact x).

Lemma hkp5_o0L_stmts_length : length hkp5_o0L_stmts = 24%nat.
Proof. reflexivity. Qed.

(* statements 0..2 *)
Definition hkp5_o0L_s1 := ltac:(let x := eval cbv beta iota delta [hkp5_seql firstn hkp5_o0L_stmts] in
  (hkp5_seql (firstn 3 hkp5_o0L_stmts)) in exact x).
(* statement 3: the fresh-counter CHECK *)
Definition hkp5_o0L_sC := ltac:(let x := eval cbv beta iota delta [nth hkp5_o0L_stmts] in
  (nth 3 hkp5_o0L_stmts Sskip) in exact x).
(* statements 4..14 *)
Definition hkp5_o0L_s2a := ltac:(let x := eval cbv beta iota delta [hkp5_seql firstn skipn hkp5_o0L_stmts] in
  (hkp5_seql (firstn 11 (skipn 4 hkp5_o0L_stmts))) in exact x).
(* statements 15..21 *)
Definition hkp5_o0L_s2b := ltac:(let x := eval cbv beta iota delta [hkp5_seql firstn skipn hkp5_o0L_stmts] in
  (hkp5_seql (firstn 7 (skipn 15 hkp5_o0L_stmts))) in exact x).
(* statement 22 *)
Definition hkp5_o0L_s3 := ltac:(let x := eval cbv beta iota delta [nth hkp5_o0L_stmts] in
  (nth 22 hkp5_o0L_stmts Sskip) in exact x).
(* statement 23 and its branches *)
Definition hkp5_o0L_s4 := ltac:(let x := eval cbv beta iota delta [nth hkp5_o0L_stmts] in
  (nth 23 hkp5_o0L_stmts Sskip) in exact x).
Definition hkp5_o0L_s4i := ltac:(let x := eval cbv beta iota delta [hkp5_o0L_s4] in
  (match hkp5_o0L_s4 with Sifthenelse _ s _ => s | _ => Sskip end) in exact x).
Definition hkp5_o0L_s4r := ltac:(let x := eval cbv beta iota delta [hkp5_o0L_s4] in
  (match hkp5_o0L_s4 with Sifthenelse _ _ s => s | _ => Sskip end) in exact x).

Lemma hkp5_o0L_shape :
  hkp5_o0_sL =
    hkp5_seqs (firstn 3 hkp5_o0L_stmts) (Ssequence hkp5_o0L_sC (hkp5_seqs (firstn 11 (skipn 4 hkp5_o0L_stmts))
      (hkp5_seqs (firstn 7 (skipn 15 hkp5_o0L_stmts)) (Ssequence hkp5_o0L_s3 hkp5_o0L_s4)))) /\
  hkp5_o0L_s1 = hkp5_seql (firstn 3 hkp5_o0L_stmts) /\
  hkp5_o0L_s2a = hkp5_seql (firstn 11 (skipn 4 hkp5_o0L_stmts)) /\
  hkp5_o0L_s2b = hkp5_seql (firstn 7 (skipn 15 hkp5_o0L_stmts)) /\
  hkp5_o0L_s4 = Sifthenelse (Etempvar KC._initiator tint) hkp5_o0L_s4i hkp5_o0L_s4r.
Proof. repeat split; reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* The new node                                                            *)
(* ---------------------------------------------------------------------- *)

(* the role: initiator = (st == HANDSHAKE_CONSUMED_RESPONSE) *)
Definition hkp5_o0L_init (O: hkp5_o0) : bool := Int.eq (hs_state (p_hs (y_P (o_Y O)))) HS_CONSUMED_RESPONSE.

(* the node's contents (hkp5_o0_live_fact's M, with now = y_now = s_boot) *)
Definition hkp5_o0L_mk (F: hkp5_fix) (O: hkp5_o0) : hk5_mk :=
  let Y := o_Y O in let Hs := p_hs (y_P Y) in
  hkp5_o0_mk (o_kp O) (o5_sn (f_p F) O) (hkp5_o0L_init O) (kdf1 (hs_ck Hs) []) (kdf2 (hs_ck Hs) []) (y_now Y)
    (Int64.add (y_kc Y) Int64.one).

(* the node after statements 4..14: kp, refs, held, keys, valid flags, role, remote index, birth, both counters
   stored; hashed, index, id and next not yet *)
Definition hkp5_o0L_kv1 (F: hkp5_fix) (O: hkp5_o0) : reptype t_mk5 :=
  let M := hkp5_o0L_mk F O in
  (m5_kp M, (Vint (m5_refs M), (Vlong (m5_held M), (Vundef, (Vundef, (bytes (m5_send M), (bytes (m5_recv M),
   (Val.of_bool (m5_sv M), (Val.of_bool (m5_rv M), (Val.of_bool (m5_init M), (Vint (m5_rindex M),
   (Vlong (m5_birth M), (Vundef, (Vlong (m5_scnt M), (Vlong (m5_rcnt M), Vundef))))))))))))))).

(* the harness's model after live = k: the node pushed on the live list *)
Definition hkp5_o0L_H1 (F: hkp5_fix) (O: hkp5_o0) : hk5_state :=
  h5_set_ML (y_H (o_Y O)) ((o_k O, hkp5_o0L_mk F O) :: h5_ML (y_H (o_Y O))).

(* after the shadow add_new_keypair *)
Definition hkp5_o0L_H3 (F: hkp5_fix) (O: hkp5_o0) : hk5_state :=
  hkp5_o0_hl (o_k O) (hkp5_o0L_mk F O) (y_H (o_Y O)).

(* ---------------------------------------------------------------------- *)
(* begin_session's result (hkp5_o0_live_fact instantiated, now = y_now)    *)
(* ---------------------------------------------------------------------- *)

Definition hkp5_o0L_facts (F: hkp5_fix) (V: hkp5_val) (O: hkp5_o0) : Prop :=
  let p := f_p F in let Y := o_Y O in let P := y_P Y in let Hs := p_hs P in
  let res := o5_res p O in let P' := snd (fst (fst res)) in let W' := snd (fst res) in
  let sn := o5_sn p O in let H' := hkp5_o0L_H3 F O in
  fst (fst (fst res)) = sn_hashed sn /\
  snd res = Int64.add (y_kc Y) Int64.one /\
  p_hs P' = hs_zero Hs /\ p_device P' = p_device P /\ p_refs P' = p_refs P /\
  hk5_prsnap_val P' = hk5_prsnap_val P /\
  (if hkp5_o0L_init O then p_cur P' else p_next P') = o_kp O /\
  In (o_kp O, kp_new Hs (Int64.add (y_kc Y) Int64.one) (y_now Y)) (kw_KS W') /\
  t_entry (kw_T W') (hs_addr p) = Some (o_E O) /\ vin (hs_addr p) (t_L (kw_T W')) = false /\
  s_allocs (kw_S W') = Int64.add (s_allocs (y_S Y)) Int64.one /\ s_fails (kw_S W') = s_fails (y_S Y) /\
  hk5_rel p (v_OD V) (v_OH V) H' P' (kw_KS W') (kw_T W') /\
  hk5_warn_ok (v_w0 V) (h5_warn H') (o5_w p O) /\
  Int64.sub (s_frees (kw_S W')) (v_frees0 V) = h5_frees H' /\
  Int64.sub (s_allocs (kw_S W')) (v_allocs0 V) = Int64.add (h5_frees H') (Int64.repr (Zlength (h5_ML H'))) /\
  Zlength (kdf1 (hs_ck Hs) []) = 32 /\ Zlength (kdf2 (hs_ck Hs) []) = 32.

(* ---------------------------------------------------------------------- *)
(* The states                                                              *)
(* ---------------------------------------------------------------------- *)

Section Ctx.
Variable x25519: list byte -> list byte -> list byte.

(* PROP of every state: M2's *)
Definition hkp5_o0L_props (F: hkp5_fix) (V: hkp5_val) (steps i: Z) (O: hkp5_o0) : list Prop :=
  hkp5_o0_props F V steps i O ++ [hkp5_o0_stok O = true; o_kp O <> nullval].

(* first / second = kdf1 / kdf2 of the snapshot's chaining key (M2's) *)
Definition hkp5_o0L_fs (F: hkp5_fix) (O: hkp5_o0) : list mpred :=
  let Hs := p_hs (y_P (o_Y O)) in
  [hbytes Tsh (kdf1 (hs_ck Hs) []) (f_first F); hbytes Tsh (kdf2 (hs_ck Hs) []) (f_second F)].

(* after statements 0..2 (and 3..14): M2's locals with initiator and kp *)
Definition hkp5_o0L_locals1 (F: hkp5_fix) (V: hkp5_val) (steps i: Z) (O: hkp5_o0) : list localdef :=
  temp KC._initiator (Val.of_bool (hkp5_o0L_init O)) :: temp KC._kp (o_kp O) :: hkp5_o0_locals F V steps i O.

(* after statements 15..21: next_id = keypair_counter + 2, id_known = 1 *)
Definition hkp5_o0L_locals2 (F: hkp5_fix) (V: hkp5_val) (steps i: Z) (O: hkp5_o0) : list localdef :=
  let Y := o_Y O in let S := y_S Y in
  temp KC._initiator (Val.of_bool (hkp5_o0L_init O)) :: temp KC._kp (o_kp O) ::
  temp KC._r (Val.of_bool (fst (fst (fst (o5_res (f_p F) O))))) ::
  temp KC._k (o_k O) ::
  temp KC._dead (Val.of_bool (p_dead (y_P Y))) ::
  temp KC._st (Vint (hs_state (p_hs (y_P Y)))) ::
  temp KC._a0 (Vlong (s_allocs S)) :: temp KC._f0 (Vlong (s_fails S)) :: temp KC._fr0 (Vlong (s_frees S)) ::
  temp KC._i (Vlong (Int64.repr i)) ::
  temp KC._steps (Vlong (Int64.repr steps)) :: temp KC._now (Vlong (y_now Y)) ::
  temp KC._next_id (Vlong (Int64.add (Int64.add (y_kc Y) Int64.one) Int64.one)) ::
  temp KC._id_known (Vint Int.one) ::
  temp KC._allocs0 (Vlong (v_allocs0 V)) :: temp KC._frees0 (Vlong (v_frees0 V)) ::
  hkp5_lvars F.

(* the SEP list with the harness's model H and the items ks of the node k (before FR); hkp5_o0_SEP's but for
   H and the node's items *)
Definition hkp5_o0L_SEP (F: hkp5_fix) (V: hkp5_val) (O: hkp5_o0) (fs: list mpred) (H: hk5_state)
  (ks: list mpred) (FR: mpred) : list mpred :=
  let Y := o_Y O in let res := o5_res (f_p F) O in
  let P' := snd (fst (fst res)) in let W' := snd (fst res) in
  [device_rep Tsh (f_w F) (hkp5_D x25519 F V); itable Tsh (f_t F) (kw_T W'); ptable Tsh (f_pt F) (v_head V);
   peer_rep Tsh (f_p F) P'; keypairs_rep W_keypairs (kw_KS W');
   hbytes Tsh (v_RAW V) (f_raw F); hbytes Tsh (v_PUB V) (f_pub F);
   @data_at HCS Tsh t_hsnap (hsnap_val (o5_sn (f_p F) O)) (f_snap F); hout Tsh 32 (f_opub F)] ++ fs ++
  hk5_items (f_gv F) H ++ hkp5_hglobs F V Y ++
  hkp5_globs (f_gv F) (kw_S W') (o5_w (f_p F) O) (snd res) ++ ks ++ [FR].

(* after statements 0..2 (and 3): M2 with initiator and kp = the new keypair (the SEP is M2's) *)
Definition hkp5_o0L_1 (F: hkp5_fix) (V: hkp5_val) (steps: Z) (FR: mpred) (i: Z) (O: hkp5_o0) : environ -> mpred :=
  PROPx (hkp5_o0L_props F V steps i O)
  (LOCALx (hkp5_o0L_locals1 F V steps i O)
  (SEPx (hkp5_o0_SEP x25519 F V O (hkp5_o0L_fs F O) FR))).

(* after statements 4..14: the node k holds hkp5_o0L_kv1 *)
Definition hkp5_o0L_1b (F: hkp5_fix) (V: hkp5_val) (steps: Z) (FR: mpred) (i: Z) (O: hkp5_o0) : environ -> mpred :=
  PROPx (hkp5_o0L_props F V steps i O)
  (LOCALx (hkp5_o0L_locals1 F V steps i O)
  (SEPx (hkp5_o0L_SEP F V O (hkp5_o0L_fs F O) (y_H (o_Y O))
           [malloc_token Ews t_mk5 (o_k O); data_at Ews t_mk5 (hkp5_o0L_kv1 F O) (o_k O)] FR))).

(* after statements 15..21 (and 22): the node k pushed on the live list (hkp5_o0L_H1) *)
Definition hkp5_o0L_2 (F: hkp5_fix) (V: hkp5_val) (steps: Z) (FR: mpred) (i: Z) (O: hkp5_o0) : environ -> mpred :=
  PROPx (hkp5_o0L_props F V steps i O)
  (LOCALx (hkp5_o0L_locals2 F V steps i O)
  (SEPx (hkp5_o0L_SEP F V O (hkp5_o0L_fs F O) (hkp5_o0L_H1 F O) [] FR))).

(* after statement 23: the harness's model is hkp5_o0_hl k M H (hkp5_o0L_H3) *)
Definition hkp5_o0L_3 (F: hkp5_fix) (V: hkp5_val) (steps: Z) (FR: mpred) (i: Z) (O: hkp5_o0) : environ -> mpred :=
  PROPx (hkp5_o0L_props F V steps i O)
  (LOCALx (hkp5_o0L_locals2 F V steps i O)
  (SEPx (hkp5_o0L_SEP F V O (hkp5_o0L_fs F O) (hkp5_o0L_H3 F O) [] FR))).

End Ctx.
