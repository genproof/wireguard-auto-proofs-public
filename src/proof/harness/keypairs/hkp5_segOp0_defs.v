(* law keypairs, segment Op0: the cut of the op 0 branch (begin_session in
   any state) and its states.

   hkp5_sOp0 = 15 statements (hkp5_op0_stmts):
     A   = statements 0..12  (a0 / f0 / fr0, dead, k = malloc (continue if NULL), hs_randomize, st, the optional
                              insert, p.is_dead, prm.is_dead, hs_take(&snap), r = begin_session(..))
                                                                         : hkp5_PL0 .. 0 -> EX O, hkp5_o0_M O
     13  = Ssequence (t'34 = st != 3 && st != 4) (if (t'34) sW else { t'105 = fails;
             if (t'105 != f0) sFl else { sS; if (dead) sD else sL } })   : hkp5_o0_M O -> hkp5_o0_Z
           sW  wrong state       (CHECK(!r && hs_same && allocs == a0 && fails == f0); free(k))
           sFl failed allocation (CHECK(!r && hs_same && allocs == a0); free(k))
           sS  success prefix    (kp = NULL; CHECK(allocs == a0 + 1); m_transport; CHECK(hs_zeroed_from))
                                                                         : hkp5_o0_M O -> hkp5_o0_M2 O
           sD  dead              (CHECK(!r && frees == fr0 + 1 && entry unchanged); m_frees++; next_id++; free(k))
           sL  live              (CHECKs kp != NULL, fresh counters; node k; push; CHECK(r == snap.hashed && ..);
                                  the shadow add_new_keypair with m_put)
     14  = hs_take(&hsm, &p.handshake)                                   : hkp5_o0_Z -> hkp5_Icont
   hkp5_o0_Z = the loop state with the invariant but its last conjunct (hk5_hsm_ok: hsm holds an old snapshot);
   statement 14 re-establishes it. *)
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

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The cut                                                                 *)
(* ---------------------------------------------------------------------- *)

Definition hkp5_o0_A := ltac:(let x := eval cbv beta iota delta [hkp5_seql firstn hkp5_op0_stmts] in
  (hkp5_seql (firstn 13 hkp5_op0_stmts)) in exact x).
Definition hkp5_o0_s13 := ltac:(let x := eval cbv beta iota delta [nth hkp5_op0_stmts] in
  (nth 13 hkp5_op0_stmts Sskip) in exact x).
Definition hkp5_o0_s14 := ltac:(let x := eval cbv beta iota delta [nth hkp5_op0_stmts] in
  (nth 14 hkp5_op0_stmts Sskip) in exact x).

Definition hkp5_o0_s13a := ltac:(let x := eval cbv beta iota delta [hkp5_o0_s13] in
  (match hkp5_o0_s13 with Ssequence s _ => s | _ => Sskip end) in exact x).
Definition hkp5_o0_s13b := ltac:(let x := eval cbv beta iota delta [hkp5_o0_s13] in
  (match hkp5_o0_s13 with Ssequence _ s => s | _ => Sskip end) in exact x).

Definition hkp5_o0_sW := ltac:(let x := eval cbv beta iota delta [hkp5_o0_s13b] in
  (match hkp5_o0_s13b with Sifthenelse _ s _ => s | _ => Sskip end) in exact x).
Definition hkp5_o0_sFl := ltac:(let x := eval cbv beta iota delta [hkp5_o0_s13b] in
  (match hkp5_o0_s13b with Sifthenelse _ _ (Ssequence _ (Sifthenelse _ s _)) => s | _ => Sskip end) in exact x).
(* the success prefix: kp = NULL; CHECK(allocs == a0 + 1); m_transport; CHECK(hs_zeroed_from) *)
Definition hkp5_o0_lS : list statement := ltac:(let x := eval cbv beta iota delta [hkp5_o0_s13b] in
  (match hkp5_o0_s13b with
   | Sifthenelse _ _ (Ssequence _ (Sifthenelse _ _ (Ssequence a (Ssequence b (Ssequence c (Ssequence d _)))))) =>
       [a; b; c; d]
   | _ => [] end) in exact x).
Definition hkp5_o0_sS := ltac:(let x := eval cbv beta iota delta [hkp5_seql hkp5_o0_lS] in
  (hkp5_seql hkp5_o0_lS) in exact x).
Definition hkp5_o0_sD := ltac:(let x := eval cbv beta iota delta [hkp5_o0_s13b] in
  (match hkp5_o0_s13b with
   | Sifthenelse _ _ (Ssequence _ (Sifthenelse _ _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _
       (Sifthenelse _ s _))))))) => s
   | _ => Sskip end) in exact x).
Definition hkp5_o0_sL := ltac:(let x := eval cbv beta iota delta [hkp5_o0_s13b] in
  (match hkp5_o0_s13b with
   | Sifthenelse _ _ (Ssequence _ (Sifthenelse _ _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _
       (Sifthenelse _ _ s))))))) => s
   | _ => Sskip end) in exact x).

Lemma hkp5_o0_shape :
  hkp5_sOp0 = hkp5_seqs (firstn 13 hkp5_op0_stmts) (Ssequence hkp5_o0_s13 hkp5_o0_s14) /\
  hkp5_o0_A = hkp5_seql (firstn 13 hkp5_op0_stmts) /\
  hkp5_o0_s13 = Ssequence hkp5_o0_s13a hkp5_o0_s13b /\
  hkp5_o0_s13a =
    Sifthenelse (Ebinop Cop.One (Etempvar KC._st tint) (Econst_int (Int.repr 3) tint) tint)
      (Sset KC._t'34 (Ecast (Ebinop Cop.One (Etempvar KC._st tint) (Econst_int (Int.repr 4) tint) tint) tbool))
      (Sset KC._t'34 (Econst_int (Int.repr 0) tint)) /\
  hkp5_o0_s13b =
    Sifthenelse (Etempvar KC._t'34 tint) hkp5_o0_sW
      (Ssequence (Sset KC._t'105 (Evar KC._wg_shim_alloc_failures tulong))
        (Sifthenelse (Ebinop Cop.One (Etempvar KC._t'105 tulong) (Etempvar KC._f0 tulong) tint) hkp5_o0_sFl
          (hkp5_seqs hkp5_o0_lS (Sifthenelse (Etempvar KC._dead tbool) hkp5_o0_sD hkp5_o0_sL)))) /\
  hkp5_o0_sS = hkp5_seql hkp5_o0_lS /\ hkp5_o0_lS <> [] /\ firstn 13 hkp5_op0_stmts <> [].
Proof. repeat split; try reflexivity; discriminate. Qed.

(* ---------------------------------------------------------------------- *)
(* The model of the live branch                                            *)
(* ---------------------------------------------------------------------- *)

(* the new node: keypair kp, one reference, none held, hashed / index from the snapshot (the handshake's index moves
   to the keypair), keys first / second in the role's order, both valid, the role, the snapshot's remote index,
   birth now, id, fresh counters *)
Definition hkp5_o0_mk (kp: val) (sn: hsnap) (init: bool) (first second: list byte) (now id: int64) : hk5_mk :=
  mkMK5 kp Int.one Int64.zero (sn_hashed sn) (if sn_hashed sn then e_index (sn_entry sn) else Int.zero)
        (if init then first else second) (if init then second else first) true true init
        (hs_rindex (sn_hs sn)) now id Int64.zero Int64.zero.

(* the harness after the live branch: node k with contents M pushed on live, then the shadow add_new_keypair
   (initiator: s_next != NULL: old = s_prev, s_prev = s_next, s_next = NULL, m_put(s_cur, 1), m_put(old, 1); else
   old = s_prev, s_prev = s_cur, m_put(old, 1); then s_cur = k.  Responder: old = s_next, s_next = k, m_put(old, 1),
   old = s_prev, s_prev = NULL, m_put(old, 1)) *)
Definition hkp5_o0_hl (k: val) (M: hk5_mk) (H: hk5_state) : hk5_state :=
  let H1 := h5_set_ML H ((k, M) :: h5_ML H) in
  if m5_init M then
    if eq_dec (h5_sn H) nullval then
      h5_set_slots (hk5_hput (h5_sp H) true H1) (h5_sc H) k nullval
    else
      h5_set_slots (hk5_hput (h5_sp H) true (hk5_hput (h5_sc H) true H1)) (h5_sn H) k nullval
  else
    h5_set_slots (hk5_hput (h5_sp H) true (hk5_hput (h5_sn H) true H1)) nullval (h5_sc H) k.

(* begin_session's result in the live case (prot_model3.begin_session_model through P4.bs_res, the warnings
   begin_session_warn) against the harness's live branch: the return value is the snapshot's hashed flag; the
   handshake zeroed, the rest of P (prm's view) unchanged; the new keypair (kp_new: fresh counters) in KS' and in
   the role's slot, id kc + 1; its entry unchanged and out of the table; one allocation more, no failure; the
   relation, the warnings and the counters of hkp5_inv re-established for the harness's update hkp5_o0_hl.
   Proved by the pure child of (hkp5_segOp0_live.v: hkp5_model_facts -> hkp5_o0_live_fact). *)
Definition hkp5_o0_live_fact : Prop :=
  forall (p: val) (OD: list (val * share * entry)) (OH: list val) (H: hk5_state) (P: peer)
         (KS: list (val * keypair)) (T: tstate) (S: shim) (w0 w: list int64) (kc: int64)
         (kp k: val) (E: entry) (frees0 allocs0: int64),
  hk5_rel p OD OH H P KS T -> hk5_warn_ok w0 (h5_warn H) w ->
  orb (Int.eq (hs_state (p_hs P)) HS_CREATED_RESPONSE) (Int.eq (hs_state (p_hs P)) HS_CONSUMED_RESPONSE) = true ->
  p_dead P = false -> hs_ok (p_hs P) ->
  kp <> nullval -> ~ In kp (saddrs (t_D T)) -> ~ In kp (map fst KS) ->
  k <> nullval -> ~ In k (map fst (h5_ML H)) ->
  t_entry T (hs_addr p) = Some E ->
  Int64.sub (s_frees S) frees0 = h5_frees H ->
  Int64.sub (s_allocs S) allocs0 = Int64.add (h5_frees H) (Int64.repr (Zlength (h5_ML H))) ->
  let Hs := p_hs P in
  let init := Int.eq (hs_state Hs) HS_CONSUMED_RESPONSE in
  let res := P4.bs_res P p kp kc KS T S in
  let P' := snd (fst (fst res)) in
  let W' := snd (fst res) in
  let sn := snap_of T (hs_addr p) E Hs in
  let M := hkp5_o0_mk kp sn init (kdf1 (hs_ck Hs) []) (kdf2 (hs_ck Hs) []) (s_boot S) (Int64.add kc Int64.one) in
  let H' := hkp5_o0_hl k M H in
  fst (fst (fst res)) = sn_hashed sn /\
  snd res = Int64.add kc Int64.one /\
  p_hs P' = hs_zero Hs /\ p_device P' = p_device P /\ p_refs P' = p_refs P /\
  hk5_prsnap_val P' = hk5_prsnap_val P /\
  (if init then p_cur P' else p_next P') = kp /\
  In (kp, kp_new Hs (Int64.add kc Int64.one) (s_boot S)) (kw_KS W') /\
  t_entry (kw_T W') (hs_addr p) = Some E /\ vin (hs_addr p) (t_L (kw_T W')) = false /\
  s_allocs (kw_S W') = Int64.add (s_allocs S) Int64.one /\ s_fails (kw_S W') = s_fails S /\
  hk5_rel p OD OH H' P' (kw_KS W') (kw_T W') /\
  hk5_warn_ok w0 (h5_warn H') (begin_session_warn P (hs_addr p) kp kc (mkKW KS T S) w) /\
  Int64.sub (s_frees (kw_S W')) frees0 = h5_frees H' /\
  Int64.sub (s_allocs (kw_S W')) allocs0 = Int64.add (h5_frees H') (Int64.repr (Zlength (h5_ML H'))).

(* ---------------------------------------------------------------------- *)
(* The invariant without hsm                                               *)
(* ---------------------------------------------------------------------- *)

(* hkp5_inv but its last conjunct (hk5_hsm_ok) *)
Definition hkp5_inv0 (F: hkp5_fix) (V: hkp5_val) (Y: hkp5_dyn) : Prop :=
  hk5_rel (f_p F) (v_OD V) (v_OH V) (y_H Y) (y_P Y) (y_KS Y) (y_T Y) /\
  hk5_warn_ok (v_w0 V) (h5_warn (y_H Y)) (y_w Y) /\
  p_device (y_P Y) = f_w F /\ hs_sid (p_hs (y_P Y)) = id_addr (f_w F) /\ p_refs (y_P Y) = v_prefs V /\
  Int64.sub (s_frees (y_S Y)) (v_frees0 V) = h5_frees (y_H Y) /\
  Int64.sub (s_allocs (y_S Y)) (v_allocs0 V) =
    Int64.add (h5_frees (y_H Y)) (Int64.repr (Zlength (h5_ML (y_H Y)))) /\
  (y_id_known Y = true -> y_next_id Y = Int64.add (y_kc Y) Int64.one) /\
  Int64.unsigned (y_now Y) < 2 ^ 62 /\ p_pknext (y_P Y) = nullval.

Lemma hkp5_inv_split F V Y :
  hkp5_inv F V Y <-> hkp5_inv0 F V Y /\ hk5_hsm_ok (f_p F) (y_T Y) (y_P Y) (y_hsn Y).
Proof. unfold hkp5_inv, hkp5_inv0. tauto. Qed.

(* ---------------------------------------------------------------------- *)
(* The state after A (after r = begin_session(..))                         *)
(* ---------------------------------------------------------------------- *)

(* o_Y: the loop state just before begin_session: the shim after the optional insert's draw, its warnings,
   keypair_counter, P with the randomized handshake and is_dead = dead, the live keypairs, the table after the
   optional insert, the harness model (unchanged), now, next_id, id_known, hsm's (old) snapshot;
   o_E: the handshake's entry in that table (the snapshot's); o_k: the harness's new node (malloc'd, not NULL);
   o_kp: begin_session's allocation (NULL: it failed) *)
Record hkp5_o0 := mkO5 { o_Y: hkp5_dyn; o_E: entry; o_k: val; o_kp: val }.

(* begin_session's result (return value, peer, keypair world, keypair_counter) and warnings *)
Definition o5_res (p: val) (O: hkp5_o0) : bool * peer * kworld * int64 :=
  let Y := o_Y O in P4.bs_res (y_P Y) p (o_kp O) (y_kc Y) (y_KS Y) (y_T Y) (y_S Y).
Definition o5_w (p: val) (O: hkp5_o0) : list int64 :=
  let Y := o_Y O in
  begin_session_warn (y_P Y) (hs_addr p) (o_kp O) (y_kc Y) (mkKW (y_KS Y) (y_T Y) (y_S Y)) (y_w Y).

(* hs_take's snapshot *)
Definition o5_sn (p: val) (O: hkp5_o0) : hsnap :=
  snap_of (y_T (o_Y O)) (hs_addr p) (o_E O) (p_hs (y_P (o_Y O))).

(* the state after the live / dead / failed branches' role test: CREATED_RESPONSE or CONSUMED_RESPONSE *)
Definition hkp5_o0_stok (O: hkp5_o0) : bool :=
  let Hs := p_hs (y_P (o_Y O)) in
  orb (Int.eq (hs_state Hs) HS_CREATED_RESPONSE) (Int.eq (hs_state Hs) HS_CONSUMED_RESPONSE).

Section Ctx.
Variable x25519: list byte -> list byte -> list byte.

Definition hkp5_o0_props (F: hkp5_fix) (V: hkp5_val) (steps i: Z) (O: hkp5_o0) : list Prop :=
  let Y := o_Y O in let Hs := p_hs (y_P Y) in
  [0 <= i < steps; hkp5_fix_ok F V; hkp5_inv0 F V Y; 0 <= steps <= Int64.max_unsigned;
   s_boot (y_S Y) = y_now Y; In (hs_state Hs) hs_states; hs_ok Hs;
   o_k O <> nullval; ~ In (o_k O) (map fst (h5_ML (y_H Y)));
   t_entry (y_T Y) (hs_addr (f_p F)) = Some (o_E O);
   (s_failnext (y_S Y) = true -> o_kp O = nullval);
   (o_kp O <> nullval -> ~ In (o_kp O) (saddrs (t_D (y_T Y))) /\ ~ In (o_kp O) (map fst (y_KS Y)))].

Definition hkp5_o0_locals (F: hkp5_fix) (V: hkp5_val) (steps i: Z) (O: hkp5_o0) : list localdef :=
  let Y := o_Y O in let S := y_S Y in
  temp KC._r (Val.of_bool (fst (fst (fst (o5_res (f_p F) O))))) ::
  temp KC._k (o_k O) ::
  temp KC._dead (Val.of_bool (p_dead (y_P Y))) ::
  temp KC._st (Vint (hs_state (p_hs (y_P Y)))) ::
  temp KC._a0 (Vlong (s_allocs S)) :: temp KC._f0 (Vlong (s_fails S)) :: temp KC._fr0 (Vlong (s_frees S)) ::
  temp KC._i (Vlong (Int64.repr i)) ::
  hkp5_temps V Y steps ++ hkp5_lvars F.

(* fs: first and second; the kernel's objects are begin_session's result; the harness's model, hsm, prm (of P
   before begin_session: its rest is unchanged), warn0, prefs are o_Y's *)
Definition hkp5_o0_SEP (F: hkp5_fix) (V: hkp5_val) (O: hkp5_o0) (fs: list mpred) (FR: mpred) : list mpred :=
  let Y := o_Y O in let res := o5_res (f_p F) O in
  let P' := snd (fst (fst res)) in let W' := snd (fst res) in
  [device_rep Tsh (f_w F) (hkp5_D x25519 F V); itable Tsh (f_t F) (kw_T W'); ptable Tsh (f_pt F) (v_head V);
   peer_rep Tsh (f_p F) P'; keypairs_rep W_keypairs (kw_KS W');
   hbytes Tsh (v_RAW V) (f_raw F); hbytes Tsh (v_PUB V) (f_pub F);
   @data_at HCS Tsh t_hsnap (hsnap_val (o5_sn (f_p F) O)) (f_snap F); hout Tsh 32 (f_opub F)] ++ fs ++
  hk5_items (f_gv F) (y_H Y) ++ hkp5_hglobs F V Y ++
  hkp5_globs (f_gv F) (kw_S W') (o5_w (f_p F) O) (snd res) ++
  [malloc_token Ews t_mk5 (o_k O); data_at_ Ews t_mk5 (o_k O); FR].

(* after A *)
Definition hkp5_o0_M (F: hkp5_fix) (V: hkp5_val) (steps: Z) (FR: mpred) (i: Z) (O: hkp5_o0) : environ -> mpred :=
  PROPx (hkp5_o0_props F V steps i O)
  (LOCALx (hkp5_o0_locals F V steps i O)
  (SEPx (hkp5_o0_SEP F V O [hout Tsh 32 (f_first F); hout Tsh 32 (f_second F)] FR))).

(* after the success prefix sS: the state is CREATED_RESPONSE or CONSUMED_RESPONSE, the allocation succeeded,
   kp = NULL, first / second = kdf1 / kdf2 of the snapshot's chaining key *)
Definition hkp5_o0_M2 (F: hkp5_fix) (V: hkp5_val) (steps: Z) (FR: mpred) (i: Z) (O: hkp5_o0) : environ -> mpred :=
  let Hs := p_hs (y_P (o_Y O)) in
  PROPx (hkp5_o0_props F V steps i O ++ [hkp5_o0_stok O = true; o_kp O <> nullval])
  (LOCALx (temp KC._kp nullval :: hkp5_o0_locals F V steps i O)
  (SEPx (hkp5_o0_SEP F V O [hbytes Tsh (kdf1 (hs_ck Hs) []) (f_first F);
                            hbytes Tsh (kdf2 (hs_ck Hs) []) (f_second F)] FR))).

(* after statement 13 (every branch): the loop state but hsm (an old snapshot) *)
Definition hkp5_o0_Z (F: hkp5_fix) (V: hkp5_val) (steps: Z) (FR: mpred) (i: Z) : environ -> mpred :=
  EX Y: hkp5_dyn,
  PROPx [0 <= i < steps; hkp5_fix_ok F V; hkp5_inv0 F V Y; 0 <= steps <= Int64.max_unsigned]
  (LOCALx (temp KC._i (Vlong (Int64.repr i)) :: hkp5_temps V Y steps ++ hkp5_lvars F)
  (SEPx (hkp5_SEP x25519 F V Y FR))).

End Ctx.

(* ---------------------------------------------------------------------- *)
(* begin_session's result in the simple cases (by unfolding)               *)
(* ---------------------------------------------------------------------- *)

Lemma hkp5_o0_res_wrong P p kp kc KS T S :
  orb (Int.eq (hs_state (p_hs P)) HS_CREATED_RESPONSE) (Int.eq (hs_state (p_hs P)) HS_CONSUMED_RESPONSE) = false ->
  P4.bs_res P p kp kc KS T S = (false, P, mkKW KS T S, kc).
Proof. intros E. unfold P4.bs_res, begin_session_model. cbv zeta. rewrite E. reflexivity. Qed.

Lemma hkp5_o0_res_fail P p kc KS T S :
  orb (Int.eq (hs_state (p_hs P)) HS_CREATED_RESPONSE) (Int.eq (hs_state (p_hs P)) HS_CONSUMED_RESPONSE) = true ->
  P4.bs_res P p nullval kc KS T S = (false, P, mkKW KS T (shim_alloc_fail S), kc).
Proof.
  intros E. unfold P4.bs_res, begin_session_model. cbv zeta. rewrite E. cbn [negb].
  rewrite if_true by reflexivity. reflexivity.
Qed.

Lemma hkp5_o0_res_dead P p kp kc KS T S :
  orb (Int.eq (hs_state (p_hs P)) HS_CREATED_RESPONSE) (Int.eq (hs_state (p_hs P)) HS_CONSUMED_RESPONSE) = true ->
  kp <> nullval -> p_dead P = true ->
  P4.bs_res P p kp kc KS T S =
  (false, p_set_hs P (hs_zero (p_hs P)), mkKW KS T (shim_free (shim_alloc_ok S)), Int64.add kc Int64.one).
Proof.
  intros E Hk Hd. unfold P4.bs_res, begin_session_model. cbv zeta. rewrite E. cbn [negb].
  rewrite if_false by exact Hk. rewrite Hd. reflexivity.
Qed.

(* the warnings: nothing but the live case's add_new_keypair warns *)
Lemma hkp5_o0_warn_wrong P hs kp kc W w :
  orb (Int.eq (hs_state (p_hs P)) HS_CREATED_RESPONSE) (Int.eq (hs_state (p_hs P)) HS_CONSUMED_RESPONSE) = false ->
  begin_session_warn P hs kp kc W w = w.
Proof. intros E. unfold begin_session_warn. cbv zeta. rewrite E. reflexivity. Qed.

Lemma hkp5_o0_warn_fail P hs kc W w :
  begin_session_warn P hs nullval kc W w = w.
Proof.
  unfold begin_session_warn. cbv zeta.
  destruct (negb _); [reflexivity |]. rewrite if_true by reflexivity. reflexivity.
Qed.

Lemma hkp5_o0_warn_dead P hs kp kc W w :
  p_dead P = true -> begin_session_warn P hs kp kc W w = w.
Proof.
  intros Hd. unfold begin_session_warn. cbv zeta.
  destruct (negb _); [reflexivity |]. destruct (eq_dec kp nullval); [reflexivity |]. rewrite Hd. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* Small facts for the children                                            *)
(* ---------------------------------------------------------------------- *)

Lemma hkp5_o0_aupd_fst {A: Type} (ML: list (val * A)) x v : map fst (aupd ML x v) = map fst ML.
Proof.
  induction ML as [| [a w] ML IH]; [reflexivity |]. cbn [aupd].
  destruct (eq_dec a x); cbn [map fst]; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma hkp5_o0_adel_incl {A: Type} (ML: list (val * A)) x y : In y (map fst (adel ML x)) -> In y (map fst ML).
Proof.
  induction ML as [| [a w] ML IH]; [intros [] |]. cbn [adel].
  destruct (eq_dec a x); cbn [map fst]; [intros H; right; exact H |].
  intros [H | H]; [left; exact H | right; apply IH; exact H].
Qed.

Lemma hkp5_o0_adel_nodup {A: Type} (ML: list (val * A)) x : NoDup (map fst ML) -> NoDup (map fst (adel ML x)).
Proof.
  intros ND. induction ML as [| [a w] ML IH]; [constructor |]. cbn [adel map fst] in *.
  inversion ND as [| ? ? Hn ND']; subst.
  destruct (eq_dec a x); [exact ND' |]. cbn [map fst]. constructor; [| apply IH; exact ND'].
  intros Hin. apply Hn. eapply hkp5_o0_adel_incl. exact Hin.
Qed.

Lemma hkp5_o0_adel_in {A: Type} (ML: list (val * A)) x y :
  In y (map fst ML) -> y <> x -> In y (map fst (adel ML x)).
Proof.
  intros Hy Hne. induction ML as [| [a w] ML IH]; [contradiction |]. cbn [adel map fst] in *.
  destruct (eq_dec a x) as [-> |].
  - destruct Hy as [-> | Hy]; [congruence | exact Hy].
  - cbn [map fst]. destruct Hy as [-> | Hy]; [left; reflexivity | right; apply IH; exact Hy].
Qed.

(* m_put keeps the other live nodes and the list's distinctness *)
Lemma hkp5_o0_put_in x u ML fr mw y :
  In y (map fst ML) -> y <> x -> In y (map fst (fst (fst (hk5_put x u ML fr mw)))).
Proof.
  intros Hy Hne. unfold hk5_put.
  destruct (eq_dec x nullval); [exact Hy |].
  destruct (afind ML x) as [M |]; [| exact Hy].
  destruct (Int.eq (m5_refs M) REFCOUNT_SATURATED); cbn [fst].
  - destruct u; [rewrite hkp5_o0_aupd_fst |]; exact Hy.
  - destruct (Int.eq _ Int.zero); cbn [fst].
    + apply hkp5_o0_adel_in; assumption.
    + rewrite hkp5_o0_aupd_fst. exact Hy.
Qed.

Lemma hkp5_o0_put_nodup x u ML fr mw :
  NoDup (map fst ML) -> NoDup (map fst (fst (fst (hk5_put x u ML fr mw)))).
Proof.
  intros ND. unfold hk5_put.
  destruct (eq_dec x nullval); [exact ND |].
  destruct (afind ML x) as [M |]; [| exact ND].
  destruct (Int.eq (m5_refs M) REFCOUNT_SATURATED); cbn [fst].
  - destruct u; [rewrite hkp5_o0_aupd_fst |]; exact ND.
  - destruct (Int.eq _ Int.zero); cbn [fst].
    + apply hkp5_o0_adel_nodup; exact ND.
    + rewrite hkp5_o0_aupd_fst. exact ND.
Qed.

(* the new node is not a live node: its memory is separate from the live list's *)
Lemma hkp5_o0_fresh_node k ML :
  data_at_ Ews t_mk5 k * hk5_mklist ML |-- !! (~ In k (map fst ML)).
Proof.
  revert k. induction ML as [| [m M] ML IH]; intros k.
  - cbn [hk5_mklist map]. apply prop_right. intros [].
  - cbn [hk5_mklist map fst]. unfold hk5_node. Intros.
    destruct (eq_dec m k) as [-> | Hne].
    + unfold data_at_.
      sep_apply (data_at_conflict Ews t_mk5 (default_val t_mk5) (hk5_mk_val M (hk5_head ML)) k).
      all: try (rewrite FF_sepcon; apply FF_left).
      all: try (auto with valid_pointer; fail).
      all: try reflexivity.
    + sep_apply (IH k). Intros. apply prop_right. intros [E | E]; [congruence | contradiction].
Qed.
