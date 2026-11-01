(* law handshake: main's phase P6 (statements 111..120) cut into ten segments, and the states between
   them.

   Statement 111 is ONE block; flattened (hhs3_p6_blk, 33 statements) and followed by statements 112..120:
     A  = blk 0..3    m_transport(first, second, st2.ck); hs_take(&snap, &pb.handshake);
                      f0 = wg_shim_alloc_failures; ra = begin_session(&pb.handshake, &pb.keypairs)   S5' -> SA
     B  = blk 4       if (failures != f0) { CHECK(!ra && hs_same && current == NULL); free; free; return 0 }
                                                                                                SA -> SB
     C1 = blk 5..10   CHECK(ra); ka = current; CHECK(slots); CHECK(initiator, remote index);
                      CHECK(keys = first / second); CHECK(valid)                                SB -> SC1
     C2 = blk 11..16  CHECK(birthdates); CHECK(counters); CHECK(refcount, entry type / peer);
                      CHECK(entry index, table_has, table_len); CHECK(!hashed, zeroed_from); id_a = id
                                                                                                SC1 -> SC
     D  = blk 17..19  hs_take(&snap, &pa.handshake); f0 = failures; rb = begin_session(pa)      SC -> SD
     E  = blk 20      if (failures != f0) { CHECK(!rb && hs_same && next == NULL);
                      wg_noise_keypairs_clear(&pb.keypairs); free; free; return 0 }             SD -> SE
     F1 = blk 21..26  CHECK(rb); kb = next; CHECK(slots); CHECK(!initiator, remote index);
                      CHECK(keys = second / first); CHECK(valid)                                SE -> SF
     F2 = blk 27..32  CHECK(birthdates); CHECK(refcount, entry); CHECK(entry index, table);
                      CHECK(!hashed, zeroed_from); CHECK(internal_id == id_a + 1); CHECK(cross-over)
                                                                                                SF -> SF
     G  = 112..113    wg_noise_keypairs_clear(&pb.keypairs); wg_noise_keypairs_clear(&pa.keypairs)
                                                                                                SF -> SG
     H  = 114..120    the final CHECKs (slots, tables' heads, shim counters, refcounts), free(m1),
                      free(m2), return 0                                                        SG -> FF
   The S5 objects are fixed (record hhs3_p6_w, context hhs3_p6_ctx); the phase lemma introduces them.
   Pure facts taken as hypotheses by the segments (proved in their own files):
     hhs3_p6_factsA_stmt  A's side after P5: pb's state (= hhs3_p6_PB2n), st2.ck's length, m1's sender
     hhs3_p6_factsB_stmt  B's side after P4: pa's state, H2's fields, m2's sender
     hhs3_p6_ck_stmt      (X25519 commutativity) B's chaining key = A's (H2's ck = st2.ck)
     hhs3_p6_model_stmt   begin_session_model / keypairs_clear_model computed on these states
     hhs3_p6_free_stmt    the returns: every local back to main's stack frame (any shim / counter) *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.handshake.hhs3_spec.
Require Import WgNoise.proof.harness.handshake.hhs3_defs.
Require WgNoise.harness.x_handshake.code.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The segments                                                            *)
(* ---------------------------------------------------------------------- *)

(* statement 111 (the begin_session block), flattened *)
Definition hhs3_p6_blk : list statement :=
  ltac:(let x := eval cbv beta iota delta [hhs3_flat_seq hhs3_l hhs3_seql firstn skipn hhs3_stmts nth] in
        (hhs3_flat_seq (nth 0 (hhs3_l 111 10) Sskip)) in exact x).

Lemma hhs3_p6_blk_length : length hhs3_p6_blk = 33%nat.
Proof. reflexivity. Qed.

Definition hhs3_p6_bl (i n: nat) : list statement := firstn n (skipn i hhs3_p6_blk).

Definition hhs3_p6_A := ltac:(let x := eval cbv beta iota delta [hhs3_p6_bl hhs3_seql firstn skipn hhs3_p6_blk] in (hhs3_seql (hhs3_p6_bl 0 4)) in exact x).
Definition hhs3_p6_B := ltac:(let x := eval cbv beta iota delta [hhs3_p6_bl hhs3_seql firstn skipn hhs3_p6_blk] in (hhs3_seql (hhs3_p6_bl 4 1)) in exact x).
Definition hhs3_p6_C1 := ltac:(let x := eval cbv beta iota delta [hhs3_p6_bl hhs3_seql firstn skipn hhs3_p6_blk] in (hhs3_seql (hhs3_p6_bl 5 6)) in exact x).
Definition hhs3_p6_C2 := ltac:(let x := eval cbv beta iota delta [hhs3_p6_bl hhs3_seql firstn skipn hhs3_p6_blk] in (hhs3_seql (hhs3_p6_bl 11 6)) in exact x).
Definition hhs3_p6_D := ltac:(let x := eval cbv beta iota delta [hhs3_p6_bl hhs3_seql firstn skipn hhs3_p6_blk] in (hhs3_seql (hhs3_p6_bl 17 3)) in exact x).
Definition hhs3_p6_E := ltac:(let x := eval cbv beta iota delta [hhs3_p6_bl hhs3_seql firstn skipn hhs3_p6_blk] in (hhs3_seql (hhs3_p6_bl 20 1)) in exact x).
Definition hhs3_p6_F1 := ltac:(let x := eval cbv beta iota delta [hhs3_p6_bl hhs3_seql firstn skipn hhs3_p6_blk] in (hhs3_seql (hhs3_p6_bl 21 6)) in exact x).
Definition hhs3_p6_F2 := ltac:(let x := eval cbv beta iota delta [hhs3_p6_bl hhs3_seql firstn skipn hhs3_p6_blk] in (hhs3_seql (hhs3_p6_bl 27 6)) in exact x).
Definition hhs3_p6_G := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 112 2)) in exact x).
Definition hhs3_p6_H := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 114 7)) in exact x).

(* the phase is the sequence of the ten segments (up to the association of Ssequence) *)
Lemma hhs3_p6_flat :
  unfold_Ssequence hhs3_P6 =
  unfold_Ssequence
    (Ssequence hhs3_p6_A (Ssequence hhs3_p6_B (Ssequence hhs3_p6_C1 (Ssequence hhs3_p6_C2
      (Ssequence hhs3_p6_D (Ssequence hhs3_p6_E (Ssequence hhs3_p6_F1 (Ssequence hhs3_p6_F2
        (Ssequence hhs3_p6_G hhs3_p6_H))))))))).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------- *)

Record hhs3_p6_w := mkW6 {
  w_R: hhs3_run; w_S: shim; w_m1: val; w_m2: val; w_a0: int64; w_f0: int64; w_l0: int64;
  w_I: hhs3_ini; w_M1: init_msg; w_H1: handshake;
  w_MI: list byte * list byte * list byte * list byte * list byte * list byte;
  w_nowb: int64; w_PA1: peer; w_CI1: list byte * list byte * list byte * list byte;
  w_CI2: list byte * list byte * list byte;
  w_Q: hhs3_rsp; w_M2: resp_msg; w_H2: handshake; w_MR: list byte * list byte * list byte * list byte * list byte;
  w_nowa: int64; w_PB2: peer; w_ST2: list byte * list byte }.

Section Model.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* the PROP of S5 *)
Definition hhs3_p6_ctx (L: hhs3_loc) (V: hhs3_p6_w) : Prop :=
  hhs3_run_ok (w_R V) /\ hhs3_cnt (w_S V) (w_a0 V) (w_f0 V) (w_l0 V) /\
  hhs3_after_init x25519 aead_enc (w_R V) L (w_I V) (w_M1 V) (w_H1 V) (w_MI V) /\
  hhs3_after_cin x25519 aead_dec (w_R V) L (w_M1 V) (w_nowb V) (w_PA1 V) (w_CI1 V) (w_CI2 V) /\
  hhs3_after_resp x25519 aead_enc (w_R V) L (w_M1 V) (w_PA1 V) (w_CI2 V) (w_Q V) (w_M2 V) (w_H2 V) (w_MR V) /\
  hhs3_after_cre x25519 aead_dec (w_R V) L (w_I V) (w_M1 V) (w_H1 V) (w_MI V) (w_M2 V) (w_nowa V) (w_PB2 V)
    (w_ST2 V) /\
  s_boot (w_S V) = w_nowa V.

(* the chaining key of A's st2 (the model's) *)
Definition hhs3_p6_ck (V: hhs3_p6_w) : list byte := fst (w_ST2 V).

(* pb's handshake entry in ita (index idx1) and pa's in itb (index of create_response) *)
Definition hhs3_p6_EB1 (L: hhs3_loc) (V: hhs3_p6_w) : entry := mkEntry (l_pb L) IDX_HANDSHAKE (i_idx (w_I V)).
Definition hhs3_p6_EA1 (L: hhs3_loc) (V: hhs3_p6_w) : entry := mkEntry (l_pa L) IDX_HANDSHAKE (s_idx (w_Q V)).

(* the peers at S5 *)
Definition hhs3_p6_PBa (V: hhs3_p6_w) : peer := p_set_refs (w_PB2 V) Int.one.
Definition hhs3_p6_PAa (V: hhs3_p6_w) : peer := hhs3_PA3 x25519 (w_R V) (w_PA1 V) (w_M2 V) (w_H2 V).

(* PB2 as consume_response made it (= hhs3_p5_new of phase P5) *)
Definition hhs3_p6_PB2n (L: hhs3_loc) (V: hhs3_p6_w) : peer :=
  let P0 := hhs3_PB1 x25519 (w_R V) L (w_M1 V) (w_H1 V) in
  let H1 := w_H1 V in
  let '(ck, h) := w_ST2 V in
  p_set_hs (p_set_refs P0 (rc_add1 (p_refs P0)))
    (mkHS HS_CONSUMED_RESPONSE (hs_lic H1) (hs_sid H1) (hs_eph H1) (hs_rstatic H1) (rm_eph (w_M2 V)) (hs_ss H1)
          (hs_psk H1) h ck (hs_ts H1) (rm_sender (w_M2 V))).

(* begin_session's results *)
Definition hhs3_p6_BA (L: hhs3_loc) (V: hhs3_p6_w) (ka: val) : bool * peer * kworld * int64 :=
  bs_res (hhs3_p6_PBa V) (l_pb L) ka Int64.zero [] (hhs3_TA1 L (w_I V)) (w_S V).
Definition hhs3_p6_BB (L: hhs3_loc) (V: hhs3_p6_w) (kb: val) : bool * peer * kworld * int64 :=
  bs_res (hhs3_p6_PAa V) (l_pa L) kb Int64.one [] (hhs3_TB1 L (w_Q V)) (shim_alloc_ok (w_S V)).

(* their explicit values at success *)
Definition hhs3_p6_KA (V: hhs3_p6_w) : keypair := kp_new (p_hs (hhs3_p6_PBa V)) Int64.one (w_nowa V).
Definition hhs3_p6_KB (V: hhs3_p6_w) : keypair := kp_new (w_H2 V) (Int64.repr 2) (w_nowa V).
Definition hhs3_p6_PB3 (V: hhs3_p6_w) (ka: val) : peer :=
  p_set_slots (p_set_hs (hhs3_p6_PBa V) (hs_zero (p_hs (hhs3_p6_PBa V)))) ka nullval nullval.
Definition hhs3_p6_PA4 (V: hhs3_p6_w) (kb: val) : peer :=
  p_set_slots (p_set_hs (hhs3_p6_PAa V) (hs_zero (w_H2 V))) nullval nullval kb.
Definition hhs3_p6_TA2 (L: hhs3_loc) (V: hhs3_p6_w) (ka: val) : tstate :=
  mkT [(ka, Ews, mkEntry (l_pb L) IDX_KEYPAIR (i_idx (w_I V))); (hs_addr (l_pb L), Tsh, hhs3_p6_EB1 L V)] [ka].
Definition hhs3_p6_TB2 (L: hhs3_loc) (V: hhs3_p6_w) (kb: val) : tstate :=
  mkT [(kb, Ews, mkEntry (l_pa L) IDX_KEYPAIR (s_idx (w_Q V))); (hs_addr (l_pa L), Tsh, hhs3_p6_EA1 L V)] [kb].

(* after both keypairs_clear *)
Definition hhs3_p6_TA3 (L: hhs3_loc) (V: hhs3_p6_w) : tstate := mkT [(hs_addr (l_pb L), Tsh, hhs3_p6_EB1 L V)] [].
Definition hhs3_p6_TB3 (L: hhs3_loc) (V: hhs3_p6_w) : tstate := mkT [(hs_addr (l_pa L), Tsh, hhs3_p6_EA1 L V)] [].
Definition hhs3_p6_S1 (V: hhs3_p6_w) : shim := shim_alloc_ok (w_S V).
Definition hhs3_p6_S2 (V: hhs3_p6_w) : shim := shim_alloc_ok (shim_alloc_ok (w_S V)).
Definition hhs3_p6_S4 (V: hhs3_p6_w) : shim := shim_free (shim_free (hhs3_p6_S2 V)).

(* ---------------------------------------------------------------------- *)
(* Pure statements                                                         *)
(* ---------------------------------------------------------------------- *)

(* A's side: consume_response's peer is hhs3_p6_PB2n (as hhs3_p5_acc_stmt of phase P5: the kernel's
   consume_resp_crypto = the harness's m_consume_response_model, here in the accepting direction), st2.ck
   has 32 bytes, m1's sender index is idx1, A's handshake belongs to A's identity *)
Definition hhs3_p6_factsA_stmt : Prop :=
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  forall L V, hhs3_p6_ctx L V ->
  w_PB2 V = hhs3_p6_PB2n L V /\ Zlength (hhs3_p6_ck V) = 32 /\ Zlength (snd (w_ST2 V)) = 32 /\
  im_sender (w_M1 V) = i_idx (w_I V) /\ hs_sid (w_H1 V) = id_addr (l_wa L).

(* B's side: create_response's handshake H2 (state CREATED_RESPONSE, remote index = m1's sender, B's
   identity), m2's sender index = the drawn index, pa's other fields (alive, no keypairs, device wb) *)
Definition hhs3_p6_factsB_stmt : Prop :=
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  forall L V, hhs3_p6_ctx L V ->
  hs_state (w_H2 V) = HS_CREATED_RESPONSE /\ hs_rindex (w_H2 V) = im_sender (w_M1 V) /\
  hs_sid (w_H2 V) = id_addr (l_wb L) /\ rm_sender (w_M2 V) = s_idx (w_Q V) /\
  p_dead (w_PA1 V) = false /\ p_cur (w_PA1 V) = nullval /\ p_prev (w_PA1 V) = nullval /\
  p_next (w_PA1 V) = nullval /\ p_device (w_PA1 V) = l_wb L.

(* completeness of the key schedule (X25519 commutativity, hhs3_comm): B's chaining key after
   create_response = A's after consume_response (both sides accepted, so every DH value of one side is that
   of the other: ee, es, se, ss, and the psk is shared) *)
Definition hhs3_p6_ck_stmt : Prop :=
  hhs3_comm x25519 -> x25519_props x25519 -> aead_props aead_enc aead_dec ->
  forall L V, hhs3_p6_ctx L V -> hs_ck (w_H2 V) = hhs3_p6_ck V.

(* the models of begin_session and keypairs_clear on these states (given factsA / factsB) *)
Definition hhs3_p6_model_stmt : Prop :=
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  forall L V, hhs3_p6_ctx L V -> hhs3_p6_factsA_stmt -> hhs3_p6_factsB_stmt ->
  (hhs3_p6_BA L V nullval = (false, hhs3_p6_PBa V, mkKW [] (hhs3_TA1 L (w_I V)) (shim_alloc_fail (w_S V)),
                             Int64.zero)) /\
  (forall ka, ka <> nullval -> ~ In ka (saddrs (t_D (hhs3_TA1 L (w_I V)))) ->
     hhs3_p6_BA L V ka = (true, hhs3_p6_PB3 V ka, mkKW [(ka, hhs3_p6_KA V)] (hhs3_p6_TA2 L V ka) (hhs3_p6_S1 V),
                          Int64.one)) /\
  (hhs3_p6_BB L V nullval = (false, hhs3_p6_PAa V, mkKW [] (hhs3_TB1 L (w_Q V)) (shim_alloc_fail (hhs3_p6_S1 V)),
                             Int64.one)) /\
  (forall kb, kb <> nullval -> ~ In kb (saddrs (t_D (hhs3_TB1 L (w_Q V)))) ->
     hhs3_p6_BB L V kb = (true, hhs3_p6_PA4 V kb, mkKW [(kb, hhs3_p6_KB V)] (hhs3_p6_TB2 L V kb) (hhs3_p6_S2 V),
                          Int64.repr 2)) /\
  (forall ka S, ka <> nullval ->
     keypairs_clear_model (hhs3_p6_PB3 V ka) (mkKW [(ka, hhs3_p6_KA V)] (hhs3_p6_TA2 L V ka) S) =
     (p_set_slots (hhs3_p6_PB3 V ka) nullval nullval nullval, mkKW [] (hhs3_p6_TA3 L V) (shim_free S))) /\
  (forall kb S, kb <> nullval ->
     keypairs_clear_model (hhs3_p6_PA4 V kb) (mkKW [(kb, hhs3_p6_KB V)] (hhs3_p6_TB2 L V kb) S) =
     (p_set_slots (hhs3_p6_PA4 V kb) nullval nullval nullval, mkKW [] (hhs3_p6_TB3 L V) (shim_free S))).

(* all of them (the hypotheses of the segment lemmas) *)
Definition hhs3_p6_pure : Prop :=
  hhs3_p6_factsA_stmt /\ hhs3_p6_factsB_stmt /\ hhs3_p6_ck_stmt /\ hhs3_p6_model_stmt.

End Model.

(* ---------------------------------------------------------------------- *)
(* The states                                                              *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* S5's locals *)
Definition hhs3_p6_locals (gv: globals) (L: hhs3_loc) (V: hhs3_p6_w) : list localdef :=
  [temp HC._m1 (w_m1 V); temp HC._m2 (w_m2 V); temp HC._now_a (Vlong (w_nowa V));
   temp HC._all_ok (Vint (if hhs3_ok4 x25519 (hhs3_ok3 x25519 (w_R V) (w_I V) (w_nowb V) (w_MI V)) (w_MI V)
                               (w_R V) (w_MR V) then Int.one else Int.zero))] ++
  hhs3_cnt_temps (w_a0 V) (w_f0 V) (w_l0 V) ++ hhs3_lvars gv L.

(* the SEP of the phase: S5's with the items that change as parameters (the tables, the peers, the shim,
   keypair_counter kc, the keypairs of pb (kpa) and pa (kpb), the snapshot, first, second) *)
Definition hhs3_p6_sep (gv: globals) (L: hhs3_loc) (FR: mpred) (V: hhs3_p6_w)
  (ita_item itb_item pb_item pa_item: mpred) (S: shim) (kc: int64) (kpa kpb snap_item first_item second_item: mpred)
  : list mpred :=
  hhs3_setup_sep x25519 (w_R V) L ++
  [ita_item; itb_item; pb_item; pa_item;
   hhs3_tok t_init (w_m1 V); init_rep Ews (w_m1 V) (hhs3_M1m x25519 (w_R V) (w_M1 V));
   hhs3_tok t_resp (w_m2 V); resp_rep Ews (w_m2 V) (hhs3_M2m x25519 (w_R V) (w_M2 V));
   hout Tsh 12 (l_ts L); hout Tsh 148 (l_img L); hout Tsh 92 (l_rimg L);
   (let '(E, encs, enct, ep, ck, h) := w_MI V in @data_at HCS Tsh t_minit (minit_val E encs enct ep ck h) (l_mi L));
   @data_at_ HCS Tsh t_mcinit (l_ci L);
   (let '(E, encn, ep, ck, h) := w_MR V in @data_at HCS Tsh t_mresp (mresp_val E encn ep ck h) (l_mr L));
   (let '(ck, h) := w_ST2 V in @data_at HCS Tsh t_mstate (mstate_val ck h) (l_st2 L));
   kpa; kpb] ++
  hhs3_globs gv S kc FR ++
  [hout Tsh 32 (l_tmp L); hout Tsh 148 (l_imgb L); hout Tsh 92 (l_rimgb L); snap_item;
   hout Tsh 32 (l_d1 L); hout Tsh 32 (l_d2 L); hout Tsh 32 (l_d1b L); hout Tsh 32 (l_d2b L);
   first_item; second_item].

(* the snapshots taken by A and D *)
Definition hhs3_p6_snapA (L: hhs3_loc) (V: hhs3_p6_w) : mpred :=
  @data_at HCS Tsh t_hsnap
    (hsnap_val (snap_of (hhs3_TA1 L (w_I V)) (hs_addr (l_pb L)) (hhs3_p6_EB1 L V) (p_hs (hhs3_p6_PBa V))))
    (l_snap L).
Definition hhs3_p6_snapB (L: hhs3_loc) (V: hhs3_p6_w) : mpred :=
  @data_at HCS Tsh t_hsnap
    (hsnap_val (snap_of (hhs3_TB1 L (w_Q V)) (hs_addr (l_pa L)) (hhs3_p6_EA1 L V) (p_hs (hhs3_p6_PAa x25519 V))))
    (l_snap L).
Definition hhs3_p6_first (L: hhs3_loc) (V: hhs3_p6_w) : mpred := hbytes Tsh (kdf1 (hhs3_p6_ck V) []) (l_first L).
Definition hhs3_p6_second (L: hhs3_loc) (V: hhs3_p6_w) : mpred := hbytes Tsh (kdf2 (hhs3_p6_ck V) []) (l_second L).

(* S5 with the objects fixed (the phase lemma's precondition after Intros; = hhs3_S5's body) *)
Definition hhs3_p6_S5 (gv: globals) (L: hhs3_loc) (FR: mpred) (V: hhs3_p6_w) : environ -> mpred :=
  PROPx []
  (LOCALx (hhs3_p6_locals gv L V)
  (SEPx (hhs3_setup_sep x25519 (w_R V) L ++
         [itable Tsh (l_ita L) (hhs3_TA1 L (w_I V)); itable Tsh (l_itb L) (hhs3_TB1 L (w_Q V));
          peer_rep Tsh (l_pb L) (hhs3_p6_PBa V); peer_rep Tsh (l_pa L) (hhs3_p6_PAa x25519 V);
          hhs3_tok t_init (w_m1 V); init_rep Ews (w_m1 V) (hhs3_M1m x25519 (w_R V) (w_M1 V));
          hhs3_tok t_resp (w_m2 V); resp_rep Ews (w_m2 V) (hhs3_M2m x25519 (w_R V) (w_M2 V));
          hout Tsh 12 (l_ts L); hout Tsh 148 (l_img L); hout Tsh 92 (l_rimg L);
          (let '(E, encs, enct, ep, ck, h) := w_MI V in @data_at HCS Tsh t_minit (minit_val E encs enct ep ck h) (l_mi L));
          @data_at_ HCS Tsh t_mcinit (l_ci L);
          (let '(E, encn, ep, ck, h) := w_MR V in @data_at HCS Tsh t_mresp (mresp_val E encn ep ck h) (l_mr L));
          (let '(ck, h) := w_ST2 V in @data_at HCS Tsh t_mstate (mstate_val ck h) (l_st2 L))] ++
         hhs3_globs gv (w_S V) Int64.zero FR ++ hhs3_scr_tmp L))).

(* after A: begin_session(pb) returned (ka = kzalloc's result) *)
Definition hhs3_p6_SA (gv: globals) (L: hhs3_loc) (FR: mpred) (V: hhs3_p6_w) : environ -> mpred :=
  EX ka: val,
  PROPx [ka <> nullval -> ~ In ka (saddrs (t_D (hhs3_TA1 L (w_I V))))]
  (LOCALx ([temp HC._ra (Val.of_bool (fst (fst (fst (hhs3_p6_BA L V ka))))); temp HC._f0 (Vlong (w_l0 V))] ++
           hhs3_p6_locals gv L V)
  (SEPx (hhs3_p6_sep gv L FR V
           (itable Tsh (l_ita L) (kw_T (snd (fst (hhs3_p6_BA L V ka)))))
           (itable Tsh (l_itb L) (hhs3_TB1 L (w_Q V)))
           (peer_rep Tsh (l_pb L) (snd (fst (fst (hhs3_p6_BA L V ka)))))
           (peer_rep Tsh (l_pa L) (hhs3_p6_PAa x25519 V))
           (kw_S (snd (fst (hhs3_p6_BA L V ka)))) (snd (hhs3_p6_BA L V ka))
           (keypairs_rep W_handshake (kw_KS (snd (fst (hhs3_p6_BA L V ka))))) emp
           (hhs3_p6_snapA L V) (hhs3_p6_first L V) (hhs3_p6_second L V)))).

(* after B (allocation succeeded) and after C1 (k = true: ka loaded into the local ka) *)
Definition hhs3_p6_SBC (k: bool) (gv: globals) (L: hhs3_loc) (FR: mpred) (V: hhs3_p6_w) : environ -> mpred :=
  EX ka: val,
  PROPx [ka <> nullval; ~ In ka (saddrs (t_D (hhs3_TA1 L (w_I V))))]
  (LOCALx ((if k then [temp HC._ka ka] else [temp HC._ra (Vint Int.one)]) ++ hhs3_p6_locals gv L V)
  (SEPx (hhs3_p6_sep gv L FR V
           (itable Tsh (l_ita L) (hhs3_p6_TA2 L V ka)) (itable Tsh (l_itb L) (hhs3_TB1 L (w_Q V)))
           (peer_rep Tsh (l_pb L) (hhs3_p6_PB3 V ka)) (peer_rep Tsh (l_pa L) (hhs3_p6_PAa x25519 V))
           (hhs3_p6_S1 V) Int64.one
           (keypairs_rep W_handshake [(ka, hhs3_p6_KA V)]) emp
           (hhs3_p6_snapA L V) (hhs3_p6_first L V) (hhs3_p6_second L V)))).
Definition hhs3_p6_SB gv L FR V := hhs3_p6_SBC false gv L FR V.
Definition hhs3_p6_SC1 gv L FR V := hhs3_p6_SBC true gv L FR V.

(* after C2: id_a = ka's internal id (1) *)
Definition hhs3_p6_SC (gv: globals) (L: hhs3_loc) (FR: mpred) (V: hhs3_p6_w) : environ -> mpred :=
  EX ka: val,
  PROPx [ka <> nullval; ~ In ka (saddrs (t_D (hhs3_TA1 L (w_I V))))]
  (LOCALx ([temp HC._ka ka; temp HC._id_a (Vlong Int64.one)] ++ hhs3_p6_locals gv L V)
  (SEPx (hhs3_p6_sep gv L FR V
           (itable Tsh (l_ita L) (hhs3_p6_TA2 L V ka)) (itable Tsh (l_itb L) (hhs3_TB1 L (w_Q V)))
           (peer_rep Tsh (l_pb L) (hhs3_p6_PB3 V ka)) (peer_rep Tsh (l_pa L) (hhs3_p6_PAa x25519 V))
           (hhs3_p6_S1 V) Int64.one
           (keypairs_rep W_handshake [(ka, hhs3_p6_KA V)]) emp
           (@data_at_ HCS Tsh t_hsnap (l_snap L)) (hhs3_p6_first L V) (hhs3_p6_second L V)))).

(* after D: begin_session(pa) returned (kb = kzalloc's result) *)
Definition hhs3_p6_SD (gv: globals) (L: hhs3_loc) (FR: mpred) (V: hhs3_p6_w) : environ -> mpred :=
  EX ka: val, EX kb: val,
  PROPx [ka <> nullval; ~ In ka (saddrs (t_D (hhs3_TA1 L (w_I V))));
         kb <> nullval -> ~ In kb (saddrs (t_D (hhs3_TB1 L (w_Q V))))]
  (LOCALx ([temp HC._rb (Val.of_bool (fst (fst (fst (hhs3_p6_BB x25519 L V kb))))); temp HC._f0 (Vlong (w_l0 V));
            temp HC._ka ka; temp HC._id_a (Vlong Int64.one)] ++ hhs3_p6_locals gv L V)
  (SEPx (hhs3_p6_sep gv L FR V
           (itable Tsh (l_ita L) (hhs3_p6_TA2 L V ka))
           (itable Tsh (l_itb L) (kw_T (snd (fst (hhs3_p6_BB x25519 L V kb)))))
           (peer_rep Tsh (l_pb L) (hhs3_p6_PB3 V ka))
           (peer_rep Tsh (l_pa L) (snd (fst (fst (hhs3_p6_BB x25519 L V kb)))))
           (kw_S (snd (fst (hhs3_p6_BB x25519 L V kb)))) (snd (hhs3_p6_BB x25519 L V kb))
           (keypairs_rep W_handshake [(ka, hhs3_p6_KA V)])
           (keypairs_rep W_handshake (kw_KS (snd (fst (hhs3_p6_BB x25519 L V kb)))))
           (hhs3_p6_snapB L V) (hhs3_p6_first L V) (hhs3_p6_second L V)))).

(* after E (allocation succeeded; k = false) and after F1 / F2 (k = true: kb loaded into the local kb) *)
Definition hhs3_p6_SEF (k: bool) (gv: globals) (L: hhs3_loc) (FR: mpred) (V: hhs3_p6_w) : environ -> mpred :=
  EX ka: val, EX kb: val,
  PROPx [ka <> nullval; ~ In ka (saddrs (t_D (hhs3_TA1 L (w_I V))));
         kb <> nullval; ~ In kb (saddrs (t_D (hhs3_TB1 L (w_Q V))))]
  (LOCALx ((if k then [temp HC._kb kb] else [temp HC._rb (Vint Int.one)]) ++
           [temp HC._ka ka; temp HC._id_a (Vlong Int64.one)] ++ hhs3_p6_locals gv L V)
  (SEPx (hhs3_p6_sep gv L FR V
           (itable Tsh (l_ita L) (hhs3_p6_TA2 L V ka)) (itable Tsh (l_itb L) (hhs3_p6_TB2 L V kb))
           (peer_rep Tsh (l_pb L) (hhs3_p6_PB3 V ka)) (peer_rep Tsh (l_pa L) (hhs3_p6_PA4 x25519 V kb))
           (hhs3_p6_S2 V) (Int64.repr 2)
           (keypairs_rep W_handshake [(ka, hhs3_p6_KA V)]) (keypairs_rep W_handshake [(kb, hhs3_p6_KB V)])
           (hhs3_p6_snapB L V) (hhs3_p6_first L V) (hhs3_p6_second L V)))).
Definition hhs3_p6_SE gv L FR V := hhs3_p6_SEF false gv L FR V.
Definition hhs3_p6_SF gv L FR V := hhs3_p6_SEF true gv L FR V.

(* after G: both keypairs freed, the tables hold only the (unhashed) handshake entries *)
Definition hhs3_p6_SG (gv: globals) (L: hhs3_loc) (FR: mpred) (V: hhs3_p6_w) : environ -> mpred :=
  EX ka: val, EX kb: val,
  PROPx [ka <> nullval; kb <> nullval]
  (LOCALx (hhs3_p6_locals gv L V)
  (SEPx (hhs3_p6_sep gv L FR V
           (itable Tsh (l_ita L) (hhs3_p6_TA3 L V)) (itable Tsh (l_itb L) (hhs3_p6_TB3 L V))
           (peer_rep Tsh (l_pb L) (p_set_slots (hhs3_p6_PB3 V ka) nullval nullval nullval))
           (peer_rep Tsh (l_pa L) (p_set_slots (hhs3_p6_PA4 x25519 V kb) nullval nullval nullval))
           (hhs3_p6_S4 V) (Int64.repr 2) emp emp
           (@data_at_ HCS Tsh t_hsnap (l_snap L)) (hout Tsh 32 (l_first L)) (hout Tsh 32 (l_second L))))).

(* ---------------------------------------------------------------------- *)
(* The returns: everything back to main's stack frame                     *)
(* ---------------------------------------------------------------------- *)

(* main's 32 locals as the stack frame wants them (fn_vars order) *)
Definition hhs3_p6_frame (L: hhs3_loc) : list mpred :=
  [@data_at_ W_handshake Tsh t_dev (l_wa L); @data_at_ W_handshake Tsh t_dev (l_wb L);
   @data_at_ W_handshake Tsh t_itab (l_ita L); @data_at_ W_handshake Tsh t_itab (l_itb L);
   @data_at_ W_handshake Tsh t_ptab (l_pta L); @data_at_ W_handshake Tsh t_ptab (l_ptb L);
   @data_at_ W_handshake Tsh t_peer (l_pb L); @data_at_ W_handshake Tsh t_peer (l_pa L);
   @data_at_ W_handshake Tsh t_mident (l_ia L); @data_at_ W_handshake Tsh t_mident (l_ib L);
   @data_at_ W_handshake Tsh (tarray tuchar 32) (l_rawa L); @data_at_ W_handshake Tsh (tarray tuchar 32) (l_rawb L);
   @data_at_ W_handshake Tsh (tarray tuchar 32) (l_psk L); @data_at_ W_handshake Tsh (tarray tuchar 32) (l_ssa L);
   @data_at_ W_handshake Tsh (tarray tuchar 32) (l_ssb L); @data_at_ W_handshake Tsh (tarray tuchar 32) (l_tmp L);
   @data_at_ W_handshake Tsh (tarray tuchar 12) (l_ts L);
   @data_at_ W_handshake Tsh (tarray tuchar 148) (l_img L); @data_at_ W_handshake Tsh (tarray tuchar 148) (l_imgb L);
   @data_at_ W_handshake Tsh (tarray tuchar 92) (l_rimg L); @data_at_ W_handshake Tsh (tarray tuchar 92) (l_rimgb L);
   @data_at_ W_handshake Tsh t_minit (l_mi L); @data_at_ W_handshake Tsh t_mcinit (l_ci L);
   @data_at_ W_handshake Tsh t_mresp (l_mr L); @data_at_ W_handshake Tsh t_mstate (l_st2 L);
   @data_at_ W_handshake Tsh t_hsnap (l_snap L);
   @data_at_ W_handshake Tsh (tarray tuchar 32) (l_d1 L); @data_at_ W_handshake Tsh (tarray tuchar 32) (l_d2 L);
   @data_at_ W_handshake Tsh (tarray tuchar 32) (l_d1b L); @data_at_ W_handshake Tsh (tarray tuchar 32) (l_d2b L);
   @data_at_ W_handshake Tsh (tarray tuchar 32) (l_first L); @data_at_ W_handshake Tsh (tarray tuchar 32) (l_second L)].

(* the objects of a return point (the messages already freed, the keypairs freed, buffers weakened to
   data_at_): the tables' pools hold exactly the peers' handshake entries, the peers any contents; any shim
   and keypair_counter (= hhs3_p5_free_stmt of phase P5 with kc any) *)
Definition hhs3_p6_free_stmt : Prop :=
  x25519_props x25519 ->
  forall gv L FR R S kc Ta Tb Ea Eb PB PA, hhs3_run_ok R ->
  t_D Ta = [(hs_addr (l_pb L), Tsh, Ea)] -> t_D Tb = [(hs_addr (l_pa L), Tsh, Eb)] ->
  fold_right_sepcon
    (hhs3_setup_sep x25519 R L ++
     [itable Tsh (l_ita L) Ta; itable Tsh (l_itb L) Tb; peer_rep Tsh (l_pb L) PB; peer_rep Tsh (l_pa L) PA;
      hout Tsh 12 (l_ts L); hout Tsh 148 (l_img L); hout Tsh 92 (l_rimg L);
      @data_at_ HCS Tsh t_minit (l_mi L); @data_at_ HCS Tsh t_mcinit (l_ci L);
      @data_at_ HCS Tsh t_mresp (l_mr L); @data_at_ HCS Tsh t_mstate (l_st2 L)] ++
     hhs3_globs gv S kc FR ++ hhs3_scr_tmp L)
  |-- fold_right_sepcon (hhs3_p6_frame L) * TT.

End States.
