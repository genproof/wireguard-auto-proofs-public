(* law create_any: phase F of main (if (op == 0) F0 else F1) cut further, and the
   states inside it.

   F0 = m = malloc(sizeof *m); if (m != NULL) { BODY0 }   (create_initiation, 10 statements)
     F0a = BODY0 0..5  fill_init, init_img(before), bytes_copy(exp, before), draw_real_clock, m_tai64n(ts, ..),
                       r = wg_noise_handshake_create_initiation(m, &p.handshake)        hca5_F0S0 -> hca5_F0S1
     F0b = BODY0 6     if (ia.ok) { the harness's step-by-step model }                   hca5_F0S1 -> hca5_F0S2
     F0c = BODY0 7..9  init_img(img), CHECK(r == ok && bytes_eq(img, exp)), free(m)      hca5_F0S2 -> hca5_SF
   F1 = m__1 = malloc(sizeof *m__1); if (m__1 != NULL) { BODY1 }   (create_response, 8 statements)
     F1a = BODY1 0..3  fill_resp, resp_img(before1), bytes_copy(exp1, before1),
                       r = wg_noise_handshake_create_response(m__1, &p.handshake)       hca5_F1S0 -> hca5_F1S1
     F1b = BODY1 4     if (s.state == CONSUMED_INITIATION) { the harness's model }       hca5_F1S1 -> hca5_F1S2
     F1c = BODY1 5..7  resp_img(img1), CHECK(r == ok && bytes_eq(img1, exp1)), free(m__1) hca5_F1S2 -> hca5_SF
   The malloc, the NULL test and the composition are proved in hca5_F.v.

   Conventions: as hca5_defs.v (shim_state4 gv S w: w fixed; hca5_rest: the kents and the snapshots ps / ds / ss,
   the shim snapshot S0 with the counters of the shim before the call).  CI = ci_res (the kernel's create_initiation: success flag, message, handshake)
   with the shim S1 after draw_real_clock, the drawn ephemeral bytes rr and the table's index idx; the shim
   after the call is hca5_ci_shim.  X = the harness's expectation hca3_init_exp (hca5_model.v) with the index
   u = wg_shim_random_u32 after the call.  Same for create_response (CR = cr_res, hca5_cr_shim, Y =
   hca3_resp_exp).  The agreement X = CI (hca3_init_agree) is only needed in F0c / F1c. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.create_any.hca3_model.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.create_any.hca5_spec.
Require Import WgNoise.proof.harness.create_any.hca5_defs.
Require WgNoise.harness.x_create_any.code.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The cut of F0 / F1                                                      *)
(* ---------------------------------------------------------------------- *)

Definition hca5_F0m : statement :=
  ltac:(let x := eval cbv beta iota delta [hca5_F0] in
        (match hca5_F0 with Ssequence a _ => a | _ => Sskip end) in exact x).
Definition hca5_F0cond : expr :=
  ltac:(let x := eval cbv beta iota delta [hca5_F0] in
        (match hca5_F0 with Ssequence _ (Sifthenelse c _ _) => c | _ => Econst_int Int.zero tint end) in exact x).
Definition hca5_F0body : statement :=
  ltac:(let x := eval cbv beta iota delta [hca5_F0] in
        (match hca5_F0 with Ssequence _ (Sifthenelse _ b _) => b | _ => Sskip end) in exact x).
Lemma hca5_F0_eq : hca5_F0 = Ssequence hca5_F0m (Sifthenelse hca5_F0cond hca5_F0body Sskip).
Proof. reflexivity. Qed.

Definition hca5_F0stmts : list statement :=
  ltac:(let x := eval cbv beta iota delta [hca5_flat_seq hca5_F0body] in (hca5_flat_seq hca5_F0body) in exact x).
Lemma hca5_F0stmts_length : length hca5_F0stmts = 10%nat.
Proof. reflexivity. Qed.
Definition hca5_F0l (i n: nat) : list statement := firstn n (skipn i hca5_F0stmts).

Definition hca5_F0a := ltac:(let x := eval cbv beta iota delta [hca5_F0l hca5_seql firstn skipn hca5_F0stmts] in (hca5_seql (hca5_F0l 0 6)) in exact x).
Definition hca5_F0b := ltac:(let x := eval cbv beta iota delta [hca5_F0l hca5_seql firstn skipn hca5_F0stmts] in (hca5_seql (hca5_F0l 6 1)) in exact x).
Definition hca5_F0c := ltac:(let x := eval cbv beta iota delta [hca5_F0l hca5_seql firstn skipn hca5_F0stmts] in (hca5_seql (hca5_F0l 7 3)) in exact x).

Lemma hca5_F0body_eq :
  hca5_F0body = hca5_seqs (hca5_F0l 0 6) (hca5_seqs (hca5_F0l 6 1) (hca5_seql (hca5_F0l 7 3))).
Proof. reflexivity. Qed.
Lemma hca5_F0segs_eq :
  hca5_F0a = hca5_seql (hca5_F0l 0 6) /\ hca5_F0b = hca5_seql (hca5_F0l 6 1) /\
  hca5_F0c = hca5_seql (hca5_F0l 7 3).
Proof. repeat split. Qed.

Definition hca5_F1m : statement :=
  ltac:(let x := eval cbv beta iota delta [hca5_F1] in
        (match hca5_F1 with Ssequence a _ => a | _ => Sskip end) in exact x).
Definition hca5_F1cond : expr :=
  ltac:(let x := eval cbv beta iota delta [hca5_F1] in
        (match hca5_F1 with Ssequence _ (Sifthenelse c _ _) => c | _ => Econst_int Int.zero tint end) in exact x).
Definition hca5_F1body : statement :=
  ltac:(let x := eval cbv beta iota delta [hca5_F1] in
        (match hca5_F1 with Ssequence _ (Sifthenelse _ b _) => b | _ => Sskip end) in exact x).
Lemma hca5_F1_eq : hca5_F1 = Ssequence hca5_F1m (Sifthenelse hca5_F1cond hca5_F1body Sskip).
Proof. reflexivity. Qed.

Definition hca5_F1stmts : list statement :=
  ltac:(let x := eval cbv beta iota delta [hca5_flat_seq hca5_F1body] in (hca5_flat_seq hca5_F1body) in exact x).
Lemma hca5_F1stmts_length : length hca5_F1stmts = 8%nat.
Proof. reflexivity. Qed.
Definition hca5_F1l (i n: nat) : list statement := firstn n (skipn i hca5_F1stmts).

Definition hca5_F1a := ltac:(let x := eval cbv beta iota delta [hca5_F1l hca5_seql firstn skipn hca5_F1stmts] in (hca5_seql (hca5_F1l 0 4)) in exact x).
Definition hca5_F1b := ltac:(let x := eval cbv beta iota delta [hca5_F1l hca5_seql firstn skipn hca5_F1stmts] in (hca5_seql (hca5_F1l 4 1)) in exact x).
Definition hca5_F1c := ltac:(let x := eval cbv beta iota delta [hca5_F1l hca5_seql firstn skipn hca5_F1stmts] in (hca5_seql (hca5_F1l 5 3)) in exact x).

Lemma hca5_F1body_eq :
  hca5_F1body = hca5_seqs (hca5_F1l 0 4) (hca5_seqs (hca5_F1l 4 1) (hca5_seql (hca5_F1l 5 3))).
Proof. reflexivity. Qed.
Lemma hca5_F1segs_eq :
  hca5_F1a = hca5_seql (hca5_F1l 0 4) /\ hca5_F1b = hca5_seql (hca5_F1l 4 1) /\
  hca5_F1c = hca5_seql (hca5_F1l 5 3).
Proof. repeat split. Qed.

(* ---------------------------------------------------------------------- *)
(* The kernel's results and the harness's expectations                     *)
(* ---------------------------------------------------------------------- *)

Definition t_init_W := Tstruct HC._message_handshake_initiation noattr.
Definition t_resp_W := Tstruct HC._message_handshake_response noattr.

(* the shim after create_initiation / create_response (their specifications' post) *)
Definition hca5_ci_shim (D: device) (S: shim) (rr: list byte) (b: bool) (idx: int) : shim :=
  if id_has (d_id D) then (if b then shim_u32 (shim_draw S rr) idx else shim_draw S rr) else S.
Definition hca5_cr_shim (P: peer) (S: shim) (rr: list byte) (b: bool) (idx: int) : shim :=
  if Int.eq (hs_state (p_hs P)) HS_CONSUMED_INITIATION
  then (if b then shim_u32 (shim_draw S rr) idx else shim_draw S rr) else S.

Section F.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.

Definition hca5_CI (R: hca5_run) (L: hca5_loc) (P: peer) (M: init_msg) (S1: shim) (rr: list byte) (idx: int)
  : bool * init_msg * handshake :=
  ci_res x25519 aead_enc (hca5_D x25519 R L) P M S1 rr idx.

Definition hca5_CIshim (R: hca5_run) (L: hca5_loc) (P: peer) (M: init_msg) (S1: shim) (rr: list byte) (idx: int)
  : shim :=
  hca5_ci_shim (hca5_D x25519 R L) S1 rr (fst (fst (hca5_CI R L P M S1 rr idx))) idx.

(* the harness's expectation after the op == 0 block (u = wg_shim_random_u32 after the call) *)
Definition hca5_X (R: hca5_run) (L: hca5_loc) (P: peer) (M: init_msg) (S1: shim) (rr: list byte) (idx: int)
  : bool * list byte * handshake :=
  hca3_init_exp x25519 aead_enc (mi_ok (hca5_I x25519 R)) (id_pub (d_id (hca5_D x25519 R L))) (p_hs P)
    (init_bytes M) rr (tai64n (s_rsec S1) (s_rnsec S1)) (s_u32 (hca5_CIshim R L P M S1 rr idx)).

Definition hca5_CR (P: peer) (M: resp_msg) (rr: list byte) (idx: int) : bool * resp_msg * handshake :=
  cr_res x25519 aead_enc P M rr idx.

Definition hca5_CRshim (P: peer) (M: resp_msg) (S1: shim) (rr: list byte) (idx: int) : shim :=
  hca5_cr_shim P S1 rr (fst (fst (hca5_CR P M rr idx))) idx.

Definition hca5_Y (P: peer) (M: resp_msg) (S1: shim) (rr: list byte) (idx: int) : bool * list byte * handshake :=
  hca3_resp_exp x25519 aead_enc (p_hs P) (resp_bytes M) rr (s_u32 (hca5_CRshim P M S1 rr idx)).

End F.

(* ---------------------------------------------------------------------- *)
(* The states inside F0                                                    *)
(* ---------------------------------------------------------------------- *)

Section F0States.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.

(* BODY0's start: hca5_SEo 0 and m = the (non-NULL) malloc'd message, uninitialised *)
Definition hca5_F0S0 (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) (m: val) : environ -> mpred :=
  EX R: hca5_run, EX S: shim, EX P: peer, EX T: tstate, EX KS: list kdraw, EX E: entry,
  PROPx [hca5_run_ok R; hca5_pok L P (map kd_addr KS); hca5_pool (l_p L) KS T; t_entry T (hs_addr (l_p L)) = Some E;
         m <> nullval]
  (LOCALx ([temp HC._m m; temp HC._op (Vint (Int.repr 0)); temp HC._ok (Vint Int.zero);
            temp HC._kes (kents_head KS); temp HC._refs0 (Vint (p_refs P))] ++ hca5_lvars gv L)
  (SEPx (hca5_world x25519 R L ++
         [itable Tsh (l_ita L) T; peer_rep Tsh (l_p L) P; hca5_rest x25519 L R P T KS S w;
          @data_at HCS Tsh t_hsnap (hsnap_val (snap_of T (hs_addr (l_p L)) E (p_hs P))) (l_s L);
          @data_at HCS Tsh t_hsnap (hsnap_val (snap_of T (hs_addr (l_p L)) E (p_hs P))) (l_x L);
          hca5_tok t_init_W m; @data_at_ W Ews t_init_W m] ++
         hca5_globs gv S w FR ++ hca5_scr0 L ++ hca5_scr L))).

(* after F0a: M = the pre-filled message, before = exp = its image, ts = TAI64N of the real clock (shim S1
   after draw_real_clock), r = the kernel's result CI (message, handshake, table, shim) *)
Definition hca5_F0S1 (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) (m: val) : environ -> mpred :=
  EX R: hca5_run, EX P: peer, EX T: tstate, EX KS: list kdraw, EX E: entry,
  EX M: init_msg, EX S1: shim, EX rr: list byte, EX idx: int, EX S0: shim,
  PROPx [hca5_run_ok R; hca5_pok L P (map kd_addr KS); hca5_pool (l_p L) KS T; t_entry T (hs_addr (l_p L)) = Some E;
         m <> nullval; im_ok M; Zlength rr = 32; hca5_cnt S1 = hca5_cnt S0;
         fst (fst (hca5_CI x25519 aead_enc R L P M S1 rr idx)) = true -> t_fresh T (hs_addr (l_p L)) idx]
  (LOCALx ([temp HC._m m; temp HC._r (Val.of_bool (fst (fst (hca5_CI x25519 aead_enc R L P M S1 rr idx))));
            temp HC._op (Vint (Int.repr 0)); temp HC._ok (Vint Int.zero);
            temp HC._kes (kents_head KS); temp HC._refs0 (Vint (p_refs P))] ++ hca5_lvars gv L)
  (SEPx (hca5_world x25519 R L ++
         [itable Tsh (l_ita L) (if fst (fst (hca5_CI x25519 aead_enc R L P M S1 rr idx))
                                then t_insert T (hs_addr (l_p L)) idx else T);
          peer_rep Tsh (l_p L) (p_set_hs P (snd (hca5_CI x25519 aead_enc R L P M S1 rr idx)));
          hca5_rest x25519 L R P T KS S0 w;
          @data_at HCS Tsh t_hsnap (hsnap_val (snap_of T (hs_addr (l_p L)) E (p_hs P))) (l_s L);
          @data_at HCS Tsh t_hsnap (hsnap_val (snap_of T (hs_addr (l_p L)) E (p_hs P))) (l_x L);
          hca5_tok t_init_W m; init_rep Ews m (snd (fst (hca5_CI x25519 aead_enc R L P M S1 rr idx)));
          hbytes Tsh (init_bytes M) (l_before L); hbytes Tsh (init_bytes M) (l_exp L);
          hbytes Tsh (tai64n (s_rsec S1) (s_rnsec S1)) (l_ts L)] ++
         hca5_globs gv (hca5_CIshim x25519 aead_enc R L P M S1 rr idx) w FR ++ hca5_scr0 L ++
         [@data_at_ HCS Tsh t_mstate (l_st L);
          hout Tsh 32 (l_key L); hout Tsh 32 (l_dh L); hout Tsh 32 (l_eph L); hout Tsh 32 (l_E L);
          hout Tsh 1 (l_nothing L); hout Tsh 148 (l_img L);
          hout Tsh 92 (l_before1 L); hout Tsh 92 (l_exp1 L); hout Tsh 92 (l_img1 L)]))).

(* after F0b: ok, exp and x are the harness's expectation X; st, key, dh, eph, E, before, ts back to scratch *)
Definition hca5_F0S2 (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) (m: val) : environ -> mpred :=
  EX R: hca5_run, EX P: peer, EX T: tstate, EX KS: list kdraw, EX E: entry,
  EX M: init_msg, EX S1: shim, EX rr: list byte, EX idx: int, EX S0: shim,
  PROPx [hca5_run_ok R; hca5_pok L P (map kd_addr KS); hca5_pool (l_p L) KS T; t_entry T (hs_addr (l_p L)) = Some E;
         m <> nullval; im_ok M; Zlength rr = 32; hca5_cnt S1 = hca5_cnt S0;
         fst (fst (hca5_CI x25519 aead_enc R L P M S1 rr idx)) = true -> t_fresh T (hs_addr (l_p L)) idx]
  (LOCALx ([temp HC._m m; temp HC._r (Val.of_bool (fst (fst (hca5_CI x25519 aead_enc R L P M S1 rr idx))));
            temp HC._ok (Vint (if fst (fst (hca5_X x25519 aead_enc R L P M S1 rr idx)) then Int.one else Int.zero));
            temp HC._kes (kents_head KS); temp HC._refs0 (Vint (p_refs P))] ++ hca5_lvars gv L)
  (SEPx (hca5_world x25519 R L ++
         [itable Tsh (l_ita L) (if fst (fst (hca5_CI x25519 aead_enc R L P M S1 rr idx))
                                then t_insert T (hs_addr (l_p L)) idx else T);
          peer_rep Tsh (l_p L) (p_set_hs P (snd (hca5_CI x25519 aead_enc R L P M S1 rr idx)));
          hca5_rest x25519 L R P T KS S0 w;
          @data_at_ HCS Tsh t_hsnap (l_s L);
          @data_at HCS Tsh t_hsnap
            (hsnap_val (snap_of T (hs_addr (l_p L)) E (snd (hca5_X x25519 aead_enc R L P M S1 rr idx)))) (l_x L);
          hca5_tok t_init_W m; init_rep Ews m (snd (fst (hca5_CI x25519 aead_enc R L P M S1 rr idx)));
          hbytes Tsh (snd (fst (hca5_X x25519 aead_enc R L P M S1 rr idx))) (l_exp L)] ++
         hca5_globs gv (hca5_CIshim x25519 aead_enc R L P M S1 rr idx) w FR ++ hca5_scr0 L ++
         [@data_at_ HCS Tsh t_mstate (l_st L);
          hout Tsh 32 (l_key L); hout Tsh 32 (l_dh L); hout Tsh 32 (l_eph L); hout Tsh 32 (l_E L);
          hout Tsh 12 (l_ts L); hout Tsh 1 (l_nothing L);
          hout Tsh 148 (l_before L); hout Tsh 148 (l_img L);
          hout Tsh 92 (l_before1 L); hout Tsh 92 (l_exp1 L); hout Tsh 92 (l_img1 L)]))).

End F0States.

(* ---------------------------------------------------------------------- *)
(* The states inside F1                                                    *)
(* ---------------------------------------------------------------------- *)

Section F1States.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.

(* BODY1's start: hca5_SEo 1 and m__1 = the (non-NULL) malloc'd message, uninitialised *)
Definition hca5_F1S0 (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) (m: val) : environ -> mpred :=
  EX R: hca5_run, EX S: shim, EX P: peer, EX T: tstate, EX KS: list kdraw, EX E: entry,
  PROPx [hca5_run_ok R; hca5_pok L P (map kd_addr KS); hca5_pool (l_p L) KS T; t_entry T (hs_addr (l_p L)) = Some E;
         m <> nullval]
  (LOCALx ([temp HC._m__1 m; temp HC._op (Vint (Int.repr 1)); temp HC._ok (Vint Int.zero);
            temp HC._kes (kents_head KS); temp HC._refs0 (Vint (p_refs P))] ++ hca5_lvars gv L)
  (SEPx (hca5_world x25519 R L ++
         [itable Tsh (l_ita L) T; peer_rep Tsh (l_p L) P; hca5_rest x25519 L R P T KS S w;
          @data_at HCS Tsh t_hsnap (hsnap_val (snap_of T (hs_addr (l_p L)) E (p_hs P))) (l_s L);
          @data_at HCS Tsh t_hsnap (hsnap_val (snap_of T (hs_addr (l_p L)) E (p_hs P))) (l_x L);
          hca5_tok t_resp_W m; @data_at_ W Ews t_resp_W m] ++
         hca5_globs gv S w FR ++ hca5_scr0 L ++ hca5_scr L))).

(* after F1a: M = the pre-filled message, before1 = exp1 = its image, r = the kernel's result CR *)
Definition hca5_F1S1 (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) (m: val) : environ -> mpred :=
  EX R: hca5_run, EX P: peer, EX T: tstate, EX KS: list kdraw, EX E: entry,
  EX M: resp_msg, EX S1: shim, EX rr: list byte, EX idx: int, EX S0: shim,
  PROPx [hca5_run_ok R; hca5_pok L P (map kd_addr KS); hca5_pool (l_p L) KS T; t_entry T (hs_addr (l_p L)) = Some E;
         m <> nullval; rm_ok M; Zlength rr = 32; hca5_cnt S1 = hca5_cnt S0;
         fst (fst (hca5_CR x25519 aead_enc P M rr idx)) = true -> t_fresh T (hs_addr (l_p L)) idx]
  (LOCALx ([temp HC._m__1 m; temp HC._r (Val.of_bool (fst (fst (hca5_CR x25519 aead_enc P M rr idx))));
            temp HC._op (Vint (Int.repr 1)); temp HC._ok (Vint Int.zero);
            temp HC._kes (kents_head KS); temp HC._refs0 (Vint (p_refs P))] ++ hca5_lvars gv L)
  (SEPx (hca5_world x25519 R L ++
         [itable Tsh (l_ita L) (if fst (fst (hca5_CR x25519 aead_enc P M rr idx))
                                then t_insert T (hs_addr (l_p L)) idx else T);
          peer_rep Tsh (l_p L) (p_set_hs P (snd (hca5_CR x25519 aead_enc P M rr idx)));
          hca5_rest x25519 L R P T KS S0 w;
          @data_at HCS Tsh t_hsnap (hsnap_val (snap_of T (hs_addr (l_p L)) E (p_hs P))) (l_s L);
          @data_at HCS Tsh t_hsnap (hsnap_val (snap_of T (hs_addr (l_p L)) E (p_hs P))) (l_x L);
          hca5_tok t_resp_W m; resp_rep Ews m (snd (fst (hca5_CR x25519 aead_enc P M rr idx)));
          hbytes Tsh (resp_bytes M) (l_before1 L); hbytes Tsh (resp_bytes M) (l_exp1 L)] ++
         hca5_globs gv (hca5_CRshim x25519 aead_enc P M S1 rr idx) w FR ++ hca5_scr0 L ++
         [@data_at_ HCS Tsh t_mstate (l_st L);
          hout Tsh 32 (l_key L); hout Tsh 32 (l_dh L); hout Tsh 32 (l_eph L); hout Tsh 32 (l_E L);
          hout Tsh 12 (l_ts L); hout Tsh 1 (l_nothing L);
          hout Tsh 148 (l_before L); hout Tsh 148 (l_exp L); hout Tsh 148 (l_img L);
          hout Tsh 92 (l_img1 L)]))).

(* after F1b: ok, exp1 and x are the harness's expectation Y; the other scratch locals back to scratch *)
Definition hca5_F1S2 (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) (m: val) : environ -> mpred :=
  EX R: hca5_run, EX P: peer, EX T: tstate, EX KS: list kdraw, EX E: entry,
  EX M: resp_msg, EX S1: shim, EX rr: list byte, EX idx: int, EX S0: shim,
  PROPx [hca5_run_ok R; hca5_pok L P (map kd_addr KS); hca5_pool (l_p L) KS T; t_entry T (hs_addr (l_p L)) = Some E;
         m <> nullval; rm_ok M; Zlength rr = 32; hca5_cnt S1 = hca5_cnt S0;
         fst (fst (hca5_CR x25519 aead_enc P M rr idx)) = true -> t_fresh T (hs_addr (l_p L)) idx]
  (LOCALx ([temp HC._m__1 m; temp HC._r (Val.of_bool (fst (fst (hca5_CR x25519 aead_enc P M rr idx))));
            temp HC._ok (Vint (if fst (fst (hca5_Y x25519 aead_enc P M S1 rr idx)) then Int.one else Int.zero));
            temp HC._kes (kents_head KS); temp HC._refs0 (Vint (p_refs P))] ++ hca5_lvars gv L)
  (SEPx (hca5_world x25519 R L ++
         [itable Tsh (l_ita L) (if fst (fst (hca5_CR x25519 aead_enc P M rr idx))
                                then t_insert T (hs_addr (l_p L)) idx else T);
          peer_rep Tsh (l_p L) (p_set_hs P (snd (hca5_CR x25519 aead_enc P M rr idx)));
          hca5_rest x25519 L R P T KS S0 w;
          @data_at_ HCS Tsh t_hsnap (l_s L);
          @data_at HCS Tsh t_hsnap
            (hsnap_val (snap_of T (hs_addr (l_p L)) E (snd (hca5_Y x25519 aead_enc P M S1 rr idx)))) (l_x L);
          hca5_tok t_resp_W m; resp_rep Ews m (snd (fst (hca5_CR x25519 aead_enc P M rr idx)));
          hbytes Tsh (snd (fst (hca5_Y x25519 aead_enc P M S1 rr idx))) (l_exp1 L)] ++
         hca5_globs gv (hca5_CRshim x25519 aead_enc P M S1 rr idx) w FR ++ hca5_scr0 L ++
         [@data_at_ HCS Tsh t_mstate (l_st L);
          hout Tsh 32 (l_key L); hout Tsh 32 (l_dh L); hout Tsh 32 (l_eph L); hout Tsh 32 (l_E L);
          hout Tsh 12 (l_ts L); hout Tsh 1 (l_nothing L);
          hout Tsh 148 (l_before L); hout Tsh 148 (l_exp L); hout Tsh 148 (l_img L);
          hout Tsh 92 (l_before1 L); hout Tsh 92 (l_img1 L)]))).

End F1States.
