(* law handshake: main's phase P2 (statements 37..65) cut into five segments, and the states between
   them.

   Segments (statement indices of main's body):
     A = 37..42  fill_init, init_img(img_before), draw_real_clock, m_tai64n, hs_take, create_initiation
                 S1 -> SA
     B = 43..45  if (!ia.ok) {hs_same CHECK, init_img(img), image CHECK}; if (ia.ok) {m_create_initiation,
                 CHECK(ok1 == mok), all_ok}; if (!ok1) {free; free; return 0}                SA -> SB
     C = 46..50  init_img(img), CHECKs: type, sender index (= random_u32 = the entry's index), table
                 (table_has, table_index_unique, table_len), entry type and peer            SB -> SC
     D = 51..58  CHECKs: message fields = mi's, macs untouched, handshake state / hash / ck / eph_priv = the
                 model's, the other handshake fields = the snapshot's                       SC -> SC
     E = 59..65  add_mac, m_label_key, m_mac(img + 116), bytes_set(img + 132), init_img(img_before),
                 image CHECK, cookie CHECK                                                  SC -> S2
   Pure facts taken as hypotheses by the segments (proved in their own files):
     hhs3_p2_agree_stmt  the kernel's create_initiation_model vs the harness's m_create_initiation_model
     hhs3_p2_free_stmt   the early return of B: every local back to main's stack frame. *)
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

Definition hhs3_p2_A := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 37 6)) in exact x).
Definition hhs3_p2_B := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 43 3)) in exact x).
Definition hhs3_p2_C := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 46 5)) in exact x).
Definition hhs3_p2_D := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 51 8)) in exact x).
Definition hhs3_p2_E := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 59 7)) in exact x).

Lemma hhs3_p2_split :
  hhs3_l 37 29 = hhs3_l 37 6 ++ hhs3_l 43 3 ++ hhs3_l 46 5 ++ hhs3_l 51 8 ++ hhs3_l 59 7.
Proof. reflexivity. Qed.

Lemma hhs3_p2_segs_eq :
  hhs3_p2_A = hhs3_seql (hhs3_l 37 6) /\ hhs3_p2_B = hhs3_seql (hhs3_l 43 3) /\
  hhs3_p2_C = hhs3_seql (hhs3_l 46 5) /\ hhs3_p2_D = hhs3_seql (hhs3_l 51 8) /\
  hhs3_p2_E = hhs3_seql (hhs3_l 59 7).
Proof. repeat split. Qed.

Lemma hhs3_p2_cut {Espec: OracleKind} {cs: compspecs} Delta P Q R l1 l2 :
  l1 <> [] -> l2 <> [] ->
  semax Delta P (hhs3_seql l1) (overridePost Q R) -> semax Delta Q (hhs3_seql l2) R ->
  semax Delta P (hhs3_seql (l1 ++ l2)) R.
Proof.
  intros H1 H2 S1 S2.
  apply (semax_unfold_Ssequence (Ssequence (hhs3_seql l1) (hhs3_seql l2))).
  - assert (H3: l1 ++ l2 <> []) by (destruct l1; [congruence | discriminate]).
    simpl. rewrite (hhs3_unfold_seql (l1 ++ l2) H3), (hhs3_unfold_seql l1 H1), (hhs3_unfold_seql l2 H2).
    rewrite map_app, concat_app. reflexivity.
  - eapply semax_seq; eauto.
Qed.

(* ---------------------------------------------------------------------- *)
(* The states                                                              *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.

(* the scratch locals during P2: img_before = the image of the filled message M0, snap = pb's handshake
   before create_initiation (its entry hhs3_EB, unhashed in the table hhs3_TA0); the others any *)
Definition hhs3_p2_scr (R: hhs3_run) (L: hhs3_loc) (I: hhs3_ini) : list mpred :=
  [hout Tsh 32 (l_tmp L); hbytes Tsh (init_bytes (i_M0 I)) (l_imgb L); hout Tsh 92 (l_rimgb L);
   @data_at HCS Tsh t_hsnap (hsnap_val (snap_of (hhs3_TA0 L) (hs_addr (l_pb L)) (hhs3_EB L)
                                          (p_hs (hhs3_PB0 x25519 R L)))) (l_snap L);
   hout Tsh 32 (l_d1 L); hout Tsh 32 (l_d2 L); hout Tsh 32 (l_d1b L); hout Tsh 32 (l_d2b L);
   hout Tsh 32 (l_first L); hout Tsh 32 (l_second L)].

(* after A: M0 filled (img_before = its image), the real clock (sec, nsec), ts = its TAI64N, the snapshot
   taken, create_initiation returned ok1 with message M and handshake H (= hhs3_ci, hidden behind variables);
   the shim's log = the drawn r when A has an identity, its u32 = the drawn index at success *)
Definition hhs3_p2_SA (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred :=
  EX R: hhs3_run, EX S: shim, EX m1: val, EX m2: val, EX a0: int64, EX f0: int64, EX l0: int64,
  EX I: hhs3_ini, EX ok1: bool, EX M: init_msg, EX H: handshake,
  PROPx [hhs3_run_ok R; hhs3_cnt S a0 f0 l0; im_ok (i_M0 I); Zlength (i_r I) = 32;
         0 <= i_nsec I < 1000000000;
         hhs3_ci x25519 aead_enc R L I = (ok1, M, H);
         ok1 = true -> t_fresh (hhs3_TA0 L) (hs_addr (l_pb L)) (i_idx I);
         mi_ok (hhs3_IA x25519 R) = true -> s_log S = i_r I;
         ok1 = true -> s_u32 S = i_idx I]
  (LOCALx ([temp HC._m1 m1; temp HC._m2 m2; temp HC._ok1 (Val.of_bool ok1);
            temp HC._all_ok (Vint (if hhs3_ok1 x25519 R then Int.one else Int.zero))] ++
           hhs3_cnt_temps a0 f0 l0 ++ hhs3_lvars gv L)
  (SEPx (hhs3_setup_sep x25519 R L ++
         [itable Tsh (l_ita L) (if ok1 then hhs3_TA1 L I else hhs3_TA0 L); itable Tsh (l_itb L) (hhs3_TB0 L);
          peer_rep Tsh (l_pb L) (p_set_hs (hhs3_PB0 x25519 R L) H); peer_rep Tsh (l_pa L) (hhs3_PA0 x25519 R L);
          hhs3_tok t_init m1; init_rep Ews m1 M;
          hhs3_tok t_resp m2; @data_at_ Noise.CS Ews t_resp m2;
          hbytes Tsh (hhs3_ts I) (l_ts L); hout Tsh 148 (l_img L); hout Tsh 92 (l_rimg L);
          @data_at_ HCS Tsh t_minit (l_mi L); @data_at_ HCS Tsh t_mcinit (l_ci L);
          @data_at_ HCS Tsh t_mresp (l_mr L); @data_at_ HCS Tsh t_mstate (l_st2 L)] ++
         hhs3_globs gv S Int64.zero FR ++ hhs3_p2_scr R L I))).

(* the SEP of SB / SC (after create_initiation succeeded and the model agreed); img_item = the img buffer *)
Definition hhs3_p2_sepB (gv: globals) (L: hhs3_loc) (FR: mpred) (R: hhs3_run) (S: shim) (m1 m2: val)
  (I: hhs3_ini) (M1: init_msg) (H1: handshake)
  (MI: list byte * list byte * list byte * list byte * list byte * list byte) (img_item: mpred) : list mpred :=
  hhs3_setup_sep x25519 R L ++
  [itable Tsh (l_ita L) (hhs3_TA1 L I); itable Tsh (l_itb L) (hhs3_TB0 L);
   peer_rep Tsh (l_pb L) (p_set_hs (hhs3_PB0 x25519 R L) H1); peer_rep Tsh (l_pa L) (hhs3_PA0 x25519 R L);
   hhs3_tok t_init m1; init_rep Ews m1 M1;
   hhs3_tok t_resp m2; @data_at_ Noise.CS Ews t_resp m2;
   hbytes Tsh (hhs3_ts I) (l_ts L); img_item; hout Tsh 92 (l_rimg L);
   (let '(E, encs, enct, ep, ck, h) := MI in @data_at HCS Tsh t_minit (minit_val E encs enct ep ck h) (l_mi L));
   @data_at_ HCS Tsh t_mcinit (l_ci L); @data_at_ HCS Tsh t_mresp (l_mr L);
   @data_at_ HCS Tsh t_mstate (l_st2 L)] ++
  hhs3_globs gv S Int64.zero FR ++ hhs3_p2_scr R L I.

(* after B: create_initiation succeeded (M1, H1), the model too (MI), all_ok = hhs3_ok2; img not written *)
Definition hhs3_p2_SB (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred :=
  EX R: hhs3_run, EX S: shim, EX m1: val, EX m2: val, EX a0: int64, EX f0: int64, EX l0: int64,
  EX I: hhs3_ini, EX M1: init_msg, EX H1: handshake,
  EX MI: list byte * list byte * list byte * list byte * list byte * list byte,
  PROPx [hhs3_run_ok R; hhs3_cnt S a0 f0 l0; hhs3_after_init x25519 aead_enc R L I M1 H1 MI;
         s_u32 S = i_idx I]
  (LOCALx ([temp HC._m1 m1; temp HC._m2 m2;
            temp HC._all_ok (Vint (if hhs3_ok2 x25519 R I then Int.one else Int.zero))] ++
           hhs3_cnt_temps a0 f0 l0 ++ hhs3_lvars gv L)
  (SEPx (hhs3_p2_sepB gv L FR R S m1 m2 I M1 H1 MI (hout Tsh 148 (l_img L))))).

(* after C (and after D): img = the image of M1 *)
Definition hhs3_p2_SC (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred :=
  EX R: hhs3_run, EX S: shim, EX m1: val, EX m2: val, EX a0: int64, EX f0: int64, EX l0: int64,
  EX I: hhs3_ini, EX M1: init_msg, EX H1: handshake,
  EX MI: list byte * list byte * list byte * list byte * list byte * list byte,
  PROPx [hhs3_run_ok R; hhs3_cnt S a0 f0 l0; hhs3_after_init x25519 aead_enc R L I M1 H1 MI;
         s_u32 S = i_idx I]
  (LOCALx ([temp HC._m1 m1; temp HC._m2 m2;
            temp HC._all_ok (Vint (if hhs3_ok2 x25519 R I then Int.one else Int.zero))] ++
           hhs3_cnt_temps a0 f0 l0 ++ hhs3_lvars gv L)
  (SEPx (hhs3_p2_sepB gv L FR R S m1 m2 I M1 H1 MI (hbytes Tsh (init_bytes M1) (l_img L))))).

(* ---------------------------------------------------------------------- *)
(* Pure: the kernel's create_initiation vs the harness's model             *)
(* ---------------------------------------------------------------------- *)

(* when A has an identity: create_initiation succeeds exactly when m_create_initiation does, and then the
   message and the handshake are the model's (clamp r is never zero; precomputed = m_precomputed_model;
   memneq_bool ss zeros32 = negb (is_zero ss) for |ss| = 32) *)
Definition hhs3_p2_agree_stmt : Prop :=
  x25519_props x25519 ->
  forall R L I, hhs3_run_ok R -> Zlength (i_r I) = 32 -> mi_ok (hhs3_IA x25519 R) = true ->
  match hhs3_mi x25519 aead_enc R L I with
  | Some (E, encs, enct, ep, ck, h) =>
      hhs3_ci x25519 aead_enc R L I =
        (true, mkIM (Int.repr 1) (i_idx I) E encs enct (im_mac1 (i_M0 I)) (im_mac2 (i_M0 I)),
         hs_set_state (hs_set_ckh (hs_set_eph (p_hs (hhs3_PB0 x25519 R L)) ep) ck h) HS_CREATED_INITIATION)
  | None => fst (fst (hhs3_ci x25519 aead_enc R L I)) = false
  end.

(* ---------------------------------------------------------------------- *)
(* B's early return: everything back to main's stack frame                 *)
(* ---------------------------------------------------------------------- *)

(* main's 32 locals as the stack frame wants them (fn_vars order) *)
Definition hhs3_p2_frame (L: hhs3_loc) : list mpred :=
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

(* the objects of a return point (the messages already freed; buffers weakened to data_at_): the tables'
   pools hold exactly the peers' handshake entries, the peers any contents *)
Definition hhs3_p2_free_stmt : Prop :=
  x25519_props x25519 ->
  forall gv L FR R S Ta Tb Ea Eb PB PA, hhs3_run_ok R ->
  t_D Ta = [(hs_addr (l_pb L), Tsh, Ea)] -> t_D Tb = [(hs_addr (l_pa L), Tsh, Eb)] ->
  fold_right_sepcon
    (hhs3_setup_sep x25519 R L ++
     [itable Tsh (l_ita L) Ta; itable Tsh (l_itb L) Tb; peer_rep Tsh (l_pb L) PB; peer_rep Tsh (l_pa L) PA;
      hout Tsh 12 (l_ts L); hout Tsh 148 (l_img L); hout Tsh 92 (l_rimg L);
      @data_at_ HCS Tsh t_minit (l_mi L); @data_at_ HCS Tsh t_mcinit (l_ci L);
      @data_at_ HCS Tsh t_mresp (l_mr L); @data_at_ HCS Tsh t_mstate (l_st2 L)] ++
     hhs3_globs gv S Int64.zero FR ++ hhs3_scr_tmp L)
  |-- fold_right_sepcon (hhs3_p2_frame L) * TT.

End States.
