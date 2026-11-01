(* law handshake: main's phase P1 (statements 0..36) cut into seven segments, and the states between
   them.

   Segments (statement indices of main's body):
     A =  0.. 9  boot clock, ratelimit_allow, wg_noise_init, raw_a / raw_b, use_psk, psk, allocs0/frees0/fails0
                 S0 -> SA
     B = 10..13  setup_device x2, m_identity_of x2                                       SA -> SB
     C = 14..20  identity CHECKs, m_static_public_field x2 + CHECKs                      SB -> SB
     D = 21..22  setup_peer x2 (+ the handshake entries into the index tables' pools)    SB -> SD
     E = 23..27  m_precomputed x2, precomputed / psk CHECKs                              SD -> SE
     F = 28..32  m_label_key x2 + cookie-key CHECKs, state CHECK                         SE -> SE
     G = 33..36  the two mallocs (NULL: free both, return), all_ok                       SE -> S1
   The early return of G frees nothing but the messages: the locals go back to the stack frame
   (hhs3_p1_free_stmt, proved separately). *)
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

Definition hhs3_p1_A := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 0 10)) in exact x).
Definition hhs3_p1_B := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 10 4)) in exact x).
Definition hhs3_p1_C := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 14 7)) in exact x).
Definition hhs3_p1_D := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 21 2)) in exact x).
Definition hhs3_p1_E := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 23 5)) in exact x).
Definition hhs3_p1_F := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 28 5)) in exact x).
Definition hhs3_p1_G := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 33 4)) in exact x).

Lemma hhs3_p1_split :
  hhs3_l 0 37 = hhs3_l 0 10 ++ hhs3_l 10 4 ++ hhs3_l 14 7 ++ hhs3_l 21 2 ++ hhs3_l 23 5 ++ hhs3_l 28 5 ++
                hhs3_l 33 4.
Proof. reflexivity. Qed.

Lemma hhs3_p1_segs_eq :
  hhs3_p1_A = hhs3_seql (hhs3_l 0 10) /\ hhs3_p1_B = hhs3_seql (hhs3_l 10 4) /\
  hhs3_p1_C = hhs3_seql (hhs3_l 14 7) /\ hhs3_p1_D = hhs3_seql (hhs3_l 21 2) /\
  hhs3_p1_E = hhs3_seql (hhs3_l 23 5) /\ hhs3_p1_F = hhs3_seql (hhs3_l 28 5) /\
  hhs3_p1_G = hhs3_seql (hhs3_l 33 4).
Proof. repeat split. Qed.

Lemma hhs3_p1_cut {Espec: OracleKind} {cs: compspecs} Delta P Q R l1 l2 :
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

(* the buffers P1 does not touch (besides the scratch locals hhs3_scr_tmp) *)
Definition hhs3_p1_rest (L: hhs3_loc) : list mpred :=
  [hout Tsh 12 (l_ts L); hout Tsh 148 (l_img L); hout Tsh 92 (l_rimg L);
   @data_at_ HCS Tsh t_minit (l_mi L); @data_at_ HCS Tsh t_mcinit (l_ci L);
   @data_at_ HCS Tsh t_mresp (l_mr L); @data_at_ HCS Tsh t_mstate (l_st2 L)].

(* after A: the boot clock (s_boot S, < 2^62), noise.c's globals initialised, raw keys and psk drawn (psk zero
   without use_psk), allocs0 / frees0 / fails0 = the shim's counters *)
Definition hhs3_p1_SA (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred :=
  EX rawa: list byte, EX rawb: list byte, EX psk: list byte, EX up: bool, EX S: shim,
  EX a0: int64, EX f0: int64, EX l0: int64,
  PROPx [Zlength rawa = 32; Zlength rawb = 32; Zlength psk = 32; up = false -> psk = zeros32;
         0 <= Int64.unsigned (s_boot S) < 2 ^ 62; hhs3_cnt S a0 f0 l0]
  (LOCALx (temp HC._use_psk (Vint (if up then Int.one else Int.zero)) :: hhs3_cnt_temps a0 f0 l0 ++
           hhs3_lvars gv L)
  (SEPx ([@data_at_ Noise.CS Tsh t_dev (l_wa L); @data_at_ Noise.CS Tsh t_dev (l_wb L);
          @data_at_ Noise.CS Tsh t_itab (l_ita L); @data_at_ Noise.CS Tsh t_itab (l_itb L);
          @data_at_ Noise.CS Tsh t_ptab (l_pta L); @data_at_ Noise.CS Tsh t_ptab (l_ptb L);
          @data_at_ Noise.CS Tsh t_peer (l_pb L); @data_at_ Noise.CS Tsh t_peer (l_pa L);
          @data_at_ HCS Tsh t_mident (l_ia L); @data_at_ HCS Tsh t_mident (l_ib L);
          hbytes Tsh rawa (l_rawa L); hbytes Tsh rawb (l_rawb L); hbytes Tsh psk (l_psk L);
          hout Tsh 32 (l_ssa L); hout Tsh 32 (l_ssb L)] ++
         hhs3_p1_rest L ++ hhs3_globs gv S Int64.zero FR ++ hhs3_scr_tmp L))).

(* after B (and after C): the devices set up (R's secrets and boot clock), the empty tables, the harness's
   identities *)
Definition hhs3_p1_SB (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred :=
  EX R: hhs3_run, EX S: shim, EX a0: int64, EX f0: int64, EX l0: int64,
  PROPx [hhs3_run_ok R; hhs3_cnt S a0 f0 l0]
  (LOCALx (temp HC._use_psk (Vint (if r_up R then Int.one else Int.zero)) :: hhs3_cnt_temps a0 f0 l0 ++
           hhs3_lvars gv L)
  (SEPx ([device_rep Tsh (l_wa L) (hhs3_DA x25519 R L); device_rep Tsh (l_wb L) (hhs3_DB x25519 R L);
          itable Tsh (l_ita L) (mkT [] []); itable Tsh (l_itb L) (mkT [] []);
          ptable Tsh (l_pta L) nullval; ptable Tsh (l_ptb L) nullval;
          @data_at_ Noise.CS Tsh t_peer (l_pb L); @data_at_ Noise.CS Tsh t_peer (l_pa L);
          @data_at HCS Tsh t_mident (mident_val (hhs3_IA x25519 R)) (l_ia L);
          @data_at HCS Tsh t_mident (mident_val (hhs3_IB x25519 R)) (l_ib L);
          hbytes Tsh (r_rawa R) (l_rawa L); hbytes Tsh (r_rawb R) (l_rawb L); hbytes Tsh (r_psk R) (l_psk L);
          hout Tsh 32 (l_ssa L); hout Tsh 32 (l_ssb L)] ++
         hhs3_p1_rest L ++ hhs3_globs gv S Int64.zero FR ++ hhs3_scr_tmp L))).

(* after D: the peers set up (pb = A's peer for B, pa = B's peer for A), each linked in its public-key table,
   each handshake entry in its index table's pool (unhashed) *)
Definition hhs3_p1_SD (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred :=
  EX R: hhs3_run, EX S: shim, EX a0: int64, EX f0: int64, EX l0: int64,
  PROPx [hhs3_run_ok R; hhs3_cnt S a0 f0 l0]
  (LOCALx (hhs3_cnt_temps a0 f0 l0 ++ hhs3_lvars gv L)
  (SEPx ([device_rep Tsh (l_wa L) (hhs3_DA x25519 R L); device_rep Tsh (l_wb L) (hhs3_DB x25519 R L);
          ptable Tsh (l_pta L) (l_pb L); ptable Tsh (l_ptb L) (l_pa L);
          @data_at HCS Tsh t_mident (mident_val (hhs3_IA x25519 R)) (l_ia L);
          @data_at HCS Tsh t_mident (mident_val (hhs3_IB x25519 R)) (l_ib L);
          hbytes Tsh (r_rawa R) (l_rawa L); hbytes Tsh (r_rawb R) (l_rawb L); hbytes Tsh (r_psk R) (l_psk L);
          hout Tsh 32 (l_ssa L); hout Tsh 32 (l_ssb L);
          itable Tsh (l_ita L) (hhs3_TA0 L); itable Tsh (l_itb L) (hhs3_TB0 L);
          peer_rep Tsh (l_pb L) (hhs3_PB0 x25519 R L); peer_rep Tsh (l_pa L) (hhs3_PA0 x25519 R L)] ++
         hhs3_p1_rest L ++ hhs3_globs gv S Int64.zero FR ++ hhs3_scr_tmp L))).

(* the SEP of SE (after E and F) *)
Definition hhs3_p1_SEsep (gv: globals) (L: hhs3_loc) (FR: mpred) (R: hhs3_run) (S: shim) : list mpred :=
  hhs3_setup_sep x25519 R L ++
  [itable Tsh (l_ita L) (hhs3_TA0 L); itable Tsh (l_itb L) (hhs3_TB0 L);
   peer_rep Tsh (l_pb L) (hhs3_PB0 x25519 R L); peer_rep Tsh (l_pa L) (hhs3_PA0 x25519 R L)] ++
  hhs3_p1_rest L ++ hhs3_globs gv S Int64.zero FR ++ hhs3_scr_tmp L.

(* after E (and after F): ssa / ssb = the harness's precomputed values, the CHECKs passed *)
Definition hhs3_p1_SE (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred :=
  EX R: hhs3_run, EX S: shim, EX a0: int64, EX f0: int64, EX l0: int64,
  PROPx [hhs3_run_ok R; hhs3_cnt S a0 f0 l0]
  (LOCALx (hhs3_cnt_temps a0 f0 l0 ++ hhs3_lvars gv L)
  (SEPx (hhs3_p1_SEsep gv L FR R S))).

(* ---------------------------------------------------------------------- *)
(* G's early return: everything of SE back to main's stack frame           *)
(* ---------------------------------------------------------------------- *)

(* main's 32 locals as the stack frame wants them (fn_vars order) *)
Definition hhs3_p1_frame (L: hhs3_loc) : list mpred :=
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

Definition hhs3_p1_free_stmt : Prop :=
  x25519_props x25519 ->
  forall gv L FR R S, hhs3_run_ok R ->
  fold_right_sepcon (hhs3_p1_SEsep gv L FR R S) |-- fold_right_sepcon (hhs3_p1_frame L) * TT.

End States.
