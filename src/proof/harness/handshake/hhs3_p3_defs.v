(* law handshake: main's phase P3 (statements 66..76) cut into six segments, and the states between
   them.

   Segments (statement indices of main's body):
     A = 66..69  wg_shim_boottime_ns = draw_boottime(); now_b = wg_shim_boottime_ns; hs_take(&snap, &pa.handshake);
                 ret = wg_noise_handshake_consume_initiation(m1, &wb)                    S2 -> SA
     B = 70      acc1 = ib.ok && m_consume_initiation_1(..) && bytes_eq(ci.spub, pa..remote_static) &&
                 m_consume_initiation_2(&ci, ssb, ..) && m_ts_newer(ci.ts, snap.ts) && m_not_flood(..)
                                                                                         SA -> SB
     C = 71..73  all_ok = all_ok && now_b >= 20 ms; init_img(img_before, m1); CHECK(img == img_before)
                                                                                         SB -> SC
     D = 74      if (!acc1) { CHECK(ret == NULL && hs_same && refcount == 1) }
                 else { CHECK(ret == &pa && refcount == 2); wg_peer_put(ret); the field CHECKs }
                                                                                         SC -> SD
     E = 75      completeness 1: if (all_ok) { m_dh x2, bytes_eq, bytes_zero(ssa), bytes_eq(ssa, ssb);
                 all_ok = agree; if (all_ok) CHECK(acc1) }                               SD -> SE
     F = 76      if (!acc1) { free(m1); free(m2); return 0; }                            SE -> S3
   Pure facts taken as hypotheses by the segments (proved in their own files):
     hhs3_p3_acc_stmt     the kernel's consume_initiation_model vs the harness's acc1 formula (structural)
     hhs3_p3_crypto_stmt  B decrypts A's timestamp (ci.ts == ts, needs hhs3_comm), and completeness
                          (all_ok after E -> acc1)
     hhs3_p3_free_stmt    the early return of F: every local back to main's stack frame (the same statement
                          as hhs3_p2_free_stmt of phase P2). *)
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

Definition hhs3_p3_A := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 66 4)) in exact x).
Definition hhs3_p3_B := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 70 1)) in exact x).
Definition hhs3_p3_C := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 71 3)) in exact x).
Definition hhs3_p3_D := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 74 1)) in exact x).
Definition hhs3_p3_E := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 75 1)) in exact x).
Definition hhs3_p3_F := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 76 1)) in exact x).

Lemma hhs3_p3_split :
  hhs3_l 66 11 = hhs3_l 66 4 ++ hhs3_l 70 1 ++ hhs3_l 71 3 ++ hhs3_l 74 1 ++ hhs3_l 75 1 ++ hhs3_l 76 1.
Proof. reflexivity. Qed.

Lemma hhs3_p3_segs_eq :
  hhs3_p3_A = hhs3_seql (hhs3_l 66 4) /\ hhs3_p3_B = hhs3_seql (hhs3_l 70 1) /\
  hhs3_p3_C = hhs3_seql (hhs3_l 71 3) /\ hhs3_p3_D = hhs3_seql (hhs3_l 74 1) /\
  hhs3_p3_E = hhs3_seql (hhs3_l 75 1) /\ hhs3_p3_F = hhs3_seql (hhs3_l 76 1).
Proof. repeat split. Qed.

Lemma hhs3_p3_cut {Espec: OracleKind} {cs: compspecs} Delta P Q R l1 l2 :
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
(* The harness's acc1, the accepted peer                                   *)
(* ---------------------------------------------------------------------- *)

Section Model.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* stage 2 of the harness from stage 1's result CI1 = (spub, key, ck, h) *)
Definition hhs3_p3_cs2 (R: hhs3_run) (M1: init_msg) (CI1: list byte * list byte * list byte * list byte)
  : option (list byte * list byte * list byte) :=
  let '(_, _, ck, h) := CI1 in m_consume_init2_model aead_dec (hhs3_ssb x25519 R) ck h (im_enct M1).

(* the harness's acc1 (C: ib.ok && stage 1 && spub == pa's remote static && stage 2 && ts newer than the
   snapshot's && not flood; snap = pa's handshake before the call = p_hs PA0) *)
Definition hhs3_p3_acc (R: hhs3_run) (L: hhs3_loc) (M1: init_msg) (nowb: int64) : bool :=
  let H0 := p_hs (hhs3_PA0 x25519 R L) in
  mi_ok (hhs3_IB x25519 R) &&
  match hhs3_cs1 x25519 aead_dec R M1 with
  | Some CI1 =>
      let '(s, _, _, _) := CI1 in
      bytes_eqb s (hs_rstatic H0) &&
      match hhs3_p3_cs2 R M1 CI1 with
      | Some (t, _, _) => ts_newer t (hs_ts H0) && not_flood (hs_lic H0) nowb
      | None => false
      end
  | None => false
  end.

(* the kernel's accepted peer: one more reference, the new handshake (CI2 = (ts, ck, h) of stage 2) *)
Definition hhs3_p3_new (R: hhs3_run) (L: hhs3_loc) (M1: init_msg) (nowb: int64)
  (CI2: list byte * list byte * list byte) : peer :=
  let P0 := hhs3_PA0 x25519 R L in
  let H0 := p_hs P0 in
  let '(t, ck2, h2) := CI2 in
  p_set_hs (p_set_refs P0 (rc_add1 (p_refs P0)))
    (mkHS HS_CONSUMED_INITIATION (last_consumption (hs_lic H0) nowb) (hs_sid H0) (hs_eph H0)
          (hs_rstatic H0) (im_eph M1) (hs_ss H0) (hs_psk H0) h2 ck2 t (im_sender M1)).

(* pa's state after consume_initiation (SA) *)
Definition hhs3_p3_pa (R: hhs3_run) (L: hhs3_loc) (Cin: option (val * peer)) : peer :=
  match Cin with Some (_, P) => P | None => hhs3_PA0 x25519 R L end.

(* ci after stage 2 (as in S3) *)
Definition hhs3_p3_civ (R: hhs3_run) (CI1: list byte * list byte * list byte * list byte)
  (CI2: list byte * list byte * list byte) : reptype t_mcinit :=
  let '(s, _, ck1, _) := CI1 in let '(t, ck, h) := CI2 in
  @mcinit_val ck h (bytes (kdf2 ck1 (hhs3_ssb x25519 R))) (bytes s) (bytes t).

(* pa's snapshot (hs_take in A): its entry unhashed in the pool of itb *)
Definition hhs3_p3_snap (R: hhs3_run) (L: hhs3_loc) : hsnap :=
  snap_of (hhs3_TB0 L) (hs_addr (l_pa L)) (hhs3_EA L) (p_hs (hhs3_PA0 x25519 R L)).

(* all_ok after C *)
Definition hhs3_p3_ok25 (R: hhs3_run) (I: hhs3_ini) (nowb: int64) : bool :=
  hhs3_ok2 x25519 R I && negb (Int64.ltu nowb (Int64.repr 20000000)).

(* ---------------------------------------------------------------------- *)
(* Pure statements                                                         *)
(* ---------------------------------------------------------------------- *)

(* the kernel's consume_initiation (one peer pa = PA0 in B's table) accepts exactly when the harness's acc1
   holds, and then with the state hhs3_p3_new; its accepted address is always pa, the remote static unchanged.
   Structural: setup_identity raw_b = (mi_pub, mi_priv, mi_ok) of mident_of raw_b when mi_ok; hs_ss PA0 =
   hhs3_ssb; Z.leb (memcmp_Z t l) 0 = negb (ts_newer t l); the flood test = negb not_flood; peer_get PA0 *)
Definition hhs3_p3_acc_stmt : Prop :=
  forall R L M1 nowb, hhs3_run_ok R ->
  (hhs3_p3_acc R L M1 nowb = false -> hhs3_cin x25519 aead_dec R L M1 nowb = None) /\
  (forall CI1 CI2, hhs3_cs1 x25519 aead_dec R M1 = Some CI1 -> hhs3_p3_cs2 R M1 CI1 = Some CI2 ->
     hhs3_p3_acc R L M1 nowb = true ->
     hhs3_cin x25519 aead_dec R L M1 nowb = Some (l_pa L, hhs3_p3_new R L M1 nowb CI2)) /\
  (forall a P, hhs3_cin x25519 aead_dec R L M1 nowb = Some (a, P) ->
     a = l_pa L /\ hs_rstatic (p_hs P) = hs_rstatic (p_hs (hhs3_PA0 x25519 R L))).

(* B decrypts A's timestamp (DH values agree by hhs3_comm: B's es = A's es, ssb = ssa), and completeness:
   all_ok after E (hhs3_ok3: B's identity, the DH values of es agree and are non-zero, ssa = ssb non-zero,
   ts non-zero, now_b >= 20 ms) implies acc1 *)
Definition hhs3_p3_crypto_stmt : Prop :=
  hhs3_comm x25519 -> x25519_props x25519 -> aead_props aead_enc aead_dec ->
  forall R L I M1 H1 MI nowb, hhs3_run_ok R -> hhs3_after_init x25519 aead_enc R L I M1 H1 MI ->
  0 <= Int64.unsigned nowb < 2 ^ 62 ->
  (forall CI1 CI2, mi_ok (hhs3_IB x25519 R) = true ->
     hhs3_cs1 x25519 aead_dec R M1 = Some CI1 -> hhs3_p3_cs2 R M1 CI1 = Some CI2 ->
     (let '(t, _, _) := CI2 in t = hhs3_ts I)) /\
  (hhs3_ok3 x25519 R I nowb MI = true -> hhs3_p3_acc R L M1 nowb = true).

End Model.

(* ---------------------------------------------------------------------- *)
(* The states                                                              *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* the SEP of SA .. SE: pa_item = pa's peer_rep, ci_item = the local ci, imgb_item = img_before, d_items =
   d1, d2 (the scratch locals of the completeness block); snap = pa's snapshot *)
Definition hhs3_p3_sep (gv: globals) (L: hhs3_loc) (FR: mpred) (R: hhs3_run) (S: shim) (m1 m2: val)
  (I: hhs3_ini) (M1: init_msg) (H1: handshake)
  (MI: list byte * list byte * list byte * list byte * list byte * list byte)
  (pa_item ci_item imgb_item: mpred) : list mpred :=
  hhs3_setup_sep x25519 R L ++
  [itable Tsh (l_ita L) (hhs3_TA1 L I); itable Tsh (l_itb L) (hhs3_TB0 L);
   peer_rep Tsh (l_pb L) (hhs3_PB1 x25519 R L M1 H1); pa_item;
   hhs3_tok t_init m1; init_rep Ews m1 (hhs3_M1m x25519 R M1);
   hhs3_tok t_resp m2; @data_at_ Noise.CS Ews t_resp m2;
   hbytes Tsh (hhs3_ts I) (l_ts L); hbytes Tsh (init_bytes (hhs3_M1m x25519 R M1)) (l_img L);
   hout Tsh 92 (l_rimg L);
   (let '(E, encs, enct, ep, ck, h) := MI in @data_at HCS Tsh t_minit (minit_val E encs enct ep ck h) (l_mi L));
   ci_item; @data_at_ HCS Tsh t_mresp (l_mr L); @data_at_ HCS Tsh t_mstate (l_st2 L)] ++
  hhs3_globs gv S Int64.zero FR ++
  [hout Tsh 32 (l_tmp L); imgb_item; hout Tsh 92 (l_rimgb L);
   @data_at HCS Tsh t_hsnap (hsnap_val (hhs3_p3_snap x25519 R L)) (l_snap L);
   hout Tsh 32 (l_d1 L); hout Tsh 32 (l_d2 L); hout Tsh 32 (l_d1b L); hout Tsh 32 (l_d2b L);
   hout Tsh 32 (l_first L); hout Tsh 32 (l_second L)].

(* after A: the boot clock now_b (in the shim), the snapshot of pa, consume_initiation's result Cin
   (= hhs3_cin, hidden behind a variable), ret = its peer or NULL, pa = its state *)
Definition hhs3_p3_SA (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred :=
  EX R: hhs3_run, EX S: shim, EX m1: val, EX m2: val, EX a0: int64, EX f0: int64, EX l0: int64,
  EX I: hhs3_ini, EX M1: init_msg, EX H1: handshake,
  EX MI: list byte * list byte * list byte * list byte * list byte * list byte,
  EX nowb: int64, EX Cin: option (val * peer),
  PROPx [hhs3_run_ok R; hhs3_cnt S a0 f0 l0; hhs3_after_init x25519 aead_enc R L I M1 H1 MI;
         0 <= Int64.unsigned nowb < 2 ^ 62; s_boot S = nowb;
         hhs3_cin x25519 aead_dec R L M1 nowb = Cin]
  (LOCALx ([temp HC._m1 m1; temp HC._m2 m2; temp HC._now_b (Vlong nowb); temp HC._ret (peer_result Cin);
            temp HC._all_ok (Vint (if hhs3_ok2 x25519 R I then Int.one else Int.zero))] ++
           hhs3_cnt_temps a0 f0 l0 ++ hhs3_lvars gv L)
  (SEPx (hhs3_p3_sep gv L FR R S m1 m2 I M1 H1 MI
           (peer_rep Tsh (l_pa L) (hhs3_p3_pa x25519 R L Cin))
           (@data_at_ HCS Tsh t_mcinit (l_ci L)) (hout Tsh 148 (l_imgb L))))).

(* after B (okf = hhs3_ok2) and after C (okf = hhs3_p3_ok25, img_before = the image of m1, weakened):
   acc1 = hhs3_p3_acc; when acc1, the stages CI1 / CI2 and ci holds them *)
Definition hhs3_p3_SBC (okf: hhs3_run -> hhs3_ini -> int64 -> bool) (gv: globals) (L: hhs3_loc) (FR: mpred)
  : environ -> mpred :=
  EX R: hhs3_run, EX S: shim, EX m1: val, EX m2: val, EX a0: int64, EX f0: int64, EX l0: int64,
  EX I: hhs3_ini, EX M1: init_msg, EX H1: handshake,
  EX MI: list byte * list byte * list byte * list byte * list byte * list byte,
  EX nowb: int64, EX Cin: option (val * peer), EX acc: bool,
  EX CI1: list byte * list byte * list byte * list byte, EX CI2: list byte * list byte * list byte,
  PROPx [hhs3_run_ok R; hhs3_cnt S a0 f0 l0; hhs3_after_init x25519 aead_enc R L I M1 H1 MI;
         0 <= Int64.unsigned nowb < 2 ^ 62; s_boot S = nowb;
         hhs3_cin x25519 aead_dec R L M1 nowb = Cin;
         acc = hhs3_p3_acc x25519 aead_dec R L M1 nowb;
         acc = true -> hhs3_cs1 x25519 aead_dec R M1 = Some CI1 /\
                       hhs3_p3_cs2 x25519 aead_dec R M1 CI1 = Some CI2]
  (LOCALx ([temp HC._m1 m1; temp HC._m2 m2; temp HC._now_b (Vlong nowb); temp HC._ret (peer_result Cin);
            temp HC._acc1 (Vint (if acc then Int.one else Int.zero));
            temp HC._all_ok (Vint (if okf R I nowb then Int.one else Int.zero))] ++
           hhs3_cnt_temps a0 f0 l0 ++ hhs3_lvars gv L)
  (SEPx (hhs3_p3_sep gv L FR R S m1 m2 I M1 H1 MI
           (peer_rep Tsh (l_pa L) (hhs3_p3_pa x25519 R L Cin))
           (if acc then @data_at HCS Tsh t_mcinit (hhs3_p3_civ x25519 R CI1 CI2) (l_ci L)
            else @data_at_ HCS Tsh t_mcinit (l_ci L))
           (hout Tsh 148 (l_imgb L))))).

Definition hhs3_p3_SB (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred :=
  hhs3_p3_SBC (fun R I _ => hhs3_ok2 x25519 R I) gv L FR.
Definition hhs3_p3_SC (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred :=
  hhs3_p3_SBC (hhs3_p3_ok25 x25519) gv L FR.

(* after D (okf = hhs3_p3_ok25) and after E (okf = hhs3_ok3): the branches done, pa = the accepted state with
   its reference dropped again (PA1 = consume_initiation's peer) or unchanged; ret no longer used *)
Definition hhs3_p3_SDE (okf: hhs3_run -> hhs3_ini -> int64 ->
                              list byte * list byte * list byte * list byte * list byte * list byte -> bool)
  (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred :=
  EX R: hhs3_run, EX S: shim, EX m1: val, EX m2: val, EX a0: int64, EX f0: int64, EX l0: int64,
  EX I: hhs3_ini, EX M1: init_msg, EX H1: handshake,
  EX MI: list byte * list byte * list byte * list byte * list byte * list byte,
  EX nowb: int64, EX acc: bool, EX PA1: peer,
  EX CI1: list byte * list byte * list byte * list byte, EX CI2: list byte * list byte * list byte,
  PROPx [hhs3_run_ok R; hhs3_cnt S a0 f0 l0; hhs3_after_init x25519 aead_enc R L I M1 H1 MI;
         0 <= Int64.unsigned nowb < 2 ^ 62;
         acc = hhs3_p3_acc x25519 aead_dec R L M1 nowb;
         acc = true -> hhs3_cs1 x25519 aead_dec R M1 = Some CI1 /\
                       hhs3_p3_cs2 x25519 aead_dec R M1 CI1 = Some CI2 /\
                       hhs3_cin x25519 aead_dec R L M1 nowb = Some (l_pa L, PA1)]
  (LOCALx ([temp HC._m1 m1; temp HC._m2 m2;
            temp HC._acc1 (Vint (if acc then Int.one else Int.zero));
            temp HC._all_ok (Vint (if okf R I nowb MI then Int.one else Int.zero))] ++
           hhs3_cnt_temps a0 f0 l0 ++ hhs3_lvars gv L)
  (SEPx (hhs3_p3_sep gv L FR R S m1 m2 I M1 H1 MI
           (peer_rep Tsh (l_pa L) (if acc then hhs3_PA2 PA1 else hhs3_PA0 x25519 R L))
           (if acc then @data_at HCS Tsh t_mcinit (hhs3_p3_civ x25519 R CI1 CI2) (l_ci L)
            else @data_at_ HCS Tsh t_mcinit (l_ci L))
           (hout Tsh 148 (l_imgb L))))).

Definition hhs3_p3_SD (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred :=
  hhs3_p3_SDE (fun R I nowb _ => hhs3_p3_ok25 x25519 R I nowb) gv L FR.
Definition hhs3_p3_SE (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred :=
  hhs3_p3_SDE (hhs3_ok3 x25519) gv L FR.

(* ---------------------------------------------------------------------- *)
(* F's early return: everything back to main's stack frame                 *)
(* ---------------------------------------------------------------------- *)

(* main's 32 locals as the stack frame wants them (fn_vars order) *)
Definition hhs3_p3_frame (L: hhs3_loc) : list mpred :=
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
   pools hold exactly the peers' handshake entries, the peers any contents (= hhs3_p2_free_stmt) *)
Definition hhs3_p3_free_stmt : Prop :=
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
  |-- fold_right_sepcon (hhs3_p3_frame L) * TT.

End States.
