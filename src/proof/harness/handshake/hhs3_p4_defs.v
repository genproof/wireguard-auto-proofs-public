(* law handshake: main's phase P4 (statements 77..100) cut into six segments, and the states between
   them.

   Segments (statement indices of main's body):
     A  = 77..80  fill_resp(m2); resp_img(rimg_before, m2); hs_take(&snap, &pa.handshake);
                  ok2 = wg_noise_handshake_create_response(m2, &pa.handshake)                S3 -> SA
     BC = 81..82  { mok = m_create_response(&mr, &ci.st, m1->eph, pa.handshake.remote_static, psk,
                  wg_shim_random_log); CHECK(ok2 == mok); }  completeness 2: if (all_ok) { m_dh x4,
                  bytes_eq x2, bytes_zero(mr.ephemeral); all_ok = ..; if (all_ok) CHECK(ok2) }  SA -> SC
     D  = 83      if (!ok2) { free(m1); free(m2); return 0; }                                 SC -> SD
     E1 = 84..88  resp_img(rimg, m2); CHECK type; CHECK receiver_index; CHECK sender_index ==
                  wg_shim_random_u32 == entry.index; CHECK table_has / index_unique / len    SD -> SE
     E2 = 89..94  CHECKs: eph / enc_nothing vs mr, macs unchanged (rimg + 60), state, hash / ck /
                  eph_priv vs mr, the other fields vs snap                                    SE -> SE
     F  = 95..100 add_mac(m2, 92, &pa); m_label_key(tmp, ..); m_mac(rimg + 60, ..); bytes_set(rimg + 76,
                  0, 16); resp_img(rimg_before, m2); CHECK(rimg == rimg_before)              SE -> S4
   Pure facts taken as hypotheses by the segments (proved in their own files):
     hhs3_p4_pa1_stmt    pa's state after P3 is hhs3_p4_new (the kernel's accepted peer)
     hhs3_p4_agree_stmt  the kernel's create_response vs the harness's m_create_response, and
                         completeness (a failed m_create_response makes all_ok false)
     hhs3_p4_free_stmt   the early return of D: every local back to main's stack frame (the same
                         statement as hhs3_p2_free_stmt / hhs3_p3_free_stmt). *)
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

Definition hhs3_p4_A := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 77 4)) in exact x).
Definition hhs3_p4_BC := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 81 2)) in exact x).
Definition hhs3_p4_D := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 83 1)) in exact x).
Definition hhs3_p4_E1 := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 84 5)) in exact x).
Definition hhs3_p4_E2 := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 89 6)) in exact x).
Definition hhs3_p4_F := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 95 6)) in exact x).

Lemma hhs3_p4_split :
  hhs3_l 77 24 = hhs3_l 77 4 ++ hhs3_l 81 2 ++ hhs3_l 83 1 ++ hhs3_l 84 5 ++ hhs3_l 89 6 ++ hhs3_l 95 6.
Proof. reflexivity. Qed.

Lemma hhs3_p4_segs_eq :
  hhs3_p4_A = hhs3_seql (hhs3_l 77 4) /\ hhs3_p4_BC = hhs3_seql (hhs3_l 81 2) /\
  hhs3_p4_D = hhs3_seql (hhs3_l 83 1) /\ hhs3_p4_E1 = hhs3_seql (hhs3_l 84 5) /\
  hhs3_p4_E2 = hhs3_seql (hhs3_l 89 6) /\ hhs3_p4_F = hhs3_seql (hhs3_l 95 6).
Proof. repeat split. Qed.

Lemma hhs3_p4_cut {Espec: OracleKind} {cs: compspecs} Delta P Q R l1 l2 :
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
(* Model                                                                   *)
(* ---------------------------------------------------------------------- *)

Section Model.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* the kernel's accepted peer of P3 (= hhs3_p3_new of phase P3): one more reference, the new handshake
   (CI2 = (ts, ck, h) of stage 2) *)
Definition hhs3_p4_new (R: hhs3_run) (L: hhs3_loc) (M1: init_msg) (nowb: int64)
  (CI2: list byte * list byte * list byte) : peer :=
  let P0 := hhs3_PA0 x25519 R L in
  let H0 := p_hs P0 in
  let '(t, ck2, h2) := CI2 in
  p_set_hs (p_set_refs P0 (rc_add1 (p_refs P0)))
    (mkHS HS_CONSUMED_INITIATION (last_consumption (hs_lic H0) nowb) (hs_sid H0) (hs_eph H0)
          (hs_rstatic H0) (im_eph M1) (hs_ss H0) (hs_psk H0) h2 ck2 t (im_sender M1)).

(* pa's snapshot (hs_take in A): its entry unhashed in the pool of itb, its handshake = P3's result *)
Definition hhs3_p4_snap (L: hhs3_loc) (PA1: peer) : hsnap :=
  snap_of (hhs3_TB0 L) (hs_addr (l_pa L)) (hhs3_EA L) (p_hs (hhs3_PA2 PA1)).

(* ---------------------------------------------------------------------- *)
(* Pure statements                                                         *)
(* ---------------------------------------------------------------------- *)

(* the peer B accepted in P3 is hhs3_p4_new (consume_initiation_model on the one-element peer list
   [(pa, Tsh, PA0)]; stage 1 / stage 2 of the kernel = the harness's m_consume_init1/2_model, hs_ss PA0 =
   hhs3_ssb; the same fact as the second conjunct of P3's hhs3_p3_acc_stmt) *)
Definition hhs3_p4_pa1_stmt : Prop :=
  forall R L M1 nowb PA1 CI1 CI2, hhs3_run_ok R ->
  hhs3_after_cin x25519 aead_dec R L M1 nowb PA1 CI1 CI2 ->
  PA1 = hhs3_p4_new R L M1 nowb CI2.

(* the kernel's create_response from pa's state (CONSUMED_INITIATION, remote ephemeral = m1's, remote
   static = A's public, psk = the psk buffer, (ck, h) = CI2's) agrees with the harness's m_create_response:
   same success, and at success the message / handshake are those of the model's values; completeness: if
   m_create_response fails, the harness's agreement flag computed from mr.ephemeral = X25519(clamp r, 9)
   and mr.eph_priv = clamp r (the fields the C writes before any failure) is false *)
Definition hhs3_p4_agree_stmt : Prop :=
  x25519_props x25519 ->
  forall R L I M1 H1 MI nowb CI2 Q, hhs3_run_ok R -> hhs3_after_init x25519 aead_enc R L I M1 H1 MI ->
  Zlength (s_r Q) = 32 ->
  let PA1 := hhs3_p4_new R L M1 nowb CI2 in
  (fst (fst (hhs3_cr x25519 aead_enc PA1 Q)) =
     match hhs3_mr x25519 aead_enc R PA1 M1 CI2 Q with Some _ => true | None => false end) /\
  (forall E encn ep ck h, hhs3_mr x25519 aead_enc R PA1 M1 CI2 Q = Some (E, encn, ep, ck, h) ->
     hhs3_cr x25519 aead_enc PA1 Q =
       (true, mkRM (Int.repr 2) (s_idx Q) (im_sender M1) E encn (rm_mac1 (s_M0 Q)) (rm_mac2 (s_M0 Q)),
        hs_set_state (hs_set_ckh (hs_set_eph (p_hs (hhs3_PA2 PA1)) ep) ck h) HS_CREATED_RESPONSE) /\
     ep = clamp (s_r Q) /\ E = x25519 ep basepoint9) /\
  (hhs3_mr x25519 aead_enc R PA1 M1 CI2 Q = None ->
     forall z1 z2 z3,
     hhs3_ok4 x25519 (hhs3_ok3 x25519 R I nowb MI) MI R
       (x25519 (clamp (s_r Q)) basepoint9, z1, clamp (s_r Q), z2, z3) = false).

End Model.

(* ---------------------------------------------------------------------- *)
(* The states                                                              *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* the SEP of SA .. SE: itb_item = itb, pa_item = pa's peer_rep, m2_item = m2's contents, rimg_item = rimg,
   mr_item = the local mr, rimgb_item = rimg_before; ci as in S3; snap = pa's snapshot (taken in A) *)
Definition hhs3_p4_sep (gv: globals) (L: hhs3_loc) (FR: mpred) (R: hhs3_run) (S: shim) (m1 m2: val)
  (I: hhs3_ini) (M1: init_msg) (H1: handshake)
  (MI: list byte * list byte * list byte * list byte * list byte * list byte)
  (PA1: peer) (CI1: list byte * list byte * list byte * list byte) (CI2: list byte * list byte * list byte)
  (itb_item pa_item m2_item rimg_item mr_item rimgb_item: mpred) : list mpred :=
  hhs3_setup_sep x25519 R L ++
  [itable Tsh (l_ita L) (hhs3_TA1 L I); itb_item;
   peer_rep Tsh (l_pb L) (hhs3_PB1 x25519 R L M1 H1); pa_item;
   hhs3_tok t_init m1; init_rep Ews m1 (hhs3_M1m x25519 R M1);
   hhs3_tok t_resp m2; m2_item;
   hout Tsh 12 (l_ts L); hout Tsh 148 (l_img L); rimg_item;
   (let '(E, encs, enct, ep, ck, h) := MI in @data_at HCS Tsh t_minit (minit_val E encs enct ep ck h) (l_mi L));
   (let '(s, _, ck1, _) := CI1 in let '(t, ck, h) := CI2 in
    @data_at HCS Tsh t_mcinit (mcinit_val ck h (bytes (kdf2 ck1 (hhs3_ssb x25519 R))) (bytes s) (bytes t))
      (l_ci L));
   mr_item; @data_at_ HCS Tsh t_mstate (l_st2 L)] ++
  hhs3_globs gv S Int64.zero FR ++
  [hout Tsh 32 (l_tmp L); hout Tsh 148 (l_imgb L); rimgb_item;
   @data_at HCS Tsh t_hsnap (hsnap_val (hhs3_p4_snap L PA1)) (l_snap L);
   hout Tsh 32 (l_d1 L); hout Tsh 32 (l_d2 L); hout Tsh 32 (l_d1b L); hout Tsh 32 (l_d2b L);
   hout Tsh 32 (l_first L); hout Tsh 32 (l_second L)].

(* after A: the response M0 filled (rimg_before = its image), the snapshot of pa, create_response's
   result (ok2, M, H) = hhs3_cr PA1 Q (hidden behind variables), Q = (M0, r, idx) its draws; the shim
   holds the ephemeral draw r in wg_shim_random_log, and idx in wg_shim_random_u32 at success *)
Definition hhs3_p4_SA (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred :=
  EX R: hhs3_run, EX S: shim, EX m1: val, EX m2: val, EX a0: int64, EX f0: int64, EX l0: int64,
  EX I: hhs3_ini, EX M1: init_msg, EX H1: handshake,
  EX MI: list byte * list byte * list byte * list byte * list byte * list byte,
  EX nowb: int64, EX PA1: peer, EX CI1: list byte * list byte * list byte * list byte,
  EX CI2: list byte * list byte * list byte,
  EX Q: hhs3_rsp, EX ok2: bool, EX M: resp_msg, EX H: handshake,
  PROPx [hhs3_run_ok R; hhs3_cnt S a0 f0 l0; hhs3_after_init x25519 aead_enc R L I M1 H1 MI;
         hhs3_after_cin x25519 aead_dec R L M1 nowb PA1 CI1 CI2;
         hhs3_cr x25519 aead_enc PA1 Q = (ok2, M, H); rm_ok (s_M0 Q); Zlength (s_r Q) = 32;
         ok2 = true -> t_fresh (hhs3_TB0 L) (hs_addr (l_pa L)) (s_idx Q);
         s_log S = s_r Q; ok2 = true -> s_u32 S = s_idx Q]
  (LOCALx ([temp HC._m1 m1; temp HC._m2 m2; temp HC._ok2 (Val.of_bool ok2);
            temp HC._all_ok (Vint (if hhs3_ok3 x25519 R I nowb MI then Int.one else Int.zero))] ++
           hhs3_cnt_temps a0 f0 l0 ++ hhs3_lvars gv L)
  (SEPx (hhs3_p4_sep gv L FR R S m1 m2 I M1 H1 MI PA1 CI1 CI2
           (itable Tsh (l_itb L) (if ok2 then hhs3_TB1 L Q else hhs3_TB0 L))
           (peer_rep Tsh (l_pa L) (p_set_hs (hhs3_PA2 PA1) H))
           (resp_rep Ews m2 M)
           (hout Tsh 92 (l_rimg L))
           (@data_at_ HCS Tsh t_mresp (l_mr L))
           (hbytes Tsh (resp_bytes (s_M0 Q)) (l_rimgb L))))).

(* after BC: ok2 = mok; at success the facts of S4 (hhs3_after_resp, MR = the model's values in mr) and
   all_ok = hhs3_ok4 (any value otherwise: D returns) *)
Definition hhs3_p4_SC (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred :=
  EX R: hhs3_run, EX S: shim, EX m1: val, EX m2: val, EX a0: int64, EX f0: int64, EX l0: int64,
  EX I: hhs3_ini, EX M1: init_msg, EX H1: handshake,
  EX MI: list byte * list byte * list byte * list byte * list byte * list byte,
  EX nowb: int64, EX PA1: peer, EX CI1: list byte * list byte * list byte * list byte,
  EX CI2: list byte * list byte * list byte,
  EX Q: hhs3_rsp, EX ok2: bool, EX M: resp_msg, EX H: handshake,
  EX MR: list byte * list byte * list byte * list byte * list byte, EX aok: bool,
  PROPx [hhs3_run_ok R; hhs3_cnt S a0 f0 l0; hhs3_after_init x25519 aead_enc R L I M1 H1 MI;
         hhs3_after_cin x25519 aead_dec R L M1 nowb PA1 CI1 CI2;
         hhs3_cr x25519 aead_enc PA1 Q = (ok2, M, H); rm_ok (s_M0 Q);
         ok2 = true -> hhs3_after_resp x25519 aead_enc R L M1 PA1 CI2 Q M H MR;
         ok2 = true -> s_u32 S = s_idx Q;
         ok2 = true -> aok = hhs3_ok4 x25519 (hhs3_ok3 x25519 R I nowb MI) MI R MR]
  (LOCALx ([temp HC._m1 m1; temp HC._m2 m2; temp HC._ok2 (Val.of_bool ok2);
            temp HC._all_ok (Vint (if aok then Int.one else Int.zero))] ++
           hhs3_cnt_temps a0 f0 l0 ++ hhs3_lvars gv L)
  (SEPx (hhs3_p4_sep gv L FR R S m1 m2 I M1 H1 MI PA1 CI1 CI2
           (itable Tsh (l_itb L) (if ok2 then hhs3_TB1 L Q else hhs3_TB0 L))
           (peer_rep Tsh (l_pa L) (p_set_hs (hhs3_PA2 PA1) H))
           (resp_rep Ews m2 M)
           (hout Tsh 92 (l_rimg L))
           (if ok2 then (let '(E, encn, ep, ck, h) := MR in
                         @data_at HCS Tsh t_mresp (mresp_val E encn ep ck h) (l_mr L))
            else @data_at_ HCS Tsh t_mresp (l_mr L))
           (hbytes Tsh (resp_bytes (s_M0 Q)) (l_rimgb L))))).

(* after D (filled = false) and after E1 / E2 (filled = true: rimg = the image of m2): create_response
   succeeded (M2, H2), the model's MR *)
Definition hhs3_p4_SDE (filled: bool) (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred :=
  EX R: hhs3_run, EX S: shim, EX m1: val, EX m2: val, EX a0: int64, EX f0: int64, EX l0: int64,
  EX I: hhs3_ini, EX M1: init_msg, EX H1: handshake,
  EX MI: list byte * list byte * list byte * list byte * list byte * list byte,
  EX nowb: int64, EX PA1: peer, EX CI1: list byte * list byte * list byte * list byte,
  EX CI2: list byte * list byte * list byte,
  EX Q: hhs3_rsp, EX M2: resp_msg, EX H2: handshake,
  EX MR: list byte * list byte * list byte * list byte * list byte,
  PROPx [hhs3_run_ok R; hhs3_cnt S a0 f0 l0; hhs3_after_init x25519 aead_enc R L I M1 H1 MI;
         hhs3_after_cin x25519 aead_dec R L M1 nowb PA1 CI1 CI2;
         hhs3_after_resp x25519 aead_enc R L M1 PA1 CI2 Q M2 H2 MR;
         s_u32 S = s_idx Q]
  (LOCALx ([temp HC._m1 m1; temp HC._m2 m2;
            temp HC._all_ok (Vint (if hhs3_ok4 x25519 (hhs3_ok3 x25519 R I nowb MI) MI R MR
                                   then Int.one else Int.zero))] ++
           hhs3_cnt_temps a0 f0 l0 ++ hhs3_lvars gv L)
  (SEPx (hhs3_p4_sep gv L FR R S m1 m2 I M1 H1 MI PA1 CI1 CI2
           (itable Tsh (l_itb L) (hhs3_TB1 L Q))
           (peer_rep Tsh (l_pa L) (p_set_hs (hhs3_PA2 PA1) H2))
           (resp_rep Ews m2 M2)
           (if filled then hbytes Tsh (resp_bytes M2) (l_rimg L) else hout Tsh 92 (l_rimg L))
           (let '(E, encn, ep, ck, h) := MR in @data_at HCS Tsh t_mresp (mresp_val E encn ep ck h) (l_mr L))
           (hbytes Tsh (resp_bytes (s_M0 Q)) (l_rimgb L))))).

Definition hhs3_p4_SD (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred := hhs3_p4_SDE false gv L FR.
Definition hhs3_p4_SE (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred := hhs3_p4_SDE true gv L FR.

(* ---------------------------------------------------------------------- *)
(* D's early return: everything back to main's stack frame                 *)
(* ---------------------------------------------------------------------- *)

(* main's 32 locals as the stack frame wants them (fn_vars order) *)
Definition hhs3_p4_frame (L: hhs3_loc) : list mpred :=
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
   pools hold exactly the peers' handshake entries, the peers any contents (= hhs3_p3_free_stmt) *)
Definition hhs3_p4_free_stmt : Prop :=
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
  |-- fold_right_sepcon (hhs3_p4_frame L) * TT.

End States.
