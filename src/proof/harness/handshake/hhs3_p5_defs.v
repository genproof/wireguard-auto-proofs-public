(* law handshake: main's phase P5 (statements 101..110) cut into six segments, and the states between
   them.

   Segments (statement indices of main's body):
     A = 101..104 wg_shim_boottime_ns = draw_boottime(); now_a = wg_shim_boottime_ns; hs_take(&snap, &pb.handshake);
                  ret = wg_noise_handshake_consume_response(m2, &wa)                     S4 -> SA
     B = 105      acc2 = ia.ok && m2->receiver_index == pb.handshake.entry.index &&
                  m_consume_response(&st2, &mi.st, mi.eph_priv, ia.priv, psk, m2->eph, m2->encn)
                                                                                         SA -> SB
     C = 106..107 resp_img(rimg_before, m2); CHECK(bytes_eq(rimg, rimg_before, 92))     SB -> SC
     D = 108      if (!acc2) { CHECK(ret == NULL && hs_same && refcount == 1) }
                  else { CHECK(ret == &pb && refcount == 2); wg_peer_put(ret); the field CHECKs }
                                                                                         SC -> SD
     E = 109      completeness 3: if (all_ok) CHECK(acc2 && st2.ck == mr.st.ck && st2.h == mr.st.h)
                                                                                         SD -> SD
     F = 110      if (!acc2) { free(m1); free(m2); return 0; }                           SD -> S5
   Pure facts taken as hypotheses by the segments (proved in their own files):
     hhs3_p5_acc_stmt     the kernel's consume_response_model vs the harness's acc2 formula (structural)
     hhs3_p5_crypto_stmt  completeness: all_ok (hhs3_ok4) -> acc2 and st2 = mr's chaining key and hash
     hhs3_p5_free_stmt    the early return of F: every local back to main's stack frame (the same statement
                          as hhs3_p2_free_stmt / hhs3_p3_free_stmt of phases P2 / P3). *)
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

Definition hhs3_p5_A := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 101 4)) in exact x).
Definition hhs3_p5_B := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 105 1)) in exact x).
Definition hhs3_p5_C := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 106 2)) in exact x).
Definition hhs3_p5_D := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 108 1)) in exact x).
Definition hhs3_p5_E := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 109 1)) in exact x).
Definition hhs3_p5_F := ltac:(let x := eval cbv beta iota delta [hhs3_l hhs3_seql firstn skipn hhs3_stmts] in (hhs3_seql (hhs3_l 110 1)) in exact x).

Lemma hhs3_p5_split :
  hhs3_l 101 10 = hhs3_l 101 4 ++ hhs3_l 105 1 ++ hhs3_l 106 2 ++ hhs3_l 108 1 ++ hhs3_l 109 1 ++ hhs3_l 110 1.
Proof. reflexivity. Qed.

Lemma hhs3_p5_segs_eq :
  hhs3_p5_A = hhs3_seql (hhs3_l 101 4) /\ hhs3_p5_B = hhs3_seql (hhs3_l 105 1) /\
  hhs3_p5_C = hhs3_seql (hhs3_l 106 2) /\ hhs3_p5_D = hhs3_seql (hhs3_l 108 1) /\
  hhs3_p5_E = hhs3_seql (hhs3_l 109 1) /\ hhs3_p5_F = hhs3_seql (hhs3_l 110 1).
Proof. repeat split. Qed.

Lemma hhs3_p5_cut {Espec: OracleKind} {cs: compspecs} Delta P Q R l1 l2 :
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
(* The harness's acc2, the accepted peer                                   *)
(* ---------------------------------------------------------------------- *)

Section Model.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* pb's handshake entry in ita after P2 (create_initiation inserted it with index idx1) *)
Definition hhs3_p5_EB1 (L: hhs3_loc) (I: hhs3_ini) : entry := mkEntry (l_pb L) IDX_HANDSHAKE (i_idx I).

(* pb's snapshot (hs_take in A) *)
Definition hhs3_p5_snap (R: hhs3_run) (L: hhs3_loc) (I: hhs3_ini) (M1: init_msg) (H1: handshake) : hsnap :=
  snap_of (hhs3_TA1 L I) (hs_addr (l_pb L)) (hhs3_p5_EB1 L I) (p_hs (hhs3_PB1 x25519 R L M1 H1)).

(* the harness's acc2 (C: ia.ok && m2's receiver index == pb's entry index (= idx1) && m_consume_response) *)
Definition hhs3_p5_acc (R: hhs3_run) (I: hhs3_ini)
  (MI: list byte * list byte * list byte * list byte * list byte * list byte) (M2: resp_msg) : bool :=
  mi_ok (hhs3_IA x25519 R) && Int.eq (rm_receiver M2) (i_idx I) &&
  match hhs3_mcr x25519 aead_dec R MI M2 with Some _ => true | None => false end.

(* the kernel's accepted peer: one more reference, the new handshake (ST2 = (ck, h) of the harness model) *)
Definition hhs3_p5_new (R: hhs3_run) (L: hhs3_loc) (M1: init_msg) (H1: handshake) (M2: resp_msg)
  (ST2: list byte * list byte) : peer :=
  let P0 := hhs3_PB1 x25519 R L M1 H1 in
  let '(ck, h) := ST2 in
  p_set_hs (p_set_refs P0 (rc_add1 (p_refs P0)))
    (mkHS HS_CONSUMED_RESPONSE (hs_lic H1) (hs_sid H1) (hs_eph H1) (hs_rstatic H1) (rm_eph M2) (hs_ss H1)
          (hs_psk H1) h ck (hs_ts H1) (rm_sender M2)).

(* pb's state after consume_response (SA) *)
Definition hhs3_p5_pb (R: hhs3_run) (L: hhs3_loc) (M1: init_msg) (H1: handshake) (Cre: option (val * peer)) : peer :=
  match Cre with Some (_, P) => P | None => hhs3_PB1 x25519 R L M1 H1 end.

(* ---------------------------------------------------------------------- *)
(* Pure statements                                                         *)
(* ---------------------------------------------------------------------- *)

(* the kernel's consume_response (A's table TA1 = pb's entry with index idx1, one peer pb = PB1) accepts
   exactly when the harness's acc2 holds, and then with the state hhs3_p5_new.  Structural: H1 (P2's
   create_initiation) = PB0's handshake with eph = MI's ep, ck / h = MI's, state CREATED_INITIATION
   (create_initiation_model vs m_create_initiation_model, as hhs3_p2_agree_stmt); d_id DA's private key and
   has-flag = mi_priv / mi_ok of IA; hs_psk = r_psk R; t_lookup finds pb's entry exactly when the receiver
   index is idx1; peer_get PB1 (refs 1); consume_resp_crypto with these = m_consume_response_model; the
   accepted address is always pb (the only entry of TA1 is pb's) *)
Definition hhs3_p5_acc_stmt : Prop :=
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  forall R L I M1 H1 MI M2, hhs3_run_ok R -> hhs3_after_init x25519 aead_enc R L I M1 H1 MI ->
  (hhs3_p5_acc R I MI M2 = false -> hhs3_cre x25519 aead_dec R L I M1 H1 M2 = None) /\
  (forall ST2, hhs3_p5_acc R I MI M2 = true -> hhs3_mcr x25519 aead_dec R MI M2 = Some ST2 ->
     hhs3_cre x25519 aead_dec R L I M1 H1 M2 = Some (l_pb L, hhs3_p5_new R L M1 H1 M2 ST2)) /\
  (forall a P, hhs3_cre x25519 aead_dec R L I M1 H1 M2 = Some (a, P) -> a = l_pb L).

(* completeness 3: all_ok after P4 (hhs3_ok4: hhs3_ok3's agreements of the first half, the ee and se DH
   values agree and are non-zero, the responder's ephemeral non-zero) implies acc2 and the harness's
   st2 = mr's (ck, h).  M2's receiver = pa's remote index = M1's sender = idx1; B's chain after stage 2
   (CI2) = A's (MI's ck, h) (hhs3_ok3: es and ss agree); M2's ephemeral / enc_nothing = MR's
   (create_response_model vs m_create_response_model); aead_dec of aead_enc *)
Definition hhs3_p5_crypto_stmt : Prop :=
  hhs3_comm x25519 -> x25519_props x25519 -> aead_props aead_enc aead_dec ->
  forall R L I M1 H1 MI nowb PA1 CI1 CI2 Q M2 H2 MR, hhs3_run_ok R ->
  hhs3_after_init x25519 aead_enc R L I M1 H1 MI ->
  hhs3_after_cin x25519 aead_dec R L M1 nowb PA1 CI1 CI2 ->
  hhs3_after_resp x25519 aead_enc R L M1 PA1 CI2 Q M2 H2 MR ->
  hhs3_ok4 x25519 (hhs3_ok3 x25519 R I nowb MI) MI R MR = true ->
  hhs3_p5_acc R I MI M2 = true /\
  (let '(_, _, _, ck, h) := MR in hhs3_mcr x25519 aead_dec R MI M2 = Some (ck, h)).

End Model.

(* ---------------------------------------------------------------------- *)
(* The states                                                              *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* the SEP of SA .. SD: pb_item = pb's peer_rep, rimg_item = rimg, st2_item = the local st2; rimg_before
   any contents (written and weakened in C); snap = pb's snapshot *)
Definition hhs3_p5_sep (gv: globals) (L: hhs3_loc) (FR: mpred) (R: hhs3_run) (S: shim) (m1 m2: val)
  (I: hhs3_ini) (M1: init_msg) (H1: handshake)
  (MI: list byte * list byte * list byte * list byte * list byte * list byte)
  (PA1: peer) (Q: hhs3_rsp) (M2: resp_msg) (H2: handshake)
  (MR: list byte * list byte * list byte * list byte * list byte)
  (pb_item rimg_item st2_item: mpred) : list mpred :=
  hhs3_setup_sep x25519 R L ++
  [itable Tsh (l_ita L) (hhs3_TA1 L I); itable Tsh (l_itb L) (hhs3_TB1 L Q);
   pb_item; peer_rep Tsh (l_pa L) (hhs3_PA3 x25519 R PA1 M2 H2);
   hhs3_tok t_init m1; init_rep Ews m1 (hhs3_M1m x25519 R M1);
   hhs3_tok t_resp m2; resp_rep Ews m2 (hhs3_M2m x25519 R M2);
   hout Tsh 12 (l_ts L); hout Tsh 148 (l_img L); rimg_item;
   (let '(E, encs, enct, ep, ck, h) := MI in @data_at HCS Tsh t_minit (minit_val E encs enct ep ck h) (l_mi L));
   @data_at_ HCS Tsh t_mcinit (l_ci L);
   (let '(E, encn, ep, ck, h) := MR in @data_at HCS Tsh t_mresp (mresp_val E encn ep ck h) (l_mr L));
   st2_item] ++
  hhs3_globs gv S Int64.zero FR ++
  [hout Tsh 32 (l_tmp L); hout Tsh 148 (l_imgb L); hout Tsh 92 (l_rimgb L);
   @data_at HCS Tsh t_hsnap (hsnap_val (hhs3_p5_snap x25519 R L I M1 H1)) (l_snap L);
   hout Tsh 32 (l_d1 L); hout Tsh 32 (l_d2 L); hout Tsh 32 (l_d1b L); hout Tsh 32 (l_d2b L);
   hout Tsh 32 (l_first L); hout Tsh 32 (l_second L)].

(* st2 after B: the model's (ck, h) when acc2, else any contents *)
Definition hhs3_p5_st2 (L: hhs3_loc) (acc: bool) (ST2: list byte * list byte) : mpred :=
  if acc then (let '(ck, h) := ST2 in @data_at HCS Tsh t_mstate (mstate_val ck h) (l_st2 L))
  else @data_at_ HCS Tsh t_mstate (l_st2 L).

(* after A: the boot clock now_a (in the shim), the snapshot of pb, consume_response's result Cre
   (= hhs3_cre, hidden behind a variable), ret = its peer or NULL, pb = its state *)
Definition hhs3_p5_SA (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred :=
  EX R: hhs3_run, EX S: shim, EX m1: val, EX m2: val, EX a0: int64, EX f0: int64, EX l0: int64,
  EX I: hhs3_ini, EX M1: init_msg, EX H1: handshake,
  EX MI: list byte * list byte * list byte * list byte * list byte * list byte,
  EX nowb: int64, EX PA1: peer, EX CI1: list byte * list byte * list byte * list byte,
  EX CI2: list byte * list byte * list byte,
  EX Q: hhs3_rsp, EX M2: resp_msg, EX H2: handshake, EX MR: list byte * list byte * list byte * list byte * list byte,
  EX nowa: int64, EX Cre: option (val * peer),
  PROPx [hhs3_run_ok R; hhs3_cnt S a0 f0 l0; hhs3_after_init x25519 aead_enc R L I M1 H1 MI;
         hhs3_after_cin x25519 aead_dec R L M1 nowb PA1 CI1 CI2;
         hhs3_after_resp x25519 aead_enc R L M1 PA1 CI2 Q M2 H2 MR;
         0 <= Int64.unsigned nowa < 2 ^ 62; s_boot S = nowa;
         hhs3_cre x25519 aead_dec R L I M1 H1 M2 = Cre]
  (LOCALx ([temp HC._m1 m1; temp HC._m2 m2; temp HC._now_a (Vlong nowa); temp HC._ret (peer_result Cre);
            temp HC._all_ok (Vint (if hhs3_ok4 x25519 (hhs3_ok3 x25519 R I nowb MI) MI R MR
                                   then Int.one else Int.zero))] ++
           hhs3_cnt_temps a0 f0 l0 ++ hhs3_lvars gv L)
  (SEPx (hhs3_p5_sep gv L FR R S m1 m2 I M1 H1 MI PA1 Q M2 H2 MR
           (peer_rep Tsh (l_pb L) (hhs3_p5_pb x25519 R L M1 H1 Cre))
           (hbytes Tsh (resp_bytes (hhs3_M2m x25519 R M2)) (l_rimg L))
           (@data_at_ HCS Tsh t_mstate (l_st2 L))))).

(* after B (c = false) and after C (c = true: rimg weakened to any contents): acc2 = hhs3_p5_acc; when
   acc2, the model's result ST2 and st2 holds it *)
Definition hhs3_p5_SBC (c: bool) (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred :=
  EX R: hhs3_run, EX S: shim, EX m1: val, EX m2: val, EX a0: int64, EX f0: int64, EX l0: int64,
  EX I: hhs3_ini, EX M1: init_msg, EX H1: handshake,
  EX MI: list byte * list byte * list byte * list byte * list byte * list byte,
  EX nowb: int64, EX PA1: peer, EX CI1: list byte * list byte * list byte * list byte,
  EX CI2: list byte * list byte * list byte,
  EX Q: hhs3_rsp, EX M2: resp_msg, EX H2: handshake, EX MR: list byte * list byte * list byte * list byte * list byte,
  EX nowa: int64, EX Cre: option (val * peer), EX acc: bool, EX ST2: list byte * list byte,
  PROPx [hhs3_run_ok R; hhs3_cnt S a0 f0 l0; hhs3_after_init x25519 aead_enc R L I M1 H1 MI;
         hhs3_after_cin x25519 aead_dec R L M1 nowb PA1 CI1 CI2;
         hhs3_after_resp x25519 aead_enc R L M1 PA1 CI2 Q M2 H2 MR;
         0 <= Int64.unsigned nowa < 2 ^ 62; s_boot S = nowa;
         hhs3_cre x25519 aead_dec R L I M1 H1 M2 = Cre;
         acc = hhs3_p5_acc x25519 aead_dec R I MI M2;
         acc = true -> hhs3_mcr x25519 aead_dec R MI M2 = Some ST2]
  (LOCALx ([temp HC._m1 m1; temp HC._m2 m2; temp HC._now_a (Vlong nowa); temp HC._ret (peer_result Cre);
            temp HC._acc2 (Vint (if acc then Int.one else Int.zero));
            temp HC._all_ok (Vint (if hhs3_ok4 x25519 (hhs3_ok3 x25519 R I nowb MI) MI R MR
                                   then Int.one else Int.zero))] ++
           hhs3_cnt_temps a0 f0 l0 ++ hhs3_lvars gv L)
  (SEPx (hhs3_p5_sep gv L FR R S m1 m2 I M1 H1 MI PA1 Q M2 H2 MR
           (peer_rep Tsh (l_pb L) (hhs3_p5_pb x25519 R L M1 H1 Cre))
           (if c then hout Tsh 92 (l_rimg L) else hbytes Tsh (resp_bytes (hhs3_M2m x25519 R M2)) (l_rimg L))
           (hhs3_p5_st2 L acc ST2)))).

Definition hhs3_p5_SB (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred := hhs3_p5_SBC false gv L FR.
Definition hhs3_p5_SC (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred := hhs3_p5_SBC true gv L FR.

(* after D (and after E: the same state): the branches done, pb = the accepted state with its reference
   dropped again (PB2 = consume_response's peer) or unchanged; ret no longer used *)
Definition hhs3_p5_SD (gv: globals) (L: hhs3_loc) (FR: mpred) : environ -> mpred :=
  EX R: hhs3_run, EX S: shim, EX m1: val, EX m2: val, EX a0: int64, EX f0: int64, EX l0: int64,
  EX I: hhs3_ini, EX M1: init_msg, EX H1: handshake,
  EX MI: list byte * list byte * list byte * list byte * list byte * list byte,
  EX nowb: int64, EX PA1: peer, EX CI1: list byte * list byte * list byte * list byte,
  EX CI2: list byte * list byte * list byte,
  EX Q: hhs3_rsp, EX M2: resp_msg, EX H2: handshake, EX MR: list byte * list byte * list byte * list byte * list byte,
  EX nowa: int64, EX acc: bool, EX PB2: peer, EX ST2: list byte * list byte,
  PROPx [hhs3_run_ok R; hhs3_cnt S a0 f0 l0; hhs3_after_init x25519 aead_enc R L I M1 H1 MI;
         hhs3_after_cin x25519 aead_dec R L M1 nowb PA1 CI1 CI2;
         hhs3_after_resp x25519 aead_enc R L M1 PA1 CI2 Q M2 H2 MR;
         0 <= Int64.unsigned nowa < 2 ^ 62; s_boot S = nowa;
         acc = hhs3_p5_acc x25519 aead_dec R I MI M2;
         acc = true -> hhs3_mcr x25519 aead_dec R MI M2 = Some ST2 /\
                       hhs3_cre x25519 aead_dec R L I M1 H1 M2 = Some (l_pb L, PB2)]
  (LOCALx ([temp HC._m1 m1; temp HC._m2 m2; temp HC._now_a (Vlong nowa);
            temp HC._acc2 (Vint (if acc then Int.one else Int.zero));
            temp HC._all_ok (Vint (if hhs3_ok4 x25519 (hhs3_ok3 x25519 R I nowb MI) MI R MR
                                   then Int.one else Int.zero))] ++
           hhs3_cnt_temps a0 f0 l0 ++ hhs3_lvars gv L)
  (SEPx (hhs3_p5_sep gv L FR R S m1 m2 I M1 H1 MI PA1 Q M2 H2 MR
           (peer_rep Tsh (l_pb L) (if acc then p_set_refs PB2 Int.one else hhs3_PB1 x25519 R L M1 H1))
           (hout Tsh 92 (l_rimg L))
           (hhs3_p5_st2 L acc ST2)))).

(* ---------------------------------------------------------------------- *)
(* F's early return: everything back to main's stack frame                 *)
(* ---------------------------------------------------------------------- *)

(* main's 32 locals as the stack frame wants them (fn_vars order) *)
Definition hhs3_p5_frame (L: hhs3_loc) : list mpred :=
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
Definition hhs3_p5_free_stmt : Prop :=
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
  |-- fold_right_sepcon (hhs3_p5_frame L) * TT.

End States.
