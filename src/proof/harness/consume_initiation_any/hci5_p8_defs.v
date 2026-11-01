(* law consume_initiation_any, phase P8 cut into
   segments: the statements and the intermediate states.

   P8 = s31; s32; s33; s34; (s35; s36; s37; s38)
     s31..s32  init_img(img_after, msg); CHECK(bytes_eq(img, img_after))                   S7 -> Q1  (hci5_p8_a)
     s33       CHECK(dev_same(&ds, &wb) && itb.head == head0 && kents_same(kes) && shim_same(&ss))
                                                                                        Q1 -> Q1  (hci5_p8_b)
     s34       if (target == NULL) CHECK(ret == NULL && hnodes_same_except(peers, NULL))
               else ACC                                                                Q1 -> Q2  (hci5_p8_if)
     s35..s38  free(msg); kents_free(kes); hnodes_free(peers); return 0                  Q2 -> FF  (hci5_p8_c)
   ACC (the else branch, 13 statements, hci5_p8_acc):
     A1 = 0..3   h = &target->p->handshake; s = &target->snap;
                 CHECK(ret == target->p && target->p->refcount.refcount == target->refs + 1); wg_peer_put(ret)
                                                                                        QA0 -> QA1
     A2 = 4      CHECK(hnodes_same_except(peers, target->p))                             QA1 -> QA1
     A3 = 5..12  the CHECKs of the handshake's fields,
                 CHECK(target->p->refcount.refcount == target->refs && pr_same(&target->rest, target->p))
                                                                                        QA1 -> Q2
   From s34 on, the snapshot locals ds, ss are back to data_at_ (hci5_snaps0), ci too in Q2. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_cut.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_model.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_globals.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_spec.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_defs.
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* The statements                                                          *)
(* ---------------------------------------------------------------------- *)

Definition hci5_p8_s3132 := ltac:(let x := eval cbv beta iota delta [hci5_l hci5_seql firstn skipn hci5_stmts] in (hci5_seql (hci5_l 31 2)) in exact x).
Definition hci5_p8_s33 := ltac:(let x := eval cbv beta iota delta [hci5_l hci5_seql firstn skipn hci5_stmts] in (hci5_seql (hci5_l 33 1)) in exact x).
Definition hci5_p8_s34 := ltac:(let x := eval cbv beta iota delta [hci5_l hci5_seql firstn skipn hci5_stmts] in (hci5_seql (hci5_l 34 1)) in exact x).
Definition hci5_p8_s3538 := ltac:(let x := eval cbv beta iota delta [hci5_l hci5_seql firstn skipn hci5_stmts] in (hci5_seql (hci5_l 35 4)) in exact x).

(* the else branch of s34, as a list of statements *)
Definition hci5_p8_acc : list statement :=
  ltac:(let x := eval cbv beta iota delta [hci5_flat hci5_p8_s34] in
        (match hci5_p8_s34 with Sifthenelse _ _ c => hci5_flat c | _ => [] end) in exact x).

Lemma hci5_p8_acc_length : length hci5_p8_acc = 13%nat.
Proof. reflexivity. Qed.

Definition hci5_p8_A1 := ltac:(let x := eval cbv beta iota delta [hci5_seql firstn skipn hci5_p8_acc] in (hci5_seql (firstn 4 hci5_p8_acc)) in exact x).
Definition hci5_p8_A2 := ltac:(let x := eval cbv beta iota delta [hci5_seql firstn skipn hci5_p8_acc] in (hci5_seql (firstn 1 (skipn 4 hci5_p8_acc))) in exact x).
Definition hci5_p8_A3 := ltac:(let x := eval cbv beta iota delta [hci5_seql firstn skipn hci5_p8_acc] in (hci5_seql (skipn 5 hci5_p8_acc)) in exact x).

(* ---------------------------------------------------------------------- *)
(* The states                                                              *)
(* ---------------------------------------------------------------------- *)

(* the scratch locals still untouched in P8 (img_after and ci are listed apart) *)
Definition hci5_p8_scr (L: hci5_loc) : list mpred :=
  [hout Tsh 32 (l_pub L); hout Tsh 12 (l_ts L); @data_at_ HCS Tsh t_minit (l_mi L);
   hout Tsh 32 (l_eraw L); hout Tsh 32 (l_ss1 L); hout Tsh 32 (l_ss2 L)].

(* the accepted peer after wg_peer_put: the kernel's new state with its reference count back
   (rc_sub1 (rc_add1 r) = r below INT_MAX) *)
Definition hci5_p8_put (P: peer) (M: init_msg) (now: int64) (t ck2 h2: list byte) : peer :=
  p_set_refs (hci5_new P M now t ck2 h2) (p_refs P).

Section States.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* after s31..s32 (and after s33: the same state): hci5_S7 with img_after = the message's image *)
Definition hci5_p8_Q1 (gv: globals) (L: hci5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hci5_run, EX S: shim, EX w: list int64, EX NS: list hnode4, EX PS: list (val * share * peer),
  EX T: tstate, EX head: val, EX na: val, EX KE: list kent4, EX m: val, EX M: init_msg,
  PROPx [hci5_run_ok R; hci5_inv x25519 R L NS PS KE T head na; im_ok M;
         0 <= Int64.unsigned (s_boot S) < 2 ^ 62]
  (LOCALx ([temp HC._kes (hci5_khead KE); temp HC._msg m; temp HC._now (Vlong (s_boot S));
            temp HC._head0 (hd nullval (t_L T));
            temp HC._ret (peer_result (cin_res x25519 aead_dec (hci5_DB x25519 R L) PS M S));
            temp HC._target (hci5_tnode NS (hci5_tgt x25519 aead_dec (hci5_IB x25519 R) PS M (s_boot S)))] ++
           hci5_lvars gv L)
  (SEPx (hci5_world x25519 R L NS (hnodes_snapped4 T NS PS) T head ++
         [peers_rep (peers_after PS (cin_res x25519 aead_dec (hci5_DB x25519 R L) PS M S));
          kents_rep W (hci5_khead KE) (map (kent_snapped T) KE);
          @data_at CKS Tsh t_devsnap (devsnap_val (hci5_DB x25519 R L) head) (l_ds L);
          @data_at CKS Tsh t_shimsnap (shimsnap_val S w) (l_ss L);
          hbytes Tsh (init_bytes M) (l_img L); hbytes Tsh (init_bytes M) (l_imga L);
          hci5_tok t_init m; init_rep Ews m M;
          hci5_ci_rep (hci5_tgt x25519 aead_dec (hci5_IB x25519 R) PS M (s_boot S)) (l_ci L)] ++
         hci5_globs gv S w FR ++ hci5_p8_scr L))).

(* the acceptance branch at its start: the harness's model accepted the peer at a (state P before the call,
   timestamp t, chaining key ck2, hash h2); by hci5_agree the kernel returned a and the peer at a is
   hci5_new P ..; target = a's node; ds, ss back to data_at_ *)
Definition hci5_p8_QA0 (gv: globals) (L: hci5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hci5_run, EX S: shim, EX w: list int64, EX NS: list hnode4, EX PS: list (val * share * peer),
  EX T: tstate, EX head: val, EX na: val, EX KE: list kent4, EX m: val, EX M: init_msg,
  EX a: val, EX P: peer, EX t: list byte, EX ck2: list byte, EX h2: list byte,
  EX key: list val, EX spub: list val,
  PROPx [hci5_run_ok R; hci5_inv x25519 R L NS PS KE T head na; im_ok M;
         0 <= Int64.unsigned (s_boot S) < 2 ^ 62;
         hci5_tgt x25519 aead_dec (hci5_IB x25519 R) PS M (s_boot S) = Some (a, P, t, ck2, h2);
         Zlength key = 32; Zlength spub = 32]
  (LOCALx ([temp HC._kes (hci5_khead KE); temp HC._msg m; temp HC._now (Vlong (s_boot S)); temp HC._ret a;
            temp HC._target (hci5_nfind NS a)] ++ hci5_lvars gv L)
  (SEPx (hci5_world x25519 R L NS (hnodes_snapped4 T NS PS) T head ++
         [peers_rep (supd PS a (hci5_new P M (s_boot S) t ck2 h2));
          kents_rep W (hci5_khead KE) (map (kent_snapped T) KE);
          hbytes Tsh (init_bytes M) (l_img L); hbytes Tsh (init_bytes M) (l_imga L);
          hci5_tok t_init m; init_rep Ews m M;
          @data_at HCS Tsh t_mcinit (mcinit_val ck2 h2 key spub (bytes t)) (l_ci L)] ++
         hci5_globs gv S w FR ++ hci5_snaps0 L ++ hci5_p8_scr L))).

(* after A1 (and A2): h = &a->handshake, s = &target->snap (offset 8 of struct hnode), the peer's
   reference count back (hci5_p8_put), the shim and its warnings unchanged *)
Definition hci5_p8_QA1 (gv: globals) (L: hci5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hci5_run, EX S: shim, EX w: list int64, EX NS: list hnode4, EX PS: list (val * share * peer),
  EX T: tstate, EX head: val, EX na: val, EX KE: list kent4, EX m: val, EX M: init_msg,
  EX a: val, EX P: peer, EX t: list byte, EX ck2: list byte, EX h2: list byte,
  EX key: list val, EX spub: list val,
  PROPx [hci5_run_ok R; hci5_inv x25519 R L NS PS KE T head na; im_ok M;
         0 <= Int64.unsigned (s_boot S) < 2 ^ 62;
         hci5_tgt x25519 aead_dec (hci5_IB x25519 R) PS M (s_boot S) = Some (a, P, t, ck2, h2);
         Zlength key = 32; Zlength spub = 32]
  (LOCALx ([temp HC._kes (hci5_khead KE); temp HC._msg m; temp HC._now (Vlong (s_boot S)); temp HC._ret a;
            temp HC._target (hci5_nfind NS a); temp HC._h (hs_addr a);
            temp HC._s (offset_val 8 (hci5_nfind NS a))] ++ hci5_lvars gv L)
  (SEPx (hci5_world x25519 R L NS (hnodes_snapped4 T NS PS) T head ++
         [peers_rep (supd PS a (hci5_p8_put P M (s_boot S) t ck2 h2));
          kents_rep W (hci5_khead KE) (map (kent_snapped T) KE);
          hbytes Tsh (init_bytes M) (l_img L); hbytes Tsh (init_bytes M) (l_imga L);
          hci5_tok t_init m; init_rep Ews m M;
          @data_at HCS Tsh t_mcinit (mcinit_val ck2 h2 key spub (bytes t)) (l_ci L)] ++
         hci5_globs gv S w FR ++ hci5_snaps0 L ++ hci5_p8_scr L))).

(* after s34 (both branches): the peers PS2 (same addresses as PS, all at Ews), the nodes NS2 (same peers as NS),
   the kents KE2 (same addresses as KE), ci any; ready for free(msg), kents_free(kes), hnodes_free(peers) and the
   return *)
Definition hci5_p8_Q2 (gv: globals) (L: hci5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hci5_run, EX S: shim, EX w: list int64, EX NS: list hnode4, EX NS2: list hnode4,
  EX PS: list (val * share * peer), EX PS2: list (val * share * peer), EX T: tstate, EX head: val, EX na: val,
  EX KE: list kent4, EX KE2: list kent4, EX m: val, EX M: init_msg,
  PROPx [hci5_run_ok R; hci5_inv x25519 R L NS PS KE T head na; im_ok M;
         map peer_addr4 PS2 = map peer_addr4 PS;
         Forall (fun x => match x with (_, sh, _) => sh = Ews end) PS2;
         map hn_p NS2 = map hn_p NS; map ke_addr KE2 = map ke_addr KE]
  (LOCALx ([temp HC._kes (hci5_khead KE); temp HC._msg m] ++ hci5_lvars gv L)
  (SEPx (hci5_world x25519 R L NS NS2 T head ++
         [peers_rep PS2; kents_rep W (hci5_khead KE) KE2;
          hbytes Tsh (init_bytes M) (l_img L); hbytes Tsh (init_bytes M) (l_imga L);
          hci5_tok t_init m; init_rep Ews m M; @data_at_ HCS Tsh t_mcinit (l_ci L)] ++
         hci5_globs gv S w FR ++ hci5_snaps0 L ++ hci5_p8_scr L))).

End States.

(* the cut of P8 *)
Lemma hci5_p8_s34_eq : exists b c1, hci5_p8_s34 = Sifthenelse b c1 (hci5_seql hci5_p8_acc).
Proof. eexists; eexists; reflexivity. Qed.

Lemma hci5_p8_cut {Espec: OracleKind} Delta P Q1 Q2 R :
  semax Delta P hci5_p8_s3132 (overridePost Q1 R) ->
  semax Delta Q1 hci5_p8_s33 (overridePost Q1 R) ->
  semax Delta Q1 hci5_p8_s34 (overridePost Q2 R) ->
  semax Delta Q2 hci5_p8_s3538 R ->
  semax Delta P hci5_P8 R.
Proof.
  intros H1 H2 H3 H4.
  change hci5_P8 with (hci5_seqs (hci5_l 31 2) (hci5_seqs (hci5_l 33 1) (Ssequence hci5_p8_s34 hci5_p8_s3538))).
  eapply hci5_semax_cut; [discriminate | exact H1 |].
  eapply hci5_semax_cut; [discriminate | exact H2 |].
  eapply semax_seq; [exact H3 | exact H4].
Qed.

(* the cut of the else branch *)
Lemma hci5_p8_acc_cut {Espec: OracleKind} Delta P Q1 R :
  semax Delta P hci5_p8_A1 (overridePost Q1 R) ->
  semax Delta Q1 hci5_p8_A2 (overridePost Q1 R) ->
  semax Delta Q1 hci5_p8_A3 R ->
  semax Delta P (hci5_seql hci5_p8_acc) R.
Proof.
  intros H1 H2 H3.
  change (hci5_seql hci5_p8_acc) with (hci5_seqs (firstn 4 hci5_p8_acc) (hci5_seqs (firstn 1 (skipn 4 hci5_p8_acc)) hci5_p8_A3)).
  eapply hci5_semax_cut; [discriminate | exact H1 |].
  eapply hci5_semax_cut; [discriminate | exact H2 | exact H3].
Qed.
