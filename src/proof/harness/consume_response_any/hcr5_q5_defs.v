(* law consume_response_any, phase Q5 (the then-branch's statements 17..18) cut into segments:
   the statements and the intermediate states.

   Q5 = s17; s18
     s17  if (target == NULL) CHECK(ret == NULL && hnodes_same_except(peers, NULL))
          else ACC                                                           SQ4 -> QE   (hcr5_q5_if)
     s18  free(msg)                                                          QE  -> SE   (hcr5_q5_free)
   ACC (the else branch, hcr5_q5_acc, 11 statements):
     A1  h = &target->p->handshake; s = &target->snap;
         CHECK(ret == target->p && target->p->refcount == target->refs + 1); wg_peer_put(ret)
                                                                             QA0 -> QA1  (hcr5_q5_A1)
     A2  CHECK(hnodes_same_except(peers, target->p))                         QA1 -> QA1  (hcr5_q5_A2)
     A3  CHECK(h->state == CONSUMED_RESPONSE); CHECK(remote_ephemeral); CHECK(hash && chaining_key);
         CHECK(remote_index == sender_index)                                 QA1 -> QA1  (hcr5_q5_A3)
     A4  CHECK(entry fields, static_identity, ephemeral_private, remote_static, precomputed ss, psk,
         latest_timestamp, last_initiation_consumption all as in the snapshot) QA1 -> QA1  (hcr5_q5_A4)
     A5  CHECK(target->p->refcount == target->refs && pr_same(&target->rest, target->p))
                                                                             QA1 -> QE   (hcr5_q5_A5)
   The pure facts shared by the segments: hcr5_q5_pure.v (statement hcr5_q5_pure_stmt, a hypothesis of the
   segments). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
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
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_cut.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_model.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_spec.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_defs.
Require WgNoise.harness.x_consume_response_any.code.

#[local] Existing Instance W_consume_response_any.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The statements                                                          *)
(* ---------------------------------------------------------------------- *)

Definition hcr5_q5_s17 := ltac:(let x := eval cbv beta iota delta [hcr5_tl hcr5_seql firstn skipn hcr5_tstmts] in (hcr5_seql (hcr5_tl 17 1)) in exact x).
Definition hcr5_q5_s18 := ltac:(let x := eval cbv beta iota delta [hcr5_tl hcr5_seql firstn skipn hcr5_tstmts] in (hcr5_seql (hcr5_tl 18 1)) in exact x).

(* the else branch of s17, as a list of statements *)
Definition hcr5_q5_acc : list statement :=
  ltac:(let x := eval cbv beta iota delta [hcr5_flat hcr5_q5_s17] in
        (match hcr5_q5_s17 with Sifthenelse _ _ c => hcr5_flat c | _ => [] end) in exact x).

Lemma hcr5_q5_acc_length : length hcr5_q5_acc = 11%nat.
Proof. reflexivity. Qed.

Definition hcr5_q5_A1 := ltac:(let x := eval cbv beta iota delta [hcr5_seql firstn skipn hcr5_q5_acc] in (hcr5_seql (firstn 4 hcr5_q5_acc)) in exact x).
Definition hcr5_q5_A2 := ltac:(let x := eval cbv beta iota delta [hcr5_seql firstn skipn hcr5_q5_acc] in (hcr5_seql (firstn 1 (skipn 4 hcr5_q5_acc))) in exact x).
Definition hcr5_q5_A3 := ltac:(let x := eval cbv beta iota delta [hcr5_seql firstn skipn hcr5_q5_acc] in (hcr5_seql (firstn 4 (skipn 5 hcr5_q5_acc))) in exact x).
Definition hcr5_q5_A4 := ltac:(let x := eval cbv beta iota delta [hcr5_seql firstn skipn hcr5_q5_acc] in (hcr5_seql (firstn 1 (skipn 9 hcr5_q5_acc))) in exact x).
Definition hcr5_q5_A5 := ltac:(let x := eval cbv beta iota delta [hcr5_seql firstn skipn hcr5_q5_acc] in (hcr5_seql (skipn 10 hcr5_q5_acc)) in exact x).

(* ---------------------------------------------------------------------- *)
(* The states                                                              *)
(* ---------------------------------------------------------------------- *)

(* the accepted peer after wg_peer_put: the kernel's new state with its reference count back
   (rc_sub1 (rc_add1 r) = r: prot_model3's rc_sub1_add1) *)
Definition hcr5_q5_put (P: peer) (M: resp_msg) (ck h: list byte) : peer :=
  p_set_refs (hcr5_new P M ck h) (p_refs P).

(* the scratch locals untouched in Q5's acceptance branch (st and img_after are listed apart) *)
Definition hcr5_q5_scr (L: hcr5_loc) : list mpred :=
  [hout Tsh 32 (l_pub L); @data_at_ HCS Tsh t_mresp (l_mr L); @data_at_ HCS Tsh t_mstate (l_cur L);
   hout Tsh 32 (l_eraw L); hout Tsh 32 (l_ei L); @data_at_ HCS Tsh t_mstate (l_before L)].

Section States.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* the objects main lends to hnodes_same_except (common4's vobj): A's device (the peers' p_device and the
   handshakes' static identity) and the kents (the peers' keypair slots), as they are in the world / the SEP *)
Definition hcr5_q5_VO (R: hcr5_run) (L: hcr5_loc) (T: tstate) (KE: list kent4) : list vobj :=
  [VDev Tsh (l_wa L) (hcr5_DAL x25519 R L); VKents (hcr5_khead KE) (map (kent_snapped T) KE)].

(* the objects main lends to pr_same (common4 v4.1: a kent's address is its index-table entry, lent with the
   table): A's device (p_device) and the index table (the keypair slots: kents, pool items); the other peers are
   appended by the caller *)
Definition hcr5_q5_VOp (R: hcr5_run) (L: hcr5_loc) (T: tstate) : list vobj :=
  [VDev Tsh (l_wa L) (hcr5_DAL x25519 R L); VItab Tsh (l_ita L) T].

(* the acceptance branch at its start: the harness's model accepted the peer at a (state P before the call,
   chaining key ck, hash h); by hcr5_agree the kernel returned a and the peer at a is hcr5_new P M ck h;
   target = a's node; st = the model's state *)
Definition hcr5_q5_QA0 (gv: globals) (L: hcr5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcr5_run, EX S: shim, EX NS: list hnode4, EX PS: list (val * share * peer), EX head: val, EX nb: val,
  EX T: tstate, EX KE: list kent4, EX m: val, EX M: resp_msg,
  EX a: val, EX P: peer, EX ck: list byte, EX h: list byte,
  PROPx [hcr5_run_ok R; hcr5_list_ok L (hcr5_ka KE) NS PS head nb; hcr5_pool (hcr5_ka KE) PS T; m <> nullval;
         rm_ok M; hcr5_tg x25519 aead_dec R T PS M = Some (a, P, ck, h)]
  (LOCALx ([temp HR5._kes (hcr5_khead KE); temp HR5._msg m; temp HR5._ret a;
            temp HR5._target (hcr5_nfind NS a)] ++ hcr5_lvars gv L)
  (SEPx (hcr5_world x25519 R L NS (hnodes_snapped4 T NS PS) head T ++
         [peers_rep (supd PS a (hcr5_new P M ck h));
          hbytes Tsh (resp_bytes M) (l_img L); kents_rep W (hcr5_khead KE) (map (kent_snapped T) KE);
          hcr5_tok t_resp m; resp_rep Ews m M;
          @data_at HCS Tsh t_mstate (mstate_val ck h) (l_st L); hbytes Tsh (resp_bytes M) (l_imga L)] ++
         hcr5_globs gv S FR ++ hcr5_snaps L (hcr5_DAL x25519 R L) head S ++ hcr5_q5_scr L))).

(* after A1 (and after A2, A3, A4): h = &a->handshake, s = &target->snap (offset 8 of struct hnode), the
   peer's reference count back (hcr5_q5_put) *)
Definition hcr5_q5_QA1 (gv: globals) (L: hcr5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcr5_run, EX S: shim, EX NS: list hnode4, EX PS: list (val * share * peer), EX head: val, EX nb: val,
  EX T: tstate, EX KE: list kent4, EX m: val, EX M: resp_msg,
  EX a: val, EX P: peer, EX ck: list byte, EX h: list byte,
  PROPx [hcr5_run_ok R; hcr5_list_ok L (hcr5_ka KE) NS PS head nb; hcr5_pool (hcr5_ka KE) PS T; m <> nullval;
         rm_ok M; hcr5_tg x25519 aead_dec R T PS M = Some (a, P, ck, h)]
  (LOCALx ([temp HR5._kes (hcr5_khead KE); temp HR5._msg m; temp HR5._ret a;
            temp HR5._target (hcr5_nfind NS a); temp HR5._h__1 (hs_addr a);
            temp HR5._s (offset_val 8 (hcr5_nfind NS a))] ++ hcr5_lvars gv L)
  (SEPx (hcr5_world x25519 R L NS (hnodes_snapped4 T NS PS) head T ++
         [peers_rep (supd PS a (hcr5_q5_put P M ck h));
          hbytes Tsh (resp_bytes M) (l_img L); kents_rep W (hcr5_khead KE) (map (kent_snapped T) KE);
          hcr5_tok t_resp m; resp_rep Ews m M;
          @data_at HCS Tsh t_mstate (mstate_val ck h) (l_st L); hbytes Tsh (resp_bytes M) (l_imga L)] ++
         hcr5_globs gv S FR ++ hcr5_snaps L (hcr5_DAL x25519 R L) head S ++ hcr5_q5_scr L))).

End States.

(* after s17 (both branches): hcr5_SE with the message still allocated *)
Definition hcr5_q5_QE (x25519: list byte -> list byte -> list byte) (gv: globals) (L: hcr5_loc) (FR: mpred)
  : environ -> mpred :=
  EX R: hcr5_run, EX S: shim, EX NS: list hnode4, EX NS': list hnode4, EX PS: list (val * share * peer),
  EX head: val, EX T: tstate, EX KE: list kent4, EX m: val, EX M: resp_msg,
  PROPx [hcr5_run_ok R; hnodes_peers4 NS' PS; peers_wf PS; hcr5_pool (hcr5_ka KE) PS T; m <> nullval; rm_ok M;
         Forall (fun x : val * share * peer => match x with (_, sh, _) => sh = Ews end) PS]
  (LOCALx ([temp HR5._kes (hcr5_khead KE); temp HR5._msg m] ++ hcr5_lvars gv L)
  (SEPx (hcr5_world x25519 R L NS NS' head T ++
         [peers_rep PS; hout Tsh 92 (l_img L); kents_rep W (hcr5_khead KE) KE;
          hcr5_tok t_resp m; resp_rep Ews m M] ++
         hcr5_globs gv S FR ++ hcr5_snaps0 L ++ hcr5_scr L))).

(* ---------------------------------------------------------------------- *)
(* The cuts                                                                *)
(* ---------------------------------------------------------------------- *)

Lemma hcr5_q5_s17_eq : exists b c1, hcr5_q5_s17 = Sifthenelse b c1 (hcr5_seql hcr5_q5_acc).
Proof. eexists; eexists; reflexivity. Qed.

Lemma hcr5_q5_cut {Espec: OracleKind} Delta P Q1 R :
  semax Delta P hcr5_q5_s17 (overridePost Q1 R) ->
  semax Delta Q1 hcr5_q5_s18 R ->
  semax Delta P hcr5_Q5 R.
Proof.
  intros H1 H2. change hcr5_Q5 with (Ssequence hcr5_q5_s17 hcr5_q5_s18).
  eapply semax_seq; [exact H1 | exact H2].
Qed.

Lemma hcr5_q5_acc_cut {Espec: OracleKind} Delta P Q1 Q R :
  semax Delta P hcr5_q5_A1 (overridePost Q1 R) ->
  semax Delta Q1 hcr5_q5_A2 (overridePost Q1 R) ->
  semax Delta Q1 hcr5_q5_A3 (overridePost Q1 R) ->
  semax Delta Q1 hcr5_q5_A4 (overridePost Q1 R) ->
  semax Delta Q1 hcr5_q5_A5 (overridePost Q R) ->
  semax Delta P (hcr5_seql hcr5_q5_acc) (overridePost Q R).
Proof.
  intros H1 H2 H3 H4 H5.
  change (hcr5_seql hcr5_q5_acc) with
    (hcr5_seqs (firstn 4 hcr5_q5_acc) (hcr5_seqs (firstn 1 (skipn 4 hcr5_q5_acc))
      (hcr5_seqs (firstn 4 (skipn 5 hcr5_q5_acc)) (hcr5_seqs (firstn 1 (skipn 9 hcr5_q5_acc)) hcr5_q5_A5)))).
  eapply hcr5_semax_cut; [discriminate | rewrite hcr5_overridePost2; exact H1 |].
  eapply hcr5_semax_cut; [discriminate | rewrite hcr5_overridePost2; exact H2 |].
  eapply hcr5_semax_cut; [discriminate | rewrite hcr5_overridePost2; exact H3 |].
  eapply hcr5_semax_cut; [discriminate | rewrite hcr5_overridePost2; exact H4 | exact H5].
Qed.
