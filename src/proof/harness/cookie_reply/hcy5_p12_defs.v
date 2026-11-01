(* law cookie_reply, phase P12: the cut of the phase into segments and the state they share.  Port of v1's hcy4_p12_defs.v.

   P12 = s70 (cn = cns; for (; cn; cn = cn->next) if (cn != target) CHECK(ck_same(&cn->cs, &cn->n->p->latest_cookie)))
         s71 (if (target == NULL) CHECK(hnodes_same_except(peers, NULL));
              else { tn = target->n; CHECK(hnodes_same_except(peers, tn->p));
                     CHECK(hs_same(&tn->snap, &tn->p->handshake) && tn->p->refcount.refcount == tn->refs &&
                           pr_same_but_cookie(&tn->rest, tn->p)); })
         s72 (CHECK(dev_same(&da, &wa) && ita.head == head0 && kents_same(kes) && shim_same(&ss)))
         s73 (cookie_img(img2, reply))
         s74 (CHECK(bytes_eq(img, img2, 64)))
         s75 (if (honest && np != NULL && ib.ok) { CHECK(target != NULL && target->n == np);
                                                   CHECK(bytes_eq(np->p->latest_cookie.cookie, cookie, 16)); })
   Segments: L = s70, X = s71, Y = s72, I = s73; s74, R = s75.  P12 changes nothing of hcy5_S11 (only temps), so
   every segment goes from the state hcy5_p12_St to the same state, over FIXED values (the EX of hcy5_S11
   opened), with the facts of hcy5_S11 (hcy5_p12_inv) as a Coq hypothesis, posts as normal_ret_assert (chained
   with hcy5_p12_seq). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require WgNoise.harness.x_cookie_reply.code.

#[local] Existing Instance W_cookie_reply.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The statements                                                          *)
(* ---------------------------------------------------------------------- *)

Definition hcy5_p12_s70 := ltac:(let x := eval cbv beta iota delta [hcy5_stmts nth] in (nth 70 hcy5_stmts Sskip) in exact x).
Definition hcy5_p12_s71 := ltac:(let x := eval cbv beta iota delta [hcy5_stmts nth] in (nth 71 hcy5_stmts Sskip) in exact x).
Definition hcy5_p12_s72 := ltac:(let x := eval cbv beta iota delta [hcy5_stmts nth] in (nth 72 hcy5_stmts Sskip) in exact x).
Definition hcy5_p12_s73 := ltac:(let x := eval cbv beta iota delta [hcy5_stmts nth] in (nth 73 hcy5_stmts Sskip) in exact x).
Definition hcy5_p12_s74 := ltac:(let x := eval cbv beta iota delta [hcy5_stmts nth] in (nth 74 hcy5_stmts Sskip) in exact x).
Definition hcy5_p12_s75 := ltac:(let x := eval cbv beta iota delta [hcy5_stmts nth] in (nth 75 hcy5_stmts Sskip) in exact x).

Lemma hcy5_p12_P12_eq :
  hcy5_P12 = Ssequence hcy5_p12_s70 (Ssequence hcy5_p12_s71 (Ssequence hcy5_p12_s72
               (Ssequence hcy5_p12_s73 (Ssequence hcy5_p12_s74 hcy5_p12_s75)))).
Proof. reflexivity. Qed.

(* a statement followed by the rest, its post a normal_ret_assert *)
Lemma hcy5_p12_seq {Espec: OracleKind} {cs: compspecs} Delta P Q R c1 c2 :
  semax Delta P c1 (normal_ret_assert Q) -> semax Delta Q c2 R -> semax Delta P (Ssequence c1 c2) R.
Proof.
  intros H1 H2. apply semax_seq with Q; auto.
  destruct R as [Rn Rb Rc Rr].
  eapply semax_post; [| | | | exact H1]; simpl; intros; try (apply andp_left2; apply derives_refl);
    apply andp_left2; apply FF_left.
Qed.

(* ---------------------------------------------------------------------- *)
(* The state                                                               *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* the facts of hcy5_S11 *)
Definition hcy5_p12_inv (R: hcy5_run) (L: hcy5_loc) (Q: hcy5_pkt) (m: val) (nonce rr CK: list byte)
  (CM: cookie_msg) (NS: list hnode4) (PS: list (val * share * peer)) (T: tstate) (np: val)
  (CL: list (val * val * option cookie)) (KE: list kent4) (CM': cookie_msg) (honest: bool) (now2: int64) : Prop :=
  hcy5_reply_ok x25519 xaead_enc R L Q m nonce rr CK CM /\ hcy5_lists_ok L (map ke_addr KE) NS PS /\
  hcy5_np_ok (hcy5_pubB x25519 R L) NS PS np /\ hcy5_T_ok PS KE T /\
  hcy5_cl_nodes CL NS /\ hcy5_cl_snap CL PS /\ cm_ok CM' /\
  (honest = true -> hcy5_honest_ok (hcy5_pubB x25519 R L) Q CM CM' NS PS T np) /\
  0 <= Int64.unsigned now2 < 2 ^ 62.

(* hcy5_S11's locals and SEP over fixed values *)
Definition hcy5_p12_St (gv: globals) (L: hcy5_loc) (FR: mpred) (R: hcy5_run) (S: shim) (m c rp: val)
  (Q: hcy5_pkt) (rr CK: list byte) (NS: list hnode4) (PS: list (val * share * peer)) (T: tstate) (np: val)
  (CL: list (val * val * option cookie)) (KE: list kent4) (CM': cookie_msg) (honest: bool) (now2: int64)
  : environ -> mpred :=
  PROPx []
  (LOCALx ([temp HY._kes (hcy5_khead KE); temp HY._cns (hcy5_chead CL);
            temp HY._msg m; temp HY._copy c; temp HY._reply rp; temp HY._np np;
            temp HY._honest (Vint (if honest then Int.one else Int.zero));
            temp HY._head0 (hd nullval (t_L T));
            temp HY._target (hcy5_tgt NS CL (hcy5_res xaead_dec T PS CM' now2))] ++ hcy5_lvars gv L)
  (SEPx (hcy5_aside x25519 R L T (hnodes_snapped4 T NS PS) (peers_after PS (hcy5_res xaead_dec T PS CM' now2)) ++
         hcy5_bside x25519 R L (hcy5_CC2 x25519 R L Q rr) ++
         hcy5_bufs x25519 R L ++ hcy5_pbufs L Q m c rp ++
         [cmsg_rep Ews rp CM'; hbytes Tsh CK (l_cookie L); hbytes Tsh (cookie_msg_bytes CM') (l_img L);
          hcy5_cns (hcy5_chead CL) CL; kents_rep W (hcy5_khead KE) (map (kent_snapped T) KE);
          @data_at CKS Tsh t_devsnap (devsnap_val (hcy5_DA x25519 R L) (hcy5_phead PS)) (l_da L);
          @data_at_ W Tsh t_devsnap (l_db L); @data_at_ W Tsh t_skbsnap (l_sks L);
          @data_at CKS Tsh t_shimsnap (shimsnap_val S hcy5_w0) (l_ss L)] ++
         hcy5_scrB L ++ hcy5_globs gv S FR))).

End States.
