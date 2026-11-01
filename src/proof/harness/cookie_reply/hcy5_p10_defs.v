(* law cookie_reply, phase P10: the cut into four segments and the three intermediate states.
   - A = statement 57: hnodes_snap(peers)                                     S9 -> hcy5_p10_TA
   - B = statement 58: for (cn = cns; cn; cn = cn->next) ck_take(&cn->cs, &cn->n->p->latest_cookie)
                                                                              hcy5_p10_TA -> hcy5_p10_TB
   - C = statements 59..61: kents_snap(kes); dev_take(&da, &wa); head0 = ita.head
                                                                              hcy5_p10_TB -> hcy5_p10_TC
   - D = statements 62..65: now = draw_boottime(); wg_shim_boottime_ns = now; shim_take(&ss);
         wg_cookie_message_consume(reply, &wa)                                hcy5_p10_TC -> S10
   TA = S9 with the nodes snapped (hcy5_aside .. T (hnodes_snapped4 T NS PS) PS); TB = TA with every cnode's
   snapshot taken (hcy5_cl_snap CL PS instead of hcy5_cl_none CL); TC = TB with the kents snapped
   (map (kent_snapped T) KE), da = A as a whole (devsnap_val (hcy5_DA ..) (hcy5_phead PS) at CKS) and
   temp head0 = hd nullval (t_L T). *)
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
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require WgNoise.harness.x_cookie_reply.code.

Local Open Scope logic.

Definition hcy5_p10_sA := ltac:(let x := eval cbv beta iota delta [hcy5_l hcy5_seql firstn skipn hcy5_stmts] in (hcy5_seql (hcy5_l 57 1)) in exact x).
Definition hcy5_p10_sB := ltac:(let x := eval cbv beta iota delta [hcy5_l hcy5_seql firstn skipn hcy5_stmts] in (hcy5_seql (hcy5_l 58 1)) in exact x).
Definition hcy5_p10_sC := ltac:(let x := eval cbv beta iota delta [hcy5_l hcy5_seql firstn skipn hcy5_stmts] in (hcy5_seql (hcy5_l 59 3)) in exact x).
Definition hcy5_p10_sD := ltac:(let x := eval cbv beta iota delta [hcy5_l hcy5_seql firstn skipn hcy5_stmts] in (hcy5_seql (hcy5_l 62 4)) in exact x).

Lemma hcy5_p10_eq : hcy5_P10 = Ssequence hcy5_p10_sA (Ssequence hcy5_p10_sB (hcy5_seqs (hcy5_l 59 3) hcy5_p10_sD)).
Proof. reflexivity. Qed.

Lemma hcy5_p10_sC_eq : hcy5_seql (hcy5_l 59 3) = hcy5_p10_sC.
Proof. reflexivity. Qed.

Section States.
Variable x25519: list byte -> list byte -> list byte.
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.

(* after A: S9 with the nodes holding the snapshots of the peers (table T) *)
Definition hcy5_p10_TA (gv: globals) (L: hcy5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcy5_run, EX S: shim, EX m: val, EX c: val, EX rp: val, EX Q: hcy5_pkt,
  EX nonce: list byte, EX rr: list byte, EX CK: list byte, EX CM: cookie_msg,
  EX NS: list hnode4, EX PS: list (val * share * peer), EX T: tstate, EX np: val,
  EX CL: list (val * val * option cookie), EX KE: list kent4, EX CM': cookie_msg, EX honest: bool,
  PROPx [hcy5_reply_ok x25519 xaead_enc R L Q m nonce rr CK CM; hcy5_lists_ok L (map ke_addr KE) NS PS;
         hcy5_np_ok (hcy5_pubB x25519 R L) NS PS np; hcy5_T_ok PS KE T;
         hcy5_cl_nodes CL NS; hcy5_cl_none CL; cm_ok CM';
         honest = true -> hcy5_honest_ok (hcy5_pubB x25519 R L) Q CM CM' NS PS T np]
  (LOCALx ([temp HY._kes (hcy5_khead KE); temp HY._cns (hcy5_chead CL);
            temp HY._msg m; temp HY._copy c; temp HY._reply rp; temp HY._np np;
            temp HY._honest (Vint (if honest then Int.one else Int.zero))] ++ hcy5_lvars gv L)
  (SEPx (hcy5_aside x25519 R L T (hnodes_snapped4 T NS PS) PS ++
         hcy5_bside x25519 R L (hcy5_CC2 x25519 R L Q rr) ++
         hcy5_bufs x25519 R L ++ hcy5_pbufs L Q m c rp ++
         [cmsg_rep Ews rp CM'; hbytes Tsh CK (l_cookie L); hbytes Tsh (cookie_msg_bytes CM') (l_img L);
          hcy5_cns (hcy5_chead CL) CL; kents_rep W (hcy5_khead KE) KE] ++
         hcy5_scrB L ++ hcy5_snaps0 L ++ hcy5_globs gv S FR))).

(* after B: every cnode holds its peer's cookie *)
Definition hcy5_p10_TB (gv: globals) (L: hcy5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcy5_run, EX S: shim, EX m: val, EX c: val, EX rp: val, EX Q: hcy5_pkt,
  EX nonce: list byte, EX rr: list byte, EX CK: list byte, EX CM: cookie_msg,
  EX NS: list hnode4, EX PS: list (val * share * peer), EX T: tstate, EX np: val,
  EX CL: list (val * val * option cookie), EX KE: list kent4, EX CM': cookie_msg, EX honest: bool,
  PROPx [hcy5_reply_ok x25519 xaead_enc R L Q m nonce rr CK CM; hcy5_lists_ok L (map ke_addr KE) NS PS;
         hcy5_np_ok (hcy5_pubB x25519 R L) NS PS np; hcy5_T_ok PS KE T;
         hcy5_cl_nodes CL NS; hcy5_cl_snap CL PS; cm_ok CM';
         honest = true -> hcy5_honest_ok (hcy5_pubB x25519 R L) Q CM CM' NS PS T np]
  (LOCALx ([temp HY._kes (hcy5_khead KE); temp HY._cns (hcy5_chead CL);
            temp HY._msg m; temp HY._copy c; temp HY._reply rp; temp HY._np np;
            temp HY._honest (Vint (if honest then Int.one else Int.zero))] ++ hcy5_lvars gv L)
  (SEPx (hcy5_aside x25519 R L T (hnodes_snapped4 T NS PS) PS ++
         hcy5_bside x25519 R L (hcy5_CC2 x25519 R L Q rr) ++
         hcy5_bufs x25519 R L ++ hcy5_pbufs L Q m c rp ++
         [cmsg_rep Ews rp CM'; hbytes Tsh CK (l_cookie L); hbytes Tsh (cookie_msg_bytes CM') (l_img L);
          hcy5_cns (hcy5_chead CL) CL; kents_rep W (hcy5_khead KE) KE] ++
         hcy5_scrB L ++ hcy5_snaps0 L ++ hcy5_globs gv S FR))).

(* after C: the kents hold their snapshots, da = A as a whole, head0 = the table's first entry *)
Definition hcy5_p10_TC (gv: globals) (L: hcy5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcy5_run, EX S: shim, EX m: val, EX c: val, EX rp: val, EX Q: hcy5_pkt,
  EX nonce: list byte, EX rr: list byte, EX CK: list byte, EX CM: cookie_msg,
  EX NS: list hnode4, EX PS: list (val * share * peer), EX T: tstate, EX np: val,
  EX CL: list (val * val * option cookie), EX KE: list kent4, EX CM': cookie_msg, EX honest: bool,
  PROPx [hcy5_reply_ok x25519 xaead_enc R L Q m nonce rr CK CM; hcy5_lists_ok L (map ke_addr KE) NS PS;
         hcy5_np_ok (hcy5_pubB x25519 R L) NS PS np; hcy5_T_ok PS KE T;
         hcy5_cl_nodes CL NS; hcy5_cl_snap CL PS; cm_ok CM';
         honest = true -> hcy5_honest_ok (hcy5_pubB x25519 R L) Q CM CM' NS PS T np]
  (LOCALx ([temp HY._kes (hcy5_khead KE); temp HY._cns (hcy5_chead CL);
            temp HY._msg m; temp HY._copy c; temp HY._reply rp; temp HY._np np;
            temp HY._honest (Vint (if honest then Int.one else Int.zero));
            temp HY._head0 (hd nullval (t_L T))] ++ hcy5_lvars gv L)
  (SEPx (hcy5_aside x25519 R L T (hnodes_snapped4 T NS PS) PS ++
         hcy5_bside x25519 R L (hcy5_CC2 x25519 R L Q rr) ++
         hcy5_bufs x25519 R L ++ hcy5_pbufs L Q m c rp ++
         [cmsg_rep Ews rp CM'; hbytes Tsh CK (l_cookie L); hbytes Tsh (cookie_msg_bytes CM') (l_img L);
          hcy5_cns (hcy5_chead CL) CL; kents_rep W (hcy5_khead KE) (map (kent_snapped T) KE);
          @data_at CKS Tsh t_devsnap (devsnap_val (hcy5_DA x25519 R L) (hcy5_phead PS)) (l_da L);
          @data_at_ W Tsh t_devsnap (l_db L); @data_at_ W Tsh t_skbsnap (l_sks L);
          @data_at_ W Tsh t_shimsnap (l_ss L)] ++
         hcy5_scrB L ++ hcy5_globs gv S FR))).

End States.
