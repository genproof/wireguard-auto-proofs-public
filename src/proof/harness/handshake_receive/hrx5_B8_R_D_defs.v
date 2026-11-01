(* law handshake_receive: phase B8, branch R, segment D: statements 8..9 of branch R. A port of law handshake_clear's P7 loop.

   hrx5_B8R_D = S8 ; S9 with
     S8 = CHECK(pr_same(&target->rest, target->p))              (hrx5_B8RD_s8: RB -> RB, child)
     S9 = nd = peers; for (; nd; nd = nd->next) { if (nd == target) continue; CHK; HIF }
   CHK = CHECK(hs_same_but_next(&nd->snap, &nd->p->handshake) && nd->p->refcount.refcount == nd->refs &&
               pr_same(&nd->rest, nd->p))                            (hrx5_B8RD_chk, child)
   HIF = t = nd->snap.hashed; if (t) { CHECK(table_has(&itd, &nd->p->handshake.entry)); hashed++; }
                                                                     (hrx5_B8RD_hif, child)

   The loop's states (Section Loop): every value the loop does not change is a section variable (the temps
   vh .. vpath, the device D, the table Tf, the frame FRM = the rest of hrx5_B8R_RB's SEP); the target is node
   j (address tg, peer a, its new state Pf: the peers are upd_Znth j PS (a, Ews, Pf)); the node list holds
   hnodes_snapped4 T NS PS (snapshots of the ORIGINAL peers PS, taken in T); the table is Tf = T or
   t_remove T (hs_addr a) (hrx5_B8RD_hyp).  The node of index k: address hn_addr (Znth k NS), peer
   (q, Ews, Q) = Znth k PS, its value hrx5_B8RD_nv q (hs_snap_cur T q Q) Q nx (nx: the next node).
   `hashed` counts hrx5_B8R_nh T a (firstn k PS). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_cut.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mspec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require WgNoise.contracts.x_handshake_receive.
Require WgNoise.harness.x_handshake_receive.code.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_defs.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* the statements                                                          *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_B8RD_s8 : statement :=
  ltac:(let x := eval cbv delta [hrx5_B8R_D] in hrx5_B8R_D in match x with Ssequence ?a _ => exact a end).
Definition hrx5_B8RD_s9 : statement :=
  ltac:(let x := eval cbv delta [hrx5_B8R_D] in hrx5_B8R_D in match x with Ssequence _ ?a => exact a end).
Definition hrx5_B8RD_s0 : statement :=
  ltac:(let x := eval cbv delta [hrx5_B8RD_s9] in hrx5_B8RD_s9 in match x with Ssequence ?a _ => exact a end).
Definition hrx5_B8RD_body : statement :=
  ltac:(let x := eval cbv delta [hrx5_B8RD_s9] in hrx5_B8RD_s9 in
        match x with Ssequence _ (Sloop ?b _) => exact b end).
Definition hrx5_B8RD_incr : statement :=
  ltac:(let x := eval cbv delta [hrx5_B8RD_s9] in hrx5_B8RD_s9 in
        match x with Ssequence _ (Sloop _ ?c) => exact c end).
Definition hrx5_B8RD_ifb : statement :=
  ltac:(let x := eval cbv delta [hrx5_B8RD_body] in hrx5_B8RD_body in match x with Ssequence ?a _ => exact a end).
Definition hrx5_B8RD_ifc : statement :=
  ltac:(let x := eval cbv delta [hrx5_B8RD_body] in hrx5_B8RD_body in
        match x with Ssequence _ (Ssequence ?a _) => exact a end).
Definition hrx5_B8RD_chk : statement :=
  ltac:(let x := eval cbv delta [hrx5_B8RD_body] in hrx5_B8RD_body in
        match x with Ssequence _ (Ssequence _ (Ssequence ?a _)) => exact a end).
Definition hrx5_B8RD_hif : statement :=
  ltac:(let x := eval cbv delta [hrx5_B8RD_body] in hrx5_B8RD_body in
        match x with Ssequence _ (Ssequence _ (Ssequence _ ?a)) => exact a end).

Lemma hrx5_B8RD_eq : hrx5_B8R_D = Ssequence hrx5_B8RD_s8 hrx5_B8RD_s9.
Proof. reflexivity. Qed.
Lemma hrx5_B8RD_s9_eq : hrx5_B8RD_s9 = Ssequence hrx5_B8RD_s0 (Sloop hrx5_B8RD_body hrx5_B8RD_incr).
Proof. reflexivity. Qed.
Lemma hrx5_B8RD_body_eq :
  hrx5_B8RD_body = Ssequence hrx5_B8RD_ifb (Ssequence hrx5_B8RD_ifc (Ssequence hrx5_B8RD_chk hrx5_B8RD_hif)).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* the node's value, the segment of the node list                          *)
(* ---------------------------------------------------------------------- *)

(* the value of the node of peer (q, Q) (snapshot sn), next nx: ONE constant (kernel cost) *)
Definition hrx5_B8RD_nv (q: val) (sn: hsnap) (Q: peer) (nx: val) : @reptype W_handshake_receive t_hnode4 :=
  (q, (hsnap_val sn, (Vint (p_refs Q), (prsnap_val Q, nx)))).

(* a segment of the node list, from l to e (the nodes' values at CKS, as in hnodes_rep4) *)
Fixpoint hrx5_B8RD_seg (l e: val) (NS: list hnode4) : mpred :=
  match NS with
  | [] => !! (l = e) && emp
  | N :: NS' =>
      !! (l = hn_addr N) &&
      EX nx: val,
        @malloc_token W_handshake_receive Ews t_hnode4 l *
        @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) l *
        @malloc_token W_handshake_receive Ews t_peer (hn_p N) *
        hrx5_B8RD_seg nx e NS'
  end.

(* the head of the rest of the list after k nodes *)
Definition hrx5_B8RD_at (NS: list hnode4) (k: Z) : val := hrx5_head (skipn (Z.to_nat k) NS).

(* ---------------------------------------------------------------------- *)
(* the states                                                              *)
(* ---------------------------------------------------------------------- *)

Section Loop.
Variable x25519: list byte -> list byte -> list byte.
Variables (gv: globals) (L: hrx5_loc) (R: hrx5_run) (NS: list hnode4) (PS: list (val * share * peer))
  (KE: list kent4) (T: tstate) (head nk: val) (j: Z) (a tg: val) (Pf: peer) (Tf: tstate) (D: device) (FRM: mpred).
(* the values of the temps the loop does not change (hrx5_B8R_St's, but nd and hashed) *)
Variables (vh vs vallok vsess vnk vkes vsteps vi vnow vlul vbuf vmi vmr vmc vimg vlen vkind vai var vhead0
           vpath: val).

(* what the loop needs of the state: the invariant of the packet loop, the target j (node tg, peer a), the
   nodes pairwise distinct, the table T or T without a's handshake entry *)
Definition hrx5_B8RD_hyp : Prop :=
  hrx5_inv x25519 R L NS PS KE T head nk /\ 0 <= j < Zlength NS /\ hn_p (Znth j NS) = a /\
  tg = hn_addr (Znth j NS) /\ NoDup (map hn_addr NS) /\ (Tf = T \/ Tf = t_remove T (hs_addr a)).

(* the temps: hrx5_B8R_St's (with nd in front, hashed = h) *)
Definition hrx5_B8RD_lcr (h: Z) : list localdef :=
  [temp HM._h__2 vh; temp HM._s__1 vs; temp HM._alloc_ok vallok; temp HM._session vsess;
   temp HM._hashed (Vlong (Int64.repr h));
   temp HM._nk vnk; temp HM._kes vkes; temp HM._steps vsteps; temp HM._i vi; temp HM._now vnow;
   temp HM._m_lul vlul;
   temp HM._buf vbuf; temp HM._mi vmi; temp HM._mr vmr; temp HM._mc vmc;
   temp HM._img vimg; temp HM._len vlen; temp HM._kind vkind; temp HM._acc_init vai; temp HM._acc_resp var;
   temp HM._target tg; temp HM._head0 vhead0; temp HM._path vpath] ++ hrx5_lvars gv L.
Definition hrx5_B8RD_lc (x: val) (h: Z) : list localdef := temp HM._nd x :: hrx5_B8RD_lcr h.

(* the count of the other peers' entries in T among the first k *)
Definition hrx5_B8RD_nhk (k: Z) : Z := hrx5_B8R_nh T a (firstn (Z.to_nat k) PS).

(* what the loop does not touch *)
Definition hrx5_B8RD_fix : list mpred :=
  [device_rep Tsh (l_wd L) D; itable Tsh (l_itd L) Tf;
   @data_at W_handshake_receive Tsh (tptr t_hnode4) (hrx5_head (hnodes_snapped4 T NS PS)) (l_peers L); FRM].

(* before the loop (after S8, nd not yet set) and at its exit *)
Definition hrx5_B8RD_P0 : environ -> mpred :=
  PROPx []
  (LOCALx (hrx5_B8RD_lcr 0)
  (SEPx (hrx5_B8RD_fix ++
         [hnodes_rep4 W_handshake_receive (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS);
          peers_rep (upd_Znth j PS (a, Ews, Pf))]))).
Definition hrx5_B8RD_X : environ -> mpred :=
  PROPx []
  (LOCALx (hrx5_B8RD_lc nullval (hrx5_B8R_nh T a PS))
  (SEPx (hrx5_B8RD_fix ++
         [hnodes_rep4 W_handshake_receive (hrx5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS);
          peers_rep (upd_Znth j PS (a, Ews, Pf))]))).

(* the loop invariant: k nodes done, nd = the next one (NULL at the end) *)
Definition hrx5_B8RD_inv (k: Z) : environ -> mpred :=
  PROPx [0 <= k <= Zlength NS]
  (LOCALx (hrx5_B8RD_lc (hrx5_B8RD_at NS k) (hrx5_B8RD_nhk k))
  (SEPx (hrx5_B8RD_fix ++
         [hrx5_B8RD_seg (hrx5_head (hnodes_snapped4 T NS PS)) (hrx5_B8RD_at NS k)
            (firstn (Z.to_nat k) (hnodes_snapped4 T NS PS));
          hnodes_rep4 W_handshake_receive (hrx5_B8RD_at NS k) (skipn (Z.to_nat k) (hnodes_snapped4 T NS PS));
          peers_rep (upd_Znth j PS (a, Ews, Pf))]))).

(* at the node of index k (peer (q, Ews, Q) = Znth k PS, next node nx), with `hashed` = h and extra facts pl:
   - hrx5_B8RD_Q0 (after the two ifs: k <> j, h = the count before k): the pre- and postcondition of CHK, the
     precondition of HIF;
   - hrx5_B8RD_Q1 (h = the count up to k inclusive): the postcondition of HIF = the loop's continue state *)
Definition hrx5_B8RD_Q (k: Z) (nx q: val) (Q: peer) (h: Z) (pl: list Prop) : environ -> mpred :=
  PROPx ([0 <= k < Zlength NS; Znth k PS = (q, Ews, Q)] ++ pl)
  (LOCALx (hrx5_B8RD_lc (hn_addr (Znth k NS)) h)
  (SEPx (hrx5_B8RD_fix ++
         [hrx5_B8RD_seg (hrx5_head (hnodes_snapped4 T NS PS)) (hn_addr (Znth k NS))
            (firstn (Z.to_nat k) (hnodes_snapped4 T NS PS));
          @malloc_token W_handshake_receive Ews t_hnode4 (hn_addr (Znth k NS));
          @data_at W_handshake_receive Ews t_hnode4 (hrx5_B8RD_nv q (hs_snap_cur T q Q) Q nx) (hn_addr (Znth k NS));
          @malloc_token W_handshake_receive Ews t_peer q;
          hnodes_rep4 W_handshake_receive nx (skipn (Z.to_nat (k + 1)) (hnodes_snapped4 T NS PS));
          peers_rep (upd_Znth j PS (a, Ews, Pf))]))).

Definition hrx5_B8RD_Q0 (k: Z) (nx q: val) (Q: peer) : environ -> mpred :=
  hrx5_B8RD_Q k nx q Q (hrx5_B8RD_nhk k) [k <> j].

Definition hrx5_B8RD_Q1 (k: Z) (nx q: val) (Q: peer) : environ -> mpred :=
  hrx5_B8RD_Q k nx q Q (hrx5_B8RD_nhk (k + 1)) [].

(* the loop's continue state *)
Definition hrx5_B8RD_cont : environ -> mpred :=
  EX k: Z, EX nx: val, EX q: val, EX Q: peer, hrx5_B8RD_Q1 k nx q Q.

End Loop.
