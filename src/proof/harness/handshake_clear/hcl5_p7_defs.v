(* law handshake_clear, phase P7: the loop over the node list,
   statements 19..20 of main.

   The loop: hashed = 0; for (nd = peers; nd; nd = nd->next) { if (nd == target) continue; CHK; HIF }
   with CHK = the CHECK(hs_same_but_next && refcount == refs && pr_same) block (hcl5_p7_chk) and
   HIF = `t'23 = nd->snap.hashed; if (t'23) { CHECK(table_has(&it, &nd->p->handshake.entry)); hashed++; }`
   (hcl5_p7_hif).

   Notation: the target is node i, its peer p = hn_p (Znth i NS); the node list holds NS' = hnodes_snapped4 T NS PS
   (snapshots of the ORIGINAL peers PS, taken in T); the peers are now hcl5_clr i PS, the table t_remove T (hs_addr p).
   The node of index k: address hn_addr (Znth k NS), peer (q, Ews, Q) = Znth k PS, its value
   hcl5_p7_nv q (hs_snap_cur T q Q) Q nx (nx: the next node). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_world.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_cut.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_globals.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_spec.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_defs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_conv.
Require WgNoise.harness.x_handshake_clear.code.

#[local] Existing Instance W_handshake_clear.
Local Open Scope Z_scope.

Module HCL := WgNoise.harness.x_handshake_clear.code.

(* ---------------------------------------------------------------------- *)
(* the statements                                                          *)
(* ---------------------------------------------------------------------- *)

(* P7 = hashed = 0; (nd = peers; loop) *)
Definition hcl5_p7_s0 : statement :=
  ltac:(let x := eval cbv delta [hcl5_P7] in hcl5_P7 in match x with Ssequence ?a _ => exact a end).
Definition hcl5_p7_s1 : statement :=
  ltac:(let x := eval cbv delta [hcl5_P7] in hcl5_P7 in match x with Ssequence _ (Ssequence ?a _) => exact a end).
Definition hcl5_p7_body : statement :=
  ltac:(let x := eval cbv delta [hcl5_P7] in hcl5_P7 in
        match x with Ssequence _ (Ssequence _ (Sloop ?b _)) => exact b end).
Definition hcl5_p7_incr : statement :=
  ltac:(let x := eval cbv delta [hcl5_P7] in hcl5_P7 in
        match x with Ssequence _ (Ssequence _ (Sloop _ ?c)) => exact c end).
(* the body: if (!nd) break; if (nd == target) continue; CHK; HIF *)
Definition hcl5_p7_ifb : statement :=
  ltac:(let x := eval cbv delta [hcl5_p7_body] in hcl5_p7_body in match x with Ssequence ?a _ => exact a end).
Definition hcl5_p7_ifc : statement :=
  ltac:(let x := eval cbv delta [hcl5_p7_body] in hcl5_p7_body in
        match x with Ssequence _ (Ssequence ?a _) => exact a end).
Definition hcl5_p7_chk : statement :=
  ltac:(let x := eval cbv delta [hcl5_p7_body] in hcl5_p7_body in
        match x with Ssequence _ (Ssequence _ (Ssequence ?a _)) => exact a end).
Definition hcl5_p7_hif : statement :=
  ltac:(let x := eval cbv delta [hcl5_p7_body] in hcl5_p7_body in
        match x with Ssequence _ (Ssequence _ (Ssequence _ ?a)) => exact a end).

Lemma hcl5_p7_P7_eq : hcl5_P7 = Ssequence hcl5_p7_s0 (Ssequence hcl5_p7_s1 (Sloop hcl5_p7_body hcl5_p7_incr)).
Proof. reflexivity. Qed.
Lemma hcl5_p7_body_eq : hcl5_p7_body = Ssequence hcl5_p7_ifb (Ssequence hcl5_p7_ifc (Ssequence hcl5_p7_chk hcl5_p7_hif)).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* the node's value, the segment of the node list                          *)
(* ---------------------------------------------------------------------- *)

(* the value of the node of peer (q, Q) (snapshot sn), next nx: ONE constant (kernel cost) *)
Definition hcl5_p7_nv (q: val) (sn: hsnap) (Q: peer) (nx: val) : @reptype W_handshake_clear t_hnode4 :=
  (q, (hsnap_val sn, (Vint (p_refs Q), (prsnap_val Q, nx)))).

(* a segment of the node list, from l to e (the nodes' values at CKS, as in hnodes_rep4) *)
Fixpoint hcl5_p7_seg (l e: val) (NS: list hnode4) : mpred :=
  match NS with
  | [] => !! (l = e) && emp
  | N :: NS' =>
      !! (l = hn_addr N) &&
      EX nx: val,
        @malloc_token W_handshake_clear Ews t_hnode4 l *
        @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) l *
        @malloc_token W_handshake_clear Ews t_peer (hn_p N) *
        hcl5_p7_seg nx e NS'
  end.

(* the head of the rest of the list after k nodes *)
Definition hcl5_p7_at (NS: list hnode4) (k: Z) : val := hcl5_head (skipn (Z.to_nat k) NS).

(* ---------------------------------------------------------------------- *)
(* the states                                                              *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.

(* what the loop does not touch *)
Definition hcl5_p7_fix gv (L: hcl5_loc) FR (R: hcl5_run) (S: shim) (w: list int64) (NS: list hnode4)
  (T: tstate) (head: val) (KE: list kent4) (i: Z) : list mpred :=
  [device_rep Tsh (l_w L) (hcl5_D x25519 R L); itable Tsh (l_it L) (t_remove T (hs_addr (hn_p (Znth i NS))));
   ptable Tsh (l_pt L) head; hbytes Tsh (r_raw R) (l_raw L);
   @data_at W_handshake_clear Tsh (tptr t_hnode4) (hcl5_head NS) (l_peers L);
   kents_rep W_handshake_clear (hcl5_khead KE) (map (kent_snapped T) KE);
   @data_at CKS Tsh t_devsnap (devsnap_val (hcl5_D x25519 R L) head) (l_ds L);
   @data_at CKS Tsh t_shimsnap (shimsnap_val S w) (l_ss L);
   mem_mgr gv; shim_state4 gv S w; wg_consts gv; FR; hout Tsh 32 (l_pub L)].

(* the loop invariant: k nodes done, nd = the next one (NULL at the end) *)
Definition hcl5_p7_inv gv L FR R S w NS PS T head KE i (k: Z) : environ -> mpred :=
  PROPx [hcl5_run_ok R; hcl5_inv L NS PS KE T head; 0 <= i < Zlength NS; 0 <= k <= Zlength NS;
         NoDup (map hn_addr NS)]
  (LOCALx ([temp HCL._nd (hcl5_p7_at NS k);
            temp HCL._hashed (Vlong (Int64.repr (hcl5_nh T (hn_p (Znth i NS)) (firstn (Z.to_nat k) PS))));
            temp HCL._kes (hcl5_khead KE); temp HCL._target (hn_addr (Znth i NS))] ++ hcl5_lvars gv L)
  (SEPx (hcl5_p7_fix gv L FR R S w NS T head KE i ++
         [hcl5_p7_seg (hcl5_head NS) (hcl5_p7_at NS k) (firstn (Z.to_nat k) (hnodes_snapped4 T NS PS));
          hnodes_rep4 W_handshake_clear (hcl5_p7_at NS k) (skipn (Z.to_nat k) (hnodes_snapped4 T NS PS));
          peers_rep (hcl5_clr i PS)]))).

(* at the node of index k (peer (q, Ews, Q) = Znth k PS, next node nx), with `hashed` = h and extra facts pl:
   - hcl5_p7_Q0 (after the two ifs: k <> i, h = the count before k): the precondition of CHK, its postcondition
     and the precondition of HIF;
   - hcl5_p7_Q1 (h = the count up to k inclusive): the postcondition of HIF = the loop's continue state *)
Definition hcl5_p7_Q gv L FR R S w NS PS T head KE i (k: Z) (nx q: val) (Q: peer) (h: Z) (pl: list Prop)
  : environ -> mpred :=
  PROPx ([hcl5_run_ok R; hcl5_inv L NS PS KE T head; 0 <= i < Zlength NS; 0 <= k < Zlength NS;
          NoDup (map hn_addr NS); Znth k PS = (q, Ews, Q)] ++ pl)
  (LOCALx ([temp HCL._nd (hn_addr (Znth k NS)); temp HCL._hashed (Vlong (Int64.repr h));
            temp HCL._kes (hcl5_khead KE); temp HCL._target (hn_addr (Znth i NS))] ++ hcl5_lvars gv L)
  (SEPx (hcl5_p7_fix gv L FR R S w NS T head KE i ++
         [hcl5_p7_seg (hcl5_head NS) (hn_addr (Znth k NS)) (firstn (Z.to_nat k) (hnodes_snapped4 T NS PS));
          @malloc_token W_handshake_clear Ews t_hnode4 (hn_addr (Znth k NS));
          @data_at W_handshake_clear Ews t_hnode4 (hcl5_p7_nv q (hs_snap_cur T q Q) Q nx) (hn_addr (Znth k NS));
          @malloc_token W_handshake_clear Ews t_peer q;
          hnodes_rep4 W_handshake_clear nx (skipn (Z.to_nat (k + 1)) (hnodes_snapped4 T NS PS));
          peers_rep (hcl5_clr i PS)]))).

Definition hcl5_p7_Q0 gv L FR R S w NS PS T head KE i k nx q Q : environ -> mpred :=
  hcl5_p7_Q gv L FR R S w NS PS T head KE i k nx q Q
    (hcl5_nh T (hn_p (Znth i NS)) (firstn (Z.to_nat k) PS)) [k <> i].

Definition hcl5_p7_Q1 gv L FR R S w NS PS T head KE i k nx q Q : environ -> mpred :=
  hcl5_p7_Q gv L FR R S w NS PS T head KE i k nx q Q
    (hcl5_nh T (hn_p (Znth i NS)) (firstn (Z.to_nat (k + 1)) PS)) [].

(* the loop's continue state *)
Definition hcl5_p7_cont gv L FR R S w NS PS T head KE i : environ -> mpred :=
  EX k: Z, EX nx: val, EX q: val, EX Q: peer, hcl5_p7_Q1 gv L FR R S w NS PS T head KE i k nx q Q.

End States.
