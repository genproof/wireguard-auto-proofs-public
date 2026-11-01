(* law keypairs: the cut of check_all's body (harness/keypairs.c) into
   segments, their context and states.
   check_all's body =  hashed = 0; HEAD; SLOTS; LOOP; HS; OLOOP; KFIN; return t'43 == hashed + t'44
     HEAD  = hs_same_but_next(&hsm, &p->handshake), rest_same(&prm, p), p->refcount == prefs, dev_same(&dsm, w),
             warn_same() (if one fails: return 0)
     SLOTS = the three slot comparisons
     LOOP  = k = live; for (; k; k = k->next) NODE        (NODE = the loop body after the test of k)
     HS    = if (p->handshake.entry.hashed) { table_has / table_index_unique checks; hashed++ }
     OLOOP = o = others; for (; o; o = o->next) ONODE      (ONODE = the loop body after the test of o)
     KFIN  = kents_same_but_next(kes, t) check; t'43 = table_len(t); t'44 = kents_hashed(kes)
   The context hkc5_G = bytes_eq_spec :: hkp5_G_check; the glue lifts the segments to the target's context. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Export WgNoise.proof.harness.keypairs.hkp5_spec.

#[local] Existing Instance W_keypairs.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* The context of check_all's body                                         *)
(* ---------------------------------------------------------------------- *)

Definition hkc5_G : funspecs := bytes_eq_spec :: hkp5_G_check.
Definition hkc5_Delta : tycontext := func_tycontext KC.f_check_all hkp5_V hkc5_G [].

(* ---------------------------------------------------------------------- *)
(* The statements                                                          *)
(* ---------------------------------------------------------------------- *)

Definition hkc5_head : statement :=
  ltac:(let x := eval cbv beta iota delta [KC.f_check_all fn_body] in
        (match fn_body KC.f_check_all with Ssequence _ (Ssequence s _) => s | _ => Sskip end) in exact x).
Definition hkc5_slots : statement :=
  ltac:(let x := eval cbv beta iota delta [KC.f_check_all fn_body] in
        (match fn_body KC.f_check_all with Ssequence _ (Ssequence _ (Ssequence s _)) => s | _ => Sskip end)
        in exact x).
Definition hkc5_loop : statement :=
  ltac:(let x := eval cbv beta iota delta [KC.f_check_all fn_body] in
        (match fn_body KC.f_check_all with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence s _))) => s
         | _ => Sskip end) in exact x).
Definition hkc5_hs : statement :=
  ltac:(let x := eval cbv beta iota delta [KC.f_check_all fn_body] in
        (match fn_body KC.f_check_all with
         | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence s _)))) => s
         | _ => Sskip end) in exact x).
Definition hkc5_oloop : statement :=
  ltac:(let x := eval cbv beta iota delta [KC.f_check_all fn_body] in
        (match fn_body KC.f_check_all with
         | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence s _))))) => s
         | _ => Sskip end) in exact x).
Definition hkc5_kfin : statement :=
  ltac:(let x := eval cbv beta iota delta [KC.f_check_all fn_body] in
        (match fn_body KC.f_check_all with
         | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _
             (Ssequence k (Ssequence f _))))))) => Ssequence k f
         | _ => Sskip end) in exact x).
Definition hkc5_ret : statement :=
  ltac:(let x := eval cbv beta iota delta [KC.f_check_all fn_body] in
        (match fn_body KC.f_check_all with
         | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _
             (Ssequence _ (Ssequence _ r))))))) => r
         | _ => Sskip end) in exact x).
(* the loop bodies after the tests of k / o (k = k->next, o = o->next are the loops' increments) *)
Definition hkc5_node : statement :=
  ltac:(let x := eval cbv beta iota delta [hkc5_loop] in
        (match hkc5_loop with Ssequence _ (Sloop (Ssequence _ s) _) => s | _ => Sskip end) in exact x).
Definition hkc5_onode : statement :=
  ltac:(let x := eval cbv beta iota delta [hkc5_oloop] in
        (match hkc5_oloop with Ssequence _ (Sloop (Ssequence _ s) _) => s | _ => Sskip end) in exact x).

Lemma hkc5_body_eq :
  fn_body KC.f_check_all =
  Ssequence (Sset KC._hashed (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Ssequence hkc5_head (Ssequence hkc5_slots (Ssequence hkc5_loop (Ssequence hkc5_hs
      (Ssequence hkc5_oloop
        (Ssequence (match hkc5_kfin with Ssequence k _ => k | _ => Sskip end)
          (Ssequence (match hkc5_kfin with Ssequence _ f => f | _ => Sskip end) hkc5_ret))))))).
Proof. reflexivity. Qed.

Lemma hkc5_loop_eq :
  hkc5_loop =
  Ssequence (Sset KC._k (Evar KC._live (tptr t_mk5)))
    (Sloop (Ssequence (Sifthenelse (Etempvar KC._k (tptr t_mk5)) Sskip Sbreak) hkc5_node)
       (Sset KC._k (Efield (Ederef (Etempvar KC._k (tptr t_mk5)) t_mk5) KC._next (tptr t_mk5)))).
Proof. reflexivity. Qed.

Lemma hkc5_oloop_eq :
  hkc5_oloop =
  Ssequence (Sset KC._o (Evar KC._others (tptr t_hnode4)))
    (Sloop (Ssequence (Sifthenelse (Etempvar KC._o (tptr t_hnode4)) Sskip Sbreak) hkc5_onode)
       (Sset KC._o (Efield (Ederef (Etempvar KC._o (tptr t_hnode4)) t_hnode4) KC._next (tptr t_hnode4)))).
Proof. reflexivity. Qed.

Lemma hkc5_ret_eq :
  hkc5_ret =
  Sreturn (Some (Ebinop Oeq (Etempvar KC._t'43 tulong)
                   (Ebinop Oadd (Etempvar KC._hashed tulong) (Etempvar KC._t'44 tulong) tulong) tint)).
Proof. reflexivity. Qed.

(* a default peer list item (Znth) *)
Definition hkc5_hs0 : handshake :=
  mkHS Int.zero Int64.zero nullval [] [] [] [] [] [] [] [] Int.zero.
Definition hkc5_ck0 : cookie := mkCookie Int64.zero false [] false [] [] [].
#[export] Instance hkc5_inh_x : Inhabitant (val * share * peer) :=
  (nullval, Tsh, mkPeer nullval false nullval nullval nullval hkc5_hs0 Int64.zero hkc5_ck0 Int.zero Int64.zero nullval).

(* ---------------------------------------------------------------------- *)
(* Counting                                                                *)
(* ---------------------------------------------------------------------- *)

(* the hashed nodes of the live list, the other peers whose handshake entry is hashed in T *)
Definition hkc5_nh (ML: list (val * hk5_mk)) : Z := Zlength (filter (fun x => m5_hashed (snd x)) ML).
Definition hkc5_oh (T: tstate) (PS: list (val * share * peer)) : Z :=
  Zlength (filter (fun x => vin (hs_addr (peer_addr4 x)) (t_L T)) PS).

(* ---------------------------------------------------------------------- *)
(* The states                                                              *)
(* ---------------------------------------------------------------------- *)

Definition hkc5_lv (F: hkp5_fix) (n: Z) : list localdef :=
  [temp KC._hashed (Vlong (Int64.repr n)); temp KC._p (f_p F); temp KC._t (f_t F); temp KC._w (f_w F);
   gvars (f_gv F)].

Section States.
Variable x25519: list byte -> list byte -> list byte.

(* the whole state (check_all's precondition) with hashed = n *)
Definition hkc5_S (F: hkp5_fix) (V: hkp5_val) (Y: hkp5_dyn) (O: hkp5_oth) (n: Z) : environ -> mpred :=
  PROPx [hkp5_fix_ok F V; hkp5_inv F V Y; hkp5_oth_ok F V O]
  (LOCALx (hkc5_lv F n)
  (SEPx (hkp5_SEP x25519 F V Y (hkp5_othR x25519 F V O)))).

End States.

(* the live loop's body for one node m (contents M, next field nx) and its keypair K at m5_kp M; FR: the rest *)
Definition hkc5_PN (F: hkp5_fix) (T: tstate) (P: peer) (m: val) (M: hk5_mk) (nx: val) (K: keypair) (n: Z)
  (FR: mpred) : environ -> mpred :=
  PROPx []
  (LOCALx (temp KC._k m :: hkc5_lv F n)
  (SEPx [hk5_node m M nx; keypair_rep W_keypairs (m5_kp M) K; itable Tsh (f_t F) T; peer_rep Tsh (f_p F) P; FR])).

(* P's handshake entry: hashed = n; FR: the rest *)
Definition hkc5_PH (F: hkp5_fix) (T: tstate) (P: peer) (n: Z) (FR: mpred) : environ -> mpred :=
  PROPx []
  (LOCALx (hkc5_lv F n)
  (SEPx [peer_rep Tsh (f_p F) P; itable Tsh (f_t F) T; FR])).

(* the others loop: the list head hd in the global others, the nodes NS, their peers PS, the table, objects VO
   lent to the comparisons (the glue lends [VDev (the device); VPeer (P)]), FR the rest *)
Definition hkc5_PO (F: hkp5_fix) (T: tstate) (hd: val) (NS: list hnode4) (PS: list (val * share * peer))
  (VO: list vobj) (n: Z) (FR: mpred) : environ -> mpred :=
  PROPx []
  (LOCALx (hkc5_lv F n)
  (SEPx [data_at Ews (tptr t_hnode4) hd (f_gv F KC._others); hnodes_rep4 W_keypairs hd NS; peers_rep PS;
         itable Tsh (f_t F) T; vobjs W_keypairs VO; FR])).

(* one node N of the others loop (next field nx) and its peer x = (q, sh, Q); VO: the lent objects (the glue
   lends the other peers of the list too, VPeers); FR the rest *)
Definition hkc5_PON (F: hkp5_fix) (T: tstate) (N: hnode4) (nx: val) (x: val * share * peer) (VO: list vobj)
  (n: Z) (FR: mpred) : environ -> mpred :=
  match x with (q, sh, Q) =>
  PROPx []
  (LOCALx (temp KC._o (hn_addr N) :: hkc5_lv F n)
  (SEPx [@data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N);
         peer_rep sh q Q; itable Tsh (f_t F) T; vobjs W_keypairs VO; FR]))
  end.

(* what the others loop's checks need of one node N and its peer x: N holds a snapshot sn of x's handshake
   (equal to the current one but the link), x's count and rest; the pointers compared are NULL or valid *)
Definition hkc5_on_ok (t: val) (T: tstate) (VO: list vobj) (N: hnode4) (x: val * share * peer) : Prop :=
  match x with (q, sh, Q) => exists sn: hsnap,
    hn_p N = q /\ hn_snap N = hsnap_val sn /\ hn_refs N = Vint (p_refs Q) /\ hn_rest N = prsnap_val Q /\
    readable_share sh /\ Forall vobj_ok VO /\ In (hs_addr q) (saddrs (t_D T)) /\
    Forall (vp_ok (hs_own q T VO)) (hs_ptrs_nn sn (hs_snap_cur T q Q)) /\
    Forall (vp_ok (q :: vobjs_addrs (VItab Tsh t T :: VO))) (pr_ptrs Q Q) /\
    snap_eqb_nn sn (hs_snap_cur T q Q) = true /\ pr_eqb Q Q = true /\
    sn_hashed sn = vin (hs_addr q) (t_L T)
  end.

(* the peers of PS but the i-th *)
Definition hkc5_rest (PS: list (val * share * peer)) (i: Z) : list (val * share * peer) :=
  sublist 0 i PS ++ sublist (i + 1) (Zlength PS) PS.

(* KFIN: the kents (head kd in the global kes), the table, lent objects VO (the glue lends [VPeers PS]) *)
Definition hkc5_PK (F: hkp5_fix) (T: tstate) (kd: val) (KE: list kent4) (VO: list vobj) (n: Z) (FR: mpred)
  : environ -> mpred :=
  PROPx []
  (LOCALx (hkc5_lv F n)
  (SEPx [data_at Ews (tptr t_kent) kd (f_gv F KC._kes); kents_rep W_keypairs kd KE; itable Tsh (f_t F) T;
         vobjs W_keypairs VO; FR])).

(* after KFIN: t'43 = table_len(t), t'44 = kents_hashed(kes) *)
Definition hkc5_PK' (F: hkp5_fix) (T: tstate) (kd: val) (KE: list kent4) (VO: list vobj) (n: Z) (FR: mpred)
  : environ -> mpred :=
  PROPx []
  (LOCALx (temp KC._t'43 (Vlong (Int64.repr (Zlength (t_L T)))) ::
           temp KC._t'44 (Vlong (Int64.repr (kents_hashed_n T KE))) :: hkc5_lv F n)
  (SEPx [data_at Ews (tptr t_kent) kd (f_gv F KC._kes); kents_rep W_keypairs kd KE; itable Tsh (f_t F) T;
         vobjs W_keypairs VO; FR])).

(* ---------------------------------------------------------------------- *)
(* The segment statements *)
(* ---------------------------------------------------------------------- *)

(* HEAD: under the invariant, the five checks pass: no return, nothing changes *)
Definition hkc5_head_stmt : Prop :=
  forall (Espec: OracleKind) x25519 F V Y O (R: ret_assert),
  semax hkc5_Delta (hkc5_S x25519 F V Y O 0) hkc5_head (overridePost (hkc5_S x25519 F V Y O 0) R).

(* SLOTS: under the invariant, P's three slots are the model's: no return *)
Definition hkc5_slots_stmt : Prop :=
  forall (Espec: OracleKind) x25519 F V Y O (R: ret_assert),
  semax hkc5_Delta (hkc5_S x25519 F V Y O 0) hkc5_slots (overridePost (hkc5_S x25519 F V Y O 0) R).

(* NODE: a node and its keypair agree in every compared field; a hashed one is in the table with a unique index;
   hashed counts it *)
Definition hkc5_node_stmt : Prop :=
  forall (Espec: OracleKind) F T P m M nx K n FR (R: ret_assert),
  hk5_match (f_p F) T M K ->
  (m5_hashed M = true -> count_index T (m5_index M) = 1) ->
  semax hkc5_Delta (hkc5_PN F T P m M nx K n FR) hkc5_node
    (overridePost (hkc5_PN F T P m M nx K (n + if m5_hashed M then 1 else 0) FR) R).

(* HS: P's handshake entry, if hashed, is in the table with a unique index; hashed counts it *)
Definition hkc5_hs_stmt : Prop :=
  forall (Espec: OracleKind) F T P idx n FR (R: ret_assert),
  sfind (t_D T) (hs_addr (f_p F)) = Some (Tsh, mkEntry (f_p F) IDX_HANDSHAKE idx) ->
  (vin (hs_addr (f_p F)) (t_L T) = true -> count_index T idx = 1) ->
  semax hkc5_Delta (hkc5_PH F T P n FR) hkc5_hs
    (overridePost (hkc5_PH F T P (n + if vin (hs_addr (f_p F)) (t_L T) then 1 else 0) FR) R).

(* ONODE: one node of the others loop passes its checks; hashed counts its peer's hashed handshake entry *)
Definition hkc5_onode_stmt : Prop :=
  forall (Espec: OracleKind) F T N nx q sh Q VO n FR (R: ret_assert),
  hkc5_on_ok (f_t F) T VO N (q, sh, Q) ->
  semax hkc5_Delta (hkc5_PON F T N nx (q, sh, Q) VO n FR) hkc5_onode
    (overridePost (hkc5_PON F T N nx (q, sh, Q) VO (n + if vin (hs_addr q) (t_L T) then 1 else 0) FR) R).

(* OLOOP (from ONODE): the others loop passes; hashed counts the hashed handshake entries of the other peers *)
Definition hkc5_oloop_stmt : Prop :=
  hkc5_onode_stmt ->
  forall (Espec: OracleKind) F T hd NS PS VO n FR (R: ret_assert),
  Zlength NS = Zlength PS ->
  (forall i, 0 <= i < Zlength PS ->
     hkc5_on_ok (f_t F) T (VPeers (hkc5_rest PS i) :: VO) (Znth i NS) (Znth i PS)) ->
  semax hkc5_Delta (hkc5_PO F T hd NS PS VO n FR) hkc5_oloop
    (overridePost (hkc5_PO F T hd NS PS VO (n + hkc5_oh T PS) FR) R).

(* KFIN: the kents are as snapped (but their links): no return; t'43 / t'44 are the table's length and the
   number of hashed kents *)
Definition hkc5_kfin_stmt : Prop :=
  forall (Espec: OracleKind) F T kd KE VO n FR (R: ret_assert),
  Forall vobj_ok VO ->
  Forall (fun e => In (ke_addr e) (saddrs (t_D T)) /\ ke_snap e <> None /\
                   Forall (vp_ok (saddrs (t_D T) ++ vobjs_addrs VO)) (kent_ptrs_nn T e)) KE ->
  forallb (kent_same_bn T) KE = true ->
  semax hkc5_Delta (hkc5_PK F T kd KE VO n FR) hkc5_kfin
    (overridePost (hkc5_PK' F T kd KE VO n FR) R).

(* the pure facts *)

(* a hashed entry's index occurs once *)
Definition hkc5_count_index_stmt : Prop :=
  forall T a E, NoDup (t_indices T (t_L T)) -> In a (t_L T) -> t_entry T a = Some E ->
  count_index T (e_index E) = 1.

(* the table's length: the hashed live keypairs, P's handshake entry, the other peers' handshake entries, the
   kents' entries *)
Definition hkc5_table_len_stmt : Prop :=
  forall F V Y O, hkp5_inv F V Y -> hkp5_oth_ok F V O ->
  NoDup (map hs_addr (map peer_addr4 (o_PS O)) ++ map ke_addr (o_KE O)) ->
  Zlength (t_L (y_T Y)) =
    hkc5_nh (h5_ML (y_H Y)) + (if vin (hs_addr (f_p F)) (t_L (y_T Y)) then 1 else 0) +
    hkc5_oh (y_T Y) (o_PS O) + kents_hashed_n (y_T Y) (o_KE O).

(* the others: what ONODE (lent: the device, P, the other peers) and KFIN (lent: the peers) need *)
Definition hkc5_oth_facts_stmt : Prop :=
  forall x25519 F V Y O, hkp5_fix_ok F V -> hkp5_inv F V Y -> hkp5_oth_ok F V O ->
  Zlength (o_NS O) = Zlength (o_PS O) /\
  (forall i, 0 <= i < Zlength (o_PS O) ->
     hkc5_on_ok (f_t F) (y_T Y)
       (VPeers (hkc5_rest (o_PS O) i) :: [VDev Tsh (f_w F) (hkp5_D x25519 F V); VPeer Tsh (f_p F) (y_P Y)])
       (Znth i (o_NS O)) (Znth i (o_PS O))) /\
  Forall vobj_ok [VPeers (o_PS O)] /\
  Forall (fun e => In (ke_addr e) (saddrs (t_D (y_T Y))) /\ ke_snap e <> None /\
                   Forall (vp_ok (saddrs (t_D (y_T Y)) ++ vobjs_addrs [VPeers (o_PS O)])) (kent_ptrs_nn (y_T Y) e))
    (o_KE O) /\
  forallb (kent_same_bn (y_T Y)) (o_KE O) = true.
