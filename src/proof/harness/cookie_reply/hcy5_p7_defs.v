(* law cookie_reply, phase P7: the statement pieces, the pieces of the
   loop invariant and its states.
   - hcy5_p7_seg: the node list's done segment (from the head to the current node);
   - hcy5_p7_nP / nS / nX: the current node in 3 opaque pieces (W field p / CKS snap+refs+rest / W field next);
   - hcy5_p7_F: the SEP items the loop never touches (one opaque item: forward stays fast);
   - hcy5_p7_upd: main's effect on one peer (peer_randomize_rest: p_rest_randomized). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
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

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The statements                                                          *)
(* ---------------------------------------------------------------------- *)

Definition hcy5_p7_s0 : statement :=
  ltac:(let x := eval cbv delta [hcy5_P7] in hcy5_P7 in match x with Ssequence ?a _ => exact a end).
Definition hcy5_p7_body : statement :=
  ltac:(let x := eval cbv delta [hcy5_P7] in hcy5_P7 in match x with Ssequence _ (Sloop ?b _) => exact b end).
Definition hcy5_p7_incr : statement :=
  ltac:(let x := eval cbv delta [hcy5_P7] in hcy5_P7 in match x with Ssequence _ (Sloop _ ?i) => exact i end).
Definition hcy5_p7_brk : statement :=
  ltac:(let x := eval cbv delta [hcy5_p7_body] in hcy5_p7_body in match x with Ssequence ?a _ => exact a end).
Definition hcy5_p7_A : statement :=
  ltac:(let x := eval cbv delta [hcy5_p7_body] in hcy5_p7_body in
        match x with Ssequence _ (Ssequence ?a _) => exact a end).
Definition hcy5_p7_B : statement :=
  ltac:(let x := eval cbv delta [hcy5_p7_body] in hcy5_p7_body in
        match x with Ssequence _ (Ssequence _ (Ssequence ?b _)) => exact b end).
Definition hcy5_p7_C : statement :=
  ltac:(let x := eval cbv delta [hcy5_p7_body] in hcy5_p7_body in
        match x with Ssequence _ (Ssequence _ (Ssequence _ ?r)) => exact r end).

Lemma hcy5_p7_P7_eq : hcy5_P7 = Ssequence hcy5_p7_s0 (Sloop hcy5_p7_body hcy5_p7_incr).
Proof. reflexivity. Qed.

Lemma hcy5_p7_body_eq :
  hcy5_p7_body = Ssequence hcy5_p7_brk (Ssequence hcy5_p7_A (Ssequence hcy5_p7_B hcy5_p7_C)).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* The node list                                                           *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hcy5_p7_cce_K : change_composite_env CKS W_cookie_reply.
Proof. make_cs_preserve CKS W_cookie_reply. Defined.

(* the node's value *)
Definition hcy5_p7_nv (N: hnode4) (nx: val) : @reptype CKS t_hnode4 :=
  (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))).

(* a segment of the node list, from l to e *)
Fixpoint hcy5_p7_seg (l e: val) (NS: list hnode4) : mpred :=
  match NS with
  | [] => !! (l = e) && emp
  | N :: NS' =>
      !! (l = hn_addr N) &&
      EX nx: val,
        @malloc_token W Ews t_hnode4 l *
        @data_at CKS Ews t_hnode4 (hcy5_p7_nv N nx) l *
        @malloc_token W Ews t_peer (hn_p N) *
        hcy5_p7_seg nx e NS'
  end.

Lemma hcy5_p7_seg_app l e NS1 NS2 :
  hcy5_p7_seg l e NS1 * hnodes_rep4 W e NS2 |-- hnodes_rep4 W l (NS1 ++ NS2).
Proof.
  revert l; induction NS1 as [| N NS1 IH]; intros l; simpl.
  - Intros. subst. cancel.
  - Intros nx. Exists nx. unfold hcy5_p7_nv. entailer!. sep_apply (IH nx). cancel.
Qed.

Lemma hcy5_p7_seg_snoc l e N nx NS1 : e = hn_addr N ->
  hcy5_p7_seg l e NS1 *
  (@malloc_token W Ews t_hnode4 e *
   @data_at CKS Ews t_hnode4 (hcy5_p7_nv N nx) e *
   @malloc_token W Ews t_peer (hn_p N)) |--
  hcy5_p7_seg l nx (NS1 ++ [N]).
Proof.
  intros He. revert l; induction NS1 as [| M NS1 IH]; intros l; simpl.
  - Intros. subst. Exists nx. entailer!.
  - Intros nx'. Exists nx'. entailer!. sep_apply (IH nx'). cancel.
Qed.

Lemma hcy5_p7_pn l NS : hnodes_rep4 W l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [| N NS]; simpl.
  - Intros. subst. entailer!.
  - Intros nx. subst. entailer!.
    match goal with H: field_compatible _ [] (hn_addr N) |- _ => destruct H as [Hp _] end.
    destruct (hn_addr N); try contradiction; simpl; auto.
Qed.

Lemma hcy5_p7_vp l NS : hnodes_rep4 W l NS |-- valid_pointer l.
Proof.
  destruct NS as [| N NS]; simpl.
  - Intros. subst. apply valid_pointer_null.
  - Intros nx. subst.
    sep_apply (@data_at_valid_ptr CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N)).
    { apply readable_nonidentity, writable_readable, writable_Ews. }
    apply sepcon_valid_pointer1, derives_refl.
Qed.

Lemma hcy5_p7_peers_snoc l y : peers_rep (l ++ [y]) = (peers_rep l * peer_item_rep y)%logic.
Proof. unfold peers_rep. rewrite iter_sepcon_app. simpl. rewrite sepcon_emp. reflexivity. Qed.

(* the current node in 3 opaque pieces *)
Definition hcy5_p7_nP (N: hnode4) : mpred :=
  @field_at W Ews t_hnode4 [StructField HY._p] (hn_p N) (hn_addr N).
Definition hcy5_p7_nS (N: hnode4) : mpred :=
  @field_at CKS Ews t_hnode4 [StructField HC._snap] (hn_snap N) (hn_addr N) *
  @field_at CKS Ews t_hnode4 [StructField HC._refs] (hn_refs N) (hn_addr N) *
  spacer Ews 300 304 (hn_addr N) *
  @field_at CKS Ews t_hnode4 [StructField HC._rest] (hn_rest N) (hn_addr N).
Definition hcy5_p7_nX (N: hnode4) (nx: val) : mpred :=
  @field_at W Ews t_hnode4 [StructField HY._next] nx (hn_addr N).

Lemma hcy5_p7_fP (v: val) a :
  @field_at CKS Ews t_hnode4 [StructField HC._p] v a = @field_at W Ews t_hnode4 [StructField HY._p] v a.
Proof.
  rewrite (@field_at_change_composite CKS W_cookie_reply _ Ews t_hnode4 [StructField HC._p] v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hcy5_p7_fX (v: val) a :
  @field_at CKS Ews t_hnode4 [StructField HC._next] v a = @field_at W Ews t_hnode4 [StructField HY._next] v a.
Proof.
  rewrite (@field_at_change_composite CKS W_cookie_reply _ Ews t_hnode4 [StructField HC._next] v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hcy5_p7_node_split N nx :
  @data_at CKS Ews t_hnode4 (hcy5_p7_nv N nx) (hn_addr N) =
  hcy5_p7_nP N * hcy5_p7_nS N * hcy5_p7_nX N nx.
Proof.
  unfold hcy5_p7_nv.
  unfold_data_at (@data_at CKS _ _ _ _).
  unfold hcy5_p7_nP, hcy5_p7_nS, hcy5_p7_nX.
  rewrite <- hcy5_p7_fP, <- hcy5_p7_fX.
  apply pred_ext; cancel.
Qed.

(* ---------------------------------------------------------------------- *)
(* main's effect on one peer, the frame                                    *)
(* ---------------------------------------------------------------------- *)

(* peer_randomize_rest: the rest drawn (dead flag, last sent handshake, cookie state), the keys kept *)
Definition hcy5_p7_upd (x y: val * share * peer) : Prop :=
  match x, y with (a, sh, P), (a', sh', P') =>
    a' = a /\ sh' = sh /\
    exists dead lsh valid birth ck sent mac1, P' = p_rest_randomized P dead lsh valid birth ck sent mac1
  end.

Section F.
Variable x25519: list byte -> list byte -> list byte.

(* the SEP items of S6 the loop never touches *)
Definition hcy5_p7_Fl (gv: globals) (L: hcy5_loc) (FR: mpred) (R: hcy5_run) (Q: hcy5_pkt) (m c rp: val)
  (rr CK: list byte) (CM: cookie_msg) (NS: list hnode4) (PS: list (val * share * peer)) : list mpred :=
  [device_rep Tsh (l_wa L) (hcy5_DA x25519 R L); ptable Tsh (l_pta L) (hcy5_phead PS);
   @data_at W Tsh (tptr t_hnode4) (hcy5_head NS) (l_peers L)] ++
  hcy5_bside x25519 R L (hcy5_CC2 x25519 R L Q rr) ++
  hcy5_bufs x25519 R L ++ hcy5_pbufs L Q m c rp ++
  [cmsg_rep Ews rp CM; hbytes Tsh CK (l_cookie L); hout Tsh 64 (l_img L)] ++
  hcy5_scrB L ++ hcy5_snaps0 L ++
  [noise_globals gv Int64.zero; wg_consts gv; hcy5_consts gv; FR].

Definition hcy5_p7_F (gv: globals) (L: hcy5_loc) (FR: mpred) (R: hcy5_run) (Q: hcy5_pkt) (m c rp: val)
  (rr CK: list byte) (CM: cookie_msg) (NS: list hnode4) (PS: list (val * share * peer)) : mpred :=
  fold_right_sepcon (hcy5_p7_Fl gv L FR R Q m c rp rr CK CM NS PS).

End F.

(* ---------------------------------------------------------------------- *)
(* The states                                                              *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.
Variables (gv: globals) (L: hcy5_loc) (FR: mpred) (R: hcy5_run) (Q: hcy5_pkt) (m c rp: val)
  (rr CK: list byte) (CM: cookie_msg) (np: val).

(* the locals of the loop: it, cns, and S6's *)
Definition hcy5_p7_lc (it cns: val) : list localdef :=
  [temp HY._it it; temp HY._cns cns;
   temp HY._len (Vlong (Int64.repr (q_n Q))); temp HY._msg m; temp HY._copy c;
   temp HY._reply rp; temp HY._np np] ++ hcy5_lvars gv L.

Definition hcy5_p7_Inv (NS: list hnode4) (PS: list (val * share * peer)) : environ -> mpred :=
  EX NS1: list hnode4, EX NS2: list hnode4, EX PS1: list (val * share * peer),
  EX PS1': list (val * share * peer), EX PS2: list (val * share * peer), EX T': tstate, EX S': shim,
  EX CL: list (val * val * option cookie), EX it: val,
  PROPx [NS = NS1 ++ NS2; PS = PS1 ++ PS2; Forall2 hcy5_p7_upd PS1 PS1'; hnodes_peers4 NS2 PS2;
         hcy5_T_ok PS [] T'; hcy5_cl_nodes CL NS1; hcy5_cl_none CL]
  (LOCALx (hcy5_p7_lc it (hcy5_chead CL))
  (SEPx [hcy5_p7_F x25519 gv L FR R Q m c rp rr CK CM NS PS; itable Tsh (l_ita L) T';
         hcy5_p7_seg (hcy5_head NS) it NS1; hnodes_rep4 W it NS2; peers_rep PS1'; peers_rep PS2;
         hcy5_cns (hcy5_chead CL) CL; mem_mgr gv; shim_state4 gv S' hcy5_w0])).

Definition hcy5_p7_Cont (NS: list hnode4) (PS: list (val * share * peer)) : environ -> mpred :=
  EX NS1: list hnode4, EX N: hnode4, EX NS2: list hnode4, EX PS1: list (val * share * peer),
  EX PS1': list (val * share * peer), EX x: val * share * peer, EX y: val * share * peer,
  EX PS2: list (val * share * peer), EX T': tstate, EX S': shim,
  EX CL: list (val * val * option cookie), EX nx: val,
  PROPx [NS = NS1 ++ N :: NS2; PS = PS1 ++ x :: PS2; Forall2 hcy5_p7_upd PS1 PS1'; hcy5_p7_upd x y;
         hnodes_peers4 NS2 PS2; hn_p N = peer_addr4 x;
         hcy5_T_ok PS [] T'; hcy5_cl_nodes CL (NS1 ++ [N]); hcy5_cl_none CL]
  (LOCALx (hcy5_p7_lc (hn_addr N) (hcy5_chead CL))
  (SEPx [hcy5_p7_F x25519 gv L FR R Q m c rp rr CK CM NS PS; itable Tsh (l_ita L) T';
         hcy5_p7_seg (hcy5_head NS) (hn_addr N) NS1;
         @malloc_token W Ews t_hnode4 (hn_addr N);
         hcy5_p7_nP N; hcy5_p7_nS N; hcy5_p7_nX N nx;
         @malloc_token W Ews t_peer (hn_p N);
         hnodes_rep4 W nx NS2; peers_rep PS1'; peer_item_rep y; peers_rep PS2;
         hcy5_cns (hcy5_chead CL) CL; mem_mgr gv; shim_state4 gv S' hcy5_w0])).

(* after brk: the node N, its peer P (open) as P' (ck = false: P' = P; true: drawn by peer_randomize_rest) *)
Definition hcy5_p7_K (NS: list hnode4) (PS: list (val * share * peer)) (ck: bool) : environ -> mpred :=
  EX NS1: list hnode4, EX N: hnode4, EX NS2: list hnode4, EX PS1: list (val * share * peer),
  EX PS1': list (val * share * peer), EX P: peer, EX P': peer, EX PS2: list (val * share * peer),
  EX T': tstate, EX S': shim, EX CL: list (val * val * option cookie), EX nx: val,
  PROPx [NS = NS1 ++ N :: NS2; PS = PS1 ++ (hn_p N, Ews, P) :: PS2; Forall2 hcy5_p7_upd PS1 PS1';
         hnodes_peers4 NS2 PS2; hcy5_T_ok PS [] T'; hcy5_cl_nodes CL NS1; hcy5_cl_none CL;
         if ck then hcy5_p7_upd (hn_p N, Ews, P) (hn_p N, Ews, P') else P' = P]
  (LOCALx (hcy5_p7_lc (hn_addr N) (hcy5_chead CL))
  (SEPx [peer_rep Ews (hn_p N) P';
         hcy5_p7_F x25519 gv L FR R Q m c rp rr CK CM NS PS; itable Tsh (l_ita L) T';
         hcy5_p7_seg (hcy5_head NS) (hn_addr N) NS1;
         @malloc_token W Ews t_hnode4 (hn_addr N);
         hcy5_p7_nP N; hcy5_p7_nS N; hcy5_p7_nX N nx;
         @malloc_token W Ews t_peer (hn_p N);
         hnodes_rep4 W nx NS2; peers_rep PS1'; peers_rep PS2;
         hcy5_cns (hcy5_chead CL) CL; mem_mgr gv; shim_state4 gv S' hcy5_w0])).

End States.

(* main's return (after hcy5_post_canon) and the loop's exit *)
Definition hcy5_p7_Rf : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (PROP () LOCAL () SEP (TT))) (@stackframe_of W HY.f_main).
