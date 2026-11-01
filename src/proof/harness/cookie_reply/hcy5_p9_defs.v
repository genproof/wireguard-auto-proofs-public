(* law cookie_reply, phase P9: the cut of the phase into segments and the states between them.
   Port of v1's hcy4_p9_defs.v.

   P9 = s53 (mode = nondet_u8() % 3); s54 (honest = 0); s55 (the mode block); s56 (cookie_img(img, reply)).
   s55 = (t'44 = mode != 2 && np != NULL); if (t'44) BA else if (mode == 2) BB else skip, with
     BA = BA1 (h = &np->p->handshake; if (!h->entry.hashed) insert(&ita, &h->entry))
          BA2a (reply->receiver_index = h->entry.index)
          BA2b (np->p->latest_cookie.have_sent_mac1 = true; bytes_copy(np->p->latest_cookie.last_mac1_sent,
                msg + len - 32, 16))
          BA3 (honest = mode == 0; if (mode == 1) flip one byte of the reply)
     BB = fill_cookie_msg(reply); if (ita.head != NULL && (nondet_u8() & 1)) { kk = nondet_size(); walk ita's
          list kk steps (at most to its last entry); reply->receiver_index = e->index }.
   The segment lemmas are stated over FIXED values (the EX of hcy5_S8 already opened), with the facts of S8
   (hcy5_p9_inv) as Coq hypotheses, and posts as normal_ret_assert (chained with hcy5_p9_seq).
   All states share S8's SEP layout (hcy5_p9_sep, img's item a parameter) and S8's locals (hcy5_p9_loc, extra
   temps in front).  v2: the kents KE (kents_rep W (hcy5_khead KE) KE) instead of v1's kentries KS; their
   entries are pool items of A's table (hcy5_T_ok PS KE T). *)
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

Definition hcy5_p9_s53 := ltac:(let x := eval cbv beta iota delta [hcy5_stmts nth] in (nth 53 hcy5_stmts Sskip) in exact x).
Definition hcy5_p9_s54 := ltac:(let x := eval cbv beta iota delta [hcy5_stmts nth] in (nth 54 hcy5_stmts Sskip) in exact x).
Definition hcy5_p9_s55 := ltac:(let x := eval cbv beta iota delta [hcy5_stmts nth] in (nth 55 hcy5_stmts Sskip) in exact x).
Definition hcy5_p9_s56 := ltac:(let x := eval cbv beta iota delta [hcy5_stmts nth] in (nth 56 hcy5_stmts Sskip) in exact x).

Lemma hcy5_p9_P9_eq : hcy5_P9 = Ssequence hcy5_p9_s53 (Ssequence hcy5_p9_s54 (Ssequence hcy5_p9_s55 hcy5_p9_s56)).
Proof. reflexivity. Qed.

(* s55 = Ssequence (t'44 = ..) (Sifthenelse t'44 BA (Sifthenelse (mode == 2) BB Sskip)) *)
Definition hcy5_p9_tc := ltac:(let x := eval cbv delta [hcy5_p9_s55] in hcy5_p9_s55 in
  match x with Ssequence ?a _ => exact a end).
Definition hcy5_p9_BA := ltac:(let x := eval cbv delta [hcy5_p9_s55] in hcy5_p9_s55 in
  match x with Ssequence _ (Sifthenelse _ ?a _) => exact a end).
Definition hcy5_p9_BB := ltac:(let x := eval cbv delta [hcy5_p9_s55] in hcy5_p9_s55 in
  match x with Ssequence _ (Sifthenelse _ _ (Sifthenelse _ ?b _)) => exact b end).
Definition hcy5_p9_cc := ltac:(let x := eval cbv delta [hcy5_p9_s55] in hcy5_p9_s55 in
  match x with Ssequence _ (Sifthenelse ?c _ _) => exact c end).
Definition hcy5_p9_c2 := ltac:(let x := eval cbv delta [hcy5_p9_s55] in hcy5_p9_s55 in
  match x with Ssequence _ (Sifthenelse _ _ (Sifthenelse ?c _ _)) => exact c end).

Lemma hcy5_p9_s55_eq :
  hcy5_p9_s55 = Ssequence hcy5_p9_tc (Sifthenelse hcy5_p9_cc hcy5_p9_BA (Sifthenelse hcy5_p9_c2 hcy5_p9_BB Sskip)).
Proof. reflexivity. Qed.

(* BA = BA1; BA2a; BA2b; BA3 *)
Definition hcy5_p9_BA1 := ltac:(let x := eval cbv delta [hcy5_p9_BA] in hcy5_p9_BA in
  match x with Ssequence ?h (Ssequence ?i _) => exact (Ssequence h i) end).
Definition hcy5_p9_BA2a := ltac:(let x := eval cbv delta [hcy5_p9_BA] in hcy5_p9_BA in
  match x with Ssequence _ (Ssequence _ (Ssequence ?a _)) => exact a end).
Definition hcy5_p9_BA2b := ltac:(let x := eval cbv delta [hcy5_p9_BA] in hcy5_p9_BA in
  match x with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence ?a (Ssequence ?b _)))) => exact (Ssequence a b) end).
Definition hcy5_p9_BA3 := ltac:(let x := eval cbv delta [hcy5_p9_BA] in hcy5_p9_BA in
  match x with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ ?r)))) => exact r end).

Lemma hcy5_p9_BA_eq :
  unfold_Ssequence hcy5_p9_BA =
  unfold_Ssequence (Ssequence hcy5_p9_BA1 (Ssequence hcy5_p9_BA2a (Ssequence hcy5_p9_BA2b hcy5_p9_BA3))).
Proof. reflexivity. Qed.

(* a statement followed by the rest, its post a normal_ret_assert *)
Lemma hcy5_p9_seq {Espec: OracleKind} {cs: compspecs} Delta P Q R c1 c2 :
  semax Delta P c1 (normal_ret_assert Q) -> semax Delta Q c2 R -> semax Delta P (Ssequence c1 c2) R.
Proof.
  intros H1 H2. apply semax_seq with Q; auto.
  destruct R as [Rn Rb Rc Rr].
  eapply semax_post; [| | | | exact H1]; simpl; intros; try (apply andp_left2; apply derives_refl);
    apply andp_left2; apply FF_left.
Qed.

(* the BA chain: the sequence BA as the four segments *)
Lemma hcy5_p9_BA_split {Espec: OracleKind} {cs: compspecs} Delta P R :
  semax Delta P (Ssequence hcy5_p9_BA1 (Ssequence hcy5_p9_BA2a (Ssequence hcy5_p9_BA2b hcy5_p9_BA3))) R ->
  semax Delta P hcy5_p9_BA R.
Proof.
  intros H. apply (semax_unfold_Ssequence _ _ (eq_sym hcy5_p9_BA_eq)). exact H.
Qed.

(* ---------------------------------------------------------------------- *)
(* The states                                                              *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.

(* the facts of hcy5_S8 (the peers PS, the table T, the kents KE) *)
Definition hcy5_p9_inv (R: hcy5_run) (L: hcy5_loc) (Q: hcy5_pkt) (m: val) (nonce rr CK: list byte)
  (CM: cookie_msg) (NS: list hnode4) (PS: list (val * share * peer)) (T: tstate) (np: val)
  (CL: list (val * val * option cookie)) (KE: list kent4) : Prop :=
  hcy5_reply_ok x25519 xaead_enc R L Q m nonce rr CK CM /\ hcy5_lists_ok L (map ke_addr KE) NS PS /\
  hcy5_np_ok (hcy5_pubB x25519 R L) NS PS np /\ hcy5_T_ok PS KE T /\
  hcy5_cl_nodes CL NS /\ hcy5_cl_none CL.

(* S8's SEP with A's table T, the peers PS, the reply CM' (cmsg_rep), the shim S, img's item *)
Definition hcy5_p9_sep (gv: globals) (L: hcy5_loc) (FR: mpred) (R: hcy5_run) (S: shim) (m c rp: val)
  (Q: hcy5_pkt) (rr CK: list byte) (NS: list hnode4) (PS: list (val * share * peer)) (T: tstate)
  (CL: list (val * val * option cookie)) (KE: list kent4) (CM': cookie_msg) (img: mpred) : list mpred :=
  hcy5_aside x25519 R L T NS PS ++ hcy5_bside x25519 R L (hcy5_CC2 x25519 R L Q rr) ++
  hcy5_bufs x25519 R L ++ hcy5_pbufs L Q m c rp ++
  [cmsg_rep Ews rp CM'; hbytes Tsh CK (l_cookie L); img;
   hcy5_cns (hcy5_chead CL) CL; kents_rep W (hcy5_khead KE) KE] ++
  hcy5_scrB L ++ hcy5_snaps0 L ++ hcy5_globs gv S FR.

(* S8's locals, extra temps tl in front *)
Definition hcy5_p9_loc (gv: globals) (L: hcy5_loc) (m c rp: val) (Q: hcy5_pkt) (np: val)
  (CL: list (val * val * option cookie)) (KE: list kent4) (tl: list localdef) : list localdef :=
  tl ++ [temp HY._kes (hcy5_khead KE); temp HY._cns (hcy5_chead CL);
         temp HY._len (Vlong (Int64.repr (q_n Q)));
         temp HY._msg m; temp HY._copy c; temp HY._reply rp; temp HY._np np] ++ hcy5_lvars gv L.

(* the states inside s55: mode = md, honest = 0, img not written yet; props pr, extra temps tl *)
Definition hcy5_p9_PA (gv: globals) (L: hcy5_loc) (FR: mpred) (R: hcy5_run) (S: shim) (m c rp: val)
  (Q: hcy5_pkt) (rr CK: list byte) (NS: list hnode4) (PS: list (val * share * peer)) (T: tstate) (np: val)
  (CL: list (val * val * option cookie)) (KE: list kent4) (CM': cookie_msg) (md: Z)
  (pr: list Prop) (tl: list localdef) : environ -> mpred :=
  PROPx pr
  (LOCALx (hcy5_p9_loc gv L m c rp Q np CL KE
             (tl ++ [temp HY._mode (Vint (Int.repr md)); temp HY._honest (Vint Int.zero)]))
  (SEPx (hcy5_p9_sep gv L FR R S m c rp Q rr CK NS PS T CL KE CM' (hout Tsh 64 (l_img L))))).

(* after s55 (before cookie_img): the reply A consumes CM', honest; PS / T / S as left by the branch *)
Definition hcy5_p9_Q1 (gv: globals) (L: hcy5_loc) (FR: mpred) (R: hcy5_run) (m c rp: val) (Q: hcy5_pkt)
  (nonce rr CK: list byte) (CM: cookie_msg) (NS: list hnode4) (np: val)
  (CL: list (val * val * option cookie)) (KE: list kent4) : environ -> mpred :=
  EX S: shim, EX PS: list (val * share * peer), EX T: tstate, EX CM': cookie_msg, EX honest: bool,
  PROPx [hcy5_p9_inv R L Q m nonce rr CK CM NS PS T np CL KE; cm_ok CM';
         honest = true -> hcy5_honest_ok (hcy5_pubB x25519 R L) Q CM CM' NS PS T np]
  (LOCALx (hcy5_p9_loc gv L m c rp Q np CL KE [temp HY._honest (Vint (if honest then Int.one else Int.zero))])
  (SEPx (hcy5_p9_sep gv L FR R S m c rp Q rr CK NS PS T CL KE CM' (hout Tsh 64 (l_img L))))).

End States.

(* ---------------------------------------------------------------------- *)
(* The model of branch BA                                                  *)
(* ---------------------------------------------------------------------- *)

(* the reply with the receiver index idx *)
Definition hcy5_p9_rcv (M: cookie_msg) (idx: int) : cookie_msg :=
  mkCM (cm_type M) idx (cm_nonce M) (cm_enc M).

(* P's cookie after BA2b: mac1 sent, the packet's mac1 remembered *)
Definition hcy5_p9_ck (C: cookie) (m1: list byte) : cookie :=
  mkCookie (ck_birth C) (ck_valid C) (ck_cookie C) true m1 (ck_dkey C) (ck_mkey C).
Definition hcy5_p9_peer (P: peer) (Q: hcy5_pkt) : peer :=
  p_set_cookie P (hcy5_p9_ck (p_cookie P) (hcy5_mac1 Q)).
(* the peers after BA2b (P at address a updated) *)
Definition hcy5_p9_PS (PS: list (val * share * peer)) (a: val) (P: peer) (Q: hcy5_pkt) : list (val * share * peer) :=
  supd PS a (hcy5_p9_peer P Q).
