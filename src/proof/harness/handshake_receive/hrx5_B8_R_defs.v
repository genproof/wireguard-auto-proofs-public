(* law handshake_receive: phase B8, branch R.  The cut of hrx5_B8_R into segments, the states between them and the pure
   statements the segments share.

   hrx5_B8_R = 12 statements (hrx5_B8R_l):
     0  h = &target->p->handshake         1  s = &target->snap
     2  alloc_ok = (failures == ss.alloc_failures)
     3  session = alloc_ok && !target->rest.is_dead
     4  hashed = 0
     5  CHECK(rx_authenticated(target->p, &skb, 0, session))
     6  CHECK(target->p->refcount == target->refs && shim_no_warning(&ss))
     7  if (!alloc_ok) { the failure CHECKs } else { CHECK(hs_zeroed_from ..);
          if (session) { the keypair CHECKs; wg_noise_keypairs_clear(&target->p->keypairs); CHECK(frees) }
          else { CHECK(h->entry.hashed && index && frees) } }
     8  CHECK(pr_same(&target->rest, target->p))
     9  nd = peers; for (; nd; nd = nd->next) { if (nd == target) continue; CHECKs; if (snap.hashed) {..; hashed++} }
     10 if (h->entry.hashed) { CHECK(table_has(&itd, &h->entry)); hashed++; }
     11 CHECK(kents_same_but_next(kes, &itd) && table_len(&itd) == hashed + kents_hashed(kes))
   Segments: A = 0..6 (hrx5_B8R_A), B = 7 (hrx5_B8R_B), D = 8..9 (hrx5_B8R_D), E = 10..11 (hrx5_B8R_E).

   States (all variables of hrx5_B8_Q fixed, plus the accepted peer: address a, state P before the call, the
   message M, the model's ck / h, its index j in PS):
     hrx5_B8R_St .. Wx tl pl = hrx5_B8_Q with the world W1 replaced by Wx, the temps tl added in front of Q's,
       the PROPs pl after Q's.
     R0 = St W1 [] F (F = hrx5_B8R_facts: the case analysis, W1 = rx_resp_accepted ..)
     RA = St W1 (hrx5_B8R_tl .. 0) F                                  (after A)
     RB = St (hrx5_B8R_Wx ..) (hrx5_B8R_tl .. 0) F                    (after B: the final world, explicit)
     RD = St (hrx5_B8R_Wx ..) (hrx5_B8R_tl .. (hrx5_B8R_nh T a PS)) F  (after D: the other peers' hashed count)
     post of E = overridePost (hrx5_S8 ..) (hrx5_RB ..).
   Pure statements: hrx5_B8R_P_stmt (Q's PROPs and hrx5_B8_isR give the facts), hrx5_B8R_I_stmt (the new world
   satisfies the invariant: the PROPs of hrx5_S8). *)
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
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* the statements                                                          *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_B8R_l : list statement :=
  ltac:(let x := eval cbv beta iota delta [hrx5_flat hrx5_B8_R] in (hrx5_flat hrx5_B8_R) in exact x).

Lemma hrx5_B8R_l_length : length hrx5_B8R_l = 12%nat.
Proof. reflexivity. Qed.

Lemma hrx5_B8R_l_eq : hrx5_B8_R = hrx5_seql hrx5_B8R_l.
Proof. reflexivity. Qed.

Definition hrx5_B8R_A := ltac:(let x := eval cbv beta iota delta [hrx5_seql firstn skipn hrx5_B8R_l] in
  (hrx5_seql (firstn 7 hrx5_B8R_l)) in exact x).
Definition hrx5_B8R_B := ltac:(let x := eval cbv beta iota delta [hrx5_seql firstn skipn hrx5_B8R_l] in
  (hrx5_seql (firstn 1 (skipn 7 hrx5_B8R_l))) in exact x).
Definition hrx5_B8R_D := ltac:(let x := eval cbv beta iota delta [hrx5_seql firstn skipn hrx5_B8R_l] in
  (hrx5_seql (firstn 2 (skipn 8 hrx5_B8R_l))) in exact x).
Definition hrx5_B8R_E := ltac:(let x := eval cbv beta iota delta [hrx5_seql firstn skipn hrx5_B8R_l] in
  (hrx5_seql (skipn 10 hrx5_B8R_l)) in exact x).

(* ---------------------------------------------------------------------- *)
(* the model of the branch                                                 *)
(* ---------------------------------------------------------------------- *)

(* D's verdict / rotation (rx_packet's vm, D1, S1, lul): the device before (D), the shim before (S) *)
Definition hrx5_B8R_vm (D: device) (S: shim) (q: int) (lul: int64) (s: skb) (msg: list byte) (d: rxdraw)
  : Z * checker :=
  validate_model (d_cc D) s msg (fst (load_model q lul (s_boot S))) (s_boot S) (s_rlallow S) (rd_r d).
Definition hrx5_B8R_D1 (D: device) (S: shim) (q: int) (lul: int64) (s: skb) (msg: list byte) (d: rxdraw)
  : device :=
  dev_set_cc D (snd (hrx5_B8R_vm D S q lul s msg d)).
Definition hrx5_B8R_S1 (D: device) (S: shim) (q: int) (lul: int64) (msg: list byte) (d: rxdraw) : shim :=
  if validate_rotates (d_cc D) msg (fst (load_model q lul (s_boot S))) (s_boot S) then shim_draw S (rd_r d)
  else S.
Definition hrx5_B8R_lul1 (S: shim) (q: int) (lul: int64) : int64 := snd (load_model q lul (s_boot S)).

(* begin_session's allocation succeeded (the keypair kzalloc returned); a session was made *)
Definition hrx5_B8R_alloc (d: rxdraw) : bool := if eq_dec (rd_k d) nullval then false else true.
Definition hrx5_B8R_sess (d: rxdraw) (P: peer) : bool := hrx5_B8R_alloc d && negb (p_dead P).

(* the accepted peer at the end (P = its state before the call): consume_response's state, begin_session's
   zeroing unless the allocation failed, its reference count back; slots as before (NULL) *)
Definition hrx5_B8R_Pf (d: rxdraw) (P: peer) (M: resp_msg) (ck h: list byte) : peer :=
  let Pn := hrx5cr_new P M ck h in
  if hrx5_B8R_alloc d then p_set_refs (p_set_hs Pn (hs_zero (p_hs Pn))) (p_refs P)
  else p_set_refs Pn (p_refs P).

(* the table at the end: the handshake's entry left it after a session (its keypair came and went) *)
Definition hrx5_B8R_Tf (d: rxdraw) (P: peer) (T: tstate) (a: val) : tstate :=
  if hrx5_B8R_sess d P then t_remove T (hs_addr a) else T.

(* the shim at the end: the keypair freed by wg_noise_keypairs_clear after a session *)
Definition hrx5_B8R_Sf (d: rxdraw) (P: peer) (W1: rxw) : shim :=
  if hrx5_B8R_sess d P then shim_free (rw_S W1) else rw_S W1.

(* the world at the end of statement 7 (after the harness's wg_noise_keypairs_clear in a session) *)
Definition hrx5_B8R_Wx (W1: rxw) (d: rxdraw) (T: tstate) (PS: list (val * share * peer)) (a: val) (P: peer)
  (M: resp_msg) (ck h: list byte) : rxw :=
  mkRW (rw_D W1) (hrx5_B8R_Tf d P T a) (supd PS a (hrx5_B8R_Pf d P M ck h)) [] (hrx5_B8R_Sf d P W1) (rw_w W1)
       (rw_kc W1) (rw_lul W1) (rw_rx W1).

(* the other peers' handshake entries in the table (counted by the node loop: their snapshots, taken in T) *)
Definition hrx5_B8R_nh (T: tstate) (a: val) (PS: list (val * share * peer)) : Z :=
  Zlength (filter (fun x => andb (negb (veqb (peer_addr4 x) a)) (vin (hs_addr (peer_addr4 x)) (t_L T))) PS).

(* a default peer entry (Znth on PS) *)
Definition hrx5_B8R_hs0 : handshake :=
  mkHS Int.zero Int64.zero nullval [] [] [] [] [] [] [] [] Int.zero.
Definition hrx5_B8R_ck0 : cookie := mkCookie Int64.zero false [] false [] [] [].
#[export] Instance hrx5_B8R_pinh : Inhabitant (val * share * peer) :=
  (nullval, Ews, mkPeer nullval false nullval nullval nullval hrx5_B8R_hs0 Int64.zero hrx5_B8R_ck0 Int.zero
                        Int64.zero nullval).

(* ---------------------------------------------------------------------- *)
(* the states                                                              *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* the world after dispatch (as in hrx5_B8_Q) *)
Definition hrx5_B8R_W1 (L: hrx5_loc) (R: hrx5_run) (sec: list byte) (birth: int64) (S: shim) (w: list int64)
  (PS: list (val * share * peer)) (T: tstate) (kc lul: int64) (q: int) (proto: Z) (ip4 ip6 port: list byte)
  (o: hrx5_obj) (dp: val) (d: rxdraw) : rxw :=
  rx_model x25519 aead_dec xaead_enc xaead_dec (hrx5_W0 (hrx5_DL x25519 R L sec birth) T PS S w kc lul) q (l_skb L)
    (hrx5_skb dp o proto ip4 ip6 port) (obj_bytes o) d.

(* the facts of the branch (hrx5_B8R_P_stmt): the response M accepted by the harness's model for the peer a
   (index j of PS, state P before the call), the target its node, the world after dispatch: consume_response
   accepted it, then begin_session with the keypair rd_k d *)
Definition hrx5_B8R_facts (L: hrx5_loc) (R: hrx5_run) (sec: list byte) (birth: int64) (S: shim) (w: list int64)
  (NS: list hnode4) (PS: list (val * share * peer)) (T: tstate) (kc lul: int64) (q: int) (proto: Z)
  (ip4 ip6 port: list byte) (o: hrx5_obj) (dp tg: val) (ai ar: Z) (d: rxdraw)
  (a: val) (P: peer) (M: resp_msg) (ck h: list byte) (j: Z) : list Prop :=
  let D := hrx5_DL x25519 R L sec birth in
  let s := hrx5_skb dp o proto ip4 ip6 port in
  let msg := obj_bytes o in
  [o = OResp M; hrx5_fwd msg = true; ai = 0; ar = 1;
   hrx5cr_tgt x25519 aead_dec (hrx5_ID x25519 R) T PS M = Some (a, P, ck, h);
   0 <= j < Zlength PS; Znth j PS = (a, Ews, P); hn_p (Znth j NS) = a; tg = hn_addr (Znth j NS);
   hrx5_B8R_W1 L R sec birth S w PS T kc lul q proto ip4 ip6 port o dp d =
     rx_resp_accepted (hrx5_W0 D T PS S w kc lul) (hrx5_B8R_D1 D S q lul s msg d) (hrx5_B8R_S1 D S q lul msg d)
       (hrx5_B8R_lul1 S q lul) a (hrx5cr_new P M ck h) (rd_k d) (l_skb L) (sk_len s)].

(* the temps the branch sets: h, s, alloc_ok, session, hashed *)
Definition hrx5_B8R_tl (tg a: val) (d: rxdraw) (P: peer) (nh: Z) : list localdef :=
  [temp HM._h__2 (hs_addr a); temp HM._s__1 (offset_val 8 tg);
   temp HM._alloc_ok (Vint (if hrx5_B8R_alloc d then Int.one else Int.zero));
   temp HM._session (Vint (if hrx5_B8R_sess d P then Int.one else Int.zero));
   temp HM._hashed (Vlong (Int64.repr nh))].

(* hrx5_B8_Q with the world Wx, the temps tl in front, the PROPs pl after Q's *)
Definition hrx5_B8R_St (gv: globals) (L: hrx5_loc) (FR: mpred)
  (R: hrx5_run) (sec: list byte) (birth: int64) (S: shim) (w: list int64) (NS: list hnode4)
  (PS: list (val * share * peer)) (T: tstate) (head nk: val) (KE: list kent4) (st i: Z) (kc lul: int64) (q: int)
  (proto: Z) (ip4 ip6 port: list byte) (o: hrx5_obj) (dp img tg: val) (ai ar: Z) (d: rxdraw)
  (Wx: rxw) (tl: list localdef) (pl: list Prop) : environ -> mpred :=
  let W0 := hrx5_W0 (hrx5_DL x25519 R L sec birth) T PS S w kc lul in
  let s := hrx5_skb dp o proto ip4 ip6 port in
  let W1 := rx_model x25519 aead_dec xaead_enc xaead_dec W0 q (l_skb L) s (obj_bytes o) d in
  PROPx ([hrx5_base_ok R sec birth S; hrx5_inv x25519 R L NS PS KE T head nk; 0 <= st <= Int64.max_unsigned;
          0 <= i < st; obj_ok o; malloc_compatible (Zlength (obj_bytes o)) dp;
          hrx5_acc_ok x25519 aead_dec xaead_dec R NS PS T o (s_boot S) tg ai ar; rxdraw_ok T d] ++ pl)
  (LOCALx (tl ++ [temp HM._nk nk; temp HM._kes (hrx5_khead KE); temp HM._steps (Vlong (Int64.repr st));
            temp HM._i (Vlong (Int64.repr i)); temp HM._now (Vlong (s_boot S));
            temp HM._m_lul (Vlong (rw_lul W1))] ++ hrx5_ptrs dp o ++
           [temp HM._img img; temp HM._len (Vlong (Int64.repr (Zlength (obj_bytes o))));
            temp HM._kind (Vint (Int.repr (obj_kind o)));
            temp HM._acc_init (Vint (Int.repr ai)); temp HM._acc_resp (Vint (Int.repr ar)); temp HM._target tg;
            temp HM._head0 (hd nullval (t_L T));
            temp HM._path (Vint (Int.repr (hrx5_path W0 q s (obj_bytes o) d)))] ++
           hrx5_lvars gv L)
  (SEPx ([rxw_rep W gv Tsh (l_wd L) head Wx] ++
         hrx5_rest x25519 R L (hnodes_snapped4 T NS PS) (map (kent_snapped T) KE) ++
         hrx5_cglobs gv FR ++
         [qlen_rep gv q; skb_rep Tsh (l_skb L) s; obj_rep dp o; img_rep img (obj_bytes o)] ++
         hrx5_scr5 x25519 aead_dec xaead_dec R L T PS o (s_boot S) (devsnap_val (rw_D W1) head) S w s
           (hout Tsh 32 (l_secret L))))).

End States.

(* ---------------------------------------------------------------------- *)
(* the pure statements                                                     *)
(* ---------------------------------------------------------------------- *)

(* P: on branch R the facts hold for some a P M ck h j *)
Definition hrx5_B8R_P_stmt : Prop :=
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (L: hrx5_loc)
    R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp tg ai ar d,
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hrx5_base_ok R sec birth S -> hrx5_inv x25519 R L NS PS KE T head nk -> 0 <= st <= Int64.max_unsigned ->
  0 <= i < st -> obj_ok o -> malloc_compatible (Zlength (obj_bytes o)) dp ->
  hrx5_acc_ok x25519 aead_dec xaead_dec R NS PS T o (s_boot S) tg ai ar -> rxdraw_ok T d ->
  hrx5_B8_isR o (hrx5_B8_path x25519 L R sec birth S w PS T kc lul q proto ip4 ip6 port o dp d) ai ar tg ->
  exists a P M ck h j,
    fold_right and True
      (hrx5_B8R_facts x25519 aead_dec xaead_enc xaead_dec L R sec birth S w NS PS T kc lul q proto ip4 ip6 port o dp
         tg ai ar d a P M ck h j).

(* I: the new world satisfies the invariant (the PROPs of hrx5_S8): the device is D with the checker rotated
   (a new secret and birthdate), the boot clock unchanged, the nodes and kents with the snapshots taken in T *)
Definition hrx5_B8R_I_stmt : Prop :=
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (L: hrx5_loc)
    R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp tg ai ar d a P M ck h j,
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hrx5_base_ok R sec birth S -> hrx5_inv x25519 R L NS PS KE T head nk -> 0 <= st <= Int64.max_unsigned ->
  0 <= i < st -> obj_ok o -> malloc_compatible (Zlength (obj_bytes o)) dp ->
  hrx5_acc_ok x25519 aead_dec xaead_dec R NS PS T o (s_boot S) tg ai ar -> rxdraw_ok T d ->
  fold_right and True
    (hrx5_B8R_facts x25519 aead_dec xaead_enc xaead_dec L R sec birth S w NS PS T kc lul q proto ip4 ip6 port o dp
       tg ai ar d a P M ck h j) ->
  let W1 := hrx5_B8R_W1 x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6 port o dp d in
  exists sec1 birth1,
    rw_D W1 = hrx5_DL x25519 R L sec1 birth1 /\
    hrx5_base_ok R sec1 birth1 (hrx5_B8R_Sf d P W1) /\
    s_boot (hrx5_B8R_Sf d P W1) = s_boot S /\
    hrx5_inv x25519 R L (hnodes_snapped4 T NS PS) (supd PS a (hrx5_B8R_Pf d P M ck h)) (map (kent_snapped T) KE)
      (hrx5_B8R_Tf d P T a) head nk.

(* ---------------------------------------------------------------------- *)
(* the segment statements                                                  *)
(* ---------------------------------------------------------------------- *)

(* the common binders of the segments: hrx5_B8_branch's and the accepted peer's *)
Definition hrx5_B8R_seg
  (pre post: forall (x25519: list byte -> list byte -> list byte)
     (aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte))
     (xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte)
     (xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte))
     (gv: globals) (L: hrx5_loc) (FR: mpred)
     (R: hrx5_run) (sec: list byte) (birth: int64) (S: shim) (w: list int64) (NS: list hnode4)
     (PS: list (val * share * peer)) (T: tstate) (head nk: val) (KE: list kent4) (st i: Z) (kc lul: int64) (q: int)
     (proto: Z) (ip4 ip6 port: list byte) (o: hrx5_obj) (dp img tg: val) (ai ar: Z) (d: rxdraw)
     (a: val) (P: peer) (M: resp_msg) (ck h: list byte) (j: Z), environ -> mpred)
  (c: statement) (final: bool) : Prop :=
  forall (Espec: OracleKind) x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR
    R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j,
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  @semax W Espec (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (pre x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6
       port o dp img tg ai ar d a P M ck h j)
    c
    (overridePost
       (if final then hrx5_S8 x25519 gv L FR
        else post x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto
               ip4 ip6 port o dp img tg ai ar d a P M ck h j)
       (hrx5_RB x25519 gv L FR)).

(* the same with the table before the packet well-formed (itable_wf T: NoDup (t_L T) ..), a hypothesis of
   hrx5_B8_R2_stmt: segment B's session sub-branch needs it *)
Definition hrx5_B8R_segw
  (pre post: forall (x25519: list byte -> list byte -> list byte)
     (aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte))
     (xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte)
     (xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte))
     (gv: globals) (L: hrx5_loc) (FR: mpred)
     (R: hrx5_run) (sec: list byte) (birth: int64) (S: shim) (w: list int64) (NS: list hnode4)
     (PS: list (val * share * peer)) (T: tstate) (head nk: val) (KE: list kent4) (st i: Z) (kc lul: int64) (q: int)
     (proto: Z) (ip4 ip6 port: list byte) (o: hrx5_obj) (dp img tg: val) (ai ar: Z) (d: rxdraw)
     (a: val) (P: peer) (M: resp_msg) (ck h: list byte) (j: Z), environ -> mpred)
  (c: statement) (final: bool) : Prop :=
  forall (Espec: OracleKind) x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR
    R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j,
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> itable_wf T ->
  @semax W Espec (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (pre x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6
       port o dp img tg ai ar d a P M ck h j)
    c
    (overridePost
       (if final then hrx5_S8 x25519 gv L FR
        else post x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto
               ip4 ip6 port o dp img tg ai ar d a P M ck h j)
       (hrx5_RB x25519 gv L FR)).

Section Cut.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable gv: globals.
Variable L: hrx5_loc.
Variable FR: mpred.
Variables (R: hrx5_run) (sec: list byte) (birth: int64) (S: shim) (w: list int64) (NS: list hnode4)
  (PS: list (val * share * peer)) (T: tstate) (head nk: val) (KE: list kent4) (st i: Z) (kc lul: int64) (q: int)
  (proto: Z) (ip4 ip6 port: list byte) (o: hrx5_obj) (dp img tg: val) (ai ar: Z) (d: rxdraw)
  (a: val) (P: peer) (M: resp_msg) (ck h: list byte) (j: Z).

Definition hrx5_B8R_F : list Prop :=
  hrx5_B8R_facts x25519 aead_dec xaead_enc xaead_dec L R sec birth S w NS PS T kc lul q proto ip4 ip6 port o dp
    tg ai ar d a P M ck h j.
Definition hrx5_B8R_W1v : rxw :=
  hrx5_B8R_W1 x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6 port o dp d.
Definition hrx5_B8R_Wxv : rxw := hrx5_B8R_Wx hrx5_B8R_W1v d T PS a P M ck h.

Definition hrx5_B8R_R0 : environ -> mpred :=
  hrx5_B8R_St x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4
    ip6 port o dp img tg ai ar d hrx5_B8R_W1v [] hrx5_B8R_F.
Definition hrx5_B8R_RA : environ -> mpred :=
  hrx5_B8R_St x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4
    ip6 port o dp img tg ai ar d hrx5_B8R_W1v (hrx5_B8R_tl tg a d P 0) hrx5_B8R_F.
Definition hrx5_B8R_RB : environ -> mpred :=
  hrx5_B8R_St x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4
    ip6 port o dp img tg ai ar d hrx5_B8R_Wxv (hrx5_B8R_tl tg a d P 0) hrx5_B8R_F.
Definition hrx5_B8R_RD : environ -> mpred :=
  hrx5_B8R_St x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4
    ip6 port o dp img tg ai ar d hrx5_B8R_Wxv (hrx5_B8R_tl tg a d P (hrx5_B8R_nh T a PS)) hrx5_B8R_F.

End Cut.

(* the segments: A = statements 0..6, B = 7, D = 8..9, E = 10..11 *)
Definition hrx5_B8R_A_stmt : Prop := hrx5_B8R_seg hrx5_B8R_R0 hrx5_B8R_RA hrx5_B8R_A false.
(* B takes itable_wf T (see hrx5_B8R_segw) *)
Definition hrx5_B8R_B_stmt : Prop := hrx5_B8R_segw hrx5_B8R_RA hrx5_B8R_RB hrx5_B8R_B false.
Definition hrx5_B8R_D_stmt : Prop := hrx5_B8R_seg hrx5_B8R_RB hrx5_B8R_RD hrx5_B8R_D false.
(* E takes the invariant of the new world (hrx5_B8R_I_stmt, child I) as a hypothesis *)
Definition hrx5_B8R_E_stmt : Prop := hrx5_B8R_I_stmt -> hrx5_B8R_seg hrx5_B8R_RD hrx5_B8R_RD hrx5_B8R_E true.
