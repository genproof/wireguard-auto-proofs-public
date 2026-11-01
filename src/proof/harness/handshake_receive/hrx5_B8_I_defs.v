(* law handshake_receive, phase B8, branch I: the cut
   of hrx5_B8_I (initiation accepted) into five segments and the intermediate states.

   hrx5_B8_I = (t341 = target->p; h = &t341->handshake;) s = &target->snap; L1; L2; L3; L4; L5
     I0 = the three assignments and L1 = CHECK(rx_authenticated(target->p, &skb, 1, 0))      QI0 -> QI
     I1 = L2 = CHECK(h->state, remote_ephemeral, latest_timestamp, hash, chaining_key, remote_index,
                     last_initiation_consumption vs ci / mi / m_last_consumption)               QI -> QI
     I2 = L3 = CHECK(h->entry.*, static_identity, 4 x bytes_eq vs the snapshot s)              QI -> QI
     I3 = L4 = CHECK(refcount == target->refs && pr_same(&target->rest, target->p))            QI -> QI
     I4 = L5 = CHECK(hnodes_same_except(peers, target->p) && itd.head == head0 && kents_same(kes)
                     && shim_same(&ss))                                                       QI -> QI
     fold: QI |-- hrx5_S8 (the new world: hrx5_B8I_fold_stmt)
   The states QI0 / QI: hrx5_B8_Q of branch I with the world after the packet made explicit (hrx5_B8_I_pure.v:
   rx_model = rx_init_accepted ..: the device with the secret / birthdate after the checker's rotation (sec1,
   birth1), the peers with a's handshake consumed and its reference count back (hrx5_B8I_put), the shim S1 (the
   rotation's draw at most: the counters of S), the warnings w, the log hrx5_B8I_log). *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_conv.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_ilem.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* the statements                                                          *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_B8I_I0 := ltac:(let x := eval cbv delta [hrx5_B8_I] in hrx5_B8_I in
  match x with Ssequence (Ssequence ?a ?b) (Ssequence ?c (Ssequence ?l1 _)) =>
    exact (Ssequence (Ssequence (Ssequence a b) c) l1) end).
Definition hrx5_B8I_I1 := ltac:(let x := eval cbv delta [hrx5_B8_I] in hrx5_B8_I in
  match x with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence ?l2 _))) => exact l2 end).
Definition hrx5_B8I_I2 := ltac:(let x := eval cbv delta [hrx5_B8_I] in hrx5_B8_I in
  match x with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence ?l3 _)))) => exact l3 end).
Definition hrx5_B8I_I3 := ltac:(let x := eval cbv delta [hrx5_B8_I] in hrx5_B8_I in
  match x with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence ?l4 _))))) => exact l4 end).
Definition hrx5_B8I_I4 := ltac:(let x := eval cbv delta [hrx5_B8_I] in hrx5_B8_I in
  match x with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ ?l5))))) => exact l5 end).

Lemma hrx5_B8I_cut {Espec: OracleKind} {cs: compspecs} Delta Q0 Q1 Q2 R :
  semax Delta Q0 hrx5_B8I_I0 (overridePost Q1 R) ->
  semax Delta Q1 hrx5_B8I_I1 (overridePost Q1 R) ->
  semax Delta Q1 hrx5_B8I_I2 (overridePost Q1 R) ->
  semax Delta Q1 hrx5_B8I_I3 (overridePost Q1 R) ->
  semax Delta Q1 hrx5_B8I_I4 (overridePost Q2 R) ->
  semax Delta Q0 hrx5_B8_I (overridePost Q2 R).
Proof.
  intros H0 H1 H2 H3 H4.
  match goal with |- semax _ _ ?c _ =>
    let x := eval cbv delta [hrx5_B8_I] in c in
    match x with Ssequence ?ab (Ssequence ?s (Ssequence ?l1 _)) =>
      change c with (Ssequence ab (Ssequence s (Ssequence l1
        (Ssequence hrx5_B8I_I1 (Ssequence hrx5_B8I_I2 (Ssequence hrx5_B8I_I3 hrx5_B8I_I4))))))
    end end.
  apply <- seq_assoc. apply <- seq_assoc.
  eapply semax_seq; [rewrite overridePost_overridePost; exact H0 |].
  eapply semax_seq; [rewrite overridePost_overridePost; exact H1 |].
  eapply semax_seq; [rewrite overridePost_overridePost; exact H2 |].
  eapply semax_seq; [rewrite overridePost_overridePost; exact H3 | exact H4].
Qed.

(* ---------------------------------------------------------------------- *)
(* the world after the accepted initiation                                 *)
(* ---------------------------------------------------------------------- *)

(* the accepted peer after wg_peer_put: the kernel's new state with its reference count back *)
Definition hrx5_B8I_put (P: peer) (M: init_msg) (now: int64) (t ck2 h2: list byte) : peer :=
  p_set_refs (hrx5ci_new P M now t ck2 h2) (p_refs P).

(* the log after the accepted initiation of the peer a (skb sp, length len) *)
Definition hrx5_B8I_log (a sp: val) (len: int) : rxlog :=
  rx_tail (rx_send_response (rx_set_endpoint rx0 a sp) a) a len.

(* the receive world's memory after the packet, made explicit *)
Definition hrx5_B8I_world (x25519: list byte -> list byte -> list byte) (gv: globals) (L: hrx5_loc) (R: hrx5_run)
  (sec1: list byte) (birth1: int64) (T: tstate) (head: val) (PS1: list (val * share * peer)) (S1: shim)
  (w: list int64) (kc lul1: int64) (X: rxlog) : list mpred :=
  [device_rep Tsh (l_wd L) (hrx5_DL x25519 R L sec1 birth1); itable Tsh (l_itd L) T; ptable Tsh (l_ptd L) head;
   peers_rep PS1; shim_state4 gv S1 w; noise_globals gv kc; lul_rep gv lul1; rxlog_rep gv X].

(* the scratch locals in branch I: ds = the device after the packet, ss = the shim before, sks = the skb, ci =
   the harness's model of the accepted initiation, the others any *)
Definition hrx5_B8I_scr (x25519: list byte -> list byte -> list byte) (L: hrx5_loc) (R: hrx5_run)
  (sec1: list byte) (birth1: int64) (head: val) (S: shim) (w: list int64) (s: skb)
  (ck2 h2: list byte) (key spub: list val) (t: list byte) : list mpred :=
  [hout Tsh 32 (l_pub L); @data_at CKS Tsh t_devsnap (devsnap_val (hrx5_DL x25519 R L sec1 birth1) head) (l_ds L);
   @data_at CKS Tsh t_shimsnap (shimsnap_val S w) (l_ss L); @data_at CKS Tsh t_skbsnap (skbsnap_val s) (l_sks L);
   @data_at HCS Tsh t_mcinit (mcinit_val ck2 h2 key spub (bytes t)) (l_ci L); @data_at_ HCS Tsh t_mstate (l_st L);
   hout Tsh 32 (l_secret L); hout Tsh 16 (l_c L); hout Tsh 16 (l_mac L); hout Tsh 16 (l_pt L);
   @data_at_ Noise.CS Tsh t_init (l_t L); @data_at_ Noise.CS Tsh t_resp (l_t1 L); hout Tsh 16 (l_ck L);
   hout Tsh 32 (l_sst L); @data_at_ HCS Tsh t_mstate (l_before L)].

Section Q.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* the pure facts of branch I *)
Definition hrx5_B8I_props (L: hrx5_loc) (R: hrx5_run) (sec: list byte) (birth: int64) (S: shim) (w: list int64)
  (NS: list hnode4) (PS: list (val * share * peer)) (T: tstate) (head nk: val) (KE: list kent4) (st i: Z)
  (M: init_msg) (dp: val) (a: val) (P: peer) (t ck2 h2: list byte) (key spub: list val)
  (sec1: list byte) (birth1: int64) (S1: shim) : list Prop :=
  [hrx5_base_ok R sec birth S; hrx5_base_ok R sec1 birth1 S1; s_boot S1 = s_boot S; shim_eqb S w S1 w = true;
   hrx5_inv x25519 R L NS PS KE T head nk; 0 <= st <= Int64.max_unsigned; 0 <= i < st; im_ok M;
   malloc_compatible (Zlength (init_bytes M)) dp; hrx5_fwd (init_bytes M) = true;
   hrx5ci_tgt x25519 aead_dec (hrx5_ID x25519 R) PS M (s_boot S) = Some (a, P, t, ck2, h2);
   Zlength key = 32; Zlength spub = 32].

(* the temps of branch I (hrx5_B8_Q's, the values known) *)
Definition hrx5_B8I_temps (NS: list hnode4) (nk: val) (KE: list kent4) (st i: Z) (S: shim) (lul1: int64)
  (dp img: val) (M: init_msg) (T: tstate) (a: val) : list localdef :=
  [temp HM._nk nk; temp HM._kes (hrx5_khead KE); temp HM._steps (Vlong (Int64.repr st));
   temp HM._i (Vlong (Int64.repr i)); temp HM._now (Vlong (s_boot S)); temp HM._m_lul (Vlong lul1);
   temp HM._buf nullval; temp HM._mi dp; temp HM._mr nullval; temp HM._mc nullval;
   temp HM._img img; temp HM._len (Vlong (Int64.repr (Zlength (init_bytes M))));
   temp HM._kind (Vint (Int.repr 1)); temp HM._acc_init (Vint (Int.repr 1)); temp HM._acc_resp (Vint (Int.repr 0));
   temp HM._target (hrx5_nfind NS a); temp HM._head0 (hd nullval (t_L T)); temp HM._path (Vint (Int.repr 1))].

(* the start of branch I: hrx5_B8_Q with the world after the packet explicit *)
Definition hrx5_B8I_QI0 (gv: globals) (L: hrx5_loc) (FR: mpred)
  (R: hrx5_run) (sec: list byte) (birth: int64) (S: shim) (w: list int64) (NS: list hnode4)
  (PS: list (val * share * peer)) (T: tstate) (head nk: val) (KE: list kent4) (st i: Z) (kc: int64) (q: int)
  (proto: Z) (ip4 ip6 port: list byte) (M: init_msg) (dp img: val)
  (a: val) (P: peer) (t ck2 h2: list byte) (key spub: list val) (sec1: list byte) (birth1: int64) (S1: shim)
  (lul1: int64) : environ -> mpred :=
  let s := hrx5_skb dp (OInit M) proto ip4 ip6 port in
  PROPx (hrx5_B8I_props L R sec birth S w NS PS T head nk KE st i M dp a P t ck2 h2 key spub sec1 birth1 S1)
  (LOCALx (hrx5_B8I_temps NS nk KE st i S lul1 dp img M T a ++ hrx5_lvars gv L)
  (SEPx (hrx5_B8I_world x25519 gv L R sec1 birth1 T head (supd PS a (hrx5_B8I_put P M (s_boot S) t ck2 h2)) S1 w
           kc lul1 (hrx5_B8I_log a (l_skb L) (sk_len s)) ++
         hrx5_rest x25519 R L (hnodes_snapped4 T NS PS) (map (kent_snapped T) KE) ++
         hrx5_cglobs gv FR ++
         [qlen_rep gv q; skb_rep Tsh (l_skb L) s; @malloc_token W Ews t_init dp; init_rep Ews dp M;
          img_rep img (init_bytes M)] ++
         hrx5_B8I_scr x25519 L R sec1 birth1 head S w s ck2 h2 key spub t))).

(* after I0 (and I1 .. I3): h = &a->handshake, s = &target->snap (offset 8 of struct hnode) *)
Definition hrx5_B8I_QI (gv: globals) (L: hrx5_loc) (FR: mpred)
  (R: hrx5_run) (sec: list byte) (birth: int64) (S: shim) (w: list int64) (NS: list hnode4)
  (PS: list (val * share * peer)) (T: tstate) (head nk: val) (KE: list kent4) (st i: Z) (kc: int64) (q: int)
  (proto: Z) (ip4 ip6 port: list byte) (M: init_msg) (dp img: val)
  (a: val) (P: peer) (t ck2 h2: list byte) (key spub: list val) (sec1: list byte) (birth1: int64) (S1: shim)
  (lul1: int64) : environ -> mpred :=
  let s := hrx5_skb dp (OInit M) proto ip4 ip6 port in
  PROPx (hrx5_B8I_props L R sec birth S w NS PS T head nk KE st i M dp a P t ck2 h2 key spub sec1 birth1 S1)
  (LOCALx (temp HM._h__1 (hs_addr a) :: temp HM._s (offset_val 8 (hrx5_nfind NS a)) ::
           hrx5_B8I_temps NS nk KE st i S lul1 dp img M T a ++ hrx5_lvars gv L)
  (SEPx (hrx5_B8I_world x25519 gv L R sec1 birth1 T head (supd PS a (hrx5_B8I_put P M (s_boot S) t ck2 h2)) S1 w
           kc lul1 (hrx5_B8I_log a (l_skb L) (sk_len s)) ++
         hrx5_rest x25519 R L (hnodes_snapped4 T NS PS) (map (kent_snapped T) KE) ++
         hrx5_cglobs gv FR ++
         [qlen_rep gv q; skb_rep Tsh (l_skb L) s; @malloc_token W Ews t_init dp; init_rep Ews dp M;
          img_rep img (init_bytes M)] ++
         hrx5_B8I_scr x25519 L R sec1 birth1 head S w s ck2 h2 key spub t))).

End Q.

(* the segment statements (children: hrx5_B8_I_<seg>.v, `hrx5_B8I_<seg>_ok : hrx5_B8I_<seg>_stmt`) *)
Definition hrx5_B8I_seg (pre post: forall (x25519: list byte -> list byte -> list byte)
    (aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte)), globals -> hrx5_loc -> mpred ->
    hrx5_run -> list byte -> int64 -> shim -> list int64 -> list hnode4 -> list (val * share * peer) -> tstate ->
    val -> val -> list kent4 -> Z -> Z -> int64 -> int -> Z -> list byte -> list byte -> list byte -> init_msg ->
    val -> val -> val -> peer -> list byte -> list byte -> list byte -> list val -> list val -> list byte ->
    int64 -> shim -> int64 -> environ -> mpred) (stmt: statement) : Prop :=
  forall (Espec: OracleKind) x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR
    R sec birth S w NS PS T head nk KE st i kc q proto ip4 ip6 port M dp img a P t ck2 h2 key spub sec1 birth1
    S1 lul1,
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  @semax W Espec (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (pre x25519 aead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc q proto ip4 ip6 port M dp img a P t
       ck2 h2 key spub sec1 birth1 S1 lul1)
    stmt
    (overridePost (post x25519 aead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc q proto ip4 ip6 port M
       dp img a P t ck2 h2 key spub sec1 birth1 S1 lul1) (hrx5_RB x25519 gv L FR)).

Definition hrx5_B8I_I0_stmt : Prop := hrx5_B8I_seg hrx5_B8I_QI0 hrx5_B8I_QI hrx5_B8I_I0.
Definition hrx5_B8I_I1_stmt : Prop := hrx5_B8I_seg hrx5_B8I_QI hrx5_B8I_QI hrx5_B8I_I1.
Definition hrx5_B8I_I2_stmt : Prop := hrx5_B8I_seg hrx5_B8I_QI hrx5_B8I_QI hrx5_B8I_I2.
Definition hrx5_B8I_I3_stmt : Prop := hrx5_B8I_seg hrx5_B8I_QI hrx5_B8I_QI hrx5_B8I_I3.
Definition hrx5_B8I_I4_stmt : Prop := hrx5_B8I_seg hrx5_B8I_QI hrx5_B8I_QI hrx5_B8I_I4.

(* the end of branch I: the loop's state hrx5_S8 with a NEW world (sec1, birth1, S1, lul1; the peers with a's
   handshake consumed, the nodes and kents with their snapshots) *)
Definition hrx5_B8I_fold_stmt : Prop :=
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR
    R sec birth S w NS PS T head nk KE st i kc q proto ip4 ip6 port M dp img a P t ck2 h2 key spub sec1 birth1
    S1 lul1,
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  ENTAIL (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec),
    hrx5_B8I_QI x25519 aead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc q proto ip4 ip6 port M dp img
      a P t ck2 h2 key spub sec1 birth1 S1 lul1
  |-- hrx5_S8 x25519 gv L FR.
