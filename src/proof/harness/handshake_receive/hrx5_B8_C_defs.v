(* law handshake_receive, phase B8, branch C: the
   cut of hrx5_B8_C (a cookie reply accepted) into segments and the intermediate states.

   hrx5_B8_C = (t'252 = target->p; ck = &t'252->latest_cookie;) L1; L2; L3; L4
     C0 = the two assignments and L1 = CHECK(rx_only_cookie(0))                                 QC0 -> QC
     C1 = L2 = CHECK(bytes_eq(ck->cookie, pt, 16) && ck->birthdate == now && ck->is_valid &&
                     !ck->have_sent_mac1 && bytes_eq(ck->last_mac1_sent / cookie_decryption_key /
                     message_mac1_key, target->rest.cookie.<same>))                              QC -> QC
     C2 = L3 = CHECK(hs_same(&target->snap, &target->p->handshake) &&
                     target->p->refcount.refcount == target->refs &&
                     pr_same_but_cookie(&target->rest, target->p))                               QC -> QC
     C3 = L4 = CHECK(hnodes_same_except(peers, target->p) && itd.head == head0 && kents_same(kes) &&
                     shim_same(&ss))                                                             QC -> QC
   then the fold QC |-- hrx5_S8 (hrx5_B8C_fold_stmt) and, before C0, the entry hrx5_B8_Q |-- EX .. QC0
   (hrx5_B8C_entry_stmt: the pure analysis of branch C: o = OCookie M, the cookie reply forwarded and accepted by
   the harness's model hrx5ck_tgt = Some (a, P, pt), tg = hrx5_nfind NS a, and by hrx5ck_agree the receive world
   after the packet = the one before with a's cookie hrx5ck_new P pt now: no rotation, no draw, the log rx0).
   The states QC0 / QC: hrx5_B8_Q of branch C with that world explicit. *)
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

#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* the statements                                                          *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_B8C_C0 := ltac:(let x := eval cbv delta [hrx5_B8_C] in hrx5_B8_C in
  match x with Ssequence ?ab (Ssequence ?l1 _) => exact (Ssequence ab l1) end).
Definition hrx5_B8C_C1 := ltac:(let x := eval cbv delta [hrx5_B8_C] in hrx5_B8_C in
  match x with Ssequence _ (Ssequence _ (Ssequence ?l2 _)) => exact l2 end).
Definition hrx5_B8C_C2 := ltac:(let x := eval cbv delta [hrx5_B8_C] in hrx5_B8_C in
  match x with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence ?l3 _))) => exact l3 end).
Definition hrx5_B8C_C3 := ltac:(let x := eval cbv delta [hrx5_B8_C] in hrx5_B8_C in
  match x with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ ?l4))) => exact l4 end).

Lemma hrx5_B8C_cut {Espec: OracleKind} {cs: compspecs} Delta Q0 Q1 R :
  semax Delta Q0 hrx5_B8C_C0 (overridePost Q1 R) ->
  semax Delta Q1 hrx5_B8C_C1 (overridePost Q1 R) ->
  semax Delta Q1 hrx5_B8C_C2 (overridePost Q1 R) ->
  semax Delta Q1 hrx5_B8C_C3 (overridePost Q1 R) ->
  semax Delta Q0 hrx5_B8_C (overridePost Q1 R).
Proof.
  intros H0 H1 H2 H3.
  match goal with |- semax _ _ ?c _ =>
    let x := eval cbv delta [hrx5_B8_C] in c in
    match x with Ssequence ?ab (Ssequence ?l1 _) =>
      change c with (Ssequence ab (Ssequence l1
        (Ssequence hrx5_B8C_C1 (Ssequence hrx5_B8C_C2 hrx5_B8C_C3))))
    end end.
  apply <- seq_assoc.
  eapply semax_seq; [rewrite overridePost_overridePost; exact H0 |].
  eapply semax_seq; [rewrite overridePost_overridePost; exact H1 |].
  eapply semax_seq; [rewrite overridePost_overridePost; exact H2 | exact H3].
Qed.

(* ---------------------------------------------------------------------- *)
(* the world after the accepted cookie reply                               *)
(* ---------------------------------------------------------------------- *)

(* the receive world's memory after the packet (rxw_rep of it, keypairs_rep [] dropped): D, T, the peers PS1, the
   shim S and its warnings w unchanged, the log rx0 *)
Definition hrx5_B8C_world (x25519: list byte -> list byte -> list byte) (gv: globals) (L: hrx5_loc) (R: hrx5_run)
  (sec: list byte) (birth: int64) (T: tstate) (head: val) (PS1: list (val * share * peer)) (S: shim)
  (w: list int64) (kc lul: int64) : list mpred :=
  [device_rep Tsh (l_wd L) (hrx5_DL x25519 R L sec birth); itable Tsh (l_itd L) T; ptable Tsh (l_ptd L) head;
   peers_rep PS1; shim_state4 gv S w; noise_globals gv kc; lul_rep gv lul; rxlog_rep gv rx0].

(* the scratch locals in branch C: ds = the device (unchanged), ss = the shim, sks = the skb, pt = the plaintext
   cookie, the others any *)
Definition hrx5_B8C_scr (x25519: list byte -> list byte -> list byte) (L: hrx5_loc) (R: hrx5_run)
  (sec: list byte) (birth: int64) (head: val) (S: shim) (w: list int64) (s: skb) (pt: list byte) : list mpred :=
  [hout Tsh 32 (l_pub L); @data_at CKS Tsh t_devsnap (devsnap_val (hrx5_DL x25519 R L sec birth) head) (l_ds L);
   @data_at CKS Tsh t_shimsnap (shimsnap_val S w) (l_ss L); @data_at CKS Tsh t_skbsnap (skbsnap_val s) (l_sks L);
   @data_at_ HCS Tsh t_mcinit (l_ci L); @data_at_ HCS Tsh t_mstate (l_st L);
   hout Tsh 32 (l_secret L); hout Tsh 16 (l_c L); hout Tsh 16 (l_mac L); hbytes Tsh pt (l_pt L);
   @data_at_ Noise.CS Tsh t_init (l_t L); @data_at_ Noise.CS Tsh t_resp (l_t1 L); hout Tsh 16 (l_ck L);
   hout Tsh 32 (l_sst L); @data_at_ HCS Tsh t_mstate (l_before L)].

Section Q.
Variable x25519: list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* the pure facts of branch C *)
Definition hrx5_B8C_props (L: hrx5_loc) (R: hrx5_run) (sec: list byte) (birth: int64) (S: shim)
  (NS: list hnode4) (PS: list (val * share * peer)) (T: tstate) (head nk: val) (KE: list kent4) (st i: Z)
  (M: cookie_msg) (dp: val) (a: val) (P: peer) (pt: list byte) : list Prop :=
  [hrx5_base_ok R sec birth S; hrx5_inv x25519 R L NS PS KE T head nk; 0 <= st <= Int64.max_unsigned;
   0 <= i < st; cm_ok M; malloc_compatible (Zlength (cookie_msg_bytes M)) dp;
   hrx5_fwd (cookie_msg_bytes M) = true; hrx5ck_tgt xaead_dec T PS M = Some (a, P, pt);
   hrx5_nfind NS a <> nullval; sfind PS a = Some (Ews, P); Zlength pt = 16].

(* the temps of branch C (hrx5_B8_Q's, the values known) *)
Definition hrx5_B8C_temps (NS: list hnode4) (nk: val) (KE: list kent4) (st i: Z) (S: shim) (lul: int64)
  (dp img: val) (M: cookie_msg) (T: tstate) (a: val) : list localdef :=
  [temp HM._nk nk; temp HM._kes (hrx5_khead KE); temp HM._steps (Vlong (Int64.repr st));
   temp HM._i (Vlong (Int64.repr i)); temp HM._now (Vlong (s_boot S)); temp HM._m_lul (Vlong lul);
   temp HM._buf nullval; temp HM._mi nullval; temp HM._mr nullval; temp HM._mc dp;
   temp HM._img img; temp HM._len (Vlong (Int64.repr (Zlength (cookie_msg_bytes M))));
   temp HM._kind (Vint (Int.repr 3)); temp HM._acc_init (Vint (Int.repr 0)); temp HM._acc_resp (Vint (Int.repr 0));
   temp HM._target (hrx5_nfind NS a); temp HM._head0 (hd nullval (t_L T)); temp HM._path (Vint (Int.repr 1))].

(* the SEP of branch C *)
Definition hrx5_B8C_sep (gv: globals) (L: hrx5_loc) (FR: mpred)
  (R: hrx5_run) (sec: list byte) (birth: int64) (S: shim) (w: list int64) (NS: list hnode4)
  (PS: list (val * share * peer)) (T: tstate) (head: val) (KE: list kent4) (kc lul: int64) (q: int)
  (proto: Z) (ip4 ip6 port: list byte) (M: cookie_msg) (dp img: val) (a: val) (P: peer) (pt: list byte)
  : list mpred :=
  let s := hrx5_skb dp (OCookie M) proto ip4 ip6 port in
  hrx5_B8C_world x25519 gv L R sec birth T head (supd PS a (hrx5ck_new P pt (s_boot S))) S w kc lul ++
  hrx5_rest x25519 R L (hnodes_snapped4 T NS PS) (map (kent_snapped T) KE) ++
  hrx5_cglobs gv FR ++
  [qlen_rep gv q; skb_rep Tsh (l_skb L) s; @malloc_token W Ews t_cmsg dp; cmsg_rep Ews dp M;
   img_rep img (cookie_msg_bytes M)] ++
  hrx5_B8C_scr x25519 L R sec birth head S w s pt.

(* the start of branch C: hrx5_B8_Q with the world after the packet explicit *)
Definition hrx5_B8C_QC0 (gv: globals) (L: hrx5_loc) (FR: mpred)
  (R: hrx5_run) (sec: list byte) (birth: int64) (S: shim) (w: list int64) (NS: list hnode4)
  (PS: list (val * share * peer)) (T: tstate) (head nk: val) (KE: list kent4) (st i: Z) (kc lul: int64) (q: int)
  (proto: Z) (ip4 ip6 port: list byte) (M: cookie_msg) (dp img: val) (a: val) (P: peer) (pt: list byte)
  : environ -> mpred :=
  PROPx (hrx5_B8C_props L R sec birth S NS PS T head nk KE st i M dp a P pt)
  (LOCALx (hrx5_B8C_temps NS nk KE st i S lul dp img M T a ++ hrx5_lvars gv L)
  (SEPx (hrx5_B8C_sep gv L FR R sec birth S w NS PS T head KE kc lul q proto ip4 ip6 port M dp img a P pt))).

(* after C0 (and C1 .. C3): ck = &a->latest_cookie (offset 360 of struct wg_peer) *)
Definition hrx5_B8C_QC (gv: globals) (L: hrx5_loc) (FR: mpred)
  (R: hrx5_run) (sec: list byte) (birth: int64) (S: shim) (w: list int64) (NS: list hnode4)
  (PS: list (val * share * peer)) (T: tstate) (head nk: val) (KE: list kent4) (st i: Z) (kc lul: int64) (q: int)
  (proto: Z) (ip4 ip6 port: list byte) (M: cookie_msg) (dp img: val) (a: val) (P: peer) (pt: list byte)
  : environ -> mpred :=
  PROPx (hrx5_B8C_props L R sec birth S NS PS T head nk KE st i M dp a P pt)
  (LOCALx (temp HM._ck__1 (offset_val 360 a) ::
           hrx5_B8C_temps NS nk KE st i S lul dp img M T a ++ hrx5_lvars gv L)
  (SEPx (hrx5_B8C_sep gv L FR R sec birth S w NS PS T head KE kc lul q proto ip4 ip6 port M dp img a P pt))).

End Q.

(* the segment statements (children: hrx5_B8_C_<seg>.v, `hrx5_B8C_<seg>_ok : hrx5_B8C_<seg>_stmt`) *)
Definition hrx5_B8C_seg (pre: forall (x25519: list byte -> list byte -> list byte)
    (xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte)), globals -> hrx5_loc ->
    mpred -> hrx5_run -> list byte -> int64 -> shim -> list int64 -> list hnode4 -> list (val * share * peer) ->
    tstate -> val -> val -> list kent4 -> Z -> Z -> int64 -> int64 -> int -> Z -> list byte -> list byte ->
    list byte -> cookie_msg -> val -> val -> val -> peer -> list byte -> environ -> mpred)
  (stmt: statement) : Prop :=
  forall (Espec: OracleKind) x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR
    R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img a P pt,
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  @semax W Espec (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (pre x25519 xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img a P pt)
    stmt
    (overridePost (hrx5_B8C_QC x25519 xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4
       ip6 port M dp img a P pt) (hrx5_RB x25519 gv L FR)).

Definition hrx5_B8C_C0_stmt : Prop := hrx5_B8C_seg hrx5_B8C_QC0 hrx5_B8C_C0.
Definition hrx5_B8C_C1_stmt : Prop := hrx5_B8C_seg hrx5_B8C_QC hrx5_B8C_C1.
Definition hrx5_B8C_C2_stmt : Prop := hrx5_B8C_seg hrx5_B8C_QC hrx5_B8C_C2.
Definition hrx5_B8C_C3_stmt : Prop := hrx5_B8C_seg hrx5_B8C_QC hrx5_B8C_C3.

(* the fold: after the CHECKs, the loop's state hrx5_S8 with the new world (a's updated peer, the nodes and
   kents as snapped) *)
Definition hrx5_B8C_fold_stmt : Prop :=
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR
    R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img a P pt,
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  ENTAIL (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec),
    hrx5_B8C_QC x25519 xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp
      img a P pt
  |-- hrx5_S8 x25519 gv L FR.

(* the entry: hrx5_B8_Q in branch C is QC0 for some M, a, P, pt *)
Definition hrx5_B8C_entry_stmt : Prop :=
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR
    R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d,
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hrx5_B8_isC o (hrx5_B8_path x25519 L R sec birth S w PS T kc lul q proto ip4 ip6 port o dp d) ai ar tg ->
  ENTAIL (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec),
    hrx5_B8_Q x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
      proto ip4 ip6 port o dp img tg ai ar d
  |-- EX M: cookie_msg, EX a: val, EX P: peer, EX pt: list byte,
        hrx5_B8C_QC0 x25519 xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port
          M dp img a P pt.
