(* law handshake_receive, phase B4, segment I: the cut of the
   model block hrx5_B4_M for an initiation object OInit M into segments, and the intermediate states.  Port of
   consume_initiation_any's hci5_p7_defs.v. 'B4' (segment I).
   hrx5_B4_M = a1; if2,   a1 = the three conditionals (fwd, kind == 1, id.ok, m_consume_initiation_1) into t'97,
   if2 = if (t'97) body else els   (els: the response / cookie branches, conditions false for kind 1),
   body = lp; ifp,   lp = (nd = peers); the first-match loop (target = nd),   ifp = if (target != NULL) x else skip,
   x = e1; (((c2; if14); if15); asg)   (e1: m_precomputed into sst, c2: m_consume_initiation_2 (t'78),
   if14: m_ts_newer (t'79), if15: m_not_flood (t'81), asg: acc_init = t'81). *)
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
#[local] Existing Instance W_handshake_receive.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_defs.
Local Open Scope logic.

Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_I_pure.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* the statements                                                          *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_B4_I_a1 : statement :=
  ltac:(let x := eval cbv delta [hrx5_B4_M] in hrx5_B4_M in match x with Ssequence ?a _ => exact a end).
Definition hrx5_B4_I_if2 : statement :=
  ltac:(let x := eval cbv delta [hrx5_B4_M] in hrx5_B4_M in match x with Ssequence _ ?a => exact a end).
Definition hrx5_B4_I_body : statement :=
  ltac:(let x := eval cbv delta [hrx5_B4_I_if2] in hrx5_B4_I_if2 in match x with Sifthenelse _ ?a _ => exact a end).
Definition hrx5_B4_I_els : statement :=
  ltac:(let x := eval cbv delta [hrx5_B4_I_if2] in hrx5_B4_I_if2 in match x with Sifthenelse _ _ ?a => exact a end).
Definition hrx5_B4_I_lp : statement :=
  ltac:(let x := eval cbv delta [hrx5_B4_I_body] in hrx5_B4_I_body in match x with Ssequence ?a _ => exact a end).
Definition hrx5_B4_I_ifp : statement :=
  ltac:(let x := eval cbv delta [hrx5_B4_I_body] in hrx5_B4_I_body in match x with Ssequence _ ?a => exact a end).
Definition hrx5_B4_I_x : statement :=
  ltac:(let x := eval cbv delta [hrx5_B4_I_ifp] in hrx5_B4_I_ifp in match x with Sifthenelse _ ?a Sskip => exact a end).
Definition hrx5_B4_I_e1 : statement :=
  ltac:(let x := eval cbv delta [hrx5_B4_I_x] in hrx5_B4_I_x in match x with Ssequence ?a _ => exact a end).
Definition hrx5_B4_I_c2 : statement :=
  ltac:(let x := eval cbv delta [hrx5_B4_I_x] in hrx5_B4_I_x in
        match x with Ssequence _ (Ssequence (Ssequence (Ssequence ?a _) _) _) => exact a end).
Definition hrx5_B4_I_if14 : statement :=
  ltac:(let x := eval cbv delta [hrx5_B4_I_x] in hrx5_B4_I_x in
        match x with Ssequence _ (Ssequence (Ssequence (Ssequence _ ?a) _) _) => exact a end).
Definition hrx5_B4_I_if15 : statement :=
  ltac:(let x := eval cbv delta [hrx5_B4_I_x] in hrx5_B4_I_x in
        match x with Ssequence _ (Ssequence (Ssequence _ ?a) _) => exact a end).
Definition hrx5_B4_I_asg : statement :=
  ltac:(let x := eval cbv delta [hrx5_B4_I_x] in hrx5_B4_I_x in match x with Ssequence _ (Ssequence _ ?a) => exact a end).

Lemma hrx5_B4_I_M_eq : hrx5_B4_M = Ssequence hrx5_B4_I_a1 hrx5_B4_I_if2.
Proof. reflexivity. Qed.
Definition hrx5_B4_I_c97 : expr :=
  ltac:(let x := eval cbv delta [hrx5_B4_I_if2] in hrx5_B4_I_if2 in match x with Sifthenelse ?a _ _ => exact a end).
Definition hrx5_B4_I_cp : expr :=
  ltac:(let x := eval cbv delta [hrx5_B4_I_ifp] in hrx5_B4_I_ifp in match x with Sifthenelse ?a _ _ => exact a end).
Lemma hrx5_B4_I_if2_eq : hrx5_B4_I_if2 = Sifthenelse hrx5_B4_I_c97 hrx5_B4_I_body hrx5_B4_I_els.
Proof. reflexivity. Qed.
Lemma hrx5_B4_I_body_eq : hrx5_B4_I_body = Ssequence hrx5_B4_I_lp hrx5_B4_I_ifp.
Proof. reflexivity. Qed.
Lemma hrx5_B4_I_ifp_eq : hrx5_B4_I_ifp = Sifthenelse hrx5_B4_I_cp hrx5_B4_I_x Sskip.
Proof. reflexivity. Qed.
Lemma hrx5_B4_I_x_eq :
  hrx5_B4_I_x = Ssequence hrx5_B4_I_e1 (Ssequence (Ssequence (Ssequence hrx5_B4_I_c2 hrx5_B4_I_if14) hrx5_B4_I_if15)
                                                  hrx5_B4_I_asg).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* the states                                                              *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* the scratch locals with ci and sst as given *)
Definition hrx5_B4_I_scr (L: hrx5_loc) (ci sst: mpred) : list mpred :=
  [hout Tsh 32 (l_pub L); @data_at_ CKS Tsh t_devsnap (l_ds L); @data_at_ CKS Tsh t_shimsnap (l_ss L);
   @data_at_ CKS Tsh t_skbsnap (l_sks L); ci; @data_at_ HCS Tsh t_mstate (l_st L);
   hout Tsh 32 (l_secret L); hout Tsh 16 (l_c L); hout Tsh 16 (l_mac L); hout Tsh 16 (l_pt L);
   @data_at_ Noise.CS Tsh t_init (l_t L); @data_at_ Noise.CS Tsh t_resp (l_t1 L); hout Tsh 16 (l_ck L);
   sst; @data_at_ HCS Tsh t_mstate (l_before L)].

(* hrx5_B4_Q for o = OInit M with extra temps tl (in front), target = tg, ci and sst as given *)
Definition hrx5_B4_I_st (gv: globals) (L: hrx5_loc) (FR: mpred) (R: hrx5_run) (sec: list byte) (birth: int64)
  (S: shim) (w: list int64) (NS: list hnode4) (PS: list (val * share * peer)) (T: tstate) (head nk: val)
  (KE: list kent4) (st i: Z) (kc lul: int64) (q: int) (proto: Z) (ip4 ip6 port: list byte) (M: init_msg)
  (dp img: val) (tl: list localdef) (tg: val) (ci sst: mpred) : environ -> mpred :=
  PROPx [hrx5_base_ok R sec birth S; hrx5_inv x25519 R L NS PS KE T head nk; 0 <= st <= Int64.max_unsigned;
         0 <= i < st; obj_ok (OInit M); malloc_compatible (Zlength (obj_bytes (OInit M))) dp]
  (LOCALx (tl ++ hrx5_ltemps nk KE st i S lul ++ hrx5_ptrs dp (OInit M) ++
           [temp HM._img img; temp HM._len (Vlong (Int64.repr (Zlength (obj_bytes (OInit M)))));
            temp HM._kind (Vint (Int.repr (obj_kind (OInit M))));
            temp HM._tw (Vint (if Z.leb 4 (Zlength (obj_bytes (OInit M))) then hrx5_tw (obj_bytes (OInit M))
                               else Int.zero));
            temp HM._fwd (Vint (if hrx5_fwd (obj_bytes (OInit M)) then Int.one else Int.zero));
            temp HM._acc_init (Vint Int.zero); temp HM._acc_resp (Vint Int.zero); temp HM._target tg] ++
           hrx5_lvars gv L)
  (SEPx (hrx5_wcore x25519 R L sec birth T head PS ++
         hrx5_rest x25519 R L (hnodes_snapped4 T NS PS) (map (kent_snapped T) KE) ++
         hrx5_globs gv S w kc FR ++
         [lul_rep gv lul; @data_at_ HRX Ews t_rxlog (gv HM._wg_shim_rx); qlen_rep gv q;
          skb_rep Tsh (l_skb L) (hrx5_skb dp (OInit M) proto ip4 ip6 port); obj_rep dp (OInit M);
          img_rep img (obj_bytes (OInit M))] ++
         hrx5_B4_I_scr L ci sst))).

(* stage 1 of the harness's model, as the code reaches it (fwd, kind == 1 (true), id.ok) *)
Definition hrx5_B4_I_c1 (IB: mident) (M: init_msg) : option (list byte * list byte * list byte * list byte) :=
  if mi_ok IB then m_consume_init1_model x25519 aead_dec IB (im_eph M) (im_encs M) else None.
Definition hrx5_B4_I_c1f (IB: mident) (M: init_msg) : option (list byte * list byte * list byte * list byte) :=
  if hrx5_fwd (init_bytes M) then hrx5_B4_I_c1 IB M else None.

Definition hrx5_B4_I_ci1 (L: hrx5_loc) (c: option (list byte * list byte * list byte * list byte)) : mpred :=
  match c with
  | Some (s, key, ck, h) => @data_at HCS Tsh t_mcinit (mcinit_val ck h (bytes key) (bytes s) (Zrepeat Vundef 12)) (l_ci L)
  | None => @data_at_ HCS Tsh t_mcinit (l_ci L)
  end.

Definition hrx5_B4_I_ok1 (c: option (list byte * list byte * list byte * list byte)) : bool :=
  match c with Some _ => true | None => false end.

Definition hrx5_B4_I_SS (IB: mident) (P: peer) : list byte := m_precomputed_model x25519 IB (hs_rstatic (p_hs P)).

(* stage 2 *)
Definition hrx5_B4_I_c2v (SS ck1 h1: list byte) (M: init_msg) : option (list byte * list byte * list byte) :=
  m_consume_init2_model aead_dec SS ck1 h1 (im_enct M).

Definition hrx5_B4_I_ci2 (L: hrx5_loc) (SS ck1 s: list byte) (c: option (list byte * list byte * list byte)) : mpred :=
  match c with
  | Some (t, ck, h) => @data_at HCS Tsh t_mcinit (mcinit_val ck h (bytes (kdf2 ck1 SS)) (bytes s) (bytes t)) (l_ci L)
  | None => @data_at_ HCS Tsh t_mcinit (l_ci L)
  end.

Definition hrx5_B4_I_b15 (c: option (list byte * list byte * list byte)) (P: peer) : bool :=
  match c with Some (t, _, _) => ts_newer t (hs_ts (p_hs P)) | None => false end.

Section Fixed.
Variables (gv: globals) (L: hrx5_loc) (FR: mpred) (R: hrx5_run) (sec: list byte) (birth: int64)
  (S: shim) (w: list int64) (NS: list hnode4) (PS: list (val * share * peer)) (T: tstate) (head nk: val)
  (KE: list kent4) (st i: Z) (kc lul: int64) (q: int) (proto: Z) (ip4 ip6 port: list byte) (M: init_msg)
  (dp img: val).

Local Notation ST := (hrx5_B4_I_st gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img).
Local Notation ID := (hrx5_ID x25519 R).

(* after a1 *)
Definition hrx5_B4_I_Q1 : environ -> mpred :=
  ST [temp HM._t'97 (Vint (if hrx5_B4_I_ok1 (hrx5_B4_I_c1f ID M) then Int.one else Int.zero))] nullval
     (hrx5_B4_I_ci1 L (hrx5_B4_I_c1f ID M)) (hout Tsh 32 (l_sst L)).

(* body's start: stage 1 succeeded with (s, key, ck1, h1) *)
Definition hrx5_B4_I_Q2 (s key ck1 h1: list byte) : environ -> mpred :=
  ST [] nullval (hrx5_B4_I_ci1 L (Some (s, key, ck1, h1))) (hout Tsh 32 (l_sst L)).

(* after the first-match loop *)
Definition hrx5_B4_I_Qb (s key ck1 h1: list byte) : environ -> mpred :=
  ST [] (hrx5_B4_I_fmv (hrx5_B4_I_fm (hnodes_snapped4 T NS PS) PS s))
     (hrx5_B4_I_ci1 L (Some (s, key, ck1, h1))) (hout Tsh 32 (l_sst L)).

(* x's start: the loop found the node of peer a (pk_find PS s = Some (a, P)) *)
Definition hrx5_B4_I_Qf (s key ck1 h1: list byte) (a: val) : environ -> mpred :=
  ST [] (hrx5_nfind NS a) (hrx5_B4_I_ci1 L (Some (s, key, ck1, h1))) (hout Tsh 32 (l_sst L)).

(* after e1 (m_precomputed) *)
Definition hrx5_B4_I_Q5 (s key ck1 h1: list byte) (a: val) (P: peer) : environ -> mpred :=
  ST [] (hrx5_nfind NS a) (hrx5_B4_I_ci1 L (Some (s, key, ck1, h1))) (hbytes Tsh (hrx5_B4_I_SS ID P) (l_sst L)).

(* after c2 *)
Definition hrx5_B4_I_Q6 (s ck1 h1: list byte) (a: val) (P: peer) : environ -> mpred :=
  ST [temp HM._t'78 (Vint (match hrx5_B4_I_c2v (hrx5_B4_I_SS ID P) ck1 h1 M with Some _ => Int.one | None => Int.zero end))]
     (hrx5_nfind NS a) (hrx5_B4_I_ci2 L (hrx5_B4_I_SS ID P) ck1 s (hrx5_B4_I_c2v (hrx5_B4_I_SS ID P) ck1 h1 M))
     (hbytes Tsh (hrx5_B4_I_SS ID P) (l_sst L)).

(* after if14 (m_ts_newer) *)
Definition hrx5_B4_I_Q7 (s ck1 h1: list byte) (a: val) (P: peer) : environ -> mpred :=
  ST [temp HM._t'79 (Vint (if hrx5_B4_I_b15 (hrx5_B4_I_c2v (hrx5_B4_I_SS ID P) ck1 h1 M) P then Int.one else Int.zero))]
     (hrx5_nfind NS a) (hrx5_B4_I_ci2 L (hrx5_B4_I_SS ID P) ck1 s (hrx5_B4_I_c2v (hrx5_B4_I_SS ID P) ck1 h1 M))
     (hbytes Tsh (hrx5_B4_I_SS ID P) (l_sst L)).

(* after if15 (m_not_flood) *)
Definition hrx5_B4_I_Q8 (s ck1 h1: list byte) (a: val) (P: peer) : environ -> mpred :=
  ST [temp HM._t'81 (Vint (if (hrx5_B4_I_b15 (hrx5_B4_I_c2v (hrx5_B4_I_SS ID P) ck1 h1 M) P &&
                               not_flood (hs_lic (p_hs P)) (s_boot S))%bool then Int.one else Int.zero))]
     (hrx5_nfind NS a) (hrx5_B4_I_ci2 L (hrx5_B4_I_SS ID P) ck1 s (hrx5_B4_I_c2v (hrx5_B4_I_SS ID P) ck1 h1 M))
     (hbytes Tsh (hrx5_B4_I_SS ID P) (l_sst L)).

End Fixed.

(* the harness's model in terms of the stages *)
Lemma hrx5_B4_I_tgt_none1 IB PS M now :
  hrx5_B4_I_c1 IB M = None -> hrx5ci_tgt x25519 aead_dec IB PS M now = None.
Proof. unfold hrx5_B4_I_c1, hrx5ci_tgt. intros Hc. destruct (mi_ok IB); [rewrite Hc|]; reflexivity. Qed.

Lemma hrx5_B4_I_tgt_none2 IB PS M now s key ck1 h1 :
  hrx5_B4_I_c1 IB M = Some (s, key, ck1, h1) -> pk_find PS s = None -> hrx5ci_tgt x25519 aead_dec IB PS M now = None.
Proof.
  unfold hrx5_B4_I_c1, hrx5ci_tgt. intros Hc Hp. destruct (mi_ok IB); [|discriminate]. rewrite Hc, Hp. reflexivity.
Qed.

Lemma hrx5_B4_I_tgt_some IB PS M now s key ck1 h1 a P :
  hrx5_B4_I_c1 IB M = Some (s, key, ck1, h1) -> pk_find PS s = Some (a, P) ->
  hrx5ci_tgt x25519 aead_dec IB PS M now =
  match hrx5_B4_I_c2v (hrx5_B4_I_SS IB P) ck1 h1 M with
  | Some (t, ck2, h2) =>
      if (ts_newer t (hs_ts (p_hs P)) && not_flood (hs_lic (p_hs P)) now)%bool then Some (a, P, t, ck2, h2) else None
  | None => None
  end.
Proof.
  unfold hrx5_B4_I_c1, hrx5ci_tgt, hrx5_B4_I_c2v, hrx5_B4_I_SS. intros Hc Hp. destruct (mi_ok IB); [|discriminate].
  rewrite Hc, Hp. reflexivity.
Qed.

Lemma hrx5_B4_I_c1_some IB M s key ck1 h1 :
  hrx5_B4_I_c1 IB M = Some (s, key, ck1, h1) ->
  mi_ok IB = true /\ m_consume_init1_model x25519 aead_dec IB (im_eph M) (im_encs M) = Some (s, key, ck1, h1).
Proof. unfold hrx5_B4_I_c1. destruct (mi_ok IB); [auto|discriminate]. Qed.

Lemma hrx5_B4_I_c1f_some IB M s key ck1 h1 :
  hrx5_B4_I_c1f IB M = Some (s, key, ck1, h1) ->
  hrx5_fwd (init_bytes M) = true /\ hrx5_B4_I_c1 IB M = Some (s, key, ck1, h1).
Proof. unfold hrx5_B4_I_c1f. destruct (hrx5_fwd (init_bytes M)); [auto|discriminate]. Qed.

(* when stage 1 fails as the code reaches it, the model rejects (or fwd is false) *)
Lemma hrx5_B4_I_c1f_none IB PS M now :
  hrx5_B4_I_c1f IB M = None ->
  (if hrx5_fwd (init_bytes M) then hrx5ci_tgt x25519 aead_dec IB PS M now else None) = None.
Proof.
  unfold hrx5_B4_I_c1f. intros H. destruct (hrx5_fwd (init_bytes M)); [|reflexivity].
  apply hrx5_B4_I_tgt_none1; exact H.
Qed.

End States.
