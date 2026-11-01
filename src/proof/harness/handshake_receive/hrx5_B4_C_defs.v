(* law handshake_receive, phase B4, segment C: the cut of the
   model block hrx5_B4_M for a cookie-reply object OCookie M into segments, and the intermediate states.
   Port of cookie_reply's P11 (hcy5_p11_defs.v). 'B4 segment C'.
   hrx5_B4_M = a1; if (t'97) _ else (a2; if (t'94) _ else (a3; if (t'92) body else skip))
     a1 / a2 / a3: the conditions of the three kinds (t'97 = 0, t'94 = 0 for kind 3; t'92 = fwd),
     body = sW; (sN; sD)
     sW = e = itd.head; for (; e != NULL && e->index != mc->receiver_index; e = e->next);
     sN = if (e != NULL) t'89 = e->type & (1 | 2) else t'89 = 0; if (t'89) for (nd = peers; nd; nd = nd->next)
          if (nd->p == e->peer && target == NULL) target = nd;
     sD = if (target != NULL) t'90 = !have_sent_mac1 || !xchacha20poly1305_decrypt(pt, ...) else t'90 = 0;
          if (t'90) target = NULL;
   States: hrx5_B4_C_st = hrx5_B4_Q (hrx5_B4_defs.v) for o = OCookie M with fwd = true (PROP), extra temps tl in
   front, target tg and the scratch pt as ptR. *)
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

(* ---------------------------------------------------------------------- *)
(* the statements                                                          *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_B4_C_a1 : statement :=
  ltac:(let x := eval cbv delta [hrx5_B4_M] in hrx5_B4_M in match x with Ssequence ?a _ => exact a end).
Definition hrx5_B4_C_c97 : expr :=
  ltac:(let x := eval cbv delta [hrx5_B4_M] in hrx5_B4_M in
        match x with Ssequence _ (Sifthenelse ?a _ _) => exact a end).
Definition hrx5_B4_C_bI : statement :=
  ltac:(let x := eval cbv delta [hrx5_B4_M] in hrx5_B4_M in
        match x with Ssequence _ (Sifthenelse _ ?a _) => exact a end).
Definition hrx5_B4_C_a2 : statement :=
  ltac:(let x := eval cbv delta [hrx5_B4_M] in hrx5_B4_M in
        match x with Ssequence _ (Sifthenelse _ _ (Ssequence ?a _)) => exact a end).
Definition hrx5_B4_C_c94 : expr :=
  ltac:(let x := eval cbv delta [hrx5_B4_M] in hrx5_B4_M in
        match x with Ssequence _ (Sifthenelse _ _ (Ssequence _ (Sifthenelse ?a _ _))) => exact a end).
Definition hrx5_B4_C_bR : statement :=
  ltac:(let x := eval cbv delta [hrx5_B4_M] in hrx5_B4_M in
        match x with Ssequence _ (Sifthenelse _ _ (Ssequence _ (Sifthenelse _ ?a _))) => exact a end).
Definition hrx5_B4_C_a3 : statement :=
  ltac:(let x := eval cbv delta [hrx5_B4_M] in hrx5_B4_M in
        match x with Ssequence _ (Sifthenelse _ _ (Ssequence _ (Sifthenelse _ _ (Ssequence ?a _)))) => exact a end).
Definition hrx5_B4_C_c92 : expr :=
  ltac:(let x := eval cbv delta [hrx5_B4_M] in hrx5_B4_M in
        match x with Ssequence _ (Sifthenelse _ _ (Ssequence _ (Sifthenelse _ _
          (Ssequence _ (Sifthenelse ?a _ Sskip))))) => exact a end).
Definition hrx5_B4_C_sW : statement :=
  ltac:(let x := eval cbv delta [hrx5_B4_M] in hrx5_B4_M in
        match x with Ssequence _ (Sifthenelse _ _ (Ssequence _ (Sifthenelse _ _
          (Ssequence _ (Sifthenelse _ (Ssequence ?a (Ssequence _ _)) Sskip))))) => exact a end).
Definition hrx5_B4_C_sN : statement :=
  ltac:(let x := eval cbv delta [hrx5_B4_M] in hrx5_B4_M in
        match x with Ssequence _ (Sifthenelse _ _ (Ssequence _ (Sifthenelse _ _
          (Ssequence _ (Sifthenelse _ (Ssequence _ (Ssequence ?a _)) Sskip))))) => exact a end).
Definition hrx5_B4_C_sD : statement :=
  ltac:(let x := eval cbv delta [hrx5_B4_M] in hrx5_B4_M in
        match x with Ssequence _ (Sifthenelse _ _ (Ssequence _ (Sifthenelse _ _
          (Ssequence _ (Sifthenelse _ (Ssequence _ (Ssequence _ ?a)) Sskip))))) => exact a end).

Lemma hrx5_B4_C_M_eq : hrx5_B4_M =
  Ssequence hrx5_B4_C_a1 (Sifthenelse hrx5_B4_C_c97 hrx5_B4_C_bI
    (Ssequence hrx5_B4_C_a2 (Sifthenelse hrx5_B4_C_c94 hrx5_B4_C_bR
      (Ssequence hrx5_B4_C_a3 (Sifthenelse hrx5_B4_C_c92
        (Ssequence hrx5_B4_C_sW (Ssequence hrx5_B4_C_sN hrx5_B4_C_sD)) Sskip))))).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* the models                                                              *)
(* ---------------------------------------------------------------------- *)

(* the harness's walk of D's table: the first entry of the list with that index, or NULL *)
Definition hrx5_B4_C_ewalk (T: tstate) (idx: int) : val :=
  match t_find_index T (t_L T) idx with Some (a, _) => a | None => nullval end.

(* the harness's target before the decryption: the first node of the peer of the entry the kernel's lookup finds
   (index idx, type handshake or keypair), or NULL *)
Definition hrx5_B4_C_t0 (NS: list hnode4) (T: tstate) (M: cookie_msg) : val :=
  match t_lookup T (Int.or IDX_HANDSHAKE IDX_KEYPAIR) (cm_receiver M) with
  | Some (_, E) => hrx5_nfind NS (e_peer E)
  | None => nullval
  end.

(* ---------------------------------------------------------------------- *)
(* the states                                                              *)
(* ---------------------------------------------------------------------- *)

(* the scratch locals with pt as given *)
Definition hrx5_B4_C_scr (L: hrx5_loc) (ptR: mpred) : list mpred :=
  [hout Tsh 32 (l_pub L); @data_at_ CKS Tsh t_devsnap (l_ds L); @data_at_ CKS Tsh t_shimsnap (l_ss L);
   @data_at_ CKS Tsh t_skbsnap (l_sks L); @data_at_ HCS Tsh t_mcinit (l_ci L); @data_at_ HCS Tsh t_mstate (l_st L);
   hout Tsh 32 (l_secret L); hout Tsh 16 (l_c L); hout Tsh 16 (l_mac L); ptR;
   @data_at_ Noise.CS Tsh t_init (l_t L); @data_at_ Noise.CS Tsh t_resp (l_t1 L); hout Tsh 16 (l_ck L);
   hout Tsh 32 (l_sst L); @data_at_ HCS Tsh t_mstate (l_before L)].

Section States.
Variable x25519: list byte -> list byte -> list byte.

(* hrx5_B4_Q for o = OCookie M with fwd true, extra temps tl (in front), target = tg, pt as ptR *)
Definition hrx5_B4_C_st (gv: globals) (L: hrx5_loc) (FR: mpred) (R: hrx5_run) (sec: list byte) (birth: int64)
  (S: shim) (w: list int64) (NS: list hnode4) (PS: list (val * share * peer)) (T: tstate) (head nk: val)
  (KE: list kent4) (st i: Z) (kc lul: int64) (q: int) (proto: Z) (ip4 ip6 port: list byte) (M: cookie_msg)
  (dp img: val) (tl: list localdef) (tg: val) (ptR: mpred) : environ -> mpred :=
  PROPx [hrx5_base_ok R sec birth S; hrx5_inv x25519 R L NS PS KE T head nk; 0 <= st <= Int64.max_unsigned;
         0 <= i < st; obj_ok (OCookie M); malloc_compatible (Zlength (obj_bytes (OCookie M))) dp;
         hrx5_fwd (obj_bytes (OCookie M)) = true]
  (LOCALx (tl ++ hrx5_ltemps nk KE st i S lul ++ hrx5_ptrs dp (OCookie M) ++
           [temp HM._img img; temp HM._len (Vlong (Int64.repr (Zlength (obj_bytes (OCookie M)))));
            temp HM._kind (Vint (Int.repr (obj_kind (OCookie M))));
            temp HM._tw (Vint (if Z.leb 4 (Zlength (obj_bytes (OCookie M))) then hrx5_tw (obj_bytes (OCookie M))
                               else Int.zero));
            temp HM._fwd (Vint (if hrx5_fwd (obj_bytes (OCookie M)) then Int.one else Int.zero));
            temp HM._acc_init (Vint Int.zero); temp HM._acc_resp (Vint Int.zero); temp HM._target tg] ++
           hrx5_lvars gv L)
  (SEPx (hrx5_wcore x25519 R L sec birth T head PS ++
         hrx5_rest x25519 R L (hnodes_snapped4 T NS PS) (map (kent_snapped T) KE) ++
         hrx5_globs gv S w kc FR ++
         [lul_rep gv lul; @data_at_ HRX Ews t_rxlog (gv HM._wg_shim_rx); qlen_rep gv q;
          skb_rep Tsh (l_skb L) (hrx5_skb dp (OCookie M) proto ip4 ip6 port); obj_rep dp (OCookie M);
          img_rep img (obj_bytes (OCookie M))] ++
         hrx5_B4_C_scr L ptR))).

End States.

(* ---------------------------------------------------------------------- *)
(* the segments' statements                                                *)
(* ---------------------------------------------------------------------- *)

(* W: the walk of D's table *)
Definition hrx5_B4_C_W_stmt : Prop :=
  forall {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR
    R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img,
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B4_C_st x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img
       [] nullval (hout Tsh 16 (l_pt L)))
    hrx5_B4_C_sW
    (overridePost
       (hrx5_B4_C_st x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img
          [temp HM._e (hrx5_B4_C_ewalk T (cm_receiver M))] nullval (hout Tsh 16 (l_pt L)))
       (hrx5_RB x25519 gv L FR)).

(* N: the node search *)
Definition hrx5_B4_C_N_stmt : Prop :=
  forall {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR
    R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img,
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B4_C_st x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img
       [temp HM._e (hrx5_B4_C_ewalk T (cm_receiver M))] nullval (hout Tsh 16 (l_pt L)))
    hrx5_B4_C_sN
    (overridePost
       (hrx5_B4_C_st x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img
          [] (hrx5_B4_C_t0 NS T M) (hout Tsh 16 (l_pt L)))
       (hrx5_RB x25519 gv L FR)).

(* D: the decryption, for a non-NULL target: the node N (in the snapped list) of the peer P of the entry E *)
Definition hrx5_B4_C_D_stmt : Prop :=
  forall {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR
    R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img
    a E P NS1 N NS2,
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  t_lookup T (Int.or IDX_HANDSHAKE IDX_KEYPAIR) (cm_receiver M) = Some (a, E) ->
  sfind PS (e_peer E) = Some (Ews, P) ->
  hnodes_snapped4 T NS PS = NS1 ++ N :: NS2 ->
  hn_addr N = hrx5_nfind NS (e_peer E) -> hn_rest N = prsnap_val P ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B4_C_st x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img
       [] (hn_addr N) (hout Tsh 16 (l_pt L)))
    hrx5_B4_C_sD
    (overridePost (hrx5_S4 x25519 aead_dec xaead_dec gv L FR) (hrx5_RB x25519 gv L FR)).

(* G: the agreement of the harness's target with the model (pure) *)
Definition hrx5_B4_C_G_stmt : Prop :=
  forall x25519 (xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte))
    R L NS PS KE T head nk M,
  hrx5_inv x25519 R L NS PS KE T head nk -> Forall (fun N => isptr (hn_addr N)) NS ->
  (hrx5_B4_C_t0 NS T M = nullval -> hrx5ck_tgt xaead_dec T PS M = None) /\
  (hrx5_B4_C_t0 NS T M <> nullval ->
   exists a E P NS1 N NS2,
     t_lookup T (Int.or IDX_HANDSHAKE IDX_KEYPAIR) (cm_receiver M) = Some (a, E) /\
     sfind PS (e_peer E) = Some (Ews, P) /\
     hnodes_snapped4 T NS PS = NS1 ++ N :: NS2 /\
     hn_addr N = hrx5_nfind NS (e_peer E) /\ hn_rest N = prsnap_val P).
