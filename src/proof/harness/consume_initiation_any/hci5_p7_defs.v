(* law consume_initiation_any, phase P7: the cut of P7 into segments (one call each) and the
   intermediate states (port of v1's hci3_p7_defs.v).
   P7 = s29; (a1; if2)   with s29 = (target = NULL), a1 = (t'96 = ib.ok; if (t'96) {t'29 = m_consume_initiation_1(..);
   t'28 = (bool) t'29} else t'28 = 0), if2 = if (t'28) body else skip;
   body = (p = NULL); ((it = peers); loop); ifp,   ifp = if (p != NULL) x else skip;
   x = e1; (((c2; if14); if15); if17)   (e1: m_precomputed into ss__2, c2: m_consume_initiation_2 (t'23),
   if14: m_ts_newer (t'24), if15: m_not_flood (t'26), if17: target = p). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_cut.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_model.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_spec.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p7_pure.
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* the statements                                                          *)
(* ---------------------------------------------------------------------- *)

Definition hci5_p7_s29 : statement :=
  ltac:(let x := eval cbv delta [hci5_P7] in hci5_P7 in match x with Ssequence ?a _ => exact a end).
Definition hci5_p7_a1 : statement :=
  ltac:(let x := eval cbv delta [hci5_P7] in hci5_P7 in match x with Ssequence _ (Ssequence ?a _) => exact a end).
Definition hci5_p7_body : statement :=
  ltac:(let x := eval cbv delta [hci5_P7] in hci5_P7 in
        match x with Ssequence _ (Ssequence _ (Sifthenelse _ ?b Sskip)) => exact b end).
Definition hci5_p7_if2 : statement := Sifthenelse (Etempvar HC._t'28 tint) hci5_p7_body Sskip.
Definition hci5_p7_sp : statement :=
  ltac:(let x := eval cbv delta [hci5_p7_body] in hci5_p7_body in match x with Ssequence ?a _ => exact a end).
Definition hci5_p7_sit : statement :=
  ltac:(let x := eval cbv delta [hci5_p7_body] in hci5_p7_body in
        match x with Ssequence _ (Ssequence (Ssequence ?a _) _) => exact a end).
Definition hci5_p7_loop : statement :=
  ltac:(let x := eval cbv delta [hci5_p7_body] in hci5_p7_body in
        match x with Ssequence _ (Ssequence (Ssequence _ ?a) _) => exact a end).
Definition hci5_p7_lp : statement := Ssequence hci5_p7_sp (Ssequence hci5_p7_sit hci5_p7_loop).
Definition hci5_p7_x : statement :=
  ltac:(let x := eval cbv delta [hci5_p7_body] in hci5_p7_body in
        match x with Ssequence _ (Ssequence _ (Sifthenelse _ ?b Sskip)) => exact b end).
Definition hci5_p7_ifp : statement :=
  ltac:(let x := eval cbv delta [hci5_p7_body] in hci5_p7_body in
        match x with Ssequence _ (Ssequence _ (Sifthenelse ?c _ Sskip)) => exact (Sifthenelse c hci5_p7_x Sskip) end).
Definition hci5_p7_e1 : statement :=
  ltac:(let x := eval cbv delta [hci5_p7_x] in hci5_p7_x in match x with Ssequence ?a _ => exact a end).
Definition hci5_p7_c2 : statement :=
  ltac:(let x := eval cbv delta [hci5_p7_x] in hci5_p7_x in
        match x with Ssequence _ (Ssequence (Ssequence (Ssequence ?a _) _) _) => exact a end).
Definition hci5_p7_if14 : statement :=
  ltac:(let x := eval cbv delta [hci5_p7_x] in hci5_p7_x in
        match x with Ssequence _ (Ssequence (Ssequence (Ssequence _ ?a) _) _) => exact a end).
Definition hci5_p7_if15 : statement :=
  ltac:(let x := eval cbv delta [hci5_p7_x] in hci5_p7_x in
        match x with Ssequence _ (Ssequence (Ssequence _ ?a) _) => exact a end).
Definition hci5_p7_if17 : statement :=
  ltac:(let x := eval cbv delta [hci5_p7_x] in hci5_p7_x in
        match x with Ssequence _ (Ssequence _ ?a) => exact a end).

Lemma hci5_p7_P7_eq : hci5_P7 = Ssequence hci5_p7_s29 (Ssequence hci5_p7_a1 hci5_p7_if2).
Proof. reflexivity. Qed.
Lemma hci5_p7_body_eq :
  hci5_p7_body = Ssequence hci5_p7_sp (Ssequence (Ssequence hci5_p7_sit hci5_p7_loop) hci5_p7_ifp).
Proof. reflexivity. Qed.
Lemma hci5_p7_x_eq :
  hci5_p7_x = Ssequence hci5_p7_e1 (Ssequence (Ssequence (Ssequence hci5_p7_c2 hci5_p7_if14) hci5_p7_if15) hci5_p7_if17).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* the states                                                              *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* S6's frame with extra props pl, extra temps tl, ci and ss__2 as given *)
Definition hci5_p7_st (gv: globals) (L: hci5_loc) (FR: mpred) (R: hci5_run) (S: shim) (w: list int64)
  (NS: list hnode4) (PS: list (val * share * peer)) (T: tstate) (head na: val) (KE: list kent4) (m: val)
  (M: init_msg) (pl: list Prop) (tl: list localdef) (ci ss2: mpred) : environ -> mpred :=
  PROPx (pl ++ [hci5_run_ok R; hci5_inv x25519 R L NS PS KE T head na; im_ok M;
                0 <= Int64.unsigned (s_boot S) < 2 ^ 62])
  (LOCALx (tl ++ [temp HC._kes (hci5_khead KE); temp HC._msg m; temp HC._now (Vlong (s_boot S));
                  temp HC._head0 (hd nullval (t_L T));
                  temp HC._ret (peer_result (cin_res x25519 aead_dec (hci5_DB x25519 R L) PS M S))] ++
           hci5_lvars gv L)
  (SEPx (hci5_world x25519 R L NS (hnodes_snapped4 T NS PS) T head ++
         [peers_rep (peers_after PS (cin_res x25519 aead_dec (hci5_DB x25519 R L) PS M S));
          kents_rep W (hci5_khead KE) (map (kent_snapped T) KE);
          @data_at CKS Tsh t_devsnap (devsnap_val (hci5_DB x25519 R L) head) (l_ds L);
          @data_at CKS Tsh t_shimsnap (shimsnap_val S w) (l_ss L);
          hbytes Tsh (init_bytes M) (l_img L); hci5_tok t_init m; init_rep Ews m M; ci] ++
         hci5_globs gv S w FR ++
         [hout Tsh 32 (l_pub L); hout Tsh 12 (l_ts L); hout Tsh 148 (l_imga L);
          @data_at_ HCS Tsh t_minit (l_mi L); hout Tsh 32 (l_eraw L); hout Tsh 32 (l_ss1 L); ss2]))).

(* stage 1 of the harness's model, as the code reaches it *)
Definition hci5_p7_c1 (IB: mident) (M: init_msg) : option (list byte * list byte * list byte * list byte) :=
  if mi_ok IB then m_consume_init1_model x25519 aead_dec IB (im_eph M) (im_encs M) else None.

Definition hci5_p7_ci1 (L: hci5_loc) (c: option (list byte * list byte * list byte * list byte)) : mpred :=
  match c with
  | Some (s, key, ck, h) => @data_at HCS Tsh t_mcinit (mcinit_val ck h (bytes key) (bytes s) (Zrepeat Vundef 12)) (l_ci L)
  | None => @data_at_ HCS Tsh t_mcinit (l_ci L)
  end.

Definition hci5_p7_ok1 (c: option (list byte * list byte * list byte * list byte)) : bool :=
  match c with Some _ => true | None => false end.

(* after a1 *)
Definition hci5_p7_Q1 gv L FR R S w NS PS T head na KE m M : environ -> mpred :=
  hci5_p7_st gv L FR R S w NS PS T head na KE m M []
    [temp HC._t'28 (Vint (if hci5_p7_ok1 (hci5_p7_c1 (hci5_IB x25519 R) M) then Int.one else Int.zero));
     temp HC._target nullval]
    (hci5_p7_ci1 L (hci5_p7_c1 (hci5_IB x25519 R) M)) (hout Tsh 32 (l_ss2 L)).

(* body's start: stage 1 succeeded with (s, key, ck1, h1) *)
Definition hci5_p7_Q2 gv L FR R S w NS PS T head na KE m M s key ck1 h1 : environ -> mpred :=
  hci5_p7_st gv L FR R S w NS PS T head na KE m M [] [temp HC._target nullval]
    (hci5_p7_ci1 L (Some (s, key, ck1, h1))) (hout Tsh 32 (l_ss2 L)).

(* after the first-match loop *)
Definition hci5_p7_Qb gv L FR R S w NS PS T head na KE m M s key ck1 h1 : environ -> mpred :=
  hci5_p7_st gv L FR R S w NS PS T head na KE m M []
    [temp HC._p (hci5_p7_fmv (hci5_p7_fm (hnodes_snapped4 T NS PS)
                    (peers_after PS (cin_res x25519 aead_dec (hci5_DB x25519 R L) PS M S)) s));
     temp HC._target nullval]
    (hci5_p7_ci1 L (Some (s, key, ck1, h1))) (hout Tsh 32 (l_ss2 L)).

(* x's start: the loop found the node of peer a (pk_find PS s = Some (a, P)) *)
Definition hci5_p7_Qf gv L FR R S w NS PS T head na KE m M s key ck1 h1 a : environ -> mpred :=
  hci5_p7_st gv L FR R S w NS PS T head na KE m M [] [temp HC._p (hci5_nfind NS a); temp HC._target nullval]
    (hci5_p7_ci1 L (Some (s, key, ck1, h1))) (hout Tsh 32 (l_ss2 L)).

Definition hci5_p7_SS (IB: mident) (P: peer) : list byte := m_precomputed_model x25519 IB (hs_rstatic (p_hs P)).

(* after e1 (m_precomputed) *)
Definition hci5_p7_Q5 gv L FR R S w NS PS T head na KE m M s key ck1 h1 a P : environ -> mpred :=
  hci5_p7_st gv L FR R S w NS PS T head na KE m M [] [temp HC._p (hci5_nfind NS a); temp HC._target nullval]
    (hci5_p7_ci1 L (Some (s, key, ck1, h1))) (hbytes Tsh (hci5_p7_SS (hci5_IB x25519 R) P) (l_ss2 L)).

(* stage 2 *)
Definition hci5_p7_c2v (SS ck1 h1: list byte) (M: init_msg) : option (list byte * list byte * list byte) :=
  m_consume_init2_model aead_dec SS ck1 h1 (im_enct M).

Definition hci5_p7_ci2 (L: hci5_loc) (SS ck1 s: list byte) (c: option (list byte * list byte * list byte)) : mpred :=
  match c with
  | Some (t, ck, h) => @data_at HCS Tsh t_mcinit (mcinit_val ck h (bytes (kdf2 ck1 SS)) (bytes s) (bytes t)) (l_ci L)
  | None => @data_at_ HCS Tsh t_mcinit (l_ci L)
  end.

(* after c2 *)
Definition hci5_p7_Q6 gv L FR R S w NS PS T head na KE m M s (ck1 h1: list byte) a P : environ -> mpred :=
  let SS := hci5_p7_SS (hci5_IB x25519 R) P in
  let c := hci5_p7_c2v SS ck1 h1 M in
  hci5_p7_st gv L FR R S w NS PS T head na KE m M []
    [temp HC._t'23 (Vint (match c with Some _ => Int.one | None => Int.zero end));
     temp HC._p (hci5_nfind NS a); temp HC._target nullval]
    (hci5_p7_ci2 L SS ck1 s c) (hbytes Tsh SS (l_ss2 L)).

Definition hci5_p7_b15 (c: option (list byte * list byte * list byte)) (P: peer) : bool :=
  match c with Some (t, _, _) => ts_newer t (hs_ts (p_hs P)) | None => false end.

(* after if14 (m_ts_newer) *)
Definition hci5_p7_Q7 gv L FR R S w NS PS T head na KE m M s (ck1 h1: list byte) a P : environ -> mpred :=
  let SS := hci5_p7_SS (hci5_IB x25519 R) P in
  let c := hci5_p7_c2v SS ck1 h1 M in
  hci5_p7_st gv L FR R S w NS PS T head na KE m M []
    [temp HC._t'24 (Vint (if hci5_p7_b15 c P then Int.one else Int.zero));
     temp HC._p (hci5_nfind NS a); temp HC._target nullval]
    (hci5_p7_ci2 L SS ck1 s c) (hbytes Tsh SS (l_ss2 L)).

(* after if15 (m_not_flood) *)
Definition hci5_p7_Q8 gv L FR R S w NS PS T head na KE m M s (ck1 h1: list byte) a P : environ -> mpred :=
  let SS := hci5_p7_SS (hci5_IB x25519 R) P in
  let c := hci5_p7_c2v SS ck1 h1 M in
  hci5_p7_st gv L FR R S w NS PS T head na KE m M []
    [temp HC._t'26 (Vint (if (hci5_p7_b15 c P && not_flood (hs_lic (p_hs P)) (s_boot S))%bool
                          then Int.one else Int.zero));
     temp HC._p (hci5_nfind NS a); temp HC._target nullval]
    (hci5_p7_ci2 L SS ck1 s c) (hbytes Tsh SS (l_ss2 L)).

(* the harness's model in terms of the stages *)
Lemma hci5_p7_tgt_none1 IB PS M now :
  hci5_p7_c1 IB M = None -> hci5_tgt x25519 aead_dec IB PS M now = None.
Proof. unfold hci5_p7_c1, hci5_tgt. intros Hc. destruct (mi_ok IB); [rewrite Hc|]; reflexivity. Qed.

Lemma hci5_p7_tgt_none2 IB PS M now s key ck1 h1 :
  hci5_p7_c1 IB M = Some (s, key, ck1, h1) -> pk_find PS s = None -> hci5_tgt x25519 aead_dec IB PS M now = None.
Proof.
  unfold hci5_p7_c1, hci5_tgt. intros Hc Hp. destruct (mi_ok IB); [|discriminate]. rewrite Hc, Hp. reflexivity.
Qed.

Lemma hci5_p7_tgt_some IB PS M now s key ck1 h1 a P :
  hci5_p7_c1 IB M = Some (s, key, ck1, h1) -> pk_find PS s = Some (a, P) ->
  hci5_tgt x25519 aead_dec IB PS M now =
  match hci5_p7_c2v (hci5_p7_SS IB P) ck1 h1 M with
  | Some (t, ck2, h2) =>
      if (ts_newer t (hs_ts (p_hs P)) && not_flood (hs_lic (p_hs P)) now)%bool then Some (a, P, t, ck2, h2) else None
  | None => None
  end.
Proof.
  unfold hci5_p7_c1, hci5_tgt, hci5_p7_c2v, hci5_p7_SS. intros Hc Hp. destruct (mi_ok IB); [|discriminate].
  rewrite Hc, Hp. reflexivity.
Qed.

Lemma hci5_p7_c1_some IB M s key ck1 h1 :
  hci5_p7_c1 IB M = Some (s, key, ck1, h1) ->
  mi_ok IB = true /\ m_consume_init1_model x25519 aead_dec IB (im_eph M) (im_encs M) = Some (s, key, ck1, h1).
Proof. unfold hci5_p7_c1. destruct (mi_ok IB); [auto|discriminate]. Qed.

End States.
