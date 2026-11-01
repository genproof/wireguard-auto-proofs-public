(* law handshake_receive: main's phase B8 = body statement 41: the four cases of CHECKs.
   From hrx5_S6 to hrx5_S8 (hrx5_defs.v; the cut: hrx5_cut.v). *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_I.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R2.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_C.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_E.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* pure helpers                                                            *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_b8_path_range W q s msg d : 0 <= hrx5_path W q s msg d <= 2.
Proof.
  unfold hrx5_path.
  destruct (hrx5_fwd msg); [| lia].
  destruct (Int.eq _ _); [lia |].
  destruct (rx_consumes _ _); [lia |]. destruct (rx_needs_cookie _ _); lia.
Qed.

Lemma hrx5_b8_nfind_in NS a : hrx5_nfind NS a = nullval \/ In (hrx5_nfind NS a) (map hn_addr NS).
Proof.
  induction NS as [|N NS IH]; simpl; [auto |].
  destruct (EqDec_val (hn_p N) a); [auto |]. destruct IH as [-> | H]; auto.
Qed.

Lemma hrx5_b8_snapped_addr T NS PS :
  length NS = length PS -> map hn_addr (hnodes_snapped4 T NS PS) = map hn_addr NS.
Proof.
  revert PS; induction NS as [|N NS IH]; intros [|[[p sh] P] PS] HL; simpl in *; try discriminate; auto.
  f_equal. apply IH. lia.
Qed.

Lemma hrx5_b8_fold_valid (l: list mpred) X p :
  In X l -> X |-- valid_pointer p -> fold_right_sepcon l |-- valid_pointer p.
Proof.
  induction l as [|a l IH]; simpl; intros Hin HX; [contradiction |].
  destruct Hin as [<- | Hin].
  - apply sepcon_valid_pointer1; auto.
  - apply sepcon_valid_pointer2; auto.
Qed.

Lemma hrx5_b8_hnodes_valid CSw h NS a :
  In a (map hn_addr NS) -> hnodes_rep4 CSw h NS |-- valid_pointer a.
Proof.
  revert h; induction NS as [|N NS IH]; intros h Ha; simpl in Ha; [contradiction |].
  simpl hnodes_rep4. Intros nx. destruct Ha as [<- | Ha].
  - subst h. sep_apply (@data_at_valid_ptr CKS Ews t_hnode4); [auto |].
    apply sepcon_valid_pointer1; apply derives_refl.
  - sep_apply (IH nx Ha). apply sepcon_valid_pointer1; apply derives_refl.
Qed.

(* closing the value of a condition temp *)
Ltac hrx5_b8_val :=
  repeat match goal with
  | |- context [zeq ?a ?b] => destruct (zeq a b)
  | |- context [?a =? ?b] => destruct (Z.eqb_spec a b)
  | H: context [?a =? ?b] |- _ => destruct (Z.eqb_spec a b)
  end; cbn [andb negb] in *; try lia; try (exfalso; congruence); try reflexivity;
  try match goal with Hx: ?a <> ?b |- _ => exfalso; apply Hx; reflexivity end;
  try match goal with Hx: @eq int ?a ?b |- _ =>
    exfalso; apply (f_equal Int.unsigned) in Hx; vm_compute in Hx; discriminate end;
  match goal with
  | Hx: ?a = 0 \/ ?a = 1 |- context [Int.repr ?a] => destruct Hx as [-> | ->]; (reflexivity || lia)
  end.

(* one `if (c) t = e1; else t = e2;` of the condition evaluations: the post adds temp t = Vint v *)
Ltac hrx5_b8_cond tid v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?S))) _ _ =>
    let PP := fresh "PP" in
    pose (PP := PROPx P (LOCALx (temp tid (Vint v) :: Q) (SEPx S)));
    forward_if PP;
    [ forward; match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with PP end; unfold PP; entailer!;
      solve [hrx5_b8_val]
    | forward; match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with PP end; unfold PP; entailer!;
      solve [hrx5_b8_val]
    | unfold PP; clear PP ]
  end.

(* apply a branch lemma K (instantiated but for its case hypothesis Hc) to the current goal *)
Ltac hrx5_b8_branch K Hc :=
  match type of K with _ -> semax ?DL ?Q _ _ =>
    eapply semax_pre with (P' := Q);
    [ | match goal with D := _ : tycontext, PO := _ : ret_assert |- _ =>
          unfold PO, abbreviate; change D with DL; exact (K Hc) end ] end.

Section B8.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_b8_acc R NS PS T o now tg ai ar :
  hrx5_acc_ok x25519 aead_dec xaead_dec R NS PS T o now tg ai ar ->
  (ai = 0 \/ ai = 1) /\ (ar = 0 \/ ar = 1) /\ (obj_kind o = 3 -> tg = nullval \/ In tg (map hn_addr NS)).
Proof.
  unfold hrx5_acc_ok. destruct o as [b|M|M|M]; cbn [obj_kind].
  - intros (-> & -> & ->). (split; [lia | split; [lia | intros; lia]]).
  - intros [-> H]. destruct (hrx5_fwd _).
    + destruct (hrx5ci_tgt _ _ _ _ _ _) as [[[[[? ?] ?] ?] ?]|]; destruct H as [-> _]; (split; [lia | split; [lia | intros; lia]]).
    + destruct H as [-> _]; (split; [lia | split; [lia | intros; lia]]).
  - intros [-> H]. destruct (hrx5_fwd _).
    + destruct (hrx5cr_tgt _ _ _ _ _ _) as [[[[? ?] ?] ?]|]; destruct H as [-> _]; (split; [lia | split; [lia | intros; lia]]).
    + destruct H as [-> _]; (split; [lia | split; [lia | intros; lia]]).
  - intros (-> & -> & ->). split; [lia | split; [lia |]]. intros _.
    destruct (hrx5_fwd _); [| auto].
    destruct (hrx5ck_tgt _ _ _ _) as [[[a ?] ?]|]; [apply hrx5_b8_nfind_in | auto].
Qed.

(* hrx5_S6's body with its variables fixed: hrx5_B8_Q plus `itable_wf T` (its last PROP, defs 6274f9a) *)
Definition hrx5_B8_Q6 (gv: globals) (L: hrx5_loc) (FR: mpred)
  (R: hrx5_run) (sec: list byte) (birth: int64) (S: shim) (w: list int64) (NS: list hnode4)
  (PS: list (val * share * peer)) (T: tstate) (head nk: val) (KE: list kent4) (st i: Z) (kc lul: int64) (q: int)
  (proto: Z) (ip4 ip6 port: list byte) (o: hrx5_obj) (dp img tg: val) (ai ar: Z) (d: rxdraw)
  : environ -> mpred :=
  let W0 := hrx5_W0 (hrx5_DL x25519 R L sec birth) T PS S w kc lul in
  let s := hrx5_skb dp o proto ip4 ip6 port in
  let W1 := rx_model x25519 aead_dec xaead_enc xaead_dec W0 q (l_skb L) s (obj_bytes o) d in
  PROPx [hrx5_base_ok R sec birth S; hrx5_inv x25519 R L NS PS KE T head nk; 0 <= st <= Int64.max_unsigned;
         0 <= i < st; obj_ok o; malloc_compatible (Zlength (obj_bytes o)) dp;
         hrx5_acc_ok x25519 aead_dec xaead_dec R NS PS T o (s_boot S) tg ai ar; rxdraw_ok T d; itable_wf T]
  (LOCALx ([temp HM._nk nk; temp HM._kes (hrx5_khead KE); temp HM._steps (Vlong (Int64.repr st));
            temp HM._i (Vlong (Int64.repr i)); temp HM._now (Vlong (s_boot S));
            temp HM._m_lul (Vlong (rw_lul W1))] ++ hrx5_ptrs dp o ++
           [temp HM._img img; temp HM._len (Vlong (Int64.repr (Zlength (obj_bytes o))));
            temp HM._kind (Vint (Int.repr (obj_kind o)));
            temp HM._acc_init (Vint (Int.repr ai)); temp HM._acc_resp (Vint (Int.repr ar)); temp HM._target tg;
            temp HM._head0 (hd nullval (t_L T));
            temp HM._path (Vint (Int.repr (hrx5_path W0 q s (obj_bytes o) d)))] ++
           hrx5_lvars gv L)
  (SEPx ([rxw_rep W gv Tsh (l_wd L) head W1] ++
         hrx5_rest x25519 R L (hnodes_snapped4 T NS PS) (map (kent_snapped T) KE) ++
         hrx5_cglobs gv FR ++
         [qlen_rep gv q; skb_rep Tsh (l_skb L) s; obj_rep dp o; img_rep img (obj_bytes o)] ++
         hrx5_scr5 x25519 aead_dec xaead_dec R L T PS o (s_boot S) (devsnap_val (rw_D W1) head) S w s
           (hout Tsh 32 (l_secret L))))).

Lemma hrx5_B8_S6_eq gv L FR :
  hrx5_S6 x25519 aead_dec xaead_enc xaead_dec gv L FR =
  EX R: hrx5_run, EX sec: list byte, EX birth: int64, EX S: shim, EX w: list int64, EX NS: list hnode4,
  EX PS: list (val * share * peer), EX T: tstate, EX head: val, EX nk: val, EX KE: list kent4, EX st: Z,
  EX i: Z, EX kc: int64, EX lul: int64, EX q: int, EX proto: Z, EX ip4: list byte, EX ip6: list byte,
  EX port: list byte, EX o: hrx5_obj, EX dp: val, EX img: val, EX tg: val, EX ai: Z, EX ar: Z, EX d: rxdraw,
  hrx5_B8_Q6 gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d.
Proof. reflexivity. Qed.

Lemma hrx5_B8_ok {Espec: OracleKind} gv L FR :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_S6 x25519 aead_dec xaead_enc xaead_dec gv L FR) hrx5_B8
    (overridePost (hrx5_S8 x25519 gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HY.
  rewrite hrx5_B8_S6_eq, hrx5_B8_eq.
  Intros R sec birth S w NS PS T. Intros head nk KE st i kc lul q. Intros proto ip4 ip6 port o dp img tg.
  Intros ai ar d.
  pose proof (hrx5_B8_I_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T
    head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d HY) as KI.
  pose proof (hrx5_B8_R2_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T
    head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d HY) as KR.
  pose proof (hrx5_B8_C_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T
    head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d HY) as KC.
  pose proof (hrx5_B8_E_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T
    head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d HY) as KE'.
  unfold hrx5_B8_Q6.
  match goal with |- semax _ ?P _ _ => let P' := eval cbv zeta in P in change P with P' end.
  set (pth := hrx5_path _ _ _ _ _).
  set (W1 := rx_model _ _ _ _ _ _ _ _ _ _).
  Intros.
  pose proof (hrx5_b8_path_range (hrx5_W0 (hrx5_DL x25519 R L sec birth) T PS S w kc lul) q
    (hrx5_skb dp o proto ip4 ip6 port) (obj_bytes o) d) as Hpr. fold pth in Hpr.
  match goal with H: hrx5_acc_ok _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof (hrx5_b8_acc _ _ _ _ _ _ _ _ _ H) as (Hai & Har & Htg) end.
  unfold hrx5_Delta, hrx5_ptrs, hrx5_lvars; cbn [app].
  abbreviate_semax.
  assert (Hk: 0 <= obj_kind o <= 3) by (destruct o; cbn [obj_kind]; lia).
  unfold hrx5_B8_C1.
  hrx5_b8_cond HM._t'232 (if andb (pth =? 1) (obj_kind o =? 1) then Int.one else Int.zero).
  hrx5_b8_cond HM._t'233 (if andb (andb (pth =? 1) (obj_kind o =? 1)) (ai =? 1) then Int.one else Int.zero).
  forward_if.
  - assert (Hc: hrx5_B8_isI o pth ai ar tg).
    { unfold hrx5_B8_isI.
      match goal with Hx: (if _ then _ else _) <> Int.zero |- _ => revert Hx end.
      destruct (Z.eqb_spec pth 1), (Z.eqb_spec (obj_kind o) 1), (Z.eqb_spec ai 1);
        cbv beta iota delta [andb]; intros Hx; auto; contradiction Hx; reflexivity. }
    hrx5_b8_branch KI Hc.
    unfold hrx5_B8_Q; cbv zeta; unfold hrx5_ptrs, hrx5_lvars; cbn [app]; entailer!; apply derives_refl.
  - assert (Hn: ~ hrx5_B8_isI o pth ai ar tg).
    { unfold hrx5_B8_isI.
      match goal with Hx: (if _ then _ else _) = Int.zero |- _ => revert Hx end.
      destruct (Z.eqb_spec pth 1), (Z.eqb_spec (obj_kind o) 1), (Z.eqb_spec ai 1);
        cbv beta iota delta [andb]; intros Hx; try tauto;
        apply (f_equal Int.unsigned) in Hx; vm_compute in Hx; discriminate. }
    unfold hrx5_B8_C2.
    hrx5_b8_cond HM._t'230 (if andb (pth =? 1) (obj_kind o =? 2) then Int.one else Int.zero).
    hrx5_b8_cond HM._t'231 (if andb (andb (pth =? 1) (obj_kind o =? 2)) (ar =? 1) then Int.one else Int.zero).
    forward_if.
    + assert (Hc: hrx5_B8_isR o pth ai ar tg).
      { unfold hrx5_B8_isR.
        match goal with Hx: (if _ then _ else _) <> Int.zero |- _ => revert Hx end.
        destruct (Z.eqb_spec pth 1), (Z.eqb_spec (obj_kind o) 2), (Z.eqb_spec ar 1);
          cbv beta iota delta [andb]; intros Hx; auto; contradiction Hx; reflexivity. }
      match goal with Hw: itable_wf T |- _ => pose proof (fun Hc' => KR Hc' Hw) as KR2 end.
      hrx5_b8_branch KR2 Hc.
      unfold hrx5_B8_Q; cbv zeta; unfold hrx5_ptrs, hrx5_lvars; cbn [app]; entailer!; apply derives_refl.
    + assert (Hn2: ~ hrx5_B8_isR o pth ai ar tg).
      { unfold hrx5_B8_isR.
        match goal with Hx: (if _ then _ else _) = Int.zero |- _ => revert Hx end.
        destruct (Z.eqb_spec pth 1), (Z.eqb_spec (obj_kind o) 2), (Z.eqb_spec ar 1);
          cbv beta iota delta [andb]; intros Hx; try tauto;
          apply (f_equal Int.unsigned) in Hx; vm_compute in Hx; discriminate. }
      unfold hrx5_B8_C3.
      hrx5_b8_cond HM._t'228 (if andb (pth =? 1) (obj_kind o =? 3) then Int.one else Int.zero).
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?S))) _ _ =>
        pose (PP := PROPx P (LOCALx (temp HM._t'229 (Vint (if andb (andb (pth =? 1) (obj_kind o =? 3))
                      (if Val.eq tg nullval then false else true) then Int.one else Int.zero)) :: Q) (SEPx S))) end.
      forward_if PP.
      { assert (Hc3: pth = 1 /\ obj_kind o = 3).
        { match goal with Hx: (if _ then _ else _) <> Int.zero |- _ => revert Hx end.
          destruct (Z.eqb_spec pth 1), (Z.eqb_spec (obj_kind o) 3);
            cbv beta iota delta [andb]; intros Hx; auto; contradiction Hx; reflexivity. }
        forward.
        { entailer!. apply denote_tc_test_eq_split; [| apply valid_pointer_null].
          destruct (Htg (proj2 Hc3)) as [-> | Hin]; [apply valid_pointer_null |].
          apply sepcon_valid_pointer2.
          assert (HL: length NS = length PS).
          { destruct H0 as (_ & _ & _ & _ & Hnp & _). unfold hnodes_peers4 in Hnp.
            apply (f_equal (@length val)) in Hnp. rewrite !map_length in Hnp. exact Hnp. }
          apply (hrx5_b8_fold_valid _ (hnodes_rep4 W (hrx5_head (hnodes_snapped4 T NS PS))
                                       (hnodes_snapped4 T NS PS))).
          - apply in_or_app; left. unfold hrx5_rest. repeat (first [left; reflexivity | right]).
          - apply hrx5_b8_hnodes_valid. rewrite hrx5_b8_snapped_addr by exact HL. exact Hin. }
        match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with PP end. unfold PP. entailer!.
        destruct Hc3 as [E1 E2]. rewrite E1, E2. cbn [Z.eqb Pos.eqb andb].
        destruct tg; simpl in PNtg; try contradiction.
        - subst. reflexivity.
        - reflexivity. }
      { forward. match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with PP end. unfold PP.
        entailer!. revert H9. destruct (Z.eqb_spec pth 1), (Z.eqb_spec (obj_kind o) 3);
          cbv beta iota delta [andb]; intros Hx; try reflexivity.
        apply (f_equal Int.unsigned) in Hx; vm_compute in Hx; discriminate. }
      unfold PP; clear PP.
      forward_if.
      * assert (Hc: hrx5_B8_isC o pth ai ar tg).
        { unfold hrx5_B8_isC.
          match goal with Hx: (if _ then _ else _) <> Int.zero |- _ => revert Hx end.
          destruct (Z.eqb_spec pth 1), (Z.eqb_spec (obj_kind o) 3), (Val.eq tg nullval);
            cbv beta iota delta [andb]; intros Hx; auto; contradiction Hx; reflexivity. }
        hrx5_b8_branch KC Hc.
        unfold hrx5_B8_Q; cbv zeta; unfold hrx5_ptrs, hrx5_lvars; cbn [app]; entailer!; apply derives_refl.
      * assert (Hc: hrx5_B8_isE o pth ai ar tg).
        { split; [exact Hn | split; [exact Hn2 |]]. unfold hrx5_B8_isC.
          match goal with Hx: (if _ then _ else _) = Int.zero |- _ => revert Hx end.
          destruct (Z.eqb_spec pth 1), (Z.eqb_spec (obj_kind o) 3), (Val.eq tg nullval);
            cbv beta iota delta [andb]; intros Hx; try tauto;
            apply (f_equal Int.unsigned) in Hx; vm_compute in Hx; discriminate. }
        hrx5_b8_branch KE' Hc.
        unfold hrx5_B8_Q; cbv zeta; unfold hrx5_ptrs, hrx5_lvars; cbn [app]; entailer!; apply derives_refl.
Qed.

End B8.
