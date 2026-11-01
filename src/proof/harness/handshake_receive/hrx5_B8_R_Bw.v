(* law handshake_receive: B8 branch R, segment B under the CORRECTED
   statement: hrx5_B8R_B_stmt of hrx5_B8_R_defs.v is unprovable (its precondition lacks
   NoDup (t_L T)); hrx5_B8R_Bw_stmt adds the hypothesis itable_wf T. *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_P.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_C1.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_C2.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_C3.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_Z.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_N.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_K.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_L.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

(* hrx5_B8R_seg with the hypothesis itable_wf T (verbatim copy of hrx5_B8R_segw) *)
Definition hrx5_B8R_Bw_seg
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

Definition hrx5_B8R_Bw_stmt : Prop := hrx5_B8R_Bw_seg hrx5_B8R_RA hrx5_B8R_RB hrx5_B8R_B false.

(* ---------------------------------------------------------------------- *)
(* generic helpers                                                         *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B8RB_pw (Ps1 Ps2: list Prop) (Lc: list localdef) (Sp: list mpred) :
  fold_right and True Ps2 -> PROPx Ps1 (LOCALx Lc (SEPx Sp)) |-- PROPx Ps2 (LOCALx Lc (SEPx Sp)).
Proof.
  intros H rho. unfold PROPx. simpl. apply andp_derives; [| apply derives_refl].
  apply prop_derives. intros _. exact H.
Qed.

Lemma hrx5_B8RB_ext {Espec: OracleKind} {cs: compspecs} Delta (Ps: list Prop) (Lc: list localdef) (Sp: list mpred)
  c Post :
  (fold_right and True Ps -> semax Delta (PROPx Ps (LOCALx Lc (SEPx Sp))) c Post) ->
  semax Delta (PROPx Ps (LOCALx Lc (SEPx Sp))) c Post.
Proof.
  intros HS.
  apply semax_pre with (!! (fold_right and True Ps) && PROPx Ps (LOCALx Lc (SEPx Sp))).
  - apply andp_left2. intro rho. unfold PROPx. simpl. apply derives_extract_prop. intros HP.
    apply andp_right; [apply prop_right; exact HP |]. apply andp_right; [apply prop_right; exact HP |].
    apply derives_refl.
  - apply semax_extract_prop. exact HS.
Qed.

Lemma hrx5_B8RB_post {Espec: OracleKind} {cs: compspecs} Delta P c Q Q' R :
  semax Delta P c (overridePost Q R) -> (local (tc_environ Delta) && Q |-- Q') ->
  semax Delta P c (overridePost Q' R).
Proof.
  intros H HQ. destruct R as [r1 r2 r3 r4].
  eapply semax_post; [| | | | exact H]; unfold overridePost; cbn [RA_normal RA_break RA_continue RA_return].
  - exact HQ.
  - apply andp_left2; apply derives_refl.
  - apply andp_left2; apply derives_refl.
  - intros; apply andp_left2; apply derives_refl.
Qed.

(* the world's index table is well formed (from the itable in the SEP) *)
Lemma hrx5_B8RB_itwf (CSw: compspecs) gv wg head W Rst :
  rxw_rep CSw gv Tsh wg head W * Rst |-- !! itable_wf (rw_T W).
Proof.
  unfold rxw_rep, itable. Intros. apply prop_right. assumption.
Qed.

Lemma hrx5_B8RB_fapp (A B: list Prop) :
  fold_right and True A -> fold_right and True B -> fold_right and True (A ++ B).
Proof. induction A as [|x A IH]; simpl; tauto. Qed.

Lemma hrx5_B8R_Bw_ok : hrx5_B8R_Bw_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul
    q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY HW.
  set (W1 := hrx5_B8R_W1 x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6 port o dp d).
  (* the world's table is well formed *)
  assert (HIT: forall pl (Wx: rxw) tl,
    hrx5_B8R_St x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4
      ip6 port o dp img tg ai ar d Wx tl pl |-- !! itable_wf (rw_T Wx)).
  { intros pl Wx tl rho. unfold hrx5_B8R_St. cbv zeta. unfold PROPx, LOCALx, SEPx. simpl.
    apply andp_left2. apply andp_left2. apply hrx5_B8RB_itwf. }
  match goal with |- semax _ ?Pre _ _ => apply semax_pre with (!! itable_wf (rw_T W1) && Pre) end.
  { apply andp_left2. apply andp_right; [apply HIT | apply derives_refl]. }
  apply semax_extract_prop. intros HT.
  cbv beta zeta delta [hrx5_B8R_RA hrx5_B8R_St]. apply hrx5_B8RB_ext. cbn [fold_right app].
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & HF).
  pose proof (hrx5_B8RB_pure_ok x25519 aead_enc aead_dec xaead_enc xaead_dec L R sec birth S w NS PS T head nk KE st i
                kc lul q proto ip4 ip6 port o dp tg ai ar d a P M ck h j HY H1 H2 H3 H4 H5 H6 H7 H8 HF HT)
    as (HG & HFF & HFA & HFS).
  assert (HB: fold_right and True
    [hrx5_base_ok R sec birth S; hrx5_inv x25519 R L NS PS KE T head nk; 0 <= st <= Int64.max_unsigned;
     0 <= i < st; obj_ok o; malloc_compatible (Zlength (obj_bytes o)) dp;
     hrx5_acc_ok x25519 aead_dec xaead_dec R NS PS T o (s_boot S) tg ai ar; rxdraw_ok T d])
    by exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 I)))))))).
  rewrite hrx5_B8RB_eq. unfold hrx5_Delta. abbreviate_semax.
  destruct (hrx5_B8R_alloc d) eqn:Ha.
  - (* the allocation succeeded *)
    specialize (HFA eq_refl). forward_if.
    { rewrite Ha in H. apply Int.one_not_zero in H. contradiction. }
    unfold MORE_COMMANDS, abbreviate.
    apply semax_pre with (P' := hrx5_B8RB_Sa x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j).
    { apply andp_left2. cbv beta zeta delta [hrx5_B8RB_Sa hrx5_B8R_St]. apply hrx5_B8RB_pw.
      apply hrx5_B8RB_fapp; [exact HB | apply hrx5_B8RB_fapp; [exact HG | exact HFA]]. }
    apply semax_seq with (Q := hrx5_B8RB_Sa x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j).
    { unfold POSTCONDITION, abbreviate. rewrite hrx5_overridePost2. exact (hrx5_B8RB_Z_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY). }
    cbv beta zeta delta [hrx5_B8RB_Sa hrx5_B8R_St].
    destruct (hrx5_B8R_sess d P) eqn:Hs.
    + (* a session *)
      assert (HND: NoDup (t_L T)) by (destruct HW as [HND _]; exact HND).
      specialize (HFS eq_refl HND).
      forward_if.
      2: { match goal with Hx: (if hrx5_B8R_sess d P then _ else _) = _ |- _ =>
             rewrite Hs in Hx; apply Int.one_not_zero in Hx; contradiction end. }
      apply semax_pre with (P' := hrx5_B8RB_Ss x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j).
      { apply andp_left2. cbv beta zeta delta [hrx5_B8RB_Ss hrx5_B8R_St]. apply hrx5_B8RB_pw.
        apply hrx5_B8RB_fapp; [exact HB | apply hrx5_B8RB_fapp; [exact HG | apply hrx5_B8RB_fapp; [exact HFA |]]].
        split; [exact Hs | exact HFS]. }
      destruct (hrx5_B8RB_K_ok) as (HKP & HK1 & HK2).
      apply semax_seq with (Q := hrx5_B8RB_Ssk x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j).
      { unfold POSTCONDITION, abbreviate. rewrite hrx5_overridePost2. exact (HKP Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY). }
      apply semax_seq with (Q := hrx5_B8RB_Ssk x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j).
      { unfold POSTCONDITION, abbreviate. rewrite hrx5_overridePost2. exact (HK1 Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY). }
      apply semax_seq with (Q := hrx5_B8RB_Ssk x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j).
      { unfold POSTCONDITION, abbreviate. rewrite hrx5_overridePost2. exact (HK2 Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY). }
      unfold POSTCONDITION, abbreviate.
      eapply hrx5_B8RB_post; [exact (hrx5_B8RB_CLR_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY) |].
      apply andp_left2. cbv beta zeta delta [hrx5_B8RB_Sx hrx5_B8R_RB hrx5_B8R_St]. apply hrx5_B8RB_pw.
      apply hrx5_B8RB_fapp; [exact HB | exact HF].
    + (* P dead *)
      forward_if.
      { match goal with Hx: (if hrx5_B8R_sess d P then _ else _) <> _ |- _ =>
             rewrite Hs in Hx; contradiction end. }
      apply semax_pre with (P' := hrx5_B8RB_Sn x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j).
      { apply andp_left2. cbv beta zeta delta [hrx5_B8RB_Sn hrx5_B8R_St]. apply hrx5_B8RB_pw.
        apply hrx5_B8RB_fapp; [exact HB | apply hrx5_B8RB_fapp; [exact HG | apply hrx5_B8RB_fapp; [exact HFA |]]].
        split; [exact Hs | exact I]. }
      unfold POSTCONDITION, abbreviate.
      eapply hrx5_B8RB_post; [exact (hrx5_B8RB_DEAD_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY) |].
      apply andp_left2. cbv beta zeta delta [hrx5_B8RB_Sn hrx5_B8R_RB hrx5_B8R_St hrx5_B8R_Wxv hrx5_B8R_W1v].
      cbv beta zeta delta [hrx5_B8RB_FA] in HFA. cbn [fold_right] in HFA.
      destruct HFA as (_ & _ & _ & _ & _ & _ & _ & _ & HWx & _). rewrite (HWx Hs).
      apply hrx5_B8RB_pw. apply hrx5_B8RB_fapp; [exact HB | exact HF].
  - (* the allocation failed *)
    specialize (HFF eq_refl). forward_if.
    2: { rewrite Ha in H. contradiction. }
    apply semax_pre with (P' := hrx5_B8RB_Sf x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j).
    { apply andp_left2. cbv beta zeta delta [hrx5_B8RB_Sf hrx5_B8R_St]. apply hrx5_B8RB_pw.
      apply hrx5_B8RB_fapp; [exact HB | apply hrx5_B8RB_fapp; [exact HG | exact HFF]]. }
    apply semax_seq with (Q := hrx5_B8RB_Sf x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j).
    { unfold POSTCONDITION, abbreviate. rewrite hrx5_overridePost2. exact (hrx5_B8RB_C1_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY). }
    apply semax_seq with (Q := hrx5_B8RB_Sf x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j).
    { unfold POSTCONDITION, abbreviate. rewrite hrx5_overridePost2. exact (hrx5_B8RB_C2_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY). }
    unfold POSTCONDITION, abbreviate.
    eapply hrx5_B8RB_post; [exact (hrx5_B8RB_C3_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY) |].
    apply andp_left2. cbv beta zeta delta [hrx5_B8RB_Sf hrx5_B8R_RB hrx5_B8R_St hrx5_B8R_Wxv hrx5_B8R_W1v].
    cbv beta delta [hrx5_B8RB_FF] in HFF. cbn [fold_right] in HFF.
    destruct HFF as (_ & _ & _ & _ & _ & HWx & _). rewrite HWx.
    apply hrx5_B8RB_pw. apply hrx5_B8RB_fapp; [exact HB | exact HF].
Qed.
