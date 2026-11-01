(* law keypairs: main's body from its parts (hkp5_parts of hkp5_stmts.v: the segments,
   the context lifting, the initial globals, the model facts as HYPOTHESES) - the prologue (main_pre's globals, the
   stack frame, create_mem_mgr), segment A, the loop (invariant hkp5_Inv with the frame hkp5_othR .. O * FR0; body
   L0, the if-chain on op, LC; i++) and segment F. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.harness.keypairs.hkp5_stmts.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.
Local Open Scope Z_scope.

Lemma hkp5m_lift {Espec: OracleKind} G0 D P c R :
  tycontext_sub (hkp5_Delta G0) D -> semax (hkp5_Delta G0) P c R -> semax D P c R.
Proof. intros HS H. eapply semax_Delta_subsumption; eauto. Qed.

Lemma hkp5m_l1w {Espec: OracleKind} {cs: compspecs} Delta P c (Q: Z -> environ -> mpred) (i: Z) R :
  semax Delta P c (loop1_ret_assert (Q i) R) -> semax Delta P c (loop1_ret_assert (EX j: Z, Q j) R).
Proof.
  intros H. eapply semax_post; [| | | | exact H]; destruct R; simpl; intros; try intro rho; apply andp_left2;
    try apply derives_refl; cbv beta; apply (exp_right i); apply derives_refl.
Qed.

Lemma hkp5m_ovl Q R : overridePost Q (loop1_ret_assert Q R) = loop1_ret_assert Q R.
Proof. destruct R; reflexivity. Qed.

Lemma hkp5m_seqs_app l1 l2 rest : hkp5_seqs (l1 ++ l2) rest = hkp5_seqs l1 (hkp5_seqs l2 rest).
Proof. induction l1 as [|a l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma hkp5m_repr_op op n : 0 <= op < 8 -> 0 <= n < 8 -> Int.repr op = Int.repr n -> op = n.
Proof.
  intros Ho Hn E. apply (f_equal Int.unsigned) in E. rewrite !Int.unsigned_repr in E by rep_lia. exact E.
Qed.

Lemma hkp5m_normal {Espec: OracleKind} {cs: compspecs} Delta P c Q Post :
  ENTAIL Delta, Q |-- RA_normal Post ->
  semax Delta P c (normal_ret_assert Q) -> semax Delta P c Post.
Proof.
  intros HE H. apply semax_post with (R' := normal_ret_assert Q); [exact HE | | | | exact H];
    [apply andp_left2, FF_left .. | intros vl; apply andp_left2, FF_left].
Qed.

(* x = e and if (b) c else d, without floyd's Delta simplification (main's context is abstract here) *)
Lemma hkp5m_set {Espec: OracleKind} {cs: compspecs} Delta id e t v L S Post :
  typeof_temp Delta id = Some t -> is_neutral_cast (implicit_deref (typeof e)) t = true ->
  ENTAIL Delta, PROPx [] (LOCALx L (SEPx S)) |-- local (liftx (@eq val v) (eval_expr e)) ->
  ENTAIL Delta, PROPx [] (LOCALx L (SEPx S)) |-- tc_expr Delta e ->
  ENTAIL Delta, PROPx [] (LOCALx (temp id v :: remove_localdef_temp id L) (SEPx S)) |-- RA_normal Post ->
  semax Delta (PROPx [] (LOCALx L (SEPx S))) (Sset id e) Post.
Proof.
  intros H1 H2 H3 H4 H5. eapply semax_pre; [apply andp_left2, now_later |].
  eapply hkp5m_normal; [exact H5 | eapply semax_SC_set; eauto].
Qed.

Lemma hkp5m_if {Espec: OracleKind} {cs: compspecs} Delta b v L S c d Post :
  bool_type (typeof b) = true ->
  ENTAIL Delta, PROPx [] (LOCALx L (SEPx S)) |-- tc_expr Delta (Eunop Cop.Onotbool b tint) ->
  ENTAIL Delta, PROPx [] (LOCALx L (SEPx S)) |-- local (liftx (@eq val v) (eval_expr b)) ->
  semax Delta (PROPx [typed_true (typeof b) v] (LOCALx L (SEPx S))) c Post ->
  semax Delta (PROPx [typed_false (typeof b) v] (LOCALx L (SEPx S))) d Post ->
  semax Delta (PROPx [] (LOCALx L (SEPx S))) (Sifthenelse b c d) Post.
Proof.
  intros H1 H2 H3 H4 H5. eapply semax_pre; [apply andp_left2, now_later |].
  eapply semax_ifthenelse_PQR'; eauto.
Qed.

Ltac hkp5m_unf := unfold hkp5_PL0, hkp5_St, hkp5_temps, hkp5_lvars, hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs,
  hkp5_globs; simpl app.

Section Glue.
Context {Espec: OracleKind}.
Variable x25519: list byte -> list byte -> list byte.
Variable G: funspecs.

(* the branch op == n of the if-chain *)
Lemma hkp5m_if_op F V steps FR i op n s1 s2 (Post: ret_assert) :
  0 <= n < 8 ->
  (op = n -> semax (hkp5_Delta G) (hkp5_PL0 x25519 F V steps FR i n) s1 Post) ->
  (op <> n -> semax (hkp5_Delta G) (hkp5_PL0 x25519 F V steps FR i op) s2 Post) ->
  semax (hkp5_Delta G) (hkp5_PL0 x25519 F V steps FR i op) (Sifthenelse (hkp5_op_test n) s1 s2) Post.
Proof.
  intros Hn H1 H2.
  unfold hkp5_PL0 at 1. Intros Y. unfold hkp5_op_test.
  unfold hkp5_temps, hkp5_lvars; simpl app.
  eapply semax_pre; [apply andp_left2, now_later |].
  apply semax_ifthenelse_PQR' with (v := bool2val (Int.eq (Int.repr op) (Int.repr n))); [reflexivity | | | |].
  - entailer!.
  - entailer!.
  - Intros. assert (E: op = n).
    { match goal with HT: Int.eq _ _ = true |- _ => apply Int.same_if_eq in HT; apply hkp5m_repr_op; auto end. }
    subst op. eapply semax_pre; [| apply H1; reflexivity].
    Exists Y. unfold hkp5_temps, hkp5_lvars; simpl app. entailer!.
  - Intros. assert (E: op <> n).
    { intros ->. rewrite Int.eq_true in *. discriminate. }
    eapply semax_pre; [| apply H2; exact E].
    Exists Y. unfold hkp5_temps, hkp5_lvars; simpl app. entailer!.
Qed.

(* the last two branches: t = (op == 4 || op == 5); op 4 / 5 or op 6 *)
Lemma hkp5m_if_45 F V steps FR i op (Post: ret_assert) :
  op <> 0 -> op <> 1 -> op <> 2 -> op <> 3 -> op <> 7 ->
  ((op = 4 \/ op = 5) -> semax (hkp5_Delta G) (hkp5_PL0 x25519 F V steps FR i op) hkp5_sOp45 Post) ->
  semax (hkp5_Delta G) (hkp5_PL0 x25519 F V steps FR i 6) hkp5_sOp6 Post ->
  semax (hkp5_Delta G) (hkp5_PL0 x25519 F V steps FR i op)
    (Ssequence hkp5_s45 (Sifthenelse (Etempvar hkp5_t45 tint) hkp5_sOp45 hkp5_sOp6)) Post.
Proof.
  intros N0 N1 N2 N3 N7 H45 H6. destruct Post as [Pn Pb Pc Pr].
  unfold hkp5_PL0 at 1. Intros Y. rewrite hkp5_s45_shape. unfold hkp5_op_test.
  unfold hkp5_temps, hkp5_lvars; simpl app.
  change hkp5_t45 with 185%positive.
  set (b := if zeq op 4 then Int.one else if zeq op 5 then Int.one else Int.zero).
  match goal with |- semax _ (PROPx _ (LOCALx ?L (SEPx ?S))) _ _ =>
    apply semax_seq with (Q := PROPx [] (LOCALx (temp 185%positive (Vint b) :: L) (SEPx S))) end.
  - apply hkp5m_if with (v := bool2val (Int.eq (Int.repr op) (Int.repr 4))); [reflexivity | entailer! | entailer! | |].
    + Intros. assert (E4: op = 4).
      { match goal with HT: Int.eq _ _ = true |- _ => apply Int.same_if_eq in HT; apply hkp5m_repr_op; auto; lia end. }
      apply hkp5m_set with (t := tint) (v := Vint Int.one); [reflexivity | reflexivity | entailer! | entailer! |].
      simpl RA_normal. unfold b. rewrite if_true by auto. simpl remove_localdef_temp. entailer!.
    + Intros. assert (E4: op <> 4) by (intros ->; rewrite Int.eq_true in *; discriminate).
      apply hkp5m_set with (t := tint) (v := Vint b); [reflexivity | reflexivity | entailer! | entailer! |].
      * unfold b. rewrite if_false by auto. destruct (zeq op 5) as [->|N5]; [reflexivity |].
        rewrite (Int.eq_false (Int.repr op) (Int.repr 5)); [reflexivity |].
        intros E. apply hkp5m_repr_op in E; auto; lia.
      * simpl RA_normal. simpl remove_localdef_temp. entailer!.
  - apply hkp5m_if with (v := Vint b); [reflexivity | entailer! | entailer! | |].
    + Intros. assert (E45: op = 4 \/ op = 5).
      { unfold b in *. destruct (zeq op 4); auto. destruct (zeq op 5); auto.
        match goal with HT: Int.zero <> Int.zero |- _ => contradiction HT; reflexivity end. }
      eapply semax_pre; [| apply H45; exact E45].
      unfold hkp5_PL0. Exists Y. unfold hkp5_temps, hkp5_lvars; simpl app. entailer!.
    + Intros. assert (E6: op = 6).
      { unfold b in *. destruct (zeq op 4); [discriminate |]. destruct (zeq op 5); [discriminate |]. lia. }
      subst op. eapply semax_pre; [| apply H6].
      unfold hkp5_PL0. Exists Y. unfold hkp5_temps, hkp5_lvars; simpl app. entailer!.
Qed.

Variables (F: hkp5_fix) (V: hkp5_val) (steps: Z) (FR: mpred).

Variable HL0 : forall i R, semax (hkp5_Delta G) (hkp5_Icont x25519 F V steps FR i) hkp5_segL0
  (overridePost (EX op: Z, hkp5_PL0 x25519 F V steps FR i op) R).
Definition hkp5m_Sop (n: Z) (s: statement) : Prop :=
  forall i R, semax (hkp5_Delta G) (hkp5_PL0 x25519 F V steps FR i n) s
                (loop1_ret_assert (hkp5_Icont x25519 F V steps FR i) R).
Variable HOp0 : hkp5m_Sop 0 hkp5_sOp0.
Variable HOp1 : hkp5m_Sop 1 hkp5_sOp1.
Variable HOp2 : hkp5m_Sop 2 hkp5_sOp2.
Variable HOp3 : hkp5m_Sop 3 hkp5_sOp3.
Variable HOp7 : hkp5m_Sop 7 hkp5_sOp7.
Variable HOp6 : hkp5m_Sop 6 hkp5_sOp6.
Variable HOp45 : forall i op R, op = 4 \/ op = 5 ->
  semax (hkp5_Delta G) (hkp5_PL0 x25519 F V steps FR i op) hkp5_sOp45
    (loop1_ret_assert (hkp5_Icont x25519 F V steps FR i) R).
Variable HLC : forall i R, semax (hkp5_Delta G) (hkp5_Icont x25519 F V steps FR i) hkp5_segLC
  (loop1_ret_assert (hkp5_Icont x25519 F V steps FR i) R).

Lemma hkp5m_ifc_ok i op R :
  semax (hkp5_Delta G) (hkp5_PL0 x25519 F V steps FR i op) hkp5_ifc
    (loop1_ret_assert (hkp5_Icont x25519 F V steps FR i) R).
Proof.
  rewrite hkp5_ifc_shape.
  apply hkp5m_if_op; [lia | intros ->; apply HOp0 | intros N0].
  apply hkp5m_if_op; [lia | intros ->; apply HOp1 | intros N1].
  apply hkp5m_if_op; [lia | intros ->; apply HOp2 | intros N2].
  apply hkp5m_if_op; [lia | intros ->; apply HOp3 | intros N3].
  apply hkp5m_if_op; [lia | intros ->; apply HOp7 | intros N7].
  apply hkp5m_if_45; [exact N0 | exact N1 | exact N2 | exact N3 | exact N7 | intros H45; apply HOp45; exact H45 | apply HOp6].
Qed.

Lemma hkp5m_loop_ok Y R :
  hkp5_fix_ok F V -> hkp5_inv F V Y -> 0 <= steps <= Int64.max_unsigned ->
  semax (hkp5_Delta G)
    (PROPx [] (LOCALx (hkp5_temps V Y steps ++ hkp5_lvars F) (SEPx (hkp5_SEP x25519 F V Y FR))))
    hkp5_loop (overridePost (hkp5_Inv x25519 F V steps FR) R).
Proof.
  intros Hfix Hinv Hst. destruct R as [Rn Rb Rc Rr].
  destruct hkp5_bsegs_eq as (EL0 & EIF & ELC).
  rewrite hkp5_loop_shape.
  unfold hkp5_temps, hkp5_lvars; simpl app.
  apply semax_seq with (Q := hkp5_Inv x25519 F V steps FR).
  { apply hkp5m_set with (t := tulong) (v := Vlong (Int64.repr 0)); [reflexivity | reflexivity | entailer! | entailer! |].
    simpl RA_normal. simpl remove_localdef_temp. unfold hkp5_Inv. Exists 0 Y.
    unfold hkp5_St, hkp5_temps, hkp5_lvars; simpl app. entailer!. }
  apply semax_loop with (Q' := (EX j: Z, hkp5_Icont x25519 F V steps FR j)).
  - (* body *)
    unfold hkp5_Inv at 1. Intros i Y0. unfold hkp5_St, hkp5_temps, hkp5_lvars; simpl app. Intros.
    apply semax_seq with (Q := hkp5_Icont x25519 F V steps FR i).
    + apply hkp5m_if with (v := bool2val (Int64.ltu (Int64.repr i) (Int64.repr steps)));
        [reflexivity | entailer! | entailer! | |].
      * Intros. assert (Hi: i < steps).
        { match goal with HT: Int64.ltu _ _ = true |- _ => apply ltu_inv64 in HT end.
          rewrite !Int64.unsigned_repr in * by rep_lia. lia. }
        eapply hkp5m_normal; [| apply semax_skip].
        simpl RA_normal. unfold hkp5_Icont. Exists Y0.
        unfold hkp5_St, hkp5_temps, hkp5_lvars; simpl app. entailer!.
      * Intros. eapply semax_pre; [| apply semax_break].
        simpl RA_break. unfold hkp5_Inv. Exists i Y0.
        unfold hkp5_St, hkp5_temps, hkp5_lvars; simpl app. entailer!.
    + apply (hkp5m_l1w _ _ _ (hkp5_Icont x25519 F V steps FR) i).
      eapply hkp5_semax_cut with (Q := EX op: Z, hkp5_PL0 x25519 F V steps FR i op);
        [discriminate | rewrite <- EL0; apply HL0 |].
      eapply hkp5_semax_cut with (Q := hkp5_Icont x25519 F V steps FR i);
        [discriminate | rewrite <- EIF | rewrite <- ELC; apply HLC].
      rewrite hkp5m_ovl. Intros op. apply hkp5m_ifc_ok.
  - (* i++ *)
    Intros i. unfold hkp5_Icont. Intros Y0. unfold hkp5_St, hkp5_temps, hkp5_lvars; simpl app. Intros.
    apply hkp5m_set with (t := tulong) (v := Vlong (Int64.repr (i + 1))); [reflexivity | reflexivity | entailer! | entailer! |].
    simpl RA_normal. simpl remove_localdef_temp. unfold hkp5_Inv. Exists (i + 1) Y0.
    unfold hkp5_St, hkp5_temps, hkp5_lvars; simpl app. entailer!.
Qed.

End Glue.

Lemma hkp5_main_body_from x25519 aead_enc aead_dec xaead_enc xaead_dec :
  hkp5_parts -> x25519_props x25519 ->
  @semax_body hkp5_V (hkp5_Gmain x25519 aead_enc aead_dec xaead_enc xaead_dec) W_keypairs KC.f_main hkp5_main_spec.
Proof.
  intros HP Hx.
  destruct HP as (HMF & HL0 & HOp0 & HOp1b & HOp1a & HOp2 & HOp3 & HOp7 & HOp45 & HOp6 & HLC & HA & HF & HB & HG).
  pose proof (HB x25519 aead_enc aead_dec xaead_enc xaead_dec) as HB0. clear HB.
  pose proof (Forall_inv HB0) as BL0; apply Forall_inv_tail in HB0.
  pose proof (Forall_inv HB0) as BOp0; apply Forall_inv_tail in HB0.
  pose proof (Forall_inv HB0) as BOp1b; apply Forall_inv_tail in HB0.
  pose proof (Forall_inv HB0) as BOp2; apply Forall_inv_tail in HB0.
  pose proof (Forall_inv HB0) as BOp3; apply Forall_inv_tail in HB0.
  pose proof (Forall_inv HB0) as BOp7; apply Forall_inv_tail in HB0.
  pose proof (Forall_inv HB0) as BOp45; apply Forall_inv_tail in HB0.
  pose proof (Forall_inv HB0) as BOp6; apply Forall_inv_tail in HB0.
  pose proof (Forall_inv HB0) as BLC; apply Forall_inv_tail in HB0.
  pose proof (Forall_inv HB0) as BOp1a; apply Forall_inv_tail in HB0.
  pose proof (Forall_inv HB0) as BA; apply Forall_inv_tail in HB0.
  pose proof (Forall_inv HB0) as BF; clear HB0.
  unfold hkp5_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply main_pre_InitGpred; [apply HG | reflexivity | | ].
  { apply Forall_forall; intros x Hx'; vm_compute in Hx'; repeat destruct Hx' as [Hx'|Hx']; try contradiction;
      subst x; vm_compute; exact I. }
  process_stackframe_of. change globals in gv.
  set (FR0 := (TT * has_ext tt)%logic).
  set (F := mkKF5 gv v_w v_t v_pt v_p v_raw v_pub v_snap v_opub v_first v_second).
  set (Gm := hkp5_Gmain x25519 aead_enc aead_dec xaead_enc xaead_dec) in *.
  eapply semax_pre with (P' := hkp5_P0 F FR0).
  { unfold hkp5_P0, hkp5_lvars. subst F FR0.
    cbn [f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second].
    sep_apply (create_mem_mgr gv). entailer!. }
  rewrite hkp5_body_eq.
  eapply semax_seq with (Q := FF); [| apply semax_ff].
  rewrite <- !hkp5m_seqs_app.
  replace (((hkp5_l 0 15 ++ hkp5_l 15 3) ++ hkp5_l 18 3) ++ hkp5_l 21 8) with (hkp5_l 0 29) by reflexivity.
  eapply hkp5_semax_cut with (l := hkp5_l 0 29) (Q := hkp5_PA x25519 F FR0);
    [discriminate | rewrite hkp5_overridePost2, <- hkp5_segA_eq; eapply hkp5m_lift; [exact BA | apply HA; exact Hx] |].
  unfold hkp5_PA at 1. Intros V Y steps O.
  destruct hkp5_segs_eq as (_ & _ & _ & _ & EL & EF).
  eapply hkp5_semax_cut with (l := hkp5_l 29 1) (Q := hkp5_Inv x25519 F V steps (hkp5_othR x25519 F V O * FR0)%logic);
    [discriminate | rewrite hkp5_overridePost2, <- EL |
     rewrite <- EF; eapply hkp5m_lift; [exact BF | apply HF; assumption]].
  eapply semax_pre; [| eapply (hkp5m_loop_ok x25519 Gm F V steps (hkp5_othR x25519 F V O * FR0)%logic) with (Y := Y);
                         try eassumption].
  - unfold hkp5_temps, hkp5_lvars; simpl app. apply andp_left2, derives_refl.
  - intros i R. eapply hkp5m_lift; [exact BL0 | apply HL0].
  - intros i R. eapply hkp5m_lift; [exact BOp0 | apply HOp0; assumption].
  - intros i R. rewrite hkp5_op1_shape.
    apply semax_seq with (Q := hkp5_PL0 x25519 F V steps (hkp5_othR x25519 F V O * FR0)%logic i 1).
    + eapply hkp5m_lift; [exact BOp1a | apply HOp1a; assumption].
    + eapply hkp5m_lift; [exact BOp1b | apply HOp1b; assumption].
  - intros i R. eapply hkp5m_lift; [exact BOp2 | apply HOp2; assumption].
  - intros i R. eapply hkp5m_lift; [exact BOp3 | apply HOp3; assumption].
  - intros i R. eapply hkp5m_lift; [exact BOp7 | apply HOp7; assumption].
  - intros i R. eapply hkp5m_lift; [exact BOp6 | apply HOp6; assumption].
  - intros i op R Hop. eapply hkp5m_lift; [exact BOp45 | apply HOp45; assumption].
  - intros i R. eapply hkp5m_lift; [exact BLC | apply HLC; assumption].
Qed.
