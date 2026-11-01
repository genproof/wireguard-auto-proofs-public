(* law keypairs: operation 1, part a (the keypair of another peer: received_with_keypair, CHECK(!r), CHECK(check_all), continue). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.keypairs.hkp5_op1.
Require Import WgNoise.proof.harness.keypairs.hkp5_spec.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The kents' list: walking it                                             *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hk5o1a_CCE : change_composite_env CKS W_keypairs. make_cs_preserve CKS W_keypairs. Defined.

Lemma hk5o1a_next_cs sh nx k :
  @field_at CKS sh t_kent (DOT HC._next) nx k = @field_at W_keypairs sh t_kent (DOT HC._next) nx k.
Proof.
  exact (f_equal (fun f => f k) (@field_at_change_composite CKS W_keypairs hk5o1a_CCE sh t_kent (DOT HC._next)
    nx nx (JMeq_refl _) eq_refl)).
Qed.

Definition hk5o1a_hd (KE: list kent4) : val := match KE with [] => nullval | e :: _ => ke_addr e end.

Lemma hk5o1a_rep_hd l KE : kents_rep W_keypairs l KE |-- !! (l = hk5o1a_hd KE).
Proof. destruct KE; simpl; entailer!. Qed.

Lemma hk5o1a_rep_fc l KE :
  kents_rep W_keypairs l KE |-- !! Forall (fun e => @field_compatible CKS t_kent [] (ke_addr e)) KE.
Proof.
  revert l. induction KE as [|e KE IH]; intros l; simpl; [entailer!|].
  Intros nx. unfold kent_cell. Intros. sep_apply (IH nx). entailer!.
Qed.

Lemma hk5o1a_hd_pn KE :
  Forall (fun e => @field_compatible CKS t_kent [] (ke_addr e)) KE -> is_pointer_or_null (hk5o1a_hd KE).
Proof.
  destruct KE as [|e KE]; simpl; intros Hf; [reflexivity|]. inv Hf.
  match goal with H: field_compatible _ _ _ |- _ => destruct H as [Hp _] end.
  destruct (ke_addr e); try contradiction; exact I.
Qed.

Lemma hk5o1a_focus l pre e suf :
  kents_rep W_keypairs l (pre ++ e :: suf) |--
  @field_at W_keypairs Ews t_kent (DOT HC._next) (hk5o1a_hd suf) (ke_addr e) *
  (@field_at W_keypairs Ews t_kent (DOT HC._next) (hk5o1a_hd suf) (ke_addr e) -*
   kents_rep W_keypairs l (pre ++ e :: suf)).
Proof.
  revert l. induction pre as [|x pre IH]; intros l; cbn [app kents_rep].
  - Intros nx. sep_apply (hk5o1a_rep_hd nx suf). Intros. subst nx.
    unfold kent_cell. Intros. rewrite hk5o1a_next_cs. cancel.
    rewrite <- wand_sepcon_adjoint. Exists (hk5o1a_hd suf). entailer!.
    rewrite hk5o1a_next_cs; apply derives_refl.
  - Intros nx. sep_apply (IH nx). cancel.
    rewrite <- wand_sepcon_adjoint. Exists nx. entailer!.
    rewrite sepcon_comm. apply wand_frame_elim.
Qed.

Lemma hk5o1a_focus' l KE pre e suf : KE = pre ++ e :: suf ->
  kents_rep W_keypairs l KE |--
  @field_at W_keypairs Ews t_kent (DOT HC._next) (hk5o1a_hd suf) (ke_addr e) *
  (@field_at W_keypairs Ews t_kent (DOT HC._next) (hk5o1a_hd suf) (ke_addr e) -* kents_rep W_keypairs l KE).
Proof. intros ->. apply hk5o1a_focus. Qed.

Lemma hk5o1a_hd_suf KE pre e suf : KE = pre ++ e :: suf ->
  Forall (fun e => @field_compatible CKS t_kent [] (ke_addr e)) KE -> is_pointer_or_null (hk5o1a_hd suf).
Proof.
  intros -> Hf. apply hk5o1a_hd_pn. apply Forall_app in Hf. destruct Hf as [_ Hf]. inv Hf. auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* The pool: kent addresses are pool entries, not P's keypairs             *)
(* ---------------------------------------------------------------------- *)

Lemma hk5o1a_In_sfind {B: Type} (D: list (val * share * B)) a :
  In a (saddrs D) -> exists sh E, sfind D a = Some (sh, E).
Proof.
  induction D as [|[[x shx] u] D IH]; simpl; intros Hi; [contradiction|].
  destruct (EqDec_val x a); [eauto|]. destruct Hi; [congruence|auto].
Qed.

Lemma hk5o1a_sfind_In {B: Type} (D: list (val * share * B)) a sh E :
  sfind D a = Some (sh, E) -> In (a, sh, E) D.
Proof.
  induction D as [|[[x shx] u] D IH]; simpl; intros Hs; [discriminate|].
  destruct (EqDec_val x a); [inv Hs; auto|auto].
Qed.

Lemma hk5o1a_pool_split {B: Type} (D: list (val * share * B)) a sh E (f: val * share * B -> mpred) :
  sfind D a = Some (sh, E) ->
  VST.msl.iter_sepcon.iter_sepcon f D = (f (a, sh, E) * VST.msl.iter_sepcon.iter_sepcon f (sdel D a))%logic.
Proof.
  induction D as [|[[x shx] u] D IH]; simpl; intros Hs; [discriminate|].
  destruct (EqDec_val x a); [inv Hs; reflexivity|].
  rewrite (IH Hs); simpl. rewrite <- !sepcon_assoc, (sepcon_comm (f _) (f _)). reflexivity.
Qed.

Lemma hk5o1a_pool_valid sht t T a :
  In a (saddrs (t_D T)) -> itable sht t T |-- valid_pointer a.
Proof.
  intros Hi. destruct (hk5o1a_In_sfind _ _ Hi) as (sh & E & Hs).
  unfold itable. Intros. rename H into W.
  assert (Wsh: writable_share sh).
  { destruct W as (_ & _ & _ & HF). rewrite Forall_forall in HF. apply (HF (a, sh, E)).
    apply hk5o1a_sfind_In; auto. }
  rewrite (hk5o1a_pool_split _ _ _ _ _ Hs).
  apply sepcon_valid_pointer2. apply sepcon_valid_pointer1.
  unfold pool_item_rep, entry_at.
  apply data_at_valid_ptr; [apply readable_nonidentity, writable_readable; auto | reflexivity].
Qed.

Lemma hk5o1a_kin F V O p OH KS T e :
  hkp5_oth_ok F V O -> hk5_pool p (v_OD V) OH KS T -> In e (o_KE O) ->
  In (ke_addr e) (saddrs (t_D T)) /\ ~ In (ke_addr e) (map fst KS).
Proof.
  intros HO HP He.
  destruct HO as (_ & _ & _ & _ & _ & _ & HOD & _).
  destruct HP as (HT & _ & _ & HKS & _).
  assert (Hod: In (ke_addr e) (saddrs (v_OD V))) by (apply HOD; right; apply in_map; auto).
  split.
  - apply HT. right; right; auto.
  - intros Hk. exact (HKS _ Hk Hod).
Qed.

Lemma hk5o1a_fold x25519 F V Y (A B: mpred) :
  fold_right_sepcon (hkp5_SEP x25519 F V Y (A * B)) = fold_right_sepcon (hkp5_SEP x25519 F V Y A) * B.
Proof.
  unfold hkp5_SEP. rewrite !app_assoc, !fold_right_sepcon_app. cbn [fold_right_sepcon].
  rewrite !sepcon_emp. symmetry. apply sepcon_assoc.
Qed.

Lemma hk5o1a_SEPx {A0: Type} x25519 F V Y (A B: mpred) :
  @SEPx A0 (hkp5_SEP x25519 F V Y (A * B)) = SEPx [fold_right_sepcon (hkp5_SEP x25519 F V Y A); B].
Proof.
  unfold SEPx. extensionality rho. rewrite hk5o1a_fold. cbn [fold_right_sepcon]. rewrite sepcon_emp.
  reflexivity.
Qed.

Lemma hkp5_segOp1a_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps (O: hkp5_oth) FR i R :
  hkp5_model_facts -> hkp5_oth_ok F V O ->
  semax (hkp5_Delta (hkp5_G_Op1a x25519)) (hkp5_PL0 x25519 F V steps (hkp5_othR x25519 F V O * FR) i 1) hkp5_op1_a
    (overridePost (hkp5_PL0 x25519 F V steps (hkp5_othR x25519 F V O * FR) i 1)
       (loop1_ret_assert (hkp5_Icont x25519 F V steps (hkp5_othR x25519 F V O * FR) i) R)).
Proof.
  intros HM HO.
  unfold hkp5_PL0, hkp5_Delta.
  Intros Y.
  destruct F as [gv w t pt p raw pub snap opub first second].
  destruct Y as [S ww kc P KS T HH now next_id id_known hsn].
  destruct HH as [ML sp sc sn fr mw].
  rename H1 into Hinv.
  set (F0 := {| f_gv := gv; f_w := w; f_t := t; f_pt := pt; f_p := p; f_raw := raw; f_pub := pub;
                f_snap := snap; f_opub := opub; f_first := first; f_second := second |}) in *.
  unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
  unfold hkp5_othR, hkp5_oth_rep.
  cbn [app fold_right_sepcon f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second F0 y_S y_w y_kc y_P y_KS y_T y_H y_now
       y_next_id y_id_known y_hsn h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn] in Hinv |- *.
  rewrite sepcon_emp. Intros.
  destruct R as [Rn Rb Rc Rr]. unfold overridePost, loop1_ret_assert.
  abbreviate_semax.
  unfold hkp5_op1_a.
  pose proof Hinv as (Hr0 & _).
  cbn [f_p y_H y_P y_KS y_T] in Hr0.
  pose proof Hr0 as ((_ & _ & _ & _ & _ & _ & _ & _ & Hpool) & _).
  assert (Hkin: forall e, In e (o_KE O) -> In (ke_addr e) (saddrs (t_D T)) /\ ~ In (ke_addr e) (map fst KS))
    by (intros e He; exact (hk5o1a_kin _ _ _ _ _ _ _ _ HO Hpool He)).
  assert_PROP (o_kd O = hk5o1a_hd (o_KE O)) as Hhd by (sep_apply (hk5o1a_rep_hd (o_kd O) (o_KE O)); entailer!).
  assert_PROP (Forall (fun e => @field_compatible CKS t_kent [] (ke_addr e)) (o_KE O)) as Hfc
    by (sep_apply (hk5o1a_rep_fc (o_kd O) (o_KE O)); entailer!).
  pose proof (hk5o1a_hd_pn _ Hfc) as Hpn0. rewrite <- Hhd in Hpn0.
  forward.
  lazymatch goal with |- semax _ (PROPx ?P0 (LOCALx ?Q0 (SEPx ?R0))) _ _ =>
    forward_if (EX b: bool, PROPx ((b = true -> o_KE O <> []) :: P0)
      (LOCALx (temp KC._t'39 (Val.of_bool b) :: Q0) (SEPx R0))) end.
  { destruct (o_KE O) as [|e0 KE0] eqn:EKE; rewrite Hhd; cbn [hk5o1a_hd].
    - entailer!.
    - apply denote_tc_test_eq_split; [| apply valid_pointer_null].
      sep_apply (hk5o1a_pool_valid Tsh t T (ke_addr e0) (proj1 (Hkin e0 (or_introl eq_refl)))). entailer!. }
  { forward_call tt. Intros u. forward.
    { entailer!. match goal with H8: _ /\ Int.repr 8 = Int.mone |- _ => destruct H8 as [_ Hm] end.
      apply (f_equal Int.signed) in Hm. rewrite Int.signed_repr in Hm by rep_lia.
      rewrite Int.signed_mone in Hm. lia. }
    Exists (Int.eq (Int.mods (Int.repr u) (Int.repr 8)) (Int.repr 0)). entailer!.
    split; [intros _ E; rewrite E in Hhd; cbn in Hhd; contradiction |].
    destruct (Int.eq _ _); reflexivity. }
  { forward. Exists false. entailer!. }
  Intros b.
  match goal with H5: b = true -> _ |- _ => rename H5 into Hb end.
  forward_if.
  2: { forward. Exists (mkKY5 S ww kc P KS T (mkH5 ML sp sc sn fr mw) now next_id id_known hsn).
       unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
       unfold hkp5_othR, hkp5_oth_rep.
       cbn [app fold_right_sepcon f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second F0 y_S y_w y_kc
         y_P y_KS y_T y_H y_now y_next_id y_id_known y_hsn h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn].
       entailer!. }
  match goal with Ht: typed_true _ _ |- _ => rename Ht into Hbt end.
  destruct b; [specialize (Hb eq_refl) | unfold typed_true in Hbt; discriminate].
  forward.
  forward_call tt. Intros n0.
  lazymatch goal with |- semax _ (PROPx ?P0 (LOCALx (temp KC._m _ :: temp KC._e _ :: ?Q0) (SEPx ?R0))) _ _ =>
    forward_loop (EX pre: list kent4, EX e: kent4, EX suf: list kent4, EX mm: Z,
        PROPx ((o_KE O = pre ++ e :: suf) :: (0 <= mm <= Int64.max_unsigned) :: P0)
        (LOCALx (temp KC._m (Vlong (Int64.repr mm)) :: temp KC._e (ke_addr e) :: Q0) (SEPx R0)))
      break: (EX pre: list kent4, EX e: kent4, EX suf: list kent4,
        PROPx ((o_KE O = pre ++ e :: suf) :: P0)
        (LOCALx (temp KC._e (ke_addr e) :: Q0) (SEPx R0))) end.
  { destruct (o_KE O) as [|e0 KE0] eqn:EKE; [contradiction|].
    Exists (@nil kent4) e0 KE0 n0. rewrite Hhd. entailer!. }
  { Intros pre e suf mm.
    match goal with Hx: o_KE O = pre ++ e :: suf |- _ => rename Hx into Hl end.
    lazymatch goal with |- semax _ (PROPx ?P1 (LOCALx ?Q1 (SEPx ?R1))) _ _ =>
      forward_if (EX c: bool, PROPx ((c = true -> suf <> [] /\ 0 < mm) :: P1)
        (LOCALx (temp KC._t'36 (Val.of_bool c) :: Q1) (SEPx R1))) end.
    - pose proof (hk5o1a_hd_suf _ _ _ _ Hl Hfc) as Hpns.
      sep_apply (hk5o1a_focus' (o_kd O) (o_KE O) pre e suf Hl). Intros.
      forward.
      sep_apply (wand_frame_elim (@field_at W_keypairs Ews t_kent (DOT HC._next) (hk5o1a_hd suf) (ke_addr e))
                  (kents_rep W_keypairs (o_kd O) (o_KE O))).
      destruct suf as [|e2 suf2]; cbn [hk5o1a_hd].
      + forward. Exists false. entailer!.
      + assert (He2: In e2 (o_KE O)) by (rewrite Hl; apply in_or_app; right; right; left; reflexivity).
        assert (Pe2: isptr (ke_addr e2)).
        { rewrite Forall_forall in Hfc. destruct (Hfc e2 He2) as [Hp _]. exact Hp. }
        forward.
        { entailer!. apply denote_tc_test_eq_split; [| apply valid_pointer_null].
          sep_apply (hk5o1a_pool_valid Tsh t T (ke_addr e2) (proj1 (Hkin e2 He2))). entailer!. }
        Exists true. entailer!.
        split; [intros _; split; [discriminate |] |].
        { match goal with Hm: Int64.unsigned (Int64.repr 0) < _ |- _ =>
            rewrite !Int64.unsigned_repr in Hm by rep_lia; lia end. }
        destruct (ke_addr e2); try contradiction; reflexivity.
    - forward. Exists false. entailer!.
    - Intros c.
      match goal with Hx: c = true -> _ |- _ => rename Hx into Hc end.
      forward_if.
      2: { forward. Exists pre e suf. entailer!. }
      destruct c; [| match goal with Hx: typed_true _ _ |- _ => inv Hx end].
      destruct (Hc eq_refl) as [Hsuf Hmm].
      destruct suf as [|e2 suf2]; [contradiction|].
      pose proof (hk5o1a_hd_suf _ _ _ _ Hl Hfc) as Hpns. cbn [hk5o1a_hd] in Hpns.
      sep_apply (hk5o1a_focus' (o_kd O) (o_KE O) pre e (e2 :: suf2) Hl). Intros.
      forward.
      sep_apply (wand_frame_elim (@field_at W_keypairs Ews t_kent (DOT HC._next) (hk5o1a_hd (e2 :: suf2)) (ke_addr e))
                  (kents_rep W_keypairs (o_kd O) (o_KE O))).
      cbn [hk5o1a_hd].
      forward.
      Exists (pre ++ [e]) e2 suf2 (mm - 1). entailer!.
      rewrite <- app_assoc. auto. }
  Intros pre e suf.
  match goal with Hx: o_KE O = pre ++ e :: suf |- _ => rename Hx into Hl end.
  assert (He: In e (o_KE O)) by (rewrite Hl; apply in_or_app; right; left; reflexivity).
  destruct (Hkin e He) as [HeT HeKS].
  assert (Hfce: @field_compatible CKS t_kent [] (ke_addr e)) by (rewrite Forall_forall in Hfc; auto).
  set (D := hkp5_D x25519 F0 V) in *.
  pose proof Hinv as (_ & _ & Hdev & _). cbn [y_P f_w F0] in Hdev.
  change (itable Tsh t T) with (itable Tsh (d_itab D) T).
  assert (Pe: isptr (ke_addr e)) by (destruct Hfce as [Hp _]; exact Hp).
  pose proof HM as (Hpre & Hslots & _).
  pose proof (Hslots _ _ _ _ _ _ _ Hr0) as Hsok.
  pose proof Hr0 as (Hc0 & _).
  destruct (Hpre _ _ _ _ _ _ _ Hc0) as (Kp & _).
  forward_call (gv, S, ww, KS, T, Tsh, p, P, Tsh, w, D, Tsh, ke_addr e).
  assert (Nk: ke_addr e <> p_next P).
  { intros E. pose proof Hsok as (Hs1 & _). rewrite Forall_forall in Hs1.
    destruct (Hs1 (p_next P) ltac:(right; right; left; reflexivity)) as [Hn | Hn].
    - rewrite <- E in Hn. rewrite Hn in Pe. exact Pe.
    - rewrite <- E in Hn. exact (HeKS Hn). }
  assert (Ern: received_with_keypair_model P (ke_addr e) (mkKW KS T S) = (false, P, mkKW KS T S)).
  { unfold received_with_keypair_model. rewrite if_false by exact Nk. reflexivity. }
  assert (Erw: received_with_keypair_warn P (ke_addr e) (mkKW KS T S) ww = ww).
  { unfold received_with_keypair_warn. rewrite if_false by exact Nk. reflexivity. }
  rewrite Ern, Erw. cbn [fst snd kw_S kw_KS kw_T].
  change (itable Tsh (d_itab D) T) with (itable Tsh t T).
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward_if.
    { forward_call tt. { match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
      apply ENTAIL_refl. }
    forward. apply ENTAIL_refl. }
  { forward. apply ENTAIL_refl. }
  set (Y0 := mkKY5 S ww kc P KS T (mkH5 ML sp sc sn fr mw) now next_id id_known hsn).
  lazymatch goal with |- semax _ (PROPx _ (LOCALx ?Q0 _)) _ _ =>
    apply semax_pre with (PROPx [] (LOCALx Q0
      (SEPx [fold_right_sepcon (hkp5_SEP x25519 F0 V Y0 (hkp5_othR x25519 F0 V O)); FR]))) end.
  { subst Y0 D. unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_othR, hkp5_oth_rep.
    cbn [app fold_right_sepcon f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second F0 y_S y_w y_kc
         y_P y_KS y_T y_H y_now y_next_id y_id_known y_hsn h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn].
    entailer!. }
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward_call (F0, V, Y0, O).
    forward_if.
    { exfalso. match goal with Hc: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  forward.
  match goal with |- _ |-- hkp5_Icont _ _ _ _ (?X * FR) _ =>
    replace X with (hkp5_othR x25519 F0 V O)
      by (unfold hkp5_othR, hkp5_oth_rep; cbn [fold_right_sepcon]; rewrite sepcon_emp; reflexivity) end.
  unfold hkp5_Icont, hkp5_St. Exists Y0.
  rewrite hk5o1a_SEPx. unfold hkp5_temps, hkp5_lvars. cbn [app].
  subst Y0. cbn [y_now y_next_id y_id_known f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second F0].
  entailer!.
Qed.
