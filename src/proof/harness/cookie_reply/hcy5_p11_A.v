(* law cookie_reply: phase P11, segment A (statements 66..67): target = NULL; the walk of ita.
   cookie_reply/hcy4_p11_A.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require WgNoise.harness.x_cookie_reply.code.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p11_defs.

Require Import WgNoise.proof.protocol.prot_body3_shim_table1.
Require Import WgNoise.proof.protocol.prot3_shim_table2_ilookup.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

(* ---- helpers (prefix hcy5_p11_A_; copies of hcy5_p9_BB's at this segment) ---- *)
#[local] Instance hcy5_p11_A_cceN : change_composite_env Noise.CS W_cookie_reply.
Proof. make_cs_preserve Noise.CS W_cookie_reply. Defined.
#[local] Instance hcy5_p11_A_cceC : change_composite_env Cookie.CS W_cookie_reply.
Proof. make_cs_preserve Cookie.CS W_cookie_reply. Defined.

(* the reply at the world *)
Lemma hcy5_p11_A_cmsg_W sh p M :
  cmsg_rep sh p M = !! cm_ok M && @data_at W_cookie_reply sh t_cmsg (cmsg_val M) p.
Proof.
  unfold cmsg_rep. f_equal.
  rewrite (@data_at_change_composite Cookie.CS W_cookie_reply hcy5_p11_A_cceC sh t_cmsg
    (cmsg_val M) (cmsg_val M) (JMeq_refl _) eq_refl). reflexivity.
Qed.

Lemma hcy5_p11_A_itab_W sh (v: val) p :
  @data_at Noise.CS sh t_itab v p = @data_at W_cookie_reply sh t_itab v p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W_cookie_reply hcy5_p11_A_cceN sh t_itab v v (JMeq_refl _) eq_refl).
  reflexivity.
Qed.

Lemma hcy5_p11_A_entry_W sh a E nx h :
  entry_at sh a E nx h = @data_at W_cookie_reply sh t_entry_s (entry_val E nx h) a.
Proof.
  unfold entry_at.
  rewrite (@data_at_change_composite Noise.CS W_cookie_reply hcy5_p11_A_cceN sh t_entry_s
    (entry_val E nx h) (entry_val E nx h) (JMeq_refl _) eq_refl). reflexivity.
Qed.

(* the table with its head at the world *)
Lemma hcy5_p11_A_open0 sht tab T :
  itable sht tab T |--
  !! itable_wf T &&
  (@data_at W_cookie_reply sht t_itab (hd nullval (t_L T)) tab * iter_sepcon (pool_item_rep (t_L T)) (t_D T)).
Proof. unfold itable. rewrite hcy5_p11_A_itab_W. entailer!. Qed.

Lemma hcy5_p11_A_close0 sht tab T : itable_wf T ->
  @data_at W_cookie_reply sht t_itab (hd nullval (t_L T)) tab * iter_sepcon (pool_item_rep (t_L T)) (t_D T)
  |-- itable sht tab T.
Proof. intros. unfold itable. rewrite hcy5_p11_A_itab_W. entailer!. Qed.

(* the table with the entry at a (in the list) focused at the world *)
Lemma hcy5_p11_A_open sht tab T a sh E : sfind (t_D T) a = Some (sh, E) -> In a (t_L T) ->
  itable sht tab T |--
  !! (itable_wf T /\ writable_share sh) &&
  (@data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab * iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) a) *
   @data_at W_cookie_reply sh t_entry_s (entry_val E (succ_in (t_L T) a) true) a).
Proof.
  intros Hs HL. unfold itable. Intros.
  assert (WS: writable_share sh).
  { destruct H as (_ & _ & _ & H4). apply prot_rep3_sfind_In in Hs. rewrite Forall_forall in H4.
    apply (H4 _ Hs). }
  rewrite (prot_rep3_split _ _ _ _ _ Hs).
  change (pool_item_rep (t_L T) (a, sh, E)) with (entry_at sh a E (succ_in (t_L T) a) (vin a (t_L T))).
  assert (Hv: vin a (t_L T) = true) by (unfold vin; destruct (in_dec eq_dec a (t_L T)); [reflexivity|contradiction]).
  rewrite Hv, hcy5_p11_A_entry_W. entailer!.
Qed.

Lemma hcy5_p11_A_close sht tab T a sh E : sfind (t_D T) a = Some (sh, E) -> In a (t_L T) -> itable_wf T ->
  @data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab * iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) a) *
  @data_at W_cookie_reply sh t_entry_s (entry_val E (succ_in (t_L T) a) true) a
  |-- itable sht tab T.
Proof.
  intros Hs HL WF. unfold itable.
  rewrite (prot_rep3_split _ _ _ _ _ Hs).
  change (pool_item_rep (t_L T) (a, sh, E)) with (entry_at sh a E (succ_in (t_L T) a) (vin a (t_L T))).
  assert (Hv: vin a (t_L T) = true) by (unfold vin; destruct (in_dec eq_dec a (t_L T)); [reflexivity|contradiction]).
  rewrite Hv, hcy5_p11_A_entry_W. entailer!.
Qed.

(* the table with the entry at a focused at the world, its next field = the next address of the list *)
Lemma hcy5_p11_A_open2 sht tab T L1 a L2 sh E : t_L T = L1 ++ a :: L2 -> sfind (t_D T) a = Some (sh, E) ->
  itable sht tab T |--
  !! (itable_wf T /\ writable_share sh) &&
  (@data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab * iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) a) *
   @data_at W_cookie_reply sh t_entry_s (e_peer E, (hd nullval L2, (Vint Int.one, (Vint (e_type E), Vint (e_index E))))) a).
Proof.
  intros HL Hs.
  assert (HinL: In a (t_L T)) by (rewrite HL; apply in_or_app; simpl; auto).
  assert_PROP (itable_wf T) as HW by (unfold itable; entailer!).
  assert (HS: succ_in (t_L T) a = hd nullval L2).
  { rewrite HL. apply prot3_shim_table1_succ. rewrite <- HL. apply HW. }
  sep_apply (hcy5_p11_A_open sht tab T a sh E Hs HinL). rewrite HS. apply derives_refl.
Qed.

Lemma hcy5_p11_A_close2 sht tab T L1 a L2 sh E : t_L T = L1 ++ a :: L2 -> sfind (t_D T) a = Some (sh, E) ->
  itable_wf T ->
  @data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab * iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) a) *
  @data_at W_cookie_reply sh t_entry_s (e_peer E, (hd nullval L2, (Vint Int.one, (Vint (e_type E), Vint (e_index E))))) a
  |-- itable sht tab T.
Proof.
  intros HL Hs HW.
  assert (HinL: In a (t_L T)) by (rewrite HL; apply in_or_app; simpl; auto).
  assert (HS: succ_in (t_L T) a = hd nullval L2).
  { rewrite HL. apply prot3_shim_table1_succ. rewrite <- HL. apply HW. }
  rewrite <- HS. apply (hcy5_p11_A_close sht tab T a sh E Hs HinL HW).
Qed.

(* any suffix's head is a valid pointer *)
Lemma hcy5_p11_A_vp sht tab T L1 L2 : t_L T = L1 ++ L2 -> itable sht tab T |-- valid_pointer (hd nullval L2).
Proof.
  intros HL. destruct L2 as [|a L2]; simpl; [apply valid_pointer_null|].
  assert_PROP (itable_wf T) as HW by (unfold itable; entailer!).
  apply prot3_shim_table1_valid. eapply prot3_shim_table1_inL; eauto.
Qed.

Lemma hcy5_p11_A_isptr sht tab T L1 a L2 : t_L T = L1 ++ a :: L2 -> itable sht tab T |-- !! isptr a.
Proof.
  intros HL. assert_PROP (itable_wf T) as HW by (unfold itable; entailer!).
  apply prot3_shim_table1_isptr. eapply prot3_shim_table1_inL; eauto.
Qed.

(* the model: the walk stops at the first entry with the index *)
Lemma hcy5_p11_A_walk_nil T L1 idx :
  t_L T = L1 ++ [] -> ~ In idx (t_indices T L1) -> hcy5_p11_ewalk T idx = nullval.
Proof.
  intros HL HI. unfold hcy5_p11_ewalk. rewrite HL, prot3_ilookup_find_app by auto. reflexivity.
Qed.

Lemma hcy5_p11_A_walk_found T L1 a L2 idx sh E :
  t_L T = L1 ++ a :: L2 -> ~ In idx (t_indices T L1) -> sfind (t_D T) a = Some (sh, E) -> e_index E = idx ->
  hcy5_p11_ewalk T idx = a.
Proof.
  intros HL HI HE Hi. unfold hcy5_p11_ewalk. rewrite HL, prot3_ilookup_find_app by auto. simpl.
  rewrite (prot3_shim_table1_tentry _ _ _ _ HE). rewrite Hi, Int.eq_true. reflexivity.
Qed.

Section Phase.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_p11_A_ok {Espec: OracleKind} gv L FR :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcy5_S10 x25519 xaead_enc xaead_dec gv L FR) hcy5_p11_sA
    (overridePost (hcy5_p11_TA x25519 xaead_enc xaead_dec gv L FR) (hcy5_R gv)).

Proof.
  intros HH. unfold hcy5_S10, hcy5_Delta, hcy5_R, hcy5_p11_sA.
  simplify_func_tycontext. abbreviate_semax.
  Intros R S m c rp Q nonce rr CK CM. Intros NS PS T np CL KE CM' honest now2.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_lvars; simpl app.
  forward.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
  assert_PROP (itable_wf T) as HW by (unfold itable; entailer!).
  assert_PROP (is_pointer_or_null (hd nullval (t_L T))) as Hhd.
  { sep_apply (prot3_shim_table1_hd Tsh (l_ita L) T [] (t_L T) eq_refl). entailer!. }
  sep_apply (hcy5_p11_A_open0 Tsh (l_ita L) T). Intros.
  forward.
  sep_apply (hcy5_p11_A_close0 Tsh (l_ita L) T HW).
  rewrite hcy5_p11_A_cmsg_W. Intros.
  set (idx := cm_receiver CM').
  match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?Lc) (SEPx ?Sp))) _ _ =>
  forward_loop (EX L1: list val, EX L2: list val,
      PROPx [t_L T = L1 ++ L2; ~ In idx (t_indices T L1)]
      (LOCALx (temp HY._e (hd nullval L2) :: Lc) (SEPx Sp)))
    continue: (EX L1: list val, EX a: val, EX L2: list val,
      PROPx [t_L T = L1 ++ a :: L2; ~ In idx (t_indices T (L1 ++ [a]))]
      (LOCALx (temp HY._e a :: Lc) (SEPx Sp)))
    break: (PROPx [] (LOCALx (temp HY._e (hcy5_p11_ewalk T idx) :: Lc) (SEPx Sp))) end.
  { Exists (@nil val) (t_L T). entailer!. }
  { (* the test *)
    Intros L1 L2.
    match goal with Hx: t_L T = _ ++ _ |- _ => rename Hx into HL end.
    match goal with Hx: ~ In idx _ |- _ => rename Hx into HI end.
    destruct L2 as [|a L2].
    { (* end of the list *)
      simpl hd.
      match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
        forward_if (PROPx P (LOCALx (temp HY._t'46 (Vint Int.zero) :: Lc) (SEPx Sp))) end.
      { discriminate. }
      { forward. entailer!. }
      forward_if.
      { exfalso. first [discriminate | congruence | lia]. }
      forward. entailer!. rewrite (hcy5_p11_A_walk_nil T L1 idx HL HI). reflexivity. }
    assert (Ha: In a (saddrs (t_D T))) by (eapply prot3_shim_table1_inL; eauto).
    destruct (prot3_shim_table1_sfind_in _ _ Ha) as (sh & E & HE).
    assert_PROP (isptr a) as Hpa.
    { sep_apply (hcy5_p11_A_isptr Tsh (l_ita L) T L1 a L2 HL). entailer!. }
    assert (VP := hcy5_p11_A_vp Tsh (l_ita L) T L1 (a :: L2) HL). simpl in VP.
    simpl hd.
    destruct (Int.eq (e_index E) idx) eqn:Heq.
    { (* found: break *)
      match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
        forward_if (PROPx P (LOCALx (temp HY._t'46 (Vint Int.zero) :: Lc) (SEPx Sp))) end.
      { sep_apply (hcy5_p11_A_open2 Tsh (l_ita L) T L1 a L2 sh E HL HE). Intros.
        forward.
        sep_apply (hcy5_p11_A_close2 Tsh (l_ita L) T L1 a L2 sh E HL HE HW).
        forward. forward. unfold idx in Heq. rewrite Heq. entailer!. }
      { exfalso. subst a. contradiction. }
      forward_if.
      { exfalso. first [discriminate | congruence | lia]. }
      forward. entailer!. apply Int.same_if_eq in Heq.
      rewrite (hcy5_p11_A_walk_found T L1 a L2 idx sh E HL HI HE Heq). reflexivity. }
    { (* not found: go on *)
      match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
        forward_if (PROPx P (LOCALx (temp HY._t'46 (Vint Int.one) :: Lc) (SEPx Sp))) end.
      { sep_apply (hcy5_p11_A_open2 Tsh (l_ita L) T L1 a L2 sh E HL HE). Intros.
        forward.
        sep_apply (hcy5_p11_A_close2 Tsh (l_ita L) T L1 a L2 sh E HL HE HW).
        forward. forward. unfold idx in Heq. rewrite Heq. entailer!. }
      { exfalso. subst a. contradiction. }
      forward_if.
      { assert (HI2: ~ In idx (t_indices T (L1 ++ [a]))).
        { apply (prot3_shim_table1_ind_snoc T L1 a sh E idx HE HI).
          intro Hx. rewrite Hx, Int.eq_true in Heq. discriminate. }
        forward. Exists L1 a L2. entailer!. }
      { exfalso. first [discriminate | congruence | lia]. } } }
  { (* e = e->next *)
    Intros L1 a L2.
    match goal with Hx: t_L T = _ ++ _ :: _ |- _ => rename Hx into HL end.
    match goal with Hx: ~ In idx _ |- _ => rename Hx into HI end.
    assert (Ha: In a (saddrs (t_D T))) by (eapply prot3_shim_table1_inL; eauto).
    destruct (prot3_shim_table1_sfind_in _ _ Ha) as (sh & E & HE).
    assert (HL': t_L T = (L1 ++ [a]) ++ L2) by (rewrite HL, <- app_assoc; reflexivity).
    assert_PROP (is_pointer_or_null (hd nullval L2)) as Hp2.
    { sep_apply (prot3_shim_table1_hd Tsh (l_ita L) T (L1 ++ [a]) L2 HL'). entailer!. }
    sep_apply (hcy5_p11_A_open2 Tsh (l_ita L) T L1 a L2 sh E HL HE). Intros.
    forward.
    sep_apply (hcy5_p11_A_close2 Tsh (l_ita L) T L1 a L2 sh E HL HE HW).
    Exists (L1 ++ [a]) L2. entailer!. }
  (* after the walk: TA *)
  unfold POSTCONDITION, abbreviate. simpl_ret_assert. unfold hcy5_p11_TA.
  Exists R S m c rp Q nonce rr CK CM. Exists NS PS T np CL KE CM' honest now2.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_lvars; simpl app.
  rewrite hcy5_p11_A_cmsg_W. entailer!.
Qed.

End Phase.
