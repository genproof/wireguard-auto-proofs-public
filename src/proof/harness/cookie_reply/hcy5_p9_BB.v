(* law cookie_reply, phase P9, segment BB.  fill_cookie_msg(reply); maybe walk ita's list and take some entry's index (mode 2).
   Port of v1's *)
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
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p9_defs.
Require WgNoise.harness.x_cookie_reply.code.
Require Import WgNoise.proof.protocol.prot_body3_shim_table1.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

(* ---- helpers (prefix hcy5_p9_BB_) ---- *)
#[local] Instance hcy5_p9_BB_cceN : change_composite_env Noise.CS W_cookie_reply.
Proof. make_cs_preserve Noise.CS W_cookie_reply. Defined.
#[local] Instance hcy5_p9_BB_cceC : change_composite_env Cookie.CS W_cookie_reply.
Proof. make_cs_preserve Cookie.CS W_cookie_reply. Defined.

(* the reply, as fill_cookie_msg's precondition *)
Lemma hcy5_p9_BB_cmsg_ sh p M : cmsg_rep sh p M |-- @data_at_ Cookie.CS sh t_cmsg p.
Proof. unfold cmsg_rep. Intros. apply data_at_data_at_. Qed.

(* the reply at the world *)
Lemma hcy5_p9_BB_cmsg_W sh p M :
  cmsg_rep sh p M = !! cm_ok M && @data_at W_cookie_reply sh t_cmsg (cmsg_val M) p.
Proof.
  unfold cmsg_rep. f_equal.
  rewrite (@data_at_change_composite Cookie.CS W_cookie_reply hcy5_p9_BB_cceC sh t_cmsg
    (cmsg_val M) (cmsg_val M) (JMeq_refl _) eq_refl). reflexivity.
Qed.

(* the reply after the store of the receiver index *)
Lemma hcy5_p9_BB_cmsg_close sh p M idx : cm_ok M ->
  @data_at W_cookie_reply sh t_cmsg (fst (cmsg_val M), (Vint idx, snd (snd (cmsg_val M)))) p
  |-- cmsg_rep sh p (hcy5_p9_rcv M idx).
Proof.
  intros OK. rewrite hcy5_p9_BB_cmsg_W. apply andp_right; [apply prop_right; exact OK | apply derives_refl].
Qed.

Lemma hcy5_p9_BB_itab_W sh (v: val) p :
  @data_at Noise.CS sh t_itab v p = @data_at W_cookie_reply sh t_itab v p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W_cookie_reply hcy5_p9_BB_cceN sh t_itab v v (JMeq_refl _) eq_refl).
  reflexivity.
Qed.

Lemma hcy5_p9_BB_entry_W sh a E nx h :
  entry_at sh a E nx h = @data_at W_cookie_reply sh t_entry_s (entry_val E nx h) a.
Proof.
  unfold entry_at.
  rewrite (@data_at_change_composite Noise.CS W_cookie_reply hcy5_p9_BB_cceN sh t_entry_s
    (entry_val E nx h) (entry_val E nx h) (JMeq_refl _) eq_refl). reflexivity.
Qed.

(* the table with its head at the world *)
Lemma hcy5_p9_BB_open0 sht tab T :
  itable sht tab T |--
  !! itable_wf T &&
  (@data_at W_cookie_reply sht t_itab (hd nullval (t_L T)) tab * iter_sepcon (pool_item_rep (t_L T)) (t_D T)).
Proof. unfold itable. rewrite hcy5_p9_BB_itab_W. entailer!. Qed.

Lemma hcy5_p9_BB_close0 sht tab T : itable_wf T ->
  @data_at W_cookie_reply sht t_itab (hd nullval (t_L T)) tab * iter_sepcon (pool_item_rep (t_L T)) (t_D T)
  |-- itable sht tab T.
Proof. intros. unfold itable. rewrite hcy5_p9_BB_itab_W. entailer!. Qed.

(* the table with the entry at a (in the list) focused at the world *)
Lemma hcy5_p9_BB_open sht tab T a sh E : sfind (t_D T) a = Some (sh, E) -> In a (t_L T) ->
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
  rewrite Hv, hcy5_p9_BB_entry_W. entailer!.
Qed.

Lemma hcy5_p9_BB_close sht tab T a sh E : sfind (t_D T) a = Some (sh, E) -> In a (t_L T) -> itable_wf T ->
  @data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab * iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) a) *
  @data_at W_cookie_reply sh t_entry_s (entry_val E (succ_in (t_L T) a) true) a
  |-- itable sht tab T.
Proof.
  intros Hs HL WF. unfold itable.
  rewrite (prot_rep3_split _ _ _ _ _ Hs).
  change (pool_item_rep (t_L T) (a, sh, E)) with (entry_at sh a E (succ_in (t_L T) a) (vin a (t_L T))).
  assert (Hv: vin a (t_L T) = true) by (unfold vin; destruct (in_dec eq_dec a (t_L T)); [reflexivity|contradiction]).
  rewrite Hv, hcy5_p9_BB_entry_W. entailer!.
Qed.

(* the table with the entry at a focused at the world, its next field = the next address of the list *)
Lemma hcy5_p9_BB_open2 sht tab T L1 a L2 sh E : t_L T = L1 ++ a :: L2 -> sfind (t_D T) a = Some (sh, E) ->
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
  sep_apply (hcy5_p9_BB_open sht tab T a sh E Hs HinL). rewrite HS. apply derives_refl.
Qed.

Lemma hcy5_p9_BB_close2 sht tab T L1 a L2 sh E : t_L T = L1 ++ a :: L2 -> sfind (t_D T) a = Some (sh, E) ->
  itable_wf T ->
  @data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab * iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) a) *
  @data_at W_cookie_reply sh t_entry_s (e_peer E, (hd nullval L2, (Vint Int.one, (Vint (e_type E), Vint (e_index E))))) a
  |-- itable sht tab T.
Proof.
  intros HL Hs HW.
  assert (HinL: In a (t_L T)) by (rewrite HL; apply in_or_app; simpl; auto).
  assert (HS: succ_in (t_L T) a = hd nullval L2).
  { rewrite HL. apply prot3_shim_table1_succ. rewrite <- HL. apply HW. }
  rewrite <- HS. apply (hcy5_p9_BB_close sht tab T a sh E Hs HinL HW).
Qed.

(* any suffix's head is a valid pointer *)
Lemma hcy5_p9_BB_vp sht tab T L1 L2 : t_L T = L1 ++ L2 -> itable sht tab T |-- valid_pointer (hd nullval L2).
Proof.
  intros HL. destruct L2 as [|a L2]; simpl; [apply valid_pointer_null|].
  assert_PROP (itable_wf T) as HW by (unfold itable; entailer!).
  apply prot3_shim_table1_valid. eapply prot3_shim_table1_inL; eauto.
Qed.

Lemma hcy5_p9_BB_isptr sht tab T L1 a L2 : t_L T = L1 ++ a :: L2 -> itable sht tab T |-- !! isptr a.
Proof.
  intros HL. assert_PROP (itable_wf T) as HW by (unfold itable; entailer!).
  apply prot3_shim_table1_isptr. eapply prot3_shim_table1_inL; eauto.
Qed.

(* the head of the list (NULL or a pool entry) is a valid pointer *)
Lemma hcy5_p9_BB_vp_hd sht tab T : itable sht tab T |-- valid_pointer (hd nullval (t_L T)).
Proof.
  destruct (t_L T) as [|a L'] eqn:HL; simpl; [apply valid_pointer_null|].
  assert_PROP (itable_wf T) as HW by (unfold itable; entailer!).
  apply prot3_shim_table1_valid. eapply prot3_shim_table1_inL with (L1 := []); eauto.
Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_p9_BB_ok {Espec: OracleKind} gv L FR R S m c rp Q nonce rr CK CM NS PS T np CL KE :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hcy5_p9_inv x25519 xaead_enc R L Q m nonce rr CK CM NS PS T np CL KE ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hcy5_p9_PA x25519 gv L FR R S m c rp Q rr CK NS PS T np CL KE CM 2 [] [])
    hcy5_p9_BB
    (normal_ret_assert (hcy5_p9_Q1 x25519 xaead_enc gv L FR R m c rp Q nonce rr CK CM NS np CL KE)).
Proof.
  intros HH Hinv. unfold hcy5_Delta, hcy5_p9_PA, hcy5_p9_loc, hcy5_p9_sep, hcy5_p9_BB.
  simplify_func_tycontext. abbreviate_semax.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs, hcy5_lvars; simpl app.
  assert_PROP (itable_wf T) as HW by (unfold itable; entailer!).
  sep_apply (hcy5_p9_BB_cmsg_ Ews rp CM).
  forward_call (Ews, rp).
  Intros M.
  assert_PROP (is_pointer_or_null (hd nullval (t_L T))) as Hhd.
  { sep_apply (prot3_shim_table1_hd Tsh (l_ita L) T [] (t_L T) eq_refl). entailer!. }
  sep_apply (hcy5_p9_BB_open0 Tsh (l_ita L) T). Intros.
  forward.
  sep_apply (hcy5_p9_BB_close0 Tsh (l_ita L) T HW).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
    forward_if (EX b: bool, PROPx ((b = true -> t_L T <> []) :: P)
      (LOCALx (temp HY._t'42 (Val.of_bool b) :: Lc) (SEPx Sp))) end.
  { apply denote_tc_test_eq_split; [| apply valid_pointer_null].
    repeat apply sepcon_valid_pointer1. apply hcy5_p9_BB_vp_hd. }
  { forward_call tt. Intros b45. forward.
    Exists (negb (Int.eq (Int.and (Int.repr b45) (Int.repr 1)) Int.zero)). entailer!.
    split.
    - intros _ Hn. rewrite Hn in H0. simpl in H0. contradiction.
    - match goal with |- context [Int.eq ?x Int.zero] => destruct (Int.eq x Int.zero) end; reflexivity. }
  { forward. Exists false. entailer!. }
  Intros b.
  forward_if.
  { destruct b; [| unfold typed_true in H1; simpl in H1; discriminate].
    specialize (H0 eq_refl).
    forward_call tt. Intros k0.
    sep_apply (hcy5_p9_BB_open0 Tsh (l_ita L) T). Intros.
    forward.
    sep_apply (hcy5_p9_BB_close0 Tsh (l_ita L) T HW).
    destruct (t_L T) as [|a0 L0] eqn:HL0; [contradiction|]. simpl hd.
    match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?Sp))) _ _ =>
    forward_loop (EX L1: list val, EX a: val, EX L2: list val,
        PROPx [t_L T = L1 ++ a :: L2; Zlength L1 <= k0]
        (LOCALx (hcy5_p9_loc gv L m c rp Q np CL KE [temp HY._e a;
                 temp HY._kk__1 (Vlong (Int64.repr (k0 - Zlength L1)));
                 temp HY._mode (Vint (Int.repr 2)); temp HY._honest (Vint Int.zero)]) (SEPx Sp)))
      continue: (EX L1: list val, EX a: val, EX L2: list val,
        PROPx [t_L T = L1 ++ a :: L2; L2 <> []; Zlength L1 < k0]
        (LOCALx (hcy5_p9_loc gv L m c rp Q np CL KE [temp HY._e a;
                 temp HY._kk__1 (Vlong (Int64.repr (k0 - Zlength L1 - 1)));
                 temp HY._mode (Vint (Int.repr 2)); temp HY._honest (Vint Int.zero)]) (SEPx Sp)))
      break: (EX a: val,
        PROPx [In a (t_L T)]
        (LOCALx (hcy5_p9_loc gv L m c rp Q np CL KE [temp HY._e a;
                 temp HY._mode (Vint (Int.repr 2)); temp HY._honest (Vint Int.zero)]) (SEPx Sp))) end.
    { Exists (@nil val) a0 L0. unfold hcy5_p9_loc, hcy5_lvars; simpl app. entailer!. rewrite Zlength_nil; lia. }
    { (* the test *)
      Intros L1 a L2. unfold hcy5_p9_loc, hcy5_lvars; simpl app.
      match goal with Hx: t_L T = _ ++ _ :: _ |- _ => rename Hx into HL end.
      assert (Ha: In a (saddrs (t_D T))) by (eapply prot3_shim_table1_inL; eauto).
      destruct (prot3_shim_table1_sfind_in _ _ Ha) as (sh & E & HE).
      assert (HL': t_L T = (L1 ++ [a]) ++ L2) by (rewrite HL, <- app_assoc; reflexivity).
      assert (VP := hcy5_p9_BB_vp Tsh (l_ita L) T (L1 ++ [a]) L2 HL').
      assert_PROP (is_pointer_or_null (hd nullval L2)) as Hp2.
      { sep_apply (prot3_shim_table1_hd Tsh (l_ita L) T (L1 ++ [a]) L2 HL'). entailer!. }
      sep_apply (hcy5_p9_BB_open2 Tsh (l_ita L) T L1 a L2 sh E HL HE). Intros.
      forward.
      sep_apply (hcy5_p9_BB_close2 Tsh (l_ita L) T L1 a L2 sh E HL HE HW).
      destruct L2 as [|b L2'].
      { (* the last entry: break *)
        simpl hd.
        match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
          forward_if (PROPx P (LOCALx (temp HY._t'41 (Vint Int.zero) :: Lc) (SEPx Sp))) end.
        { discriminate. }
        { forward. entailer!. }
        forward_if.
        { exfalso. first [discriminate | congruence | lia]. }
        forward. Exists a. unfold hcy5_p9_loc, hcy5_lvars; simpl app. entailer!.
        rewrite HL. apply in_or_app. simpl; auto. }
      assert_PROP (isptr b) as Hpb.
      { sep_apply (hcy5_p9_BB_isptr Tsh (l_ita L) T (L1 ++ [a]) b L2' HL'). entailer!. }
      simpl hd.
      destruct (Z_lt_le_dec (Zlength L1) k0) as [Hlt|Hge].
      { (* kk > 0: go on *)
        match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
          forward_if (PROPx P (LOCALx (temp HY._t'41 (Vint Int.one) :: Lc) (SEPx Sp))) end.
        { forward. entailer!. pose proof (Zlength_nonneg L1).
          unfold Int64.cmpu, Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
          rewrite zlt_true by lia. reflexivity. }
        { exfalso. subst b. contradiction. }
        forward_if.
        2: { exfalso. first [discriminate | congruence | lia]. }
        forward.
        pose proof (Zlength_nonneg L1).
        assert (Hkk: Int64.sub (Int64.repr (k0 - Zlength L1)) (Int64.repr (Int.signed (Int.repr 1))) =
                     Int64.repr (k0 - Zlength L1 - 1)).
        { unfold Int64.sub. rewrite (Int64.unsigned_repr (k0 - Zlength L1)) by rep_lia.
          change (Int.signed (Int.repr 1)) with 1. rewrite (Int64.unsigned_repr 1) by rep_lia. reflexivity. }
        rewrite Hkk.
        Exists L1 a (b :: L2'). unfold hcy5_p9_loc, hcy5_lvars; simpl app. entailer!. }
      { (* kk = 0: break *)
        match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
          forward_if (PROPx P (LOCALx (temp HY._t'41 (Vint Int.zero) :: Lc) (SEPx Sp))) end.
        { forward. entailer!. pose proof (Zlength_nonneg L1).
          unfold Int64.cmpu, Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
          rewrite zlt_false by lia. reflexivity. }
        { exfalso. subst b. contradiction. }
        forward_if.
        { exfalso. first [discriminate | congruence | lia]. }
        forward. Exists a. unfold hcy5_p9_loc, hcy5_lvars; simpl app. entailer!.
        rewrite HL. apply in_or_app. simpl; auto. } }
    { (* e = e->next *)
      Intros L1 a L2. unfold hcy5_p9_loc, hcy5_lvars; simpl app.
      match goal with Hx: t_L T = _ ++ _ :: _ |- _ => rename Hx into HL end.
      destruct L2 as [|b L2']; [congruence|].
      assert (Ha: In a (saddrs (t_D T))) by (eapply prot3_shim_table1_inL; eauto).
      destruct (prot3_shim_table1_sfind_in _ _ Ha) as (sh & E & HE).
      assert (HL': t_L T = (L1 ++ [a]) ++ b :: L2') by (rewrite HL, <- app_assoc; reflexivity).
      assert_PROP (isptr b) as Hpb.
      { sep_apply (hcy5_p9_BB_isptr Tsh (l_ita L) T (L1 ++ [a]) b L2' HL'). entailer!. }
      sep_apply (hcy5_p9_BB_open2 Tsh (l_ita L) T L1 a (b :: L2') sh E HL HE). Intros.
      forward.
      sep_apply (hcy5_p9_BB_close2 Tsh (l_ita L) T L1 a (b :: L2') sh E HL HE HW).
      Exists (L1 ++ [a]) b L2'. unfold hcy5_p9_loc, hcy5_lvars; simpl app.
      replace (k0 - Zlength (L1 ++ [a])) with (k0 - Zlength L1 - 1)
        by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
      entailer!. rewrite Zlength_app, Zlength_cons, Zlength_nil; lia. }
    (* after the walk: the receiver index *)
    Intros a. unfold hcy5_p9_loc, hcy5_lvars; simpl app.
    match goal with Hx: In a (t_L T) |- _ => rename Hx into Hin end.
    destruct (in_split _ _ Hin) as (L1 & L2 & HL).
    assert (Ha: In a (saddrs (t_D T))) by (eapply prot3_shim_table1_inL; eauto).
    destruct (prot3_shim_table1_sfind_in _ _ Ha) as (sh & E & HE).
    sep_apply (hcy5_p9_BB_open2 Tsh (l_ita L) T L1 a L2 sh E HL HE). Intros.
    forward.
    sep_apply (hcy5_p9_BB_close2 Tsh (l_ita L) T L1 a L2 sh E HL HE HW).
    rewrite hcy5_p9_BB_cmsg_W. Intros.
    forward.
    sep_apply (hcy5_p9_BB_cmsg_close Ews rp M (e_index E) H).
    unfold hcy5_p9_Q1. Exists S PS T (hcy5_p9_rcv M (e_index E)) false.
    unfold hcy5_p9_loc, hcy5_p9_sep, hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs, hcy5_snaps0,
      hcy5_lvars; simpl app.
    entailer!. }
  { (* no change of the receiver index *)
    forward.
    unfold hcy5_p9_Q1. Exists S PS T M false.
    unfold hcy5_p9_loc, hcy5_p9_sep, hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs, hcy5_snaps0,
      hcy5_lvars; simpl app.
    entailer!. }
Qed.

End Seg.
