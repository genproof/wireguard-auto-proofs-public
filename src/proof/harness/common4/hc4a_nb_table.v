(* a copy of hc3_body_table.v at the compspecs without blake2s_ctx (hc4a_nb_cs.v), for
   law handshake_clear's unit. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.blake2s.b2s_spec3.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4a_nb_cs.
Require Import WgNoise.proof.harness.common.hc3_ctx.
Require WgNoise.harness.x_handshake.code WgNoise.harness.x_cookie_reply.code WgNoise.harness.x_consume_response_any.code
        WgNoise.harness.x_keypairs.code WgNoise.harness.x_create_any.code WgNoise.harness.x_replay.code
        WgNoise.harness.x_cookie_mac.code WgNoise.harness.x_consume_initiation_any.code.
Require WgNoise.contracts.x_cookie_reply.

Module FH := WgNoise.harness.x_handshake.code.
(* ---- helpers (group table): the index table's pool at CSknb ---- *)
Local Open Scope logic.
Local Notation iter_sepcon := VST.msl.iter_sepcon.iter_sepcon.

Section PoolT.
Context {A: Type}.

Lemma hc4nb_table_split (D: list (val * share * A)) a sh E (f: val * share * A -> mpred) :
  sfind D a = Some (sh, E) -> iter_sepcon f D = f (a, sh, E) * iter_sepcon f (sdel D a).
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; reflexivity|].
  rewrite (IH H); simpl. rewrite <- !sepcon_assoc, (sepcon_comm (f _) (f _)). reflexivity.
Qed.

Lemma hc4nb_table_sfind_in (D: list (val * share * A)) a :
  In a (saddrs D) -> exists sh E, sfind D a = Some (sh, E).
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [contradiction|].
  destruct (EqDec_val x a); [eauto|]. destruct H; [congruence|auto].
Qed.

Lemma hc4nb_table_sfind_In (D: list (val * share * A)) a sh E :
  sfind D a = Some (sh, E) -> In (a, sh, E) D.
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; auto|auto].
Qed.

Lemma hc4nb_table_sfind_wr (D: list (val * share * A)) a sh E :
  Forall (fun x : val * share * A => let (y, _) := x in let (_, sh) := y in writable_share sh) D ->
  sfind D a = Some (sh, E) -> writable_share sh.
Proof.
  intros HF H. apply hc4nb_table_sfind_In in H.
  rewrite Forall_forall in HF. apply (HF _ H).
Qed.
End PoolT.

Section TabK.
#[local] Existing Instance CSknb.

#[local] Instance hc4nb_table_cce : change_composite_env Noise.CS CSknb.
Proof. make_cs_preserve Noise.CS CSknb. Defined.

Lemma hc4nb_table_entry_K sh v p :
  @data_at Noise.CS sh t_entry_s v p = @data_at CSknb sh t_entry_s v p.
Proof. exact (f_equal (fun f => f p) (@data_at_change_composite Noise.CS CSknb _ sh t_entry_s v v (JMeq_refl v) eq_refl)). Qed.

Lemma hc4nb_table_itab_K sh v p :
  @data_at Noise.CS sh t_itab v p = @data_at CSknb sh t_itab v p.
Proof. exact (f_equal (fun f => f p) (@data_at_change_composite Noise.CS CSknb _ sh t_itab v v (JMeq_refl v) eq_refl)). Qed.

Lemma hc4nb_table_valid sht tab T a :
  In a (saddrs (t_D T)) -> itable sht tab T |-- valid_pointer a.
Proof.
  intros Ha. destruct (hc4nb_table_sfind_in _ _ Ha) as (sh & E & HE).
  unfold itable. Intros. rewrite (hc4nb_table_split _ _ _ _ _ HE).
  assert (writable_share sh) by (destruct H as (_ & _ & _ & HF); eapply hc4nb_table_sfind_wr; eauto).
  unfold pool_item_rep, entry_at.
  apply sepcon_valid_pointer2. apply sepcon_valid_pointer1.
  apply data_at_valid_ptr; [auto | simpl; lia].
Qed.

Lemma hc4nb_table_open0 sht tab T :
  itable_wf T ->
  itable sht tab T =
  @data_at CSknb sht t_itab (hd nullval (t_L T)) tab * iter_sepcon (pool_item_rep (t_L T)) (t_D T).
Proof.
  intros. unfold itable. rewrite hc4nb_table_itab_K.
  apply pred_ext; entailer!.
Qed.

Lemma hc4nb_table_open sht tab T a sh E :
  itable_wf T -> sfind (t_D T) a = Some (sh, E) ->
  itable sht tab T =
  @data_at CSknb sht t_itab (hd nullval (t_L T)) tab *
  (@data_at CSknb sh t_entry_s (entry_val E (succ_in (t_L T) a) (vin a (t_L T))) a *
   iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) a)).
Proof.
  intros. rewrite hc4nb_table_open0 by auto.
  rewrite (hc4nb_table_split _ _ _ _ _ H0). unfold pool_item_rep at 1, entry_at.
  rewrite hc4nb_table_entry_K. reflexivity.
Qed.

Lemma hc4nb_table_isptr sht tab T a :
  In a (saddrs (t_D T)) -> itable sht tab T |-- !! isptr a.
Proof.
  intros Ha. destruct (hc4nb_table_sfind_in _ _ Ha) as (sh & E & HE).
  unfold itable. Intros. rewrite (hc4nb_table_split _ _ _ _ _ HE).
  unfold pool_item_rep, entry_at. entailer!.
  match goal with Hf: field_compatible t_entry_s [] a |- _ => destruct Hf; auto end.
Qed.

Lemma hc4nb_table_inL T L1 a L2 :
  itable_wf T -> t_L T = L1 ++ a :: L2 -> In a (saddrs (t_D T)).
Proof.
  intros HW HL. apply (proj1 (proj2 HW)). rewrite HL. apply in_or_app. simpl; auto.
Qed.

Lemma hc4nb_table_hd sht tab T L1 L2 :
  t_L T = L1 ++ L2 -> itable sht tab T |-- !! is_pointer_or_null (hd nullval L2).
Proof.
  intros HL. destruct L2 as [|a L2]; simpl; [entailer!|].
  assert_PROP (itable_wf T) as HW by (unfold itable; entailer!).
  sep_apply (hc4nb_table_isptr sht tab T a (hc4nb_table_inL _ _ _ _ HW HL)).
  entailer!.
Qed.

Lemma hc4nb_table_tc_hd sht tab T L1 L2 :
  t_L T = L1 ++ L2 -> itable sht tab T |-- denote_tc_test_eq (hd nullval L2) (Vlong Int64.zero).
Proof.
  intros HL. apply denote_tc_test_eq_split; [|apply valid_pointer_null].
  destruct L2 as [|a L2]; simpl; [apply valid_pointer_null|].
  assert_PROP (itable_wf T) as HW by (unfold itable; entailer!).
  apply hc4nb_table_valid. eapply hc4nb_table_inL; eauto.
Qed.

Lemma hc4nb_table_tc_eq sht tab T a b :
  In a (saddrs (t_D T)) -> In b (saddrs (t_D T)) -> itable sht tab T |-- denote_tc_test_eq a b.
Proof.
  intros Ha Hb. apply denote_tc_test_eq_split; apply hc4nb_table_valid; auto.
Qed.

Lemma hc4nb_table_succ L1 a L2 :
  NoDup (L1 ++ a :: L2) -> succ_in (L1 ++ a :: L2) a = hd nullval L2.
Proof.
  induction L1 as [|x L1 IH]; simpl; intros H.
  - destruct (EqDec_val a a); [reflexivity|congruence].
  - inv H. destruct (EqDec_val x a).
    + subst. exfalso. apply H2. apply in_or_app. simpl; auto.
    + auto.
Qed.

Lemma hc4nb_table_tentry T a sh E :
  sfind (t_D T) a = Some (sh, E) -> t_entry T a = Some E.
Proof. unfold t_entry. intros ->. reflexivity. Qed.

(* one step over the entry a = it: open, read, close *)
Lemma hc4nb_table_focus T L1 a L2 :
  itable_wf T -> t_L T = L1 ++ a :: L2 ->
  exists sh E, sfind (t_D T) a = Some (sh, E) /\ writable_share sh /\ succ_in (t_L T) a = hd nullval L2.
Proof.
  intros HW HL. destruct (hc4nb_table_sfind_in _ _ (hc4nb_table_inL _ _ _ _ HW HL)) as (sh & E & HE).
  exists sh, E. split; [auto|split].
  - destruct HW as (_ & _ & _ & HF); eapply hc4nb_table_sfind_wr; eauto.
  - rewrite HL. apply hc4nb_table_succ. rewrite <- HL. apply HW.
Qed.

End TabK.

(* ---- pure facts ---- *)
Lemma hc4nb_table_vin_true a L : vin a L = true <-> In a L.
Proof. unfold vin. destruct (in_dec _ a L); split; intros; auto; discriminate. Qed.

Lemma hc4nb_table_vin_false a L : vin a L = false <-> ~ In a L.
Proof. unfold vin. destruct (in_dec _ a L); split; intros; auto; try discriminate; contradiction. Qed.

Lemma hc4nb_table_vin_app_ne e L a :
  a <> e -> vin e (L ++ [a]) = vin e L.
Proof.
  intros Hne. destruct (vin e L) eqn:H.
  - apply hc4nb_table_vin_true. apply hc4nb_table_vin_true in H. apply in_or_app; auto.
  - apply hc4nb_table_vin_false. apply hc4nb_table_vin_false in H. intros Hin.
    apply in_app_or in Hin. destruct Hin as [Hin|[Hin|[]]]; [contradiction|congruence].
Qed.

Lemma hc4nb_table_vin_app_eq e L :
  vin e (L ++ [e]) = true.
Proof. apply hc4nb_table_vin_true. apply in_or_app; simpl; auto. Qed.

Lemma hc4nb_table_vin_notin e L1 L2 :
  NoDup (L1 ++ e :: L2) -> vin e L1 = false.
Proof.
  intros H. apply NoDup_remove_2 in H. apply hc4nb_table_vin_false.
  intros H'. apply H. apply in_or_app; auto.
Qed.

Definition hc4nb_table_cnt (T: tstate) (idx: int) (L: list val) : Z :=
  Zlength (filter (fun i => Int.eq i idx) (t_indices T L)).

Lemma hc4nb_table_cnt_app T idx L1 L2 :
  hc4nb_table_cnt T idx (L1 ++ L2) = hc4nb_table_cnt T idx L1 + hc4nb_table_cnt T idx L2.
Proof.
  unfold hc4nb_table_cnt, t_indices. rewrite map_app, filter_app, Zlength_app. reflexivity.
Qed.

Lemma hc4nb_table_cnt_nonneg T idx L : 0 <= hc4nb_table_cnt T idx L.
Proof. unfold hc4nb_table_cnt. apply Zlength_nonneg. Qed.

Lemma hc4nb_table_cnt_one T idx a E :
  t_entry T a = Some E ->
  hc4nb_table_cnt T idx [a] = if Int.eq (e_index E) idx then 1 else 0.
Proof.
  intros HE. unfold hc4nb_table_cnt, t_indices. simpl. rewrite HE.
  destruct (Int.eq (e_index E) idx); reflexivity.
Qed.

Module FK := WgNoise.harness.x_cookie_reply.code.
Module FR := WgNoise.harness.x_consume_response_any.code.

(* every lemma takes all the section variables and hypotheses (a stable signature for the assembly) *)
#[local] Set Default Proof Using "All".

#[local] Existing Instance CSknb.

Section Bodies.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Hypothesis X25519: x25519_props x25519.
Hypothesis AEAD: aead_props aead_enc aead_dec.
Hypothesis XAEAD: xaead_props xaead_enc xaead_dec.

Lemma hc4nb_body_table_has :
  @semax_body [] (hc3_G_none) CSknb FH.f_table_has (table_has_spec).
Proof.
  start_function.
  rename H into He.
  assert_PROP (itable_wf T) as HW by (unfold itable; entailer!).
  assert_PROP (is_pointer_or_null (hd nullval (t_L T))).
  { sep_apply (hc4nb_table_hd sht tab T [] (t_L T) eq_refl). entailer!. }
  forward.
  rewrite hc4nb_table_open0 by auto. Intros.
  unfold Sfor. forward. gather_SEP 0 1. rewrite <- hc4nb_table_open0 by auto.
  forward_loop (EX L1: list val, EX L2: list val,
    PROP (t_L T = L1 ++ L2)
    LOCAL (temp FH._it (hd nullval L2); temp FH._n (Vint (Int.repr (if vin e L1 then 1 else 0)));
           temp FH._e e)
    SEP (itable sht tab T))
  continue: (EX L1: list val, EX a: val, EX L2: list val,
    PROP (t_L T = L1 ++ a :: L2)
    LOCAL (temp FH._it a; temp FH._n (Vint (Int.repr (if vin e (L1 ++ [a]) then 1 else 0)));
           temp FH._e e)
    SEP (itable sht tab T))
  break: (PROP ()
    LOCAL (temp FH._n (Vint (Int.repr (if vin e (t_L T) then 1 else 0))); temp FH._e e)
    SEP (itable sht tab T)).
  { Exists (@nil val) (t_L T). entailer!. }
  { Intros L1 L2. rename H0 into HL.
    assert_PROP (is_pointer_or_null (hd nullval L2)) as HP.
    { sep_apply (hc4nb_table_hd sht tab T L1 L2 HL). entailer!. }
    forward_if.
    { apply hc4nb_table_tc_hd with L1; auto. }
    { destruct L2 as [|a L2]; [simpl in H0; contradiction|]. simpl in H0.
      assert (Ha: In a (saddrs (t_D T))) by (eapply hc4nb_table_inL; eauto).
      forward_if.
      { apply hc4nb_table_tc_eq; auto. }
      - subst a. 
        assert (Hv: vin e L1 = false) by (apply hc4nb_table_vin_notin with L2; rewrite <- HL; apply HW).
        rewrite Hv. forward. Exists L1 e L2. entailer!.
        rewrite hc4nb_table_vin_app_eq. reflexivity.
      - forward. Exists L1 a L2. entailer!.
        rewrite hc4nb_table_vin_app_ne by auto. auto. }
    { destruct L2 as [|a L2].
      - forward. entailer!. rewrite app_nil_r in HL. rewrite HL. auto.
      - simpl in H0. subst a.
        assert_PROP (isptr nullval).
        { sep_apply (hc4nb_table_isptr sht tab T nullval ltac:(eapply hc4nb_table_inL; eauto)).
          entailer!. }
        contradiction. } }
  { Intros L1 a L2. rename H0 into HL.
    destruct (hc4nb_table_focus T L1 a L2 HW HL) as (sh & E & HE & Hsh & HS).
    assert_PROP (is_pointer_or_null (hd nullval L2)) as HP.
    { sep_apply (hc4nb_table_hd sht tab T (L1 ++ [a]) L2 ltac:(rewrite <- app_assoc; auto)). entailer!. }
    sep_apply (derives_refl' _ _ (hc4nb_table_open sht tab T a sh E HW HE)). Intros.
    unfold entry_val. rewrite HS. forward.
    gather_SEP 0 1 2. rewrite <- HS. fold (entry_val E (succ_in (t_L T) a) (vin a (t_L T))).
    sep_apply (derives_refl' _ _ (eq_sym (hc4nb_table_open sht tab T a sh E HW HE))).
    Exists (L1 ++ [a]) L2. entailer!.
    rewrite <- app_assoc; auto. }
  destruct (hc4nb_table_sfind_in _ _ He) as (sh & E & HE).
  assert (writable_share sh) by (destruct HW as (_ & _ & _ & HF); eapply hc4nb_table_sfind_wr; eauto).
  forward_if (PROP () LOCAL (temp FH._t'1 (Vint (if vin e (t_L T) then Int.one else Int.zero)))
              SEP (itable sht tab T)).
  - destruct (vin e (t_L T)) eqn:Hv.
    2: { exfalso. discriminate. }
    sep_apply (derives_refl' _ _ (hc4nb_table_open sht tab T e sh E HW HE)). Intros.
    unfold entry_val. rewrite Hv. forward. forward.
    rewrite (hc4nb_table_open sht tab T e sh E HW HE), Hv. unfold entry_val. entailer!.
  - forward. destruct (vin e (t_L T)); [contradiction|]. entailer!.
  - forward.
Qed.

Lemma hc4nb_body_table_index_unique :
  @semax_body [] (hc3_G_none) CSknb FH.f_table_index_unique (table_index_unique_spec).
Proof.
  start_function.
  assert_PROP (itable_wf T) as HW by (unfold itable; entailer!).
  assert (HC: hc4nb_table_cnt T idx (t_L T) <= 1) by exact H.
  assert_PROP (is_pointer_or_null (hd nullval (t_L T))).
  { sep_apply (hc4nb_table_hd sht tab T [] (t_L T) eq_refl). entailer!. }
  forward.
  rewrite hc4nb_table_open0 by auto. Intros.
  unfold Sfor. forward. gather_SEP 0 1. rewrite <- hc4nb_table_open0 by auto.
  forward_loop (EX L1: list val, EX L2: list val,
    PROP (t_L T = L1 ++ L2)
    LOCAL (temp FH._it (hd nullval L2); temp FH._n (Vint (Int.repr (hc4nb_table_cnt T idx L1)));
           temp FH._index (Vint idx))
    SEP (itable sht tab T))
  continue: (EX L1: list val, EX a: val, EX L2: list val,
    PROP (t_L T = L1 ++ a :: L2)
    LOCAL (temp FH._it a; temp FH._n (Vint (Int.repr (hc4nb_table_cnt T idx (L1 ++ [a]))));
           temp FH._index (Vint idx))
    SEP (itable sht tab T))
  break: (PROP ()
    LOCAL (temp FH._n (Vint (Int.repr (hc4nb_table_cnt T idx (t_L T)))))
    SEP (itable sht tab T)).
  { Exists (@nil val) (t_L T). entailer!. }
  { Intros L1 L2. rename H1 into HL.
    assert_PROP (is_pointer_or_null (hd nullval L2)) as HP.
    { sep_apply (hc4nb_table_hd sht tab T L1 L2 HL). entailer!. }
    forward_if.
    { apply hc4nb_table_tc_hd with L1; auto. }
    { destruct L2 as [|a L2]; [simpl in H1; contradiction|]. simpl in H1.
      destruct (hc4nb_table_focus T L1 a L2 HW HL) as (sh & E & HE & Hsh & HS).
      assert (HCa: hc4nb_table_cnt T idx [a] = if Int.eq (e_index E) idx then 1 else 0)
        by (apply hc4nb_table_cnt_one; eapply hc4nb_table_tentry; eauto).
      assert (HCs: hc4nb_table_cnt T idx (L1 ++ [a]) <= 1).
      { pose proof (hc4nb_table_cnt_nonneg T idx L2).
        rewrite HL, app_cons_assoc, hc4nb_table_cnt_app in HC. lia. }
      rewrite hc4nb_table_cnt_app, HCa in HCs.
      pose proof (hc4nb_table_cnt_nonneg T idx L1).
      sep_apply (derives_refl' _ _ (hc4nb_table_open sht tab T a sh E HW HE)). Intros.
      unfold entry_val. forward.
      gather_SEP 0 1 2. fold (entry_val E (succ_in (t_L T) a) (vin a (t_L T))).
      sep_apply (derives_refl' _ _ (eq_sym (hc4nb_table_open sht tab T a sh E HW HE))).
      forward_if.
      - subst idx. rewrite Int.eq_true in HCs, HCa.
        forward. Exists L1 a L2. entailer!.
        rewrite hc4nb_table_cnt_app, HCa. reflexivity.
      - forward. Exists L1 a L2. entailer!.
        rewrite hc4nb_table_cnt_app, HCa. rewrite Int.eq_false by auto. rewrite Z.add_0_r. auto. }
    { destruct L2 as [|a L2].
      - forward. entailer!. rewrite app_nil_r in HL. rewrite HL. auto.
      - simpl in H1. subst a.
        assert_PROP (isptr nullval).
        { sep_apply (hc4nb_table_isptr sht tab T nullval ltac:(eapply hc4nb_table_inL; eauto)).
          entailer!. }
        contradiction. } }
  { Intros L1 a L2. rename H1 into HL.
    destruct (hc4nb_table_focus T L1 a L2 HW HL) as (sh & E & HE & Hsh & HS).
    assert_PROP (is_pointer_or_null (hd nullval L2)) as HP.
    { sep_apply (hc4nb_table_hd sht tab T (L1 ++ [a]) L2 ltac:(rewrite <- app_assoc; auto)). entailer!. }
    rewrite (hc4nb_table_open sht tab T a sh E) by auto. Intros.
    unfold entry_val. rewrite HS. forward.
    gather_SEP 0 1 2. rewrite <- HS. fold (entry_val E (succ_in (t_L T) a) (vin a (t_L T))).
    rewrite <- (hc4nb_table_open sht tab T a sh E) by auto.
    Exists (L1 ++ [a]) L2. entailer!.
    rewrite <- app_assoc; auto. }
  pose proof (hc4nb_table_cnt_nonneg T idx (t_L T)).
  forward.
  unfold count_index. fold (hc4nb_table_cnt T idx (t_L T)).
  destruct (Z.eq_dec (hc4nb_table_cnt T idx (t_L T)) 1) as [E1|E1].
  - rewrite E1. entailer!.
  - assert (E0: hc4nb_table_cnt T idx (t_L T) = 0) by lia. rewrite E0. entailer!.
Qed.

Lemma hc4nb_body_table_len :
  @semax_body [] (hc3_G_none) CSknb FH.f_table_len (table_len_spec).
Proof.
  start_function.
  assert_PROP (itable_wf T) as HW by (unfold itable; entailer!).
  assert_PROP (is_pointer_or_null (hd nullval (t_L T))).
  { sep_apply (hc4nb_table_hd sht tab T [] (t_L T) eq_refl). entailer!. }
  forward.
  rewrite hc4nb_table_open0 by auto. Intros.
  unfold Sfor. forward. gather_SEP 0 1. rewrite <- hc4nb_table_open0 by auto.
  forward_loop (EX L1: list val, EX L2: list val,
    PROP (t_L T = L1 ++ L2)
    LOCAL (temp FH._it (hd nullval L2); temp FH._n (Vlong (Int64.repr (Zlength L1))))
    SEP (itable sht tab T))
  continue: (EX L1: list val, EX a: val, EX L2: list val,
    PROP (t_L T = L1 ++ a :: L2)
    LOCAL (temp FH._it a; temp FH._n (Vlong (Int64.repr (Zlength (L1 ++ [a])))))
    SEP (itable sht tab T))
  break: (PROP ()
    LOCAL (temp FH._n (Vlong (Int64.repr (Zlength (t_L T)))))
    SEP (itable sht tab T)).
  { Exists (@nil val) (t_L T). entailer!. }
  { Intros L1 L2. rename H0 into HL.
    assert_PROP (is_pointer_or_null (hd nullval L2)) as HP.
    { sep_apply (hc4nb_table_hd sht tab T L1 L2 HL). entailer!. }
    forward_if.
    { apply hc4nb_table_tc_hd with L1; auto. }
    { destruct L2 as [|a L2]; [simpl in H0; contradiction|]. simpl in H0.
      forward. Exists L1 a L2. entailer!.
      rewrite Zlength_app, Zlength_cons, Zlength_nil. f_equal. }
    { destruct L2 as [|a L2].
      - forward. entailer!. rewrite app_nil_r in HL. rewrite HL. auto.
      - simpl in H0. subst a.
        assert_PROP (isptr nullval).
        { sep_apply (hc4nb_table_isptr sht tab T nullval ltac:(eapply hc4nb_table_inL; eauto)).
          entailer!. }
        contradiction. } }
  { Intros L1 a L2. rename H0 into HL.
    destruct (hc4nb_table_focus T L1 a L2 HW HL) as (sh & E & HE & Hsh & HS).
    assert_PROP (is_pointer_or_null (hd nullval L2)) as HP.
    { sep_apply (hc4nb_table_hd sht tab T (L1 ++ [a]) L2 ltac:(rewrite <- app_assoc; auto)). entailer!. }
    rewrite (hc4nb_table_open sht tab T a sh E) by auto. Intros.
    unfold entry_val. rewrite HS. forward.
    gather_SEP 0 1 2. rewrite <- HS. fold (entry_val E (succ_in (t_L T) a) (vin a (t_L T))).
    rewrite <- (hc4nb_table_open sht tab T a sh E) by auto.
    Exists (L1 ++ [a]) L2. entailer!.
    rewrite <- app_assoc; auto. }
  forward.
Qed.

(* the group *)
Theorem hc4nb_bodies_table :
  (@semax_body [] (hc3_G_none) CSknb FH.f_table_has (table_has_spec)) /\
  (@semax_body [] (hc3_G_none) CSknb FH.f_table_index_unique (table_index_unique_spec)) /\
  (@semax_body [] (hc3_G_none) CSknb FH.f_table_len (table_len_spec)).
Proof.
  exact (conj hc4nb_body_table_has (conj hc4nb_body_table_index_unique hc4nb_body_table_len)).
Qed.

End Bodies.
