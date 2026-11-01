(* Body proofs of the protocol piece, group shim_table1.
   Target: prot_bodies3_shim_table1.  Prove each function's body against its specification (prot_specs3.v) in the
   compspecs of its unit, with the context Gprot3 (prot_prog3.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_prog3.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.
Require Import VST.msl.iter_sepcon.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.protocol.prot_cs.
Local Open Scope logic.

(* ---- the pool: focusing on one entry ---- *)
Section Pool.
Context {A: Type}.

Lemma prot3_shim_table1_split (D: list (val * share * A)) a sh E (f: val * share * A -> mpred) :
  sfind D a = Some (sh, E) -> iter_sepcon f D = f (a, sh, E) * iter_sepcon f (sdel D a).
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; reflexivity|].
  rewrite (IH H); simpl. rewrite <- !sepcon_assoc, (sepcon_comm (f _) (f _)). reflexivity.
Qed.

Lemma prot3_shim_table1_sfind_in (D: list (val * share * A)) a :
  In a (saddrs D) -> exists sh E, sfind D a = Some (sh, E).
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [contradiction|].
  destruct (EqDec_val x a); [eauto|]. destruct H; [congruence|auto].
Qed.

Lemma prot3_shim_table1_sfind_In (D: list (val * share * A)) a sh E :
  sfind D a = Some (sh, E) -> In (a, sh, E) D.
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; auto|auto].
Qed.

Lemma prot3_shim_table1_sfind_wr (D: list (val * share * A)) a sh E :
  Forall (fun x : val * share * A => let (y, _) := x in let (_, sh) := y in writable_share sh) D ->
  sfind D a = Some (sh, E) -> writable_share sh.
Proof.
  intros HF H. apply prot3_shim_table1_sfind_In in H.
  rewrite Forall_forall in HF. apply (HF _ H).
Qed.
End Pool.

Lemma prot3_shim_table1_entry_S sh v p :
  @data_at Noise.CS sh t_entry_s v p = @data_at Shim.CS sh t_entry_s v p.
Proof. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

Lemma prot3_shim_table1_itab_S sh v p :
  @data_at Noise.CS sh t_itab v p = @data_at Shim.CS sh t_itab v p.
Proof. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

Lemma prot3_shim_table1_valid sht tab T a :
  In a (saddrs (t_D T)) -> itable sht tab T |-- valid_pointer a.
Proof.
  intros Ha. destruct (prot3_shim_table1_sfind_in _ _ Ha) as (sh & E & HE).
  unfold itable. Intros. rewrite (prot3_shim_table1_split _ _ _ _ _ HE).
  assert (writable_share sh) by (destruct H as (_ & _ & _ & HF); eapply prot3_shim_table1_sfind_wr; eauto).
  unfold pool_item_rep, entry_at. 
  apply sepcon_valid_pointer2. apply sepcon_valid_pointer1. 
  apply data_at_valid_ptr; [auto | simpl; lia].
Qed.

Lemma prot3_shim_table1_open0 sht tab T :
  itable_wf T ->
  itable sht tab T =
  @data_at Shim.CS sht t_itab (hd nullval (t_L T)) tab * iter_sepcon (pool_item_rep (t_L T)) (t_D T).
Proof.
  intros. unfold itable. rewrite prot3_shim_table1_itab_S.
  apply pred_ext; entailer!.
Qed.

Lemma prot3_shim_table1_open sht tab T a sh E :
  itable_wf T -> sfind (t_D T) a = Some (sh, E) ->
  itable sht tab T =
  @data_at Shim.CS sht t_itab (hd nullval (t_L T)) tab *
  (@data_at Shim.CS sh t_entry_s (entry_val E (succ_in (t_L T) a) (vin a (t_L T))) a *
   iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) a)).
Proof.
  intros. rewrite prot3_shim_table1_open0 by auto.
  rewrite (prot3_shim_table1_split _ _ _ _ _ H0). unfold pool_item_rep at 1, entry_at.
  rewrite prot3_shim_table1_entry_S. reflexivity.
Qed.

Lemma prot3_shim_table1_isptr sht tab T a :
  In a (saddrs (t_D T)) -> itable sht tab T |-- !! isptr a.
Proof.
  intros Ha. destruct (prot3_shim_table1_sfind_in _ _ Ha) as (sh & E & HE).
  unfold itable. Intros. rewrite (prot3_shim_table1_split _ _ _ _ _ HE).
  unfold pool_item_rep, entry_at. entailer!.
Qed.

Lemma prot3_shim_table1_hd sht tab T L1 L2 :
  t_L T = L1 ++ L2 -> itable sht tab T |-- !! is_pointer_or_null (hd nullval L2).
Proof.
  intros HL. destruct L2 as [|a L2]; simpl; [entailer!|].
  assert_PROP (itable_wf T) as HW by (unfold itable; entailer!).
  assert (Ha: In a (saddrs (t_D T))).
  { apply (proj1 (proj2 HW)). rewrite HL. apply in_or_app. simpl; auto. }
  sep_apply (prot3_shim_table1_isptr sht tab T a Ha).
  entailer!.
Qed.

Lemma prot3_shim_table1_inL T L1 a L2 :
  itable_wf T -> t_L T = L1 ++ a :: L2 -> In a (saddrs (t_D T)).
Proof.
  intros HW HL. apply (proj1 (proj2 HW)). rewrite HL. apply in_or_app. simpl; auto.
Qed.

Lemma prot3_shim_table1_tc_hd sht tab T L1 L2 :
  t_L T = L1 ++ L2 -> itable sht tab T |-- denote_tc_test_eq (hd nullval L2) (Vlong Int64.zero).
Proof.
  intros HL. apply denote_tc_test_eq_split; [|apply valid_pointer_null].
  destruct L2 as [|a L2]; simpl; [apply valid_pointer_null|].
  assert_PROP (itable_wf T) as HW by (unfold itable; entailer!).
  apply prot3_shim_table1_valid. eapply prot3_shim_table1_inL; eauto.
Qed.

Lemma prot3_shim_table1_succ L1 a L2 :
  NoDup (L1 ++ a :: L2) -> succ_in (L1 ++ a :: L2) a = hd nullval L2.
Proof.
  induction L1 as [|x L1 IH]; simpl; intros H.
  - destruct (EqDec_val a a); [reflexivity|congruence].
  - inv H. destruct (EqDec_val x a).
    + subst. exfalso. apply H2. apply in_or_app. simpl; auto.
    + auto.
Qed.

Lemma prot3_shim_table1_tentry T a sh E :
  sfind (t_D T) a = Some (sh, E) -> t_entry T a = Some E.
Proof. unfold t_entry. intros ->. reflexivity. Qed.

Lemma prot3_shim_table1_ind_snoc T L1 a sh E idx :
  sfind (t_D T) a = Some (sh, E) -> ~ In idx (t_indices T L1) -> e_index E <> idx ->
  ~ In idx (t_indices T (L1 ++ [a])).
Proof.
  intros HE HI Hne. unfold t_indices in *. rewrite map_app. simpl.
  rewrite (prot3_shim_table1_tentry _ _ _ _ HE). intros H. apply in_app_or in H.
  destruct H as [H|[H|H]]; auto.
Qed.

Lemma prot3_shim_table1_ind_in T L L1 a L2 sh E :
  L = L1 ++ a :: L2 -> sfind (t_D T) a = Some (sh, E) -> In (e_index E) (t_indices T L).
Proof.
  intros HL HE. unfold t_indices. apply in_map_iff. exists a.
  rewrite (prot3_shim_table1_tentry _ _ _ _ HE). split; auto.
  subst L. apply in_or_app. simpl; auto.
Qed.

(* ---- the link fields ---- *)
Lemma prot3_shim_table1_itab_ptr sh v p :
  @field_compatible Shim.CS t_itab [] p ->
  @data_at Shim.CS sh t_itab v p = @data_at Shim.CS sh (tptr t_entry_s) v p.
Proof.
  intros Hfc.
  assert (Hfc': @field_compatible Shim.CS t_itab [StructField WgNoise.shim.code._head] p).
  { apply field_compatible_cons. simpl. split; auto. left; reflexivity. }
  unfold data_at at 1. erewrite field_at_Tstruct; [|reflexivity|apply JMeq_refl].
  simpl co_members. unfold nested_sfieldlist_at. simpl. unfold withspacer; simpl.
  rewrite field_at_data_at. simpl nested_field_type.
  rewrite field_compatible_field_address by auto. simpl.
  destruct p; try (destruct Hfc; contradiction). simpl. rewrite Ptrofs.add_zero. reflexivity.
Qed.

Lemma prot3_shim_table1_entry_next sh pe (rest: val * (val * val)) p :
  exists R: mpred, forall nx,
  @data_at Shim.CS sh t_entry_s (pe, (nx, rest)) p =
  @data_at Shim.CS sh (tptr t_entry_s) nx
    (@field_address Shim.CS t_entry_s [StructField WgNoise.shim.code._next] p) * R.
Proof.
  eexists. intros nx.
  unfold data_at at 1. erewrite field_at_Tstruct; [|reflexivity|apply JMeq_refl].
  simpl co_members. unfold nested_sfieldlist_at. simpl. unfold withspacer; simpl.
  rewrite (field_at_data_at _ _ [StructField WgNoise.shim.code._next]). simpl nested_field_type.
  rewrite <- sepcon_assoc, (sepcon_comm (@field_at Shim.CS sh t_entry_s [StructField WgNoise.shim.code._peer] pe p)),
    sepcon_assoc. reflexivity.
Qed.

(* ---- lists ---- *)
Lemma prot3_shim_table1_vin_iff x L : vin x L = true <-> In x L.
Proof. unfold vin. destruct (in_dec _ x L); split; auto; discriminate. Qed.

Lemma prot3_shim_table1_vremove_notin e L : ~ In e L -> vremove e L = L.
Proof.
  induction L as [|x L IH]; simpl; intros H; auto.
  destruct (EqDec_val x e); [subst; exfalso; auto|]. rewrite IH; auto.
Qed.

Lemma prot3_shim_table1_vremove_app e A B : ~ In e A -> ~ In e B -> vremove e (A ++ e :: B) = A ++ B.
Proof.
  induction A as [|x A IH]; simpl; intros HA HB.
  - destruct (EqDec_val e e); [|congruence]. apply prot3_shim_table1_vremove_notin; auto.
  - destruct (EqDec_val x e); [subst; exfalso; auto|]. rewrite IH; auto.
Qed.

Lemma prot3_shim_table1_vremove_in e L x : In x (vremove e L) -> In x L.
Proof.
  induction L as [|y L IH]; simpl; intros H; auto.
  destruct (EqDec_val y e); [right; auto|]. destruct H; [left; auto|right; auto].
Qed.

Lemma prot3_shim_table1_vremove_nodup e L : NoDup L -> NoDup (vremove e L).
Proof.
  induction L as [|y L IH]; simpl; intros H; auto. inv H.
  destruct (EqDec_val y e); auto. constructor; auto.
  intros H. apply H2. eapply prot3_shim_table1_vremove_in; eauto.
Qed.

Lemma prot3_shim_table1_succ_notin a L : ~ In a L -> succ_in L a = nullval.
Proof.
  induction L as [|x L IH]; simpl; intros H; auto.
  destruct (EqDec_val x a); [subst; exfalso; auto|]. auto.
Qed.

Lemma prot3_shim_table1_succ_skip0 x e B : x <> e -> succ_in (e :: B) x = succ_in B x.
Proof. intros. simpl. destruct (EqDec_val e x); [congruence|auto]. Qed.

Lemma prot3_shim_table1_succ_skip x A p e B : x <> p -> x <> e ->
  succ_in (A ++ p :: e :: B) x = succ_in (A ++ p :: B) x.
Proof.
  induction A as [|y A IH]; simpl; intros H1 H2.
  - destruct (EqDec_val p x); [congruence|]. destruct (EqDec_val e x); [congruence|]. reflexivity.
  - destruct (EqDec_val y x).
    + destruct A; reflexivity.
    + auto.
Qed.

Lemma prot3_shim_table1_vin_skip x A e B : x <> e -> vin x (A ++ e :: B) = vin x (A ++ B).
Proof.
  intros H. apply Bool.eq_true_iff_eq. rewrite !prot3_shim_table1_vin_iff. split; intros H1.
  - apply in_app_or in H1. apply in_or_app. destruct H1 as [?|[?|?]]; auto. congruence.
  - apply in_app_or in H1. apply in_or_app. destruct H1; simpl; auto.
Qed.

Section Pool2.
Context {A: Type}.
Lemma prot3_shim_table1_saddrs_in (D: list (val * share * A)) x sh E : In (x, sh, E) D -> In x (saddrs D).
Proof. intros H. unfold saddrs. apply in_map_iff. exists (x, sh, E). split; auto. Qed.

Lemma prot3_shim_table1_sdel_in (D: list (val * share * A)) a x sh E : In (x, sh, E) (sdel D a) -> In (x, sh, E) D.
Proof.
  induction D as [|[[y shy] w] D IH]; simpl; intros H; auto.
  destruct (EqDec_val y a); [right; auto|]. destruct H; [left; auto | right; auto].
Qed.

Lemma prot3_shim_table1_sdel_saddrs (D: list (val * share * A)) a x : In x (saddrs (sdel D a)) -> In x (saddrs D).
Proof.
  induction D as [|[[y shy] w] D IH]; simpl; intros H; auto.
  destruct (EqDec_val y a); [right; auto|]. destruct H; [left; auto | right; auto].
Qed.

Lemma prot3_shim_table1_sdel_nodup (D: list (val * share * A)) a : NoDup (saddrs D) -> NoDup (saddrs (sdel D a)).
Proof.
  induction D as [|[[y shy] w] D IH]; simpl; intros H; auto. inv H.
  destruct (EqDec_val y a); auto. simpl. constructor; auto.
  intros H. apply H2. eapply prot3_shim_table1_sdel_saddrs; eauto.
Qed.

Lemma prot3_shim_table1_sdel_ne (D: list (val * share * A)) a x sh E :
  NoDup (saddrs D) -> In (x, sh, E) (sdel D a) -> x <> a.
Proof.
  induction D as [|[[y shy] w] D IH]; simpl; intros HN H; auto. inv HN.
  destruct (EqDec_val y a).
  - subst. intros ->. apply H2. eapply prot3_shim_table1_saddrs_in; eauto.
  - destruct H as [H|H]; [inv H; auto|]. apply IH; auto.
Qed.

Lemma prot3_shim_table1_sfind_sdel (D: list (val * share * A)) a b : b <> a -> sfind (sdel D a) b = sfind D b.
Proof.
  induction D as [|[[y shy] w] D IH]; simpl; intros H; auto.
  destruct (EqDec_val y a).
  - subst. destruct (EqDec_val a b); [congruence|auto].
  - simpl. destruct (EqDec_val y b); auto.
Qed.
End Pool2.

Lemma prot3_shim_table1_pool_eq L L' (D: list (val * share * entry)) :
  (forall x sh E, In (x, sh, E) D -> succ_in L x = succ_in L' x /\ vin x L = vin x L') ->
  iter_sepcon (pool_item_rep L) D = iter_sepcon (pool_item_rep L') D.
Proof.
  intros H. apply iter_sepcon_func_strong. intros [[x sh] E] Hin.
  destruct (H _ _ _ Hin) as [H1 H2]. unfold pool_item_rep. rewrite H1, H2. reflexivity.
Qed.

Lemma prot3_shim_table1_wf_remove T e : itable_wf T -> itable_wf (t_remove T e).
Proof.
  intros (H1 & H2 & H3 & H4). unfold t_remove, itable_wf; simpl. split; [|split; [|split]]; auto.
  - apply prot3_shim_table1_vremove_nodup; auto.
  - intros x Hx. apply H2. eapply prot3_shim_table1_vremove_in; eauto.
Qed.

Lemma prot3_shim_table1_fc sht tab T a :
  In a (saddrs (t_D T)) -> itable sht tab T |-- !! @field_compatible Shim.CS t_entry_s [] a.
Proof.
  intros Ha. destruct (prot3_shim_table1_sfind_in _ _ Ha) as (sh & E & HE).
  unfold itable. Intros. rewrite (prot3_shim_table1_split _ _ _ _ _ HE).
  unfold pool_item_rep, entry_at. rewrite prot3_shim_table1_entry_S. entailer!.
Qed.

Lemma prot3_shim_table1_open2 sht tab T p shp Ep e she Ee :
  itable_wf T -> sfind (t_D T) p = Some (shp, Ep) -> sfind (t_D T) e = Some (she, Ee) -> p <> e ->
  itable sht tab T =
  @data_at Shim.CS sht t_itab (hd nullval (t_L T)) tab *
  (@data_at Shim.CS shp t_entry_s (entry_val Ep (succ_in (t_L T) p) (vin p (t_L T))) p *
   (@data_at Shim.CS she t_entry_s (entry_val Ee (succ_in (t_L T) e) (vin e (t_L T))) e *
    iter_sepcon (pool_item_rep (t_L T)) (sdel (sdel (t_D T) p) e))).
Proof.
  intros HW Hp He Hne. rewrite (prot3_shim_table1_open sht tab T p shp Ep) by auto.
  rewrite (prot3_shim_table1_split (sdel (t_D T) p) e she Ee)
    by (rewrite prot3_shim_table1_sfind_sdel; auto).
  unfold pool_item_rep at 1, entry_at. rewrite prot3_shim_table1_entry_S. reflexivity.
Qed.

(* ---- the link: &table->head, or &p->next for the last p of the prefix L1 ---- *)
Definition prot3_shim_table1_link (tab: val) (L1: list val) : val :=
  match rev L1 with
  | [] => tab
  | p :: _ => @field_address Shim.CS t_entry_s [StructField WgNoise.shim.code._next] p
  end.

Lemma prot3_shim_table1_link_snoc tab L1 p :
  prot3_shim_table1_link tab (L1 ++ [p]) =
  @field_address Shim.CS t_entry_s [StructField WgNoise.shim.code._next] p.
Proof. unfold prot3_shim_table1_link. rewrite rev_unit. reflexivity. Qed.

Lemma prot3_shim_table1_link_rd sht tab T L1 L2 :
  writable_share sht -> itable_wf T -> t_L T = L1 ++ L2 ->
  itable sht tab T |-- EX shl: share, !! writable_share shl &&
    (@data_at Shim.CS shl (tptr t_entry_s) (hd nullval L2) (prot3_shim_table1_link tab L1) *
     (@data_at Shim.CS shl (tptr t_entry_s) (hd nullval L2) (prot3_shim_table1_link tab L1) -*
      itable sht tab T)).
Proof.
  intros Hsh HW HL. destruct L1 as [|p L1 _] using rev_ind.
  - simpl in HL. rewrite prot3_shim_table1_open0 by auto.
    assert_PROP (@field_compatible Shim.CS t_itab [] tab) by entailer!.
    rewrite prot3_shim_table1_itab_ptr by auto. unfold prot3_shim_table1_link; simpl. rewrite <- HL.
    Exists sht. apply andp_right; [apply prop_right; auto|]. cancel. repeat (apply -> wand_sepcon_adjoint). cancel.
  - rewrite <- app_assoc in HL. simpl in HL.
    assert (Hp: In p (saddrs (t_D T))) by (eapply prot3_shim_table1_inL; eauto).
    destruct (prot3_shim_table1_sfind_in _ _ Hp) as (shp & Ep & HEp).
    assert (writable_share shp) by (destruct HW as (_ & _ & _ & HF); eapply prot3_shim_table1_sfind_wr; eauto).
    assert (HS: succ_in (t_L T) p = hd nullval L2).
    { rewrite HL. apply prot3_shim_table1_succ. rewrite <- HL. apply HW. }
    rewrite (prot3_shim_table1_open sht tab T p shp Ep) by auto. rewrite HS. unfold entry_val.
    destruct (prot3_shim_table1_entry_next shp (e_peer Ep)
      (Val.of_bool (vin p (t_L T)), (Vint (e_type Ep), Vint (e_index Ep))) p) as [R HR].
    rewrite HR, prot3_shim_table1_link_snoc.
    Exists shp. apply andp_right; [apply prop_right; auto|]. cancel. repeat (apply -> wand_sepcon_adjoint). cancel.
Qed.

Lemma prot3_shim_table1_link_wr sht tab T L1 e L2 she Ee :
  writable_share sht -> itable_wf T -> t_L T = L1 ++ e :: L2 -> sfind (t_D T) e = Some (she, Ee) ->
  itable sht tab T |-- EX shl: share, !! writable_share shl &&
    (@data_at Shim.CS shl (tptr t_entry_s) e (prot3_shim_table1_link tab L1) *
     @data_at Shim.CS she t_entry_s (entry_val Ee (hd nullval L2) true) e *
     ((@data_at Shim.CS shl (tptr t_entry_s) (hd nullval L2) (prot3_shim_table1_link tab L1) *
       @data_at Shim.CS she t_entry_s (entry_val Ee nullval false) e) -* itable sht tab (t_remove T e))).
Proof.
  intros Hsh HW HL HE.
  pose proof (prot3_shim_table1_wf_remove T e HW) as HW'.
  assert (HN: NoDup (L1 ++ e :: L2)) by (rewrite <- HL; apply HW).
  assert (HND: NoDup (saddrs (t_D T))) by apply HW.
  assert (He1: ~ In e L1) by (intro; apply (NoDup_remove_2 _ _ _ HN); apply in_or_app; auto).
  assert (He2: ~ In e L2) by (intro; apply (NoDup_remove_2 _ _ _ HN); apply in_or_app; auto).
  assert (HL': t_L (t_remove T e) = L1 ++ L2).
  { unfold t_remove; simpl. rewrite HL. apply prot3_shim_table1_vremove_app; auto. }
  assert (HE': sfind (t_D (t_remove T e)) e = Some (she, Ee)) by exact HE.
  assert (Hsucc: succ_in (t_L T) e = hd nullval L2) by (rewrite HL; apply prot3_shim_table1_succ; auto).
  assert (Hvin: vin e (t_L T) = true).
  { apply prot3_shim_table1_vin_iff. rewrite HL. apply in_or_app. simpl; auto. }
  assert (Hsucc': succ_in (t_L (t_remove T e)) e = nullval).
  { apply prot3_shim_table1_succ_notin. rewrite HL'. intro H. apply in_app_or in H. tauto. }
  assert (Hvin': vin e (t_L (t_remove T e)) = false).
  { apply Bool.not_true_is_false. rewrite prot3_shim_table1_vin_iff, HL'. intro H. apply in_app_or in H. tauto. }
  change (t_D (t_remove T e)) with (t_D T) in *.
  destruct L1 as [|p L1 _] using rev_ind.
  - simpl in HL. change ([] ++ L2) with L2 in HL'.
    rewrite (prot3_shim_table1_open sht tab T e she Ee) by auto.
    assert_PROP (@field_compatible Shim.CS t_itab [] tab) by entailer!.
    rewrite prot3_shim_table1_itab_ptr by auto. rewrite Hsucc, Hvin. rewrite HL at 1.
    unfold prot3_shim_table1_link; simpl.
    Exists sht. apply andp_right; [apply prop_right; auto|]. cancel. repeat (apply -> wand_sepcon_adjoint).
    rewrite (prot3_shim_table1_open sht tab (t_remove T e) e she Ee) by auto.
    rewrite prot3_shim_table1_itab_ptr by auto. rewrite Hsucc', Hvin', HL'.
    change (t_D (t_remove T e)) with (t_D T).
    rewrite (prot3_shim_table1_pool_eq (t_L T) L2 (sdel (t_D T) e)).
    + cancel.
    + intros x sh E Hx. pose proof (prot3_shim_table1_sdel_ne _ _ _ _ _ HND Hx). rewrite HL. split.
      * apply prot3_shim_table1_succ_skip0; auto.
      * apply (prot3_shim_table1_vin_skip x [] e L2); auto.
  - rewrite <- app_assoc in HL, HL'. simpl in HL. change ([p] ++ L2) with (p :: L2) in HL'.
    assert (Hpe: p <> e) by (intros ->; apply He1; apply in_or_app; simpl; auto).
    assert (Hp: In p (saddrs (t_D T))) by (eapply prot3_shim_table1_inL; eauto).
    destruct (prot3_shim_table1_sfind_in _ _ Hp) as (shp & Ep & HEp).
    assert (writable_share shp) by (destruct HW as (_ & _ & _ & HF); eapply prot3_shim_table1_sfind_wr; eauto).
    assert (HS: succ_in (t_L T) p = e).
    { rewrite HL. apply (prot3_shim_table1_succ L1 p (e :: L2)). rewrite <- HL. apply HW. }
    assert (HS': succ_in (t_L (t_remove T e)) p = hd nullval L2).
    { rewrite HL'. apply prot3_shim_table1_succ. rewrite <- HL'. apply HW'. }
    assert (HV: vin p (t_L T) = vin p (t_L (t_remove T e))).
    { rewrite HL, HL'. apply (prot3_shim_table1_vin_skip p (L1 ++ [p]) e L2) in Hpe.
      rewrite <- !app_assoc in Hpe. exact Hpe. }
    assert (HH: hd nullval (t_L T) = hd nullval (t_L (t_remove T e))).
    { rewrite HL, HL'. destruct L1; reflexivity. }
    rewrite (prot3_shim_table1_open2 sht tab T p shp Ep e she Ee) by auto.
    assert_PROP (@field_compatible Shim.CS t_itab [] tab) by entailer!.
    rewrite prot3_shim_table1_itab_ptr by auto. rewrite Hsucc, Hvin, HS. unfold entry_val at 1.
    destruct (prot3_shim_table1_entry_next shp (e_peer Ep)
      (Val.of_bool (vin p (t_L T)), (Vint (e_type Ep), Vint (e_index Ep))) p) as [R HR].
    rewrite HR, prot3_shim_table1_link_snoc.
    Exists shp. apply andp_right; [apply prop_right; auto|]. cancel. repeat (apply -> wand_sepcon_adjoint).
    rewrite (prot3_shim_table1_open2 sht tab (t_remove T e) p shp Ep e she Ee) by auto.
    rewrite prot3_shim_table1_itab_ptr by auto. rewrite Hsucc', Hvin', HS', <- HV, <- HH.
    unfold entry_val. rewrite HR.
    change (t_D (t_remove T e)) with (t_D T).
    rewrite (prot3_shim_table1_pool_eq (t_L T) (t_L (t_remove T e)) (sdel (sdel (t_D T) p) e)).
    + cancel.
    + intros x sh E Hx.
      pose proof (prot3_shim_table1_sdel_ne _ _ _ _ _ (prot3_shim_table1_sdel_nodup _ p HND) Hx) as Hxe.
      pose proof (prot3_shim_table1_sdel_ne _ _ _ _ _ HND (prot3_shim_table1_sdel_in _ _ _ _ _ Hx)) as Hxp.
      rewrite HL, HL'. split.
      * apply prot3_shim_table1_succ_skip; auto.
      * apply (prot3_shim_table1_vin_skip x (L1 ++ [p]) e L2) in Hxe. rewrite <- !app_assoc in Hxe. exact Hxe.
Qed.

(* ---- insert: the table after remove, with the entry's index i ---- *)
Section Pool3.
Context {A: Type}.
Lemma prot3_shim_table1_supd_saddrs (D: list (val * share * A)) a v : saddrs (supd D a v) = saddrs D.
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; auto.
  destruct (EqDec_val x a); simpl; f_equal; auto.
Qed.

Lemma prot3_shim_table1_supd_in (D: list (val * share * A)) a v x sh w :
  In (x, sh, w) (supd D a v) -> exists w', In (x, sh, w') D.
Proof.
  induction D as [|[[y shy] u] D IH]; simpl; intros H; [contradiction|].
  destruct (EqDec_val y a); simpl in H; destruct H as [H|H].
  - inv H. eauto.
  - eauto.
  - inv H. eauto.
  - destruct (IH H) as [w' Hw']. eauto.
Qed.

Lemma prot3_shim_table1_supd_sfind_same (D: list (val * share * A)) a sh v w :
  sfind D a = Some (sh, w) -> sfind (supd D a v) a = Some (sh, v).
Proof.
  induction D as [|[[x shx] u] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a) as [->|n]; simpl.
  - inv H. destruct (EqDec_val a a); congruence.
  - destruct (EqDec_val x a); [contradiction|auto].
Qed.

Lemma prot3_shim_table1_supd_sfind_other (D: list (val * share * A)) a b v :
  b <> a -> sfind (supd D a v) b = sfind D b.
Proof.
  induction D as [|[[x shx] u] D IH]; simpl; intros H; auto.
  destruct (EqDec_val x a) as [->|n]; simpl.
  - destruct (EqDec_val a b); [congruence|auto].
  - destruct (EqDec_val x b); auto.
Qed.

Lemma prot3_shim_table1_supd_sdel (D: list (val * share * A)) a v : sdel (supd D a v) a = sdel D a.
Proof.
  induction D as [|[[x shx] u] D IH]; simpl; auto.
  destruct (EqDec_val x a) as [->|n]; simpl.
  - destruct (EqDec_val a a); congruence.
  - destruct (EqDec_val x a); [contradiction|]. f_equal; auto.
Qed.

Lemma prot3_shim_table1_supd_same (D: list (val * share * A)) a sh v :
  sfind D a = Some (sh, v) -> supd D a v = D.
Proof.
  induction D as [|[[x shx] u] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a) as [->|n]; [inv H; reflexivity|]. f_equal; auto.
Qed.
End Pool3.

Lemma prot3_shim_table1_vremove_ne e L x : In x (vremove e L) -> x <> e.
Proof.
  induction L as [|y L IH]; simpl; intros H; [contradiction|].
  destruct (EqDec_val y e); auto. destruct H; [subst; auto|auto].
Qed.

Lemma prot3_shim_table1_vremove_notin' e L : ~ In e (vremove e L).
Proof. intros H. apply (prot3_shim_table1_vremove_ne _ _ _ H). reflexivity. Qed.

Definition prot3_shim_table1_Ti (T: tstate) (e: val) (Ee: entry) (i: int) : tstate :=
  mkT (supd (t_D T) e (mkEntry (e_peer Ee) (e_type Ee) i)) (vremove e (t_L T)).

Lemma prot3_shim_table1_wf_supd T a v L :
  itable_wf T -> NoDup L -> incl L (saddrs (t_D T)) -> itable_wf (mkT (supd (t_D T) a v) L).
Proof.
  intros (H1 & H2 & H3 & H4) HN HI. unfold itable_wf; simpl.
  rewrite prot3_shim_table1_supd_saddrs. split; [|split; [|split]]; auto.
  rewrite Forall_forall in *. intros [[x sh] w] Hin.
  destruct (prot3_shim_table1_supd_in _ _ _ _ _ _ Hin) as [w' Hw']. apply (H4 _ Hw').
Qed.

Lemma prot3_shim_table1_wf_Ti T e Ee i : itable_wf T -> itable_wf (prot3_shim_table1_Ti T e Ee i).
Proof.
  intros HW. apply prot3_shim_table1_wf_supd; auto.
  - apply prot3_shim_table1_vremove_nodup, HW.
  - intros x Hx. apply HW. eapply prot3_shim_table1_vremove_in; eauto.
Qed.

Lemma prot3_shim_table1_Ti_open sht tab T e she Ee i :
  itable_wf T -> sfind (t_D T) e = Some (she, Ee) ->
  itable sht tab (prot3_shim_table1_Ti T e Ee i) =
  @data_at Shim.CS sht t_itab (hd nullval (vremove e (t_L T))) tab *
  (@data_at Shim.CS she t_entry_s (entry_val (mkEntry (e_peer Ee) (e_type Ee) i) nullval false) e *
   iter_sepcon (pool_item_rep (vremove e (t_L T))) (sdel (t_D T) e)).
Proof.
  intros HW HE.
  rewrite (prot3_shim_table1_open sht tab _ e she (mkEntry (e_peer Ee) (e_type Ee) i)).
  - unfold prot3_shim_table1_Ti; simpl. rewrite prot3_shim_table1_supd_sdel.
    rewrite prot3_shim_table1_succ_notin by apply prot3_shim_table1_vremove_notin'.
    replace (vin e (vremove e (t_L T))) with false; [reflexivity|].
    symmetry. apply Bool.not_true_is_false. rewrite prot3_shim_table1_vin_iff.
    apply prot3_shim_table1_vremove_notin'.
  - apply prot3_shim_table1_wf_Ti; auto.
  - unfold prot3_shim_table1_Ti; simpl. eapply prot3_shim_table1_supd_sfind_same; eauto.
Qed.

Lemma prot3_shim_table1_remove_Ti T e she Ee :
  sfind (t_D T) e = Some (she, Ee) -> t_remove T e = prot3_shim_table1_Ti T e Ee (e_index Ee).
Proof.
  intros HE. unfold t_remove, prot3_shim_table1_Ti. f_equal. destruct Ee as [p ty ix]; simpl.
  symmetry. eapply prot3_shim_table1_supd_same; eauto.
Qed.

Lemma prot3_shim_table1_Ti_indices T e Ee i :
  t_indices (prot3_shim_table1_Ti T e Ee i) (vremove e (t_L T)) = t_indices T (vremove e (t_L T)).
Proof.
  unfold t_indices. apply map_ext_in. intros x Hx. unfold t_entry, prot3_shim_table1_Ti; simpl.
  rewrite prot3_shim_table1_supd_sfind_other; auto. eapply prot3_shim_table1_vremove_ne; eauto.
Qed.

Lemma prot3_shim_table1_ins_close sht tab T e she Ee n :
  itable_wf T -> sfind (t_D T) e = Some (she, Ee) ->
  @data_at Shim.CS sht t_itab e tab *
  (@data_at Shim.CS she t_entry_s
     (entry_val (mkEntry (e_peer Ee) (e_type Ee) n) (hd nullval (vremove e (t_L T))) true) e *
   iter_sepcon (pool_item_rep (vremove e (t_L T))) (sdel (t_D T) e))
  |-- itable sht tab (t_insert T e n).
Proof.
  intros HW HE.
  assert (HI: t_insert T e n = mkT (supd (t_D T) e (mkEntry (e_peer Ee) (e_type Ee) n)) (e :: vremove e (t_L T))).
  { unfold t_insert, t_set_index. rewrite (prot3_shim_table1_tentry _ _ _ _ HE). reflexivity. }
  rewrite HI.
  rewrite (prot3_shim_table1_open sht tab _ e she (mkEntry (e_peer Ee) (e_type Ee) n)).
  - simpl. rewrite prot3_shim_table1_supd_sdel.
    destruct (EqDec_val e e); [|congruence].
    replace (vin e (e :: vremove e (t_L T))) with true
      by (symmetry; apply prot3_shim_table1_vin_iff; left; auto).
    rewrite (prot3_shim_table1_pool_eq (vremove e (t_L T)) (e :: vremove e (t_L T))); [cancel|].
    intros x sh E Hx. pose proof (prot3_shim_table1_sdel_ne _ _ _ _ _ (proj1 (proj2 (proj2 HW))) Hx).
    split.
    + symmetry. apply prot3_shim_table1_succ_skip0; auto.
    + symmetry. apply (prot3_shim_table1_vin_skip x [] e); auto.
  - apply prot3_shim_table1_wf_supd; auto.
    + constructor; [apply prot3_shim_table1_vremove_notin'|]. apply prot3_shim_table1_vremove_nodup, HW.
    + intros x [<-|Hx]; [eapply prot3_shim_table1_saddrs_in, prot3_shim_table1_sfind_In; eauto|].
      apply HW. eapply prot3_shim_table1_vremove_in; eauto.
  - simpl. eapply prot3_shim_table1_supd_sfind_same; eauto.
Qed.

Lemma prot3_shim_table1_inb_false i l : ~ In i l -> int_inb i l = false.
Proof.
  unfold int_inb. intros H. apply Bool.not_true_is_false. intros H1.
  apply existsb_exists in H1. destruct H1 as (x & Hx & He).
  apply Int.same_if_eq in He. subst. auto.
Qed.

Lemma prot3_shim_table1_inb_true i l : In i l -> int_inb i l = true.
Proof.
  unfold int_inb. intros H. apply existsb_exists. exists i. split; auto. apply Int.eq_true.
Qed.

Lemma prot3_shim_table1_ins_start sht tab T e raw :
  raw_ok T e raw -> itable_wf T ->
  exists she Ee v, itable_wf (raw_add T e raw) /\ sfind (t_D (raw_add T e raw)) e = Some (she, Ee) /\
  writable_share she /\
  itable sht tab (match raw with None => t_remove T e | Some _ => T end) * raw_rep e raw =
  @data_at Shim.CS sht t_itab (hd nullval (vremove e (t_L (raw_add T e raw)))) tab *
  (@data_at Shim.CS she t_entry_s (e_peer Ee, (nullval, (Val.of_bool false, (Vint (e_type Ee), v)))) e *
   iter_sepcon (pool_item_rep (vremove e (t_L (raw_add T e raw)))) (sdel (t_D (raw_add T e raw)) e)).
Proof.
  destruct raw as [[shr Er]|]; cbn [raw_ok raw_add raw_rep].
  - intros [Hw Hn] HW. exists shr, Er, Vundef.
    assert (HnL: ~ In e (t_L T)) by (intro; apply Hn; apply HW; auto).
    unfold t_add; simpl. destruct (EqDec_val e e); [|congruence].
    rewrite prot3_shim_table1_vremove_notin by auto.
    split; [|split; [reflexivity|split; [auto|]]].
    + destruct HW as (H1 & H2 & H3 & H4). unfold itable_wf; simpl. split; [auto|split; [|split]].
      * intros x Hx. right. apply H2; auto.
      * constructor; auto.
      * constructor; auto.
    + rewrite prot3_shim_table1_open0 by auto. unfold raw_entry. rewrite prot3_shim_table1_entry_S.
      apply pred_ext; cancel.
  - intros H HW. destruct (prot3_shim_table1_sfind_in _ _ H) as (she & Ee & HEe).
    exists she, Ee, (Vint (e_index Ee)). split; [auto|split; [auto|split]].
    + destruct HW as (_ & _ & _ & HF); eapply prot3_shim_table1_sfind_wr; eauto.
    + rewrite (prot3_shim_table1_remove_Ti T e she Ee HEe), (prot3_shim_table1_Ti_open sht tab T e she Ee (e_index Ee) HW HEe).
      rewrite sepcon_emp. unfold entry_val. destruct Ee; reflexivity.
Qed.

Section Bodies.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

Lemma body_in_use :
  @semax_body (QPvarspecs Shim.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_shim_index_in_use wg_shim_index_in_use_spec.
Proof.
  start_function.
  assert_PROP (itable_wf T) as HW by (unfold itable; entailer!).
  assert_PROP (is_pointer_or_null (hd nullval (t_L T))).
  { sep_apply (prot3_shim_table1_hd sht tab T [] (t_L T) eq_refl). entailer!. }
  rewrite prot3_shim_table1_open0 by auto. Intros.
  unfold Sfor. forward. gather_SEP 0 1. rewrite <- prot3_shim_table1_open0 by auto.
  forward_loop (EX L1: list val, EX L2: list val,
    PROP (t_L T = L1 ++ L2; ~ In idx (t_indices T L1))
    LOCAL (temp code._e (hd nullval L2); temp code._table tab; temp code._index (Vint idx))
    SEP (itable sht tab T))
  continue: (EX L1: list val, EX a: val, EX L2: list val,
    PROP (t_L T = L1 ++ a :: L2; ~ In idx (t_indices T (L1 ++ [a])))
    LOCAL (temp code._e a; temp code._table tab; temp code._index (Vint idx))
    SEP (itable sht tab T))
  break: (PROP (~ In idx (t_indices T (t_L T)))
    LOCAL (temp code._table tab; temp code._index (Vint idx))
    SEP (itable sht tab T)).
 { Exists (@nil val) (t_L T). entailer!. }
  { Intros L1 L2. rename H0 into HL, H1 into HI.
    assert_PROP (is_pointer_or_null (hd nullval L2)) as HP.
    { sep_apply (prot3_shim_table1_hd sht tab T L1 L2 HL). entailer!. }
    forward_if.
    { apply prot3_shim_table1_tc_hd with L1; auto. }
    { destruct L2 as [|a L2]; [simpl in H0; contradiction|]. simpl in H0 |- *.
      assert (Ha: In a (saddrs (t_D T))) by (eapply prot3_shim_table1_inL; eauto).
      destruct (prot3_shim_table1_sfind_in _ _ Ha) as (sh & E & HE).
      assert (writable_share sh) by (destruct HW as (_ & _ & _ & HF); eapply prot3_shim_table1_sfind_wr; eauto).
      rewrite (prot3_shim_table1_open sht tab T a sh E) by auto. repeat flatten_sepcon_in_SEP.
      unfold entry_val. forward. forward.
      gather_SEP 0 1 2. fold (entry_val E (succ_in (t_L T) a) (vin a (t_L T))). rewrite <- (prot3_shim_table1_open sht tab T a sh E) by auto.
      forward_if.
      - forward. rewrite prot3_shim_table1_inb_true; [entailer!|].
        eapply prot3_shim_table1_ind_in; eauto.
      - forward. Exists L1 a L2. entailer!. eapply prot3_shim_table1_ind_snoc; eauto. }
    { destruct L2 as [|a L2].
      - forward. entailer!. rewrite app_nil_r in HL. rewrite HL in *. auto.
      - simpl in H0. subst a.
        assert_PROP (isptr nullval).
        { sep_apply (prot3_shim_table1_isptr sht tab T nullval ltac:(eapply prot3_shim_table1_inL; eauto)).
          entailer!. }
        contradiction. }
  }
  { Intros L1 a L2. rename H0 into HL, H1 into HI.
    assert (Ha: In a (saddrs (t_D T))) by (eapply prot3_shim_table1_inL; eauto).
    destruct (prot3_shim_table1_sfind_in _ _ Ha) as (sh & E & HE).
    assert (writable_share sh) by (destruct HW as (_ & _ & _ & HF); eapply prot3_shim_table1_sfind_wr; eauto).
    assert (HS: succ_in (t_L T) a = hd nullval L2).
    { rewrite HL. apply prot3_shim_table1_succ. rewrite <- HL. apply HW. }
    assert_PROP (is_pointer_or_null (hd nullval L2)) as HP.
    { sep_apply (prot3_shim_table1_hd sht tab T (L1 ++ [a]) L2 ltac:(rewrite <- app_assoc; auto)). entailer!. }
    rewrite (prot3_shim_table1_open sht tab T a sh E) by auto. repeat flatten_sepcon_in_SEP.
    unfold entry_val. rewrite HS. forward.
    gather_SEP 0 1 2. rewrite <- HS. fold (entry_val E (succ_in (t_L T) a) (vin a (t_L T))).
    rewrite <- (prot3_shim_table1_open sht tab T a sh E) by auto.
    Exists (L1 ++ [a]) L2. entailer!.
    rewrite <- app_assoc; auto. }
  forward. rewrite prot3_shim_table1_inb_false by auto. entailer!.
Qed.

Lemma body_remove :
  @semax_body (QPvarspecs Shim.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_index_hashtable_remove wg_index_hashtable_remove_spec.
Proof.
  start_function.
  assert_PROP (itable_wf T) as HW by (unfold itable; entailer!).
  destruct raw as [[shr Er]|]; cbn [raw_ok raw_rep] in *.
  { destruct H as [Hshr Hnot]. unfold raw_entry. rewrite prot3_shim_table1_entry_S.
    forward. forward_if.
    - forward. rewrite <- prot3_shim_table1_entry_S. entailer!.
    - match goal with Hc: Int.zero <> Int.zero |- _ => contradiction Hc; auto end. }
  destruct (prot3_shim_table1_sfind_in _ _ H) as (she & Ee & HEe).
  assert (writable_share she) by (destruct HW as (_ & _ & _ & HF); eapply prot3_shim_table1_sfind_wr; eauto).
  rewrite (prot3_shim_table1_open sht tab T e she Ee) by auto. repeat flatten_sepcon_in_SEP.
  assert_PROP (@field_compatible Shim.CS t_itab [] tab) as Hfct by entailer!.
  unfold entry_val. forward.
  { entailer!. destruct (vin e (t_L T)); simpl; auto. }
  gather_SEP 0 1 2. fold (entry_val Ee (succ_in (t_L T) e) (vin e (t_L T))).
  rewrite <- (prot3_shim_table1_open sht tab T e she Ee) by auto.
  destruct (vin e (t_L T)) eqn:Hvin.
  2: { forward_if.
       - forward. entailer!.
         assert (HT: t_remove T e = T).
         { destruct T as [D L]. unfold t_remove; simpl in *. rewrite prot3_shim_table1_vremove_notin; auto.
           intros Hin. apply prot3_shim_table1_vin_iff in Hin. congruence. }
         rewrite HT. auto.
       - match goal with Hc: Int.zero <> Int.zero |- _ => contradiction Hc; auto end. }
  forward_if.
  { match goal with Hc: Int.one = Int.zero |- _ => inv Hc end. }
  apply prot3_shim_table1_vin_iff in Hvin.
  unfold Sfor. forward. forward. { entailer!. destruct Hfct; auto. }
  forward_loop (EX L1: list val, EX L2: list val,
     PROP (t_L T = L1 ++ L2; In e L2)
     LOCAL (temp code._link (prot3_shim_table1_link tab L1); temp code._table tab; temp code._entry e)
     SEP (itable sht tab T))
  continue: (EX L1: list val, EX p: val, EX L2: list val,
     PROP (t_L T = L1 ++ p :: L2; In e L2)
     LOCAL (temp code._link (prot3_shim_table1_link tab L1); temp code._table tab; temp code._entry e)
     SEP (itable sht tab T))
  break: (EX L1: list val, EX L2: list val, EX shl: share,
     PROP (t_L T = L1 ++ e :: L2; writable_share shl)
     LOCAL (temp code._table tab; temp code._entry e)
     SEP (@data_at Shim.CS shl (tptr t_entry_s) (hd nullval L2) (prot3_shim_table1_link tab L1);
          @data_at Shim.CS she t_entry_s (entry_val Ee (hd nullval L2) true) e;
          (@data_at Shim.CS shl (tptr t_entry_s) (hd nullval L2) (prot3_shim_table1_link tab L1) *
           @data_at Shim.CS she t_entry_s (entry_val Ee nullval false) e) -* itable sht tab (t_remove T e))).
  { Exists (@nil val) (t_L T). entailer!.
    unfold prot3_shim_table1_link; simpl. destruct Hfct as [Hp _]. destruct tab; try contradiction.
    simpl. rewrite Ptrofs.add_zero. reflexivity. }
  { Intros L1 L2. rename H2 into HL, H3 into HeL2.
    destruct L2 as [|p L2]; [contradiction|]. change (hd nullval (p :: L2)) with p.
    assert (Hp: In p (saddrs (t_D T))) by (eapply prot3_shim_table1_inL; eauto).
    assert_PROP (isptr p) as Hpp by (sep_apply (prot3_shim_table1_isptr sht tab T p Hp); entailer!).
    sep_apply (prot3_shim_table1_link_rd sht tab T L1 (p :: L2) SH HW HL). Intros shl.
    forward. sep_apply modus_ponens_wand.
    forward_if.
    { apply (prot3_shim_table1_tc_hd sht tab T L1 (p :: L2)); auto. }
    2: { subst p. contradiction. }
    forward.
    sep_apply (prot3_shim_table1_link_rd sht tab T L1 (p :: L2) SH HW HL). Intros shl'.
    forward. sep_apply modus_ponens_wand.
    forward_if.
    { entailer!. apply denote_tc_test_eq_split; apply prot3_shim_table1_valid; auto. }
    - subst p.
      assert_PROP (is_pointer_or_null (hd nullval L2)) as HP2
        by (sep_apply (prot3_shim_table1_hd sht tab T (L1 ++ [e]) L2 ltac:(rewrite <- app_assoc; auto)); entailer!).
      sep_apply (prot3_shim_table1_link_wr sht tab T L1 e L2 she Ee SH HW HL HEe). Intros shw.
      unfold entry_val. forward. forward. forward.
      Exists L1 L2 shw. unfold entry_val. entailer!.
    - forward. Exists L1 p L2. entailer!. destruct HeL2; [congruence|auto]. }
  { Intros L1 p L2. rename H2 into HL, H3 into HeL2.
    assert (Hp: In p (saddrs (t_D T))) by (eapply prot3_shim_table1_inL; eauto).
    assert_PROP (@field_compatible Shim.CS t_entry_s [] p) as Hfp
      by (sep_apply (prot3_shim_table1_fc sht tab T p Hp); entailer!).
    sep_apply (prot3_shim_table1_link_rd sht tab T L1 (p :: L2) SH HW HL). Intros shl.
    change (hd nullval (p :: L2)) with p.
    assert (Hpp: isptr p) by (destruct Hfp; auto).
    forward. sep_apply modus_ponens_wand.
    forward.
    Exists (L1 ++ [p]) L2. entailer!.
    split; [rewrite <- app_assoc; auto|]. rewrite prot3_shim_table1_link_snoc.
    rewrite field_compatible_field_address
      by (apply field_compatible_cons; simpl; split; auto; right; left; reflexivity).
    reflexivity. }
  Intros L1 L2 shl.
  unfold entry_val. forward. forward.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
  change (Vint Int.zero) with (Val.of_bool false).
  gather_SEP 0 1. entailer!. apply modus_ponens_wand.
Qed.

Lemma body_insert :
  @semax_body (QPvarspecs Shim.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_index_hashtable_insert wg_index_hashtable_insert_spec.
Proof.
  start_function.
  assert_PROP (itable_wf T) as HW by (unfold itable; entailer!).
  forward_call (sht, tab, T, e, raw).
  destruct (prot3_shim_table1_ins_start sht tab T e raw H HW) as (she & Ee & v0 & HW0 & HE0 & Hshe & Heq).
  gather_SEP 0 1. rewrite Heq. clear Heq. repeat flatten_sepcon_in_SEP.
  set (T0 := raw_add T e raw) in *. clearbody T0.
  forward_loop (EX v: val, EX S': shim,
      PROP (forall n, shim_u32 S' n = shim_u32 S n)
      LOCAL (temp code._table tab; temp code._entry e; gvars gv)
      SEP (@data_at Shim.CS sht t_itab (hd nullval (vremove e (t_L T0))) tab;
           @data_at Shim.CS she t_entry_s (e_peer Ee, (nullval, (Val.of_bool false, (Vint (e_type Ee), v)))) e;
           iter_sepcon (pool_item_rep (vremove e (t_L T0))) (sdel (t_D T0) e);
           shim_state gv S'))
    continue: (EX n: int,
      PROP ()
      LOCAL (temp code._table tab; temp code._entry e; gvars gv)
      SEP (itable sht tab (prot3_shim_table1_Ti T0 e Ee n); shim_state gv (shim_u32 S n)))
    break: (EX n: int,
      PROP (int_inb n (t_indices (prot3_shim_table1_Ti T0 e Ee n) (vremove e (t_L T0))) = false)
      LOCAL (temp code._table tab; temp code._entry e; gvars gv)
      SEP (itable sht tab (prot3_shim_table1_Ti T0 e Ee n); shim_state gv (shim_u32 S n))).
  - Exists v0 S. entailer!.
  - Intros v S'. match goal with Hx: forall n, shim_u32 _ n = _ |- _ => rename Hx into HS' end.
    forward_call (gv, S'). Intros n.
    forward.
    Exists n. rewrite HS'. rewrite (prot3_shim_table1_Ti_open sht tab T0 e she Ee n) by auto.
    unfold entry_val; cbn [e_peer e_type e_index]. entailer!.
  - Intros n.
    rewrite (prot3_shim_table1_Ti_open sht tab T0 e she Ee n) by auto. repeat flatten_sepcon_in_SEP.
    unfold entry_val. forward.
    gather_SEP 0 1 2. fold (entry_val (mkEntry (e_peer Ee) (e_type Ee) n) nullval false).
    rewrite <- (prot3_shim_table1_Ti_open sht tab T0 e she Ee n) by auto.
    forward_call (sht, tab, prot3_shim_table1_Ti T0 e Ee n, n).
    destruct (int_inb n (t_indices (prot3_shim_table1_Ti T0 e Ee n) (t_L (prot3_shim_table1_Ti T0 e Ee n)))) eqn:Hb.
    + forward_if; [|discriminate].
      forward. Exists (Vint n) (shim_u32 S n). entailer!.
      rewrite (prot3_shim_table1_Ti_open sht tab T0 e she Ee n) by auto. unfold entry_val; cbn [e_peer e_type e_index].
      entailer!.
    + forward_if; [discriminate|].
      forward. Exists n. entailer!.
  - Intros n. match goal with Hx: int_inb _ _ = false |- _ => rename Hx into Hb end.
    assert_PROP (is_pointer_or_null (hd nullval (vremove e (t_L T0)))) as Hhd
      by (sep_apply (prot3_shim_table1_hd sht tab (prot3_shim_table1_Ti T0 e Ee n) [] (vremove e (t_L T0)) eq_refl);
          entailer!).
    rewrite (prot3_shim_table1_Ti_open sht tab T0 e she Ee n) by auto. repeat flatten_sepcon_in_SEP.
    unfold entry_val. cbn [e_peer e_type e_index].
    forward. forward. forward. forward. forward. forward.
    Exists n. apply andp_right.
    { apply prop_right. split; auto. unfold t_fresh.
      rewrite <- (prot3_shim_table1_Ti_indices T0 e Ee n). intros Hin.
      rewrite prot3_shim_table1_inb_true in Hb by auto. discriminate. }
    eapply derives_trans; [|apply sepcon_derives;
      [apply (prot3_shim_table1_ins_close sht tab T0 e she Ee n HW0 HE0) | apply derives_refl]].
    unfold entry_val; cbn [e_peer e_type e_index]. change (Vint Int.one) with (Val.of_bool true). cancel.
Qed.

End Bodies.

Theorem prot_bodies3_shim_table1 :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body (QPvarspecs Shim.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_index_hashtable_remove wg_index_hashtable_remove_spec) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_shim_index_in_use wg_shim_index_in_use_spec) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_index_hashtable_insert wg_index_hashtable_insert_spec).
Proof.
  intros. split; [|split].
  - apply body_remove.
  - apply body_in_use.
  - apply body_insert.
Qed.
