(* port of v3's prot3_shim_table2_replace.v to the v4 specifications (prot_specs4.v,
   context Gprot4: refcount_t warnings exact). v3 text follows. *)
(* Group shim_table2: the body of wg_index_hashtable_replace (patch/wg_shim.c).
   Pool lemmas: prot_body3_shim_table1.v (lemmas prot4_shim_table1_...). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.
Require Import VST.msl.iter_sepcon.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_cs.
Require Import WgNoise.proof.protocol4.prot4_shim_table1.
Local Open Scope logic.

(* ---- lists ---- *)
Lemma prot4_shim_table2_succ_rep0 x o n B : x <> o -> x <> n -> succ_in (o :: B) x = succ_in (n :: B) x.
Proof.
  intros H1 H2. simpl. destruct (EqDec_val o x); [congruence|]. destruct (EqDec_val n x); [congruence|].
  reflexivity.
Qed.

Lemma prot4_shim_table2_succ_rep x A p o n B : x <> p -> x <> o -> x <> n ->
  succ_in (A ++ p :: o :: B) x = succ_in (A ++ p :: n :: B) x.
Proof.
  induction A as [|y A IH]; simpl; intros H1 H2 H3.
  - destruct (EqDec_val p x); [congruence|]. destruct (EqDec_val o x); [congruence|].
    destruct (EqDec_val n x); [congruence|]. reflexivity.
  - destruct (EqDec_val y x).
    + destruct A; reflexivity.
    + auto.
Qed.

Lemma prot4_shim_table2_vin_rep x A o n B : x <> o -> x <> n -> vin x (A ++ o :: B) = vin x (A ++ n :: B).
Proof.
  intros H1 H2. apply Bool.eq_true_iff_eq. rewrite !prot4_shim_table1_vin_iff. split; intros H;
  apply in_app_or in H; apply in_or_app; destruct H as [?|[?|?]]; simpl; auto; congruence.
Qed.

Lemma prot4_shim_table2_vreplace A o n B : ~ In o A -> vreplace o n (A ++ o :: B) = A ++ n :: B.
Proof.
  induction A as [|x A IH]; simpl; intros H.
  - destruct (EqDec_val o o); [reflexivity|congruence].
  - destruct (EqDec_val x o); [exfalso; auto|]. rewrite IH; auto.
Qed.

Lemma prot4_shim_table2_nodup_rep (A B: list val) (o n: val) :
  NoDup (A ++ o :: B) -> ~ In n (A ++ o :: B) -> NoDup (A ++ n :: B).
Proof.
  intros H1 H2. apply Permutation.Permutation_NoDup with (n :: A ++ B); [apply Permutation.Permutation_middle|].
  constructor.
  - intros H. apply H2. apply in_app_or in H. apply in_or_app. simpl. tauto.
  - eapply NoDup_remove_1; eauto.
Qed.

Lemma prot4_shim_table2_wf_rep T A o n B :
  itable_wf T -> t_L T = A ++ o :: B -> ~ In n (t_L T) -> In n (saddrs (t_D T)) ->
  itable_wf (mkT (t_D T) (A ++ n :: B)).
Proof.
  intros (H1 & H2 & H3 & H4) HL Hn HnD. unfold itable_wf; simpl. split; [|split; [|split]]; auto.
  - rewrite HL in H1, Hn. apply prot4_shim_table2_nodup_rep with o; auto.
  - intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx|[Hx|Hx]]; [| subst; auto |];
      apply H2; rewrite HL; apply in_or_app; simpl; auto.
Qed.

Lemma prot4_shim_table2_open3 sht tab T p shp Ep o sho Eo n shn En :
  itable_wf T -> sfind (t_D T) p = Some (shp, Ep) -> sfind (t_D T) o = Some (sho, Eo) ->
  sfind (t_D T) n = Some (shn, En) -> p <> o -> p <> n -> o <> n ->
  itable sht tab T =
  @data_at Shim.CS sht t_itab (hd nullval (t_L T)) tab *
  (@data_at Shim.CS shp t_entry_s (entry_val Ep (succ_in (t_L T) p) (vin p (t_L T))) p *
   (@data_at Shim.CS sho t_entry_s (entry_val Eo (succ_in (t_L T) o) (vin o (t_L T))) o *
    (@data_at Shim.CS shn t_entry_s (entry_val En (succ_in (t_L T) n) (vin n (t_L T))) n *
     iter_sepcon (pool_item_rep (t_L T)) (sdel (sdel (sdel (t_D T) p) o) n)))).
Proof.
  intros HW Hp Ho Hn H1 H2 H3. rewrite (prot4_shim_table1_open2 sht tab T p shp Ep o sho Eo) by auto.
  rewrite (prot4_shim_table1_split (sdel (sdel (t_D T) p) o) n shn En)
    by (rewrite !prot4_shim_table1_sfind_sdel; auto).
  unfold pool_item_rep at 1, entry_at. rewrite prot4_shim_table1_entry_S. reflexivity.
Qed.

(* ---- the link to old: write new there ---- *)
Lemma prot4_shim_table2_link_rep sht tab T L1 o L2 sho Eo n shn En :
  writable_share sht -> itable_wf T -> t_L T = L1 ++ o :: L2 -> ~ In n (t_L T) ->
  sfind (t_D T) o = Some (sho, Eo) -> sfind (t_D T) n = Some (shn, En) -> o <> n ->
  itable sht tab T |-- EX shl: share, !! writable_share shl &&
    (@data_at Shim.CS shl (tptr t_entry_s) o (prot4_shim_table1_link tab L1) *
     @data_at Shim.CS sho t_entry_s (entry_val Eo (hd nullval L2) true) o *
     @data_at Shim.CS shn t_entry_s (entry_val En nullval false) n *
     ((@data_at Shim.CS shl (tptr t_entry_s) n (prot4_shim_table1_link tab L1) *
       @data_at Shim.CS sho t_entry_s (entry_val Eo nullval false) o *
       @data_at Shim.CS shn t_entry_s (entry_val En (hd nullval L2) true) n) -*
      itable sht tab (mkT (t_D T) (L1 ++ n :: L2)))).
Proof.
  intros Hsh HW HL Hn Ho HnE Hon.
  assert (HnD: In n (saddrs (t_D T)))
    by (eapply prot4_shim_table1_saddrs_in, prot4_shim_table1_sfind_In; eauto).
  pose proof (prot4_shim_table2_wf_rep T L1 o n L2 HW HL Hn HnD) as HW'.
  assert (HN: NoDup (L1 ++ o :: L2)) by (rewrite <- HL; apply HW).
  assert (HND: NoDup (saddrs (t_D T))) by apply HW.
  assert (Ho1: ~ In o L1) by (intro; apply (NoDup_remove_2 _ _ _ HN); apply in_or_app; auto).
  assert (Ho2: ~ In o L2) by (intro; apply (NoDup_remove_2 _ _ _ HN); apply in_or_app; auto).
  assert (Hn1: ~ In n L1) by (intro; apply Hn; rewrite HL; apply in_or_app; auto).
  assert (Hn2: ~ In n L2) by (intro; apply Hn; rewrite HL; apply in_or_app; simpl; auto).
  assert (HN': NoDup (L1 ++ n :: L2)) by apply HW'.
  set (T' := mkT (t_D T) (L1 ++ n :: L2)) in *.
  assert (HL': t_L T' = L1 ++ n :: L2) by reflexivity.
  assert (Hso: succ_in (t_L T) o = hd nullval L2) by (rewrite HL; apply prot4_shim_table1_succ; auto).
  assert (Hvo: vin o (t_L T) = true).
  { apply prot4_shim_table1_vin_iff. rewrite HL. apply in_or_app. simpl; auto. }
  assert (Hsn: succ_in (t_L T) n = nullval) by (apply prot4_shim_table1_succ_notin; auto).
  assert (Hvn: vin n (t_L T) = false).
  { apply Bool.not_true_is_false. rewrite prot4_shim_table1_vin_iff. auto. }
  assert (Hso': succ_in (t_L T') o = nullval).
  { apply prot4_shim_table1_succ_notin. rewrite HL'. intro H. apply in_app_or in H.
    destruct H as [H|[H|H]]; auto. }
  assert (Hvo': vin o (t_L T') = false).
  { apply Bool.not_true_is_false. rewrite prot4_shim_table1_vin_iff, HL'. intro H. apply in_app_or in H.
    destruct H as [H|[H|H]]; auto. }
  assert (Hsn': succ_in (t_L T') n = hd nullval L2) by (rewrite HL'; apply prot4_shim_table1_succ; auto).
  assert (Hvn': vin n (t_L T') = true).
  { apply prot4_shim_table1_vin_iff. rewrite HL'. apply in_or_app. simpl; auto. }
  assert (HE'o: sfind (t_D T') o = Some (sho, Eo)) by exact Ho.
  assert (HE'n: sfind (t_D T') n = Some (shn, En)) by exact HnE.
  destruct L1 as [|p L1 _] using rev_ind.
  - simpl in HL. rewrite app_nil_l in HL'.
    rewrite (prot4_shim_table1_open2 sht tab T o sho Eo n shn En) by auto.
    assert_PROP (@field_compatible Shim.CS t_itab [] tab) by entailer!.
    rewrite prot4_shim_table1_itab_ptr by auto. rewrite Hso, Hvo, Hsn, Hvn. rewrite HL at 1.
    unfold prot4_shim_table1_link; simpl.
    Exists sht. apply andp_right; [apply prop_right; auto|]. cancel. repeat (apply -> wand_sepcon_adjoint).
    rewrite (prot4_shim_table1_open2 sht tab T' o sho Eo n shn En) by auto.
    rewrite prot4_shim_table1_itab_ptr by auto. rewrite Hso', Hvo', Hsn', Hvn'. rewrite HL' at 1.
    change (t_D T') with (t_D T).
    rewrite (prot4_shim_table1_pool_eq (t_L T') (t_L T) (sdel (sdel (t_D T) o) n)).
    + simpl. cancel.
    + intros x sh E Hx.
      pose proof (prot4_shim_table1_sdel_ne _ _ _ _ _ (prot4_shim_table1_sdel_nodup _ o HND) Hx) as Hxn.
      pose proof (prot4_shim_table1_sdel_ne _ _ _ _ _ HND (prot4_shim_table1_sdel_in _ _ _ _ _ Hx)) as Hxo.
      rewrite HL, HL'. split.
      * symmetry. apply prot4_shim_table2_succ_rep0; auto.
      * symmetry. apply (prot4_shim_table2_vin_rep x [] o n L2); auto.
  - rewrite <- app_assoc in HL, HL'. simpl in HL. change ([p] ++ n :: L2) with (p :: n :: L2) in HL'.
    assert (Hpo: p <> o) by (intros ->; apply Ho1; apply in_or_app; simpl; auto).
    assert (Hpn: p <> n) by (intros ->; apply Hn1; apply in_or_app; simpl; auto).
    assert (Hp: In p (saddrs (t_D T))) by (eapply prot4_shim_table1_inL; eauto).
    destruct (prot4_shim_table1_sfind_in _ _ Hp) as (shp & Ep & HEp).
    assert (writable_share shp) by (destruct HW as (_ & _ & _ & HF); eapply prot4_shim_table1_sfind_wr; eauto).
    assert (HS: succ_in (t_L T) p = o).
    { rewrite HL. apply (prot4_shim_table1_succ L1 p (o :: L2)). rewrite <- HL. apply HW. }
    assert (HS': succ_in (t_L T') p = n).
    { rewrite HL'. apply (prot4_shim_table1_succ L1 p (n :: L2)). rewrite <- HL'. apply HW'. }
    assert (HV: vin p (t_L T) = vin p (t_L T')).
    { rewrite HL, HL'. pose proof (prot4_shim_table2_vin_rep p (L1 ++ [p]) o n L2 Hpo Hpn) as E.
      rewrite <- !app_assoc in E. exact E. }
    assert (HH: hd nullval (t_L T) = hd nullval (t_L T')).
    { rewrite HL, HL'. destruct L1; reflexivity. }
    assert (HE'p: sfind (t_D T') p = Some (shp, Ep)) by exact HEp.
    rewrite (prot4_shim_table2_open3 sht tab T p shp Ep o sho Eo n shn En) by auto.
    rewrite Hso, Hvo, Hsn, Hvn, HS. unfold entry_val at 1.
    destruct (prot4_shim_table1_entry_next shp (e_peer Ep)
      (Val.of_bool (vin p (t_L T)), (Vint (e_type Ep), Vint (e_index Ep))) p) as [R HR].
    rewrite HR, prot4_shim_table1_link_snoc.
    Exists shp. apply andp_right; [apply prop_right; auto|]. cancel. repeat (apply -> wand_sepcon_adjoint).
    rewrite (prot4_shim_table2_open3 sht tab T' p shp Ep o sho Eo n shn En) by auto.
    rewrite Hso', Hvo', Hsn', Hvn', HS', <- HV, <- HH.
    unfold entry_val. rewrite HR.
    change (t_D T') with (t_D T).
    rewrite (prot4_shim_table1_pool_eq (t_L T') (t_L T) (sdel (sdel (sdel (t_D T) p) o) n)).
    + cancel.
    + intros x sh E Hx.
      pose proof (prot4_shim_table1_sdel_ne _ _ _ _ _
        (prot4_shim_table1_sdel_nodup _ o (prot4_shim_table1_sdel_nodup _ p HND)) Hx) as Hxn.
      pose proof (prot4_shim_table1_sdel_in _ _ _ _ _ Hx) as Hx1.
      pose proof (prot4_shim_table1_sdel_ne _ _ _ _ _ (prot4_shim_table1_sdel_nodup _ p HND) Hx1) as Hxo.
      pose proof (prot4_shim_table1_sdel_ne _ _ _ _ _ HND (prot4_shim_table1_sdel_in _ _ _ _ _ Hx1)) as Hxp.
      rewrite HL, HL'. split.
      * symmetry. apply prot4_shim_table2_succ_rep; auto.
      * pose proof (prot4_shim_table2_vin_rep x (L1 ++ [p]) o n L2 Hxo Hxn) as Ev.
        rewrite <- !app_assoc in Ev. symmetry. exact Ev.
Qed.

(* ---- the table after new->index = old->index ---- *)
Definition prot4_shim_table2_T1 (T: tstate) (n: val) (En: entry) (i: int) : tstate :=
  mkT (supd (t_D T) n (mkEntry (e_peer En) (e_type En) i)) (t_L T).

Lemma prot4_shim_table2_T1_wf T n En i : itable_wf T -> itable_wf (prot4_shim_table2_T1 T n En i).
Proof. intros HW. apply prot4_shim_table1_wf_supd; apply HW. Qed.

Lemma prot4_shim_table2_T1_open sht tab T n shn En i :
  itable_wf T -> sfind (t_D T) n = Some (shn, En) ->
  itable sht tab (prot4_shim_table2_T1 T n En i) =
  @data_at Shim.CS sht t_itab (hd nullval (t_L T)) tab *
  (@data_at Shim.CS shn t_entry_s (entry_val (mkEntry (e_peer En) (e_type En) i) (succ_in (t_L T) n) (vin n (t_L T))) n *
   iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) n)).
Proof.
  intros HW HE.
  rewrite (prot4_shim_table1_open sht tab _ n shn (mkEntry (e_peer En) (e_type En) i)).
  - unfold prot4_shim_table2_T1; simpl. rewrite prot4_shim_table1_supd_sdel. reflexivity.
  - apply prot4_shim_table2_T1_wf; auto.
  - unfold prot4_shim_table2_T1; simpl. eapply prot4_shim_table1_supd_sfind_same; eauto.
Qed.

Lemma prot4_shim_table2_T1_same T n shn En :
  sfind (t_D T) n = Some (shn, En) -> prot4_shim_table2_T1 T n En (e_index En) = T.
Proof.
  intros HE. destruct T as [D L]. unfold prot4_shim_table2_T1; simpl in *. f_equal.
  destruct En as [p ty ix]; simpl. eapply prot4_shim_table1_supd_same; eauto.
Qed.

Lemma prot4_shim_table2_T1_sfind T n En i a :
  a <> n -> sfind (t_D (prot4_shim_table2_T1 T n En i)) a = sfind (t_D T) a.
Proof. intros. unfold prot4_shim_table2_T1; simpl. apply prot4_shim_table1_supd_sfind_other; auto. Qed.

Lemma prot4_shim_table2_T1_sfind_n T n shn En i :
  sfind (t_D T) n = Some (shn, En) ->
  sfind (t_D (prot4_shim_table2_T1 T n En i)) n = Some (shn, mkEntry (e_peer En) (e_type En) i).
Proof. intros. unfold prot4_shim_table2_T1; simpl. eapply prot4_shim_table1_supd_sfind_same; eauto. Qed.

Lemma prot4_shim_table2_result T o n sho Eo shn En L1 L2 :
  sfind (t_D T) o = Some (sho, Eo) -> sfind (t_D T) n = Some (shn, En) ->
  t_L T = L1 ++ o :: L2 -> ~ In o L1 ->
  t_replace T o n = (true, mkT (t_D (prot4_shim_table2_T1 T n En (e_index Eo))) (L1 ++ n :: L2)).
Proof.
  intros Ho Hn HL Ho1. unfold t_replace.
  replace (vin o (t_L T)) with true
    by (symmetry; apply prot4_shim_table1_vin_iff; rewrite HL; apply in_or_app; simpl; auto).
  rewrite (prot4_shim_table1_tentry _ _ _ _ Ho). unfold t_set_index.
  rewrite (prot4_shim_table1_tentry _ _ _ _ Hn). rewrite HL, prot4_shim_table2_vreplace by auto.
  reflexivity.
Qed.

Section Bodies.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

Lemma prot4_shim_table2_body_replace :
  @semax_body (QPvarspecs Shim.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_index_hashtable_replace wg_index_hashtable_replace_spec.
Proof.
  start_function.
  assert_PROP (itable_wf T) as HW by (unfold itable; entailer!).
  rename H into Ho, H0 into Hn, H1 into Hon, H2 into HnL.
  destruct (prot4_shim_table1_sfind_in _ _ Ho) as (sho & Eo & HEo).
  destruct (prot4_shim_table1_sfind_in _ _ Hn) as (shn & En & HEn).
  assert (writable_share sho) by (destruct HW as (_ & _ & _ & HF); eapply prot4_shim_table1_sfind_wr; eauto).
  assert (writable_share shn) by (destruct HW as (_ & _ & _ & HF); eapply prot4_shim_table1_sfind_wr; eauto).
  assert (Hsn: succ_in (t_L T) new = nullval) by (apply prot4_shim_table1_succ_notin; auto).
  assert (Hvn: vin new (t_L T) = false).
  { apply Bool.not_true_is_false. rewrite prot4_shim_table1_vin_iff. auto. }
  rewrite (prot4_shim_table1_open sht tab T old sho Eo) by auto. repeat flatten_sepcon_in_SEP.
  unfold entry_val. forward.
  { entailer!. destruct (vin old (t_L T)); simpl; auto. }
  gather_SEP 0 1 2. fold (entry_val Eo (succ_in (t_L T) old) (vin old (t_L T))).
  rewrite <- (prot4_shim_table1_open sht tab T old sho Eo) by auto.
  destruct (vin old (t_L T)) eqn:Hvin.
  2: { forward_if.
       - forward. unfold t_replace. rewrite Hvin. entailer!. apply derives_refl.
       - match goal with Hc: Int.zero <> Int.zero |- _ => contradiction Hc; auto end. }
  forward_if.
  { match goal with Hc: Int.one = Int.zero |- _ => inv Hc end. }
  apply prot4_shim_table1_vin_iff in Hvin.
  assert (Hvin' := Hvin). apply in_split in Hvin'. destruct Hvin' as (A0 & B0 & HL0).
  rewrite (prot4_shim_table1_open sht tab T old sho Eo) by auto. repeat flatten_sepcon_in_SEP.
  assert_PROP (@field_compatible Shim.CS t_itab [] tab) as Hfct by entailer!.
  unfold entry_val. forward. forward.
  gather_SEP 0 1 2. fold (entry_val Eo (succ_in (t_L T) old) (vin old (t_L T))).
  rewrite <- (prot4_shim_table1_open sht tab T old sho Eo) by auto.
  rewrite (prot4_shim_table1_open sht tab T new shn En) by auto. repeat flatten_sepcon_in_SEP.
  unfold entry_val. forward.
  change (@data_at Shim.CS shn t_entry_s
    (e_peer En, (succ_in (t_L T) new, (Val.of_bool (vin new (t_L T)), (Vint (e_type En), Vint (e_index Eo))))) new)
    with (@data_at Shim.CS shn t_entry_s (entry_val (mkEntry (e_peer En) (e_type En) (e_index Eo)) (succ_in (t_L T) new) (vin new (t_L T))) new).
  gather_SEP 0 1 2.
  rewrite <- (prot4_shim_table2_T1_open sht tab T new shn En (e_index Eo)) by auto.
  set (T1 := prot4_shim_table2_T1 T new En (e_index Eo)).
  set (En1 := mkEntry (e_peer En) (e_type En) (e_index Eo)).
  assert (HW1: itable_wf T1) by (apply prot4_shim_table2_T1_wf; auto).
  assert (HEo1: sfind (t_D T1) old = Some (sho, Eo)) by (unfold T1; rewrite prot4_shim_table2_T1_sfind; auto).
  assert (HEn1: sfind (t_D T1) new = Some (shn, En1)) by (unfold T1; eapply prot4_shim_table2_T1_sfind_n; eauto).
  assert (Ho1: In old (saddrs (t_D T1))) by (eapply prot4_shim_table1_saddrs_in, prot4_shim_table1_sfind_In; eauto).
  forward.
  { entailer!. destruct Hfct; auto. }
  forward_loop (EX L1: list val, EX L2: list val,
     PROP (t_L T = L1 ++ L2; In old L2)
     LOCAL (temp code._link (prot4_shim_table1_link tab L1); temp code._table tab; temp code._old old;
            temp code._new new)
     SEP (itable sht tab T1))
  continue: (EX L1: list val, EX p: val, EX L2: list val,
     PROP (t_L T = L1 ++ p :: L2; In old L2)
     LOCAL (temp code._link (prot4_shim_table1_link tab L1); temp code._table tab; temp code._old old;
            temp code._new new)
     SEP (itable sht tab T1))
  break: (EX L1: list val, EX L2: list val, EX shl: share,
     PROP (t_L T = L1 ++ old :: L2; writable_share shl; is_pointer_or_null (hd nullval L2))
     LOCAL (temp code._table tab; temp code._old old; temp code._new new)
     SEP (@data_at Shim.CS shl (tptr t_entry_s) new (prot4_shim_table1_link tab L1);
          @data_at Shim.CS sho t_entry_s (entry_val Eo (hd nullval L2) true) old;
          @data_at Shim.CS shn t_entry_s (entry_val En1 nullval false) new;
          (@data_at Shim.CS shl (tptr t_entry_s) new (prot4_shim_table1_link tab L1) *
           @data_at Shim.CS sho t_entry_s (entry_val Eo nullval false) old *
           @data_at Shim.CS shn t_entry_s (entry_val En1 (hd nullval L2) true) new) -*
          itable sht tab (mkT (t_D T1) (L1 ++ new :: L2)))).
  { Exists (@nil val) (t_L T). entailer!.
    unfold prot4_shim_table1_link; simpl. destruct Hfct as [Hp _]. destruct tab; try contradiction.
    simpl. rewrite Ptrofs.add_zero. reflexivity. }
  { Intros L1 L2. rename H2 into HL, H3 into HoL2.
    destruct L2 as [|p L2]; [contradiction|]. change (hd nullval (p :: L2)) with p.
    assert (Hp: In p (saddrs (t_D T1))) by (eapply prot4_shim_table1_inL; eauto).
    assert_PROP (isptr p) as Hpp by (sep_apply (prot4_shim_table1_isptr sht tab T1 p Hp); entailer!).
    sep_apply (prot4_shim_table1_link_rd sht tab T1 L1 (p :: L2) SH HW1 HL). Intros shl.
    forward. sep_apply modus_ponens_wand.
    forward_if.
    { apply (prot4_shim_table1_tc_hd sht tab T1 L1 (p :: L2)); auto. }
    2: { subst p. contradiction. }
    forward.
    sep_apply (prot4_shim_table1_link_rd sht tab T1 L1 (p :: L2) SH HW1 HL). Intros shl'.
    forward. sep_apply modus_ponens_wand.
    forward_if.
    { entailer!. apply denote_tc_test_eq_split; apply prot4_shim_table1_valid; auto. }
    - subst p.
      assert_PROP (is_pointer_or_null (hd nullval L2)) as HP2
        by (sep_apply (prot4_shim_table1_hd sht tab T1 (L1 ++ [old]) L2 ltac:(rewrite <- app_assoc; auto)); entailer!).
      sep_apply (prot4_shim_table2_link_rep sht tab T1 L1 old L2 sho Eo new shn En1 SH HW1 HL HnL HEo1 HEn1 Hon).
      Intros shw.
      forward. forward.
      Exists L1 L2 shw. entailer!.
    - forward. Exists L1 p L2. entailer!. destruct HoL2; [congruence|auto]. }
  { Intros L1 p L2. rename H2 into HL, H3 into HoL2.
    assert (Hp: In p (saddrs (t_D T1))) by (eapply prot4_shim_table1_inL; eauto).
    assert_PROP (@field_compatible Shim.CS t_entry_s [] p) as Hfp
      by (sep_apply (prot4_shim_table1_fc sht tab T1 p Hp); entailer!).
    sep_apply (prot4_shim_table1_link_rd sht tab T1 L1 (p :: L2) SH HW1 HL). Intros shl.
    change (hd nullval (p :: L2)) with p.
    assert (Hpp: isptr p) by (destruct Hfp; auto).
    forward. sep_apply modus_ponens_wand.
    forward.
    Exists (L1 ++ [p]) L2. entailer!.
    split; [rewrite <- app_assoc; auto|]. rewrite prot4_shim_table1_link_snoc.
    rewrite field_compatible_field_address
      by (apply field_compatible_cons; simpl; split; auto; right; left; reflexivity).
    reflexivity. }
  Intros L1 L2 shl. rename H2 into HL.
  assert (HN: NoDup (L1 ++ old :: L2)) by (rewrite <- HL; apply HW).
  assert (HoL1: ~ In old L1) by (intro; apply (NoDup_remove_2 _ _ _ HN); apply in_or_app; auto).
  unfold entry_val. forward. forward. forward. forward. forward.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
  change (Vint Int.zero) with (Val.of_bool false).
  change (Vint Int.one) with (Val.of_bool true).
  gather_SEP 0 1 2 3. rewrite <- !sepcon_assoc.
  forward.
  rewrite (prot4_shim_table2_result T old new sho Eo shn En L1 L2 HEo HEn HL HoL1).
  entailer!. apply modus_ponens_wand.
Qed.

End Bodies.
