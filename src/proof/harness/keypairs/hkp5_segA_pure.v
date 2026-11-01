(* law keypairs, prologue A, piece pure: the loop's entry facts
   (hkp5_fix_ok, hkp5_inv, hkp5_oth_ok) from the prologue's invariant hkp5A_inv.  Pure Coq.
   States: hkp5_segA_defs.v. *)
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
Require Import WgNoise.proof.harness.keypairs.hkp5_segA_defs.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

Lemma hkp5A_pu_sfind_in {A: Type} : forall (D: list (val * share * A)) a sh E,
  NoDup (saddrs D) -> In (a, sh, E) D -> sfind D a = Some (sh, E).
Proof.
  induction D as [|[[x sx] v] D IH]; intros a sh E ND HI; simpl in *; [contradiction|].
  inv ND. destruct HI as [HE|HI].
  - inv HE. destruct (EqDec_val a a); [reflexivity|congruence].
  - destruct (EqDec_val x a); [|auto].
    subst. exfalso. apply H1. clear -HI. induction D as [|[[y sy] w] D IH]; simpl in *; [contradiction|].
    destruct HI as [HE|HI]; [inv HE; auto|auto].
Qed.

Lemma hkp5A_pu_saddrs_filter : forall (D: list (val * share * entry)) b,
  saddrs (filter (fun d => negb (hk5_eqb (fst (fst d)) b)) D) =
  filter (fun a => negb (hk5_eqb a b)) (saddrs D).
Proof.
  induction D as [|[[x sx] v] D IH]; intros b; simpl; [reflexivity|].
  destruct (negb (hk5_eqb x b)); simpl; rewrite IH; reflexivity.
Qed.

Lemma hkp5A_pu_in_filter : forall (l: list val) b a,
  In a (filter (fun a => negb (hk5_eqb a b)) l) <-> In a l /\ a <> b.
Proof.
  intros. rewrite filter_In. unfold hk5_eqb. destruct (eq_dec a b); simpl; intuition congruence.
Qed.

Lemma hkp5A_pu_hn_p : forall T NS PS,
  length NS = length PS -> map hn_p (hnodes_snapped4 T NS PS) = map hn_p NS.
Proof.
  induction NS as [|N NS IH]; intros [|x PS] HL; simpl in *; try discriminate; auto.
  destruct x as [[q sh] Q]. simpl. f_equal. apply IH. lia.
Qed.

Lemma hkp5A_pu_snaps : forall T NS PS,
  length NS = length PS ->
  Forall2 (fun N x => match x with (q, _, Q) =>
     hn_snap N = hsnap_val (hs_snap_cur T q Q) /\ hn_refs N = Vint (p_refs Q) /\ hn_rest N = prsnap_val Q end)
     (hnodes_snapped4 T NS PS) PS.
Proof.
  induction NS as [|N NS IH]; intros [|x PS] HL; simpl in *; try discriminate; constructor.
  - destruct x as [[q sh] Q]. simpl. auto.
  - apply IH. lia.
Qed.

Lemma hkp5A_pu_ke_addr : forall T KE, map ke_addr (map (kent_snapped T) KE) = map ke_addr KE.
Proof. intros. rewrite map_map. reflexivity. Qed.

Lemma hkp5A_pure_ok : hkp5A_pure_stmt.
Proof.
  intros F R S w P NS PS KE T head HR Hw HT HI.
  destruct HR as (HR1 & HR2 & HR3 & HR4).
  unfold hkp5A_inv in HI; cbv zeta in HI.
  destruct HI as (Hp & Hdev & Hsid & Hcur & Hprev & Hnext & Hpk & HNP & Hwf & HND & Hpa & Hka & HPS & Hhead &
                  Hsad & Hfp & Hpe & Hke & Hidx & Hsh1 & Hsh2).
  pose proof HT as (HT1 & HT2 & HT3 & HT4).
  assert (HNDs: NoDup (map ke_addr KE ++ map hs_addr (map peer_addr4 PS) ++ [hs_addr (f_p F)]))
    by (rewrite <- Hsad; auto).
  assert (Hpin: ~ In (hs_addr (f_p F)) (map ke_addr KE ++ map hs_addr (map peer_addr4 PS))).
  { rewrite app_assoc in HNDs. apply NoDup_remove_2 in HNDs. rewrite app_nil_r in HNDs. auto. }
  assert (HOD: forall a, In a (saddrs (hkp5A_OD (f_p F) T)) <-> In a (saddrs (t_D T)) /\ a <> hs_addr (f_p F)).
  { intros. unfold hkp5A_OD. rewrite hkp5A_pu_saddrs_filter. apply hkp5A_pu_in_filter. }
  assert (HODf: Forall (fun x => match x with (a, sh, E) => sfind (t_D T) a = Some (sh, E) end)
                       (hkp5A_OD (f_p F) T)).
  { rewrite Forall_forall. intros [[a sh] E] Hin. unfold hkp5A_OD in Hin. apply filter_In in Hin.
    destruct Hin as [Hin _]. apply hkp5A_pu_sfind_in; auto. }
  assert (Hsp: In (hs_addr (f_p F)) (saddrs (t_D T))).
  { rewrite Hsad. apply in_or_app; right; apply in_or_app; right; left; auto. }
  split; [|split].
  - unfold hkp5_fix_ok; simpl; auto.
  - unfold hkp5_inv, hkp5A_V, hkp5A_Y; cbn [v_OD v_OH y_H y_P y_KS y_T v_w0 y_w y_S v_frees0 v_allocs0
      y_id_known y_now y_hsn v_prefs y_next_id y_kc].
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
    + unfold hk5_rel, hk5_core, hk5_pool, hkp5A_H0, hk5_slots; cbn [h5_ML h5_sp h5_sc h5_sn].
      split; [|split; [|split; [|split]]].
      * split; [constructor|]. split; [constructor|]. split; [simpl; tauto|].
        split; [constructor|]. split; [simpl; tauto|].
        split; [repeat constructor; left; reflexivity|]. split; [constructor|]. split; [constructor|].
        split; [|split; [|split; [|split; [|split; [|split]]]]].
        -- intros a. rewrite HOD. simpl. split.
           ++ intros Ha. destruct (EqDec_val a (hs_addr (f_p F))); [left; auto|right; right; auto].
           ++ intros [Ha|[[]|[Ha1 Ha2]]]; [subst; auto|auto].
        -- simpl; tauto.
        -- rewrite HOD. tauto.
        -- simpl; tauto.
        -- exists Int.zero. auto.
        -- revert HODf. apply Forall_impl. intros [[a sh] E] H. auto.
        -- auto.
      * unfold hk5_nonnull, hk5_eqb. simpl. destruct (eq_dec nullval nullval); [|congruence]. simpl. constructor.
      * rewrite Hprev. reflexivity.
      * rewrite Hcur. reflexivity.
      * rewrite Hnext. reflexivity.
    + unfold hk5_warn_ok, hkp5A_H0; cbn [h5_warn].
      split; [auto|]. split; [reflexivity|]. split; [auto|].
      split; [|split; [reflexivity|split; reflexivity]].
      intros i Hi. rewrite Znth_Zrepeat by lia. rewrite Int64.add_zero. reflexivity.
    + auto.
    + auto.
    + reflexivity.
    + rewrite Int64.sub_idem. reflexivity.
    + rewrite Int64.sub_idem. reflexivity.
    + discriminate.
    + lia.
    + unfold hk5_hsm_ok, hs_snap_cur, snap_of, t_entry_d, t_entry. rewrite Hfp. simpl. auto.
    + auto.
  - unfold hkp5_oth_ok, hkp5A_V, hkp5A_O; cbn [v_OD v_OH v_head o_PS o_KE o_T0 o_NS].
    rewrite hkp5A_pu_ke_addr.
    assert (HL: length NS = length PS).
    { unfold hnodes_peers4 in HNP. rewrite <- (map_length hn_p NS), <- (map_length peer_addr4 PS), HNP. auto. }
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]].
    + unfold hnodes_peers4. rewrite hkp5A_pu_hn_p by auto. auto.
    + auto.
    + auto.
    + apply hkp5A_pu_snaps; auto.
    + rewrite Forall_map. rewrite Forall_forall. intros [k K sn] _. reflexivity.
    + rewrite Hsad in HT3. apply NoDup_app_remove_r in HT3. auto.
    + intros a. rewrite HOD, Hsad. rewrite !in_app_iff. split.
      * intros [[Ha|[Ha|Ha]] Hn]; auto. destruct Ha as [Ha|[]]. congruence.
      * intros Ha. split; [tauto|]. intros ->. apply Hpin. apply in_app_iff. tauto.
    + unfold hkp5A_OD. rewrite hkp5A_pu_saddrs_filter. apply NoDup_filter. auto.
    + revert HODf. apply Forall_impl. intros [[a sh] E] H. auto.
    + rewrite Forall_map in Hpe. rewrite Forall_forall in Hpe, HPS |- *.
      intros [[q sh] Q] Hin. specialize (Hpe _ Hin). specialize (HPS _ Hin). simpl in Hpe, HPS.
      tauto.
    + rewrite Forall_map. auto.
    + split; [auto |]. split; [| split].
      * assert (H2: NoDup (map ke_addr KE ++ map hs_addr (map peer_addr4 PS))).
        { rewrite app_assoc in HNDs. apply NoDup_app_remove_r in HNDs. exact HNDs. }
        exact (Permutation_NoDup (Permutation_app_comm _ _) H2).
      * exact Hsh1.
      * rewrite Forall_forall. intros [[a sh] E] Hin. unfold hkp5A_OD in Hin. apply filter_In in Hin.
        destruct Hin as [Hin Hf]. rewrite Forall_forall in Hsh2. specialize (Hsh2 _ Hin). simpl in Hsh2, Hf.
        destruct Hsh2 as [Ha | Hs]; [| exact Hs].
        unfold hk5_eqb in Hf. destruct (eq_dec a (hs_addr (f_p F))); [discriminate | contradiction].
Qed.
