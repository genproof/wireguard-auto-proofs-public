(* law keypairs: operation 7 of the loop body (hkp5_sOp7). *)
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
Require Import WgNoise.proof.harness.keypairs.hkp5_defs.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* Association lists                                                       *)
(* ---------------------------------------------------------------------- *)

Section AssocL.
Context {A: Type}.

Lemma op7_map_fst_aupd (L: list (val * A)) a v : map fst (aupd L a v) = map fst L.
Proof.
  induction L as [|[x w] L IH]; simpl; [reflexivity|].
  destruct (EqDec_val x a); simpl; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma op7_Zlength_aupd (L: list (val * A)) a v : Zlength (aupd L a v) = Zlength L.
Proof.
  rewrite <- (Zlength_map _ _ fst), op7_map_fst_aupd, Zlength_map. reflexivity.
Qed.

Lemma op7_head_aupd (L: list (val * A)) a v : hk5_head (aupd L a v) = hk5_head L.
Proof. destruct L as [|[x w] L]; simpl; [reflexivity|]. destruct (EqDec_val x a); reflexivity. Qed.

Lemma op7_afind_aupd_eq (L: list (val * A)) a v w : afind L a = Some w -> afind (aupd L a v) a = Some v.
Proof.
  induction L as [|[x u] L IH]; simpl; intros Hf; [discriminate|].
  destruct (EqDec_val x a); simpl.
  - rewrite if_true by auto. reflexivity.
  - rewrite if_false by auto. auto.
Qed.

Lemma op7_afind_aupd_ne (L: list (val * A)) a v b : b <> a -> afind (aupd L a v) b = afind L b.
Proof.
  intros Hb. induction L as [|[x u] L IH]; simpl; [reflexivity|].
  destruct (EqDec_val x a); simpl.
  - subst x. rewrite !if_false by auto. reflexivity.
  - destruct (EqDec_val x b); auto.
Qed.

Lemma op7_In_afind (L: list (val * A)) a : In a (map fst L) -> exists v, afind L a = Some v.
Proof.
  induction L as [|[x u] L IH]; simpl; intros Hi; [contradiction|].
  destruct (EqDec_val x a); [eauto|]. destruct Hi; [congruence|auto].
Qed.

Lemma op7_afind_In (L: list (val * A)) a v : afind L a = Some v -> In a (map fst L).
Proof.
  induction L as [|[x u] L IH]; simpl; intros Hf; [discriminate|].
  destruct (EqDec_val x a); [auto|right; auto].
Qed.

Lemma op7_afind_in (L: list (val * A)) a v : afind L a = Some v -> In (a, v) L.
Proof.
  induction L as [|[x u] L IH]; simpl; intros Hf; [discriminate|].
  destruct (EqDec_val x a); [inv Hf; auto|right; auto].
Qed.

Lemma op7_Forall_aupd (Q: val * A -> Prop) (L: list (val * A)) a v :
  Forall Q L -> (forall w, In (a, w) L -> Q (a, v)) -> Forall Q (aupd L a v).
Proof.
  induction L as [|[x u] L IH]; simpl; intros HF Hq; [constructor|].
  inv HF. destruct (EqDec_val x a).
  - subst x. constructor; [eauto | assumption].
  - constructor; [assumption | apply IH; eauto].
Qed.

End AssocL.

(* ---------------------------------------------------------------------- *)
(* The model of op 7: both counters set                                    *)
(* ---------------------------------------------------------------------- *)

Definition op7_kset (K: keypair) (sc rc: int64) : keypair :=
  mkKP (kp_send K) sc (kp_recv K) rc (kp_backtrack K) (kp_rindex K) (kp_init K) (kp_refs K) (kp_id K).

Lemma op7_slot_kp_aupd ML m M M' x :
  afind ML m = Some M -> m5_kp M' = m5_kp M -> hk5_slot_kp (aupd ML m M') x = hk5_slot_kp ML x.
Proof.
  intros Hf Hk. unfold hk5_slot_kp. destruct (eq_dec x nullval); [reflexivity|].
  destruct (EqDec_val x m).
  - subst x. rewrite (op7_afind_aupd_eq _ _ _ _ Hf), Hf. auto.
  - rewrite op7_afind_aupd_ne by auto. reflexivity.
Qed.

Lemma op7_F2_In (Rl: val * hk5_mk -> val * keypair -> Prop) ML KS m M :
  Forall2 Rl ML KS -> (forall x y, Rl x y -> fst y = m5_kp (snd x)) ->
  afind ML m = Some M -> In (m5_kp M) (map fst KS).
Proof.
  intros HF Hr. induction HF as [|[x X] [y Y] ML KS Hxy HF IH]; simpl; intros Hf; [discriminate|].
  destruct (EqDec_val x m).
  - inv Hf. left. apply (Hr _ _ Hxy).
  - right. auto.
Qed.

Lemma op7_F2_aupd (Rl: val * hk5_mk -> val * keypair -> Prop) ML KS m M M' K' :
  Forall2 Rl ML KS -> (forall x y, Rl x y -> fst y = m5_kp (snd x)) -> NoDup (map fst KS) ->
  afind ML m = Some M -> Rl (m, M') (m5_kp M, K') ->
  Forall2 Rl (aupd ML m M') (aupd KS (m5_kp M) K').
Proof.
  intros HF Hr. induction HF as [|[x X] [y Y] ML KS Hxy HF IH]; simpl; intros Hnd Hf HR; [discriminate|].
  pose proof (Hr _ _ Hxy) as Ey. cbn [fst snd] in Ey. subst y.
  inv Hnd. destruct (EqDec_val x m).
  - subst x. inv Hf. rewrite if_true by reflexivity. constructor; assumption.
  - rewrite if_false.
    + constructor; [assumption | auto].
    + intros E. apply H1. rewrite E. eapply op7_F2_In; eauto.
Qed.

Lemma op7_pool_KS p OD OH KS KS' T :
  map fst KS' = map fst KS -> hk5_pool p OD OH KS T -> hk5_pool p OD OH KS' T.
Proof. intros E. unfold hk5_pool. rewrite E. auto. Qed.

Lemma op7_core p OD OH R ML KS T m M K sc rc :
  hk5_core p OD OH R ML KS T -> afind ML m = Some M -> afind KS (m5_kp M) = Some K -> hk5_match p T M K ->
  hk5_core p OD OH R (aupd ML m (m5_set_cnts M sc rc)) (aupd KS (m5_kp M) (op7_kset K sc rc)) T.
Proof.
  intros (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9) Hf HK Hm.
  assert (Hin: In (m, M) ML) by (eapply op7_afind_in; eauto).
  assert (Hu: forall w, In (m, w) ML -> w = M).
  { intros w Hw. clear -C2 Hw Hin. induction ML as [|[x u] L IH]; [contradiction|].
    simpl in Hw, Hin, C2. inv C2. destruct Hw as [E|Hw]; destruct Hin as [E'|Hin].
    - inv E; inv E'; auto.
    - inv E. exfalso. apply H1. apply (in_map fst) in Hin. exact Hin.
    - inv E'. exfalso. apply H1. apply (in_map fst) in Hw. exact Hw.
    - auto. }
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  - eapply op7_F2_aupd; eauto.
    + intros x y [E _]. exact E.
    + cbn [fst snd]. split; [reflexivity|].
      destruct Hm as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
      destruct M, K; cbn in *. repeat split; auto.
  - rewrite op7_map_fst_aupd; exact C2.
  - rewrite op7_map_fst_aupd; exact C3.
  - rewrite op7_map_fst_aupd; exact C4.
  - rewrite op7_map_fst_aupd; exact C5.
  - eapply Forall_impl; [| exact C6]. intros a Ha. rewrite op7_map_fst_aupd. exact Ha.
  - apply op7_Forall_aupd; [exact C7|]. intros w Hw. apply Hu in Hw. subst w.
    rewrite Forall_forall in C7. specialize (C7 _ Hin). destruct M; exact C7.
  - apply op7_Forall_aupd; [exact C8|]. intros w Hw. apply Hu in Hw. subst w.
    rewrite Forall_forall in C8. specialize (C8 _ Hin). destruct M; exact C8.
  - eapply op7_pool_KS; [| exact C9]. apply op7_map_fst_aupd.
Qed.

Lemma op7_rel p OD OH H P KS T m M K sc rc :
  hk5_rel p OD OH H P KS T -> afind (h5_ML H) m = Some M -> afind KS (m5_kp M) = Some K ->
  hk5_match p T M K ->
  hk5_rel p OD OH (h5_set_ML H (aupd (h5_ML H) m (m5_set_cnts M sc rc))) P
    (aupd KS (m5_kp M) (op7_kset K sc rc)) T.
Proof.
  intros (Hc & Hnd & Hp & Hcu & Hn) Hf HK Hm.
  assert (Hs: forall x, hk5_slot_kp (aupd (h5_ML H) m (m5_set_cnts M sc rc)) x = hk5_slot_kp (h5_ML H) x)
    by (intros; eapply op7_slot_kp_aupd; [exact Hf | destruct M; reflexivity]).
  unfold hk5_rel. destruct H as [ML sp sc0 sn fr mw]. cbn [h5_set_ML h5_ML h5_sp h5_sc h5_sn hk5_slots] in *.
  rewrite !Hs. refine (conj _ (conj Hnd (conj Hp (conj Hcu Hn)))).
  eapply op7_core; eauto.
Qed.

(* ---------------------------------------------------------------------- *)
(* The live list focused at a node; the keypairs focused at one            *)
(* ---------------------------------------------------------------------- *)

Lemma op7_focus ML m M :
  afind ML m = Some M ->
  hk5_mklist ML |-- EX nx: val, hk5_node m M nx *
    (ALL M': hk5_mk, hk5_node m M' nx -* hk5_mklist (aupd ML m M')).
Proof.
  revert M. induction ML as [|[a A] L IH]; intros M Hf; cbn [afind] in Hf; [discriminate|].
  cbn [hk5_mklist].
  destruct (eq_dec a m) as [<-|Hne].
  - inv Hf. Exists (hk5_head L). cancel. apply allp_right. intros M'.
    rewrite <- wand_sepcon_adjoint. cbn [aupd]. rewrite if_true by auto. cbn [hk5_mklist]. cancel.
  - sep_apply (IH M Hf). Intros nx. Exists nx. cancel.
    apply allp_right. intros M'. rewrite <- wand_sepcon_adjoint.
    cbn [aupd]. rewrite if_false by auto. cbn [hk5_mklist]. rewrite op7_head_aupd.
    cancel. rewrite wand_sepcon_adjoint. apply (allp_left _ M'). apply derives_refl.
Qed.

Lemma op7_kfocus (KS: list (val * keypair)) k K :
  afind KS k = Some K ->
  keypairs_rep W_keypairs KS |-- keypair_rep W_keypairs k K *
    (ALL K': keypair, keypair_rep W_keypairs k K' -* keypairs_rep W_keypairs (aupd KS k K')).
Proof.
  revert K. induction KS as [|[a A] L IH]; intros K Hf; cbn [afind] in Hf; [discriminate|].
  unfold keypairs_rep in *. cbn [VST.msl.iter_sepcon.iter_sepcon keypair_item_rep].
  destruct (eq_dec a k) as [<-|Hne].
  - inv Hf. cancel. apply allp_right. intros K'.
    rewrite <- wand_sepcon_adjoint. cbn [aupd]. rewrite if_true by auto. cbn [VST.msl.iter_sepcon.iter_sepcon keypair_item_rep].
    cancel.
  - sep_apply (IH K Hf). cancel.
    apply allp_right. intros K'. rewrite <- wand_sepcon_adjoint.
    cbn [aupd]. rewrite if_false by auto. cbn [VST.msl.iter_sepcon.iter_sepcon keypair_item_rep].
    cancel. rewrite wand_sepcon_adjoint. apply (allp_left _ K'). apply derives_refl.
Qed.

(* ---------------------------------------------------------------------- *)
(* The keypair's two counters at the harness's compspecs                   *)
(* ---------------------------------------------------------------------- *)

#[local] Instance op7_CCE : change_composite_env Noise.CS W_keypairs.
Proof. make_cs_preserve Noise.CS W_keypairs. Defined.

Lemma op7_kpcs : cs_preserve_type Noise.CS W_keypairs (@coeq _ _ op7_CCE) t_kp = true.
Proof. vm_compute; reflexivity. Qed.

Lemma op7_cs_scnt sh v k :
  @field_at Noise.CS sh t_kp [StructField prot_repr3.I._sending_counter] v k =
  @field_at W_keypairs sh t_kp (DOT KC._sending_counter) v k.
Proof.
  exact (f_equal (fun f => f k) (@field_at_change_composite Noise.CS W_keypairs op7_CCE sh t_kp
           [StructField prot_repr3.I._sending_counter] v v (JMeq_refl _) op7_kpcs)).
Qed.

Lemma op7_cs_rcnt sh v k :
  @field_at Noise.CS sh t_kp [StructField prot_repr3.I._receiving_counter] v k =
  @field_at W_keypairs sh t_kp (DOT KC._receiving_counter) v k.
Proof.
  exact (f_equal (fun f => f k) (@field_at_change_composite Noise.CS W_keypairs op7_CCE sh t_kp
           [StructField prot_repr3.I._receiving_counter] v v (JMeq_refl _) op7_kpcs)).
Qed.

Lemma op7_kp_open k K :
  keypair_rep W_keypairs k K |--
  !! (isptr k /\ kp_ok K) && EX lk: val,
  (@field_at W_keypairs Ews t_kp (DOT KC._sending_counter) (Vlong (kp_scounter K)) k *
   @field_at W_keypairs Ews t_kp (DOT KC._receiving_counter) (Vlong (kp_rcounter K), (lk, map Vlong (kp_backtrack K))) k *
   (ALL sc: int64, ALL rc: int64,
      (@field_at W_keypairs Ews t_kp (DOT KC._sending_counter) (Vlong sc) k *
       @field_at W_keypairs Ews t_kp (DOT KC._receiving_counter) (Vlong rc, (lk, map Vlong (kp_backtrack K))) k)
      -* keypair_rep W_keypairs k (op7_kset K sc rc))).
Proof.
  unfold keypair_rep at 1. Intros r lk.
  rewrite op7_cs_scnt, op7_cs_rcnt.
  apply andp_right; [apply prop_right; split; [destruct H; auto with field_compatible | tauto]|].
  Exists lk. cancel.
  apply allp_right; intros sc. apply allp_right; intros rc. rewrite <- wand_sepcon_adjoint.
  unfold keypair_rep. Exists r. Exists lk. rewrite op7_cs_scnt, op7_cs_rcnt.
  destruct K; unfold op7_kset in *; cbn in H0 |- *. entailer!.
Qed.

Lemma op7_kclose k K lk sc rc :
  @field_at W_keypairs Ews t_kp (DOT KC._sending_counter) (Vlong sc) k *
  @field_at W_keypairs Ews t_kp (DOT KC._receiving_counter) (Vlong rc, (lk, map Vlong (kp_backtrack K))) k *
  (ALL sc0: int64, ALL rc0: int64,
      (@field_at W_keypairs Ews t_kp (DOT KC._sending_counter) (Vlong sc0) k *
       @field_at W_keypairs Ews t_kp (DOT KC._receiving_counter) (Vlong rc0, (lk, map Vlong (kp_backtrack K))) k)
      -* keypair_rep W_keypairs k (op7_kset K sc0 rc0))
  |-- keypair_rep W_keypairs k (op7_kset K sc rc).
Proof.
  rewrite sepcon_comm. rewrite wand_sepcon_adjoint.
  apply (allp_left _ sc). apply (allp_left _ rc). apply derives_refl.
Qed.

Lemma op7_ksclose KS k K' :
  keypair_rep W_keypairs k K' *
  (ALL K'': keypair, keypair_rep W_keypairs k K'' -* keypairs_rep W_keypairs (aupd KS k K''))
  |-- keypairs_rep W_keypairs (aupd KS k K').
Proof.
  rewrite sepcon_comm. rewrite wand_sepcon_adjoint. apply (allp_left _ K'). apply derives_refl.
Qed.

Lemma op7_nclose ML m M nx sc rc :
  Zlength (m5_send M) = 32 -> Zlength (m5_recv M) = 32 ->
  data_at Ews t_mk5
    (m5_kp M, (Vint (m5_refs M), (Vlong (m5_held M), (Val.of_bool (m5_hashed M), (Vint (m5_index M),
     (bytes (m5_send M), (bytes (m5_recv M), (Val.of_bool (m5_sv M), (Val.of_bool (m5_rv M),
     (Val.of_bool (m5_init M), (Vint (m5_rindex M), (Vlong (m5_birth M), (Vlong (m5_id M),
     (Vlong sc, (Vlong rc, nx))))))))))))))) m * malloc_token Ews t_mk5 m *
  (ALL M': hk5_mk, hk5_node m M' nx -* hk5_mklist (aupd ML m M'))
  |-- hk5_mklist (aupd ML m (m5_set_cnts M sc rc)).
Proof.
  intros H1 H2.
  apply derives_trans with (hk5_node m (m5_set_cnts M sc rc) nx *
    (ALL M': hk5_mk, hk5_node m M' nx -* hk5_mklist (aupd ML m M'))).
  - apply sepcon_derives; [| apply derives_refl].
    unfold hk5_node, hk5_mk_val. destruct M; cbn in *. entailer!.
  - rewrite sepcon_comm, wand_sepcon_adjoint. apply (allp_left _ (m5_set_cnts M sc rc)). apply derives_refl.
Qed.

Lemma hkp5_segOp7_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps FR i R :
  hkp5_model_facts -> x25519_props x25519 ->
  semax (hkp5_Delta hkp5_G_Op7) (hkp5_PL0 x25519 F V steps FR i 7) hkp5_sOp7
    (loop1_ret_assert (hkp5_Icont x25519 F V steps FR i) R).
Proof.
  intros HM HX.
  unfold hkp5_PL0, hkp5_Delta.
  Intros Y.
  destruct F as [gv w t pt p raw pub snap opub first second].
  destruct Y as [S ww kc P KS T HH now next_id id_known hsn].
  destruct HH as [ML sp sc sn fr mw].
  rename H1 into Hinv.
  unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
  cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second y_S y_w y_kc y_P y_KS y_T y_H y_now
       y_next_id y_id_known y_hsn h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn] in Hinv |- *.
  destruct R as [Rn Rb Rc Rr]. unfold loop1_ret_assert.
  abbreviate_semax.
  unfold hkp5_sOp7.
  forward_call (gv, ML). Intros k.
  destruct H1 as [[_ ->] | [_ Hk]].
  { forward_if.
    { forward. unfold hkp5_Icont, hkp5_St.
      Exists (mkKY5 S ww kc P KS T (mkH5 ML sp sc sn fr mw) now next_id id_known hsn).
      unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
      cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second y_S y_w y_kc y_P y_KS y_T y_H y_now
         y_next_id y_id_known y_hsn h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn].
      entailer!. }
    { exfalso. auto. } }
  destruct (op7_In_afind _ _ Hk) as (M & Hf).
  pose proof HM as (Hpre & _).
  pose proof Hinv as (Hr0 & _).
  cbn [f_p y_H y_P y_KS y_T] in Hr0.
  pose proof Hr0 as (Hc & _).
  cbn [hk5_slots h5_ML h5_sp h5_sc h5_sn] in Hc.
  pose proof Hc as (_ & _ & Hnn & _).
  destruct (Hpre _ _ _ _ _ _ _ Hc) as (_ & _ & Hnode & _ & _).
  destruct (Hnode _ _ Hf) as (K & HK & Hm).
  sep_apply (op7_focus ML k M Hf). Intros nx. unfold hk5_node at 1. Intros.
  sep_apply (op7_kfocus KS (m5_kp M) K HK). sep_apply (op7_kp_open (m5_kp M) K). Intros lk.
  unfold hk5_mk_val.
  forward_if.
  { exfalso. apply Hnn. subst k. exact Hk. }
  forward_call tt. Intros v1. forward. forward.
  forward_call tt. Intros v2. forward. forward.
  forward. forward. forward. forward. forward. forward.
  gather_SEP 0 1 2.
  replace_SEP 0 (keypair_rep W_keypairs (m5_kp M) (op7_kset K v1 v2)).
  { go_lowerx. rewrite sepcon_emp, <- sepcon_assoc. apply op7_kclose. }
  sep_apply (op7_ksclose KS (m5_kp M) (op7_kset K v1 v2)).
  sep_apply (op7_nclose ML k M nx v1 v2 H1 H5).
  set (KS' := aupd KS (m5_kp M) (op7_kset K v1 v2)).
  set (ML' := aupd ML k (m5_set_cnts M v1 v2)).
  assert (Hinv': hkp5_inv {| f_gv := gv; f_w := w; f_t := t; f_pt := pt; f_p := p; f_raw := raw; f_pub := pub;
    f_snap := snap; f_opub := opub; f_first := first; f_second := second |} V
    (mkKY5 S ww kc P KS' T (mkH5 ML' sp sc sn fr mw) now next_id id_known hsn)).
  { destruct Hinv as (I1&I2&I3&I4&I5&I6&I7&I8&I9&I10).
    cbn [f_p y_H y_P y_KS y_T y_S y_w y_now y_kc y_next_id y_id_known y_hsn h5_ML h5_warn h5_frees] in *.
    refine (conj _ (conj I2 (conj I3 (conj I4 (conj I5 (conj I6 (conj _ (conj I8 (conj I9 I10))))))))).
    - exact (op7_rel _ _ _ _ _ _ _ k M K v1 v2 I1 Hf HK Hm).
    - cbn [y_S y_H h5_ML h5_frees]. unfold ML'. rewrite op7_Zlength_aupd. exact I7. }
  unfold hkp5_Icont, hkp5_St.
  Exists (mkKY5 S ww kc P KS' T (mkH5 ML' sp sc sn fr mw) now next_id id_known hsn).
  unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
  cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second y_S y_w y_kc y_P y_KS y_T y_H y_now
     y_next_id y_id_known y_hsn h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn].
  replace (hk5_head ML') with (hk5_head ML) by (unfold ML'; symmetry; apply op7_head_aupd).
  entailer!.
Qed.
