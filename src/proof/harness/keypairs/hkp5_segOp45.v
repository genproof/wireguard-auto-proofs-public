(* law keypairs: operations 4 and 5 of the loop body (hkp5_sOp45: keypair_get). *)
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

Lemma op45_map_fst_aupd (L: list (val * A)) a v : map fst (aupd L a v) = map fst L.
Proof.
  induction L as [|[x w] L IH]; simpl; [reflexivity|].
  destruct (EqDec_val x a); simpl; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma op45_Zlength_aupd (L: list (val * A)) a v : Zlength (aupd L a v) = Zlength L.
Proof.
  rewrite <- (Zlength_map _ _ fst), op45_map_fst_aupd, Zlength_map. reflexivity.
Qed.

Lemma op45_head_aupd (L: list (val * A)) a v : hk5_head (aupd L a v) = hk5_head L.
Proof. destruct L as [|[x w] L]; simpl; [reflexivity|]. destruct (EqDec_val x a); reflexivity. Qed.

Lemma op45_afind_aupd_eq (L: list (val * A)) a v w : afind L a = Some w -> afind (aupd L a v) a = Some v.
Proof.
  induction L as [|[x u] L IH]; simpl; intros Hf; [discriminate|].
  destruct (EqDec_val x a); simpl.
  - rewrite if_true by auto. reflexivity.
  - rewrite if_false by auto. auto.
Qed.

Lemma op45_afind_aupd_ne (L: list (val * A)) a v b : b <> a -> afind (aupd L a v) b = afind L b.
Proof.
  intros Hb. induction L as [|[x u] L IH]; simpl; [reflexivity|].
  destruct (EqDec_val x a); simpl.
  - subst x. rewrite !if_false by auto. reflexivity.
  - destruct (EqDec_val x b); auto.
Qed.

Lemma op45_aupd_id (L: list (val * A)) a v : afind L a = Some v -> aupd L a v = L.
Proof.
  induction L as [|[x u] L IH]; simpl; intros Hf; [reflexivity|].
  destruct (EqDec_val x a); [inv Hf; reflexivity|]. rewrite IH by auto. reflexivity.
Qed.

Lemma op45_aupd_aupd (L: list (val * A)) a v w : aupd (aupd L a v) a w = aupd L a w.
Proof.
  induction L as [|[x u] L IH]; simpl; [reflexivity|].
  destruct (EqDec_val x a); simpl.
  - rewrite if_true by auto. reflexivity.
  - rewrite if_false by auto. rewrite IH. reflexivity.
Qed.

Lemma op45_In_afind (L: list (val * A)) a : In a (map fst L) -> exists v, afind L a = Some v.
Proof.
  induction L as [|[x u] L IH]; simpl; intros Hi; [contradiction|].
  destruct (EqDec_val x a); [eauto|]. destruct Hi; [congruence|auto].
Qed.

Lemma op45_afind_In (L: list (val * A)) a v : afind L a = Some v -> In a (map fst L).
Proof.
  induction L as [|[x u] L IH]; simpl; intros Hf; [discriminate|].
  destruct (EqDec_val x a); [auto|right; auto].
Qed.

End AssocL.

Lemma op45_slot_kp_aupd ML m M M' x :
  afind ML m = Some M -> m5_kp M' = m5_kp M -> hk5_slot_kp (aupd ML m M') x = hk5_slot_kp ML x.
Proof.
  intros Hf Hk. unfold hk5_slot_kp. destruct (eq_dec x nullval); [reflexivity|].
  destruct (EqDec_val x m).
  - subst x. rewrite (op45_afind_aupd_eq _ _ _ _ Hf), Hf. auto.
  - rewrite op45_afind_aupd_ne by auto. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* The model: the state after get                                          *)
(* ---------------------------------------------------------------------- *)

Lemma op45_inv_get F V S w kc P KS T ML sp sc sn fr mw now nid idk hsn m M :
  hkp5_model_facts ->
  hkp5_inv F V (mkKY5 S w kc P KS T (mkH5 ML sp sc sn fr mw) now nid idk hsn) ->
  afind ML m = Some M ->
  fst (kp_get (m5_kp M) KS) = m5_kp M /\
  hkp5_inv F V (mkKY5 S (kp_get_warn (m5_kp M) KS w) kc P (snd (kp_get (m5_kp M) KS)) T
     (mkH5 (aupd ML m (hk5_mget M)) sp sc sn fr (hk5_get_warn (m5_refs M) mw)) now nid idk hsn).
Proof.
  intros (_ & _ & _ & _ & _ & Hget) Hinv Hf.
  destruct Hinv as (I1&I2&I3&I4&I5&I6&I7&I8&I9&I10).
  cbn [f_p y_H y_P y_KS y_T y_S y_w y_now y_kc y_next_id y_id_known y_hsn h5_ML h5_warn h5_frees] in *.
  destruct I1 as (Hc & Hnd & Hp & Hcu & Hn).
  cbn [hk5_slots h5_ML h5_sp h5_sc h5_sn] in Hc, Hnd, Hp, Hcu, Hn.
  destruct (Hget _ _ _ _ _ _ _ _ _ _ _ _ Hc I2 Hf) as (Hk & Hc' & Hw').
  assert (Hs: forall x, hk5_slot_kp (aupd ML m (hk5_mget M)) x = hk5_slot_kp ML x)
    by (intros; eapply op45_slot_kp_aupd; [exact Hf | reflexivity]).
  split; [exact Hk|].
  refine (conj _ (conj Hw' (conj I3 (conj I4 (conj I5 (conj I6 (conj _ (conj I8 (conj I9 I10))))))))).
  - unfold hk5_rel. cbn [hk5_slots h5_ML h5_sp h5_sc h5_sn]. rewrite !Hs.
    exact (conj Hc' (conj Hnd (conj Hp (conj Hcu Hn)))).
  - cbn [y_S y_H h5_ML h5_frees]. rewrite op45_Zlength_aupd. exact I7.
Qed.

Lemma op45_set_held_id M : m5_set_held M (m5_held M) = M.
Proof. destruct M; reflexivity. Qed.

Lemma op45_kp_get_null KS : kp_get nullval KS = (nullval, KS).
Proof. unfold kp_get. rewrite if_true by reflexivity. reflexivity. Qed.

Lemma op45_kp_get_warn_null KS w : kp_get_warn nullval KS w = w.
Proof. unfold kp_get_warn. rewrite if_true by reflexivity. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* Separation logic                                                        *)
(* ---------------------------------------------------------------------- *)

Section VSTside.
#[local] Existing Instance W_keypairs.

Lemma op45_focus ML m M :
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
    cbn [aupd]. rewrite if_false by auto. cbn [hk5_mklist]. rewrite op45_head_aupd.
    cancel. rewrite wand_sepcon_adjoint. apply (allp_left _ M'). apply derives_refl.
Qed.

Lemma op45_nclose ML m M nx h :
  Zlength (m5_send M) = 32 -> Zlength (m5_recv M) = 32 ->
  data_at Ews t_mk5
    (m5_kp M, (Vint (m5_refs M), (Vlong h, (Val.of_bool (m5_hashed M), (Vint (m5_index M),
     (bytes (m5_send M), (bytes (m5_recv M), (Val.of_bool (m5_sv M), (Val.of_bool (m5_rv M),
     (Val.of_bool (m5_init M), (Vint (m5_rindex M), (Vlong (m5_birth M), (Vlong (m5_id M),
     (Vlong (m5_scnt M), (Vlong (m5_rcnt M), nx))))))))))))))) m * malloc_token Ews t_mk5 m *
  (ALL M': hk5_mk, hk5_node m M' nx -* hk5_mklist (aupd ML m M'))
  |-- hk5_mklist (aupd ML m (m5_set_held M h)).
Proof.
  intros H1 H2.
  apply derives_trans with (hk5_node m (m5_set_held M h) nx *
    (ALL M': hk5_mk, hk5_node m M' nx -* hk5_mklist (aupd ML m M'))).
  - apply sepcon_derives; [| apply derives_refl].
    unfold hk5_node, hk5_mk_val. destruct M; cbn in *. entailer!.
  - rewrite sepcon_comm, wand_sepcon_adjoint. apply (allp_left _ (m5_set_held M h)). apply derives_refl.
Qed.

Lemma op45_mklist_ptr ML m : In m (map fst ML) -> hk5_mklist ML |-- !! isptr m.
Proof.
  induction ML as [|[x M] ML IH]; simpl; intros I; [contradiction|].
  destruct I as [<-|I].
  - unfold hk5_node. Intros. entailer!.
  - sep_apply (IH I). entailer!.
Qed.

(* a pool address is a valid pointer *)
Lemma op45_sfind_In {B: Type} (D: list (val * share * B)) a sh E :
  sfind D a = Some (sh, E) -> In (a, sh, E) D.
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros Hs; [discriminate|].
  destruct (EqDec_val x a); [inv Hs; auto|auto].
Qed.

Lemma op45_pool_split {B: Type} (D: list (val * share * B)) a sh E (f: val * share * B -> mpred) :
  sfind D a = Some (sh, E) -> VST.msl.iter_sepcon.iter_sepcon f D = (f (a, sh, E) * VST.msl.iter_sepcon.iter_sepcon f (sdel D a))%logic.
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros Hs; [discriminate|].
  destruct (EqDec_val x a); [inv Hs; reflexivity|].
  rewrite (IH Hs); simpl. rewrite <- !sepcon_assoc, (sepcon_comm (f _) (f _)). reflexivity.
Qed.

Lemma op45_pool_valid sht t T a sh E :
  sfind (t_D T) a = Some (sh, E) -> itable sht t T |-- valid_pointer a.
Proof.
  intros Hs.
  unfold itable. Intros. rename H into W.
  assert (Wsh: writable_share sh).
  { destruct W as (_ & _ & _ & HF). rewrite Forall_forall in HF. apply (HF (a, sh, E)).
    apply op45_sfind_In; auto. }
  rewrite (op45_pool_split _ _ _ _ _ Hs).
  apply sepcon_valid_pointer2. apply sepcon_valid_pointer1.
  unfold pool_item_rep, entry_at.
  apply data_at_valid_ptr; [apply readable_nonidentity, writable_readable; auto | reflexivity].
Qed.

Lemma op45_vp_pn v : valid_pointer v |-- !! is_pointer_or_null v.
Proof. constructor; apply valid_pointer_is_pointer_or_null. Qed.

Lemma op45_tc_kp sht t T a sh E (R: mpred) :
  sfind (t_D T) a = Some (sh, E) -> itable sht t T * R |-- denote_tc_test_eq a a.
Proof.
  intros Hs. apply denote_tc_test_eq_split; apply sepcon_valid_pointer1; eapply op45_pool_valid; eauto.
Qed.

End VSTside.

Lemma op45_cmp_self v : is_pointer_or_null v ->
  typed_true tint (match sem_unary_operation Onotbool tint (force_val (sem_cmp_pp Ceq v v)) with
                   | Some v' => v' | None => Vundef end) -> False.
Proof.
  intros Hp Ht. destruct v; try contradiction; simpl in Hp.
  - subst. vm_compute in Ht. discriminate.
  - unfold sem_cmp_pp in Ht. simpl in Ht. rewrite if_true in Ht by auto. rewrite Ptrofs.eq_true in Ht.
    vm_compute in Ht. discriminate.
Qed.

Ltac op45_false :=
  match goal with Hc: Int.repr (Z.b2z _) = Int.zero |- _ =>
    rewrite ?Int64.eq_true, ?Int.eq_true in Hc; exact (Int.one_not_zero Hc) end.

Lemma hkp5_segOp45_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps FR i op R :
  hkp5_model_facts -> x25519_props x25519 -> op = 4 \/ op = 5 ->
  semax (hkp5_Delta hkp5_G_Op45) (hkp5_PL0 x25519 F V steps FR i op) hkp5_sOp45
    (loop1_ret_assert (hkp5_Icont x25519 F V steps FR i) R).
Proof.
  intros HM HX Hop.
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
  unfold hkp5_sOp45.
  forward_call tt. Intros u.
  lazymatch goal with |- semax _ (PROPx ?P0 (LOCALx ?Q0 (SEPx ?R0))) _ _ =>
    forward_if (EX k: val, PROPx ((k = nullval \/ In k (map fst ML)) :: P0) (LOCALx (temp KC._t'52 k :: Q0) (SEPx R0))) end.
  { apply prop_right. intros [_ Hc]. apply (f_equal Int.unsigned) in Hc.
    rewrite Int.unsigned_repr in Hc by rep_lia. discriminate. }
  { forward. Exists nullval. entailer!. }
  { forward_call (gv, ML). Intros k. forward. Exists k. entailer!.
    match goal with Hk: (_ /\ k = nullval) \/ (_ /\ In k _) |- _ => destruct Hk as [[_ ->] | [_ Hk]]; auto end. }
  Intros k.
  forward.
  match goal with Hk: k = nullval \/ In k (map fst ML) |- _ => rename Hk into Hk1 end.
  pose proof HM as (Hpre & _).
  pose proof Hinv as (Hr0 & Hw0 & _).
  cbn [f_p y_H y_P y_KS y_T y_w h5_warn] in Hr0, Hw0.
  pose proof Hr0 as (Hc & _).
  cbn [hk5_slots h5_ML h5_sp h5_sc h5_sn] in Hc.
  pose proof Hc as (_ & Hnd & Hnn & _).
  destruct (Hpre _ _ _ _ _ _ _ Hc) as (Kp & _ & Hnode & _ & _).
  destruct (eq_dec k nullval) as [Hk0 | Hk0].
  { (* k = NULL: r = NULL, nothing changes *)
    subst k. clear Hk1.
    lazymatch goal with |- semax _ (PROPx ?P0 (LOCALx ?Q0 (SEPx ?R0))) _ _ =>
      forward_if (PROPx P0 (LOCALx (temp KC._t'54 nullval :: Q0) (SEPx R0))) end.
    { exfalso. auto. }
    { forward. entailer!. }
    forward_call (gv, S, ww, KS, nullval, Tsh, t, T, p).
    rewrite op45_kp_get_null, op45_kp_get_warn_null. cbn [fst snd].
    forward.
    forward_if.
    2: { exfalso. auto. }
    match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
    { apply ENTAIL_refl. }
    { forward_if.
      { forward_call tt. all: first [op45_false | entailer!]. }
      forward. entailer!. }
    { forward. apply ENTAIL_refl. }
    unfold hkp5_Icont, hkp5_St.
    Exists (mkKY5 S ww kc P KS T (mkH5 ML sp sc sn fr mw) now next_id id_known hsn).
    unfold hkp5_St, hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
    cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second y_S y_w y_kc y_P y_KS y_T y_H y_now
       y_next_id y_id_known y_hsn h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn].
    entailer!. }
  (* k: a live node *)
  assert (Hk: In k (map fst ML)) by (destruct Hk1; [contradiction | assumption]).
  clear Hk1.
  destruct (op45_In_afind _ _ Hk) as (M & Hf).
  destruct (Hnode _ _ Hf) as (K & HK & Hm).
  pose proof Hm as (_ & HsfM & _).
  assert (KinM: In (m5_kp M) (map fst KS)) by (eapply op45_afind_In; eauto).
  destruct (op45_inv_get _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k M HM Hinv Hf) as (Hget1 & Hinv').
  sep_apply (op45_focus ML k M Hf). Intros nx. unfold hk5_node at 1. Intros.
  unfold hk5_mk_val.
  assert_PROP (is_pointer_or_null (m5_kp M)) as PNkp.
  { sep_apply (op45_pool_valid Tsh t T (m5_kp M) Ews _ HsfM).
    sep_apply (op45_vp_pn (m5_kp M)). entailer!. }
  lazymatch goal with |- semax _ (PROPx ?P0 (LOCALx ?Q0 (SEPx ?R0))) _ _ =>
    forward_if (PROPx P0 (LOCALx (temp KC._t'54 (m5_kp M) :: Q0) (SEPx R0))) end.
  { forward. forward. entailer!. }
  { exfalso. subst k. apply Hnn. exact Hk. }
  forward_call (gv, S, ww, KS, m5_kp M, Tsh, t, T, p).
  rewrite Hget1.
  forward.
  forward_if.
  { exfalso. subst k. apply Hnn. exact Hk. }
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward. forward_if.
    { eapply derives_trans; [| apply (op45_tc_kp Tsh t T (m5_kp M) Ews _ TT HsfM)]. cancel. }
    { forward_call tt.
      all: first [match goal with Ht: typed_true _ _ |- False => exact (op45_cmp_self _ PNkp Ht) end
                 | entailer!]. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  sep_apply (op45_nclose ML k M nx (m5_held M) H5 H6).
  rewrite op45_set_held_id, (op45_aupd_id _ _ _ Hf).
  forward_call (gv, ML, k, M, mw).
  set (M1 := m5_set_refs M (hk5_get_refs (m5_refs M))).
  assert (Hf1: afind (aupd ML k M1) k = Some M1) by (eapply op45_afind_aupd_eq; eauto).
  sep_apply (op45_focus (aupd ML k M1) k M1 Hf1). Intros nx1. unfold hk5_node at 1. Intros.
  unfold hk5_mk_val.
  forward.
  forward.
  sep_apply (op45_nclose (aupd ML k M1) k M1 nx1 (Int64.add (m5_held M1) (Int64.repr 1))); [assumption..|].
  rewrite op45_aupd_aupd.
  replace (m5_set_held M1 (Int64.add (m5_held M1) (Int64.repr 1))) with (hk5_mget M) by reflexivity.
  unfold hkp5_Icont.
  Exists (mkKY5 S (kp_get_warn (m5_kp M) KS ww) kc P (snd (kp_get (m5_kp M) KS)) T
     (mkH5 (aupd ML k (hk5_mget M)) sp sc sn fr (hk5_get_warn (m5_refs M) mw)) now next_id id_known hsn).
  unfold hkp5_St, hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
  cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second y_S y_w y_kc y_P y_KS y_T y_H y_now
     y_next_id y_id_known y_hsn h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn].
  rewrite op45_head_aupd.
  entailer!.
Qed.
