(* law keypairs: operation 1, part b (hkp5_op1_b of hkp5_op1.v: received_with_keypair
   of NULL or of a live keypair of P). *)
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
Require Import WgNoise.proof.harness.keypairs.hkp5_op1.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* Association lists, counts                                               *)
(* ---------------------------------------------------------------------- *)

Lemma hk5o1_cnt_cons x R m : hk5_cnt (x :: R) m = (if eq_dec m x then 1 else 0) + hk5_cnt R m.
Proof. unfold hk5_cnt, hk5_eqb. simpl. destruct (EqDec_val m x); rewrite ?Zlength_cons; lia. Qed.

Lemma hk5o1_cnt_app l1 l2 m : hk5_cnt (l1 ++ l2) m = hk5_cnt l1 m + hk5_cnt l2 m.
Proof. unfold hk5_cnt. rewrite filter_app, Zlength_app. reflexivity. Qed.

Lemma hk5o1_cnt_nonneg R m : 0 <= hk5_cnt R m.
Proof. apply Zlength_nonneg. Qed.

Lemma hk5o1_cnt_remove1 s R m : In s R ->
  hk5_cnt R m = hk5_cnt (hk5_remove1 s R) m + (if eq_dec m s then 1 else 0).
Proof.
  induction R as [|x R IH]; simpl; intros I; [contradiction|].
  rewrite !hk5o1_cnt_cons. unfold eq_dec in *.
  destruct (EqDec_val x s) as [E|N].
  - subst x. lia.
  - destruct I as [E|I]; [congruence|]. rewrite hk5o1_cnt_cons, (IH I). unfold eq_dec in *. lia.
Qed.

Lemma hk5o1_cnt_In R m : 0 < hk5_cnt R m <-> In m R.
Proof.
  induction R as [|x R IH]; [unfold hk5_cnt; simpl; rewrite Zlength_nil; split; [lia | contradiction] |].
  rewrite hk5o1_cnt_cons. simpl. pose proof (hk5o1_cnt_nonneg R m). unfold eq_dec in *.
  destruct (EqDec_val m x) as [E|N]; split; intros Hm.
  - left; congruence.
  - lia.
  - right; apply IH; lia.
  - destruct Hm as [E|I]; [congruence | apply IH in I; lia].
Qed.

Lemma hk5o1_afind_in {A: Type} (l: list (val * A)) k K : afind l k = Some K -> In k (map fst l).
Proof.
  induction l as [|[x v] l IH]; simpl; [discriminate|]. unfold eq_dec in *.
  destruct (EqDec_val x k) as [<-|N]; auto.
Qed.

Lemma hk5o1_In_afind {A: Type} (L: list (val * A)) a : In a (map fst L) -> exists v, afind L a = Some v.
Proof.
  induction L as [|[x u] L IH]; simpl; intros Hi; [contradiction|].
  destruct (EqDec_val x a); [eauto|]. destruct Hi; [congruence|auto].
Qed.

Lemma hk5o1_afind_adel {A: Type} (l: list (val * A)) s m : m <> s -> afind (adel l s) m = afind l m.
Proof.
  intros N. induction l as [|[x w] l IH]; simpl; [reflexivity|]. unfold eq_dec in *.
  destruct (EqDec_val x s) as [<-|Nx]; simpl.
  - destruct (EqDec_val x m); [congruence | reflexivity].
  - destruct (EqDec_val x m); [reflexivity | exact IH].
Qed.

Lemma hk5o1_afind_aupd {A: Type} (l: list (val * A)) s v m : m <> s -> afind (aupd l s v) m = afind l m.
Proof.
  intros N. induction l as [|[x w] l IH]; simpl; [reflexivity|]. unfold eq_dec in *.
  destruct (EqDec_val x s) as [<-|Nx]; simpl.
  - destruct (EqDec_val x m); [congruence | reflexivity].
  - destruct (EqDec_val x m); [reflexivity | exact IH].
Qed.

Lemma hk5o1_aupd_id {A: Type} (L: list (val * A)) a v : afind L a = Some v -> aupd L a v = L.
Proof.
  induction L as [|[x u] L IH]; simpl; intros Hf; [reflexivity|].
  destruct (EqDec_val x a); [inv Hf; reflexivity|]. rewrite IH by auto. reflexivity.
Qed.

Lemma hk5o1_slot_put s u ML fr mw m : (m = nullval \/ m <> s) ->
  hk5_slot_kp (fst (fst (hk5_put s u ML fr mw))) m = hk5_slot_kp ML m.
Proof.
  intros Hm. unfold hk5_slot_kp. destruct (eq_dec m nullval); [reflexivity|].
  destruct Hm as [|Hm]; [contradiction|].
  unfold hk5_put. destruct (eq_dec s nullval); [reflexivity|]. destruct (afind ML s) as [M|]; [|reflexivity].
  cbv zeta. destruct (Int.eq (m5_refs M) REFCOUNT_SATURATED).
  - destruct u; cbn [fst]; [rewrite hk5o1_afind_aupd by auto|]; reflexivity.
  - destruct (Int.eq _ _); cbn [fst]; [rewrite hk5o1_afind_adel | rewrite hk5o1_afind_aupd]; auto.
Qed.

Lemma hk5o1_vin_vremove a k L : a <> k -> vin a (vremove k L) = vin a L.
Proof.
  intros N. unfold vin.
  assert (E: In a (vremove k L) <-> In a L).
  { induction L as [|x L IH]; simpl; [tauto|]. unfold eq_dec in *.
    destruct (EqDec_val x k) as [<-|Nx]; simpl; rewrite IH; split; intros H; auto;
      destruct H as [<-|H]; auto; congruence. }
  destruct (in_dec eq_dec a (vremove k L)), (in_dec eq_dec a L); tauto.
Qed.

Lemma hk5o1_sfind_sdel {A: Type} (D: list (val * share * A)) a k : a <> k -> sfind (sdel D k) a = sfind D a.
Proof.
  intros N. induction D as [|[[x sh] e] D IH]; simpl; [reflexivity|]. unfold eq_dec in *.
  destruct (EqDec_val x k) as [<-|Nx]; simpl.
  - destruct (EqDec_val x a); [congruence | reflexivity].
  - destruct (EqDec_val x a); [reflexivity | exact IH].
Qed.

(* a put of one of P's keypairs keeps the handshake entry and its membership *)
Lemma hk5o1_put_hs a k u KS T S : ~ In a (map fst KS) ->
  t_entry (kw_T (kp_put k u (mkKW KS T S))) a = t_entry T a /\
  vin a (t_L (kw_T (kp_put k u (mkKW KS T S)))) = vin a (t_L T).
Proof.
  intros NI. unfold kp_put. cbn [kw_KS kw_T kw_S].
  destruct (eq_dec k nullval); [auto|]. destruct (afind KS k) as [K|] eqn:EK; [|auto].
  assert (Nk: a <> k) by (intros ->; apply NI; eapply hk5o1_afind_in; eauto).
  assert (E1: t_entry (if u then t_remove T k else T) a = t_entry T a /\
              vin a (t_L (if u then t_remove T k else T)) = vin a (t_L T)).
  { destruct u; [|auto]. unfold t_remove, t_entry. cbn [t_D t_L]. split; [reflexivity|].
    apply hk5o1_vin_vremove; auto. }
  destruct (Int.eq _ _); cbn [kw_T]; [|exact E1].
  destruct E1 as [E1 E2]. unfold t_free, t_entry in *. cbn [t_D t_L] in *.
  rewrite hk5o1_sfind_sdel by auto. rewrite hk5o1_vin_vremove by auto. auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* The model: the slots rotate (k = s_next)                                *)
(* ---------------------------------------------------------------------- *)

(* one slot reference s (possibly NULL) of the reference list l1 ++ s :: l2 goes *)
Lemma hk5o1_step (FP: hk5_fact_put) (FPm: hk5_fact_perm) p OD OH l1 s l2 ML KS T S fr mw w0 w ML' fr' mw' :
  hk5_core p OD OH (l1 ++ s :: l2) ML KS T -> hk5_warn_ok w0 mw w ->
  hk5_put s true ML fr mw = (ML', fr', mw') ->
  hk5_core p OD OH (l1 ++ nullval :: l2) ML' (kw_KS (kp_put (hk5_slot_kp ML s) true (mkKW KS T S)))
    (kw_T (kp_put (hk5_slot_kp ML s) true (mkKW KS T S))) /\
  hk5_warn_ok w0 mw' (kp_put_warn (hk5_slot_kp ML s) KS w) /\
  ((kw_S (kp_put (hk5_slot_kp ML s) true (mkKW KS T S)) = S /\ fr' = fr /\ Zlength ML' = Zlength ML) \/
   (kw_S (kp_put (hk5_slot_kp ML s) true (mkKW KS T S)) = shim_free S /\
    fr' = Int64.add fr Int64.one /\ Zlength ML' = Zlength ML - 1)).
Proof.
  intros C Wk E.
  destruct (eq_dec s nullval) as [Es|Ns].
  - subst s. unfold hk5_put in E. rewrite if_true in E by reflexivity. inv E.
    unfold hk5_slot_kp, kp_put, kp_put_warn. rewrite !if_true by reflexivity.
    cbn [kw_KS kw_T kw_S]. split; [exact C|]. split; [exact Wk|]. left; auto.
  - assert (Is: In s (l1 ++ s :: l2)) by (apply in_or_app; right; left; reflexivity).
    pose proof (FP p OD OH _ ML KS T S fr mw w0 w s C Wk Is Ns) as FPs.
    rewrite E in FPs. destruct FPs as (C' & Wk' & D).
    split; [| split; [exact Wk' | destruct D as [D|(D1&D2&D3&_)]; [left; exact D | right; auto]]].
    assert (Ecnt: forall m, m <> nullval ->
      hk5_cnt (hk5_remove1 s (l1 ++ s :: l2)) m = hk5_cnt (l1 ++ nullval :: l2) m).
    { intros m Nm. pose proof (hk5o1_cnt_remove1 s _ m Is) as Em.
      rewrite hk5o1_cnt_app, hk5o1_cnt_cons in Em. rewrite hk5o1_cnt_app, hk5o1_cnt_cons.
      unfold eq_dec in *. destruct (EqDec_val m nullval); [contradiction|]. destruct (EqDec_val m s); lia. }
    apply (FPm _ _ _ _ _ _ _ _ Ecnt); [| exact C'].
    pose proof C' as (_&_&_&_&_&CF&_). rewrite Forall_forall in CF |- *. intros x Ix.
    destruct (eq_dec x nullval) as [|Nx]; [left; auto|]. apply CF.
    apply hk5o1_cnt_In. rewrite Ecnt by auto. apply hk5o1_cnt_In. auto.
Qed.

Lemma hk5o1_nonnull3 a b c : NoDup (hk5_nonnull [a; b; c]) ->
  (b = nullval \/ b <> a) /\ (c = nullval \/ c <> a) /\ NoDup (hk5_nonnull [b; c; nullval]).
Proof.
  unfold hk5_nonnull, hk5_eqb. simpl. unfold eq_dec in *.
  destruct (EqDec_val a nullval), (EqDec_val b nullval), (EqDec_val c nullval); simpl; intros ND;
    repeat split; auto; inv ND; try (inv H2); simpl in *; try (constructor; auto; constructor); intuition congruence.
Qed.

Lemma hk5o1_acc S fr n S' fr' n' f0 a0 :
  Int64.sub (s_frees S) f0 = fr -> Int64.sub (s_allocs S) a0 = Int64.add fr (Int64.repr n) ->
  ((S' = S /\ fr' = fr /\ n' = n) \/ (S' = shim_free S /\ fr' = Int64.add fr Int64.one /\ n' = n - 1)) ->
  Int64.sub (s_frees S') f0 = fr' /\ Int64.sub (s_allocs S') a0 = Int64.add fr' (Int64.repr n').
Proof.
  intros E1 E2 [(->&->&->)|(->&->&->)]; [auto|]. cbn [s_frees s_allocs shim_free]. split.
  - rewrite Int64.sub_add_l, E1. reflexivity.
  - rewrite E2, Int64.add_assoc. f_equal. unfold Int64.one. rewrite add64_repr. f_equal. lia.
Qed.

(* the invariant after the rotation: harness s_prev = s_cur, m_put(old s_prev, 1), s_cur = s_next, s_next = NULL;
   the kernel: prev put, cur -> prev, next -> cur, next = NULL *)
Lemma hk5o1_inv_rot (MF: hkp5_model_facts) F V S w kc P KS T ML sp sc sn fr mw now nid idk hsn ML' fr' mw' :
  hkp5_inv F V (mkKY5 S w kc P KS T (mkH5 ML sp sc sn fr mw) now nid idk hsn) ->
  hk5_put sp true ML fr mw = (ML', fr', mw') ->
  hkp5_inv F V (mkKY5 (kw_S (kp_put (p_prev P) true (mkKW KS T S))) (kp_put_warn (p_prev P) KS w) kc
     (p_set_slots P (p_next P) (p_cur P) nullval)
     (kw_KS (kp_put (p_prev P) true (mkKW KS T S))) (kw_T (kp_put (p_prev P) true (mkKW KS T S)))
     (mkH5 ML' sc sn nullval fr' mw') now nid idk hsn).
Proof.
  intros Hinv E.
  destruct MF as (FPre & FS & FPm & FP & _).
  destruct Hinv as (I1&I2&I3&I4&I5&I6&I7&I8&I9&I10).
  cbn [f_p y_H y_P y_KS y_T y_S y_w y_now y_kc y_next_id y_id_known y_hsn h5_ML h5_warn h5_frees] in *.
  destruct I1 as (C0 & ND & Ep & Ec & En).
  unfold hk5_slots in C0, ND. cbn [h5_sp h5_sc h5_sn h5_ML] in C0, ND, Ep, Ec, En.
  pose proof (hk5o1_nonnull3 _ _ _ ND) as (D1&D2&ND').
  change [sp; sc; sn] with ([] ++ sp :: [sc; sn]) in C0.
  pose proof (hk5o1_step FP FPm _ _ _ [] sp [sc; sn] ML KS T S fr mw _ w ML' fr' mw' C0 I2 E) as (C1&W1&A1).
  pose proof (hk5o1_slot_put sp true ML fr mw sc D1) as Sc1.
  pose proof (hk5o1_slot_put sp true ML fr mw sn D2) as Sn1.
  rewrite E in Sc1, Sn1. cbn [fst snd] in Sc1, Sn1.
  assert (Hhs: ~ In (hs_addr (f_p F)) (map fst KS)) by (destruct C0 as (_&_&_&_&_&_&_&_&(_&N&_)); exact N).
  pose proof (hk5o1_put_hs (hs_addr (f_p F)) (p_prev P) true KS T S Hhs) as (H1a & H1b).
  rewrite <- Ep in C1, W1, A1.
  assert (C2: hk5_core (f_p F) (v_OD V) (v_OH V) [sc; sn; nullval] ML'
                (kw_KS (kp_put (p_prev P) true (mkKW KS T S))) (kw_T (kp_put (p_prev P) true (mkKW KS T S)))).
  { apply (FPm _ _ _ ([] ++ nullval :: [sc; sn])); [| | exact C1].
    - intros m Nm. rewrite !hk5o1_cnt_cons. cbn [app]. rewrite !hk5o1_cnt_cons.
      unfold hk5_cnt. cbn [filter]. destruct (eq_dec m nullval); [contradiction|]. lia.
    - pose proof C1 as (_&_&_&_&_&CF&_). rewrite Forall_forall in CF |- *. intros x Ix. apply CF.
      cbn [app In] in Ix |- *. tauto. }
  unfold hkp5_inv. cbn [f_p y_H y_P y_KS y_T y_S y_w y_now y_kc y_next_id y_id_known y_hsn h5_ML h5_warn h5_frees].
  destruct (hk5o1_acc _ _ _ _ _ _ _ _ I6 I7 A1) as [G1 G2].
  destruct I10 as (I10 & I11).
  refine (conj _ (conj W1 (conj I3 (conj I4 (conj I5 (conj G1 (conj G2 (conj I8 (conj I9 (conj _ I11)))))))))).
  - unfold hk5_rel. cbn [hk5_slots h5_sp h5_sc h5_sn h5_ML p_prev p_cur p_next p_set_slots].
    refine (conj C2 (conj ND' (conj _ (conj _ _)))).
    + rewrite Sc1. exact Ec.
    + rewrite Sn1. exact En.
    + unfold hk5_slot_kp. rewrite if_true by reflexivity. reflexivity.
  - destruct I10 as (J1 & J2 & J3). unfold hk5_hsm_ok.
    rewrite H1a, H1b. exact (conj J1 (conj J2 J3)).
Qed.

(* ---------------------------------------------------------------------- *)
(* Separation logic                                                        *)
(* ---------------------------------------------------------------------- *)

Section VSTside.
#[local] Existing Instance W_keypairs.

Lemma hk5o1_head_aupd {A: Type} (L: list (val * A)) a v : hk5_head (aupd L a v) = hk5_head L.
Proof. destruct L as [|[x w] L]; simpl; [reflexivity|]. destruct (EqDec_val x a); reflexivity. Qed.

Lemma hk5o1_focus ML m M :
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
    cbn [aupd]. rewrite if_false by auto. cbn [hk5_mklist]. rewrite hk5o1_head_aupd.
    cancel. rewrite wand_sepcon_adjoint. apply (allp_left _ M'). apply derives_refl.
Qed.

Lemma hk5o1_nclose ML m M nx :
  afind ML m = Some M -> Zlength (m5_send M) = 32 -> Zlength (m5_recv M) = 32 ->
  data_at Ews t_mk5
    (m5_kp M, (Vint (m5_refs M), (Vlong (m5_held M), (Val.of_bool (m5_hashed M), (Vint (m5_index M),
     (bytes (m5_send M), (bytes (m5_recv M), (Val.of_bool (m5_sv M), (Val.of_bool (m5_rv M),
     (Val.of_bool (m5_init M), (Vint (m5_rindex M), (Vlong (m5_birth M), (Vlong (m5_id M),
     (Vlong (m5_scnt M), (Vlong (m5_rcnt M), nx))))))))))))))) m * malloc_token Ews t_mk5 m *
  (ALL M': hk5_mk, hk5_node m M' nx -* hk5_mklist (aupd ML m M'))
  |-- hk5_mklist ML.
Proof.
  intros Hf H1 H2.
  apply derives_trans with (hk5_node m M nx *
    (ALL M': hk5_mk, hk5_node m M' nx -* hk5_mklist (aupd ML m M'))).
  - apply sepcon_derives; [| apply derives_refl]. unfold hk5_node, hk5_mk_val. entailer!.
  - rewrite sepcon_comm, wand_sepcon_adjoint. apply (allp_left _ M). rewrite (hk5o1_aupd_id _ _ _ Hf).
    apply derives_refl.
Qed.

(* a pool address is a valid pointer *)
Lemma hk5o1_sfind_In {B: Type} (D: list (val * share * B)) a sh E :
  sfind D a = Some (sh, E) -> In (a, sh, E) D.
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros Hs; [discriminate|].
  destruct (EqDec_val x a); [inv Hs; auto|auto].
Qed.

Lemma hk5o1_pool_split {B: Type} (D: list (val * share * B)) a sh E (f: val * share * B -> mpred) :
  sfind D a = Some (sh, E) ->
  VST.msl.iter_sepcon.iter_sepcon f D = (f (a, sh, E) * VST.msl.iter_sepcon.iter_sepcon f (sdel D a))%logic.
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros Hs; [discriminate|].
  destruct (EqDec_val x a); [inv Hs; reflexivity|].
  rewrite (IH Hs); simpl. rewrite <- !sepcon_assoc, (sepcon_comm (f _) (f _)). reflexivity.
Qed.

Lemma hk5o1_pool_valid sht t T a sh E :
  sfind (t_D T) a = Some (sh, E) -> itable sht t T |-- valid_pointer a.
Proof.
  intros Hs.
  unfold itable. Intros. rename H into W.
  assert (Wsh: writable_share sh).
  { destruct W as (_ & _ & _ & HF). rewrite Forall_forall in HF. apply (HF (a, sh, E)).
    apply hk5o1_sfind_In; auto. }
  rewrite (hk5o1_pool_split _ _ _ _ _ Hs).
  apply sepcon_valid_pointer2. apply sepcon_valid_pointer1.
  unfold pool_item_rep, entry_at.
  apply data_at_valid_ptr; [apply readable_nonidentity, writable_readable; auto | reflexivity].
Qed.

Lemma hk5o1_vp_pn v : valid_pointer v |-- !! is_pointer_or_null v.
Proof. constructor; apply valid_pointer_is_pointer_or_null. Qed.

Lemma hk5o1_mklist_vp ML m : In m (map fst ML) -> hk5_mklist ML |-- valid_pointer m.
Proof.
  induction ML as [|[x M] ML IH]; simpl; intros I; [contradiction|].
  destruct I as [<-|I].
  - unfold hk5_node. rewrite sepcon_andp_prop'. apply andp_left2.
    apply sepcon_valid_pointer1, sepcon_valid_pointer1.
    apply data_at_valid_ptr; [apply readable_nonidentity, writable_readable, writable_Ews | reflexivity].
  - apply sepcon_valid_pointer2, IH, I.
Qed.

Lemma hk5o1_vp ML m (R: mpred) : m = nullval \/ In m (map fst ML) -> hk5_mklist ML * R |-- valid_pointer m.
Proof.
  intros [->|I]; [apply valid_pointer_null|]. apply sepcon_valid_pointer1, hk5o1_mklist_vp, I.
Qed.

Lemma hk5o1_ptr_or_null ML m : m = nullval \/ In m (map fst ML) -> hk5_mklist ML |-- !! is_pointer_or_null m.
Proof.
  intros Hm. eapply derives_trans; [rewrite <- (sepcon_emp (hk5_mklist ML)); apply (hk5o1_vp ML m emp Hm) |].
  constructor; apply valid_pointer_is_pointer_or_null.
Qed.

End VSTside.

Lemma hkp5_segOp1b_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps FR i R :
  hkp5_model_facts -> x25519_props x25519 ->
  semax (hkp5_Delta hkp5_G_Op1b) (hkp5_PL0 x25519 F V steps FR i 1) hkp5_op1_b
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
  unfold hkp5_op1_b.
  forward_call tt. Intros u.
  lazymatch goal with |- semax _ (PROPx ?P0 (LOCALx ?Q0 (SEPx ?R0))) _ _ =>
    forward_if (EX k: val, PROPx ((k = nullval \/ In k (map fst ML)) :: P0) (LOCALx (temp KC._t'42 k :: Q0) (SEPx R0))) end.
  { apply prop_right. intros [_ Hc]. apply (f_equal Int.unsigned) in Hc.
    rewrite Int.unsigned_repr in Hc by rep_lia. discriminate. }
  { forward. Exists nullval. entailer!. }
  { forward_call (gv, ML). Intros k. forward. Exists k. entailer!.
    match goal with Hk: (_ /\ k = nullval) \/ (_ /\ In k _) |- _ => destruct Hk as [[_ ->] | [_ Hk]]; auto end. }
  Intros k.
  forward.
  match goal with Hk: k = nullval \/ In k (map fst ML) |- _ => rename Hk into Hk1 end.
  pose proof HM as (Hpre & Hslots & _).
  pose proof Hinv as (Hr0 & Hw0 & _).
  cbn [f_p y_H y_P y_KS y_T y_w h5_warn] in Hr0, Hw0.
  pose proof (Hslots _ _ _ _ _ _ _ Hr0) as Hsok.
  pose proof Hr0 as (Hc & Hnd3 & Hpp & Hpc & Hpn).
  unfold hk5_slots in Hc, Hnd3. cbn [h5_ML h5_sp h5_sc h5_sn] in Hc, Hnd3, Hpp, Hpc, Hpn.
  pose proof Hc as (_ & Hnd & Hnn & _ & _ & HslF & _ & _ & Hpool).
  destruct (Hpre _ _ _ _ _ _ _ Hc) as (Kp & _ & Hnode & Hslotkp & Hinj).
  assert (Hsp: sp = nullval \/ In sp (map fst ML)) by (inv HslF; auto).
  assert (Hsc: sc = nullval \/ In sc (map fst ML)) by (inv HslF; match goal with H: Forall _ _ |- _ => inv H end; auto).
  assert (Hsn: sn = nullval \/ In sn (map fst ML)) by (inv HslF; match goal with H: Forall _ _ |- _ => inv H end;
    match goal with H: Forall _ _ |- _ => inv H end; auto).
  assert (Hk': hk5_slot_kp ML k = nullval \/ In (hk5_slot_kp ML k) (saddrs (t_D T))).
  { destruct Hk1 as [-> | Hk1]; [left; unfold hk5_slot_kp; rewrite if_true by auto; reflexivity |].
    right. destruct Hpool as (Hpa & _). apply Hpa. right; left. apply Hslotkp, Hk1. }
  lazymatch goal with |- semax _ (PROPx ?P0 (LOCALx ?Q0 (SEPx ?R0))) _ _ =>
    forward_if (PROPx P0 (LOCALx (temp KC._t'44 (hk5_slot_kp ML k) :: Q0) (SEPx R0))) end.
  { apply denote_tc_test_eq_split; [eapply derives_trans; [| apply (hk5o1_vp ML k TT Hk1)]; cancel |
      apply valid_pointer_null]. }
  { assert (Hk: In k (map fst ML)) by (destruct Hk1; [contradiction | assumption]).
    destruct (hk5o1_In_afind _ _ Hk) as (M & Hf).
    destruct (Hnode _ _ Hf) as (K & HK & Hm).
    pose proof Hm as (_ & HsfM & _).
    assert (Esl: hk5_slot_kp ML k = m5_kp M) by (unfold hk5_slot_kp; rewrite if_false by auto; rewrite Hf; reflexivity).
    assert_PROP (is_pointer_or_null (m5_kp M)) as PNkp.
    { sep_apply (hk5o1_pool_valid Tsh t T (m5_kp M) Ews _ HsfM).
      sep_apply (hk5o1_vp_pn (m5_kp M)). entailer!. }
    sep_apply (hk5o1_focus ML k M Hf). Intros nx. unfold hk5_node at 1. Intros.
    unfold hk5_mk_val.
    forward. forward.
    rewrite Esl.
    sep_apply (hk5o1_nclose ML k M nx Hf); [assumption..|].
    entailer!. }
  { forward. subst k. unfold hk5_slot_kp at 1. rewrite if_true by reflexivity. entailer!. }
  set (F0 := {| f_gv := gv; f_w := w; f_t := t; f_pt := pt; f_p := p; f_raw := raw; f_pub := pub;
                f_snap := snap; f_opub := opub; f_first := first; f_second := second |}) in *.
  set (D := hkp5_D x25519 F0 V) in *.
  pose proof Hinv as (_ & _ & Hdev & _).
  cbn [y_P f_w F0] in Hdev.
  change (itable Tsh t T) with (itable Tsh (d_itab D) T).
  forward_call (gv, S, ww, KS, T, Tsh, p, P, Tsh, w, D, Tsh, hk5_slot_kp ML k).
  assert_PROP (is_pointer_or_null sn) as PNsn by (sep_apply (hk5o1_ptr_or_null ML sn Hsn); entailer!).
  forward.
  forward.
  destruct (eq_dec k sn) as [Eks | Nks].
  - (* k = s_next: the slots rotate *)
    subst sn.
    assert (Ern: received_with_keypair_model P (hk5_slot_kp ML k) (mkKW KS T S) =
                 (true, p_set_slots P (hk5_slot_kp ML k) (p_cur P) nullval, kp_put (p_prev P) true (mkKW KS T S))).
    { unfold received_with_keypair_model. rewrite if_true by (rewrite Hpn; reflexivity). reflexivity. }
    assert (Erw: received_with_keypair_warn P (hk5_slot_kp ML k) (mkKW KS T S) ww = kp_put_warn (p_prev P) KS ww).
    { unfold received_with_keypair_warn. rewrite if_true by (rewrite Hpn; reflexivity). reflexivity. }
    rewrite Ern, Erw. cbn [fst snd].
    forward_if.
    { apply denote_tc_test_eq_split; eapply derives_trans; try apply (hk5o1_vp ML k TT Hk1); cancel. }
    2: { exfalso. auto. }
    match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
    { apply ENTAIL_refl. }
    { forward_if.
      { forward_call tt. { match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
        apply ENTAIL_refl. }
      forward. apply ENTAIL_refl. }
    { forward. apply ENTAIL_refl. }
    assert_PROP (is_pointer_or_null sp) as PNsp by (sep_apply (hk5o1_ptr_or_null ML sp Hsp); entailer!).
    assert_PROP (is_pointer_or_null sc) as PNsc by (sep_apply (hk5o1_ptr_or_null ML sc Hsc); entailer!).
    forward. forward. forward.
    destruct (hk5_put sp true ML fr mw) as [[ML' fr'] mw'] eqn:E.
    forward_call (gv, ML, fr, mw, sp, true).
    rewrite E. cbn [fst snd].
    forward. forward.
    pose proof (hk5o1_inv_rot HM F0 V S ww kc P KS T ML sp sc k fr mw now next_id id_known hsn ML' fr' mw' Hinv E)
      as Hinv'.
    rewrite Hpn in Hinv'.
    replace (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval by reflexivity.
    change (itable Tsh (d_itab D) (kw_T (kp_put (p_prev P) true (mkKW KS T S))))
      with (itable Tsh t (kw_T (kp_put (p_prev P) true (mkKW KS T S)))).
    assert (EPS: hk5_prsnap_val (p_set_slots P (hk5_slot_kp ML k) (p_cur P) nullval) = hk5_prsnap_val P)
      by reflexivity.
    unfold hkp5_Icont, hkp5_St.
    Exists (mkKY5 (kw_S (kp_put (p_prev P) true (mkKW KS T S))) (kp_put_warn (p_prev P) KS ww) kc
      (p_set_slots P (hk5_slot_kp ML k) (p_cur P) nullval)
      (kw_KS (kp_put (p_prev P) true (mkKW KS T S))) (kw_T (kp_put (p_prev P) true (mkKW KS T S)))
      (mkH5 ML' sc k nullval fr' mw') now next_id id_known hsn).
    unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
    subst D F0.
    cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second y_S y_w y_kc y_P y_KS y_T y_H y_now
       y_next_id y_id_known y_hsn h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn].
    rewrite EPS.
    entailer!.
  - (* k <> s_next: nothing changes *)
    assert (Ern: received_with_keypair_model P (hk5_slot_kp ML k) (mkKW KS T S) = (false, P, mkKW KS T S)).
    { unfold received_with_keypair_model. rewrite if_false; [reflexivity |]. rewrite Hpn. intros E.
      destruct Hk1 as [-> | Hk].
      - unfold hk5_slot_kp at 1 in E. rewrite if_true in E by reflexivity.
        destruct Hsn as [-> | Hsn]; [contradiction |]. apply (proj1 (Hslotkp sn Hsn)). auto.
      - exact (Nks (Hinj k sn Hk Hsn E)). }
    assert (Erw: received_with_keypair_warn P (hk5_slot_kp ML k) (mkKW KS T S) ww = ww).
    { unfold received_with_keypair_warn. unfold received_with_keypair_model in Ern.
      destruct (eq_dec (hk5_slot_kp ML k) (p_next P)); [discriminate | reflexivity]. }
    rewrite Ern, Erw. cbn [fst snd kw_S kw_KS kw_T].
    forward_if.
    { apply denote_tc_test_eq_split; eapply derives_trans; try apply (hk5o1_vp ML k TT Hk1);
        try apply (hk5o1_vp ML sn TT Hsn); cancel. }
    { exfalso. auto. }
    match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
    { apply ENTAIL_refl. }
    { forward_if.
      { forward_call tt. { match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
        apply ENTAIL_refl. }
      forward. apply ENTAIL_refl. }
    { forward. apply ENTAIL_refl. }
    unfold POSTCONDITION, abbreviate. cbn [RA_normal].
    change (itable Tsh (d_itab D) T) with (itable Tsh t T).
    unfold hkp5_Icont, hkp5_St.
    Exists (mkKY5 S ww kc P KS T (mkH5 ML sp sc sn fr mw) now next_id id_known hsn).
    unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
    subst D F0.
    cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second y_S y_w y_kc y_P y_KS y_T y_H y_now
       y_next_id y_id_known y_hsn h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn].
    entailer!.
Qed.
