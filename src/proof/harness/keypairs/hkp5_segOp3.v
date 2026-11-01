(* law keypairs: operation 3 of the loop body (hkp5_sOp3). *)
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
(* The model side of op 3: three slot puts (next, previous, current) on    *)
(* both sides keep the relation, the warnings and the counters             *)
(* ---------------------------------------------------------------------- *)

Lemma hk5o3_cnt_cons x R m : hk5_cnt (x :: R) m = (if eq_dec m x then 1 else 0) + hk5_cnt R m.
Proof. unfold hk5_cnt, hk5_eqb. simpl. destruct (EqDec_val m x); rewrite ?Zlength_cons; lia. Qed.

Lemma hk5o3_cnt_app l1 l2 m : hk5_cnt (l1 ++ l2) m = hk5_cnt l1 m + hk5_cnt l2 m.
Proof. unfold hk5_cnt. rewrite filter_app, Zlength_app. reflexivity. Qed.

Lemma hk5o3_cnt_nonneg R m : 0 <= hk5_cnt R m.
Proof. apply Zlength_nonneg. Qed.

Lemma hk5o3_cnt_remove1 s R m : In s R ->
  hk5_cnt R m = hk5_cnt (hk5_remove1 s R) m + (if eq_dec m s then 1 else 0).
Proof.
  induction R as [|x R IH]; simpl; intros I; [contradiction|].
  rewrite !hk5o3_cnt_cons. unfold eq_dec in *.
  destruct (EqDec_val x s) as [E|N].
  - subst x. lia.
  - destruct I as [E|I]; [congruence|]. rewrite hk5o3_cnt_cons, (IH I). unfold eq_dec in *. lia.
Qed.

Lemma hk5o3_cnt_In R m : 0 < hk5_cnt R m <-> In m R.
Proof.
  induction R as [|x R IH]; [unfold hk5_cnt; simpl; rewrite Zlength_nil; split; [lia | contradiction] |].
  rewrite hk5o3_cnt_cons. simpl. pose proof (hk5o3_cnt_nonneg R m). unfold eq_dec in *.
  destruct (EqDec_val m x) as [E|N]; split; intros Hm.
  - left; congruence.
  - lia.
  - right; apply IH; lia.
  - destruct Hm as [E|I]; [congruence | apply IH in I; lia].
Qed.

Lemma hk5o3_afind_in {A: Type} (l: list (val * A)) k K : afind l k = Some K -> In k (map fst l).
Proof.
  induction l as [|[x v] l IH]; simpl; [discriminate|]. unfold eq_dec in *.
  destruct (EqDec_val x k) as [<-|N]; auto.
Qed.

Lemma hk5o3_afind_adel {A: Type} (l: list (val * A)) s m : m <> s -> afind (adel l s) m = afind l m.
Proof.
  intros N. induction l as [|[x w] l IH]; simpl; [reflexivity|]. unfold eq_dec in *.
  destruct (EqDec_val x s) as [<-|Nx]; simpl.
  - destruct (EqDec_val x m); [congruence | reflexivity].
  - destruct (EqDec_val x m); [reflexivity | exact IH].
Qed.

Lemma hk5o3_afind_aupd {A: Type} (l: list (val * A)) s v m : m <> s -> afind (aupd l s v) m = afind l m.
Proof.
  intros N. induction l as [|[x w] l IH]; simpl; [reflexivity|]. unfold eq_dec in *.
  destruct (EqDec_val x s) as [<-|Nx]; simpl.
  - destruct (EqDec_val x m); [congruence | reflexivity].
  - destruct (EqDec_val x m); [reflexivity | exact IH].
Qed.

Lemma hk5o3_slot_put s u ML fr mw m : (m = nullval \/ m <> s) ->
  hk5_slot_kp (fst (fst (hk5_put s u ML fr mw))) m = hk5_slot_kp ML m.
Proof.
  intros Hm. unfold hk5_slot_kp. destruct (eq_dec m nullval); [reflexivity|].
  destruct Hm as [|Hm]; [contradiction|].
  unfold hk5_put. destruct (eq_dec s nullval); [reflexivity|]. destruct (afind ML s) as [M|]; [|reflexivity].
  cbv zeta. destruct (Int.eq (m5_refs M) REFCOUNT_SATURATED).
  - destruct u; cbn [fst]; [rewrite hk5o3_afind_aupd by auto|]; reflexivity.
  - destruct (Int.eq _ _); cbn [fst]; [rewrite hk5o3_afind_adel | rewrite hk5o3_afind_aupd]; auto.
Qed.

Lemma hk5o3_vin_vremove a k L : a <> k -> vin a (vremove k L) = vin a L.
Proof.
  intros N. unfold vin.
  assert (E: In a (vremove k L) <-> In a L).
  { induction L as [|x L IH]; simpl; [tauto|]. unfold eq_dec in *.
    destruct (EqDec_val x k) as [<-|Nx]; simpl; rewrite IH; split; intros H; auto;
      destruct H as [<-|H]; auto; congruence. }
  destruct (in_dec eq_dec a (vremove k L)), (in_dec eq_dec a L); tauto.
Qed.

Lemma hk5o3_sfind_sdel {A: Type} (D: list (val * share * A)) a k : a <> k -> sfind (sdel D k) a = sfind D a.
Proof.
  intros N. induction D as [|[[x sh] e] D IH]; simpl; [reflexivity|]. unfold eq_dec in *.
  destruct (EqDec_val x k) as [<-|Nx]; simpl.
  - destruct (EqDec_val x a); [congruence | reflexivity].
  - destruct (EqDec_val x a); [reflexivity | exact IH].
Qed.

(* a put of one of P's keypairs keeps the handshake entry and its membership *)
Lemma hk5o3_put_hs a k u KS T S : ~ In a (map fst KS) ->
  t_entry (kw_T (kp_put k u (mkKW KS T S))) a = t_entry T a /\
  vin a (t_L (kw_T (kp_put k u (mkKW KS T S)))) = vin a (t_L T).
Proof.
  intros NI. unfold kp_put. cbn [kw_KS kw_T kw_S].
  destruct (eq_dec k nullval); [auto|]. destruct (afind KS k) as [K|] eqn:EK; [|auto].
  assert (Nk: a <> k) by (intros ->; apply NI; eapply hk5o3_afind_in; eauto).
  assert (E1: t_entry (if u then t_remove T k else T) a = t_entry T a /\
              vin a (t_L (if u then t_remove T k else T)) = vin a (t_L T)).
  { destruct u; [|auto]. unfold t_remove, t_entry. cbn [t_D t_L]. split; [reflexivity|].
    apply hk5o3_vin_vremove; auto. }
  destruct (Int.eq _ _); cbn [kw_T]; [|exact E1].
  destruct E1 as [E1 E2]. unfold t_free, t_entry in *. cbn [t_D t_L] in *.
  rewrite hk5o3_sfind_sdel by auto. rewrite hk5o3_vin_vremove by auto. auto.
Qed.

Lemma hk5o3_core_in p OD OH R ML KS T m :
  hk5_core p OD OH R ML KS T -> In m R -> m = nullval \/ In m (map fst ML).
Proof. intros (_&_&_&_&_&CF&_) I. rewrite Forall_forall in CF. auto. Qed.

Lemma hk5o3_core_nodup p OD OH R ML KS T : hk5_core p OD OH R ML KS T -> NoDup (map fst ML).
Proof. intros (_&ND&_). exact ND. Qed.

Lemma hk5o3_core_hs p OD OH R ML KS T : hk5_core p OD OH R ML KS T -> ~ In (hs_addr p) (map fst KS).
Proof. intros (_&_&_&_&_&_&_&_&(_&N&_)). exact N. Qed.

(* one slot reference s (possibly NULL) of the reference list l1 ++ s :: l2 goes *)
Lemma hk5o3_step (FP: hk5_fact_put) (FPm: hk5_fact_perm) p OD OH l1 s l2 ML KS T S fr mw w0 w ML' fr' mw' :
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
    { intros m Nm. pose proof (hk5o3_cnt_remove1 s _ m Is) as Em.
      rewrite hk5o3_cnt_app, hk5o3_cnt_cons in Em. rewrite hk5o3_cnt_app, hk5o3_cnt_cons.
      unfold eq_dec in *. destruct (EqDec_val m nullval); [contradiction|]. destruct (EqDec_val m s); lia. }
    apply (FPm _ _ _ _ _ _ _ _ Ecnt); [| exact C'].
    pose proof C' as (_&_&_&_&_&CF&_). rewrite Forall_forall in CF |- *. intros x Ix.
    destruct (eq_dec x nullval) as [|Nx]; [left; auto|]. apply CF.
    apply hk5o3_cnt_In. rewrite Ecnt by auto. apply hk5o3_cnt_In. auto.
Qed.

Lemma hk5o3_nonnull3 a b c : NoDup (hk5_nonnull [a; b; c]) ->
  (a = nullval \/ a <> c) /\ (b = nullval \/ b <> c) /\ (b = nullval \/ b <> a).
Proof.
  unfold hk5_nonnull, hk5_eqb. simpl. unfold eq_dec in *.
  destruct (EqDec_val a nullval), (EqDec_val b nullval), (EqDec_val c nullval); simpl; intros ND;
    repeat split; auto; inv ND; try (inv H2); simpl in *; intuition congruence.
Qed.

Lemma hk5o3_acc S fr n S' fr' n' f0 a0 :
  Int64.sub (s_frees S) f0 = fr -> Int64.sub (s_allocs S) a0 = Int64.add fr (Int64.repr n) ->
  ((S' = S /\ fr' = fr /\ n' = n) \/ (S' = shim_free S /\ fr' = Int64.add fr Int64.one /\ n' = n - 1)) ->
  Int64.sub (s_frees S') f0 = fr' /\ Int64.sub (s_allocs S') a0 = Int64.add fr' (Int64.repr n').
Proof.
  intros E1 E2 [(->&->&->)|(->&->&->)]; [auto|]. cbn [s_frees s_allocs shim_free]. split.
  - rewrite Int64.sub_add_l, E1. reflexivity.
  - rewrite E2, Int64.add_assoc. f_equal. unfold Int64.one. rewrite add64_repr. f_equal. lia.
Qed.

Lemma hk5o3_model (MF: hkp5_model_facts) p OD OH ML sp sc sn fr mw P KS T S w0 w
    ML1 fr1 mw1 ML2 fr2 mw2 ML3 fr3 mw3 :
  hk5_rel p OD OH (mkH5 ML sp sc sn fr mw) P KS T -> hk5_warn_ok w0 mw w ->
  hk5_put sn true ML fr mw = (ML1, fr1, mw1) -> hk5_put sp true ML1 fr1 mw1 = (ML2, fr2, mw2) ->
  hk5_put sc true ML2 fr2 mw2 = (ML3, fr3, mw3) ->
  kps_in_pool T p KS /\ slots_ok P KS /\
  (sn = nullval \/ In sn (map fst ML)) /\ NoDup (map fst ML) /\
  (sp = nullval \/ In sp (map fst ML1)) /\ NoDup (map fst ML1) /\
  (sc = nullval \/ In sc (map fst ML2)) /\ NoDup (map fst ML2) /\
  hk5_rel p OD OH (mkH5 ML3 nullval nullval nullval fr3 mw3) (fst (keypairs_clear_model P (mkKW KS T S)))
    (kw_KS (snd (keypairs_clear_model P (mkKW KS T S)))) (kw_T (snd (keypairs_clear_model P (mkKW KS T S)))) /\
  hk5_warn_ok w0 mw3 (keypairs_clear_warn P (mkKW KS T S) w) /\
  t_entry (kw_T (snd (keypairs_clear_model P (mkKW KS T S)))) (hs_addr p) = t_entry T (hs_addr p) /\
  vin (hs_addr p) (t_L (kw_T (snd (keypairs_clear_model P (mkKW KS T S))))) = vin (hs_addr p) (t_L T) /\
  (forall f0 a0, Int64.sub (s_frees S) f0 = fr -> Int64.sub (s_allocs S) a0 = Int64.add fr (Int64.repr (Zlength ML)) ->
     Int64.sub (s_frees (kw_S (snd (keypairs_clear_model P (mkKW KS T S))))) f0 = fr3 /\
     Int64.sub (s_allocs (kw_S (snd (keypairs_clear_model P (mkKW KS T S))))) a0 =
       Int64.add fr3 (Int64.repr (Zlength ML3))).
Proof.
  intros R Wk E1 E2 E3.
  destruct MF as (FPre & FS & FPm & FP & _).
  pose proof (FS _ _ _ _ _ _ _ R) as SL.
  destruct R as (C0 & ND & Ep & Ec & En).
  cbn [hk5_slots h5_sp h5_sc h5_sn h5_ML] in C0, ND, Ep, Ec, En.
  pose proof (FPre _ _ _ _ _ _ _ C0) as (KP & _).
  pose proof (hk5o3_nonnull3 _ _ _ ND) as (D1&D2&D3).
  (* next *)
  change [sp; sc; sn] with ([sp; sc] ++ sn :: []) in C0.
  pose proof (hk5o3_step FP FPm p OD OH [sp; sc] sn [] ML KS T S fr mw w0 w ML1 fr1 mw1 C0 Wk E1) as (C1&W1&A1).
  pose proof (hk5o3_slot_put sn true ML fr mw sp D1) as Sp1.
  pose proof (hk5o3_slot_put sn true ML fr mw sc D2) as Sc1.
  rewrite E1 in Sp1, Sc1. cbn [fst snd] in Sp1, Sc1.
  pose proof (hk5o3_put_hs (hs_addr p) (hk5_slot_kp ML sn) true KS T S (hk5o3_core_hs _ _ _ _ _ _ _ C0)) as H1.
  unfold keypairs_clear_model, keypairs_clear_warn. cbn [fst snd kw_KS]. rewrite En.
  destruct (kp_put (hk5_slot_kp ML sn) true (mkKW KS T S)) as [KS1 T1 S1] eqn:EW1.
  cbn [kw_KS kw_T kw_S] in C1, A1, H1 |- *.
  (* previous *)
  change ([sp; sc] ++ nullval :: []) with ([] ++ sp :: [sc; nullval]) in C1.
  pose proof (hk5o3_step FP FPm p OD OH [] sp [sc; nullval] ML1 KS1 T1 S1 fr1 mw1 w0 _ ML2 fr2 mw2 C1 W1 E2)
    as (C2&W2&A2).
  pose proof (hk5o3_slot_put sp true ML1 fr1 mw1 sc D3) as Sc2.
  rewrite E2 in Sc2. cbn [fst snd] in Sc2.
  pose proof (hk5o3_put_hs (hs_addr p) (hk5_slot_kp ML1 sp) true KS1 T1 S1 (hk5o3_core_hs _ _ _ _ _ _ _ C1)) as H2.
  rewrite Ep, <- Sp1.
  destruct (kp_put (hk5_slot_kp ML1 sp) true (mkKW KS1 T1 S1)) as [KS2 T2 S2] eqn:EW2.
  cbn [kw_KS kw_T kw_S] in C2, A2, H2 |- *.
  (* current *)
  change ([] ++ nullval :: [sc; nullval]) with ([nullval] ++ sc :: [nullval]) in C2.
  pose proof (hk5o3_step FP FPm p OD OH [nullval] sc [nullval] ML2 KS2 T2 S2 fr2 mw2 w0 _ ML3 fr3 mw3 C2 W2 E3)
    as (C3&W3&A3).
  pose proof (hk5o3_put_hs (hs_addr p) (hk5_slot_kp ML2 sc) true KS2 T2 S2 (hk5o3_core_hs _ _ _ _ _ _ _ C2)) as H3.
  rewrite Ec, <- Sc1, <- Sc2.
  destruct (kp_put (hk5_slot_kp ML2 sc) true (mkKW KS2 T2 S2)) as [KS3 T3 S3] eqn:EW3.
  cbn [kw_KS kw_T kw_S] in C3, A3, H3 |- *.
  split; [exact KP|]. split; [exact SL|].
  split. { apply (hk5o3_core_in _ _ _ _ _ _ _ _ C0). cbn. tauto. }
  split; [exact (hk5o3_core_nodup _ _ _ _ _ _ _ C0)|].
  split. { apply (hk5o3_core_in _ _ _ _ _ _ _ _ C1). cbn. tauto. }
  split; [exact (hk5o3_core_nodup _ _ _ _ _ _ _ C1)|].
  split. { apply (hk5o3_core_in _ _ _ _ _ _ _ _ C2). cbn. tauto. }
  split; [exact (hk5o3_core_nodup _ _ _ _ _ _ _ C2)|].
  split.
  - unfold hk5_rel. cbn [hk5_slots h5_sp h5_sc h5_sn h5_ML p_prev p_cur p_next p_set_slots].
    split; [exact C3|].
    split; [unfold hk5_nonnull, hk5_eqb; simpl; constructor|].
    unfold hk5_slot_kp. rewrite !if_true by reflexivity. auto.
  - split; [exact W3|].
    destruct H1 as [H1a H1b], H2 as [H2a H2b], H3 as [H3a H3b].
    split; [congruence|]. split; [congruence|].
    intros f0 a0 F1 F2.
    destruct (hk5o3_acc _ _ _ _ _ _ f0 a0 F1 F2 A1) as [G1 G2].
    destruct (hk5o3_acc _ _ _ _ _ _ f0 a0 G1 G2 A2) as [G3 G4].
    exact (hk5o3_acc _ _ _ _ _ _ f0 a0 G3 G4 A3).
Qed.

Section VSTside.
#[local] Existing Instance W_keypairs.

Lemma hk5o3_mklist_ptr ML m : In m (map fst ML) -> hk5_mklist ML |-- !! isptr m.
Proof.
  induction ML as [|[x M] ML IH]; simpl; intros I; [contradiction|].
  destruct I as [<-|I].
  - unfold hk5_node. Intros. entailer!.
  - sep_apply (IH I). entailer!.
Qed.

Lemma hk5o3_ptr_or_null ML m : m = nullval \/ In m (map fst ML) -> hk5_mklist ML |-- !! is_pointer_or_null m.
Proof.
  intros [->|I].
  - apply prop_right. simpl; auto.
  - sep_apply (hk5o3_mklist_ptr ML m I). entailer!.
Qed.

End VSTside.

Lemma hkp5_segOp3_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps FR i R :
  hkp5_model_facts -> x25519_props x25519 ->
  semax (hkp5_Delta hkp5_G_Op3) (hkp5_PL0 x25519 F V steps FR i 3) hkp5_sOp3
    (loop1_ret_assert (hkp5_Icont x25519 F V steps FR i) R).
Proof.
  intros MF HX.
  unfold hkp5_PL0, hkp5_sOp3.
  Intros Y.
  destruct F as [gv w t pt p raw pub snap opub first second].
  destruct Y as [S wn kc P KS T HH now next_id id_known hsn].
  destruct HH as [ML sp sc sn fr mw].
  destruct H1 as (Hrel & Hwarn & Hdev & Hsid & Hpr & Hfr & Hal & Hid & Hnow & Hhsm).
  unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
  cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second y_S y_w y_kc y_P y_KS y_T y_H y_now
       y_next_id y_id_known y_hsn h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn]
    in Hrel, Hwarn, Hdev, Hsid, Hpr, Hfr, Hal, Hid, Hnow, Hhsm |- *.
  destruct R as [Rn Rb Rc Rr]. unfold loop1_ret_assert, hkp5_Delta.
  abbreviate_semax.
  set (F0 := {| f_gv := gv; f_w := w; f_t := t; f_pt := pt; f_p := p; f_raw := raw; f_pub := pub;
                f_snap := snap; f_opub := opub; f_first := first; f_second := second |}) in *.
  set (D := hkp5_D x25519 F0 V) in *.
  destruct (hk5_put sn true ML fr mw) as [[ML1 fr1] mw1] eqn:E1.
  destruct (hk5_put sp true ML1 fr1 mw1) as [[ML2 fr2] mw2] eqn:E2.
  destruct (hk5_put sc true ML2 fr2 mw2) as [[ML3 fr3] mw3] eqn:E3.
  destruct (hk5o3_model MF p (v_OD V) (v_OH V) ML sp sc sn fr mw P KS T S (v_w0 V) wn
              ML1 fr1 mw1 ML2 fr2 mw2 ML3 fr3 mw3 Hrel Hwarn E1 E2 E3)
    as (KP & SL & In1 & ND1 & In2 & ND2 & In3 & ND3 & Rel' & Warn' & Hent & Hvin & Acc).
  change (itable Tsh t T) with (itable Tsh (d_itab D) T).
  forward_call (gv, S, wn, KS, T, Tsh, p, P, Tsh, w, D, Tsh).
  set (CL := keypairs_clear_model P {| kw_KS := KS; kw_T := T; kw_S := S |}) in *.
  assert_PROP (is_pointer_or_null sn) as Psn by (sep_apply (hk5o3_ptr_or_null ML sn In1); entailer!).
  forward.
  forward.
  forward_call (gv, ML, fr, mw, sn, true).
  rewrite E1. cbn [fst snd].
  assert_PROP (is_pointer_or_null sp) as Psp by (sep_apply (hk5o3_ptr_or_null ML1 sp In2); entailer!).
  forward.
  forward.
  forward_call (gv, ML1, fr1, mw1, sp, true).
  rewrite E2. cbn [fst snd].
  assert_PROP (is_pointer_or_null sc) as Psc by (sep_apply (hk5o3_ptr_or_null ML2 sc In3); entailer!).
  forward.
  forward.
  forward_call (gv, ML2, fr2, mw2, sc, true).
  rewrite E3. cbn [fst snd].
  assert (EP: fst CL = p_set_slots P nullval nullval nullval) by reflexivity.
  set (Y' := mkKY5 (kw_S (snd CL)) (keypairs_clear_warn P {| kw_KS := KS; kw_T := T; kw_S := S |} wn) kc (fst CL)
               (kw_KS (snd CL)) (kw_T (snd CL)) (mkH5 ML3 nullval nullval nullval fr3 mw3) now next_id id_known hsn).
  assert (Hinv': hkp5_inv F0 V Y').
  { destruct (Acc _ _ Hfr Hal) as [A1 A2].
    destruct Hhsm as ((Hh1 & Hh2 & Hh3) & Hpk).
    unfold hkp5_inv, hk5_hsm_ok, Y'. cbn [y_S y_w y_kc y_P y_KS y_T y_H y_now y_next_id y_id_known y_hsn h5_ML h5_frees h5_warn
      f_p f_w].
    rewrite <- Hent in Hh1. rewrite <- Hvin in Hh2.
    exact (conj Rel' (conj Warn' (conj Hdev (conj Hsid (conj Hpr (conj A1 (conj A2 (conj Hid (conj Hnow
      (conj (conj Hh1 (conj Hh2 Hh3)) Hpk)))))))))). }
  assert (EPS: hk5_prsnap_val (fst CL) = hk5_prsnap_val P) by (rewrite EP; reflexivity).
  change (itable Tsh (d_itab D) (kw_T (snd CL))) with (itable Tsh t (kw_T (snd CL))).
  replace (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval by reflexivity.
  unfold hkp5_Icont, hkp5_St. Exists Y'.
  unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
  subst Y'. subst D F0.
  cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second y_S y_w y_kc y_P y_KS y_T y_H y_now
       y_next_id y_id_known y_hsn h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn].
  rewrite EPS.
  entailer!.
Qed.
