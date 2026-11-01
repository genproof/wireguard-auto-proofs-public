(* law keypairs: operation 6 of the loop body (hkp5_sOp6: keypair_put of a held reference or of NULL). *)
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
(* The model side of op 6                                                  *)
(* ---------------------------------------------------------------------- *)

Lemma hk5o6_afind_in {A: Type} (l: list (val * A)) k K : afind l k = Some K -> In k (map fst l).
Proof.
  induction l as [|[x v] l IH]; simpl; [discriminate|]. unfold eq_dec in *.
  destruct (EqDec_val x k) as [<-|N]; auto.
Qed.

Lemma hk5o6_in_afind {A: Type} (l: list (val * A)) k K : NoDup (map fst l) -> In (k, K) l -> afind l k = Some K.
Proof.
  induction l as [|[x v] l IH]; simpl; [contradiction|]. intros ND I. inv ND. unfold eq_dec in *.
  destruct (EqDec_val x k) as [<-|N].
  - destruct I as [E|I]; [congruence|]. exfalso. apply H1. change x with (fst (x, K)). apply in_map, I.
  - destruct I as [E|I]; [congruence|]. auto.
Qed.

Lemma hk5o6_afind_adel {A: Type} (l: list (val * A)) s m : m <> s -> afind (adel l s) m = afind l m.
Proof.
  intros N. induction l as [|[x w] l IH]; simpl; [reflexivity|]. unfold eq_dec in *.
  destruct (EqDec_val x s) as [<-|Nx]; simpl.
  - destruct (EqDec_val x m); [congruence | reflexivity].
  - destruct (EqDec_val x m); [reflexivity | exact IH].
Qed.

Lemma hk5o6_afind_adel_same {A: Type} (l: list (val * A)) s : NoDup (map fst l) -> afind (adel l s) s = None.
Proof.
  induction l as [|[x w] l IH]; simpl; [reflexivity|]. intros ND. inv ND. unfold eq_dec in *.
  destruct (EqDec_val x s) as [<-|Nx]; simpl.
  - clear IH. induction l as [|[y u] l IHl]; simpl; [reflexivity|].
    destruct (EqDec_val y x) as [<-|Ny]; [exfalso; apply H1; left; reflexivity|].
    inv H2. apply IHl; auto. intros I; apply H1; right; exact I.
  - destruct (EqDec_val x s); [congruence|]. auto.
Qed.

Lemma hk5o6_afind_aupd {A: Type} (l: list (val * A)) s v m : m <> s -> afind (aupd l s v) m = afind l m.
Proof.
  intros N. induction l as [|[x w] l IH]; simpl; [reflexivity|]. unfold eq_dec in *.
  destruct (EqDec_val x s) as [<-|Nx]; simpl.
  - destruct (EqDec_val x m); [congruence | reflexivity].
  - destruct (EqDec_val x m); [reflexivity | exact IH].
Qed.

Lemma hk5o6_afind_aupd_same {A: Type} (l: list (val * A)) a v M :
  afind l a = Some M -> afind (aupd l a v) a = Some v.
Proof.
  induction l as [| [x w] l IH]; simpl; [discriminate |]. unfold eq_dec in *.
  destruct (EqDec_val x a) as [-> | Hxa]; simpl.
  - rewrite if_true by auto. reflexivity.
  - rewrite if_false by auto. exact IH.
Qed.

Lemma hk5o6_map_fst_aupd {A: Type} (l: list (val * A)) a v : map fst (aupd l a v) = map fst l.
Proof.
  induction l as [| [x w] l IH]; simpl; [reflexivity |]. unfold eq_dec in *. destruct (EqDec_val x a); simpl; f_equal; auto.
Qed.

Lemma hk5o6_head_aupd {A: Type} (l: list (val * A)) a v : hk5_head (aupd l a v) = hk5_head l.
Proof. destruct l as [| [x w] l]; simpl; [reflexivity |]. unfold eq_dec. destruct (EqDec_val x a); reflexivity. Qed.

(* the keypair addresses of the nodes are kept *)
Definition hk5o6_kpp (ML ML': list (val * hk5_mk)) : Prop :=
  forall x M', afind ML' x = Some M' -> exists M'', afind ML x = Some M'' /\ m5_kp M'' = m5_kp M'.

Lemma hk5o6_kpp_trans a b c : hk5o6_kpp a b -> hk5o6_kpp b c -> hk5o6_kpp a c.
Proof.
  intros Hab Hbc x M' E. destruct (Hbc x M' E) as (M1 & E1 & K1). destruct (Hab x M1 E1) as (M2 & E2 & K2).
  exists M2. split; congruence.
Qed.

Lemma hk5o6_kpp_aupd ML m M M' : afind ML m = Some M -> m5_kp M' = m5_kp M -> hk5o6_kpp ML (aupd ML m M').
Proof.
  intros E K x M1 E1. destruct (eq_dec x m) as [->|N].
  - rewrite (hk5o6_afind_aupd_same _ _ _ _ E) in E1. inv E1. eauto.
  - rewrite hk5o6_afind_aupd in E1 by auto. eauto.
Qed.

Lemma hk5o6_kpp_put m u ML fr mw : NoDup (map fst ML) -> hk5o6_kpp ML (fst (fst (hk5_put m u ML fr mw))).
Proof.
  intros ND. unfold hk5_put. destruct (eq_dec m nullval).
  { intros x M' E; eauto. }
  destruct (afind ML m) as [M|] eqn:EM; [| intros x M' E; eauto]. cbv zeta.
  destruct (Int.eq (m5_refs M) REFCOUNT_SATURATED).
  - destruct u; cbn [fst]; [apply (hk5o6_kpp_aupd _ _ _ _ EM); reflexivity |]. intros x M' E; eauto.
  - destruct (Int.eq _ _); cbn [fst].
    + intros x M' E. destruct (eq_dec x m) as [->|N].
      * rewrite hk5o6_afind_adel_same in E by auto. discriminate.
      * rewrite hk5o6_afind_adel in E by auto. eauto.
    + apply (hk5o6_kpp_aupd _ _ _ _ EM). destruct u; reflexivity.
Qed.

Lemma hk5o6_slot_kpp ML ML' x : hk5o6_kpp ML ML' -> NoDup (map fst ML') ->
  (x = nullval \/ In x (map fst ML')) -> hk5_slot_kp ML' x = hk5_slot_kp ML x.
Proof.
  intros K ND Hx. unfold hk5_slot_kp. destruct (eq_dec x nullval); [reflexivity|].
  destruct Hx as [|Hx]; [contradiction|].
  apply list_in_map_inv in Hx. destruct Hx as ([y M'] & Ey & I). cbn [fst] in Ey. subst y.
  rewrite (hk5o6_in_afind _ _ _ ND I). destruct (K x M' (hk5o6_in_afind _ _ _ ND I)) as (M'' & E & KE).
  rewrite E. auto.
Qed.

Lemma hk5o6_vin_vremove a k L : a <> k -> vin a (vremove k L) = vin a L.
Proof.
  intros N. unfold vin.
  assert (E: In a (vremove k L) <-> In a L).
  { induction L as [|x L IH]; simpl; [tauto|]. unfold eq_dec in *.
    destruct (EqDec_val x k) as [<-|Nx]; simpl; rewrite IH; split; intros H; auto;
      destruct H as [<-|H]; auto; congruence. }
  destruct (in_dec eq_dec a (vremove k L)), (in_dec eq_dec a L); tauto.
Qed.

Lemma hk5o6_sfind_sdel {A: Type} (D: list (val * share * A)) a k : a <> k -> sfind (sdel D k) a = sfind D a.
Proof.
  intros N. induction D as [|[[x sh] e] D IH]; simpl; [reflexivity|]. unfold eq_dec in *.
  destruct (EqDec_val x k) as [<-|Nx]; simpl.
  - destruct (EqDec_val x a); [congruence | reflexivity].
  - destruct (EqDec_val x a); [reflexivity | exact IH].
Qed.

(* a put of one of P's keypairs keeps the handshake entry and its membership *)
Lemma hk5o6_put_hs a k u KS T S : ~ In a (map fst KS) ->
  t_entry (kw_T (kp_put k u (mkKW KS T S))) a = t_entry T a /\
  vin a (t_L (kw_T (kp_put k u (mkKW KS T S)))) = vin a (t_L T).
Proof.
  intros NI. unfold kp_put. cbn [kw_KS kw_T kw_S].
  destruct (eq_dec k nullval); [auto|]. destruct (afind KS k) as [K|] eqn:EK; [|auto].
  assert (Nk: a <> k) by (intros ->; apply NI; eapply hk5o6_afind_in; eauto).
  assert (E1: t_entry (if u then t_remove T k else T) a = t_entry T a /\
              vin a (t_L (if u then t_remove T k else T)) = vin a (t_L T)).
  { destruct u; [|auto]. unfold t_remove, t_entry. cbn [t_D t_L]. split; [reflexivity|].
    apply hk5o6_vin_vremove; auto. }
  destruct (Int.eq _ _); cbn [kw_T]; [|exact E1].
  destruct E1 as [E1 E2]. unfold t_free, t_entry in *. cbn [t_D t_L] in *.
  rewrite hk5o6_sfind_sdel by auto. rewrite hk5o6_vin_vremove by auto. auto.
Qed.

Lemma hk5o6_acc S fr n S' fr' n' f0 a0 :
  Int64.sub (s_frees S) f0 = fr -> Int64.sub (s_allocs S) a0 = Int64.add fr (Int64.repr n) ->
  ((S' = S /\ fr' = fr /\ n' = n) \/ (S' = shim_free S /\ fr' = Int64.add fr Int64.one /\ n' = n - 1)) ->
  Int64.sub (s_frees S') f0 = fr' /\ Int64.sub (s_allocs S') a0 = Int64.add fr' (Int64.repr n').
Proof.
  intros E1 E2 [(->&->&->)|(->&->&->)]; [auto|]. cbn [s_frees s_allocs shim_free]. split.
  - rewrite Int64.sub_add_l, E1. reflexivity.
  - rewrite E2, Int64.add_assoc. f_equal. unfold Int64.one. rewrite add64_repr. f_equal. lia.
Qed.

Lemma hk5o6_held_pos (h: int64) : h <> Int64.zero -> Int64.unsigned h > 0.
Proof.
  intros N. pose proof (Int64.unsigned_range h).
  destruct (Z.eq_dec (Int64.unsigned h) 0) as [E|]; [|lia].
  exfalso. apply N. rewrite <- (Int64.repr_unsigned h), E. reflexivity.
Qed.

Lemma hk5o6_and1 u : 0 <= u <= Byte.max_unsigned ->
  Int.and (Int.repr u) (Int.repr 1) = if Z.odd u then Int.one else Int.zero.
Proof.
  intros Hu. unfold Int.and. rewrite Int.unsigned_repr by rep_lia.
  change (Int.unsigned (Int.repr 1)) with (Z.ones 1). rewrite Z.land_ones by lia.
  rewrite Zmod_odd. destruct (Z.odd u); reflexivity.
Qed.

(* the whole model step of op 6 on a held node m *)
Lemma hk5o6_model (MF: hkp5_model_facts) p OD OH ML sp sc sn fr mw P KS T S w0 w m M u ML' fr' mw' :
  hk5_rel p OD OH (mkH5 ML sp sc sn fr mw) P KS T -> hk5_warn_ok w0 mw w ->
  afind ML m = Some M -> m5_held M <> Int64.zero ->
  hk5_put m u (aupd ML m (m5_set_held M (Int64.sub (m5_held M) Int64.one))) fr mw = (ML', fr', mw') ->
  kps_in_pool T p KS /\ In (m5_kp M) (map fst KS) /\
  hk5_rel p OD OH (mkH5 ML' sp sc sn fr' mw') P (kw_KS (kp_put (m5_kp M) u (mkKW KS T S)))
    (kw_T (kp_put (m5_kp M) u (mkKW KS T S))) /\
  hk5_warn_ok w0 mw' (kp_put_warn (m5_kp M) KS w) /\
  t_entry (kw_T (kp_put (m5_kp M) u (mkKW KS T S))) (hs_addr p) = t_entry T (hs_addr p) /\
  vin (hs_addr p) (t_L (kw_T (kp_put (m5_kp M) u (mkKW KS T S)))) = vin (hs_addr p) (t_L T) /\
  (forall f0 a0, Int64.sub (s_frees S) f0 = fr -> Int64.sub (s_allocs S) a0 = Int64.add fr (Int64.repr (Zlength ML)) ->
     Int64.sub (s_frees (kw_S (kp_put (m5_kp M) u (mkKW KS T S)))) f0 = fr' /\
     Int64.sub (s_allocs (kw_S (kp_put (m5_kp M) u (mkKW KS T S)))) a0 = Int64.add fr' (Int64.repr (Zlength ML'))).
Proof.
  intros R Wk EM HM E.
  destruct MF as (FPre & FS & FPm & FP & FH & _).
  destruct R as (C0 & ND & Ep & Ec & En).
  cbn [hk5_slots h5_sp h5_sc h5_sn h5_ML] in C0, ND, Ep, Ec, En.
  pose proof (FPre _ _ _ _ _ _ _ C0) as (KP & _ & Hnk & _).
  destruct (Hnk m M EM) as (K & EK & _).
  pose proof (FH p OD OH _ ML KS T S fr mw w0 w m M u C0 Wk EM (hk5o6_held_pos _ HM)) as FHm.
  cbv zeta in FHm. rewrite E in FHm. destruct FHm as (C' & Wk' & D).
  pose proof C0 as (_ & ND0 & _ & _ & _ & _ & _ & _ & (_ & NIhs & _)).
  set (ML1 := aupd ML m (m5_set_held M (Int64.sub (m5_held M) Int64.one))) in E.
  assert (ND1: NoDup (map fst ML1)) by (unfold ML1; rewrite hk5o6_map_fst_aupd; exact ND0).
  assert (K1: hk5o6_kpp ML ML') .
  { apply hk5o6_kpp_trans with ML1; [apply (hk5o6_kpp_aupd _ _ _ _ EM); reflexivity |].
    pose proof (hk5o6_kpp_put m u ML1 fr mw ND1) as KK. rewrite E in KK. exact KK. }
  pose proof C' as (_ & ND' & _ & _ & _ & CF' & _). rewrite Forall_forall in CF'.
  split; [exact KP|]. split; [eapply hk5o6_afind_in; eauto|].
  split.
  { unfold hk5_rel. cbn [hk5_slots h5_sp h5_sc h5_sn h5_ML].
    split; [exact C'|]. split; [exact ND|].
    rewrite !(hk5o6_slot_kpp ML ML') by (auto; apply CF'; simpl; tauto). auto. }
  split; [exact Wk'|].
  destruct (hk5o6_put_hs (hs_addr p) (m5_kp M) u KS T S NIhs) as [H1 H2].
  split; [exact H1|]. split; [exact H2|].
  intros f0 a0 F1 F2. apply (hk5o6_acc _ _ _ _ _ _ f0 a0 F1 F2).
  destruct D as [(D1&D2&D3)|(D1&D2&D3&_)]; [left|right]; auto.
Qed.

Section VSTside.
#[local] Existing Instance W_keypairs.

(* the node at k in the list, for a field update that keeps the byte lengths *)
Lemma hk5o6_focus ML k M M' : afind ML k = Some M ->
  Zlength (m5_send M') = Zlength (m5_send M) -> Zlength (m5_recv M') = Zlength (m5_recv M) ->
  exists nx Rst, hk5_mklist ML = (data_at Ews t_mk5 (hk5_mk_val M nx) k * Rst)%logic /\
    hk5_mklist (aupd ML k M') = (data_at Ews t_mk5 (hk5_mk_val M' nx) k * Rst)%logic.
Proof.
  intros E Ls Lr. induction ML as [| [x X] ML IH]; cbn [afind] in E; [discriminate |].
  cbn [hk5_mklist aupd].
  destruct (eq_dec x k) as [<- | Hne].
  - injection E as <-. cbn [hk5_mklist]. unfold hk5_node.
    exists (hk5_head ML), ((!! (Zlength (m5_send X) = 32 /\ Zlength (m5_recv X) = 32) &&
      malloc_token Ews t_mk5 x) * hk5_mklist ML)%logic.
    rewrite Ls, Lr. split; apply pred_ext; entailer!.
  - destruct (IH E) as (nx & Rst & E1 & E2). cbn [hk5_mklist]. rewrite hk5o6_head_aupd.
    exists nx, (hk5_node x X (hk5_head ML) * Rst)%logic.
    rewrite E1, E2. split; rewrite <- !sepcon_assoc, (sepcon_comm (hk5_node x X (hk5_head ML))); reflexivity.
Qed.

Lemma hk5o6_mklist_ptr ML m : In m (map fst ML) -> hk5_mklist ML |-- !! isptr m.
Proof.
  induction ML as [|[x M] ML IH]; simpl; intros I; [contradiction|].
  destruct I as [<-|I].
  - unfold hk5_node. Intros. entailer!.
  - sep_apply (IH I). entailer!.
Qed.

Lemma hk5o6_kp_ptr KS k : In k (map fst KS) -> keypairs_rep W_keypairs KS |-- !! isptr k.
Proof.
  induction KS as [| [x K] KS IH]; cbn [map fst In]; [tauto |].
  unfold keypairs_rep. cbn [iter_sepcon.iter_sepcon]. intros [-> | Hin].
  - unfold keypair_item_rep, keypair_rep at 1. rewrite sepcon_andp_prop'. apply andp_left1.
    apply prop_derives. intros [Hfc _]. exact (field_compatible_isptr _ _ _ Hfc).
  - sep_apply (IH Hin). Intros. apply prop_right; auto.
Qed.

End VSTside.

Lemma hkp5_segOp6_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps FR i R :
  hkp5_model_facts -> x25519_props x25519 ->
  semax (hkp5_Delta hkp5_G_Op6) (hkp5_PL0 x25519 F V steps FR i 6) hkp5_sOp6
    (loop1_ret_assert (hkp5_Icont x25519 F V steps FR i) R).
Proof.
  intros MF HX.
  unfold hkp5_PL0, hkp5_sOp6.
  Intros Y.
  destruct F as [gv w t pt p raw pub snap opub first second].
  destruct Y as [S wn kc P KS T HH now next_id id_known hsn].
  destruct HH as [ML sp sc sn fr mw].
  pose proof H1 as Hinv0.
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
  forward_call tt.
  Intros u.
  forward.
  rewrite (hk5o6_and1 u) by assumption.
  forward_call (gv, ML).
  Intros k.
  pose proof Hrel as (C0 & _).
  pose proof C0 as (_ & ND0 & _).
  pose proof (proj1 MF _ _ _ _ _ _ _ C0) as (KP & _).
  change (itable Tsh t T) with (itable Tsh (d_itab D) T).
  destruct H5 as [[-> Hall] | (M & HIn & HM)].
  - (* no held reference: wg_noise_keypair_put(NULL, unref) *)
    forward_if (hkp5_Icont x25519 F0 V steps FR i).
    + forward_call (gv, S, wn, KS, T, nullval, Z.odd u, Tsh, p, P, Tsh, w, D, Tsh).
      { apply prop_right. destruct (Z.odd u); reflexivity. }
      assert (EW: kp_put nullval (Z.odd u) {| kw_KS := KS; kw_T := T; kw_S := S |} = {| kw_KS := KS; kw_T := T; kw_S := S |})
        by (unfold kp_put; rewrite if_true by reflexivity; reflexivity).
      assert (Ew: kp_put_warn nullval KS wn = wn) by (unfold kp_put_warn; rewrite if_true by reflexivity; reflexivity).
      rewrite EW, Ew. cbn [kw_S kw_KS kw_T].
      change (itable Tsh (d_itab D) T) with (itable Tsh t T).
      unfold hkp5_Icont, hkp5_St.
      Exists (mkKY5 S wn kc P KS T (mkH5 ML sp sc sn fr mw) now next_id id_known hsn).
      unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
      subst D F0.
      cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second y_S y_w y_kc y_P y_KS y_T y_H y_now
           y_next_id y_id_known y_hsn h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn].
      entailer!.
    + exfalso. auto.
  - (* a held node k: k->held--, wg_noise_keypair_put(k->kp, unref), m_put(k, unref) *)
    assert (EM: afind ML k = Some M) by (apply hk5o6_in_afind; auto).
    set (M1 := m5_set_held M (Int64.sub (m5_held M) Int64.one)).
    destruct (hk5o6_focus ML k M M1 EM eq_refl eq_refl) as (nx & Rst & E1 & E2).
    rewrite E1. Intros.
    assert_PROP (isptr k) as Hkp by entailer!.
    forward_if (hkp5_Icont x25519 F0 V steps FR i).
    { subst k. contradiction. }
    assert (HkKS: In (m5_kp M) (map fst KS)).
    { destruct (proj1 MF _ _ _ _ _ _ _ C0) as (_ & _ & Hnk & _). destruct (Hnk k M EM) as (K & EK & _).
      eapply hk5o6_afind_in; eauto. }
    assert_PROP (isptr (m5_kp M)) as Hkpp.
    { sep_apply (hk5o6_kp_ptr KS (m5_kp M) HkKS). entailer!. }
    forward.
    forward.
    forward.
    change (fst (hk5_mk_val M nx)) with (m5_kp M).
    replace_SEP 1 (data_at Ews t_mk5 (hk5_mk_val M1 nx) k).
    { entailer!. }
    gather_SEP 1 2. rewrite <- E2.
    forward_call (gv, S, wn, KS, T, m5_kp M, Z.odd u, Tsh, p, P, Tsh, w, D, Tsh).
    { apply prop_right. destruct (m5_kp M); try contradiction. destruct (Z.odd u); reflexivity. }
    rewrite <- (hk5o6_head_aupd ML k M1).
    forward_call (gv, aupd ML k M1, fr, mw, k, Z.odd u).
    { rewrite hk5o6_map_fst_aupd. split; [right; eapply hk5o6_afind_in; eauto | exact ND0]. }
    destruct (hk5_put k (Z.odd u) (aupd ML k M1) fr mw) as [[ML' fr'] mw'] eqn:EP.
    cbn [fst snd].
    destruct (hk5o6_model MF p (v_OD V) (v_OH V) ML sp sc sn fr mw P KS T S (v_w0 V) wn k M (Z.odd u) ML' fr' mw'
                Hrel Hwarn EM HM EP) as (_ & _ & Rel' & Warn' & Hent & Hvin & Acc).
    set (W' := kp_put (m5_kp M) (Z.odd u) {| kw_KS := KS; kw_T := T; kw_S := S |}) in *.
    set (Y' := mkKY5 (kw_S W') (kp_put_warn (m5_kp M) KS wn) kc P (kw_KS W') (kw_T W')
                 (mkH5 ML' sp sc sn fr' mw') now next_id id_known hsn).
    assert (Hinv': hkp5_inv F0 V Y').
    { destruct (Acc _ _ Hfr Hal) as [A1 A2].
      destruct Hhsm as ((Hh1 & Hh2 & Hh3) & Hpk).
      unfold hkp5_inv, hk5_hsm_ok, Y'. cbn [y_S y_w y_kc y_P y_KS y_T y_H y_now y_next_id y_id_known y_hsn h5_ML
        h5_frees h5_warn f_p f_w].
      rewrite <- Hent in Hh1. rewrite <- Hvin in Hh2.
      exact (conj Rel' (conj Warn' (conj Hdev (conj Hsid (conj Hpr (conj A1 (conj A2 (conj Hid (conj Hnow
        (conj (conj Hh1 (conj Hh2 Hh3)) Hpk)))))))))). }
    change (itable Tsh (d_itab D) (kw_T W')) with (itable Tsh t (kw_T W')).
    unfold hkp5_Icont, hkp5_St. Exists Y'.
    unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
    subst Y'. subst D F0.
    cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second y_S y_w y_kc y_P y_KS y_T y_H y_now
         y_next_id y_id_known y_hsn h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn].
    entailer!.
Qed.
