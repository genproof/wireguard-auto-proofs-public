(* law keypairs, segment Op0: the pure live fact: begin_session_model in
   the live case against the harness's live branch (hkp5_o0_live_fact). "Op0". *)
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
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_defs.

#[local] Existing Instance W_keypairs.
Local Open Scope Z_scope.

Lemma hkp5_o0lv_cnt_cons x R m : hk5_cnt (x :: R) m = (if eq_dec m x then 1 else 0) + hk5_cnt R m.
Proof. unfold hk5_cnt, hk5_eqb. simpl. destruct (EqDec_val m x); rewrite ?Zlength_cons; lia. Qed.

Lemma hkp5_o0lv_cnt_app l1 l2 m : hk5_cnt (l1 ++ l2) m = hk5_cnt l1 m + hk5_cnt l2 m.
Proof. unfold hk5_cnt. rewrite filter_app, Zlength_app. reflexivity. Qed.

Lemma hkp5_o0lv_cnt_nonneg R m : 0 <= hk5_cnt R m.
Proof. apply Zlength_nonneg. Qed.

Lemma hkp5_o0lv_cnt_remove1 s R m : In s R ->
  hk5_cnt R m = hk5_cnt (hk5_remove1 s R) m + (if eq_dec m s then 1 else 0).
Proof.
  induction R as [|x R IH]; simpl; intros I; [contradiction|].
  rewrite !hkp5_o0lv_cnt_cons. unfold eq_dec in *.
  destruct (EqDec_val x s) as [E|N].
  - subst x. lia.
  - destruct I as [E|I]; [congruence|]. rewrite hkp5_o0lv_cnt_cons, (IH I). unfold eq_dec in *. lia.
Qed.

Lemma hkp5_o0lv_cnt_In R m : 0 < hk5_cnt R m <-> In m R.
Proof.
  induction R as [|x R IH]; [unfold hk5_cnt; simpl; rewrite Zlength_nil; split; [lia | contradiction] |].
  rewrite hkp5_o0lv_cnt_cons. simpl. pose proof (hkp5_o0lv_cnt_nonneg R m). unfold eq_dec in *.
  destruct (EqDec_val m x) as [E|N]; split; intros Hm.
  - left; congruence.
  - lia.
  - right; apply IH; lia.
  - destruct Hm as [E|I]; [congruence | apply IH in I; lia].
Qed.

Lemma hkp5_o0lv_vremove_in a L x : In x (vremove a L) <-> In x L /\ x <> a.
Proof.
  induction L as [|y L IH]; simpl; [tauto|]. unfold eq_dec in *.
  destruct (EqDec_val y a) as [E|N]; simpl; rewrite IH; split.
  - intros [I Nx]. auto.
  - intros [[<-|I] Nx]; [congruence | auto].
  - intros [<-|[I Nx]]; auto.
  - intros [[<-|I] Nx]; auto.
Qed.

Lemma hkp5_o0lv_vremove_nodup a L : NoDup L -> NoDup (vremove a L).
Proof.
  induction 1 as [|x L Nx ND IH]; simpl; [constructor|]. unfold eq_dec in *.
  destruct (EqDec_val x a); [auto|]. constructor; auto. rewrite hkp5_o0lv_vremove_in. tauto.
Qed.

Lemma hkp5_o0lv_afind_adel {A: Type} (l: list (val * A)) s m : m <> s -> afind (adel l s) m = afind l m.
Proof.
  intros N. induction l as [|[x w] l IH]; simpl; [reflexivity|]. unfold eq_dec in *.
  destruct (EqDec_val x s) as [<-|Nx]; simpl.
  - destruct (EqDec_val x m); [congruence | reflexivity].
  - destruct (EqDec_val x m); [reflexivity | exact IH].
Qed.

Lemma hkp5_o0lv_afind_aupd {A: Type} (l: list (val * A)) s v m : m <> s -> afind (aupd l s v) m = afind l m.
Proof.
  intros N. induction l as [|[x w] l IH]; simpl; [reflexivity|]. unfold eq_dec in *.
  destruct (EqDec_val x s) as [<-|Nx]; simpl.
  - destruct (EqDec_val x m); [congruence | reflexivity].
  - destruct (EqDec_val x m); [reflexivity | exact IH].
Qed.

Lemma hkp5_o0lv_acc S fr n S' fr' n' f0 a0 :
  Int64.sub (s_frees S) f0 = fr -> Int64.sub (s_allocs S) a0 = Int64.add fr (Int64.repr n) ->
  ((S' = S /\ fr' = fr /\ n' = n) \/ (S' = shim_free S /\ fr' = Int64.add fr Int64.one /\ n' = n - 1)) ->
  Int64.sub (s_frees S') f0 = fr' /\ Int64.sub (s_allocs S') a0 = Int64.add fr' (Int64.repr n').
Proof.
  intros E1 E2 [(->&->&->)|(->&->&->)]; [auto|]. cbn [s_frees s_allocs shim_free]. split.
  - rewrite Int64.sub_add_l, E1. reflexivity.
  - rewrite E2, Int64.add_assoc. f_equal. unfold Int64.one. rewrite add64_repr. f_equal. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* Lists of addresses: vin, vreplace                                        *)
(* ---------------------------------------------------------------------- *)

Lemma hkp5_o0lv_vin_true a L : vin a L = true <-> In a L.
Proof. unfold vin. destruct (in_dec eq_dec a L); split; intros; auto; discriminate. Qed.

Lemma hkp5_o0lv_vin_false a L : vin a L = false <-> ~ In a L.
Proof. unfold vin. destruct (in_dec eq_dec a L); split; intros; auto; try discriminate; contradiction. Qed.

Lemma hkp5_o0lv_vin_ext a L L' : (In a L <-> In a L') -> vin a L = vin a L'.
Proof.
  intros E. unfold vin. destruct (in_dec eq_dec a L), (in_dec eq_dec a L'); auto; exfalso; tauto.
Qed.

Lemma hkp5_o0lv_vin_vremove a c L : a <> c -> vin a (vremove c L) = vin a L.
Proof. intros N. apply hkp5_o0lv_vin_ext. rewrite hkp5_o0lv_vremove_in. tauto. Qed.

Lemma hkp5_o0lv_vreplace_in a b L x : In x (vreplace a b L) -> x = b \/ In x L.
Proof.
  induction L as [|y L IH]; simpl; [tauto|]. unfold eq_dec in *.
  destruct (EqDec_val y a); simpl; intros [<-|I]; auto. destruct (IH I); auto.
Qed.

Lemma hkp5_o0lv_vreplace_in2 a b L x : In x L -> x <> a -> In x (vreplace a b L).
Proof.
  induction L as [|y L IH]; simpl; [tauto|]. unfold eq_dec in *.
  destruct (EqDec_val y a) as [<-|N]; simpl; intros [<-|I] Nx; auto; congruence.
Qed.

Lemma hkp5_o0lv_vreplace_hit a b L : In a L -> In b (vreplace a b L).
Proof.
  induction L as [|y L IH]; simpl; [tauto|]. unfold eq_dec in *.
  destruct (EqDec_val y a); simpl; [auto|]. intros [E|I]; [congruence | auto].
Qed.

Lemma hkp5_o0lv_vreplace_nodup a b L : NoDup L -> ~ In b L -> NoDup (vreplace a b L).
Proof.
  induction 1 as [|y L Ny ND IH]; simpl; intros Nb; [constructor|]. unfold eq_dec in *.
  destruct (EqDec_val y a).
  - constructor; [intro I; apply Nb; right; exact I | exact ND].
  - constructor.
    + intro I. apply hkp5_o0lv_vreplace_in in I as [E|I]; [apply Nb; left; congruence | contradiction].
    + apply IH. intro I. apply Nb. right. exact I.
Qed.

Lemma hkp5_o0lv_vreplace_gone a b L : NoDup L -> a <> b -> ~ In a (vreplace a b L).
Proof.
  induction 1 as [|y L Ny ND IH]; simpl; intros Nab; [tauto|]. unfold eq_dec in *.
  destruct (EqDec_val y a) as [<-|N]; simpl.
  - intros [E|I]; [congruence | contradiction].
  - intros [E|I]; [congruence | exact (IH Nab I)].
Qed.

Lemma hkp5_o0lv_vin_vreplace a b x L : x <> a -> x <> b -> vin x (vreplace a b L) = vin x L.
Proof.
  intros N1 N2. apply hkp5_o0lv_vin_ext. split.
  - intros I. apply hkp5_o0lv_vreplace_in in I as [E|I]; [congruence | exact I].
  - intros I. apply hkp5_o0lv_vreplace_in2; auto.
Qed.

Lemma hkp5_o0lv_vremove_vreplace c a b L : c <> a -> c <> b ->
  vremove c (vreplace a b L) = vreplace a b (vremove c L).
Proof.
  intros Na Nb. induction L as [|y L IH]; simpl; [reflexivity|]. unfold eq_dec in *.
  destruct (EqDec_val y a) as [<-|N1]; simpl.
  - destruct (EqDec_val b c); [congruence|]. destruct (EqDec_val y c); [congruence|]. simpl.
    destruct (EqDec_val y y); [reflexivity | congruence].
  - destruct (EqDec_val y c); simpl; [exact IH|]. destruct (EqDec_val y a); [contradiction|]. rewrite IH. reflexivity.
Qed.

Lemma hkp5_o0lv_map_vreplace {B: Type} (f g: val -> B) a b L : NoDup L -> f b = g a ->
  (forall x, In x L -> x <> a -> f x = g x) -> map f (vreplace a b L) = map g L.
Proof.
  induction 1 as [|y L Ny ND IH]; simpl; intros Eab Ex; [reflexivity|]. unfold eq_dec in *.
  destruct (EqDec_val y a) as [<-|N]; simpl.
  - f_equal; [exact Eab|]. apply map_ext_in. intros x I. apply Ex; [right; exact I | congruence].
  - f_equal; [apply Ex; [left; reflexivity | exact N]|]. apply IH; [exact Eab|]. intros x I Nx. apply Ex; auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* Pools: sfind, sdel, supd                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma hkp5_o0lv_sfind_sdel {A: Type} (D: list (val * share * A)) a x : x <> a -> sfind (sdel D a) x = sfind D x.
Proof.
  intros N. induction D as [|[[y sh] e] D IH]; simpl; [reflexivity|]. unfold eq_dec in *.
  destruct (EqDec_val y a) as [<-|Ny]; simpl.
  - destruct (EqDec_val y x); [congruence | reflexivity].
  - destruct (EqDec_val y x); [reflexivity | exact IH].
Qed.

Lemma hkp5_o0lv_sfind_supd {A: Type} (D: list (val * share * A)) a v x : x <> a -> sfind (supd D a v) x = sfind D x.
Proof.
  intros N. induction D as [|[[y sh] e] D IH]; simpl; [reflexivity|]. unfold eq_dec in *.
  destruct (EqDec_val y a) as [<-|Ny]; simpl.
  - destruct (EqDec_val y x); [congruence | reflexivity].
  - destruct (EqDec_val y x); [reflexivity | exact IH].
Qed.

Lemma hkp5_o0lv_sdel_supd {A: Type} (D: list (val * share * A)) a b v : a <> b ->
  sdel (supd D b v) a = supd (sdel D a) b v.
Proof.
  intros N. induction D as [|[[y sh] e] D IH]; simpl; [reflexivity|]. unfold eq_dec in *.
  destruct (EqDec_val y b) as [<-|Nb]; simpl.
  - destruct (EqDec_val y a); [congruence|]. simpl. destruct (EqDec_val y y); [reflexivity | congruence].
  - destruct (EqDec_val y a); [reflexivity|]. simpl. destruct (EqDec_val y b); [contradiction|]. rewrite IH. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* t_replace of the handshake's entry commutes with the puts of the other   *)
(* keypairs                                                                 *)
(* ---------------------------------------------------------------------- *)

Definition hkp5_o0lv_rp (hs kp: val) (T: tstate) : tstate := snd (t_replace T hs kp).

Lemma hkp5_o0lv_rp_remove hs kp T a : a <> hs -> a <> kp ->
  hkp5_o0lv_rp hs kp (t_remove T a) = t_remove (hkp5_o0lv_rp hs kp T) a.
Proof.
  intros N1 N2. destruct T as [D L]. unfold hkp5_o0lv_rp, t_replace, t_remove. cbn [t_L t_D].
  rewrite (hkp5_o0lv_vin_vremove hs a L) by congruence.
  destruct (vin hs L); cbn [snd t_D t_L]; [|reflexivity].
  unfold t_set_index, t_entry, t_upd. cbn [t_D t_L].
  rewrite hkp5_o0lv_vremove_vreplace by auto.
  destruct (sfind D kp) as [[? ?]|]; reflexivity.
Qed.

Lemma hkp5_o0lv_rp_free hs kp T a : a <> hs -> a <> kp ->
  hkp5_o0lv_rp hs kp (t_free T a) = t_free (hkp5_o0lv_rp hs kp T) a.
Proof.
  intros N1 N2. destruct T as [D L]. unfold hkp5_o0lv_rp, t_replace, t_free. cbn [t_L t_D].
  rewrite (hkp5_o0lv_vin_vremove hs a L) by congruence.
  destruct (vin hs L); cbn [snd t_D t_L]; [|reflexivity].
  unfold t_set_index, t_entry, t_upd. cbn [t_D t_L].
  rewrite hkp5_o0lv_vremove_vreplace by auto.
  rewrite !hkp5_o0lv_sfind_sdel by congruence.
  destruct (sfind D kp) as [[? ?]|]; cbn [t_D]; [|reflexivity].
  rewrite hkp5_o0lv_sdel_supd by auto. reflexivity.
Qed.

Lemma hkp5_o0lv_put_rp hs kp c u KS T S : (c <> nullval -> c <> hs /\ c <> kp) ->
  kp_put c u (mkKW KS (hkp5_o0lv_rp hs kp T) S) =
  mkKW (kw_KS (kp_put c u (mkKW KS T S))) (hkp5_o0lv_rp hs kp (kw_T (kp_put c u (mkKW KS T S))))
       (kw_S (kp_put c u (mkKW KS T S))).
Proof.
  intros Hc. unfold kp_put. cbn [kw_KS kw_T kw_S].
  destruct (eq_dec c nullval) as [|Nc]; [reflexivity|]. destruct (Hc Nc) as [N1 N2].
  destruct (afind KS c) as [K|]; [|reflexivity].
  destruct u, (Int.eq _ _); cbn [kw_KS kw_T kw_S];
    rewrite ?hkp5_o0lv_rp_free, ?hkp5_o0lv_rp_remove by auto; reflexivity.
Qed.

(* the kernel's other effects of a put on another keypair *)
Lemma hkp5_o0lv_put_afind c u W x : x <> c -> afind (kw_KS (kp_put c u W)) x = afind (kw_KS W) x.
Proof.
  intros N. destruct W as [KS T S]. unfold kp_put. cbn [kw_KS kw_T kw_S].
  destruct (eq_dec c nullval); [reflexivity|]. destruct (afind KS c); [|reflexivity].
  destruct (Int.eq _ _); cbn [kw_KS]; [apply hkp5_o0lv_afind_adel | apply hkp5_o0lv_afind_aupd]; auto.
Qed.

Lemma hkp5_o0lv_put_sfind c u W x : x <> c -> sfind (t_D (kw_T (kp_put c u W))) x = sfind (t_D (kw_T W)) x.
Proof.
  intros N. destruct W as [KS T S]. unfold kp_put. cbn [kw_KS kw_T kw_S].
  destruct (eq_dec c nullval); [reflexivity|]. destruct (afind KS c); [|reflexivity].
  destruct u, (Int.eq _ _); cbn [kw_T t_free t_remove t_D]; rewrite ?hkp5_o0lv_sfind_sdel by auto; reflexivity.
Qed.

Lemma hkp5_o0lv_put_vin c u W x : x <> c -> vin x (t_L (kw_T (kp_put c u W))) = vin x (t_L (kw_T W)).
Proof.
  intros N. destruct W as [KS T S]. unfold kp_put. cbn [kw_KS kw_T kw_S].
  destruct (eq_dec c nullval); [reflexivity|]. destruct (afind KS c); [|reflexivity].
  destruct u, (Int.eq _ _); cbn [kw_T t_free t_remove t_L]; rewrite ?hkp5_o0lv_vin_vremove by auto; reflexivity.
Qed.

Lemma hkp5_o0lv_put_S c u W :
  s_allocs (kw_S (kp_put c u W)) = s_allocs (kw_S W) /\ s_fails (kw_S (kp_put c u W)) = s_fails (kw_S W).
Proof.
  destruct W as [KS T S]. unfold kp_put. cbn [kw_KS kw_T kw_S].
  destruct (eq_dec c nullval); [auto|]. destruct (afind KS c); [|auto].
  destruct (Int.eq _ _); cbn [kw_S]; auto.
Qed.

Lemma hkp5_o0lv_rp_fst T hs kp : fst (t_replace T hs kp) = vin hs (t_L T).
Proof. unfold t_replace. destruct (vin hs (t_L T)); reflexivity. Qed.

Lemma hkp5_o0lv_rp_sfind hs kp T x : x <> kp -> sfind (t_D (hkp5_o0lv_rp hs kp T)) x = sfind (t_D T) x.
Proof.
  intros N. destruct T as [D L]. unfold hkp5_o0lv_rp, t_replace. cbn [t_L t_D].
  destruct (vin hs L); cbn [snd t_D]; [|reflexivity].
  unfold t_set_index, t_entry, t_upd. cbn [t_D t_L].
  destruct (sfind D kp) as [[? ?]|]; cbn [t_D]; [apply hkp5_o0lv_sfind_supd; auto | reflexivity].
Qed.

Lemma hkp5_o0lv_rp_vin hs kp T : NoDup (t_L T) -> hs <> kp -> vin hs (t_L (hkp5_o0lv_rp hs kp T)) = false.
Proof.
  intros ND N. destruct T as [D L]. unfold hkp5_o0lv_rp, t_replace. cbn [t_L t_D] in *.
  destruct (vin hs L) eqn:B; cbn [snd t_L]; [|exact B].
  apply hkp5_o0lv_vin_false. apply hkp5_o0lv_vreplace_gone; auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* The new keypair's entry, after the replace                               *)
(* ---------------------------------------------------------------------- *)

Definition hkp5_o0lv_T1 (T: tstate) (hs kp p: val) (E: entry) : tstate :=
  mkT ((kp, Ews, mkEntry p IDX_KEYPAIR (if vin hs (t_L T) then e_index E else Int.zero)) :: t_D T)
      (if vin hs (t_L T) then vreplace hs kp (t_L T) else t_L T).

Lemma hkp5_o0lv_T1_eq T hs kp p E : kp <> hs -> t_entry T hs = Some E ->
  hkp5_o0lv_rp hs kp (t_add T kp Ews (mkEntry p IDX_KEYPAIR Int.zero)) = hkp5_o0lv_T1 T hs kp p E.
Proof.
  intros N HE. destruct T as [D L]. unfold hkp5_o0lv_rp, hkp5_o0lv_T1, t_replace, t_add. cbn [t_L t_D].
  destruct (vin hs L); cbn [snd]; [|reflexivity].
  unfold t_entry in HE. cbn [t_D] in HE.
  unfold t_set_index, t_entry, t_upd. cbn [t_D t_L sfind supd].
  rewrite !(if_true (kp = kp)) by reflexivity. rewrite !(if_false (kp = hs)) by exact N.
  destruct (sfind D hs) as [[sh E']|]; inversion HE; subst. reflexivity.
Qed.

Lemma hkp5_o0lv_forall2_in {A B: Type} (Pr Q: A -> B -> Prop) l1 l2 :
  Forall2 Pr l1 l2 -> (forall x y, In y l2 -> Pr x y -> Q x y) -> Forall2 Q l1 l2.
Proof.
  induction 1 as [|x y l1 l2 Hxy F IH]; intros Hq; constructor.
  - apply Hq; [left; reflexivity | exact Hxy].
  - apply IH. intros a b I. apply Hq. right. exact I.
Qed.

(* ---------------------------------------------------------------------- *)
(* begin_session's result in the live case, and one put on both sides      *)
(* ---------------------------------------------------------------------- *)

(* the kernel's world after the replace *)
Definition hkp5_o0lv_fin (W: kworld) (hs kp: val) : kworld :=
  mkKW (kw_KS W) (hkp5_o0lv_rp hs kp (kw_T W)) (kw_S W).

(* add_new_keypair_model on the zeroed peer and the world with the new keypair *)
Definition hkp5_o0lv_PW (P: peer) (Hz: handshake) (kp: val) (init: bool) (K: keypair) (KS: list (val * keypair))
  (T: tstate) (E: entry) (S: shim) : peer * kworld :=
  add_new_keypair_model (p_set_hs P Hz) kp init
    (mkKW ((kp, K) :: KS) (t_add T kp Ews (mkEntry (e_peer E) IDX_KEYPAIR Int.zero)) (shim_alloc_ok S)).

Lemma hkp5_o0lv_bs P p kp kc KS T S E :
  orb (Int.eq (hs_state (p_hs P)) HS_CREATED_RESPONSE) (Int.eq (hs_state (p_hs P)) HS_CONSUMED_RESPONSE) = true ->
  p_dead P = false -> kp <> nullval -> t_entry T (hs_addr p) = Some E ->
  P4.bs_res P p kp kc KS T S =
  let K := kp_new (p_hs P) (Int64.add kc Int64.one) (s_boot S) in
  let PW := hkp5_o0lv_PW P (hs_zero (p_hs P)) kp (kp_init K) K KS T E S in
  (vin (hs_addr p) (t_L (kw_T (snd PW))), fst PW, hkp5_o0lv_fin (snd PW) (hs_addr p) kp, Int64.add kc Int64.one).
Proof.
  intros Hst Hd Hkp HE. unfold P4.bs_res, begin_session_model, hkp5_o0lv_PW, hkp5_o0lv_fin. cbv zeta. rewrite Hst.
  cbn [negb]. rewrite if_false by exact Hkp. rewrite Hd. unfold e_peer_of_hs. cbn [kw_T kw_KS kw_S]. rewrite HE.
  destruct (add_new_keypair_model _ _ _ _) as [P2 W2]. cbn [fst snd].
  unfold hkp5_o0lv_rp, t_replace. destruct (vin _ _); reflexivity.
Qed.

Lemma hkp5_o0lv_put_rp' c u KS T S hs kp : (c <> nullval -> c <> hs /\ c <> kp) ->
  kp_put c u (mkKW KS (hkp5_o0lv_rp hs kp T) S) = hkp5_o0lv_fin (kp_put c u (mkKW KS T S)) hs kp.
Proof. intros Hc. rewrite hkp5_o0lv_put_rp by exact Hc. reflexivity. Qed.

Lemma hkp5_o0lv_put2_rp c1 c2 KS T S hs kp :
  (c1 <> nullval -> c1 <> hs /\ c1 <> kp) -> (c2 <> nullval -> c2 <> hs /\ c2 <> kp) ->
  kp_put c2 true (kp_put c1 true (mkKW KS (hkp5_o0lv_rp hs kp T) S)) =
  hkp5_o0lv_fin (kp_put c2 true (kp_put c1 true (mkKW KS T S))) hs kp.
Proof.
  intros H1 H2. rewrite hkp5_o0lv_put_rp by exact H1.
  destruct (kp_put c1 true (mkKW KS T S)) as [KS1 T1 S1]. cbn [kw_KS kw_T kw_S].
  apply hkp5_o0lv_put_rp'. exact H2.
Qed.

Lemma hkp5_o0lv_put_null u W : kp_put nullval u W = W.
Proof. unfold kp_put. rewrite if_true by reflexivity. reflexivity. Qed.

(* what the kernel's puts of other keypairs keep *)
Definition hkp5_o0lv_KF (hs kp: val) (K: keypair) (sf: option (share * entry)) (a f: int64) (W: kworld) : Prop :=
  afind (kw_KS W) kp = Some K /\ sfind (t_D (kw_T W)) hs = sf /\ vin hs (t_L (kw_T W)) = false /\
  s_allocs (kw_S W) = a /\ s_fails (kw_S W) = f.

Lemma hkp5_o0lv_KF_put hs kp K sf a f c u W : (c <> nullval -> c <> hs /\ c <> kp) ->
  hkp5_o0lv_KF hs kp K sf a f W -> hkp5_o0lv_KF hs kp K sf a f (kp_put c u W).
Proof.
  intros Hc (F1&F2&F3&F4&F5). destruct (eq_dec c nullval) as [->|Nc].
  { rewrite hkp5_o0lv_put_null. exact (conj F1 (conj F2 (conj F3 (conj F4 F5)))). }
  destruct (Hc Nc) as [N1 N2]. destruct (hkp5_o0lv_put_S c u W) as [S1 S2].
  split; [|split; [|split; [|split]]].
  - rewrite hkp5_o0lv_put_afind by congruence. exact F1.
  - rewrite hkp5_o0lv_put_sfind by congruence. exact F2.
  - rewrite hkp5_o0lv_put_vin by congruence. exact F3.
  - rewrite S1. exact F4.
  - rewrite S2. exact F5.
Qed.

Lemma hkp5_o0lv_vin_put hs c u W : (c <> nullval -> c <> hs) ->
  vin hs (t_L (kw_T (kp_put c u W))) = vin hs (t_L (kw_T W)).
Proof.
  intros Hc. destruct (eq_dec c nullval) as [->|Nc]; [rewrite hkp5_o0lv_put_null; reflexivity|].
  apply hkp5_o0lv_put_vin. exact (fun E => Hc Nc (eq_sym E)).
Qed.

Lemma hkp5_o0lv_afind_In {A: Type} (l: list (val * A)) a v : afind l a = Some v -> In (a, v) l.
Proof.
  induction l as [|[x w] l IH]; simpl; [discriminate|]. unfold eq_dec in *.
  destruct (EqDec_val x a) as [<-|N]; [intros E; inversion E; left; reflexivity | intros E; right; apply IH; exact E].
Qed.

Lemma hkp5_o0lv_slot_cons k M ML m : m <> k -> hk5_slot_kp ((k, M) :: ML) m = hk5_slot_kp ML m.
Proof.
  intros N. unfold hk5_slot_kp. destruct (eq_dec m nullval); [reflexivity|]. cbn [afind].
  rewrite if_false by congruence. reflexivity.
Qed.

Lemma hkp5_o0lv_slot_new k M ML : k <> nullval -> hk5_slot_kp ((k, M) :: ML) k = m5_kp M.
Proof.
  intros N. unfold hk5_slot_kp. rewrite if_false by exact N. cbn [afind]. rewrite if_true by reflexivity.
  reflexivity.
Qed.

Lemma hkp5_o0lv_slot_null ML : hk5_slot_kp ML nullval = nullval.
Proof. unfold hk5_slot_kp. rewrite if_true by reflexivity. reflexivity. Qed.

Lemma hkp5_o0lv_nonnull3 a b c :
  (a <> nullval -> b <> nullval -> a <> b) -> (a <> nullval -> c <> nullval -> a <> c) ->
  (b <> nullval -> c <> nullval -> b <> c) -> NoDup (hk5_nonnull [a; b; c]).
Proof.
  intros Hab Hac Hbc. unfold hk5_nonnull, hk5_eqb. cbn [filter].
  destruct (eq_dec a nullval) as [Ea|Na], (eq_dec b nullval) as [Eb|Nb], (eq_dec c nullval) as [Ec|Nc];
    cbn [negb]; repeat constructor; cbn [In]; intuition.
Qed.

Lemma hkp5_o0lv_nd3 a b c : NoDup (hk5_nonnull [a; b; c]) ->
  (a <> nullval -> b <> nullval -> a <> b) /\ (a <> nullval -> c <> nullval -> a <> c) /\
  (b <> nullval -> c <> nullval -> b <> c).
Proof.
  unfold hk5_nonnull, hk5_eqb. cbn [filter].
  destruct (eq_dec a nullval) as [Ea|Na], (eq_dec b nullval) as [Eb|Nb], (eq_dec c nullval) as [Ec|Nc];
    cbn [negb]; intros ND; rewrite ?NoDup_cons_iff in ND; cbn [In] in ND;
    (split; [|split]); intros X Y Z; subst; try contradiction; intuition.
Qed.
Lemma hkp5_o0lv_or a b : (a <> nullval -> b <> nullval -> a <> b) -> (a = nullval \/ a <> b) /\ (b = nullval \/ b <> a).
Proof.
  intros D. destruct (eq_dec a nullval) as [Ea|Na]; destruct (eq_dec b nullval) as [Eb|Nb].
  - split; left; assumption.
  - split; [left; assumption | right; congruence].
  - split; [right; congruence | left; assumption].
  - split; right; intro E; [apply (D Na Nb E) | apply (D Na Nb (eq_sym E))].
Qed.

(* ---------------------------------------------------------------------- *)
(* v2: the harness's puts (hk5_put / hk5_hput) and one put on both sides    *)

(* ---------------------------------------------------------------------- *)

Lemma hkp5_o0lv_saddrs_in {A: Type} (D: list (val * share * A)) a sh e : In (a, sh, e) D -> In a (saddrs D).
Proof. intros I. unfold saddrs. apply (in_map (fun '(x, _, _) => x)) in I. exact I. Qed.

Lemma hkp5_o0lv_slot_put s u ML fr mw m : (m = nullval \/ m <> s) ->
  hk5_slot_kp (fst (fst (hk5_put s u ML fr mw))) m = hk5_slot_kp ML m.
Proof.
  intros Hm. unfold hk5_slot_kp. destruct (eq_dec m nullval); [reflexivity|].
  destruct Hm as [|Hm]; [contradiction|].
  unfold hk5_put. destruct (eq_dec s nullval); [reflexivity|]. destruct (afind ML s) as [M|]; [|reflexivity].
  cbv zeta. destruct (Int.eq (m5_refs M) REFCOUNT_SATURATED).
  - destruct u; cbn [fst]; [rewrite hkp5_o0lv_afind_aupd by auto|]; reflexivity.
  - destruct (Int.eq _ _); cbn [fst]; [rewrite hkp5_o0lv_afind_adel | rewrite hkp5_o0lv_afind_aupd]; auto.
Qed.

Lemma hkp5_o0lv_hput_ML s u H :
  h5_ML (hk5_hput s u H) = fst (fst (hk5_put s u (h5_ML H) (h5_frees H) (h5_warn H))).
Proof. unfold hk5_hput. destruct (hk5_put _ _ _ _ _) as [[? ?] ?]. reflexivity. Qed.

Lemma hkp5_o0lv_slot_hput s u H m : (m = nullval \/ m <> s) ->
  hk5_slot_kp (h5_ML (hk5_hput s u H)) m = hk5_slot_kp (h5_ML H) m.
Proof. intros Hm. rewrite hkp5_o0lv_hput_ML. apply hkp5_o0lv_slot_put. exact Hm. Qed.

Lemma hkp5_o0lv_step (FP: hk5_fact_put) (FPm: hk5_fact_perm) p OD OH l1 s l2 ML KS T S fr mw w0 w ML' fr' mw' :
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
    { intros m Nm. pose proof (hkp5_o0lv_cnt_remove1 s _ m Is) as Em.
      rewrite hkp5_o0lv_cnt_app, hkp5_o0lv_cnt_cons in Em. rewrite hkp5_o0lv_cnt_app, hkp5_o0lv_cnt_cons.
      unfold eq_dec in *. destruct (EqDec_val m nullval); [contradiction|]. destruct (EqDec_val m s); lia. }
    apply (FPm _ _ _ _ _ _ _ _ Ecnt); [| exact C'].
    pose proof C' as (_&_&_&_&_&CF&_). rewrite Forall_forall in CF |- *. intros x Ix.
    destruct (eq_dec x nullval) as [|Nx]; [left; auto|]. apply CF.
    apply hkp5_o0lv_cnt_In. rewrite Ecnt by auto. apply hkp5_o0lv_cnt_In. auto.
Qed.

(* one slot put on both sides, on the harness's whole state *)
Lemma hkp5_o0lv_chain (FP: hk5_fact_put) (FPm: hk5_fact_perm) p OD OH l1 s l2 H KS T S w0 w f0 a0 :
  hk5_core p OD OH (l1 ++ s :: l2) (h5_ML H) KS T -> hk5_warn_ok w0 (h5_warn H) w ->
  Int64.sub (s_frees S) f0 = h5_frees H ->
  Int64.sub (s_allocs S) a0 = Int64.add (h5_frees H) (Int64.repr (Zlength (h5_ML H))) ->
  hk5_core p OD OH (l1 ++ nullval :: l2) (h5_ML (hk5_hput s true H))
    (kw_KS (kp_put (hk5_slot_kp (h5_ML H) s) true (mkKW KS T S)))
    (kw_T (kp_put (hk5_slot_kp (h5_ML H) s) true (mkKW KS T S))) /\
  hk5_warn_ok w0 (h5_warn (hk5_hput s true H)) (kp_put_warn (hk5_slot_kp (h5_ML H) s) KS w) /\
  Int64.sub (s_frees (kw_S (kp_put (hk5_slot_kp (h5_ML H) s) true (mkKW KS T S)))) f0 = h5_frees (hk5_hput s true H) /\
  Int64.sub (s_allocs (kw_S (kp_put (hk5_slot_kp (h5_ML H) s) true (mkKW KS T S)))) a0 =
    Int64.add (h5_frees (hk5_hput s true H)) (Int64.repr (Zlength (h5_ML (hk5_hput s true H)))).
Proof.
  intros C Wk E1 E2. unfold hk5_hput.
  destruct (hk5_put s true (h5_ML H) (h5_frees H) (h5_warn H)) as [[ML' fr'] mw'] eqn:E.
  cbn [h5_ML h5_frees h5_warn].
  destruct (hkp5_o0lv_step FP FPm p OD OH l1 s l2 (h5_ML H) KS T S (h5_frees H) (h5_warn H) w0 w ML' fr' mw'
              C Wk E) as (C' & W' & A).
  split; [exact C'|]. split; [exact W'|].
  apply (hkp5_o0lv_acc S (h5_frees H) (Zlength (h5_ML H))); auto.
Qed.

Lemma hkp5_o0lv_put_KS c u KS T S T' S' :
  kw_KS (kp_put c u (mkKW KS T S)) = kw_KS (kp_put c u (mkKW KS T' S')).
Proof.
  unfold kp_put. cbn [kw_KS kw_T kw_S].
  destruct (eq_dec c nullval); [reflexivity|]. destruct (afind KS c); [|reflexivity].
  destruct (Int.eq _ _); reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* The new node and keypair on the replaced table                           *)
(* ---------------------------------------------------------------------- *)

Lemma hkp5_o0lv_core0 p OD OH R ML KS T E kp k M K :
  hk5_core p OD OH R ML KS T -> t_entry T (hs_addr p) = Some E ->
  kp <> nullval -> ~ In kp (saddrs (t_D T)) -> k <> nullval -> ~ In k (map fst ML) ->
  m5_kp M = kp -> m5_refs M = Int.one -> m5_held M = Int64.zero -> m5_hashed M = vin (hs_addr p) (t_L T) ->
  m5_index M = (if vin (hs_addr p) (t_L T) then e_index E else Int.zero) ->
  kp_refs K = Int.one ->
  kp_send K = mkSym (m5_send M) (m5_birth M) (m5_sv M) -> kp_recv K = mkSym (m5_recv M) (m5_birth M) (m5_rv M) ->
  kp_init K = m5_init M -> kp_rindex K = m5_rindex M -> kp_id K = m5_id M ->
  kp_scounter K = m5_scnt M -> kp_rcounter K = m5_rcnt M ->
  hk5_core p OD OH (k :: R) ((k, M) :: ML) ((kp, K) :: KS) (hkp5_o0lv_T1 T (hs_addr p) kp p E).
Proof.
  intros (C1&C2&C3&C4&C5&C6&C7&C8&C9) HE Hkp Hkp1 Hk Hk1 Mkp Mrefs Mheld Mh Mi Kr Ks Kv Ki Kri Kid Ksc Krc.
  destruct C9 as (P1&P2&P3&P4&[idx Hidx]&P6&P7&P8).
  pose proof P8 as (W1&W2&W3&W4).
  set (hs := hs_addr p) in *.
  assert (Hhs: In hs (saddrs (t_D T))) by (apply P1; left; reflexivity).
  assert (Nhk: hs <> kp) by (intro E1; apply Hkp1; rewrite <- E1; exact Hhs).
  assert (Nks: ~ In kp (map fst KS)) by (intro I; apply Hkp1; apply P1; right; left; exact I).
  assert (NkL: ~ In kp (t_L T)) by (intro I; apply Hkp1; apply W2; exact I).
  assert (Nod: ~ In kp (saddrs OD)) by (intro I; apply Hkp1; apply P1; right; right; exact I).
  assert (Sf: forall a, a <> kp -> sfind (t_D (hkp5_o0lv_T1 T hs kp p E)) a = sfind (t_D T) a).
  { intros a Na. unfold hkp5_o0lv_T1. cbn [t_D sfind]. rewrite if_false by congruence. reflexivity. }
  assert (Vf: forall a, a <> kp -> a <> hs -> vin a (t_L (hkp5_o0lv_T1 T hs kp p E)) = vin a (t_L T)).
  { intros a N1 N2. unfold hkp5_o0lv_T1. cbn [t_L]. destruct (vin hs (t_L T)); [|reflexivity].
    apply hkp5_o0lv_vin_vreplace; auto. }
  assert (Lf: incl (t_L (hkp5_o0lv_T1 T hs kp p E)) (kp :: t_L T)).
  { intros x I. unfold hkp5_o0lv_T1 in I. cbn [t_L] in I. destruct (vin hs (t_L T)); [|right; exact I].
    apply hkp5_o0lv_vreplace_in in I as [E1|I]; [left; congruence | right; exact I]. }
  assert (Nk: hk5_cnt R k = 0).
  { pose proof (hkp5_o0lv_cnt_nonneg R k). destruct (Z.eq_dec (hk5_cnt R k) 0) as [|N]; [assumption|].
    exfalso. assert (I: In k R) by (apply hkp5_o0lv_cnt_In; lia).
    rewrite Forall_forall in C6. destruct (C6 k I); contradiction. }
  unfold hk5_core, hk5_pool.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
          (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))))).
  - (* the aligned lists *)
    constructor.
    + split; [cbn [fst snd]; symmetry; exact Mkp|].
      cbn [snd]. unfold hk5_match. rewrite Mkp.
      refine (conj _ (conj _ (conj _ (conj Ks (conj Kv (conj Ki (conj Kri (conj Kid (conj Ksc Krc))))))))).
      * rewrite Kr, Mrefs. reflexivity.
      * unfold hkp5_o0lv_T1. cbn [t_D sfind]. rewrite if_true by reflexivity. rewrite Mi. reflexivity.
      * unfold hkp5_o0lv_T1. cbn [t_L]. rewrite Mh. destruct (vin hs (t_L T)) eqn:B.
        -- apply hkp5_o0lv_vin_true. apply hkp5_o0lv_vreplace_hit. apply hkp5_o0lv_vin_true. exact B.
        -- apply hkp5_o0lv_vin_false. exact NkL.
    + apply (hkp5_o0lv_forall2_in _ _ _ _ C1). intros x y Iy [Fy Mxy]. split; [exact Fy|].
      assert (Iy': In (m5_kp (snd x)) (map fst KS)) by (rewrite <- Fy; apply in_map; exact Iy).
      assert (N1: m5_kp (snd x) <> kp) by (intro E1; apply Nks; rewrite <- E1; exact Iy').
      assert (N2: m5_kp (snd x) <> hs) by (intro E1; apply P2; rewrite <- E1; exact Iy').
      destruct Mxy as (X1&X2&X3&X4). refine (conj X1 (conj _ (conj _ X4))).
      * rewrite Sf by exact N1. exact X2.
      * rewrite Vf by assumption. exact X3.
  - cbn [map fst]. constructor; assumption.
  - cbn [map fst]. intros [E1|I]; [congruence | contradiction].
  - cbn [map fst]. constructor; assumption.
  - cbn [map fst]. intros [E1|I]; [congruence | contradiction].
  - constructor; [right; left; reflexivity|]. rewrite Forall_forall in C6 |- *. intros x I.
    destruct (C6 x I) as [|I']; [left; assumption | right; right; exact I'].
  - constructor.
    + cbn [fst snd]. unfold hk5_count_ok. right.
      rewrite hkp5_o0lv_cnt_cons, if_true by reflexivity. rewrite Nk, Mrefs, Mheld.
      rewrite Int.unsigned_one, Int64.unsigned_zero. split; [reflexivity | rep_lia].
    + rewrite Forall_forall in C7 |- *. intros x I.
      assert (Nx: fst x <> k) by (intro E1; apply Hk1; rewrite <- E1; apply in_map; exact I).
      unfold hk5_count_ok. rewrite hkp5_o0lv_cnt_cons, if_false by exact Nx. apply C7. exact I.
  - constructor; [intros _; left; reflexivity|]. rewrite Forall_forall in C8 |- *. intros x I Hx.
    right. apply C8; assumption.
  - intros a. unfold hkp5_o0lv_T1. cbn [t_D saddrs map]. fold (saddrs (t_D T)). cbn [map fst In].
    rewrite (P1 a). split; intros [X|[X|X]]; auto; destruct X as [X|X]; auto.
  - cbn [map fst In]. intros [E1|I]; [apply Nhk; symmetry; exact E1 | apply P2; exact I].
  - exact P3.
  - cbn [map fst In]. intros a [<-|I]; [exact Nod | apply P4; exact I].
  - exists idx. rewrite Sf by exact Nhk. exact Hidx.
  - rewrite Forall_forall in P6 |- *. intros [[a sh] E0] I. specialize (P6 _ I). cbv beta iota in P6 |- *.
    pose proof (hkp5_o0lv_saddrs_in _ _ _ _ I) as Ia.
    assert (Na: a <> kp) by (intro E1; apply Nod; rewrite <- E1; exact Ia).
    assert (Nb: a <> hs) by (intro E1; apply P3; rewrite <- E1; exact Ia).
    destruct P6 as [X1 X2]. rewrite Sf by exact Na. rewrite Vf by assumption. auto.
  - unfold t_indices. unfold hkp5_o0lv_T1 at 2. cbn [t_L].
    assert (Ex: forall a, a <> kp ->
      (match t_entry (hkp5_o0lv_T1 T hs kp p E) a with Some E0 => e_index E0 | None => Int.zero end) =
      (match t_entry T a with Some E0 => e_index E0 | None => Int.zero end)).
    { intros a Na. unfold t_entry. rewrite Sf by exact Na. reflexivity. }
    destruct (vin hs (t_L T)) eqn:B.
    + rewrite (hkp5_o0lv_map_vreplace _ (fun a => match t_entry T a with Some E0 => e_index E0 | None => Int.zero end)
                 hs kp (t_L T) W1).
      * exact P7.
      * unfold t_entry, hkp5_o0lv_T1. cbn [t_D sfind]. rewrite if_true by reflexivity. rewrite B.
        unfold t_entry in HE. rewrite HE. reflexivity.
      * intros x I Nx. apply Ex. intro E1. apply NkL. rewrite <- E1. exact I.
    + erewrite map_ext_in; [exact P7|]. intros x I. apply Ex. intro E1. apply NkL. rewrite <- E1. exact I.
  - unfold itable_wf. split; [|split; [|split]].
    + unfold hkp5_o0lv_T1. cbn [t_L]. destruct (vin hs (t_L T)); [apply hkp5_o0lv_vreplace_nodup; assumption | exact W1].
    + intros x I. apply Lf in I. unfold hkp5_o0lv_T1. cbn [t_D saddrs map]. fold (saddrs (t_D T)).
      destruct I as [E1|I]; [left; exact E1 | right; apply W2; exact I].
    + unfold hkp5_o0lv_T1. cbn [t_D saddrs map]. fold (saddrs (t_D T)). constructor; assumption.
    + unfold hkp5_o0lv_T1. cbn [t_D]. constructor; [apply writable_Ews | exact W4].
Qed.

(* ---------------------------------------------------------------------- *)
(* The final relation                                                       *)
(* ---------------------------------------------------------------------- *)

Lemma hkp5_o0lv_fin_rel (FPm: hk5_fact_perm) p OD OH R H0 KS' T' sp' sc' sn' P2 :
  hk5_core p OD OH R (h5_ML H0) KS' T' ->
  (forall m, m <> nullval -> hk5_cnt R m = hk5_cnt [sp'; sc'; sn'] m) ->
  (forall x, In x [sp'; sc'; sn'] -> x = nullval \/ In x R) ->
  NoDup (hk5_nonnull [sp'; sc'; sn']) ->
  p_prev P2 = hk5_slot_kp (h5_ML H0) sp' -> p_cur P2 = hk5_slot_kp (h5_ML H0) sc' ->
  p_next P2 = hk5_slot_kp (h5_ML H0) sn' ->
  hk5_rel p OD OH (h5_set_slots H0 sp' sc' sn') P2 KS' T'.
Proof.
  intros C Ecnt Inc NDs E1 E2 E3. unfold hk5_rel, hk5_slots, h5_set_slots. cbn [h5_sp h5_sc h5_sn h5_ML].
  refine (conj _ (conj NDs (conj E1 (conj E2 E3)))).
  apply (FPm p OD OH R _ _ KS' T' Ecnt); [|exact C].
  pose proof C as (_&_&_&_&_&CF&_). rewrite Forall_forall in CF |- *. intros x Ix.
  destruct (Inc x Ix) as [E|I]; [left; exact E | apply CF; exact I].
Qed.

(* ---------------------------------------------------------------------- *)
(* The live branch for a role init (abstract new node M and keypair K)     *)
(* ---------------------------------------------------------------------- *)

Definition hkp5_o0lv_PWw (P: peer) (Hz: handshake) (kp: val) (init: bool) (K: keypair) (KS: list (val * keypair))
  (T: tstate) (E: entry) (S: shim) (w: list int64) : list int64 :=
  add_new_keypair_warn (p_set_hs P Hz) kp init
    (mkKW ((kp, K) :: KS) (t_add T kp Ews (mkEntry (e_peer E) IDX_KEYPAIR Int.zero)) (shim_alloc_ok S)) w.

Lemma hkp5_o0lv_gen (MF: hkp5_model_facts) p OD OH ML sp sc sn fr mw P KS T S kp k E K M (init: bool) Hz
    fr0 al0 w0 w :
  hk5_rel p OD OH (mkH5 ML sp sc sn fr mw) P KS T -> hk5_warn_ok w0 mw w ->
  kp <> nullval -> ~ In kp (saddrs (t_D T)) -> ~ In kp (map fst KS) ->
  k <> nullval -> ~ In k (map fst ML) -> t_entry T (hs_addr p) = Some E ->
  Int64.sub (s_frees S) fr0 = fr -> Int64.sub (s_allocs S) al0 = Int64.add fr (Int64.repr (Zlength ML)) ->
  m5_kp M = kp -> m5_refs M = Int.one -> m5_held M = Int64.zero -> m5_hashed M = vin (hs_addr p) (t_L T) ->
  m5_index M = (if vin (hs_addr p) (t_L T) then e_index E else Int.zero) ->
  kp_refs K = Int.one ->
  kp_send K = mkSym (m5_send M) (m5_birth M) (m5_sv M) -> kp_recv K = mkSym (m5_recv M) (m5_birth M) (m5_rv M) ->
  kp_init K = m5_init M -> kp_rindex K = m5_rindex M -> kp_id K = m5_id M ->
  kp_scounter K = m5_scnt M -> kp_rcounter K = m5_rcnt M -> m5_init M = init ->
  let PW := hkp5_o0lv_PW P Hz kp init K KS T E S in
  let W' := hkp5_o0lv_fin (snd PW) (hs_addr p) kp in
  let H' := hkp5_o0_hl k M (mkH5 ML sp sc sn fr mw) in
  vin (hs_addr p) (t_L (kw_T (snd PW))) = vin (hs_addr p) (t_L T) /\
  (if init then p_cur (fst PW) else p_next (fst PW)) = kp /\
  In (kp, K) (kw_KS W') /\
  t_entry (kw_T W') (hs_addr p) = Some E /\ vin (hs_addr p) (t_L (kw_T W')) = false /\
  s_allocs (kw_S W') = Int64.add (s_allocs S) Int64.one /\ s_fails (kw_S W') = s_fails S /\
  hk5_rel p OD OH H' (fst PW) (kw_KS W') (kw_T W') /\
  hk5_warn_ok w0 (h5_warn H') (hkp5_o0lv_PWw P Hz kp init K KS T E S w) /\
  Int64.sub (s_frees (kw_S W')) fr0 = h5_frees H' /\
  Int64.sub (s_allocs (kw_S W')) al0 = Int64.add (h5_frees H') (Int64.repr (Zlength (h5_ML H'))).
Proof.
  intros Hrel Wk Hkp Hkp1 Hkp2 Hk Hk1 HE Hfr Hal Mkp Mr Mhe Mh Mi Kr Ks Kv Ki Kri Kid Ksc Krc Minit.
  pose proof MF as (FPre & FS & FPm & FP & _ & _).
  destruct Hrel as (C0 & ND & Ep & Ec & En).
  cbn [hk5_slots h5_sp h5_sc h5_sn h5_ML] in C0, ND, Ep, Ec, En.
  pose proof (FPre _ _ _ _ _ _ _ C0) as (_ & _ & _ & Fslot & _).
  pose proof C0 as (_&NDML&NNML&_&_&CF&_&_&(P1&P2&P3&P4&[idx Hidx]&P6&P7&P8)).
  assert (HE': E = mkEntry p IDX_HANDSHAKE idx).
  { unfold t_entry in HE. rewrite Hidx in HE. inversion HE. reflexivity. }
  assert (Hhs: In (hs_addr p) (saddrs (t_D T))) by (apply P1; left; reflexivity).
  assert (Nhk: kp <> hs_addr p) by (intro E1; apply Hkp1; rewrite E1; exact Hhs).
  (* the slots *)
  assert (Sl: forall s, s = nullval \/ In s (map fst ML) ->
     s <> k /\ (hk5_slot_kp ML s <> nullval -> hk5_slot_kp ML s <> hs_addr p /\ hk5_slot_kp ML s <> kp) /\
     (s <> nullval -> hk5_slot_kp ML s <> nullval)).
  { intros s [Es|Is].
    - subst s. rewrite hkp5_o0lv_slot_null. split; [intro E1; apply Hk; symmetry; exact E1|].
      split; intros N; contradiction N; reflexivity.
    - destruct (Fslot s Is) as [N1 I1]. split; [intro E1; apply Hk1; rewrite <- E1; exact Is|].
      split; [intros _; split; intro E1; [apply P2 | apply Hkp2]; rewrite <- E1; exact I1 | intros _; exact N1]. }
  rewrite Forall_forall in CF.
  assert (Isp: sp = nullval \/ In sp (map fst ML)) by (apply CF; cbn; auto).
  assert (Isc: sc = nullval \/ In sc (map fst ML)) by (apply CF; cbn; auto).
  assert (Isn: sn = nullval \/ In sn (map fst ML)) by (apply CF; cbn; auto).
  destruct (Sl sp Isp) as (Nkp & Hcp & _). destruct (Sl sc Isc) as (Nkc & Hcc & _).
  destruct (Sl sn Isn) as (Nkn & Hcn & Hsn).
  rewrite <- Ep in Hcp. rewrite <- Ec in Hcc. rewrite <- En in Hcn, Hsn.
  destruct (hkp5_o0lv_nd3 _ _ _ ND) as (D12 & D13 & D23).
  (* the new node and keypair on the replaced table *)
  pose proof (hkp5_o0lv_core0 p OD OH _ ML KS T E kp k M K C0 HE Hkp Hkp1 Hk Hk1 Mkp Mr Mhe Mh Mi Kr Ks Kv Ki
                Kri Kid Ksc Krc) as C1.
  assert (Ep': e_peer E = p) by (rewrite HE'; reflexivity).
  assert (KF0: hkp5_o0lv_KF (hs_addr p) kp K (sfind (t_D T) (hs_addr p)) (Int64.add (s_allocs S) Int64.one)
                 (s_fails S) (mkKW ((kp, K) :: KS) (hkp5_o0lv_T1 T (hs_addr p) kp p E) (shim_alloc_ok S))).
  { split; [|split; [|split; [|split]]]; cbn [kw_KS kw_T kw_S].
    - cbn [afind]. rewrite if_true by reflexivity. reflexivity.
    - unfold hkp5_o0lv_T1. cbn [t_D sfind]. rewrite if_false by exact Nhk. reflexivity.
    - unfold hkp5_o0lv_T1. cbn [t_L]. destruct (vin (hs_addr p) (t_L T)) eqn:B; [|exact B].
      apply hkp5_o0lv_vin_false. apply hkp5_o0lv_vreplace_gone; [apply P8 | intro E1; apply Nhk; symmetry; exact E1].
    - reflexivity.
    - reflexivity. }
  rewrite <- (hkp5_o0lv_T1_eq T (hs_addr p) kp p E Nhk HE) in C1, KF0.
  assert (Hal1: Int64.sub (s_allocs (shim_alloc_ok S)) al0 = Int64.add fr (Int64.repr (Zlength ((k, M) :: ML)))).
  { cbn [s_allocs shim_alloc_ok]. rewrite Int64.sub_add_l, Hal, Zlength_cons, Int64.add_assoc. f_equal.
    unfold Int64.one. rewrite add64_repr. reflexivity. }
  assert (Hfr1: Int64.sub (s_frees (shim_alloc_ok S)) fr0 = fr) by exact Hfr.
  cbv zeta. unfold hkp5_o0lv_PW, hkp5_o0lv_PWw. rewrite Ep'.
  unfold hkp5_o0_hl, h5_set_ML. cbn [h5_ML h5_sp h5_sc h5_sn h5_frees h5_warn]. rewrite Minit.
  unfold add_new_keypair_model, add_new_keypair_warn. cbn [p_prev p_cur p_next p_set_hs kw_KS].
  set (T0 := t_add T kp Ews (mkEntry p IDX_KEYPAIR Int.zero)) in *.
  set (H1 := mkH5 ((k, M) :: ML) sp sc sn fr mw).
  destruct (hkp5_o0lv_or _ _ D12) as [O12 O21]. destruct (hkp5_o0lv_or _ _ D13) as [O13 O31].
  destruct (hkp5_o0lv_or _ _ D23) as [O23 O32].
  assert (Ok: forall s, s <> k -> k = nullval \/ k <> s) by (intros s N; right; intro E1; apply N; symmetry; exact E1).
  destruct init.
  - destruct (eq_dec sn nullval) as [Esn|Nsn].
    + (* initiator, no next keypair: one put (previous) *)
      assert (Enx: p_next P = nullval) by (rewrite En, Esn; apply hkp5_o0lv_slot_null).
      rewrite Enx. destruct (eq_dec nullval nullval) as [Enn|Cn]; [|exfalso; apply Cn; reflexivity].
      cbn [negb Coqlib.proj_sumbool fst snd].
      rewrite <- (hkp5_o0lv_put_rp' (p_prev P) true ((kp, K) :: KS) T0 (shim_alloc_ok S) (hs_addr p) kp Hcp).
      destruct (hkp5_o0lv_chain FP FPm p OD OH [k] sp [sc; sn] H1 ((kp, K) :: KS) (hkp5_o0lv_rp (hs_addr p) kp T0)
                  (shim_alloc_ok S) w0 w fr0 al0 C1 Wk Hfr1 Hal1) as (CH & WH & FH & AH).
      cbn [h5_ML H1] in CH, WH, FH, AH.
      rewrite (hkp5_o0lv_slot_cons k M ML sp Nkp), <- Ep in CH, WH, FH, AH.
      pose proof (hkp5_o0lv_KF_put _ _ _ _ _ _ (p_prev P) true _ Hcp KF0) as (F1&F2&F3&F4&F5).
      split; [rewrite hkp5_o0lv_vin_put by (intros Nc; apply (Hcp Nc)); reflexivity|].
      split; [reflexivity|].
      split; [apply hkp5_o0lv_afind_In; exact F1|].
      split; [unfold t_entry; rewrite F2; exact HE|].
      split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
      split; [|split; [exact WH | split; [exact FH | exact AH]]].
      apply (hkp5_o0lv_fin_rel FPm p OD OH _ _ _ _ sc k nullval _ CH).
      * intros m Nm. cbn [app]. rewrite Esn, !hkp5_o0lv_cnt_cons. destruct (eq_dec m nullval); [contradiction|]. ring.
      * intros x Ix. right. revert Ix. cbn [app In]. clear - x. tauto.
      * apply hkp5_o0lv_nonnull3; intros X Y; [exact Nkc | exfalso; apply Y; reflexivity | exfalso; apply Y; reflexivity].
      * cbn [p_prev p_set_slots]. rewrite hkp5_o0lv_slot_hput by exact O21. cbn [h5_ML H1].
        rewrite hkp5_o0lv_slot_cons by exact Nkc. exact Ec.
      * cbn [p_cur p_set_slots]. rewrite hkp5_o0lv_slot_hput by exact (Ok sp Nkp). cbn [h5_ML H1].
        rewrite hkp5_o0lv_slot_new by exact Hk. symmetry. exact Mkp.
      * cbn [p_next p_set_slots]. rewrite hkp5_o0lv_slot_null. reflexivity.
    + (* initiator, a next keypair waiting: puts of current, then previous *)
      assert (Nnx: p_next P <> nullval) by (apply Hsn; exact Nsn).
      destruct (eq_dec (p_next P) nullval) as [Cn|Nnx']; [exfalso; exact (Nnx Cn)|].
      cbn [negb Coqlib.proj_sumbool fst snd].
      rewrite <- (hkp5_o0lv_put2_rp (p_cur P) (p_prev P) ((kp, K) :: KS) T0 (shim_alloc_ok S) (hs_addr p) kp Hcc Hcp).
      rewrite (hkp5_o0lv_put_KS (p_cur P) true ((kp, K) :: KS) T0 (shim_alloc_ok S)
                 (hkp5_o0lv_rp (hs_addr p) kp T0) (shim_alloc_ok S)).
      split; [rewrite !hkp5_o0lv_vin_put by (intros Nc; first [apply (Hcp Nc) | apply (Hcc Nc)]); reflexivity|].
      split; [reflexivity|].
      pose proof (hkp5_o0lv_KF_put _ _ _ _ _ _ (p_prev P) true _ Hcp
                    (hkp5_o0lv_KF_put _ _ _ _ _ _ (p_cur P) true _ Hcc KF0)) as KF2.
      destruct (hkp5_o0lv_chain FP FPm p OD OH [k; sp] sc [sn] H1 ((kp, K) :: KS) (hkp5_o0lv_rp (hs_addr p) kp T0)
                  (shim_alloc_ok S) w0 w fr0 al0 C1 Wk Hfr1 Hal1) as (CH1 & WH1 & FH1 & AH1).
      cbn [h5_ML H1] in CH1, WH1, FH1, AH1.
      rewrite (hkp5_o0lv_slot_cons k M ML sc Nkc), <- Ec in CH1, WH1, FH1, AH1.
      set (H2 := hk5_hput sc true H1) in *.
      set (W1' := kp_put (p_cur P) true _) in *. clearbody W1'. destruct W1' as [KS1' T1' S1'].
      cbn [kw_KS kw_T kw_S] in CH1, WH1, FH1, AH1 |- *.
      destruct (hkp5_o0lv_chain FP FPm p OD OH [k] sp [nullval; sn] H2 KS1' T1' S1' w0 _ fr0 al0 CH1 WH1 FH1 AH1)
        as (CH & WH & FH & AH).
      assert (Esp: hk5_slot_kp (h5_ML H2) sp = p_prev P).
      { unfold H2. rewrite hkp5_o0lv_slot_hput by exact O12. cbn [h5_ML H1].
        rewrite hkp5_o0lv_slot_cons by exact Nkp. symmetry. exact Ep. }
      rewrite Esp in CH, WH, FH, AH.
      destruct KF2 as (F1&F2&F3&F4&F5).
      split; [apply hkp5_o0lv_afind_In; exact F1|].
      split; [unfold t_entry; rewrite F2; exact HE|].
      split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
      split; [|split; [exact WH | split; [exact FH | exact AH]]].
      apply (hkp5_o0lv_fin_rel FPm p OD OH _ _ _ _ sn k nullval _ CH).
      * intros m Nm. cbn [app]. rewrite !hkp5_o0lv_cnt_cons. destruct (eq_dec m nullval); [contradiction|]. ring.
      * intros x Ix. right. revert Ix. cbn [app In]. clear - x. tauto.
      * apply hkp5_o0lv_nonnull3; intros X Y; [exact Nkn | exfalso; apply Y; reflexivity | exfalso; apply Y; reflexivity].
      * cbn [p_prev p_set_slots]. rewrite hkp5_o0lv_slot_hput by exact O31. unfold H2.
        rewrite hkp5_o0lv_slot_hput by exact O32. cbn [h5_ML H1].
        rewrite hkp5_o0lv_slot_cons by exact Nkn. exact En.
      * cbn [p_cur p_set_slots]. rewrite hkp5_o0lv_slot_hput by exact (Ok sp Nkp). unfold H2.
        rewrite hkp5_o0lv_slot_hput by exact (Ok sc Nkc). cbn [h5_ML H1].
        rewrite hkp5_o0lv_slot_new by exact Hk. symmetry. exact Mkp.
      * cbn [p_next p_set_slots]. rewrite hkp5_o0lv_slot_null. reflexivity.
  - (* responder: puts of next, then previous *)
    cbn [fst snd].
    rewrite <- (hkp5_o0lv_put2_rp (p_next P) (p_prev P) ((kp, K) :: KS) T0 (shim_alloc_ok S) (hs_addr p) kp Hcn Hcp).
    rewrite (hkp5_o0lv_put_KS (p_next P) true ((kp, K) :: KS) T0 (shim_alloc_ok S)
               (hkp5_o0lv_rp (hs_addr p) kp T0) (shim_alloc_ok S)).
    split; [rewrite !hkp5_o0lv_vin_put by (intros Nc; first [apply (Hcp Nc) | apply (Hcn Nc)]); reflexivity|].
    split; [reflexivity|].
    pose proof (hkp5_o0lv_KF_put _ _ _ _ _ _ (p_prev P) true _ Hcp
                  (hkp5_o0lv_KF_put _ _ _ _ _ _ (p_next P) true _ Hcn KF0)) as KF2.
    destruct (hkp5_o0lv_chain FP FPm p OD OH [k; sp; sc] sn [] H1 ((kp, K) :: KS) (hkp5_o0lv_rp (hs_addr p) kp T0)
                (shim_alloc_ok S) w0 w fr0 al0 C1 Wk Hfr1 Hal1) as (CH1 & WH1 & FH1 & AH1).
    cbn [h5_ML H1] in CH1, WH1, FH1, AH1.
    rewrite (hkp5_o0lv_slot_cons k M ML sn Nkn), <- En in CH1, WH1, FH1, AH1.
    set (H2 := hk5_hput sn true H1) in *.
    set (W1' := kp_put (p_next P) true _) in *. clearbody W1'. destruct W1' as [KS1' T1' S1'].
    cbn [kw_KS kw_T kw_S] in CH1, WH1, FH1, AH1 |- *.
    destruct (hkp5_o0lv_chain FP FPm p OD OH [k] sp [sc; nullval] H2 KS1' T1' S1' w0 _ fr0 al0 CH1 WH1 FH1 AH1)
      as (CH & WH & FH & AH).
    assert (Esp: hk5_slot_kp (h5_ML H2) sp = p_prev P).
    { unfold H2. rewrite hkp5_o0lv_slot_hput by exact O13. cbn [h5_ML H1].
      rewrite hkp5_o0lv_slot_cons by exact Nkp. symmetry. exact Ep. }
    rewrite Esp in CH, WH, FH, AH.
    destruct KF2 as (F1&F2&F3&F4&F5).
    split; [apply hkp5_o0lv_afind_In; exact F1|].
    split; [unfold t_entry; rewrite F2; exact HE|].
    split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
    split; [|split; [exact WH | split; [exact FH | exact AH]]].
    apply (hkp5_o0lv_fin_rel FPm p OD OH _ _ _ _ nullval sc k _ CH).
    * intros m Nm. cbn [app]. rewrite !hkp5_o0lv_cnt_cons. destruct (eq_dec m nullval); [contradiction|]. ring.
    * intros x Ix. right. revert Ix. cbn [app In]. clear - x. tauto.
    * apply hkp5_o0lv_nonnull3; intros X Y; [exfalso; apply X; reflexivity | exfalso; apply X; reflexivity | exact Nkc].
    * cbn [p_prev p_set_slots]. rewrite hkp5_o0lv_slot_null. reflexivity.
    * cbn [p_cur p_set_slots]. rewrite hkp5_o0lv_slot_hput by exact O21. unfold H2.
      rewrite hkp5_o0lv_slot_hput by exact O23. cbn [h5_ML H1].
      rewrite hkp5_o0lv_slot_cons by exact Nkc. exact Ec.
    * cbn [p_next p_set_slots]. rewrite hkp5_o0lv_slot_hput by exact (Ok sp Nkp). unfold H2.
      rewrite hkp5_o0lv_slot_hput by exact (Ok sn Nkn). cbn [h5_ML H1].
      rewrite hkp5_o0lv_slot_new by exact Hk. symmetry. exact Mkp.
Qed.

Lemma hkp5_o0lv_anm P new init W :
  p_hs (fst (add_new_keypair_model P new init W)) = p_hs P /\
  p_device (fst (add_new_keypair_model P new init W)) = p_device P /\
  p_refs (fst (add_new_keypair_model P new init W)) = p_refs P /\
  hk5_prsnap_val (fst (add_new_keypair_model P new init W)) = hk5_prsnap_val P.
Proof.
  unfold add_new_keypair_model. destruct init; [destruct (eq_dec (p_next P) nullval)|];
    cbn [negb Coqlib.proj_sumbool fst p_hs p_device p_refs p_set_slots]; repeat split; reflexivity.
Qed.

Lemma hkp5_o0lv_bsw P p kp kc KS T S E w :
  orb (Int.eq (hs_state (p_hs P)) HS_CREATED_RESPONSE) (Int.eq (hs_state (p_hs P)) HS_CONSUMED_RESPONSE) = true ->
  p_dead P = false -> kp <> nullval -> t_entry T (hs_addr p) = Some E ->
  begin_session_warn P (hs_addr p) kp kc (mkKW KS T S) w =
  let K := kp_new (p_hs P) (Int64.add kc Int64.one) (s_boot S) in
  hkp5_o0lv_PWw P (hs_zero (p_hs P)) kp (kp_init K) K KS T E S w.
Proof.
  intros Hst Hd Hkp HE. unfold begin_session_warn, hkp5_o0lv_PWw. cbv zeta. rewrite Hst.
  cbn [negb]. rewrite if_false by exact Hkp. rewrite Hd. unfold e_peer_of_hs. cbn [kw_T kw_KS kw_S]. rewrite HE.
  reflexivity.
Qed.

Lemma hkp5_segOp0_live_ok : hkp5_model_facts -> hkp5_o0_live_fact.
Proof.
  intros MF p OD OH H P KS T S w0 w kc kp k E fr0 al0 Hrel Hw Hst Hdead Hok Hkp Hkp1 Hkp2 Hk Hk1 HE Hfr Hal.
  destruct H as [ML sp sc sn fr mw]. cbn [h5_ML h5_frees h5_warn] in Hk1, Hfr, Hal, Hw.
  rewrite (hkp5_o0lv_bs P p kp kc KS T S E Hst Hdead Hkp HE).
  rewrite (hkp5_o0lv_bsw P p kp kc KS T S E w Hst Hdead Hkp HE).
  change (kp_init (kp_new (p_hs P) (Int64.add kc Int64.one) (s_boot S)))
    with (Int.eq (hs_state (p_hs P)) HS_CONSUMED_RESPONSE).
  cbv zeta. cbn [fst snd].
  pose proof (hkp5_o0lv_gen MF p OD OH ML sp sc sn fr mw P KS T S kp k E
    (kp_new (p_hs P) (Int64.add kc Int64.one) (s_boot S))
    (hkp5_o0_mk kp (snap_of T (hs_addr p) E (p_hs P)) (Int.eq (hs_state (p_hs P)) HS_CONSUMED_RESPONSE)
       (kdf1 (hs_ck (p_hs P)) []) (kdf2 (hs_ck (p_hs P)) []) (s_boot S) (Int64.add kc Int64.one))
    (Int.eq (hs_state (p_hs P)) HS_CONSUMED_RESPONSE) (hs_zero (p_hs P)) fr0 al0 w0 w
    Hrel Hw Hkp Hkp1 Hkp2 Hk Hk1 HE Hfr Hal
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
    eq_refl) as G.
  cbv zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  unfold hkp5_o0lv_PW in *.
  destruct (hkp5_o0lv_anm (p_set_hs P (hs_zero (p_hs P))) kp (Int.eq (hs_state (p_hs P)) HS_CONSUMED_RESPONSE)
    (mkKW ((kp, kp_new (p_hs P) (Int64.add kc Int64.one) (s_boot S)) :: KS)
          (t_add T kp Ews (mkEntry (e_peer E) IDX_KEYPAIR Int.zero)) (shim_alloc_ok S))) as (A1 & A2 & A3 & A4).
  split; [exact G1|]. split; [reflexivity|]. split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
  split; [exact A4|]. split; [exact G2|]. split; [exact G3|].
  split; [exact G4|]. split; [exact G5|]. split; [exact G6|]. split; [exact G7|].
  split; [exact G8|]. split; [exact G9|]. split; [exact G10 | exact G11].
Qed.
