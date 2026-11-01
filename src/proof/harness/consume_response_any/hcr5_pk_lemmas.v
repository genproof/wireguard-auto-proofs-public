(* law consume_response_any, phase PK: the pure core of
   kents_add's effect on the states (the pool of the table after kents_T, the lists after kents_PS).
   Ported from consume_initiation_any's hci5_PK.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_cut.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_model.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_spec.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_defs.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* the table after kents_add: the kents' entries first, then T's           *)
(* ---------------------------------------------------------------------- *)

Definition hcr5_pk_te (d: kdraw) : val * share * entry :=
  (kd_addr d, Ews, mkEntry (kd_owner d) IDX_KEYPAIR (kd_idx d)).

Lemma hcr5_pk_tD_kents T KD : t_D (kents_T T KD) = map hcr5_pk_te KD ++ t_D T.
Proof.
  induction KD as [| d KD IH]; cbn [kents_T map app]; auto.
  unfold t_insert, t_set_index, t_entry, t_add, t_upd. simpl.
  destruct (EqDec_val (kd_addr d) (kd_addr d)); [| congruence]. simpl.
  destruct (EqDec_val (kd_addr d) (kd_addr d)); [| congruence]. simpl.
  rewrite IH. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* the peers after kents_add (kents_PS: only slots change)                 *)
(* ---------------------------------------------------------------------- *)

Definition hcr5_pk_pj (x: val * share * peer) :=
  match x with (a, sh, P) => (a, sh, p_device P, p_hs P, p_refs P, p_pknext P) end.

Lemma hcr5_pk_pj_kents fl PS KD : map hcr5_pk_pj (kents_PS fl PS KD) = map hcr5_pk_pj PS.
Proof.
  induction KD as [| d KD IH]; simpl; auto. destruct fl; auto.
  unfold fill_peers. rewrite map_map, <- IH. apply map_ext. intros [[x sh] P].
  destruct (eq_dec x (kd_owner d)); auto. unfold fill_slot.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

Lemma hcr5_pk_addrs_pj l :
  map peer_addr4 l = map (fun y => match y with (a, _, _, _, _, _) => a end) (map hcr5_pk_pj l).
Proof. rewrite map_map. apply map_ext. intros [[? ?] ?]. reflexivity. Qed.

Lemma hcr5_pk_addrs_kents fl PS KD : map peer_addr4 (kents_PS fl PS KD) = map peer_addr4 PS.
Proof. rewrite !hcr5_pk_addrs_pj, hcr5_pk_pj_kents. reflexivity. Qed.

Lemma hcr5_pk_Forall_pj (Q: val * share * peer -> Prop) l1 l2 :
  map hcr5_pk_pj l1 = map hcr5_pk_pj l2 -> (forall x y, hcr5_pk_pj x = hcr5_pk_pj y -> Q x -> Q y) ->
  Forall Q l1 -> Forall Q l2.
Proof.
  intros Hm HQ H. revert l2 Hm. induction H as [| x l1 Hx H IH]; intros [| y l2] Hm; simpl in Hm;
    try discriminate; constructor.
  - inv Hm. eapply HQ; eauto.
  - inv Hm. auto.
Qed.

Lemma hcr5_pk_chain_pj h l1 l2 :
  map hcr5_pk_pj l1 = map hcr5_pk_pj l2 -> pk_chain h l1 -> pk_chain h l2.
Proof.
  revert h l2. induction l1 as [| [[a sh] P] l1 IH]; intros h [| [[b sh'] P'] l2] Hm; simpl in *;
    try discriminate; auto.
  injection Hm as -> -> _ _ _ E4 Hm. intros [Hh Hc]. split; auto. rewrite <- E4. eapply IH; eauto.
Qed.

Lemma hcr5_pk_paddr_addr4 PS : map hcr5_paddr PS = map peer_addr4 PS.
Proof. apply map_ext. intros [[? ?] ?]. reflexivity. Qed.

Lemma hcr5_pk_hs_addrs PS1 PS2 l :
  map peer_addr4 PS1 = map peer_addr4 PS2 -> Forall2 hcr5_hs_ok PS1 l -> Forall2 hcr5_hs_ok PS2 l.
Proof.
  intros Hm H. revert PS2 Hm. induction H as [| x y PS1 l Hxy H IH]; intros [| z PS2] Hm; simpl in Hm;
    try discriminate; constructor.
  - inv Hm. destruct x as [[? ?] ?], z as [[? ?] ?], y as [[? ?] ?]. simpl in *. subst. exact Hxy.
  - inv Hm. auto.
Qed.

(* the slots *)
Lemma hcr5_pk_pok_cons L KA k x : hcr5_pok L KA x -> hcr5_pok L (k :: KA) x.
Proof.
  destruct x as [[a sh] P]. unfold hcr5_pok. intros (H1 & H2 & H3 & H4 & H5 & H6 & H7).
  do 6 (split; [auto |]). eapply Forall_impl; [| exact H7]. intros v Hv. simpl in Hv |- *. tauto.
Qed.

Lemma hcr5_pk_pok_fill L KA d x :
  hcr5_pok L KA x ->
  hcr5_pok L (kd_addr d :: KA)
    (match x with (a, sh, P) =>
       if eq_dec a (kd_owner d) then (a, sh, fill_slot P (kd_addr d) (kd_slot d)) else (a, sh, P) end).
Proof.
  intros H. apply (hcr5_pk_pok_cons L KA (kd_addr d)) in H. destruct x as [[a sh] P].
  destruct (eq_dec a (kd_owner d)); auto.
  unfold hcr5_pok in *. destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7).
  assert (Hd: kd_addr d = nullval \/ In (kd_addr d) (kd_addr d :: KA)) by (simpl; auto).
  rewrite !Forall_cons_iff in H7. destruct H7 as (S1 & S2 & S3 & _).
  unfold fill_slot;
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; simpl;
  (split; [auto | split; [auto | split; [auto | split; [auto | split; [auto | split; [auto |]]]]]]);
  repeat (apply Forall_cons; [first [exact S1 | exact S2 | exact S3 | exact Hd] |]); apply Forall_nil.
Qed.

Lemma hcr5_pk_pok_kents L PS KD :
  Forall (hcr5_pok L []) PS -> Forall (hcr5_pok L (map kd_addr KD)) (kents_PS true PS KD).
Proof.
  intros H. induction KD as [| d KD IH]; simpl; auto.
  unfold fill_peers. rewrite Forall_map. eapply Forall_impl; [| exact IH].
  intros x Hx. apply hcr5_pk_pok_fill; auto.
Qed.

Lemma hcr5_pk_ka KD : hcr5_ka (map kd_kent KD) = map kd_addr KD.
Proof. unfold hcr5_ka. rewrite map_map. reflexivity. Qed.

Lemma hcr5_pk_khead KD : hcr5_khead (map kd_kent KD) = kents_head KD.
Proof. destruct KD; reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* the core                                                                *)
(* ---------------------------------------------------------------------- *)

Lemma hcr5_pk_firstn {A: Type} (l1 l2: list A) : firstn (length l1) (l1 ++ l2) = l1.
Proof. induction l1; simpl; f_equal; auto. Qed.

Lemma hcr5_pk_skipn {A: Type} (l1 l2: list A) : skipn (length l1) (l1 ++ l2) = l2.
Proof. induction l1; simpl; auto. Qed.

Lemma hcr5_pk_ke_F2 PS KD :
  Forall (fun d => In (kd_owner d) (map hcr5_paddr PS)) KD ->
  Forall2 (hcr5_ke_ok PS) (map kd_addr KD) (map hcr5_pk_te KD).
Proof.
  induction 1 as [| d KD Hd H IH]; simpl; constructor; auto.
  unfold hcr5_ke_ok, hcr5_pk_te; simpl. auto.
Qed.

Lemma hcr5_pk_pool PS T KD :
  hcr5_pool [] PS T -> kents_draws_ok PS KD ->
  hcr5_pool (hcr5_ka (map kd_kent KD)) (kents_PS true PS KD) (kents_T T KD).
Proof.
  intros [_ Hhs] [HKD _]. simpl in Hhs.
  unfold hcr5_pool. rewrite hcr5_pk_ka, hcr5_pk_tD_kents, map_length.
  rewrite <- (map_length hcr5_pk_te KD), hcr5_pk_firstn, hcr5_pk_skipn. split.
  - apply hcr5_pk_ke_F2. rewrite hcr5_pk_paddr_addr4, hcr5_pk_addrs_kents.
    eapply Forall_impl; [| exact HKD]. simpl; tauto.
  - eapply hcr5_pk_hs_addrs; [| exact Hhs]. symmetry. apply hcr5_pk_addrs_kents.
Qed.

Lemma hcr5_pk_list L NS PS head nb KD :
  hcr5_list_ok L [] NS PS head nb ->
  hcr5_list_ok L (hcr5_ka (map kd_kent KD)) NS (kents_PS true PS KD) head nb.
Proof.
  intros (Hpok & Hwf & Hch & Hnp & Hnd & Hnb).
  pose proof (hcr5_pk_pj_kents true PS KD) as Hpj. symmetry in Hpj.
  pose proof (hcr5_pk_addrs_kents true PS KD) as Had.
  rewrite hcr5_pk_ka.
  split; [| split; [| split; [| split; [| split]]]].
  - apply hcr5_pk_pok_kents; auto.
  - eapply hcr5_pk_Forall_pj; [exact Hpj | | exact Hwf].
    intros [[a sh] P] [[b sh'] P'] Heq; simpl in Heq. injection Heq as -> -> _ _ _ _. auto.
  - eapply hcr5_pk_chain_pj; eauto.
  - unfold hnodes_peers4 in *. rewrite Had. exact Hnp.
  - rewrite Had. exact Hnd.
  - exact Hnb.
Qed.

Lemma hcr5_pk_core L NS PS T head nb KD :
  hcr5_pool [] PS T -> hcr5_list_ok L [] NS PS head nb -> kents_draws_ok PS KD -> kents_fresh T KD ->
  hcr5_pool (hcr5_ka (map kd_kent KD)) (kents_PS true PS KD) (kents_T T KD) /\
  hcr5_list_ok L (hcr5_ka (map kd_kent KD)) NS (kents_PS true PS KD) head nb.
Proof.
  intros Hp Hl Hd _. split; [apply hcr5_pk_pool | apply hcr5_pk_list]; auto.
Qed.

(* kents_add's precondition *)
Lemma hcr5_pk_owners NS PS :
  hnodes_peers4 NS PS -> (NS <> [] -> hcr5_head NS <> nullval) ->
  kents_owners_ok (hcr5_head NS) nullval NS PS.
Proof.
  intros Hnp Hh. unfold kents_owners_ok. destruct NS as [| N NS].
  - unfold hnodes_peers4 in Hnp. simpl in Hnp |- *. split; auto.
  - simpl hcr5_head in *. rewrite if_false by (apply Hh; discriminate). split; [discriminate | auto].
Qed.
