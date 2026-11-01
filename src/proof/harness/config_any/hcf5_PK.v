(* law config_any: main's phase PK, statements 17: kes = kents_add(&it, NULL, &p, 1).
   (states: hcf5_defs.v).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.config_any.hcf5_world.
Require Import WgNoise.proof.harness.config_any.hcf5_cut.
Require Import WgNoise.proof.harness.config_any.hcf5_globals.
Require Import WgNoise.proof.harness.config_any.hcf5_spec.
Require Import WgNoise.proof.harness.config_any.hcf5_defs.
Require Import WgNoise.proof.harness.config_any.hcf5_conv.
Require Import WgNoise.proof.harness.config_any.hcf5_pure.
Require WgNoise.harness.x_config_any.code.

#[local] Existing Instance W_config_any.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* pure lemmas: the table after kents_add (kents_T); port of hci5_PK.v     *)
(* ---------------------------------------------------------------------- *)

Lemma hcf5_pk_sfind_supd_ne {A: Type} (l: list (val * share * A)) a b v :
  b <> a -> sfind (supd l a v) b = sfind l b.
Proof.
  intros Hne. induction l as [| [[x sh] u] l IH]; simpl; auto.
  destruct (EqDec_val x a) as [-> | Hxa]; simpl.
  - destruct (EqDec_val a b); [congruence | reflexivity].
  - destruct (EqDec_val x b); auto.
Qed.

Lemma hcf5_pk_sfind_supd_eq {A: Type} (l: list (val * share * A)) a sh u v :
  sfind l a = Some (sh, u) -> sfind (supd l a v) a = Some (sh, v).
Proof.
  induction l as [| [[x sh'] u'] l IH]; simpl; [discriminate |].
  destruct (EqDec_val x a) as [-> | Hxa]; simpl.
  - destruct (EqDec_val a a); [| congruence]. intros H; inv H. reflexivity.
  - destruct (EqDec_val x a); [congruence |]. auto.
Qed.

Lemma hcf5_pk_saddrs_supd {A: Type} (l: list (val * share * A)) a v : saddrs (supd l a v) = saddrs l.
Proof.
  induction l as [| [[x sh] u] l IH]; simpl; auto.
  destruct (EqDec_val x a); simpl; f_equal; auto.
Qed.

Lemma hcf5_pk_tD_insert T a idx :
  t_D (t_insert T a idx) = t_D (t_set_index T a idx).
Proof. reflexivity. Qed.

Lemma hcf5_pk_saddrs_insert T a idx : saddrs (t_D (t_insert T a idx)) = saddrs (t_D T).
Proof.
  rewrite hcf5_pk_tD_insert. unfold t_set_index, t_entry.
  destruct (sfind (t_D T) a) as [[sh E] |]; simpl; auto. apply hcf5_pk_saddrs_supd.
Qed.

Lemma hcf5_pk_epeer_insert T a idx b :
  e_peer (t_entry_d (t_insert T a idx) b) = e_peer (t_entry_d T b).
Proof.
  unfold t_entry_d, t_entry. rewrite hcf5_pk_tD_insert. unfold t_set_index, t_entry.
  destruct (sfind (t_D T) a) as [[sh E] |] eqn:Ha; simpl; auto.
  destruct (eq_dec b a) as [-> | Hba].
  - rewrite (hcf5_pk_sfind_supd_eq _ _ _ _ _ Ha), Ha. reflexivity.
  - rewrite hcf5_pk_sfind_supd_ne by auto. reflexivity.
Qed.

Lemma hcf5_pk_epeer_add T a sh E b :
  e_peer (t_entry_d (t_add T a sh E) b) = if eq_dec a b then e_peer E else e_peer (t_entry_d T b).
Proof. unfold t_entry_d, t_entry, t_add; simpl. destruct (EqDec_val a b); reflexivity. Qed.

Lemma hcf5_pk_saddrs_kents T KD : saddrs (t_D (kents_T T KD)) = map kd_addr KD ++ saddrs (t_D T).
Proof.
  induction KD as [| d KD IH]; cbn [kents_T map app]; auto.
  rewrite hcf5_pk_saddrs_insert. unfold t_add; simpl. f_equal. exact IH.
Qed.

Lemma hcf5_pk_epeer_kents_out T KD b :
  ~ In b (map kd_addr KD) -> e_peer (t_entry_d (kents_T T KD) b) = e_peer (t_entry_d T b).
Proof.
  induction KD as [| d KD IH]; cbn [kents_T map In]; auto. intros Hn.
  rewrite hcf5_pk_epeer_insert, hcf5_pk_epeer_add. rewrite if_false by tauto. apply IH; tauto.
Qed.

Lemma hcf5_pk_epeer_kents_in T KD (own: list val) :
  Forall (fun d => In (kd_owner d) own) KD ->
  Forall (fun d => In (e_peer (t_entry_d (kents_T T KD) (kd_addr d))) own) KD.
Proof.
  induction KD as [| d KD IH]; cbn [kents_T]; intros H; auto. inv H. constructor.
  - rewrite hcf5_pk_epeer_insert, hcf5_pk_epeer_add. rewrite if_true by reflexivity. simpl. auto.
  - specialize (IH H3). eapply Forall_impl; [| exact IH]. intros d0 H0.
    rewrite hcf5_pk_epeer_insert, hcf5_pk_epeer_add. destruct (eq_dec (kd_addr d) (kd_addr d0)); auto.
Qed.

(* the shares of the pool items (hcf5_tsh) *)
Lemma hcf5_pk_tsh_insert T a idx b : hcf5_tsh (t_insert T a idx) b = hcf5_tsh T b.
Proof.
  unfold hcf5_tsh. rewrite hcf5_pk_tD_insert. unfold t_set_index, t_entry.
  destruct (sfind (t_D T) a) as [[sh E] |] eqn:Ha; simpl; auto.
  destruct (eq_dec b a) as [-> | Hba].
  - rewrite (hcf5_pk_sfind_supd_eq _ _ _ _ _ Ha), Ha. reflexivity.
  - rewrite hcf5_pk_sfind_supd_ne by auto. reflexivity.
Qed.

Lemma hcf5_pk_tsh_add T a sh E b :
  hcf5_tsh (t_add T a sh E) b = if eq_dec a b then sh else hcf5_tsh T b.
Proof. unfold hcf5_tsh, t_add; simpl. destruct (EqDec_val a b); reflexivity. Qed.

Lemma hcf5_pk_tsh_kents_out T KD b :
  ~ In b (map kd_addr KD) -> hcf5_tsh (kents_T T KD) b = hcf5_tsh T b.
Proof.
  induction KD as [| d KD IH]; cbn [kents_T map In]; auto. intros Hn.
  rewrite hcf5_pk_tsh_insert, hcf5_pk_tsh_add. rewrite if_false by tauto. apply IH; tauto.
Qed.

Lemma hcf5_pk_tsh_kents_in T KD :
  Forall (fun d => hcf5_tsh (kents_T T KD) (kd_addr d) = Ews) KD.
Proof.
  induction KD as [| d KD IH]; cbn [kents_T]; auto. constructor.
  - rewrite hcf5_pk_tsh_insert, hcf5_pk_tsh_add. rewrite if_true by reflexivity. reflexivity.
  - eapply Forall_impl; [| exact IH]. intros d0 H0.
    rewrite hcf5_pk_tsh_insert, hcf5_pk_tsh_add. destruct (eq_dec (kd_addr d) (kd_addr d0)); auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* pure lemmas: the peer after kents_add (kents_PS: only slots change)      *)
(* ---------------------------------------------------------------------- *)

Definition hcf5_pk_pj (x: val * share * peer) :=
  match x with (a, sh, P) => (a, sh, p_device P, p_hs P, p_refs P, p_pknext P) end.

Lemma hcf5_pk_pj_kents fl PS KD : map hcf5_pk_pj (kents_PS fl PS KD) = map hcf5_pk_pj PS.
Proof.
  induction KD as [| d KD IH]; simpl; auto. destruct fl; auto.
  unfold fill_peers. rewrite map_map, <- IH. apply map_ext. intros [[x sh] P].
  destruct (eq_dec x (kd_owner d)); auto. unfold fill_slot.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

Lemma hcf5_pk_single a sh P KD : exists P',
  kents_PS true [(a, sh, P)] KD = [(a, sh, P')] /\
  p_device P' = p_device P /\ p_hs P' = p_hs P /\ p_pknext P' = p_pknext P.
Proof.
  pose proof (hcf5_pk_pj_kents true [(a, sh, P)] KD) as H.
  destruct (kents_PS true [(a, sh, P)] KD) as [| [[a' sh'] P'] [| y l]]; simpl in H; try discriminate.
  injection H as -> -> E1 E2 E3 E4. exists P'. auto.
Qed.

Definition hcf5_pk_sl (KE: list kent4) (PS: list (val * share * peer)) : Prop :=
  Forall (fun x => match x with (_, _, P) => hcf5_slots_ok KE P end) PS.

Lemma hcf5_pk_slots_cons e KE PS : hcf5_pk_sl KE PS -> hcf5_pk_sl (e :: KE) PS.
Proof.
  unfold hcf5_pk_sl, hcf5_slots_ok. apply Forall_impl. intros [[a sh] P] H.
  eapply Forall_impl; [| exact H]. intros k Hk. simpl in Hk |- *. tauto.
Qed.

Lemma hcf5_pk_slots_fill KE PS d :
  hcf5_pk_sl KE PS -> hcf5_pk_sl (kd_kent d :: KE) (fill_peers PS d).
Proof.
  intros H. pose proof (hcf5_pk_slots_cons (kd_kent d) _ _ H) as H'. clear H.
  unfold hcf5_pk_sl, hcf5_slots_ok, fill_peers in *. rewrite Forall_map.
  eapply Forall_impl; [| exact H']. intros [[a sh] P] HP. unfold Basics.compose. cbv beta iota.
  assert (Hd: kd_addr d = nullval \/ In (kd_addr d) (map ke_addr (kd_kent d :: KE))) by (simpl; auto).
  rewrite !Forall_cons_iff in HP. destruct HP as (H1 & H2 & H3 & _).
  match goal with |- context [if ?c then _ else _] => destruct c end; [unfold fill_slot |];
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; simpl;
  repeat (apply Forall_cons; [first [exact H1 | exact H2 | exact H3 | exact Hd] |]); apply Forall_nil.
Qed.

Lemma hcf5_pk_slots_kents PS KD :
  hcf5_pk_sl [] PS -> hcf5_pk_sl (map kd_kent KD) (kents_PS true PS KD).
Proof.
  intros H. induction KD as [| d KD IH]; simpl; auto. apply hcf5_pk_slots_fill; auto.
Qed.

Lemma hcf5_pk_khead KD : hcf5_khead (map kd_kent KD) = kents_head KD.
Proof. destruct KD; reflexivity. Qed.

(* the table facts after the kents *)
Lemma hcf5_pk_T_ok L T KD :
  hcf5_T_ok L [] false T -> itable_wf (kents_T T KD) ->
  Forall (fun d => In (kd_owner d) [l_p L]) KD ->
  hcf5_T_ok L (map kd_kent KD) false (kents_T T KD).
Proof.
  intros (HTa & _ & HTs & HTp & _) Hwf HKD. simpl in HTa.
  assert (Hout: ~ In (hs_addr (l_p L)) (map kd_addr KD)).
  { destruct Hwf as (_ & _ & Hnd & _). rewrite hcf5_pk_saddrs_kents, HTa in Hnd.
    apply NoDup_app in Hnd. destruct Hnd as (_ & _ & Hnd). intros Hin. apply (Hnd _ Hin). left; reflexivity. }
  unfold hcf5_T_ok, hcf5_qs. rewrite hcf5_pk_saddrs_kents, HTa, map_map. cbn [app ke_addr kd_kent].
  split; [reflexivity | split; [| split; [| split; [| discriminate]]]].
  - rewrite Forall_map. cbn [ke_addr kd_kent].
    pose proof (hcf5_pk_tsh_kents_in T KD) as H1. pose proof (hcf5_pk_epeer_kents_in T KD _ HKD) as H2.
    rewrite Forall_forall in H1, H2 |- *. intros d Hd. split; [exact (H1 d Hd) |].
    specialize (H2 d Hd). destruct H2 as [H2 | []]. symmetry; exact H2.
  - rewrite hcf5_pk_tsh_kents_out by exact Hout. exact HTs.
  - rewrite hcf5_pk_epeer_kents_out by exact Hout. exact HTp.
Qed.

Lemma hcf5_pk_boot S KD : s_boot (kents_S S KD) = s_boot S.
Proof. destruct KD; reflexivity. Qed.

Lemma hcf5_pk_fold a sh P :
  peer_rep sh a P |-- peers_rep [(a, sh, P)] * hnodes_rep4 W nullval [].
Proof. unfold peers_rep, hnodes_rep4; simpl. entailer!. Qed.

Lemma hcf5_pk_unfold a sh P :
  peers_rep [(a, sh, P)] * hnodes_rep4 W nullval [] |-- peer_rep sh a P.
Proof. unfold peers_rep, hnodes_rep4; simpl. entailer!. Qed.

Section PK.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcf5_PK_ok {Espec: OracleKind} gv L FR :
  hcf5_hyps x25519 ->
  semax (hcf5_Delta x25519) (hcf5_SA gv L FR) hcf5_PK
    (overridePost (hcf5_SK gv L FR) (hcf5_R gv)).
Proof.
  intros HH. unfold hcf5_SA, hcf5_Delta, hcf5_R, hcf5_PK. simplify_func_tycontext.
  Intros R S w D P T.
  abbreviate_semax.
  unfold hcf5_globs, hcf5_lvars; cbn [app].
  assert_PROP (isptr (l_p L)) as Hpp by entailer!.
  sep_apply (hcf5_pk_fold (l_p L) Tsh P).
  forward_call (gv, Tsh, l_it L, T, nullval, @nil hnode4, l_p L, [(l_p L, Tsh, P)], Int.one, S, w).
  { cancel. }
  { split; [| split].
    - unfold peers_wf. constructor; [apply writable_share_top | constructor].
    - unfold kents_owners_ok. rewrite if_true by reflexivity. split; [reflexivity |].
      rewrite if_false by (intros E; rewrite E in Hpp; inv Hpp). reflexivity.
    - (* v4.1: the owner's slots are NULL *)
      constructor; [| constructor]. rewrite H4, H5, H6.
      repeat constructor; left; reflexivity. }
  Intros KD.
  assert_PROP (itable_wf (kents_T T KD)) as Hwf' by (unfold itable; entailer!).
  destruct (hcf5_pk_single (l_p L) Tsh P KD) as (P' & HPS & E1 & E2 & E3).
  change (negb (Int.eq Int.one Int.zero)) with true. rewrite HPS.
  sep_apply (hcf5_pk_unfold (l_p L) Tsh P').
  forward.
  unfold hcf5_SK.
  Exists R (kents_S S KD) w D P' (kents_T T KD) (map kd_kent KD).
  rewrite hcf5_pk_khead.
  unfold hcf5_globs, hcf5_lvars; cbn [app].
  assert (Hsl: hcf5_pk_sl (map kd_kent KD) [(l_p L, Tsh, P')]).
  { rewrite <- HPS. apply hcf5_pk_slots_kents. unfold hcf5_pk_sl, hcf5_slots_ok.
    constructor; [| constructor]. rewrite H4, H5, H6. repeat constructor; auto. }
  assert (HT: hcf5_T_ok L (map kd_kent KD) false (kents_T T KD)).
  { apply hcf5_pk_T_ok; auto. destruct H8 as [HKD _]. eapply Forall_impl; [| exact HKD].
    intros d Hd. exact (proj1 Hd). }
  entailer!.
  split; [rewrite hcf5_pk_boot; exact H0 |].
  split.
  - unfold hcf5_pok in *. rewrite E1, E2, E3. auto.
  - inv Hsl. auto.
Qed.

End PK.
