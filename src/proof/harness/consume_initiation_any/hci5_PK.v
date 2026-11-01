(* law consume_initiation_any: main's phase PK, statement 12: kes = kents_add(&itb, peers, NULL, 1).
   (states: hci5_defs.v).
   harness/consume_initiation_any/hci3_*.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
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
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_cut.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_model.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_globals.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_spec.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_conv.
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* pure lemmas: the table after kents_add (kents_T)                         *)
(* ---------------------------------------------------------------------- *)

Lemma hci5_pk_sfind_supd_ne {A: Type} (l: list (val * share * A)) a b v :
  b <> a -> sfind (supd l a v) b = sfind l b.
Proof.
  intros Hne. induction l as [| [[x sh] u] l IH]; simpl; auto.
  destruct (EqDec_val x a) as [-> | Hxa]; simpl.
  - destruct (EqDec_val a b); [congruence | reflexivity].
  - destruct (EqDec_val x b); auto.
Qed.

Lemma hci5_pk_sfind_supd_eq {A: Type} (l: list (val * share * A)) a sh u v :
  sfind l a = Some (sh, u) -> sfind (supd l a v) a = Some (sh, v).
Proof.
  induction l as [| [[x sh'] u'] l IH]; simpl; [discriminate |].
  destruct (EqDec_val x a) as [-> | Hxa]; simpl.
  - destruct (EqDec_val a a); [| congruence]. intros H; inv H. reflexivity.
  - destruct (EqDec_val x a); [congruence |]. auto.
Qed.

Lemma hci5_pk_saddrs_supd {A: Type} (l: list (val * share * A)) a v : saddrs (supd l a v) = saddrs l.
Proof.
  induction l as [| [[x sh] u] l IH]; simpl; auto.
  destruct (EqDec_val x a); simpl; f_equal; auto.
Qed.

Lemma hci5_pk_shares_supd (l: list (val * share * entry)) a v :
  Forall (fun d => match d with (_, sh, _) => sh = Ews end) l ->
  Forall (fun d => match d with (_, sh, _) => sh = Ews end) (supd l a v).
Proof.
  induction l as [| [[x sh] u] l IH]; simpl; auto. intros H; inv H.
  destruct (EqDec_val x a); constructor; auto.
Qed.

Lemma hci5_pk_tD_insert T a idx :
  t_D (t_insert T a idx) = t_D (t_set_index T a idx).
Proof. reflexivity. Qed.

Lemma hci5_pk_saddrs_insert T a idx : saddrs (t_D (t_insert T a idx)) = saddrs (t_D T).
Proof.
  rewrite hci5_pk_tD_insert. unfold t_set_index, t_entry.
  destruct (sfind (t_D T) a) as [[sh E] |]; simpl; auto. apply hci5_pk_saddrs_supd.
Qed.

Lemma hci5_pk_shares_insert T a idx :
  Forall (fun d => match d with (_, sh, _) => sh = Ews end) (t_D T) ->
  Forall (fun d => match d with (_, sh, _) => sh = Ews end) (t_D (t_insert T a idx)).
Proof.
  rewrite hci5_pk_tD_insert. unfold t_set_index, t_entry.
  destruct (sfind (t_D T) a) as [[sh E] |]; simpl; auto. apply hci5_pk_shares_supd.
Qed.

Lemma hci5_pk_epeer_insert T a idx b :
  e_peer (t_entry_d (t_insert T a idx) b) = e_peer (t_entry_d T b).
Proof.
  unfold t_entry_d, t_entry. rewrite hci5_pk_tD_insert. unfold t_set_index, t_entry.
  destruct (sfind (t_D T) a) as [[sh E] |] eqn:Ha; simpl; auto.
  destruct (eq_dec b a) as [-> | Hba].
  - rewrite (hci5_pk_sfind_supd_eq _ _ _ _ _ Ha), Ha. reflexivity.
  - rewrite hci5_pk_sfind_supd_ne by auto. reflexivity.
Qed.

Lemma hci5_pk_epeer_add T a sh E b :
  e_peer (t_entry_d (t_add T a sh E) b) = if eq_dec a b then e_peer E else e_peer (t_entry_d T b).
Proof. unfold t_entry_d, t_entry, t_add; simpl. destruct (EqDec_val a b); reflexivity. Qed.

Lemma hci5_pk_saddrs_kents T KD : saddrs (t_D (kents_T T KD)) = map kd_addr KD ++ saddrs (t_D T).
Proof.
  induction KD as [| d KD IH]; cbn [kents_T map app]; auto.
  rewrite hci5_pk_saddrs_insert. unfold t_add; simpl. f_equal. exact IH.
Qed.

Lemma hci5_pk_shares_kents T KD :
  Forall (fun d => match d with (_, sh, _) => sh = Ews end) (t_D T) ->
  Forall (fun d => match d with (_, sh, _) => sh = Ews end) (t_D (kents_T T KD)).
Proof.
  intros H. induction KD as [| d KD IH]; cbn [kents_T]; auto.
  apply hci5_pk_shares_insert. unfold t_add; simpl. constructor; auto.
Qed.

Lemma hci5_pk_epeer_kents_out T KD b :
  ~ In b (map kd_addr KD) -> e_peer (t_entry_d (kents_T T KD) b) = e_peer (t_entry_d T b).
Proof.
  induction KD as [| d KD IH]; cbn [kents_T map In]; auto. intros Hn.
  rewrite hci5_pk_epeer_insert, hci5_pk_epeer_add. rewrite if_false by tauto. apply IH; tauto.
Qed.

Lemma hci5_pk_epeer_kents_in T KD (own: list val) :
  Forall (fun d => In (kd_owner d) own) KD ->
  Forall (fun d => In (e_peer (t_entry_d (kents_T T KD) (kd_addr d))) own) KD.
Proof.
  induction KD as [| d KD IH]; cbn [kents_T]; intros H; auto. inv H. constructor.
  - rewrite hci5_pk_epeer_insert, hci5_pk_epeer_add. rewrite if_true by reflexivity. simpl. auto.
  - specialize (IH H3). eapply Forall_impl; [| exact IH]. intros d0 H0.
    rewrite hci5_pk_epeer_insert, hci5_pk_epeer_add. destruct (eq_dec (kd_addr d) (kd_addr d0)); auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* pure lemmas: the peers after kents_add (kents_PS: only slots change)     *)
(* ---------------------------------------------------------------------- *)

Definition hci5_pk_pj (x: val * share * peer) :=
  match x with (a, sh, P) => (a, sh, p_device P, p_hs P, p_refs P, p_pknext P) end.

Lemma hci5_pk_pj_kents fl PS KD : map hci5_pk_pj (kents_PS fl PS KD) = map hci5_pk_pj PS.
Proof.
  induction KD as [| d KD IH]; simpl; auto. destruct fl; auto.
  unfold fill_peers. rewrite map_map, <- IH. apply map_ext. intros [[x sh] P].
  destruct (eq_dec x (kd_owner d)); auto. unfold fill_slot.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

Lemma hci5_pk_addrs_pj l :
  map peer_addr4 l = map (fun y => match y with (a, _, _, _, _, _) => a end) (map hci5_pk_pj l).
Proof. rewrite map_map. apply map_ext. intros [[? ?] ?]. reflexivity. Qed.

Lemma hci5_pk_addrs_kents fl PS KD : map peer_addr4 (kents_PS fl PS KD) = map peer_addr4 PS.
Proof. rewrite !hci5_pk_addrs_pj, hci5_pk_pj_kents. reflexivity. Qed.

Lemma hci5_pk_Forall_pj (Q: val * share * peer -> Prop) l1 l2 :
  map hci5_pk_pj l1 = map hci5_pk_pj l2 -> (forall x y, hci5_pk_pj x = hci5_pk_pj y -> Q x -> Q y) ->
  Forall Q l1 -> Forall Q l2.
Proof.
  intros Hm HQ H. revert l2 Hm. induction H as [| x l1 Hx H IH]; intros [| y l2] Hm; simpl in Hm;
    try discriminate; constructor.
  - inv Hm. eapply HQ; eauto.
  - inv Hm. auto.
Qed.

Lemma hci5_pk_chain_pj h l1 l2 :
  map hci5_pk_pj l1 = map hci5_pk_pj l2 -> pk_chain h l1 -> pk_chain h l2.
Proof.
  revert h l2. induction l1 as [| [[a sh] P] l1 IH]; intros h [| [[b sh'] P'] l2] Hm; simpl in *;
    try discriminate; auto.
  injection Hm as -> -> _ _ _ E4 Hm. intros [Hh Hc]. split; auto. rewrite <- E4. eapply IH; eauto.
Qed.

Section Pok.
Variable x25519: list byte -> list byte -> list byte.

Lemma hci5_pk_pok_pj R L x y :
  hci5_pk_pj x = hci5_pk_pj y -> hci5_pok x25519 R L x -> hci5_pok x25519 R L y.
Proof.
  destruct x as [[a sh] P], y as [[b sh'] P']. simpl. intros Heq.
  injection Heq as -> -> E1 E2 E3 E4. unfold hci5_pok.
  rewrite <- E1, <- E2, <- E3, <- E4. auto.
Qed.
End Pok.

Lemma hci5_pk_slots_cons e KE PS : hci5_slots_ok KE PS -> hci5_slots_ok (e :: KE) PS.
Proof.
  unfold hci5_slots_ok. apply Forall_impl. intros [[a sh] P] H.
  eapply Forall_impl; [| exact H]. intros k Hk. simpl in Hk |- *. tauto.
Qed.

Lemma hci5_pk_slots_fill KE PS d :
  hci5_slots_ok KE PS -> hci5_slots_ok (kd_kent d :: KE) (fill_peers PS d).
Proof.
  intros H. pose proof (hci5_pk_slots_cons (kd_kent d) _ _ H) as H'. clear H.
  unfold hci5_slots_ok, fill_peers in *. rewrite Forall_map.
  eapply Forall_impl; [| exact H']. intros [[a sh] P] HP. unfold Basics.compose. cbv beta iota.
  assert (Hd: kd_addr d = nullval \/ In (kd_addr d) (map ke_addr (kd_kent d :: KE))) by (simpl; auto).
  rewrite !Forall_cons_iff in HP. destruct HP as (H1 & H2 & H3 & _).
  match goal with |- context [if ?c then _ else _] => destruct c end; [unfold fill_slot |];
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; simpl;
  repeat (apply Forall_cons; [first [exact H1 | exact H2 | exact H3 | exact Hd] |]); apply Forall_nil.
Qed.

Lemma hci5_pk_slots_kents PS KD :
  hci5_slots_ok [] PS -> hci5_slots_ok (map kd_kent KD) (kents_PS true PS KD).
Proof.
  intros H. induction KD as [| d KD IH]; simpl; auto. apply hci5_pk_slots_fill; auto.
Qed.

Lemma hci5_pk_khead KD : hci5_khead (map kd_kent KD) = kents_head KD.
Proof. destruct KD; reflexivity. Qed.

Section Inv.
Variable x25519: list byte -> list byte -> list byte.

Lemma hci5_pk_inv R L NS PS T KD head na :
  hci5_inv x25519 R L NS PS [] T head na -> kents_draws_ok PS KD -> itable_wf (kents_T T KD) ->
  hci5_inv x25519 R L NS (kents_PS true PS KD) (map kd_kent KD) (kents_T T KD) head na.
Proof.
  intros (Hpok & Hwf & Hch & Hnp & Hna & HT & Hsl) [HKD HND] Hwf'.
  pose proof (hci5_pk_pj_kents true PS KD) as Hpj. symmetry in Hpj.
  pose proof (hci5_pk_addrs_kents true PS KD) as Had.
  destruct HT as (HTa & HTs & HTp & _).
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - eapply hci5_pk_Forall_pj; [exact Hpj | | exact Hpok]. apply hci5_pk_pok_pj.
  - eapply hci5_pk_Forall_pj; [exact Hpj | | exact Hwf].
    intros [[a sh] P] [[b sh'] P'] Heq; simpl in Heq. injection Heq as -> -> _ _ _ _. auto.
  - eapply hci5_pk_chain_pj; eauto.
  - unfold hnodes_peers4 in *. rewrite Had. exact Hnp.
  - exact Hna.
  - unfold hci5_T_ok. rewrite Had, hci5_pk_saddrs_kents, HTa. simpl.
    rewrite map_map. simpl.
    assert (Hdis: forall x, In x PS -> ~ In (hs_addr (peer_addr4 x)) (map kd_addr KD)).
    { destruct Hwf' as (_ & _ & Hnd & _). rewrite hci5_pk_saddrs_kents, HTa in Hnd. simpl in Hnd.
      apply NoDup_app in Hnd. destruct Hnd as (_ & _ & Hnd).
      intros x Hx Hin. apply (Hnd _ Hin).
      apply (in_map (fun x => hs_addr (peer_addr4 x))) in Hx. exact Hx. }
    split; [rewrite <- (map_map peer_addr4 hs_addr (kents_PS true PS KD)), Had, map_map; reflexivity | split; [| split]].
    + apply hci5_pk_shares_kents; auto.
    + (* the peers' entries *)
      assert (Hp': Forall (fun x => e_peer (t_entry_d (kents_T T KD) (hs_addr (peer_addr4 x))) = peer_addr4 x) PS).
      { rewrite Forall_forall in HTp |- *. intros x Hx.
        rewrite hci5_pk_epeer_kents_out by (apply Hdis; auto). auto. }
      eapply hci5_pk_Forall_pj; [exact Hpj | | exact Hp'].
      intros [[a sh] P] [[b sh'] P'] Heq; simpl in Heq. injection Heq as -> -> _ _ _ _. auto.
    + rewrite Forall_map. simpl.
      apply hci5_pk_epeer_kents_in. eapply Forall_impl; [| exact HKD]. simpl; tauto.
  - apply hci5_pk_slots_kents; auto.
Qed.

End Inv.

Lemma hci5_pk_owners NS PS :
  hnodes_peers4 NS PS -> (NS <> [] -> hci5_head NS <> nullval) ->
  kents_owners_ok (hci5_head NS) nullval NS PS.
Proof.
  intros Hnp Hh. unfold kents_owners_ok. destruct NS as [| N NS].
  - unfold hnodes_peers4 in Hnp. simpl in Hnp |- *. split; auto.
  - simpl hci5_head in *. rewrite if_false by (apply Hh; discriminate). split; [discriminate | auto].
Qed.

Lemma hci5_pk_head_ptr NS :
  hnodes_rep4 W (hci5_head NS) NS |--
  !! (is_pointer_or_null (hci5_head NS) /\ (NS <> [] -> hci5_head NS <> nullval)).
Proof.
  destruct NS as [| N NS]; simpl.
  - apply prop_right. split; [reflexivity | congruence].
  - Intros nx. entailer!.
    match goal with H: field_compatible _ _ (hn_addr N) |- _ => destruct H as [Hp _] end.
    split; [apply isptr_is_pointer_or_null; auto |].
    intros _ E. rewrite E in Hp. inv Hp.
Qed.

Section PK.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hci5_PK_ok {Espec: OracleKind} gv L FR :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> 
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_SA x25519 gv L FR) hci5_PK
    (overridePost (hci5_SK x25519 gv L FR) (hci5_R gv)).
Proof.
  intros HH. unfold hci5_SA, hci5_Delta, hci5_R, hci5_PK. simplify_func_tycontext.
  Intros R S w NS PS T head na.
  abbreviate_semax.
  unfold hci5_world, hci5_globs, hci5_lvars, hci5_snaps0, hci5_scr; cbn [app].
  assert_PROP (is_pointer_or_null (hci5_head NS) /\ (NS <> [] -> hci5_head NS <> nullval)) as Hhd
    by (sep_apply (hci5_pk_head_ptr NS); entailer!).
  destruct Hhd as [Hhp Hhn].
  forward.
  forward_call (gv, Tsh, l_itb L, T, hci5_head NS, NS, nullval, PS, Int.one, S, w).
  { destruct H0 as (_ & Hwf & _ & Hnp & _ & _ & Hsl). split; [auto |]. split; [apply hci5_pk_owners; auto |].
    (* v4.1: the owners' slots are NULL (no kent yet) *)
    unfold hci5_slots_ok in Hsl. eapply Forall_impl; [| exact Hsl].
    intros [[a sh] P] HP. eapply Forall_impl; [| exact HP].
    intros k [Hk | Hk]; [left; exact Hk | contradiction]. }
  Intros KD.
  assert_PROP (itable_wf (kents_T T KD)) as Hwf' by (unfold itable; entailer!).
  forward.
  change (negb (Int.eq Int.one Int.zero)) with true.
  unfold hci5_SK.
  Exists R (kents_S S KD) w NS (kents_PS true PS KD) (kents_T T KD) head na (map kd_kent KD).
  rewrite hci5_pk_khead.
  unfold hci5_world, hci5_globs, hci5_lvars, hci5_snaps0, hci5_scr; cbn [app].
  entailer!.
  apply hci5_pk_inv; auto.
Qed.

End PK.
