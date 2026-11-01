(* law handshake_clear: main's phase PK, statement 8: kes = kents_add(&it, peers, NULL, 1) (kents_add4: KE = map kd_kent KD, table kents_T, peers kents_PS true, shim kents_S).
   (states: hcl5_defs.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_world.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_cut.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_globals.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_spec.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_defs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_conv.
Require WgNoise.harness.x_handshake_clear.code.

#[local] Existing Instance W_handshake_clear.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* pure lemmas: the table after kents_add (kents_T)                         *)
(* ---------------------------------------------------------------------- *)

Lemma hcl5_pk_sfind_supd_ne {A: Type} (l: list (val * share * A)) a b v :
  b <> a -> sfind (supd l a v) b = sfind l b.
Proof.
  intros Hne. induction l as [| [[x sh] u] l IH]; simpl; auto.
  destruct (EqDec_val x a) as [-> | Hxa]; simpl.
  - destruct (EqDec_val a b); [congruence | reflexivity].
  - destruct (EqDec_val x b); auto.
Qed.

Lemma hcl5_pk_sfind_supd_eq {A: Type} (l: list (val * share * A)) a sh u v :
  sfind l a = Some (sh, u) -> sfind (supd l a v) a = Some (sh, v).
Proof.
  induction l as [| [[x sh'] u'] l IH]; simpl; [discriminate |].
  destruct (EqDec_val x a) as [-> | Hxa]; simpl.
  - destruct (EqDec_val a a); [| congruence]. intros H; inv H. reflexivity.
  - destruct (EqDec_val x a); [congruence |]. auto.
Qed.

Lemma hcl5_pk_saddrs_supd {A: Type} (l: list (val * share * A)) a v : saddrs (supd l a v) = saddrs l.
Proof.
  induction l as [| [[x sh] u] l IH]; simpl; auto.
  destruct (EqDec_val x a); simpl; f_equal; auto.
Qed.

Lemma hcl5_pk_shares_supd (l: list (val * share * entry)) a v :
  Forall (fun d => match d with (_, sh, _) => sh = Ews end) l ->
  Forall (fun d => match d with (_, sh, _) => sh = Ews end) (supd l a v).
Proof.
  induction l as [| [[x sh] u] l IH]; simpl; auto. intros H; inv H.
  destruct (EqDec_val x a); constructor; auto.
Qed.

Lemma hcl5_pk_tD_insert T a idx :
  t_D (t_insert T a idx) = t_D (t_set_index T a idx).
Proof. reflexivity. Qed.

Lemma hcl5_pk_saddrs_insert T a idx : saddrs (t_D (t_insert T a idx)) = saddrs (t_D T).
Proof.
  rewrite hcl5_pk_tD_insert. unfold t_set_index, t_entry.
  destruct (sfind (t_D T) a) as [[sh E] |]; simpl; auto. apply hcl5_pk_saddrs_supd.
Qed.

Lemma hcl5_pk_shares_insert T a idx :
  Forall (fun d => match d with (_, sh, _) => sh = Ews end) (t_D T) ->
  Forall (fun d => match d with (_, sh, _) => sh = Ews end) (t_D (t_insert T a idx)).
Proof.
  rewrite hcl5_pk_tD_insert. unfold t_set_index, t_entry.
  destruct (sfind (t_D T) a) as [[sh E] |]; simpl; auto. apply hcl5_pk_shares_supd.
Qed.

Lemma hcl5_pk_epeer_insert T a idx b :
  e_peer (t_entry_d (t_insert T a idx) b) = e_peer (t_entry_d T b).
Proof.
  unfold t_entry_d, t_entry. rewrite hcl5_pk_tD_insert. unfold t_set_index, t_entry.
  destruct (sfind (t_D T) a) as [[sh E] |] eqn:Ha; simpl; auto.
  destruct (eq_dec b a) as [-> | Hba].
  - rewrite (hcl5_pk_sfind_supd_eq _ _ _ _ _ Ha), Ha. reflexivity.
  - rewrite hcl5_pk_sfind_supd_ne by auto. reflexivity.
Qed.

Lemma hcl5_pk_epeer_add T a sh E b :
  e_peer (t_entry_d (t_add T a sh E) b) = if eq_dec a b then e_peer E else e_peer (t_entry_d T b).
Proof. unfold t_entry_d, t_entry, t_add; simpl. destruct (EqDec_val a b); reflexivity. Qed.

Lemma hcl5_pk_saddrs_kents T KD : saddrs (t_D (kents_T T KD)) = map kd_addr KD ++ saddrs (t_D T).
Proof.
  induction KD as [| d KD IH]; cbn [kents_T map app]; auto.
  rewrite hcl5_pk_saddrs_insert. unfold t_add; simpl. f_equal. exact IH.
Qed.

Lemma hcl5_pk_shares_kents T KD :
  Forall (fun d => match d with (_, sh, _) => sh = Ews end) (t_D T) ->
  Forall (fun d => match d with (_, sh, _) => sh = Ews end) (t_D (kents_T T KD)).
Proof.
  intros H. induction KD as [| d KD IH]; cbn [kents_T]; auto.
  apply hcl5_pk_shares_insert. unfold t_add; simpl. constructor; auto.
Qed.

Lemma hcl5_pk_epeer_kents_out T KD b :
  ~ In b (map kd_addr KD) -> e_peer (t_entry_d (kents_T T KD) b) = e_peer (t_entry_d T b).
Proof.
  induction KD as [| d KD IH]; cbn [kents_T map In]; auto. intros Hn.
  rewrite hcl5_pk_epeer_insert, hcl5_pk_epeer_add. rewrite if_false by tauto. apply IH; tauto.
Qed.

Lemma hcl5_pk_epeer_kents_in T KD (own: list val) :
  Forall (fun d => In (kd_owner d) own) KD ->
  Forall (fun d => In (e_peer (t_entry_d (kents_T T KD) (kd_addr d))) own) KD.
Proof.
  induction KD as [| d KD IH]; cbn [kents_T]; intros H; auto. inv H. constructor.
  - rewrite hcl5_pk_epeer_insert, hcl5_pk_epeer_add. rewrite if_true by reflexivity. simpl. auto.
  - specialize (IH H3). eapply Forall_impl; [| exact IH]. intros d0 H0.
    rewrite hcl5_pk_epeer_insert, hcl5_pk_epeer_add. destruct (eq_dec (kd_addr d) (kd_addr d0)); auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* pure lemmas: the peers after kents_add (kents_PS: only slots change)     *)
(* ---------------------------------------------------------------------- *)

Definition hcl5_pk_pj (x: val * share * peer) :=
  match x with (a, sh, P) => (a, sh, p_device P, p_hs P, p_refs P, p_pknext P) end.

Lemma hcl5_pk_pj_kents fl PS KD : map hcl5_pk_pj (kents_PS fl PS KD) = map hcl5_pk_pj PS.
Proof.
  induction KD as [| d KD IH]; simpl; auto. destruct fl; auto.
  unfold fill_peers. rewrite map_map, <- IH. apply map_ext. intros [[x sh] P].
  destruct (eq_dec x (kd_owner d)); auto. unfold fill_slot.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

Lemma hcl5_pk_addrs_pj l :
  map peer_addr4 l = map (fun y => match y with (a, _, _, _, _, _) => a end) (map hcl5_pk_pj l).
Proof. rewrite map_map. apply map_ext. intros [[? ?] ?]. reflexivity. Qed.

Lemma hcl5_pk_addrs_kents fl PS KD : map peer_addr4 (kents_PS fl PS KD) = map peer_addr4 PS.
Proof. rewrite !hcl5_pk_addrs_pj, hcl5_pk_pj_kents. reflexivity. Qed.

Lemma hcl5_pk_Forall_pj (Q: val * share * peer -> Prop) l1 l2 :
  map hcl5_pk_pj l1 = map hcl5_pk_pj l2 -> (forall x y, hcl5_pk_pj x = hcl5_pk_pj y -> Q x -> Q y) ->
  Forall Q l1 -> Forall Q l2.
Proof.
  intros Hm HQ H. revert l2 Hm. induction H as [| x l1 Hx H IH]; intros [| y l2] Hm; simpl in Hm;
    try discriminate; constructor.
  - inv Hm. eapply HQ; eauto.
  - inv Hm. auto.
Qed.

Lemma hcl5_pk_chain_pj h l1 l2 :
  map hcl5_pk_pj l1 = map hcl5_pk_pj l2 -> pk_chain h l1 -> pk_chain h l2.
Proof.
  revert h l2. induction l1 as [| [[a sh] P] l1 IH]; intros h [| [[b sh'] P'] l2] Hm; simpl in *;
    try discriminate; auto.
  injection Hm as -> -> _ _ _ E4 Hm. intros [Hh Hc]. split; auto. rewrite <- E4. eapply IH; eauto.
Qed.

Lemma hcl5_pk_pok_pj L x y :
  hcl5_pk_pj x = hcl5_pk_pj y -> hcl5_pok L x -> hcl5_pok L y.
Proof.
  destruct x as [[a sh] P], y as [[b sh'] P']. simpl. intros Heq.
  injection Heq as -> -> E1 E2 E3 E4. unfold hcl5_pok.
  rewrite <- E1, <- E2, <- E3. auto.
Qed.

Lemma hcl5_pk_slots_cons e KE PS : hcl5_slots_ok KE PS -> hcl5_slots_ok (e :: KE) PS.
Proof.
  unfold hcl5_slots_ok. apply Forall_impl. intros [[a sh] P] H.
  eapply Forall_impl; [| exact H]. intros k Hk. simpl in Hk |- *. tauto.
Qed.

Lemma hcl5_pk_slots_fill KE PS d :
  hcl5_slots_ok KE PS -> hcl5_slots_ok (kd_kent d :: KE) (fill_peers PS d).
Proof.
  intros H. pose proof (hcl5_pk_slots_cons (kd_kent d) _ _ H) as H'. clear H.
  unfold hcl5_slots_ok, fill_peers in *. rewrite Forall_map.
  eapply Forall_impl; [| exact H']. intros [[a sh] P] HP. unfold Basics.compose. cbv beta iota.
  assert (Hd: kd_addr d = nullval \/ In (kd_addr d) (map ke_addr (kd_kent d :: KE))) by (simpl; auto).
  rewrite !Forall_cons_iff in HP. destruct HP as (H1 & H2 & H3 & _).
  match goal with |- context [if ?c then _ else _] => destruct c end; [unfold fill_slot |];
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; simpl;
  repeat (apply Forall_cons; [first [exact H1 | exact H2 | exact H3 | exact Hd] |]); apply Forall_nil.
Qed.

Lemma hcl5_pk_slots_kents PS KD :
  hcl5_slots_ok [] PS -> hcl5_slots_ok (map kd_kent KD) (kents_PS true PS KD).
Proof.
  intros H. induction KD as [| d KD IH]; simpl; auto. apply hcl5_pk_slots_fill; auto.
Qed.

Lemma hcl5_pk_khead KD : hcl5_khead (map kd_kent KD) = kents_head KD.
Proof. destruct KD; reflexivity. Qed.

Lemma hcl5_pk_inv L NS PS T KD head :
  hcl5_inv L NS PS [] T head -> kents_draws_ok PS KD -> itable_wf (kents_T T KD) ->
  hcl5_inv L NS (kents_PS true PS KD) (map kd_kent KD) (kents_T T KD) head.
Proof.
  intros (Hpok & Hwf & Hch & Hnp & HT & Hsl) [HKD HND] Hwf'.
  pose proof (hcl5_pk_pj_kents true PS KD) as Hpj. symmetry in Hpj.
  pose proof (hcl5_pk_addrs_kents true PS KD) as Had.
  destruct HT as (HTa & HTs & HTp & _).
  split; [| split; [| split; [| split; [| split]]]].
  - eapply hcl5_pk_Forall_pj; [exact Hpj | | exact Hpok]. apply hcl5_pk_pok_pj.
  - eapply hcl5_pk_Forall_pj; [exact Hpj | | exact Hwf].
    intros [[a sh] P] [[b sh'] P'] Heq; simpl in Heq. injection Heq as -> -> _ _ _ _. auto.
  - eapply hcl5_pk_chain_pj; eauto.
  - unfold hnodes_peers4 in *. rewrite Had. exact Hnp.
  - unfold hcl5_T_ok. rewrite Had, hcl5_pk_saddrs_kents, HTa. simpl.
    rewrite map_map. simpl.
    assert (Hdis: forall x, In x PS -> ~ In (hs_addr (peer_addr4 x)) (map kd_addr KD)).
    { destruct Hwf' as (_ & _ & Hnd & _). rewrite hcl5_pk_saddrs_kents, HTa in Hnd. simpl in Hnd.
      apply NoDup_app in Hnd. destruct Hnd as (_ & _ & Hnd).
      intros x Hx Hin. apply (Hnd _ Hin).
      apply (in_map (fun x => hs_addr (peer_addr4 x))) in Hx. exact Hx. }
    split; [rewrite <- (map_map peer_addr4 hs_addr (kents_PS true PS KD)), Had, map_map; reflexivity | split; [| split]].
    + apply hcl5_pk_shares_kents; auto.
    + (* the peers' entries *)
      assert (Hp': Forall (fun x => e_peer (t_entry_d (kents_T T KD) (hs_addr (peer_addr4 x))) = peer_addr4 x) PS).
      { rewrite Forall_forall in HTp |- *. intros x Hx.
        rewrite hcl5_pk_epeer_kents_out by (apply Hdis; auto). auto. }
      eapply hcl5_pk_Forall_pj; [exact Hpj | | exact Hp'].
      intros [[a sh] P] [[b sh'] P'] Heq; simpl in Heq. injection Heq as -> -> _ _ _ _. auto.
    + rewrite Forall_map. simpl.
      apply hcl5_pk_epeer_kents_in. eapply Forall_impl; [| exact HKD]. simpl; tauto.
  - apply hcl5_pk_slots_kents; auto.
Qed.

Lemma hcl5_pk_owners NS PS :
  hnodes_peers4 NS PS -> NS <> [] -> hcl5_head NS <> nullval ->
  kents_owners_ok (hcl5_head NS) nullval NS PS.
Proof.
  intros Hnp Hne Hh. unfold kents_owners_ok. destruct NS as [| N NS]; [congruence |].
  simpl hcl5_head in *. rewrite if_false by exact Hh. split; [discriminate | auto].
Qed.

Lemma hcl5_pk_head_ptr NS :
  hnodes_rep4 W (hcl5_head NS) NS |--
  !! (is_pointer_or_null (hcl5_head NS) /\ (NS <> [] -> hcl5_head NS <> nullval)).
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

Lemma hcl5_PK_ok {Espec: OracleKind} gv L FR :
  hcl5_hyps x25519 ->
  semax (hcl5_Delta x25519) (hcl5_SB x25519 gv L FR) hcl5_PK
    (overridePost (hcl5_SK x25519 gv L FR) (hcl5_R gv)).
Proof.
  intros HH. unfold hcl5_SB, hcl5_Delta, hcl5_R, hcl5_PK. simplify_func_tycontext.
  Intros R S w NS PS T head.
  abbreviate_semax.
  unfold hcl5_world, hcl5_globs, hcl5_lvars, hcl5_snaps0, hcl5_scr; cbn [app].
  assert_PROP (is_pointer_or_null (hcl5_head NS) /\ (NS <> [] -> hcl5_head NS <> nullval)) as Hhd
    by (sep_apply (hcl5_pk_head_ptr NS); entailer!).
  destruct Hhd as [Hhp Hhn].
  match goal with H: hcl5_inv _ _ _ _ _ _ |- _ => pose proof H as Hinv end.
  forward.
  forward_call (gv, Tsh, l_it L, T, hcl5_head NS, NS, nullval, PS, Int.one, S, w).
  { destruct Hinv as (_ & Hwf & _ & Hnp & _ & Hsl). split; [auto |]. split; [apply hcl5_pk_owners; auto |].
    (* v4.1: the owners' slots are NULL (no kent yet) *)
    unfold hcl5_slots_ok in Hsl. eapply Forall_impl; [| exact Hsl].
    intros [[a sh] P] HP. eapply Forall_impl; [| exact HP].
    intros k [Hk | Hk]; [left; exact Hk | contradiction]. }
  Intros KD.
  assert_PROP (itable_wf (kents_T T KD)) as Hwf' by (unfold itable; entailer!).
  forward.
  change (negb (Int.eq Int.one Int.zero)) with true.
  unfold hcl5_SK.
  Exists R (kents_S S KD) w NS (kents_PS true PS KD) (kents_T T KD) head (map kd_kent KD).
  rewrite hcl5_pk_khead.
  unfold hcl5_world, hcl5_globs, hcl5_lvars, hcl5_snaps0, hcl5_scr; cbn [app].
  entailer!.
  apply hcl5_pk_inv; auto.
Qed.

End PK.
