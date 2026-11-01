(* law keypairs, prologue A, piece 3a: statement 18 (kes = kents_add(&t, others, NULL, 1)).
   States: hkp5_segA_defs.v. "Prologue A".
*)
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
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.keypairs.hkp5_op1.
Require Import WgNoise.proof.harness.keypairs.hkp5_spec.
Require Import WgNoise.proof.harness.keypairs.hkp5_segA_defs.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* pure lemmas (after hci5_PK): the table after kents_add                    *)
(* ---------------------------------------------------------------------- *)

Lemma hkp5A3a_sfind_supd_ne {A: Type} (l: list (val * share * A)) a b v :
  b <> a -> sfind (supd l a v) b = sfind l b.
Proof.
  intros Hne. induction l as [| [[x sh] u] l IH]; simpl; auto.
  destruct (EqDec_val x a) as [-> | Hxa]; simpl.
  - destruct (EqDec_val a b); [congruence | reflexivity].
  - destruct (EqDec_val x b); auto.
Qed.

Lemma hkp5A3a_saddrs_supd {A: Type} (l: list (val * share * A)) a v : saddrs (supd l a v) = saddrs l.
Proof.
  induction l as [| [[x sh] u] l IH]; simpl; auto.
  destruct (EqDec_val x a); simpl; f_equal; auto.
Qed.

(* one step of kents_T, unfolded *)
Lemma hkp5A3a_step T a E idx :
  t_insert (t_add T a Ews E) a idx =
  mkT ((a, Ews, mkEntry (e_peer E) (e_type E) idx) :: t_D T) (a :: vremove a (t_L T)).
Proof.
  unfold t_insert, t_set_index, t_entry, t_add, t_upd; simpl.
  destruct (EqDec_val a a); [| congruence]. simpl. destruct (EqDec_val a a); [| congruence]. reflexivity.
Qed.

Lemma hkp5A3a_saddrs_kents T KD : saddrs (t_D (kents_T T KD)) = map kd_addr KD ++ saddrs (t_D T).
Proof.
  induction KD as [| d KD IH]; cbn [kents_T map app]; auto.
  rewrite hkp5A3a_step. simpl. f_equal. exact IH.
Qed.

Lemma hkp5A3a_sfind_kents_out T KD b :
  ~ In b (map kd_addr KD) -> sfind (t_D (kents_T T KD)) b = sfind (t_D T) b.
Proof.
  induction KD as [| d KD IH]; cbn [kents_T map In]; auto. intros Hn.
  rewrite hkp5A3a_step. simpl. destruct (EqDec_val (kd_addr d) b); [tauto |]. apply IH; tauto.
Qed.

Lemma hkp5A3a_entry_kents_out T KD b :
  ~ In b (map kd_addr KD) -> t_entry_d (kents_T T KD) b = t_entry_d T b.
Proof. intros Hn. unfold t_entry_d, t_entry. rewrite hkp5A3a_sfind_kents_out; auto. Qed.

Lemma hkp5A3a_epeer_kents_in T KD (own: list val) :
  Forall (fun d => In (kd_owner d) own) KD ->
  Forall (fun d => In (e_peer (t_entry_d (kents_T T KD) (kd_addr d))) own) KD.
Proof.
  induction KD as [| d KD IH]; cbn [kents_T]; intros H; auto. inv H. constructor.
  - rewrite hkp5A3a_step. unfold t_entry_d, t_entry; simpl. destruct (EqDec_val (kd_addr d) (kd_addr d)); [| congruence].
    simpl. auto.
  - specialize (IH H3). eapply Forall_impl; [| exact IH]. intros d0 H0.
    rewrite hkp5A3a_step. unfold t_entry_d, t_entry in *; simpl.
    destruct (EqDec_val (kd_addr d) (kd_addr d0)) as [E|]; auto.
Qed.

Lemma hkp5A3a_vremove_notin a L : ~ In a (vremove a L).
Proof.
  induction L as [|x L IH]; simpl; auto.
  destruct (EqDec_val x a); simpl; auto. intros [H|H]; auto.
Qed.

Lemma hkp5A3a_vremove_in a L b : In b (vremove a L) -> In b L.
Proof.
  induction L as [|x L IH]; simpl; auto.
  destruct (EqDec_val x a); simpl; intros; [right; auto | destruct H; auto].
Qed.

Lemma hkp5A3a_nodup_map {B: Type} (f: val -> B) a L : NoDup (map f L) -> NoDup (map f (vremove a L)).
Proof.
  induction L as [|x L IH]; simpl; auto.
  intros Hn. inversion Hn; subst.
  destruct (EqDec_val x a); simpl; auto.
  constructor; auto.
  intros Hin. apply H1. apply in_map_iff in Hin. destruct Hin as [y [Hy Hin]].
  apply in_map_iff. exists y. split; auto. eapply hkp5A3a_vremove_in; eauto.
Qed.

Lemma hkp5A3a_indices_cons D a sh E L1 L2 L :
  ~ In a L -> t_indices (mkT ((a, sh, E) :: D) L1) L = t_indices (mkT D L2) L.
Proof.
  intros Hn. unfold t_indices, t_entry. simpl. apply map_ext_in. intros b Hb.
  destruct (EqDec_val a b); auto. subst; contradiction.
Qed.

Lemma hkp5A3a_indices_kents T KD :
  NoDup (t_indices T (t_L T)) -> kents_fresh T KD ->
  NoDup (t_indices (kents_T T KD) (t_L (kents_T T KD))).
Proof.
  intros H0. induction KD as [| d KD IH]; cbn [kents_T kents_fresh]; auto.
  intros [Hf Hfr]. rewrite hkp5A3a_step in *. simpl.
  unfold t_indices at 1. simpl. unfold t_entry at 1. simpl.
  destruct (EqDec_val (kd_addr d) (kd_addr d)); [| congruence]. simpl.
  fold (t_indices (mkT ((kd_addr d, Ews, mkEntry (kd_owner d) IDX_KEYPAIR (kd_idx d)) :: t_D (kents_T T KD))
                       (kd_addr d :: vremove (kd_addr d) (t_L (kents_T T KD)))) (vremove (kd_addr d) (t_L (kents_T T KD)))).
  rewrite (hkp5A3a_indices_cons _ _ _ _ _ (t_L (kents_T T KD))) by apply hkp5A3a_vremove_notin.
  unfold t_fresh, t_add in Hfr. simpl in Hfr.
  rewrite (hkp5A3a_indices_cons _ _ _ _ _ (t_L (kents_T T KD))) in Hfr by apply hkp5A3a_vremove_notin.
  constructor.
  - destruct (kents_T T KD); exact Hfr.
  - specialize (IH Hf). destruct (kents_T T KD) as [D L]. apply hkp5A3a_nodup_map. exact IH.
Qed.

(* ---------------------------------------------------------------------- *)
(* pure lemmas: the peers after kents_add (only slots change)               *)
(* ---------------------------------------------------------------------- *)

Definition hkp5A3a_pj (x: val * share * peer) :=
  match x with (a, sh, P) => (a, sh, p_device P, p_hs P, p_refs P, p_pknext P) end.

Lemma hkp5A3a_pj_kents fl PS KD : map hkp5A3a_pj (kents_PS fl PS KD) = map hkp5A3a_pj PS.
Proof.
  induction KD as [| d KD IH]; simpl; auto. destruct fl; auto.
  unfold fill_peers. rewrite map_map, <- IH. apply map_ext. intros [[x sh] P].
  destruct (eq_dec x (kd_owner d)); auto. unfold fill_slot.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

Lemma hkp5A3a_addrs_pj l :
  map peer_addr4 l = map (fun y => match y with (a, _, _, _, _, _) => a end) (map hkp5A3a_pj l).
Proof. rewrite map_map. apply map_ext. intros [[? ?] ?]. reflexivity. Qed.

Lemma hkp5A3a_addrs_kents fl PS KD : map peer_addr4 (kents_PS fl PS KD) = map peer_addr4 PS.
Proof. rewrite !hkp5A3a_addrs_pj, hkp5A3a_pj_kents. reflexivity. Qed.

Lemma hkp5A3a_Forall_pj (Q: val * share * peer -> Prop) l1 l2 :
  map hkp5A3a_pj l1 = map hkp5A3a_pj l2 -> (forall x y, hkp5A3a_pj x = hkp5A3a_pj y -> Q x -> Q y) ->
  Forall Q l1 -> Forall Q l2.
Proof.
  intros Hm HQ H. revert l2 Hm. induction H as [| x l1 Hx H IH]; intros [| y l2] Hm; simpl in Hm;
    try discriminate; constructor.
  - inv Hm. eapply HQ; eauto.
  - inv Hm. auto.
Qed.

(* the other peers' conditions of hkp5A_inv *)
Definition hkp5A3a_pok (w p: val) (pa ka: list val) (x: val * share * peer) : Prop :=
  match x with (q, _, Q) =>
     p_device Q = w /\ hs_sid (p_hs Q) = id_addr w /\ 0 < Int.unsigned (p_refs Q) < 2147483647 /\
     Forall (vp_ok ka) [p_cur Q; p_prev Q; p_next Q] /\ vp_ok (p :: pa) (p_pknext Q) end.

Lemma hkp5A3a_pok_fill w p pa ka d PS :
  Forall (hkp5A3a_pok w p pa ka) PS -> Forall (hkp5A3a_pok w p pa (kd_addr d :: ka)) (fill_peers PS d).
Proof.
  intros H. unfold fill_peers. rewrite Forall_map. eapply Forall_impl; [| exact H].
  intros [[a sh] P] (H1 & H2 & H3 & H4 & H5). unfold Basics.compose. cbv beta iota.
  assert (Hv: forall x, vp_ok ka x -> vp_ok (kd_addr d :: ka) x) by (unfold vp_ok; simpl; tauto).
  assert (Hd: vp_ok (kd_addr d :: ka) (kd_addr d)) by (unfold vp_ok; simpl; auto).
  rewrite !Forall_cons_iff in H4. destruct H4 as (K1 & K2 & K3 & _).
  match goal with |- context [if ?c then _ else _] => destruct c end; [unfold fill_slot |];
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; simpl;
  (split; [assumption | split; [assumption | split; [assumption | split; [| assumption]]]]);
  repeat (apply Forall_cons; [first [exact Hd | apply Hv; assumption] |]); apply Forall_nil.
Qed.

Lemma hkp5A3a_pok_kents w p pa PS KD :
  Forall (hkp5A3a_pok w p pa []) PS ->
  Forall (hkp5A3a_pok w p pa (map ke_addr (map kd_kent KD))) (kents_PS true PS KD).
Proof.
  intros H. induction KD as [| d KD IH]; simpl; auto. apply hkp5A3a_pok_fill; auto.
Qed.

Lemma hkp5A3a_khead KD : hkp5A_khead (map kd_kent KD) = kents_head KD.
Proof. destruct KD; reflexivity. Qed.

Lemma hkp5A3a_ka KD : map ke_addr (map kd_kent KD) = map kd_addr KD.
Proof. rewrite map_map. reflexivity. Qed.

Lemma hkp5A3a_sh_kents a0 T KD :
  Forall (fun d => match d with (a, sh, _) => a = a0 \/ sh = Ews end) (t_D T) ->
  Forall (fun d => match d with (a, sh, _) => a = a0 \/ sh = Ews end) (t_D (kents_T T KD)).
Proof.
  intros H. induction KD as [| d KD IH]; cbn [kents_T]; auto.
  rewrite hkp5A3a_step. cbn [t_D]. constructor; [right; reflexivity | exact IH].
Qed.

Lemma hkp5A3a_inv F P NS PS T head KD :
  hkp5A_inv F P NS PS [] T head -> kents_draws_ok PS KD -> kents_fresh T KD -> itable_wf (kents_T T KD) ->
  Forall isptr (map kd_addr KD) ->
  hkp5A_inv F P NS (kents_PS true PS KD) (map kd_kent KD) (kents_T T KD) head.
Proof.
  intros (Hp & Hd & Hs & Hc & Hpr & Hn & Hk & Hnp & Hwf & Hnd & Hpa & _ & Hok & Hh & Ha & Hsf & Hpe & _ & Hi & Hsh1 & Hsh2)
    [HKD HND] Hfr Hwf' Hka.
  pose proof (hkp5A3a_pj_kents true PS KD) as Hpj. symmetry in Hpj.
  pose proof (hkp5A3a_addrs_kents true PS KD) as Had.
  assert (Hdis: forall b, In b (saddrs (t_D T)) -> ~ In b (map kd_addr KD)).
  { destruct Hwf' as (_ & _ & Hnd' & _). rewrite hkp5A3a_saddrs_kents in Hnd'.
    apply NoDup_app in Hnd'. destruct Hnd' as (_ & _ & Hnd'). intros b Hb Hin. exact (Hnd' _ Hin Hb). }
  rewrite Ha in Hdis.
  unfold hkp5A_inv. rewrite Had, hkp5A3a_ka.
  split; [exact Hp |]. split; [exact Hd |]. split; [exact Hs |]. split; [exact Hc |]. split; [exact Hpr |].
  split; [exact Hn |]. split; [exact Hk |]. split; [| split; [| split; [exact Hnd |]]].
  3: split; [exact Hpa |]. 3: split; [exact Hka |]. 3: split; [| split; [exact Hh |]].
  4: split; [| split; [| split; [| split]]].
  - unfold hnodes_peers4 in *. rewrite Had. exact Hnp.
  - eapply hkp5A3a_Forall_pj; [exact Hpj | | exact Hwf].
    intros [[a sh] Q] [[b sh'] Q'] Heq; simpl in Heq. injection Heq as -> -> _ _ _ _. auto.
  - pose proof (hkp5A3a_pok_kents (f_w F) (f_p F) (map peer_addr4 PS) PS KD) as HH.
    rewrite hkp5A3a_ka in HH. apply HH. eapply Forall_impl; [| exact Hok].
    intros [[a sh] Q] (H1 & H2 & H3 & H4 & H5). unfold hkp5A3a_pok. auto.
  - rewrite hkp5A3a_saddrs_kents, Ha. reflexivity.
  - rewrite hkp5A3a_sfind_kents_out; auto. apply Hdis. apply in_app_iff; right; apply in_app_iff; right; left; auto.
  - rewrite Forall_forall in Hpe |- *. intros q Hq.
    rewrite hkp5A3a_entry_kents_out; auto. apply Hdis. apply in_app_iff; right; apply in_app_iff; left.
    apply in_map; auto.
  - rewrite Forall_map. simpl. apply hkp5A3a_epeer_kents_in. eapply Forall_impl; [| exact HKD]. simpl; tauto.
  - split; [apply hkp5A3a_indices_kents; auto |]. split.
    + eapply hkp5A3a_Forall_pj; [exact Hpj | | exact Hsh1].
      intros [[a sh] Q] [[b sh'] Q'] Heq; simpl in Heq. injection Heq as -> -> _ _ _ _. auto.
    + apply hkp5A3a_sh_kents. exact Hsh2.
Qed.

(* ---------------------------------------------------------------------- *)
(* separation lemmas                                                       *)
(* ---------------------------------------------------------------------- *)

Lemma hkp5A3a_owners NS PS :
  hnodes_peers4 NS PS -> (NS <> [] -> hkp5A_nhead NS <> nullval) ->
  kents_owners_ok (hkp5A_nhead NS) nullval NS PS.
Proof.
  intros Hnp Hh. unfold kents_owners_ok. destruct NS as [| N NS].
  - unfold hnodes_peers4 in Hnp. simpl in Hnp |- *. split; auto.
  - simpl hkp5A_nhead in *. rewrite if_false by (apply Hh; discriminate). split; [discriminate | auto].
Qed.

Lemma hkp5A3a_head_ptr NS :
  hnodes_rep4 W_keypairs (hkp5A_nhead NS) NS |--
  !! (is_pointer_or_null (hkp5A_nhead NS) /\ (NS <> [] -> hkp5A_nhead NS <> nullval)).
Proof.
  destruct NS as [| N NS]; simpl.
  - apply prop_right. split; [reflexivity | congruence].
  - Intros nx. entailer!.
    match goal with H: field_compatible _ _ (hn_addr N) |- _ => destruct H as [Hp _] end.
    split; [apply isptr_is_pointer_or_null; auto |].
    intros _ E. rewrite E in Hp. inv Hp.
Qed.

Lemma hkp5A3a_kents_ptr l KE :
  kents_rep W_keypairs l KE |-- !! Forall isptr (map ke_addr KE).
Proof.
  revert l; induction KE as [| e KE IH]; intros l; simpl.
  - entailer!.
  - Intros nx. unfold kent_cell. Intros. sep_apply (IH nx). entailer!.
    match goal with H: field_compatible _ _ (ke_addr e) |- _ => destruct H as [Hp _] end. auto.
Qed.

Lemma hkp5A_3a_ok {Espec: OracleKind} x25519 (F: hkp5_fix) (FR: mpred) R :
  x25519_props x25519 ->
  semax (hkp5_Delta (hkp5_G_A x25519)) (hkp5A_S2 x25519 F FR) hkp5A_s3a (overridePost (hkp5A_SK x25519 F FR) R).
Proof.
  intros Hx. unfold hkp5A_S2, hkp5A_s3a, hkp5_Delta.
  destruct R as [Rn Rb Rc Rr]. unfold overridePost.
  Intros RA P S w NS PS T head.
  unfold hkp5A_world, hkp5A_oth, hkp5A_globs, hkp5A_snaps0, hkp5_lvars, hkp5A_temps, hk5_items; cbn [app].
  assert_PROP (is_pointer_or_null (hkp5A_nhead NS) /\ (NS <> [] -> hkp5A_nhead NS <> nullval)) as Hhd
    by (sep_apply (hkp5A3a_head_ptr NS); entailer!).
  destruct Hhd as [Hhp Hhn].
  abbreviate_semax.
  forward.
  forward_call (f_gv F, Tsh, f_t F, T, hkp5A_nhead NS, NS, nullval, PS, Int.one, S, w).
  { destruct H1 as (_ & _ & _ & _ & _ & _ & _ & Hnp & Hwf & _ & _ & _ & Hok & _).
    split; [exact Hwf |]. split; [apply hkp5A3a_owners; auto |].
    eapply Forall_impl; [| exact Hok]. intros [[a sh] Q] (_ & _ & _ & H4 & _).
    eapply Forall_impl; [| exact H4]. intros k [Hk | Hk]; [left; exact Hk | contradiction]. }
  Intros KD.
  assert_PROP (itable_wf (kents_T T KD)) as Hwf' by (unfold itable; entailer!).
  assert_PROP (Forall isptr (map ke_addr (map kd_kent KD))) as Hka
    by (sep_apply (hkp5A3a_kents_ptr (kents_head KD) (map kd_kent KD)); entailer!).
  forward.
  change (negb (Int.eq Int.one Int.zero)) with true.
  unfold hkp5A_SK. simpl RA_normal.
  Exists RA P (kents_S S KD) w NS (kents_PS true PS KD) (map kd_kent KD) (kents_T T KD) head.
  unfold hkp5A_world, hkp5A_oth, hkp5A_kes, hkp5A_globs, hkp5A_snaps0, hkp5_lvars, hkp5A_temps, hk5_items; cbn [app].
  rewrite hkp5A3a_khead.
  entailer!.
  apply hkp5A3a_inv; auto. rewrite <- hkp5A3a_ka. exact Hka.
Qed.
