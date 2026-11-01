(* law keypairs, prologue A, piece 2b: statement 17 (the loop over others: hs_randomize, peer_randomize_rest, maybe wg_index_hashtable_insert).
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

Require Import VST.msl.iter_sepcon.

#[local] Instance hkp5A2b_cceK : change_composite_env CKS W_keypairs.
Proof. make_cs_preserve CKS W_keypairs. Defined.

(* ---------------------------------------------------------------------- *)
(* the index table                                                         *)
(* ---------------------------------------------------------------------- *)

Lemma hkp5A2b_sfind_other {A: Type} (D: list (val * share * A)) a b v :
  b <> a -> sfind (supd D a v) b = sfind D b.
Proof.
  intros Hne. induction D as [|[[x sh] w] D IH]; simpl; auto.
  destruct (EqDec_val x a); simpl; destruct (EqDec_val x b); subst; try congruence; auto.
Qed.

Lemma hkp5A2b_sfind_same {A: Type} (D: list (val * share * A)) a sh v w :
  sfind D a = Some (sh, w) -> sfind (supd D a v) a = Some (sh, v).
Proof.
  induction D as [|[[x sh'] w'] D IH]; simpl; [discriminate|].
  destruct (EqDec_val x a); subst; simpl.
  - intros Hs; inversion Hs; subst. destruct (EqDec_val a a); [auto|congruence].
  - intros Hs. destruct (EqDec_val x a); [congruence|]. auto.
Qed.

Lemma hkp5A2b_saddrs {A: Type} (D: list (val * share * A)) a v : saddrs (supd D a v) = saddrs D.
Proof.
  induction D as [|[[x sh] w] D IH]; simpl; auto.
  destruct (EqDec_val x a); simpl; auto. unfold saddrs in IH |- *. simpl. f_equal. exact IH.
Qed.

Lemma hkp5A2b_sfind_in {A: Type} (D: list (val * share * A)) a :
  In a (saddrs D) -> exists sh v, sfind D a = Some (sh, v).
Proof.
  induction D as [|[[x sh] w] D IH]; simpl; [tauto|].
  intros [-> | H].
  - exists sh, w. destruct (EqDec_val a a); [reflexivity | congruence].
  - destruct (EqDec_val x a); [eauto | auto].
Qed.

Lemma hkp5A2b_vremove_notin a L : ~ In a (vremove a L).
Proof.
  induction L as [|x L IH]; simpl; auto.
  destruct (EqDec_val x a); simpl; auto. intros [Hx|Hx]; [congruence|auto].
Qed.

Lemma hkp5A2b_vremove_in a L b : b <> a -> (In b (vremove a L) <-> In b L).
Proof.
  intros Hne. induction L as [|x L IH]; simpl; [tauto|].
  destruct (EqDec_val x a); subst; simpl; [|rewrite IH]; split; intros; try tauto.
  destruct H as [H|H]; [congruence|tauto].
Qed.

Lemma hkp5A2b_nodup_map {B: Type} (f: val -> B) a L : NoDup (map f L) -> NoDup (map f (vremove a L)).
Proof.
  induction L as [|x L IH]; simpl; auto.
  intros Hn. inversion Hn; subst.
  destruct (EqDec_val x a); simpl; auto.
  constructor; auto.
  intros Hin. apply H1. apply in_map_iff in Hin. destruct Hin as [y [Hy Hin]].
  apply in_map_iff. exists y. split; auto.
  destruct (EqDec_val y a) as [->|Hya]; [exfalso; exact (hkp5A2b_vremove_notin a L Hin)|].
  apply (hkp5A2b_vremove_in a L y Hya). auto.
Qed.

Lemma hkp5A2b_indices D a v L1 L2 L :
  ~ In a L -> t_indices (mkT (supd D a v) L1) L = t_indices (mkT D L2) L.
Proof.
  intros Hn. unfold t_indices, t_entry. simpl. apply map_ext_in. intros b Hb.
  rewrite hkp5A2b_sfind_other; auto. intros ->. auto.
Qed.

Lemma hkp5A2b_entry_insert T a idx b :
  e_peer (t_entry_d (t_insert T a idx) b) = e_peer (t_entry_d T b) /\
  e_type (t_entry_d (t_insert T a idx) b) = e_type (t_entry_d T b).
Proof.
  unfold t_entry_d, t_insert, t_set_index, t_upd, t_entry. cbn [t_D t_L].
  destruct (sfind (t_D T) a) as [[sh E] |] eqn:Ha; cbn [t_D]; [| auto].
  destruct (EqDec_val b a) as [-> | Hne].
  - rewrite (hkp5A2b_sfind_same _ _ _ _ _ Ha), Ha. auto.
  - rewrite hkp5A2b_sfind_other by auto. auto.
Qed.

Lemma hkp5A2b_hs_inj p q : isptr p -> isptr q -> hs_addr q = hs_addr p -> q = p.
Proof.
  intros Hp Hq H. destruct p, q; try contradiction. unfold hs_addr, offset_val in H.
  assert (Hb: b0 = b) by congruence.
  assert (Hi: Ptrofs.add i0 (Ptrofs.repr OFS_PEER_HANDSHAKE) = Ptrofs.add i (Ptrofs.repr OFS_PEER_HANDSHAKE))
    by congruence.
  subst b0. f_equal.
  apply (f_equal (fun x => Ptrofs.sub x (Ptrofs.repr OFS_PEER_HANDSHAKE))) in Hi.
  rewrite !Ptrofs.sub_add_opp, !Ptrofs.add_assoc, !Ptrofs.add_neg_zero, !Ptrofs.add_zero in Hi.
  exact Hi.
Qed.

Lemma hkp5A2b_supd_sh (Pr: val -> share -> Prop) (D: list (val * share * entry)) a v :
  Forall (fun d => match d with (x, sh, _) => Pr x sh end) D ->
  Forall (fun d => match d with (x, sh, _) => Pr x sh end) (supd D a v).
Proof.
  induction D as [| [[x sh] u] D IH]; intros H; [constructor |]. inversion H; subst. cbn.
  match goal with |- context [if ?c then _ else _] => destruct c end; constructor; auto.
Qed.

Lemma hkp5A2b_inv_insert F P NS PS T head q idx :
  hkp5A_inv F P NS PS [] T head -> In q (map peer_addr4 PS) -> t_fresh T (hs_addr q) idx ->
  hkp5A_inv F P NS PS [] (t_insert T (hs_addr q) idx) head.
Proof.
  intros Hinv Hq Hfr.
  destruct Hinv as (Hp & H1 & H2 & H3 & H4 & H5 & H6 & Hnp & Hwf & Hnd & Hpa & Hka & Hps & Hhead & Hsa & Hsp &
                    Hpe & Hke & Hidx & Hsh1 & Hsh2).
  assert (Hin: In (hs_addr q) (saddrs (t_D T))).
  { rewrite Hsa. cbn [map app]. apply in_or_app. left. apply in_map, Hq. }
  destruct (hkp5A2b_sfind_in _ _ Hin) as (sh & E & Hs).
  assert (Ht: t_insert T (hs_addr q) idx =
    mkT (supd (t_D T) (hs_addr q) (mkEntry (e_peer E) (e_type E) idx)) (hs_addr q :: vremove (hs_addr q) (t_L T))).
  { unfold t_insert, t_set_index, t_upd, t_entry. rewrite Hs. reflexivity. }
  assert (Hqp: hs_addr q <> hs_addr (f_p F)).
  { intros He. apply hkp5A2b_hs_inj in He; [| exact Hp |].
    - subst q. inversion Hnd; subst. contradiction.
    - rewrite Forall_forall in Hpa. apply Hpa, Hq. }
  unfold hkp5A_inv. cbv zeta.
  refine (conj Hp (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj Hnp (conj Hwf (conj Hnd
    (conj Hpa (conj Hka (conj Hps (conj Hhead _)))))))))))))).
  split; [| split; [| split; [| split]]].
  5: split.
  6: { split; [exact Hsh1 |]. rewrite Ht. cbn [t_D].
       apply (hkp5A2b_supd_sh (fun x sh => x = hs_addr (f_p F) \/ sh = Ews)). exact Hsh2. }
  - rewrite Ht. cbn [t_D]. rewrite hkp5A2b_saddrs. exact Hsa.
  - rewrite Ht. cbn [t_D]. rewrite hkp5A2b_sfind_other by congruence. exact Hsp.
  - eapply Forall_impl; [| exact Hpe]. intros a [Ha1 Ha2].
    destruct (hkp5A2b_entry_insert T (hs_addr q) idx (hs_addr a)) as [E1 E2]. rewrite E1, E2. auto.
  - constructor.
  - rewrite Ht. unfold t_indices at 1. cbn [map t_D t_L]. unfold t_entry at 1. cbn [t_D].
    rewrite (hkp5A2b_sfind_same _ _ _ _ _ Hs).
    fold (t_indices (mkT (supd (t_D T) (hs_addr q) (mkEntry (e_peer E) (e_type E) idx))
                         (hs_addr q :: vremove (hs_addr q) (t_L T))) (vremove (hs_addr q) (t_L T))).
    rewrite (hkp5A2b_indices _ _ _ _ (t_L T)) by apply hkp5A2b_vremove_notin.
    cbn [e_index]. constructor.
    + destruct T as [D L]. exact Hfr.
    + destruct T as [D L]. apply hkp5A2b_nodup_map. exact Hidx.
Qed.

(* ---------------------------------------------------------------------- *)
(* the randomization of one peer                                          *)
(* ---------------------------------------------------------------------- *)

Definition hkp5A2b_rnd (x y: val * share * peer) : Prop :=
  match x, y with (a, sh, P), (a', sh', P') =>
    a' = a /\ sh' = sh /\ p_device P' = p_device P /\ hs_sid (p_hs P') = hs_sid (p_hs P) /\
    p_refs P' = p_refs P /\ p_cur P' = p_cur P /\ p_prev P' = p_prev P /\ p_next P' = p_next P /\
    p_pknext P' = p_pknext P
  end.

Lemma hkp5A2b_rnd_step a sh P st lic eph reph hash ck ts ri dead lsh valid birth cki sent mac1 :
  hkp5A2b_rnd (a, sh, P)
    (a, sh, p_rest_randomized (p_set_hs P (hs_randomized (p_hs P) st lic eph reph hash ck ts ri))
              dead lsh valid birth cki sent mac1).
Proof. cbn. repeat split. Qed.

Lemma hkp5A2b_rnd_map PS PS' : Forall2 hkp5A2b_rnd PS PS' -> map peer_addr4 PS' = map peer_addr4 PS.
Proof.
  induction 1 as [| x y PS PS' Hxy _ IH]; [reflexivity |]. cbn. rewrite IH.
  destruct x as [[a sh] P], y as [[a' sh'] P']; cbn in *. f_equal. tauto.
Qed.

Lemma hkp5A2b_f2_in {A B: Type} (R: A -> B -> Prop) l l' y :
  Forall2 R l l' -> In y l' -> exists x, In x l /\ R x y.
Proof.
  induction 1 as [| x y' l l' Hxy _ IH]; [contradiction |]. intros [-> | Hy].
  - exists x. split; [left; reflexivity | exact Hxy].
  - destruct (IH Hy) as (x' & Hx' & H'). exists x'. split; [right; exact Hx' | exact H'].
Qed.

Lemma hkp5A2b_inv_rnd F P NS PS PS' T head :
  Forall2 hkp5A2b_rnd PS PS' -> hkp5A_inv F P NS PS [] T head -> hkp5A_inv F P NS PS' [] T head.
Proof.
  intros H Hinv. pose proof (hkp5A2b_rnd_map _ _ H) as Hm.
  destruct Hinv as (Hp & H1 & H2 & H3 & H4 & H5 & H6 & Hnp & Hwf & Hnd & Hpa & Hka & Hps & Hhead & Hsa & Hsp &
                    Hpe & Hke & Hidx & Hsh1 & Hsh2).
  unfold hkp5A_inv. cbv zeta. rewrite Hm.
  refine (conj Hp (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj _ (conj _ (conj Hnd
    (conj Hpa (conj Hka (conj _ (conj Hhead (conj Hsa (conj Hsp (conj Hpe (conj Hke (conj Hidx (conj _ Hsh2)))))))))))))))))))).
  - unfold hnodes_peers4 in *. rewrite Hnp, Hm. reflexivity.
  - clear - H Hwf. unfold peers_wf in *. induction H as [| x y PS PS' Hxy _ IH]; [constructor |].
    inversion Hwf; subst. constructor; [| auto].
    destruct x as [[a sh] P], y as [[a' sh'] P']; cbn in *. destruct Hxy as (_ & -> & _). assumption.
  - rewrite Forall_forall in Hps |- *. intros y Hy.
    destruct (hkp5A2b_f2_in _ _ _ _ H Hy) as (x & Hx & Hxy). specialize (Hps x Hx).
    destruct x as [[a sh] P0], y as [[a' sh'] P']; cbn in Hxy |- *.
    destruct Hxy as (_ & _ & -> & -> & -> & -> & -> & -> & ->). exact Hps.
  - clear - H Hsh1. induction H as [| x y PS PS' Hxy _ IH]; [constructor |].
    inversion Hsh1; subst. constructor; [| auto].
    destruct x as [[a sh] P], y as [[a' sh'] P']; cbn in *. destruct Hxy as (_ & -> & _). assumption.
Qed.

(* ---------------------------------------------------------------------- *)
(* the node list: segments                                                *)
(* ---------------------------------------------------------------------- *)

Fixpoint hkp5A2b_seg (l e: val) (NS: list hnode4) : mpred :=
  match NS with
  | [] => !! (l = e) && emp
  | N :: NS' =>
      !! (l = hn_addr N) &&
      EX nx: val,
        @malloc_token W_keypairs Ews t_hnode4 l *
        @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) l *
        @malloc_token W_keypairs Ews t_peer (hn_p N) *
        hkp5A2b_seg nx e NS'
  end.

Lemma hkp5A2b_seg_app l e NS1 NS2 :
  hkp5A2b_seg l e NS1 * hnodes_rep4 W_keypairs e NS2 |-- hnodes_rep4 W_keypairs l (NS1 ++ NS2).
Proof.
  revert l; induction NS1 as [| N NS1 IH]; intros l; simpl.
  - Intros. subst. cancel.
  - Intros nx. Exists nx. entailer!. sep_apply (IH nx). cancel.
Qed.

Lemma hkp5A2b_seg_snoc l e N nx NS1 : e = hn_addr N ->
  hkp5A2b_seg l e NS1 *
  (@malloc_token W_keypairs Ews t_hnode4 e *
   @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) e *
   @malloc_token W_keypairs Ews t_peer (hn_p N)) |--
  hkp5A2b_seg l nx (NS1 ++ [N]).
Proof.
  intros He. revert l; induction NS1 as [| M NS1 IH]; intros l; simpl.
  - Intros. subst. Exists nx. entailer!.
  - Intros nx'. Exists nx'. entailer!. sep_apply (IH nx'). cancel.
Qed.

Lemma hkp5A2b_vp l NS : hnodes_rep4 W_keypairs l NS |-- valid_pointer l.
Proof.
  destruct NS as [| N NS]; simpl.
  - Intros. subst. apply valid_pointer_null.
  - Intros nx. subst.
    sep_apply (@data_at_valid_ptr CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N)).
    { apply readable_nonidentity, writable_readable, writable_Ews. }
    apply sepcon_valid_pointer1, derives_refl.
Qed.

Lemma hkp5A2b_pn l NS : hnodes_rep4 W_keypairs l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [| N NS]; simpl.
  - Intros. subst. entailer!.
  - Intros nx. subst. entailer!.
    match goal with Hf: field_compatible t_hnode4 [] _ |- _ => apply field_compatible_isptr in Hf end.
    destruct (hn_addr N); try contradiction; exact I.
Qed.

#[local] Hint Resolve hkp5A2b_vp : valid_pointer.

Lemma hkp5A2b_node_W v l : @data_at CKS Ews t_hnode4 v l = @data_at W_keypairs Ews t_hnode4 v l.
Proof.
  rewrite (@data_at_change_composite CKS W_keypairs _ Ews t_hnode4 v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

(* the node's value as ONE constant at W (see hci5_P3: a literal tuple mixing reptypes makes Qed slow) *)
Definition hkp5A2b_nv (N: hnode4) (nx: val) : @reptype W_keypairs t_hnode4 :=
  (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))).

Lemma hkp5A2b_node_nv N nx l :
  @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) l =
  @data_at W_keypairs Ews t_hnode4 (hkp5A2b_nv N nx) l.
Proof. unfold hkp5A2b_nv. apply hkp5A2b_node_W. Qed.

Lemma hkp5A2b_seg_snoc_nv l e N nx NS1 : e = hn_addr N ->
  hkp5A2b_seg l e NS1 *
  (@malloc_token W_keypairs Ews t_hnode4 e *
   @data_at W_keypairs Ews t_hnode4 (hkp5A2b_nv N nx) e *
   @malloc_token W_keypairs Ews t_peer (hn_p N)) |--
  hkp5A2b_seg l nx (NS1 ++ [N]).
Proof. intros He. rewrite <- hkp5A2b_node_nv. apply hkp5A2b_seg_snoc, He. Qed.

Lemma hkp5A2b_peers_snoc l y : peers_rep (l ++ [y]) = (peers_rep l * peer_item_rep y)%logic.
Proof. unfold peers_rep. rewrite iter_sepcon_app. simpl. rewrite sepcon_emp. reflexivity. Qed.

(* the items the loop does not touch (but the table and the shim) *)
Definition hkp5A2b_fix x25519 F FR R P S w (NS: list hnode4) T head : list mpred :=
  hkp5A_world x25519 F R P T head ++ hk5_items (f_gv F) hkp5A_H0 ++ hkp5A_snaps0 F ++
  [data_at Ews (tptr t_hnode4) (hkp5A_nhead NS) (f_gv F KC._others);
   data_at_ Ews (tptr (Tstruct KC._kent noattr)) (f_gv F KC._kes)] ++
  hkp5A_globs (f_gv F) S w ++ [FR].

Lemma hkp5A_2b_ok {Espec: OracleKind} x25519 (F: hkp5_fix) (FR: mpred) R :
  x25519_props x25519 ->
  semax (hkp5_Delta (hkp5_G_A x25519)) (hkp5A_S2 x25519 F FR) hkp5A_s2b (overridePost (hkp5A_S2 x25519 F FR) R).
Proof.
  intros HX. destruct R as [Rn Rb Rc Rr]. unfold overridePost. unfold hkp5_Delta, hkp5A_s2b. unfold hkp5A_S2 at 1. simplify_func_tycontext. abbreviate_semax.
  Intros RR P S w NS PS T head.
  unfold hkp5A_oth, hkp5A_world, hk5_items, hkp5A_snaps0, hkp5A_globs, hkp5A_temps, hkp5_lvars; cbn [app].
  assert_PROP (is_pointer_or_null (hkp5A_nhead NS)) as Hpn.
  { sep_apply (hkp5A2b_pn (hkp5A_nhead NS) NS). entailer!. }
  forward.
  forward_loop
    (EX NS1: list hnode4, EX NS2: list hnode4, EX PS1: list (val * share * peer),
     EX PS1': list (val * share * peer), EX PS2: list (val * share * peer), EX it: val, EX T': tstate,
     EX S': shim,
     PROPx [NS = NS1 ++ NS2; PS = PS1 ++ PS2; Forall2 hkp5A2b_rnd PS1 PS1'; hnodes_peers4 NS2 PS2;
            hkp5A_inv F P NS PS [] T' head]
     (LOCALx (temp KC._o it :: hkp5A_temps RR ++ hkp5_lvars F)
     (SEPx (hkp5A2b_fix x25519 F FR RR P S' w NS T' head ++
            [hkp5A2b_seg (hkp5A_nhead NS) it NS1; hnodes_rep4 W_keypairs it NS2;
             peers_rep PS1'; peers_rep PS2]))))
    continue:
    (EX NS1: list hnode4, EX N: hnode4, EX NS2: list hnode4, EX PS1: list (val * share * peer),
     EX PS1': list (val * share * peer), EX x: val * share * peer, EX y: val * share * peer,
     EX PS2: list (val * share * peer), EX nx: val, EX T': tstate, EX S': shim,
     PROPx [NS = NS1 ++ N :: NS2; PS = PS1 ++ x :: PS2; Forall2 hkp5A2b_rnd PS1 PS1';
            hkp5A2b_rnd x y; hnodes_peers4 NS2 PS2; hn_p N = peer_addr4 x; hkp5A_inv F P NS PS [] T' head]
     (LOCALx (temp KC._o (hn_addr N) :: hkp5A_temps RR ++ hkp5_lvars F)
     (SEPx (hkp5A2b_fix x25519 F FR RR P S' w NS T' head ++
            [hkp5A2b_seg (hkp5A_nhead NS) (hn_addr N) NS1;
             @malloc_token W_keypairs Ews t_hnode4 (hn_addr N);
             @data_at W_keypairs Ews t_hnode4 (hkp5A2b_nv N nx) (hn_addr N);
             @malloc_token W_keypairs Ews t_peer (hn_p N);
             hnodes_rep4 W_keypairs nx NS2;
             peers_rep PS1'; peer_item_rep y; peers_rep PS2]))))
    break: (hkp5A_S2 x25519 F FR).
  - Exists (@nil hnode4) NS (@nil (val * share * peer)) (@nil (val * share * peer)) PS (hkp5A_nhead NS) T S.
    unfold hkp5A2b_fix, hkp5A_world, hk5_items, hkp5A_snaps0, hkp5A_globs, hkp5A_temps, hkp5_lvars; cbn [app].
    entailer!.
    { destruct H1 as (_ & _ & _ & _ & _ & _ & _ & Hnp & _). exact Hnp. }
    simpl. entailer!.
  - Intros NS1 NS2 PS1 PS1' PS2 it T' S'.
    unfold hkp5A2b_fix, hkp5A_world, hk5_items, hkp5A_snaps0, hkp5A_globs, hkp5A_temps, hkp5_lvars; cbn [app].
    forward_if.
    + destruct NS2 as [| N NS2']; [simpl hnodes_rep4; Intros; subst it; contradiction |].
      destruct PS2 as [| x PS2']; [unfold hnodes_peers4 in *; discriminate |].
      match goal with Hp: hnodes_peers4 (N :: NS2') (x :: PS2') |- _ =>
        unfold hnodes_peers4 in Hp; cbn in Hp; injection Hp as Hpx Hnp' end.
      simpl hnodes_rep4. Intros nx. subst it.
      rewrite hkp5A2b_node_nv.
      assert (HxPS: In x PS) by (subst PS; apply in_or_app; right; left; reflexivity).
      assert (Hxa: In (peer_addr4 x) (map peer_addr4 PS)) by (apply in_map, HxPS).
      assert (Hpool: In (hs_addr (peer_addr4 x)) (saddrs (t_D T'))).
      { match goal with Hi: hkp5A_inv F P NS PS [] T' head |- _ =>
          destruct Hi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsa & _) end.
        rewrite Hsa. cbn [map app]. apply in_or_app. left. apply in_map, Hxa. }
      assert (Hwx: writable_share (snd (fst x))).
      { match goal with Hi: hkp5A_inv F P NS PS [] T' head |- _ =>
          destruct Hi as (_ & _ & _ & _ & _ & _ & _ & _ & Hwf & _) end.
        unfold peers_wf in Hwf. rewrite Forall_forall in Hwf. specialize (Hwf x HxPS).
        destruct x as [[a sh] Q]. exact Hwf. }
      destruct x as [[a sh] Q]. cbn in Hpx, Hpool, Hwx, Hxa. subst a.
      change (peers_rep ((hn_p N, sh, Q) :: PS2')) with (peer_rep sh (hn_p N) Q * peers_rep PS2')%logic.
      Intros.
      assert_PROP (isptr (hn_p N)) as Hpp.
      { unfold peer_rep. Intros. entailer!.
        match goal with Hf: field_compatible t_peer [] _ |- _ => exact (field_compatible_isptr _ _ _ Hf) end. }
      forward.
      forward_call (sh, hn_p N, Q, false).
      Intros vret. destruct vret as [[[[[[[st lic] eph] reph] hash] ck] ts] ri]. cbn [fst snd] in *.
      forward.
      forward_call (sh, hn_p N, p_set_hs Q (hs_randomized (p_hs Q) st lic eph reph hash ck ts ri)).
      Intros vret. destruct vret as [[[[[[dead lsh] valid] birth] cki] sent] mac1]. cbn [fst snd] in *.
      forward_call tt. Intros b.
      forward_if.
      1: entailer!; match goal with Hm: _ /\ Int.repr 4 = Int.mone |- _ => destruct Hm as [_ Hm];
           apply (f_equal Int.unsigned) in Hm; rewrite Int.unsigned_repr, Int.unsigned_mone in Hm by rep_lia;
           rep_lia end.
      * forward.
        forward_call (f_gv F, S', w, Tsh, f_t F, T', hs_addr (hn_p N), @None (share * entry)).
        { unfold P4.raw_rep. rewrite emp_sepcon. cancel. }
        Intros idx.
        Exists NS1 N NS2' PS1 PS1' (hn_p N, sh, Q)
          (hn_p N, sh, p_rest_randomized (p_set_hs Q (hs_randomized (p_hs Q) st lic eph reph hash ck ts ri))
                   dead lsh valid birth cki sent mac1) PS2' nx (t_insert T' (hs_addr (hn_p N)) idx) (shim_u32 S' idx).
        unfold hkp5A2b_fix, hkp5A_world, hk5_items, hkp5A_snaps0, hkp5A_globs, hkp5A_temps, hkp5_lvars;
          cbn [app P4.raw_add]. entailer!.
        split; [apply hkp5A2b_rnd_step | apply hkp5A2b_inv_insert; auto].
      * forward.
        Exists NS1 N NS2' PS1 PS1' (hn_p N, sh, Q)
          (hn_p N, sh, p_rest_randomized (p_set_hs Q (hs_randomized (p_hs Q) st lic eph reph hash ck ts ri))
                   dead lsh valid birth cki sent mac1) PS2' nx T' S'.
        unfold hkp5A2b_fix, hkp5A_world, hk5_items, hkp5A_snaps0, hkp5A_globs, hkp5A_temps, hkp5_lvars;
          cbn [app]. entailer!.
        apply hkp5A2b_rnd_step.
    + forward. subst it.
      destruct NS2 as [| N NS2'].
      2: { simpl hnodes_rep4. Intros nx.
           assert_PROP (isptr (hn_addr N)) as Hf by entailer!.
           match goal with Hq: nullval = hn_addr N |- _ => rewrite <- Hq in Hf end. contradiction. }
      destruct PS2 as [| x PS2']; [| unfold hnodes_peers4 in *; discriminate].
      rewrite app_nil_r in *. subst NS PS.
      sep_apply (hkp5A2b_seg_app (hkp5A_nhead NS1) nullval NS1 []). rewrite app_nil_r.
      unfold hkp5A_S2. Exists RR P S' w NS1 PS1' T' head.
      unfold hkp5A_oth, hkp5A_world, hk5_items, hkp5A_snaps0, hkp5A_globs, hkp5A_temps, hkp5_lvars; cbn [app].
      entailer!.
      apply hkp5A2b_inv_rnd with PS1; assumption.
  - Intros NS1 N NS2 PS1 PS1' x y PS2 nx T' S'.
    unfold hkp5A2b_fix, hkp5A_world, hk5_items, hkp5A_snaps0, hkp5A_globs, hkp5A_temps, hkp5_lvars; cbn [app].
    assert_PROP (is_pointer_or_null nx) as Hnx. { sep_apply (hkp5A2b_pn nx NS2). entailer!. }
    forward.
    sep_apply (hkp5A2b_seg_snoc_nv (hkp5A_nhead NS) (hn_addr N) N nx NS1 eq_refl).
    Exists (NS1 ++ [N]) NS2 (PS1 ++ [x]) (PS1' ++ [y]) PS2 nx T' S'.
    unfold hkp5A2b_fix, hkp5A_world, hk5_items, hkp5A_snaps0, hkp5A_globs, hkp5A_temps, hkp5_lvars; cbn [app].
    rewrite hkp5A2b_peers_snoc.
    entailer!.
    split; [rewrite <- app_assoc; reflexivity |]. split; [rewrite <- app_assoc; reflexivity |].
    apply Forall2_app; [assumption | constructor; [assumption | constructor]].
  - unfold POSTCONDITION, abbreviate. simpl RA_normal. apply andp_left2, derives_refl.
Qed.
