(* law handshake_clear: main's phase P8, statements 21..26: CHECK(kents_same_but_next(kes, &it)); CHECK(table_len(&it) == hashed + kents_hashed(kes)); CHECK(dev_same(&ds, &w) && shim_same(&ss)); kents_free(kes); hnodes_free(peers); return 0 (hcl5_closeH).
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

Ltac hcl5_p8_dif := match goal with |- context [if ?c then _ else _] => destruct c end.

(* ---- reflexivity of the comparisons ---- *)
Lemma hcl5_p8_veqb_refl x : veqb x x = true.
Proof. unfold veqb. destruct (eq_dec x x); congruence. Qed.
Lemma hcl5_p8_bytes_eqb_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.
Lemma hcl5_p8_entry_eqb_refl E : entry_eqb E E = true.
Proof. unfold entry_eqb. hcl5_p8_dif; [|congruence]. rewrite !Int.eq_true. reflexivity. Qed.
Lemma hcl5_p8_int64s_eqb_refl l : int64s_eqb l l = true.
Proof. induction l; cbn; auto. rewrite Int64.eq_true; auto. Qed.
Lemma hcl5_p8_kp_eqb_refl K : kp_eqb K K = true.
Proof.
  unfold kp_eqb, symkey_eqb. rewrite !hcl5_p8_bytes_eqb_refl, !Int64.eq_true, !Int.eq_true, !Bool.eqb_reflx,
    hcl5_p8_int64s_eqb_refl. reflexivity.
Qed.
Lemma hcl5_p8_dev_eqb_refl D h : dev_eqb D h D h = true.
Proof. unfold dev_eqb. rewrite !hcl5_p8_veqb_refl, !hcl5_p8_bytes_eqb_refl, !Int64.eq_true, !Bool.eqb_reflx. reflexivity. Qed.
Lemma hcl5_p8_shim_eqb_refl S w : shim_eqb S w S w = true.
Proof. unfold shim_eqb, warn_eqb. cbn [forallb]. rewrite !Int64.eq_true. reflexivity. Qed.

(* ---- vremove ---- *)
Lemma hcl5_p8_vin_vremove k a L : k <> a -> vin k (vremove a L) = vin k L.
Proof.
  intros Hne. unfold vin.
  destruct (in_dec eq_dec k (vremove a L)) as [H1|H1]; destruct (in_dec eq_dec k L) as [H2|H2]; auto; exfalso.
  - apply H2; clear H2. induction L as [|x L IH]; cbn in H1; [contradiction|].
    revert H1; hcl5_p8_dif; intros H1; [right; auto | destruct H1; [left | right]; auto].
  - apply H1; clear H1. induction L as [|x L IH]; [contradiction|]. cbn.
    destruct H2 as [<- | H2]; hcl5_p8_dif; subst; try contradiction; [left; auto | auto | right; auto].
Qed.

Lemma hcl5_p8_vremove_filter a L : vremove a L = filter (fun x => negb (veqb x a)) L.
Proof.
  induction L as [|x L IH]; cbn; auto. unfold veqb.
  rewrite IH. change (EqDec_val x a) with (eq_dec x a). destruct (eq_dec x a); reflexivity.
Qed.

Lemma hcl5_p8_nodup_app_r (l1 l2: list val) x : NoDup (l1 ++ l2) -> In x l2 -> ~ In x l1.
Proof.
  induction l1 as [|y l1 IH]; cbn; intros Hn Hx Hin; [auto|]. inversion Hn; subst.
  destruct Hin as [<- | Hin]; [apply H1; apply in_or_app; right; auto | eapply IH; eauto].
Qed.

(* ---- counting ---- *)
Lemma hcl5_p8_count (L U: list val) : NoDup L -> NoDup U -> incl L U ->
  Zlength L = Zlength (filter (fun x => vin x L) U).
Proof.
  intros HL HU HI. rewrite !Zlength_correct. f_equal. apply Nat.le_antisymm; apply NoDup_incl_length.
  - exact HL.
  - intros x Hx. apply filter_In. split; [apply HI, Hx|].
    unfold vin. destruct (in_dec eq_dec x L); [reflexivity | contradiction].
  - apply NoDup_filter, HU.
  - intros x Hx. apply filter_In in Hx. destruct Hx as [Hx Hv].
    unfold vin in Hv. destruct (in_dec eq_dec x L); [auto | discriminate].
Qed.

Lemma hcl5_p8_notin_vremove a L : vin a (vremove a L) = false.
Proof.
  unfold vin. destruct (in_dec eq_dec a (vremove a L)) as [H|H]; auto. exfalso.
  induction L as [|x L IH]; cbn in H; [contradiction|].
  revert H; hcl5_p8_dif; intros H; [auto | destruct H as [<- | H]; [contradiction | auto]].
Qed.

Lemma hcl5_p8_filter_map {A B: Type} (g: B -> bool) (f: A -> B) l :
  Zlength (filter g (map f l)) = Zlength (filter (fun x => g (f x)) l).
Proof. induction l as [|x l IH]; cbn; auto. destruct (g (f x)); rewrite ?Zlength_cons, IH; auto. Qed.

Lemma hcl5_p8_hs_veqb y p : isptr y -> isptr p -> veqb (hs_addr y) (hs_addr p) = veqb y p.
Proof.
  intros Hy Hp. destruct y; try contradiction. destruct p; try contradiction.
  unfold veqb, hs_addr.
  match goal with |- (if ?c then _ else _) = (if ?d then _ else _) => destruct c as [E'|E']; destruct d as [E|E] end;
    auto; exfalso.
  - apply E. cbn in E'. assert (Hb: b = b0) by congruence. subst b0. f_equal.
    assert (Hq: Ptrofs.add i (Ptrofs.repr OFS_PEER_HANDSHAKE) = Ptrofs.add i0 (Ptrofs.repr OFS_PEER_HANDSHAKE))
      by congruence.
    match goal with Hq: Ptrofs.add ?x ?r = Ptrofs.add ?y ?r |- _ =>
      apply (f_equal (fun z => Ptrofs.sub z r)) in Hq; rewrite !Ptrofs.sub_add_opp, !Ptrofs.add_assoc,
        !Ptrofs.add_neg_zero, !Ptrofs.add_zero in Hq; exact Hq end.
  - apply E'. rewrite E. reflexivity.
Qed.

Lemma hcl5_p8_clr_addrs i PS : 0 <= i < Zlength PS -> map peer_addr4 (hcl5_clr i PS) = map peer_addr4 PS.
Proof.
  intros Hi. unfold hcl5_clr. rewrite <- upd_Znth_map.
  replace (peer_addr4 (hcl5_clr1 (Znth i PS))) with (Znth i (map peer_addr4 PS)).
  - apply upd_Znth_triv; [rewrite Zlength_map; lia | reflexivity].
  - rewrite Znth_map by lia. destruct (Znth i PS) as [[a sh] P]. reflexivity.
Qed.

Lemma hcl5_p8_clr_Forall (Q: val * share * peer -> Prop) i PS :
  (forall x, Q x -> Q (hcl5_clr1 x)) -> 0 <= i < Zlength PS -> Forall Q PS -> Forall Q (hcl5_clr i PS).
Proof.
  intros HQ Hi HF. unfold hcl5_clr. apply Forall_upd_Znth; auto. apply HQ.
  rewrite Forall_forall in HF. apply HF, Znth_In; lia.
Qed.

(* the kents' check and count *)
Lemma hcl5_p8_kbn T a KE : ~ In a (map ke_addr KE) ->
  forallb (kent_same_bn (t_remove T a)) (map (kent_snapped T) KE) = true.
Proof.
  intros Ha. apply forallb_forall. intros e' Hin. apply in_map_iff in Hin. destruct Hin as (e & <- & He).
  assert (Hne: ke_addr e <> a) by (intro X; apply Ha; rewrite <- X; apply in_map; auto).
  unfold kent_same_bn, kent_eqb_cur, kent_snapped, kent_eqb_nn. cbn [ke_snap ke_addr ke_K ks_E ks_hashed ks_K].
  change (t_entry_d (t_remove T a) (ke_addr e)) with (t_entry_d T (ke_addr e)).
  change (t_L (t_remove T a)) with (vremove a (t_L T)).
  rewrite hcl5_p8_vin_vremove by auto. rewrite hcl5_p8_entry_eqb_refl, Bool.eqb_reflx, hcl5_p8_kp_eqb_refl.
  destruct (vin _ _); reflexivity.
Qed.

Lemma hcl5_p8_hs_inj y p : isptr y -> isptr p -> hs_addr y = hs_addr p -> y = p.
Proof.
  intros Hy Hp E. pose proof (hcl5_p8_hs_veqb y p Hy Hp) as X. rewrite E, hcl5_p8_veqb_refl in X.
  unfold veqb in X. destruct (eq_dec y p); [auto | discriminate].
Qed.

Lemma hcl5_p8_len T KE PS p :
  itable_wf (t_remove T (hs_addr p)) ->
  saddrs (t_D T) = map ke_addr KE ++ map (fun x => hs_addr (peer_addr4 x)) PS ->
  Forall (fun x => isptr (peer_addr4 x)) PS -> In p (map peer_addr4 PS) ->
  Zlength (t_L (t_remove T (hs_addr p))) =
  hcl5_nh T p PS + kents_hashed_n (t_remove T (hs_addr p)) (map (kent_snapped T) KE).
Proof.
  intros (HnL & Hincl & HnD & _) HD Hptr Hp. cbn [t_remove t_L t_D] in HnL, Hincl, HnD |- *.
  assert (Hpp: isptr p) by (apply in_map_iff in Hp; destruct Hp as (x & <- & Hx);
    rewrite Forall_forall in Hptr; apply Hptr, Hx).
  assert (Ha: ~ In (hs_addr p) (map ke_addr KE)).
  { rewrite HD in HnD. eapply hcl5_p8_nodup_app_r; [exact HnD|].
    apply in_map_iff in Hp. destruct Hp as (x & <- & Hx). apply in_map_iff. exists x; auto. }
  rewrite (hcl5_p8_count (vremove (hs_addr p) (t_L T)) (saddrs (t_D T))) by auto.
  rewrite HD, filter_app, Zlength_app, !hcl5_p8_filter_map. rewrite Z.add_comm. f_equal.
  - unfold hcl5_nh. f_equal. apply filter_ext_in. intros x Hx.
    rewrite Forall_forall in Hptr. unfold veqb. destruct (eq_dec (peer_addr4 x) p) as [E|E]; cbn [negb andb].
    + rewrite E. apply hcl5_p8_notin_vremove.
    + apply hcl5_p8_vin_vremove. intros X. apply E. apply hcl5_p8_hs_inj; auto.
  - unfold kents_hashed_n. rewrite hcl5_p8_filter_map. reflexivity.
Qed.

Lemma hcl5_p8_ptrs PS : peers_rep PS |-- !! Forall (fun x => isptr (peer_addr4 x)) PS.
Proof.
  induction PS as [| [[a sh] P] PS IH]; unfold peers_rep in *; simpl.
  - entailer!.
  - sep_apply IH. unfold peer_item_rep at 1, peer_rep. entailer!.
    constructor; [cbn; destruct H0; assumption | assumption].
Qed.

Lemma hcl5_p8_kpre T a KE PS PS' :
  saddrs (t_D T) = map ke_addr KE ++ map (fun x => hs_addr (peer_addr4 x)) PS ->
  Forall (fun e => In (e_peer (t_entry_d T (ke_addr e))) (map peer_addr4 PS)) KE ->
  map peer_addr4 PS' = map peer_addr4 PS ->
  Forall (fun e => In (ke_addr e) (saddrs (t_D (t_remove T a))) /\ ke_snap e <> None /\
           Forall (vp_ok (saddrs (t_D (t_remove T a)) ++ vobjs_addrs [VPeers PS'])) (kent_ptrs_nn (t_remove T a) e))
    (map (kent_snapped T) KE).
Proof.
  intros HD HK HA. apply Forall_map. rewrite Forall_forall in HK |- *. intros e He. specialize (HK e He).
  unfold Basics.compose, kent_snapped, kent_ptrs_nn. cbn [ke_addr ke_snap ks_E t_remove t_D].
  change (t_entry_d (t_remove T a) (ke_addr e)) with (t_entry_d T (ke_addr e)).
  assert (Hv: vp_ok (saddrs (t_D T) ++ vobjs_addrs [VPeers PS']) (e_peer (t_entry_d T (ke_addr e)))).
  { right. apply in_or_app. right. unfold vobjs_addrs. cbn. rewrite app_nil_r, HA. exact HK. }
  split; [rewrite HD; apply in_or_app; left; apply in_map, He|].
  split; [discriminate|]. constructor; [exact Hv | constructor; [exact Hv | constructor]].
Qed.

Lemma hcl5_p8_notkent T KE PS p :
  NoDup (saddrs (t_D T)) ->
  saddrs (t_D T) = map ke_addr KE ++ map (fun x => hs_addr (peer_addr4 x)) PS ->
  In p (map peer_addr4 PS) -> ~ In (hs_addr p) (map ke_addr KE).
Proof.
  intros HnD HD Hp. rewrite HD in HnD. eapply hcl5_p8_nodup_app_r; [exact HnD|].
  apply in_map_iff in Hp. destruct Hp as (x & <- & Hx). apply in_map_iff. exists x; auto.
Qed.

Lemma hcl5_p8_head head PS : pk_chain head PS -> head = nullval \/ In head (map peer_addr4 PS).
Proof. destruct PS as [|[[a sh] P] PS]; cbn; intros Hc; [left; exact Hc | right; left; symmetry; apply Hc]. Qed.

Lemma hcl5_p8_dpre wg it pt head T' PS' D :
  d_dev D = nullval -> cc_dev (d_cc D) = wg -> d_ptab D = pt -> d_itab D = it ->
  head = nullval \/ In head (map peer_addr4 PS') ->
  Forall (vp_ok ([wg; pt] ++ vobjs_addrs [VItab Tsh it T'; VPeers PS'])) (dev_ptrs D head D head).
Proof.
  intros H1 H2 H3 H4 Hh. unfold dev_ptrs. rewrite H1, H2, H3, H4.
  assert (Hv: vp_ok ([wg; pt] ++ vobjs_addrs [VItab Tsh it T'; VPeers PS']) head).
  { destruct Hh as [-> | Hh]; [left; reflexivity|]. right. cbn. right; right; right.
    apply in_or_app; right. rewrite app_nil_r. exact Hh. }
  assert (Hn: vp_ok ([wg; pt] ++ vobjs_addrs [VItab Tsh it T'; VPeers PS']) nullval) by (left; reflexivity).
  assert (Hw: vp_ok ([wg; pt] ++ vobjs_addrs [VItab Tsh it T'; VPeers PS']) wg) by (right; left; reflexivity).
  assert (Hp: vp_ok ([wg; pt] ++ vobjs_addrs [VItab Tsh it T'; VPeers PS']) pt) by (right; right; left; reflexivity).
  assert (Hi: vp_ok ([wg; pt] ++ vobjs_addrs [VItab Tsh it T'; VPeers PS']) it)
    by (right; right; right; left; reflexivity).
  apply Forall_cons; [exact Hn|]. apply Forall_cons; [exact Hn|].
  apply Forall_cons; [exact Hw|]. apply Forall_cons; [exact Hw|].
  apply Forall_cons; [exact Hp|]. apply Forall_cons; [exact Hp|].
  apply Forall_cons; [exact Hi|]. apply Forall_cons; [exact Hi|].
  apply Forall_cons; [exact Hv|]. apply Forall_cons; [exact Hv|]. apply Forall_nil.
Qed.

Lemma hcl5_p8_snapped_p T NS PS : Zlength NS = Zlength PS ->
  map hn_p (hnodes_snapped4 T NS PS) = map hn_p NS.
Proof.
  unfold hnodes_snapped4. revert PS. induction NS as [|N NS IH]; intros [|x PS] Hl; cbn; auto.
  - rewrite Zlength_cons, Zlength_nil in Hl. pose proof (Zlength_nonneg NS). lia.
  - rewrite !Zlength_cons in Hl. destruct x as [[a sh] P]. cbn. f_equal. apply IH. lia.
Qed.

Lemma hcl5_p8_hbytes32 bs p : Zlength bs = 32 ->
  hbytes Tsh bs p |-- @data_at_ W_handshake_clear Tsh (tarray tuchar 32) p.
Proof. intros Hl. unfold hbytes. rewrite Hl, <- hcl5_conv_bytes. unfold hout. apply data_at_data_at_. Qed.

Lemma hcl5_p8_ptable p head : ptable Tsh p head |-- @data_at_ W_handshake_clear Tsh t_ptab p.
Proof. unfold ptable. rewrite <- hcl5_conv_ptab. apply data_at_data_at_. Qed.

Lemma hcl5_p8_pn l NS : hnodes_rep4 W l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [| N NS]; cbn [hnodes_rep4].
  - entailer!.
  - Intros nx. subst l. sep_apply (@data_at_local_facts CKS). entailer!.
    match goal with X: field_compatible _ _ (hn_addr N) |- _ => destruct X as [Hp _] end.
    destruct (hn_addr N); try contradiction; simpl; auto.
Qed.

Lemma hcl5_p8_vok PS : Forall (fun x => match x with (_, sh, _) => sh = Ews end) PS -> vobj_ok (VPeers PS).
Proof. intros H. cbn. eapply Forall_impl; [|exact H]. intros [[a sh] P] ->. apply writable_readable, writable_Ews. Qed.

Lemma hcl5_p8_vo1 PS : peers_rep PS = vobjs W [VPeers PS].
Proof. unfold vobjs. cbn. rewrite sepcon_emp. reflexivity. Qed.
Lemma hcl5_p8_vo2 tab T PS : (itable Tsh tab T * peers_rep PS)%logic = vobjs W [VItab Tsh tab T; VPeers PS].
Proof. unfold vobjs. cbn. rewrite sepcon_emp. reflexivity. Qed.

Section P8.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcl5_P8_ok {Espec: OracleKind} gv L FR :
  hcl5_hyps x25519 -> hcl5_closeH ->
  semax (hcl5_Delta x25519) (hcl5_S7 x25519 gv L FR) hcl5_P8
    (overridePost FF (hcl5_R gv)).
Proof.
  intros HH HC. unfold hcl5_S7, hcl5_Delta, hcl5_R, hcl5_P8. simplify_func_tycontext. abbreviate_semax.
  Intros R S w NS PS T head KE i.
  unfold hcl5_lvars, hcl5_scr, hcl5_world, hcl5_globs; cbn [app].
  pose proof H0 as Hinv. destruct Hinv as (Hpok & Hwf & Hch & Hnp & HT & Hsl).
  destruct HT as (HT1 & HT2 & HT3 & HT4).
  assert (Hlen: Zlength NS = Zlength PS)
    by (rewrite <- (Zlength_map _ _ hn_p NS), <- (Zlength_map _ _ peer_addr4 PS); f_equal; exact Hnp).
  assert (HpI: hn_p (Znth i NS) = peer_addr4 (Znth i PS))
    by (rewrite <- (Znth_map i hn_p NS), <- (Znth_map i peer_addr4 PS) by lia; f_equal; exact Hnp).
  assert (HiP: 0 <= i < Zlength PS) by lia.
  assert (Haddr := hcl5_p8_clr_addrs i PS HiP).
  assert_PROP (Forall (fun x => isptr (peer_addr4 x)) (hcl5_clr i PS)) as Hptr'
    by (sep_apply (hcl5_p8_ptrs (hcl5_clr i PS)); entailer!).
  assert (Hptr: Forall (fun x => isptr (peer_addr4 x)) PS).
  { rewrite <- (Forall_map (fun v => isptr v) peer_addr4) in Hptr' |- *. rewrite <- Haddr. exact Hptr'. }
  clear Hptr'.
  assert (Hpin: In (hn_p (Znth i NS)) (map peer_addr4 PS)) by (rewrite HpI; apply in_map, Znth_In; lia).
  remember (hn_p (Znth i NS)) as p eqn:Ep.
  assert_PROP (itable_wf (t_remove T (hs_addr p))) as Hwf' by (unfold itable; entailer!).
  assert (Hok: Forall (fun x => match x with (_, sh, _) => sh = Ews end) (hcl5_clr i PS)).
  { apply hcl5_p8_clr_Forall; auto; [intros [[a sh] P]; cbn; auto|].
    eapply Forall_impl; [| exact Hpok]. intros [[a sh] P] Hx. apply Hx. }
  (* 21: CHECK(kents_same_but_next(kes, &it)) *)
  rewrite (hcl5_p8_vo1 (hcl5_clr i PS)).
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
  - entailer!.
  - forward_call (hcl5_khead KE, map (kent_snapped T) KE, Tsh, l_it L, t_remove T (hs_addr p),
                  [VPeers (hcl5_clr i PS)]).
    { split; [repeat constructor; apply hcl5_p8_vok, Hok|]. apply (hcl5_p8_kpre T (hs_addr p) KE PS); auto. }
    rewrite (hcl5_p8_kbn T (hs_addr p) KE).
    2: { destruct Hwf' as (_ & _ & Hnd & _). apply (hcl5_p8_notkent T KE PS p Hnd HT1 Hpin). }
    forward_if True; [discriminate | forward; entailer! |].
    forward. entailer!.
  - (* 22: CHECK(table_len(&it) == hashed + kents_hashed(kes)) *)
    pose proof (hcl5_p8_len T KE PS p Hwf' HT1 Hptr Hpin) as Hn.
    match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
    + entailer!.
    + forward_call (Tsh, l_it L, t_remove T (hs_addr p)).
      forward_call (hcl5_khead KE, map (kent_snapped T) KE, Tsh, l_it L, t_remove T (hs_addr p)).
      { eapply Forall_impl; [| apply (hcl5_p8_kpre T (hs_addr p) KE PS (hcl5_clr i PS)); auto].
        intros e (X & _); exact X. }
      rewrite Hn.
      forward_if True.
      * exfalso. rewrite add64_repr, Int64.eq_true in H2. discriminate.
      * forward; entailer!.
      * forward. entailer!.
    + (* 23: CHECK(dev_same(&ds, &w) && shim_same(&ss)) *)
      rewrite <- (hcl5_p8_vo1 (hcl5_clr i PS)).
      gather_SEP (itable _ _ _) (peers_rep _).
      rewrite hcl5_p8_vo2.
      change (ptable Tsh (l_pt L) head) with (ptable Tsh (d_ptab (hcl5_D x25519 R L)) head).
      match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
      * entailer!.
      * forward_call (Tsh, l_ds L, hcl5_D x25519 R L, head, Tsh, l_w L, hcl5_D x25519 R L, Tsh, head,
                      [VItab Tsh (l_it L) (t_remove T (hs_addr p)); VPeers (hcl5_clr i PS)]).
        { split; [constructor; [cbn; apply writable_readable, writable_share_top |
                                constructor; [apply hcl5_p8_vok, Hok | constructor]] |].
          apply hcl5_p8_dpre; try reflexivity. rewrite Haddr. apply hcl5_p8_head, Hch. }
        rewrite hcl5_p8_dev_eqb_refl.
        forward_if (temp HCL5._t'20 (Vint Int.one)).
        -- forward_call (gv, Tsh, l_ss L, S, w, S, w).
           rewrite hcl5_p8_shim_eqb_refl. forward. entailer!.
        -- exfalso. apply Int.one_not_zero. assumption.
        -- forward_if True; [discriminate | forward; entailer! |].
           forward. entailer!.
      * (* 24..26: kents_free(kes); hnodes_free(peers); return 0 *)
        rewrite <- hcl5_p8_vo2.
        destruct HC as [HCd HCp].
        assert (Hnp': hnodes_peers4 (hnodes_snapped4 T NS PS) (hcl5_clr i PS)).
        { unfold hnodes_peers4 in *. rewrite hcl5_p8_snapped_p by exact Hlen. rewrite Haddr. exact Hnp. }
        assert (HD': saddrs (t_D (t_remove T (hs_addr p))) =
                     map ke_addr (map (kent_snapped T) KE) ++ map (fun x => hs_addr (peer_addr4 x)) PS)
          by (rewrite map_map; exact HT1).
        sep_apply (HCp (l_it L) (t_remove T (hs_addr p)) PS (hcl5_clr i PS) (map (kent_snapped T) KE)
                     (hnodes_snapped4 T NS PS) HD' HT2 Haddr Hok Hnp').
        forward_call (gv, hcl5_khead KE, map (kent_snapped T) KE).
        { cancel. }
        assert_PROP (is_pointer_or_null (hcl5_head NS)) as Hhd
          by (sep_apply (hcl5_p8_pn (hcl5_head NS) (hnodes_snapped4 T NS PS)); entailer!).
        forward.
        forward_call (gv, hcl5_head NS, hnodes_snapped4 T NS PS).
        apply hcl5_post_canon.
        sep_apply (HCd Tsh (l_w L) (hcl5_D x25519 R L)).
        forward.
        destruct H as (Hra & _).
        rewrite hcl5_conv_dev, hcl5_conv_itab, !hcl5_conv_bytes.
        sep_apply (hcl5_p8_hbytes32 (r_raw R) (l_raw L) Hra).
        sep_apply (hcl5_p8_ptable (d_ptab (hcl5_D x25519 R L)) head).
        sep_apply (data_at_data_at_ Tsh (tptr t_hnode4) (hcl5_head NS) (l_peers L)).
        sep_apply (hcl5_conv_devsnap_v Tsh (devsnap_val (hcl5_D x25519 R L) head) (l_ds L)).
        sep_apply (hcl5_conv_shimsnap_v Tsh (shimsnap_val S w) (l_ss L)).
        cancel.
Qed.

End P8.
