(* law handshake_receive: main's phase PD = the randomization loop over the nodes (statement 17).
   From hrx5_SB to hrx5_SB (hrx5_defs.v; the cut: hrx5_cut.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_cut.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mspec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require WgNoise.contracts.x_handshake_receive.
Require WgNoise.harness.x_handshake_receive.code.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_conv.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Local Open Scope Z_scope.

#[local] Instance hrx5_pd_cceK : change_composite_env CKS W.
Proof. make_cs_preserve CKS W. Defined.

(* ---------------------------------------------------------------------- *)
(* the pool: an insert keeps it; only the peers' addresses matter         *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_pd_hs_addr PS PS' D :
  map peer_addr4 PS' = map peer_addr4 PS -> Forall2 hrx5cr_hs_ok PS D -> Forall2 hrx5cr_hs_ok PS' D.
Proof.
  intros Hm H. revert PS' Hm. induction H as [| y x PS D Hxy _ IH]; intros PS' Hm.
  - destruct PS'; [constructor | discriminate].
  - destruct PS' as [| y' PS']; [discriminate |]. cbn in Hm. injection Hm as Hy Hm.
    constructor; [| apply IH; exact Hm].
    destruct y as [[p sh] P], y' as [[p' sh'] P'], x as [[a sha] E]; cbn in *. subst p'. exact Hxy.
Qed.

Lemma hrx5_pd_pool_addr PS PS' T :
  map peer_addr4 PS' = map peer_addr4 PS -> hrx5cr_pool [] PS T -> hrx5cr_pool [] PS' T.
Proof.
  intros Hm (H1 & H2). unfold hrx5cr_pool in *. cbn [length firstn skipn] in *.
  split; [constructor | eapply hrx5_pd_hs_addr; eauto].
Qed.

Lemma hrx5_pd_hs_supd PS D a sh E idx :
  Forall2 hrx5cr_hs_ok PS D -> sfind D a = Some (sh, E) ->
  Forall2 hrx5cr_hs_ok PS (supd D a (mkEntry (e_peer E) (e_type E) idx)).
Proof.
  induction 1 as [| y x PS D Hxy HPD IH]; intros Hf; [discriminate |].
  destruct x as [[a' sh'] E']. cbn in Hf |- *.
  destruct (EqDec_val a' a) as [<- | Hne].
  - injection Hf as <- <-. constructor; [| assumption].
    destruct y as [[p shp] P]; cbn in *. destruct Hxy as (? & ? & ? & ?). cbn. auto.
  - constructor; [exact Hxy | auto].
Qed.

Lemma hrx5_pd_pool_insert PS T a idx : hrx5cr_pool [] PS T -> hrx5cr_pool [] PS (t_insert T a idx).
Proof.
  intros (H1 & H2). unfold hrx5cr_pool in *. cbn [length firstn skipn] in *.
  split; [constructor |].
  unfold t_insert, t_set_index, t_entry, t_upd. cbn.
  destruct (sfind (t_D T) a) as [[sh E] |] eqn:Hf; cbn; [eapply hrx5_pd_hs_supd; eauto | exact H2].
Qed.

Lemma hrx5_pd_pool_in PS T x : hrx5cr_pool [] PS T -> In x PS -> In (hs_addr (peer_addr4 x)) (saddrs (t_D T)).
Proof.
  intros (_ & H2). cbn [length skipn] in H2. revert H2. generalize (t_D T) as D.
  intros D H2 Hin. induction H2 as [| y z PS D Hyz _ IH]; [destruct Hin |].
  destruct z as [[a sh] E], y as [[p shp] P]; cbn in Hyz |- *. destruct Hyz as (-> & _).
  destruct Hin as [<- | Hin]; [left; reflexivity | right; auto].
Qed.

(* ---------------------------------------------------------------------- *)
(* the randomization of one peer                                          *)
(* ---------------------------------------------------------------------- *)

Section Rnd.
Variable x25519: list byte -> list byte -> list byte.

Definition hrx5_pd_rnd (R: hrx5_run) (L: hrx5_loc) (x y: val * share * peer) : Prop :=
  match x, y with (a, sh, P), (a', sh', P') =>
    a' = a /\ sh' = sh /\ hrx5_pok x25519 R L y /\ p_pknext P' = p_pknext P
  end.

Lemma hrx5_pd_rnd_step R L a sh P st lic eph reph hash ck ts ri dead lsh valid birth cki sent mac1 :
  hrx5_pok x25519 R L (a, sh, P) ->
  0 <= Int64.unsigned lic < 2 ^ 62 -> Zlength eph = 32 -> Zlength reph = 32 -> Zlength hash = 32 ->
  Zlength ck = 32 -> Zlength ts = 12 ->
  hrx5_pd_rnd R L (a, sh, P)
    (a, sh, p_rest_randomized (p_set_hs P (hs_randomized (p_hs P) st lic eph reph hash ck ts ri))
              dead lsh valid birth cki sent mac1).
Proof.
  intros (Hsh & Hdev & Hsid & Hok & Hss & Hrefs & Hlic & Hpk & Hc & Hp & Hn) H1 H2 H3 H4 H5 H6.
  unfold hrx5_pd_rnd, hrx5_pok, hs_ok in *; cbn. intuition.
Qed.

Lemma hrx5_pd_rnd_addr R L x y : hrx5_pd_rnd R L x y -> peer_addr4 y = peer_addr4 x.
Proof. destruct x as [[a sh] P], y as [[a' sh'] P']; cbn; tauto. Qed.

Lemma hrx5_pd_rnd_map R L PS PS' : Forall2 (hrx5_pd_rnd R L) PS PS' -> map peer_addr4 PS' = map peer_addr4 PS.
Proof.
  induction 1 as [| x y PS PS' Hxy _ IH]; [reflexivity |]. cbn. rewrite IH, (hrx5_pd_rnd_addr _ _ _ _ Hxy).
  reflexivity.
Qed.

Lemma hrx5_pd_inv R L NS PS PS' T T' head nk :
  Forall2 (hrx5_pd_rnd R L) PS PS' -> hrx5_inv x25519 R L NS PS [] T head nk -> hrx5cr_pool [] PS T' ->
  hrx5_inv x25519 R L NS PS' [] T' head nk.
Proof.
  intros H (Hpok & Hwf & Hnd & Hch & Hnp & Hnk & _) HT. unfold hrx5_inv. cbn [map].
  split; [| split; [| split; [| split; [| split; [| split]]]]]; [| | | | | exact Hnk |].
  - clear - H. induction H as [| x y PS PS' Hxy _ IH]; [constructor |].
    constructor; [| auto]. destruct x as [[a sh] P], y as [[a' sh'] P']; cbn in *. tauto.
  - clear - H. induction H as [| x y PS PS' Hxy _ IH]; [constructor |].
    constructor; [| auto]. destruct x as [[a sh] P], y as [[a' sh'] P']; cbn in *.
    destruct Hxy as (_ & _ & (-> & _) & _). apply writable_Ews.
  - rewrite (hrx5_pd_rnd_map R L _ _ H). exact Hnd.
  - clear - H Hch. revert head Hch. induction H as [| x y PS PS' Hxy _ IH]; intros head Hch; [exact Hch |].
    destruct x as [[a sh] P], y as [[a' sh'] P']; cbn in *.
    destruct Hxy as (-> & -> & _ & Hpk). destruct Hch as [-> Hch]. split; [reflexivity |].
    rewrite Hpk. apply IH, Hch.
  - unfold hnodes_peers4 in *. rewrite Hnp. symmetry. apply (hrx5_pd_rnd_map R L), H.
  - apply hrx5_pd_pool_addr with PS; [apply (hrx5_pd_rnd_map R L), H | exact HT].
Qed.

End Rnd.

(* ---------------------------------------------------------------------- *)
(* the node list: segments                                                *)
(* ---------------------------------------------------------------------- *)

Fixpoint hrx5_pd_seg (l e: val) (NS: list hnode4) : mpred :=
  match NS with
  | [] => !! (l = e) && emp
  | N :: NS' =>
      !! (l = hn_addr N) &&
      EX nx: val,
        @malloc_token W Ews t_hnode4 l *
        @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) l *
        @malloc_token W Ews t_peer (hn_p N) *
        hrx5_pd_seg nx e NS'
  end.

Lemma hrx5_pd_seg_app l e NS1 NS2 :
  hrx5_pd_seg l e NS1 * hnodes_rep4 W e NS2 |-- hnodes_rep4 W l (NS1 ++ NS2).
Proof.
  revert l; induction NS1 as [| N NS1 IH]; intros l; simpl.
  - Intros. subst. cancel.
  - Intros nx. Exists nx. entailer!. sep_apply (IH nx). cancel.
Qed.

Lemma hrx5_pd_seg_snoc l e N nx NS1 : e = hn_addr N ->
  hrx5_pd_seg l e NS1 *
  (@malloc_token W Ews t_hnode4 e *
   @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) e *
   @malloc_token W Ews t_peer (hn_p N)) |--
  hrx5_pd_seg l nx (NS1 ++ [N]).
Proof.
  intros He. revert l; induction NS1 as [| M NS1 IH]; intros l; simpl.
  - Intros. subst. Exists nx. entailer!.
  - Intros nx'. Exists nx'. entailer!. sep_apply (IH nx'). cancel.
Qed.

Lemma hrx5_pd_vp l NS : hnodes_rep4 W l NS |-- valid_pointer l.
Proof.
  destruct NS as [| N NS]; simpl.
  - Intros. subst. apply valid_pointer_null.
  - Intros nx. subst.
    sep_apply (@data_at_valid_ptr CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N)).
    { apply readable_nonidentity, writable_readable, writable_Ews. }
    apply sepcon_valid_pointer1, derives_refl.
Qed.

Lemma hrx5_pd_pn l NS : hnodes_rep4 W l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [| N NS]; simpl.
  - Intros. subst. entailer!.
  - Intros nx. subst. entailer!.
    match goal with Hf: field_compatible t_hnode4 [] _ |- _ => apply field_compatible_isptr in Hf end.
    destruct (hn_addr N); try contradiction; exact I.
Qed.

#[local] Hint Resolve hrx5_pd_vp : valid_pointer.

Lemma hrx5_pd_node_W v l : @data_at CKS Ews t_hnode4 v l = @data_at W Ews t_hnode4 v l.
Proof.
  rewrite (@data_at_change_composite CKS W _ Ews t_hnode4 v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

(* the node's value as ONE constant at W (hci5_P3.v: a literal tuple mixing reptypes makes Qed slow) *)
Definition hrx5_pd_nv (N: hnode4) (nx: val) : @reptype W t_hnode4 :=
  (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))).

Lemma hrx5_pd_node_nv N nx l :
  @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) l =
  @data_at W Ews t_hnode4 (hrx5_pd_nv N nx) l.
Proof. unfold hrx5_pd_nv. apply hrx5_pd_node_W. Qed.

Lemma hrx5_pd_seg_snoc_nv l e N nx NS1 : e = hn_addr N ->
  hrx5_pd_seg l e NS1 *
  (@malloc_token W Ews t_hnode4 e * @data_at W Ews t_hnode4 (hrx5_pd_nv N nx) e *
   @malloc_token W Ews t_peer (hn_p N)) |--
  hrx5_pd_seg l nx (NS1 ++ [N]).
Proof. intros He. rewrite <- hrx5_pd_node_nv. apply hrx5_pd_seg_snoc, He. Qed.

Lemma hrx5_pd_peers_snoc l y : peers_rep (l ++ [y]) = (peers_rep l * peer_item_rep y)%logic.
Proof. unfold peers_rep. rewrite iter_sepcon_app. simpl. rewrite sepcon_emp. reflexivity. Qed.

(* the items the loop does not touch (but the table and the shim) *)
Definition hrx5_pd_fix x25519 gv L FR R sec birth S w (NS: list hnode4) T head : list mpred :=
  [device_rep Tsh (l_wd L) (hrx5_DL x25519 R L sec birth); itable Tsh (l_itd L) T; ptable Tsh (l_ptd L) head;
   @data_at HCS Tsh t_mident (mident_val (hrx5_ID x25519 R)) (l_id L);
   @data_at HCS Tsh t_mident (mident_val (hrx5_IK x25519 R)) (l_ik L);
   hbytes Tsh (rr_rawd R) (l_rawd L); hbytes Tsh (rr_rawk R) (l_rawk L);
   hbytes Tsh (hrx5_mk1 x25519 R) (l_mk1 L); hbytes Tsh (hrx5_ssk x25519 R) (l_ssk L);
   @data_at W Tsh (tptr t_hnode4) (hrx5_head NS) (l_peers L);
   kents_rep W (hrx5_khead []) [];
   mem_mgr gv; shim_state4 gv S w; noise_globals gv Int64.zero; wg_consts gv; hrx5_consts gv; FR] ++
  hrx5_rglobs gv Int64.zero ++ [hrx5_skb0 L] ++ hrx5_scr L.

Section PD.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_PD_ok {Espec: OracleKind} gv L FR :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_SB x25519 gv L FR) hrx5_PD
    (overridePost (hrx5_SB x25519 gv L FR) (hrx5_R gv)).
Proof.
  intros HH. unfold hrx5_SB, hrx5_R, hrx5_PD. unfold hrx5_Delta. simplify_func_tycontext. abbreviate_semax.
  Intros R sec birth S w. Intros NS PS T head nk.
  unfold hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_rglobs, hrx5_scr, hrx5_lvars; cbn [app].
  assert_PROP (is_pointer_or_null (hrx5_head NS)) as Hpn.
  { sep_apply (hrx5_pd_pn (hrx5_head NS) NS). entailer!. }
  forward.
  forward_loop
    (EX NS1: list hnode4, EX NS2: list hnode4, EX PS1: list (val * share * peer),
     EX PS1': list (val * share * peer), EX PS2: list (val * share * peer), EX nd: val, EX T': tstate,
     EX S': shim,
     PROPx [NS = NS1 ++ NS2; PS = PS1 ++ PS2; Forall2 (hrx5_pd_rnd x25519 R L) PS1 PS1'; hnodes_peers4 NS2 PS2;
            hrx5cr_pool [] PS T'; s_boot S' = s_boot S]
     (LOCALx ([temp HM._nd nd; temp HM._nk nk; temp HM._now (Vlong (s_boot S)); temp HM._m_lul (Vlong Int64.zero)]
              ++ hrx5_lvars gv L)
     (SEPx (hrx5_pd_fix x25519 gv L FR R sec birth S' w NS T' head ++
            [hrx5_pd_seg (hrx5_head NS) nd NS1; hnodes_rep4 W nd NS2;
             peers_rep PS1'; peers_rep PS2]))))
    continue:
    (EX NS1: list hnode4, EX N: hnode4, EX NS2: list hnode4, EX PS1: list (val * share * peer),
     EX PS1': list (val * share * peer), EX x: val * share * peer, EX y: val * share * peer,
     EX PS2: list (val * share * peer), EX nx: val, EX T': tstate, EX S': shim,
     PROPx [NS = NS1 ++ N :: NS2; PS = PS1 ++ x :: PS2; Forall2 (hrx5_pd_rnd x25519 R L) PS1 PS1';
            hrx5_pd_rnd x25519 R L x y; hnodes_peers4 NS2 PS2; hn_p N = peer_addr4 x; hrx5cr_pool [] PS T';
            s_boot S' = s_boot S]
     (LOCALx ([temp HM._nd (hn_addr N); temp HM._nk nk; temp HM._now (Vlong (s_boot S));
               temp HM._m_lul (Vlong Int64.zero)] ++ hrx5_lvars gv L)
     (SEPx (hrx5_pd_fix x25519 gv L FR R sec birth S' w NS T' head ++
            [hrx5_pd_seg (hrx5_head NS) (hn_addr N) NS1;
             @malloc_token W Ews t_hnode4 (hn_addr N);
             @data_at W Ews t_hnode4 (hrx5_pd_nv N nx) (hn_addr N);
             @malloc_token W Ews t_peer (hn_p N);
             hnodes_rep4 W nx NS2;
             peers_rep PS1'; peer_item_rep y; peers_rep PS2]))))
    break: (hrx5_SB x25519 gv L FR).
  - Exists (@nil hnode4) NS (@nil (val * share * peer)) (@nil (val * share * peer)) PS (hrx5_head NS) T S.
    unfold hrx5_pd_fix, hrx5_lvars, hrx5_rglobs, hrx5_scr; cbn [app].
    entailer!.
    { destruct H0 as (_ & _ & _ & _ & Hnp & _ & Hpool). split; [exact Hnp | exact Hpool]. }
    simpl. entailer!.
  - Intros NS1 NS2 PS1 PS1' PS2 nd T' S'. unfold hrx5_pd_fix, hrx5_lvars, hrx5_rglobs, hrx5_scr; cbn [app].
    forward_if.
    + destruct NS2 as [| N NS2']; [simpl hnodes_rep4; Intros; subst nd; contradiction |].
      destruct PS2 as [| x PS2']; [unfold hnodes_peers4 in *; discriminate |].
      match goal with Hp: hnodes_peers4 (N :: NS2') (x :: PS2') |- _ =>
        unfold hnodes_peers4 in Hp; cbn in Hp; injection Hp as Hpx Hnp' end.
      simpl hnodes_rep4. Intros nx. subst nd.
      rewrite hrx5_pd_node_nv.
      assert (Hpokx: hrx5_pok x25519 R L x).
      { destruct H0 as (Hpok & _). rewrite Forall_forall in Hpok. apply Hpok.
        subst PS; apply in_or_app; right; left; reflexivity. }
      assert (Hpool: In (hs_addr (peer_addr4 x)) (saddrs (t_D T'))).
      { apply hrx5_pd_pool_in with PS; [assumption | subst PS; apply in_or_app; right; left; reflexivity]. }
      destruct x as [[a sh] P]. cbn in Hpx, Hpool. subst a.
      assert (sh = Ews) by (destruct Hpokx; assumption). subst sh.
      change (peers_rep ((hn_p N, Ews, P) :: PS2')) with (peer_rep Ews (hn_p N) P * peers_rep PS2')%logic.
      Intros.
      assert_PROP (isptr (hn_p N)) as Hpp.
      { unfold peer_rep. Intros. entailer!.
        match goal with Hf: field_compatible t_peer [] _ |- _ => exact (field_compatible_isptr _ _ _ Hf) end. }
      forward.
      forward_call (Ews, hn_p N, P, false).
      Intros vret. destruct vret as [[[[[[[st lic] eph] reph] hash] ck] ts] ri]. cbn [fst snd] in *.
      forward.
      forward_call (Ews, hn_p N, p_set_hs P (hs_randomized (p_hs P) st lic eph reph hash ck ts ri)).
      Intros vret. destruct vret as [[[[[[dead lsh] valid] bth] cki] sent] mac1]. cbn [fst snd] in *.
      forward_call tt. Intros b.
      forward_if.
      1: entailer!; match goal with Hm: _ /\ Int.repr 4 = Int.mone |- _ => destruct Hm as [_ Hm];
           apply (f_equal Int.unsigned) in Hm; rewrite Int.unsigned_repr, Int.unsigned_mone in Hm by rep_lia;
           rep_lia end.
      * forward.
        forward_call (gv, S', w, Tsh, l_itd L, T', hs_addr (hn_p N), @None (share * entry)).
        { unfold raw_rep. rewrite emp_sepcon. cancel. }
        Intros idx.
        Exists NS1 N NS2' PS1 PS1' (hn_p N, Ews, P).
        Exists (hn_p N, Ews, p_rest_randomized (p_set_hs P (hs_randomized (p_hs P) st lic eph reph hash ck ts ri))
                   dead lsh valid bth cki sent mac1) PS2' nx (t_insert T' (hs_addr (hn_p N)) idx) (shim_u32 S' idx).
        unfold hrx5_pd_fix, hrx5_lvars, hrx5_rglobs, hrx5_scr; cbn [app raw_add]. entailer!.
        split; [apply hrx5_pd_rnd_step; auto | apply hrx5_pd_pool_insert; auto].
      * forward.
        Exists NS1 N NS2' PS1 PS1' (hn_p N, Ews, P).
        Exists (hn_p N, Ews, p_rest_randomized (p_set_hs P (hs_randomized (p_hs P) st lic eph reph hash ck ts ri))
                   dead lsh valid bth cki sent mac1) PS2' nx T' S'.
        unfold hrx5_pd_fix, hrx5_lvars, hrx5_rglobs, hrx5_scr; cbn [app]. entailer!.
        apply hrx5_pd_rnd_step; auto.
    + forward. subst nd.
      destruct NS2 as [| N NS2'].
      2: { simpl hnodes_rep4. Intros nx.
           assert_PROP (isptr (hn_addr N)) as Hf by entailer!.
           match goal with Hq: nullval = hn_addr N |- _ => rewrite <- Hq in Hf end. contradiction. }
      destruct PS2 as [| x PS2']; [| unfold hnodes_peers4 in *; discriminate].
      rewrite app_nil_r in *. subst NS PS.
      sep_apply (hrx5_pd_seg_app (hrx5_head NS1) nullval NS1 []). rewrite app_nil_r.
      unfold hrx5_SB. Exists R sec birth S' w. Exists NS1 PS1' T' head nk.
      unfold hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_rglobs, hrx5_scr, hrx5_lvars; cbn [app].
      entailer!.
      split.
      * unfold hrx5_base_ok in *.
        match goal with Hb: s_boot S' = s_boot S |- _ => rewrite Hb end. tauto.
      * apply hrx5_pd_inv with PS1 T; assumption.
  - Intros NS1 N NS2 PS1 PS1' x y PS2. Intros nx T' S'. unfold hrx5_pd_fix, hrx5_lvars, hrx5_rglobs, hrx5_scr; cbn [app].
    assert_PROP (is_pointer_or_null nx) as Hnx. { sep_apply (hrx5_pd_pn nx NS2). entailer!. }
    forward.
    sep_apply (hrx5_pd_seg_snoc_nv (hrx5_head NS) (hn_addr N) N nx NS1 eq_refl).
    Exists (NS1 ++ [N]) NS2 (PS1 ++ [x]) (PS1' ++ [y]) PS2 nx T' S'.
    unfold hrx5_pd_fix, hrx5_lvars, hrx5_rglobs, hrx5_scr; cbn [app].
    rewrite hrx5_pd_peers_snoc.
    entailer!.
    split; [rewrite <- app_assoc; reflexivity |]. split; [rewrite <- app_assoc; reflexivity |].
    apply Forall2_app; [assumption | constructor; [assumption | constructor]].
  - unfold POSTCONDITION, abbreviate. simpl RA_normal. apply andp_left2, derives_refl.
Qed.

End PD.
