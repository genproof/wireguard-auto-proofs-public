(* law consume_response_any, phase P3: statement 11 of main: for (it = peers; it; it = it->next) { hs_randomize(&it->p->handshake); peer_randomize_rest(it->p); if (nondet_u8() % 4 != 0) wg_index_hashtable_insert(&ita, &it->p->handshake.entry); }.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_cut.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_model.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_spec.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_conv.
Require WgNoise.harness.x_consume_response_any.code.

#[local] Existing Instance W_consume_response_any.
Local Open Scope logic.

Local Open Scope Z_scope.

#[local] Instance hcr5_p3_cceK : change_composite_env CKS W_consume_response_any.
Proof. make_cs_preserve CKS W_consume_response_any. Defined.

(* ---------------------------------------------------------------------- *)
(* the pool: an insert keeps it; only the peers' addresses matter         *)
(* ---------------------------------------------------------------------- *)

Lemma hcr5_p3_hs_addr PS PS' D :
  map peer_addr4 PS' = map peer_addr4 PS -> Forall2 hcr5_hs_ok PS D -> Forall2 hcr5_hs_ok PS' D.
Proof.
  intros Hm H. revert PS' Hm. induction H as [| y x PS D Hxy _ IH]; intros PS' Hm.
  - destruct PS'; [constructor | discriminate].
  - destruct PS' as [| y' PS']; [discriminate |]. cbn in Hm. injection Hm as Hy Hm.
    constructor; [| apply IH; exact Hm].
    destruct y as [[p sh] P], y' as [[p' sh'] P'], x as [[a sha] E]; cbn in *. subst p'. exact Hxy.
Qed.

Lemma hcr5_p3_pool_addr PS PS' T :
  map peer_addr4 PS' = map peer_addr4 PS -> hcr5_pool [] PS T -> hcr5_pool [] PS' T.
Proof.
  intros Hm (H1 & H2). unfold hcr5_pool in *. cbn [length firstn skipn] in *.
  split; [constructor | eapply hcr5_p3_hs_addr; eauto].
Qed.

Lemma hcr5_p3_hs_supd PS D a sh E idx :
  Forall2 hcr5_hs_ok PS D -> sfind D a = Some (sh, E) ->
  Forall2 hcr5_hs_ok PS (supd D a (mkEntry (e_peer E) (e_type E) idx)).
Proof.
  induction 1 as [| y x PS D Hxy HPD IH]; intros Hf; [discriminate |].
  destruct x as [[a' sh'] E']. cbn in Hf |- *.
  destruct (EqDec_val a' a) as [<- | Hne].
  - injection Hf as <- <-. constructor; [| assumption].
    destruct y as [[p shp] P]; cbn in *. destruct Hxy as (? & ? & ? & ?). cbn. auto.
  - constructor; [exact Hxy | auto].
Qed.

Lemma hcr5_p3_pool_insert PS T a idx : hcr5_pool [] PS T -> hcr5_pool [] PS (t_insert T a idx).
Proof.
  intros (H1 & H2). unfold hcr5_pool in *. cbn [length firstn skipn] in *.
  split; [constructor |].
  unfold t_insert, t_set_index, t_entry, t_upd. cbn.
  destruct (sfind (t_D T) a) as [[sh E] |] eqn:Hf; cbn; [eapply hcr5_p3_hs_supd; eauto | exact H2].
Qed.

Lemma hcr5_p3_pool_in PS T x : hcr5_pool [] PS T -> In x PS -> In (hs_addr (peer_addr4 x)) (saddrs (t_D T)).
Proof.
  intros (_ & H2). cbn [length skipn] in H2. revert H2. generalize (t_D T) as D.
  intros D H2 Hin. induction H2 as [| y z PS D Hyz _ IH]; [destruct Hin |].
  destruct z as [[a sh] E], y as [[p shp] P]; cbn in Hyz |- *. destruct Hyz as (-> & _).
  destruct Hin as [<- | Hin]; [left; reflexivity | right; auto].
Qed.

(* ---------------------------------------------------------------------- *)
(* the randomization of one peer                                          *)
(* ---------------------------------------------------------------------- *)

Definition hcr5_p3_rnd (L: hcr5_loc) (x y: val * share * peer) : Prop :=
  match x, y with (a, sh, P), (a', sh', P') =>
    a' = a /\ sh' = sh /\ hcr5_pok L [] y /\ p_pknext P' = p_pknext P
  end.

Lemma hcr5_p3_rnd_step L a sh P st lic eph reph hash ck ts ri dead lsh valid birth cki sent mac1 :
  hcr5_pok L [] (a, sh, P) ->
  Zlength eph = 32 -> Zlength reph = 32 -> Zlength hash = 32 -> Zlength ck = 32 -> Zlength ts = 12 ->
  hcr5_p3_rnd L (a, sh, P)
    (a, sh, p_rest_randomized (p_set_hs P (hs_randomized (p_hs P) st lic eph reph hash ck ts ri))
              dead lsh valid birth cki sent mac1).
Proof.
  intros (Hsh & Hpa & Hdev & Hsid & Hok & Hrefs & Hsl) H2 H3 H4 H5 H6.
  unfold hcr5_p3_rnd, hcr5_pok, hs_ok in *; cbn. intuition.
Qed.

Lemma hcr5_p3_rnd_addr L x y : hcr5_p3_rnd L x y -> peer_addr4 y = peer_addr4 x.
Proof. destruct x as [[a sh] P], y as [[a' sh'] P']; cbn; tauto. Qed.

Lemma hcr5_p3_rnd_map L PS PS' : Forall2 (hcr5_p3_rnd L) PS PS' -> map peer_addr4 PS' = map peer_addr4 PS.
Proof.
  induction 1 as [| x y PS PS' Hxy _ IH]; [reflexivity |]. cbn. rewrite IH, (hcr5_p3_rnd_addr _ _ _ Hxy).
  reflexivity.
Qed.

Lemma hcr5_p3_list L NS PS PS' head nb :
  Forall2 (hcr5_p3_rnd L) PS PS' -> hcr5_list_ok L [] NS PS head nb -> hcr5_list_ok L [] NS PS' head nb.
Proof.
  intros H (Hpok & Hwf & Hch & Hnp & Hnd & Hnb). unfold hcr5_list_ok.
  split; [| split; [| split; [| split; [| split]]]]; [| | | | | exact Hnb].
  - clear - H. induction H as [| x y PS PS' Hxy _ IH]; [constructor |].
    constructor; [| auto]. destruct x as [[a sh] P], y as [[a' sh'] P']; cbn in *. tauto.
  - clear - H. induction H as [| x y PS PS' Hxy _ IH]; [constructor |].
    constructor; [| auto]. destruct x as [[a sh] P], y as [[a' sh'] P']; cbn in *.
    destruct Hxy as (_ & _ & (-> & _) & _). apply writable_Ews.
  - clear - H Hch. revert head Hch. induction H as [| x y PS PS' Hxy _ IH]; intros head Hch; [exact Hch |].
    destruct x as [[a sh] P], y as [[a' sh'] P']; cbn in *.
    destruct Hxy as (-> & -> & _ & Hpk). destruct Hch as [-> Hch]. split; [reflexivity |].
    rewrite Hpk. apply IH, Hch.
  - unfold hnodes_peers4 in *. rewrite Hnp. symmetry. apply (hcr5_p3_rnd_map L), H.
  - rewrite (hcr5_p3_rnd_map L _ _ H). exact Hnd.
Qed.

(* ---------------------------------------------------------------------- *)
(* the node list: segments                                                *)
(* ---------------------------------------------------------------------- *)

Fixpoint hcr5_p3_seg (l e: val) (NS: list hnode4) : mpred :=
  match NS with
  | [] => !! (l = e) && emp
  | N :: NS' =>
      !! (l = hn_addr N) &&
      EX nx: val,
        @malloc_token W_consume_response_any Ews t_hnode4 l *
        @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) l *
        @malloc_token W_consume_response_any Ews t_peer (hn_p N) *
        hcr5_p3_seg nx e NS'
  end.

Lemma hcr5_p3_seg_app l e NS1 NS2 :
  hcr5_p3_seg l e NS1 * hnodes_rep4 W_consume_response_any e NS2 |--
  hnodes_rep4 W_consume_response_any l (NS1 ++ NS2).
Proof.
  revert l; induction NS1 as [| N NS1 IH]; intros l; simpl.
  - Intros. subst. cancel.
  - Intros nx. Exists nx. entailer!. sep_apply (IH nx). cancel.
Qed.

Lemma hcr5_p3_seg_snoc l e N nx NS1 : e = hn_addr N ->
  hcr5_p3_seg l e NS1 *
  (@malloc_token W_consume_response_any Ews t_hnode4 e *
   @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) e *
   @malloc_token W_consume_response_any Ews t_peer (hn_p N)) |--
  hcr5_p3_seg l nx (NS1 ++ [N]).
Proof.
  intros He. revert l; induction NS1 as [| M NS1 IH]; intros l; simpl.
  - Intros. subst. Exists nx. entailer!.
  - Intros nx'. Exists nx'. entailer!. sep_apply (IH nx'). cancel.
Qed.

Lemma hcr5_p3_vp l NS : hnodes_rep4 W_consume_response_any l NS |-- valid_pointer l.
Proof.
  destruct NS as [| N NS]; simpl.
  - Intros. subst. apply valid_pointer_null.
  - Intros nx. subst.
    sep_apply (@data_at_valid_ptr CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N)).
    { apply readable_nonidentity, writable_readable, writable_Ews. }
    apply sepcon_valid_pointer1, derives_refl.
Qed.

Lemma hcr5_p3_pn l NS : hnodes_rep4 W_consume_response_any l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [| N NS]; simpl.
  - Intros. subst. entailer!.
  - Intros nx. subst. entailer!.
    match goal with Hf: field_compatible t_hnode4 [] _ |- _ => apply field_compatible_isptr in Hf end.
    destruct (hn_addr N); try contradiction; exact I.
Qed.

#[local] Hint Resolve hcr5_p3_vp : valid_pointer.

Lemma hcr5_p3_node_W v l :
  @data_at CKS Ews t_hnode4 v l = @data_at W_consume_response_any Ews t_hnode4 v l.
Proof.
  rewrite (@data_at_change_composite CKS W_consume_response_any _ Ews t_hnode4 v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

(* the node's value as ONE constant at W (a literal tuple mixing reptypes at CKS and W makes the kernel
   re-normalize reptype t_hnode4 at every occurrence: Qed > 600 s; hci5_P3.v) *)
Definition hcr5_p3_nv (N: hnode4) (nx: val) : @reptype W_consume_response_any t_hnode4 :=
  (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))).

Lemma hcr5_p3_node_nv N nx l :
  @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) l =
  @data_at W_consume_response_any Ews t_hnode4 (hcr5_p3_nv N nx) l.
Proof. unfold hcr5_p3_nv. apply hcr5_p3_node_W. Qed.

Lemma hcr5_p3_seg_snoc_nv l e N nx NS1 : e = hn_addr N ->
  hcr5_p3_seg l e NS1 *
  (@malloc_token W_consume_response_any Ews t_hnode4 e *
   @data_at W_consume_response_any Ews t_hnode4 (hcr5_p3_nv N nx) e *
   @malloc_token W_consume_response_any Ews t_peer (hn_p N)) |--
  hcr5_p3_seg l nx (NS1 ++ [N]).
Proof. intros He. rewrite <- hcr5_p3_node_nv. apply hcr5_p3_seg_snoc, He. Qed.

Lemma hcr5_p3_peers_snoc l y : peers_rep (l ++ [y]) = (peers_rep l * peer_item_rep y)%logic.
Proof. unfold peers_rep. rewrite iter_sepcon_app. simpl. rewrite sepcon_emp. reflexivity. Qed.

(* the items the loop does not touch (but the table and the shim) *)
Definition hcr5_p3_fix x25519 gv L FR R S (NS: list hnode4) T head : list mpred :=
  [device_rep Tsh (l_wa L) (hcr5_DAL x25519 R L); itable Tsh (l_ita L) T; ptable Tsh (l_pta L) head;
   @data_at HCS Tsh t_mident (mident_val (hcr5_IA x25519 R)) (l_ia L);
   @data_at HCS Tsh t_mident (mident_val (hcr5_IB x25519 R)) (l_ib L);
   hbytes Tsh (r5_rawa R) (l_rawa L); hbytes Tsh (r5_rawb R) (l_rawb L);
   @data_at W_consume_response_any Tsh (tptr t_hnode4) (hcr5_head NS) (l_peers L);
   hout Tsh 92 (l_img L);
   mem_mgr gv; shim_state4 gv S hcr5_w0; noise_globals gv Int64.zero; wg_consts gv; hcr5_consts gv; FR;
   @data_at_ CKS Tsh t_devsnap (l_ds L); @data_at_ CKS Tsh t_shimsnap (l_ss L);
   hout Tsh 32 (l_pub L); hout Tsh 92 (l_imga L);
   @data_at_ HCS Tsh t_mstate (l_st L); @data_at_ HCS Tsh t_mresp (l_mr L);
   @data_at_ HCS Tsh t_mstate (l_cur L);
   hout Tsh 32 (l_eraw L); hout Tsh 32 (l_ei L); @data_at_ HCS Tsh t_mstate (l_before L)].

Section Phase.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcr5_P3_ok {Espec: OracleKind} gv L FR :
  hcr5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> 
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_SA x25519 gv L FR) hcr5_P3
    (overridePost (hcr5_SA x25519 gv L FR) (hcr5_R gv)).
Proof.
  intros HH. unfold hcr5_SA, hcr5_Delta, hcr5_R, hcr5_P3. simplify_func_tycontext. abbreviate_semax.
  Intros R S NS PS head nb T.
  unfold hcr5_lvars, hcr5_scr, hcr5_world, hcr5_globs, hcr5_snaps0; cbn [app].
  assert_PROP (is_pointer_or_null (hcr5_head NS)) as Hpn.
  { sep_apply (hcr5_p3_pn (hcr5_head NS) NS). entailer!. }
  forward.
  forward_loop
    (EX NS1: list hnode4, EX NS2: list hnode4, EX PS1: list (val * share * peer),
     EX PS1': list (val * share * peer), EX PS2: list (val * share * peer), EX it: val, EX T': tstate,
     EX S': shim,
     PROPx [NS = NS1 ++ NS2; PS = PS1 ++ PS2; Forall2 (hcr5_p3_rnd L) PS1 PS1'; hnodes_peers4 NS2 PS2;
            hcr5_pool [] PS T']
     (LOCALx ([temp HR5._it it; temp HR5._nb nb] ++ hcr5_lvars gv L)
     (SEPx (hcr5_p3_fix x25519 gv L FR R S' NS T' head ++
            [hcr5_p3_seg (hcr5_head NS) it NS1; hnodes_rep4 W_consume_response_any it NS2;
             peers_rep PS1'; peers_rep PS2]))))
    continue:
    (EX NS1: list hnode4, EX N: hnode4, EX NS2: list hnode4, EX PS1: list (val * share * peer),
     EX PS1': list (val * share * peer), EX x: val * share * peer, EX y: val * share * peer,
     EX PS2: list (val * share * peer), EX nx: val, EX T': tstate, EX S': shim,
     PROPx [NS = NS1 ++ N :: NS2; PS = PS1 ++ x :: PS2; Forall2 (hcr5_p3_rnd L) PS1 PS1';
            hcr5_p3_rnd L x y; hnodes_peers4 NS2 PS2; hn_p N = peer_addr4 x; hcr5_pool [] PS T']
     (LOCALx ([temp HR5._it (hn_addr N); temp HR5._nb nb] ++ hcr5_lvars gv L)
     (SEPx (hcr5_p3_fix x25519 gv L FR R S' NS T' head ++
            [hcr5_p3_seg (hcr5_head NS) (hn_addr N) NS1;
             @malloc_token W_consume_response_any Ews t_hnode4 (hn_addr N);
             @data_at W_consume_response_any Ews t_hnode4 (hcr5_p3_nv N nx) (hn_addr N);
             @malloc_token W_consume_response_any Ews t_peer (hn_p N);
             hnodes_rep4 W_consume_response_any nx NS2;
             peers_rep PS1'; peer_item_rep y; peers_rep PS2]))))
    break: (hcr5_SA x25519 gv L FR).
  - Exists (@nil hnode4) NS (@nil (val * share * peer)) (@nil (val * share * peer)) PS (hcr5_head NS) T S.
    unfold hcr5_p3_fix, hcr5_lvars; cbn [app].
    entailer!.
    { destruct H0 as (_ & _ & _ & Hnp & _). exact Hnp. }
    simpl. entailer!.
  - Intros NS1 NS2 PS1 PS1' PS2 it T' S'. unfold hcr5_p3_fix, hcr5_lvars; cbn [app].
    forward_if.
    + destruct NS2 as [| N NS2']; [simpl hnodes_rep4; Intros; subst it; contradiction |].
      destruct PS2 as [| x PS2']; [unfold hnodes_peers4 in *; discriminate |].
      match goal with Hp: hnodes_peers4 (N :: NS2') (x :: PS2') |- _ =>
        unfold hnodes_peers4 in Hp; cbn in Hp; injection Hp as Hpx Hnp' end.
      simpl hnodes_rep4. Intros nx. subst it.
      rewrite hcr5_p3_node_nv.
      assert (Hpokx: hcr5_pok L [] x).
      { destruct H0 as (Hpok & _). rewrite Forall_forall in Hpok. apply Hpok.
        subst PS; apply in_or_app; right; left; reflexivity. }
      assert (Hpool: In (hs_addr (peer_addr4 x)) (saddrs (t_D T'))).
      { apply hcr5_p3_pool_in with PS; [assumption | subst PS; apply in_or_app; right; left; reflexivity]. }
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
      Intros vret. destruct vret as [[[[[[dead lsh] valid] birth] cki] sent] mac1]. cbn [fst snd] in *.
      forward_call tt. Intros b.
      forward_if.
      1: entailer!; match goal with Hm: _ /\ Int.repr 4 = Int.mone |- _ => destruct Hm as [_ Hm];
           apply (f_equal Int.unsigned) in Hm; rewrite Int.unsigned_repr, Int.unsigned_mone in Hm by rep_lia;
           rep_lia end.
      * forward.
        forward_call (gv, S', hcr5_w0, Tsh, l_ita L, T', hs_addr (hn_p N), @None (share * entry)).
        { unfold raw_rep. rewrite emp_sepcon. cancel. }
        Intros idx.
        Exists NS1 N NS2' PS1 PS1' (hn_p N, Ews, P)
          (hn_p N, Ews, p_rest_randomized (p_set_hs P (hs_randomized (p_hs P) st lic eph reph hash ck ts ri))
                   dead lsh valid birth cki sent mac1) PS2' nx (t_insert T' (hs_addr (hn_p N)) idx) (shim_u32 S' idx).
        unfold hcr5_p3_fix, hcr5_lvars; cbn [app raw_add]. entailer!.
        split; [apply hcr5_p3_rnd_step; auto | apply hcr5_p3_pool_insert; auto].
      * forward.
        Exists NS1 N NS2' PS1 PS1' (hn_p N, Ews, P)
          (hn_p N, Ews, p_rest_randomized (p_set_hs P (hs_randomized (p_hs P) st lic eph reph hash ck ts ri))
                   dead lsh valid birth cki sent mac1) PS2' nx T' S'.
        unfold hcr5_p3_fix, hcr5_lvars; cbn [app]. entailer!.
        apply hcr5_p3_rnd_step; auto.
    + forward. subst it.
      destruct NS2 as [| N NS2'].
      2: { simpl hnodes_rep4. Intros nx.
           assert_PROP (isptr (hn_addr N)) as Hf by entailer!.
           match goal with Hq: nullval = hn_addr N |- _ => rewrite <- Hq in Hf end. contradiction. }
      destruct PS2 as [| x PS2']; [| unfold hnodes_peers4 in *; discriminate].
      rewrite app_nil_r in *. subst NS PS.
      sep_apply (hcr5_p3_seg_app (hcr5_head NS1) nullval NS1 []). rewrite app_nil_r.
      unfold hcr5_SA. Exists R S' NS1 PS1' head nb T'.
      unfold hcr5_world, hcr5_globs, hcr5_scr, hcr5_snaps0, hcr5_lvars; cbn [app].
      entailer!.
      split; [apply hcr5_p3_list with PS1; assumption |].
      apply hcr5_p3_pool_addr with PS1; [apply (hcr5_p3_rnd_map L) |]; assumption.
  - Intros NS1 N NS2 PS1 PS1' x y PS2 nx T' S'. unfold hcr5_p3_fix, hcr5_lvars; cbn [app].
    assert_PROP (is_pointer_or_null nx) as Hnx. { sep_apply (hcr5_p3_pn nx NS2). entailer!. }
    forward.
    sep_apply (hcr5_p3_seg_snoc_nv (hcr5_head NS) (hn_addr N) N nx NS1 eq_refl).
    Exists (NS1 ++ [N]) NS2 (PS1 ++ [x]) (PS1' ++ [y]) PS2 nx T' S'.
    unfold hcr5_p3_fix, hcr5_lvars; cbn [app].
    rewrite hcr5_p3_peers_snoc.
    entailer!.
    split; [rewrite <- app_assoc; reflexivity |]. split; [rewrite <- app_assoc; reflexivity |].
    apply Forall2_app; [assumption | constructor; [assumption | constructor]].
  - unfold POSTCONDITION, abbreviate. simpl RA_normal. apply andp_left2, derives_refl.
Qed.

End Phase.
