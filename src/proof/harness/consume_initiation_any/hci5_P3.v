(* law consume_initiation_any: main's phase P3, statement 11: for (it = peers; it; it = it->next) { hs_randomize(&it->p->handshake); peer_randomize_rest(it->p); if (nondet_u8() % 4 != 0) wg_index_hashtable_insert(&itb, &it->p->handshake.entry); }.
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

#[local] Instance hci5_p3_cceK : change_composite_env CKS W_consume_initiation_any.
Proof. make_cs_preserve CKS W_consume_initiation_any. Defined.

(* ---------------------------------------------------------------------- *)
(* the index table: an insert of a pool entry keeps hci5_T_ok             *)
(* ---------------------------------------------------------------------- *)

Lemma hci5_p3_sfind_supd (D: list (val * share * entry)) a v b :
  sfind (supd D a v) b =
  match sfind D b with Some (sh, w) => Some (sh, if eq_dec b a then v else w) | None => None end.
Proof.
  induction D as [| [[x sh] w] D IH]; [reflexivity |]. cbn.
  destruct (EqDec_val x a) as [Hxa | Hxa]; cbn; destruct (EqDec_val x b) as [Hxb | Hxb]; subst; cbn; rewrite ?IH.
  all: try (destruct (EqDec_val b b); [reflexivity | congruence]).
  all: try (destruct (sfind D b) as [[sh' w'] |]; [| reflexivity]).
  all: repeat (destruct (EqDec_val _ _); try congruence); try reflexivity.
Qed.

Lemma hci5_p3_saddrs_supd (D: list (val * share * entry)) a v : saddrs (supd D a v) = saddrs D.
Proof.
  induction D as [| [[x sh] w] D IH]; [reflexivity |]. cbn.
  unfold saddrs in *. destruct (EqDec_val x a); cbn; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma hci5_p3_sh_supd (D: list (val * share * entry)) a v :
  Forall (fun d => match d with (_, sh, _) => sh = Ews end) D ->
  Forall (fun d => match d with (_, sh, _) => sh = Ews end) (supd D a v).
Proof.
  induction D as [| [[x sh] w] D IH]; intros H; [constructor |]. inversion H; subst. cbn.
  destruct (EqDec_val x a); constructor; auto.
Qed.

Lemma hci5_p3_tD_insert T a idx :
  t_D (t_insert T a idx) = t_D T \/
  exists E, t_entry T a = Some E /\ t_D (t_insert T a idx) = supd (t_D T) a (mkEntry (e_peer E) (e_type E) idx).
Proof.
  unfold t_insert, t_set_index. destruct (t_entry T a) as [E |] eqn:HE; [right | left; reflexivity].
  exists E. split; reflexivity.
Qed.

Lemma hci5_p3_peer_insert T a idx b :
  e_peer (t_entry_d (t_insert T a idx) b) = e_peer (t_entry_d T b).
Proof.
  unfold t_entry_d, t_entry. destruct (hci5_p3_tD_insert T a idx) as [-> | (E & HE & ->)]; [reflexivity |].
  rewrite hci5_p3_sfind_supd. unfold t_entry in HE.
  destruct (sfind (t_D T) b) as [[sh w] |] eqn:Hb; [| reflexivity].
  destruct (eq_dec b a) as [-> | _]; [| reflexivity].
  rewrite Hb in HE. injection HE as ->. reflexivity.
Qed.

Lemma hci5_p3_Tok_insert PS KE T a idx : hci5_T_ok PS KE T -> hci5_T_ok PS KE (t_insert T a idx).
Proof.
  intros (Ha & Hs & Hp & Hk). unfold hci5_T_ok.
  split; [| split; [| split]].
  - destruct (hci5_p3_tD_insert T a idx) as [-> | (E & _ & ->)]; [exact Ha |].
    rewrite hci5_p3_saddrs_supd. exact Ha.
  - destruct (hci5_p3_tD_insert T a idx) as [-> | (E & _ & ->)]; [exact Hs |].
    apply hci5_p3_sh_supd, Hs.
  - eapply Forall_impl; [| exact Hp]. intros x Hx. rewrite hci5_p3_peer_insert. exact Hx.
  - eapply Forall_impl; [| exact Hk]. intros e He. rewrite hci5_p3_peer_insert. exact He.
Qed.

Lemma hci5_p3_Tok_addr PS PS' KE T : map peer_addr4 PS' = map peer_addr4 PS ->
  hci5_T_ok PS KE T -> hci5_T_ok PS' KE T.
Proof.
  intros Hm (Ha & Hs & Hp & Hk). unfold hci5_T_ok.
  split; [| split; [| split]]; [| exact Hs | |].
  - rewrite Ha. f_equal. rewrite <- !(map_map peer_addr4 hs_addr), Hm. reflexivity.
  - clear Ha Hk Hs. revert PS Hm Hp. induction PS' as [| y PS' IH]; intros PS Hm Hp; [constructor |].
    destruct PS as [| x PS]; [discriminate |]. cbn in Hm. injection Hm as Hxy Hm.
    inversion Hp; subst. constructor; [rewrite Hxy; assumption | eapply IH; eauto].
  - rewrite Hm. exact Hk.
Qed.

Lemma hci5_p3_in_pool PS KE T x : hci5_T_ok PS KE T -> In x PS -> In (hs_addr (peer_addr4 x)) (saddrs (t_D T)).
Proof.
  intros (Ha & _) Hx. rewrite Ha. apply in_or_app. right. apply (in_map (fun x => hs_addr (peer_addr4 x))), Hx.
Qed.

(* ---------------------------------------------------------------------- *)
(* the randomization of one peer                                          *)
(* ---------------------------------------------------------------------- *)

Section Rnd.
Variable x25519: list byte -> list byte -> list byte.

Definition hci5_p3_rnd (R: hci5_run) (L: hci5_loc) (x y: val * share * peer) : Prop :=
  match x, y with (a, sh, P), (a', sh', P') =>
    a' = a /\ sh' = sh /\ hci5_pok x25519 R L y /\ p_pknext P' = p_pknext P /\
    p_cur P' = p_cur P /\ p_prev P' = p_prev P /\ p_next P' = p_next P
  end.

Lemma hci5_p3_rnd_step R L a sh P st lic eph reph hash ck ts ri dead lsh valid birth cki sent mac1 :
  hci5_pok x25519 R L (a, sh, P) ->
  0 <= Int64.unsigned lic < 2 ^ 62 -> Zlength eph = 32 -> Zlength reph = 32 -> Zlength hash = 32 ->
  Zlength ck = 32 -> Zlength ts = 12 ->
  hci5_p3_rnd R L (a, sh, P)
    (a, sh, p_rest_randomized (p_set_hs P (hs_randomized (p_hs P) st lic eph reph hash ck ts ri))
              dead lsh valid birth cki sent mac1).
Proof.
  intros (Hsh & Hdev & Hsid & Hok & Hss & Hrefs & Hlic & Hpk) H1 H2 H3 H4 H5 H6.
  unfold hci5_p3_rnd, hci5_pok, hs_ok in *; cbn. intuition.
Qed.

Lemma hci5_p3_rnd_addr R L x y : hci5_p3_rnd R L x y -> peer_addr4 y = peer_addr4 x.
Proof. destruct x as [[a sh] P], y as [[a' sh'] P']; cbn; tauto. Qed.

Lemma hci5_p3_rnd_map R L PS PS' : Forall2 (hci5_p3_rnd R L) PS PS' -> map peer_addr4 PS' = map peer_addr4 PS.
Proof.
  induction 1 as [| x y PS PS' Hxy _ IH]; [reflexivity |]. cbn. rewrite IH, (hci5_p3_rnd_addr _ _ _ _ Hxy).
  reflexivity.
Qed.

Lemma hci5_p3_inv R L NS PS PS' T head na :
  Forall2 (hci5_p3_rnd R L) PS PS' -> hci5_inv x25519 R L NS PS [] T head na ->
  hci5_inv x25519 R L NS PS' [] T head na.
Proof.
  intros H (Hpok & Hwf & Hch & Hnp & Hna & HT & Hsl). unfold hci5_inv.
  split; [| split; [| split; [| split; [| split; [| split]]]]]; [| | | | exact Hna | |].
  - clear - H. induction H as [| x y PS PS' Hxy _ IH]; [constructor |].
    constructor; [| auto]. destruct x as [[a sh] P], y as [[a' sh'] P']; cbn in *. tauto.
  - clear - H. induction H as [| x y PS PS' Hxy _ IH]; [constructor |].
    constructor; [| auto]. destruct x as [[a sh] P], y as [[a' sh'] P']; cbn in *.
    destruct Hxy as (_ & _ & (-> & _) & _). apply writable_Ews.
  - clear - H Hch. revert head Hch. induction H as [| x y PS PS' Hxy _ IH]; intros head Hch; [exact Hch |].
    destruct x as [[a sh] P], y as [[a' sh'] P']; cbn in *.
    destruct Hxy as (-> & -> & _ & Hpk & _). destruct Hch as [-> Hch]. split; [reflexivity |].
    rewrite Hpk. apply IH, Hch.
  - unfold hnodes_peers4 in *. rewrite Hnp. symmetry. apply (hci5_p3_rnd_map R L), H.
  - apply (hci5_p3_Tok_addr PS); [apply (hci5_p3_rnd_map R L), H | exact HT].
  - clear - H Hsl. induction H as [| x y PS PS' Hxy _ IH]; [constructor |].
    inversion Hsl; subst. constructor; [| apply IH; exact H2].
    destruct x as [[a sh] P], y as [[a' sh'] P']; cbn in *.
    destruct Hxy as (_ & _ & _ & _ & -> & -> & ->). assumption.
Qed.

End Rnd.

(* ---------------------------------------------------------------------- *)
(* the node list: segments                                                *)
(* ---------------------------------------------------------------------- *)

Fixpoint hci5_p3_seg (l e: val) (NS: list hnode4) : mpred :=
  match NS with
  | [] => !! (l = e) && emp
  | N :: NS' =>
      !! (l = hn_addr N) &&
      EX nx: val,
        @malloc_token W_consume_initiation_any Ews t_hnode4 l *
        @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) l *
        @malloc_token W_consume_initiation_any Ews t_peer (hn_p N) *
        hci5_p3_seg nx e NS'
  end.

Lemma hci5_p3_seg_app l e NS1 NS2 :
  hci5_p3_seg l e NS1 * hnodes_rep4 W_consume_initiation_any e NS2 |--
  hnodes_rep4 W_consume_initiation_any l (NS1 ++ NS2).
Proof.
  revert l; induction NS1 as [| N NS1 IH]; intros l; simpl.
  - Intros. subst. cancel.
  - Intros nx. Exists nx. entailer!. sep_apply (IH nx). cancel.
Qed.

Lemma hci5_p3_seg_snoc l e N nx NS1 : e = hn_addr N ->
  hci5_p3_seg l e NS1 *
  (@malloc_token W_consume_initiation_any Ews t_hnode4 e *
   @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) e *
   @malloc_token W_consume_initiation_any Ews t_peer (hn_p N)) |--
  hci5_p3_seg l nx (NS1 ++ [N]).
Proof.
  intros He. revert l; induction NS1 as [| M NS1 IH]; intros l; simpl.
  - Intros. subst. Exists nx. entailer!.
  - Intros nx'. Exists nx'. entailer!. sep_apply (IH nx'). cancel.
Qed.

Lemma hci5_p3_vp l NS : hnodes_rep4 W_consume_initiation_any l NS |-- valid_pointer l.
Proof.
  destruct NS as [| N NS]; simpl.
  - Intros. subst. apply valid_pointer_null.
  - Intros nx. subst.
    sep_apply (@data_at_valid_ptr CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N)).
    { apply readable_nonidentity, writable_readable, writable_Ews. }
    apply sepcon_valid_pointer1, derives_refl.
Qed.

Lemma hci5_p3_pn l NS : hnodes_rep4 W_consume_initiation_any l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [| N NS]; simpl.
  - Intros. subst. entailer!.
  - Intros nx. subst. entailer!.
    match goal with Hf: field_compatible t_hnode4 [] _ |- _ => apply field_compatible_isptr in Hf end.
    destruct (hn_addr N); try contradiction; exact I.
Qed.

#[local] Hint Resolve hci5_p3_vp : valid_pointer.

Lemma hci5_p3_node_W v l :
  @data_at CKS Ews t_hnode4 v l = @data_at W_consume_initiation_any Ews t_hnode4 v l.
Proof.
  rewrite (@data_at_change_composite CKS W_consume_initiation_any _ Ews t_hnode4 v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

(* the node's value as ONE constant at W (a literal tuple mixing reptypes at CKS and W makes the kernel
   re-normalize reptype t_hnode4 at every occurrence: Qed > 600 s) *)
Definition hci5_p3_nv (N: hnode4) (nx: val) : @reptype W_consume_initiation_any t_hnode4 :=
  (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))).

Lemma hci5_p3_node_nv N nx l :
  @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) l =
  @data_at W_consume_initiation_any Ews t_hnode4 (hci5_p3_nv N nx) l.
Proof. unfold hci5_p3_nv. apply hci5_p3_node_W. Qed.

Lemma hci5_p3_seg_snoc_nv l e N nx NS1 : e = hn_addr N ->
  hci5_p3_seg l e NS1 *
  (@malloc_token W_consume_initiation_any Ews t_hnode4 e *
   @data_at W_consume_initiation_any Ews t_hnode4 (hci5_p3_nv N nx) e *
   @malloc_token W_consume_initiation_any Ews t_peer (hn_p N)) |--
  hci5_p3_seg l nx (NS1 ++ [N]).
Proof. intros He. rewrite <- hci5_p3_node_nv. apply hci5_p3_seg_snoc, He. Qed.

Lemma hci5_p3_peers_snoc l y : peers_rep (l ++ [y]) = (peers_rep l * peer_item_rep y)%logic.
Proof. unfold peers_rep. rewrite iter_sepcon_app. simpl. rewrite sepcon_emp. reflexivity. Qed.

Lemma hci5_p3_inv2 x25519 R L NS PS PS' T T' head na :
  Forall2 (hci5_p3_rnd x25519 R L) PS PS' -> hci5_inv x25519 R L NS PS [] T head na -> hci5_T_ok PS [] T' ->
  hci5_inv x25519 R L NS PS' [] T' head na.
Proof.
  intros H Hinv HT. apply hci5_p3_inv with PS; [exact H |].
  destruct Hinv as (A1 & A2 & A3 & A4 & A5 & _ & A7). unfold hci5_inv. tauto.
Qed.

(* the items the loop does not touch (but the table and the shim) *)
Definition hci5_p3_fix x25519 gv L FR R S w (NS: list hnode4) T head : list mpred :=
  [device_rep Tsh (l_wb L) (hci5_DB x25519 R L); itable Tsh (l_itb L) T; ptable Tsh (l_ptb L) head;
   @data_at HCS Tsh t_mident (mident_val (hci5_IA x25519 R)) (l_ia L);
   @data_at HCS Tsh t_mident (mident_val (hci5_IB x25519 R)) (l_ib L);
   hbytes Tsh (r_rawa R) (l_rawa L); hbytes Tsh (r_rawb R) (l_rawb L);
   @data_at W_consume_initiation_any Tsh (tptr t_hnode4) (hci5_head NS) (l_peers L);
   hout Tsh 148 (l_img L);
   mem_mgr gv; shim_state4 gv S w; noise_globals gv Int64.zero; wg_consts gv; hci5_consts gv; FR;
   @data_at_ CKS Tsh t_devsnap (l_ds L); @data_at_ CKS Tsh t_shimsnap (l_ss L);
   hout Tsh 32 (l_pub L); hout Tsh 12 (l_ts L); hout Tsh 148 (l_imga L);
   @data_at_ HCS Tsh t_mcinit (l_ci L); @data_at_ HCS Tsh t_minit (l_mi L);
   hout Tsh 32 (l_eraw L); hout Tsh 32 (l_ss1 L); hout Tsh 32 (l_ss2 L)].

Section P3.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hci5_P3_ok {Espec: OracleKind} gv L FR :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> 
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_SA x25519 gv L FR) hci5_P3
    (overridePost (hci5_SA x25519 gv L FR) (hci5_R gv)).
Proof.
  intros HH. unfold hci5_SA, hci5_Delta, hci5_R, hci5_P3. simplify_func_tycontext. abbreviate_semax.
  Intros R S w NS PS T head na.
  unfold hci5_lvars, hci5_scr, hci5_world, hci5_globs, hci5_snaps0; cbn [app].
  assert_PROP (is_pointer_or_null (hci5_head NS)) as Hpn.
  { sep_apply (hci5_p3_pn (hci5_head NS) NS). entailer!. }
  forward.
  forward_loop
    (EX NS1: list hnode4, EX NS2: list hnode4, EX PS1: list (val * share * peer),
     EX PS1': list (val * share * peer), EX PS2: list (val * share * peer), EX it: val, EX T': tstate,
     EX S': shim,
     PROPx [NS = NS1 ++ NS2; PS = PS1 ++ PS2; Forall2 (hci5_p3_rnd x25519 R L) PS1 PS1'; hnodes_peers4 NS2 PS2;
            hci5_T_ok PS [] T']
     (LOCALx ([temp HC._it it; temp HC._na na] ++ hci5_lvars gv L)
     (SEPx (hci5_p3_fix x25519 gv L FR R S' w NS T' head ++
            [hci5_p3_seg (hci5_head NS) it NS1; hnodes_rep4 W_consume_initiation_any it NS2;
             peers_rep PS1'; peers_rep PS2]))))
    continue:
    (EX NS1: list hnode4, EX N: hnode4, EX NS2: list hnode4, EX PS1: list (val * share * peer),
     EX PS1': list (val * share * peer), EX x: val * share * peer, EX y: val * share * peer,
     EX PS2: list (val * share * peer), EX nx: val, EX T': tstate, EX S': shim,
     PROPx [NS = NS1 ++ N :: NS2; PS = PS1 ++ x :: PS2; Forall2 (hci5_p3_rnd x25519 R L) PS1 PS1';
            hci5_p3_rnd x25519 R L x y; hnodes_peers4 NS2 PS2; hn_p N = peer_addr4 x; hci5_T_ok PS [] T']
     (LOCALx ([temp HC._it (hn_addr N); temp HC._na na] ++ hci5_lvars gv L)
     (SEPx (hci5_p3_fix x25519 gv L FR R S' w NS T' head ++
            [hci5_p3_seg (hci5_head NS) (hn_addr N) NS1;
             @malloc_token W_consume_initiation_any Ews t_hnode4 (hn_addr N);
             @data_at W_consume_initiation_any Ews t_hnode4 (hci5_p3_nv N nx) (hn_addr N);
             @malloc_token W_consume_initiation_any Ews t_peer (hn_p N);
             hnodes_rep4 W_consume_initiation_any nx NS2;
             peers_rep PS1'; peer_item_rep y; peers_rep PS2]))))
    break: (hci5_SA x25519 gv L FR).
  - Exists (@nil hnode4) NS (@nil (val * share * peer)) (@nil (val * share * peer)) PS (hci5_head NS) T S.
    unfold hci5_p3_fix, hci5_lvars; cbn [app].
    entailer!.
    { destruct H0 as (_ & _ & _ & Hnp & _ & HT & _). split; [exact Hnp | exact HT]. }
    simpl. entailer!.
  - Intros NS1 NS2 PS1 PS1' PS2 it T' S'. unfold hci5_p3_fix, hci5_lvars; cbn [app].
    forward_if.
    + destruct NS2 as [| N NS2']; [simpl hnodes_rep4; Intros; subst it; contradiction |].
      destruct PS2 as [| x PS2']; [unfold hnodes_peers4 in *; discriminate |].
      match goal with Hp: hnodes_peers4 (N :: NS2') (x :: PS2') |- _ =>
        unfold hnodes_peers4 in Hp; cbn in Hp; injection Hp as Hpx Hnp' end.
      simpl hnodes_rep4. Intros nx. subst it.
      rewrite hci5_p3_node_nv.
      assert (Hpokx: hci5_pok x25519 R L x).
      { destruct H0 as (Hpok & _). rewrite Forall_forall in Hpok. apply Hpok.
        subst PS; apply in_or_app; right; left; reflexivity. }
      assert (Hpool: In (hs_addr (peer_addr4 x)) (saddrs (t_D T'))).
      { apply hci5_p3_in_pool with PS []; [exact H5 | subst PS; apply in_or_app; right; left; reflexivity]. }
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
        forward_call (gv, S', w, Tsh, l_itb L, T', hs_addr (hn_p N), @None (share * entry)).
        { unfold raw_rep. rewrite emp_sepcon. cancel. }
        Intros idx.
        Exists NS1 N NS2' PS1 PS1' (hn_p N, Ews, P)
          (hn_p N, Ews, p_rest_randomized (p_set_hs P (hs_randomized (p_hs P) st lic eph reph hash ck ts ri))
                   dead lsh valid birth cki sent mac1) PS2' nx (t_insert T' (hs_addr (hn_p N)) idx) (shim_u32 S' idx).
        unfold hci5_p3_fix, hci5_lvars; cbn [app raw_add]. entailer!.
        split; [apply hci5_p3_rnd_step; auto | apply hci5_p3_Tok_insert; auto].
      * forward.
        Exists NS1 N NS2' PS1 PS1' (hn_p N, Ews, P)
          (hn_p N, Ews, p_rest_randomized (p_set_hs P (hs_randomized (p_hs P) st lic eph reph hash ck ts ri))
                   dead lsh valid birth cki sent mac1) PS2' nx T' S'.
        unfold hci5_p3_fix, hci5_lvars; cbn [app]. entailer!.
        apply hci5_p3_rnd_step; auto.
    + forward. subst it.
      destruct NS2 as [| N NS2'].
      2: { simpl hnodes_rep4. Intros nx.
           assert_PROP (isptr (hn_addr N)) as Hf by entailer!.
           match goal with Hq: nullval = hn_addr N |- _ => rewrite <- Hq in Hf end. contradiction. }
      destruct PS2 as [| x PS2']; [| unfold hnodes_peers4 in *; discriminate].
      rewrite app_nil_r in *. subst NS PS.
      sep_apply (hci5_p3_seg_app (hci5_head NS1) nullval NS1 []). rewrite app_nil_r.
      unfold hci5_SA. Exists R S' w NS1 PS1' T' head na.
      unfold hci5_world, hci5_globs, hci5_scr, hci5_snaps0, hci5_lvars; cbn [app].
      entailer!.
      apply hci5_p3_inv2 with PS1 T; assumption.
  - Intros NS1 N NS2 PS1 PS1' x y PS2 nx T' S'. unfold hci5_p3_fix, hci5_lvars; cbn [app].
    assert_PROP (is_pointer_or_null nx) as Hnx. { sep_apply (hci5_p3_pn nx NS2). entailer!. }
    forward.
    sep_apply (hci5_p3_seg_snoc_nv (hci5_head NS) (hn_addr N) N nx NS1 eq_refl).
    Exists (NS1 ++ [N]) NS2 (PS1 ++ [x]) (PS1' ++ [y]) PS2 nx T' S'.
    unfold hci5_p3_fix, hci5_lvars; cbn [app].
    rewrite hci5_p3_peers_snoc.
    entailer!.
    split; [rewrite <- app_assoc; reflexivity |]. split; [rewrite <- app_assoc; reflexivity |].
    apply Forall2_app; [assumption | constructor; [assumption | constructor]].
  - unfold POSTCONDITION, abbreviate. simpl RA_normal. apply andp_left2, derives_refl.
Qed.

End P3.
