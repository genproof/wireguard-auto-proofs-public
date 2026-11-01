(* law handshake_clear: main's phase P7, statements 19..20: hashed = 0; for (nd = peers; nd; nd = nd->next) { if (nd == target) continue; CHECK(hs_same_but_next(&nd->snap, &nd->p->handshake) && refcount == refs && pr_same(&nd->rest, nd->p)); if (nd->snap.hashed) { CHECK(table_has(&it, &nd->p->handshake.entry)); hashed++; } }.
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
Require Import WgNoise.proof.harness.handshake_clear.hcl5_p7_defs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_p7_chk.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_p7_hif.
Require WgNoise.harness.x_handshake_clear.code.

#[local] Existing Instance W_handshake_clear.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* pure lemmas                                                             *)
(* ---------------------------------------------------------------------- *)

Lemma hcl5_p7_len_snap T NS PS : Zlength NS = Zlength PS -> Zlength (hnodes_snapped4 T NS PS) = Zlength NS.
Proof. intros H. unfold hnodes_snapped4. rewrite Zlength_map, Zlength_combine. lia. Qed.

Lemma hcl5_p7_addr_snap T NS PS : Zlength NS = Zlength PS -> map hn_addr (hnodes_snapped4 T NS PS) = map hn_addr NS.
Proof.
  revert PS; induction NS as [| N NS IH]; intros [| x PS] H; try reflexivity.
  - rewrite Zlength_cons, Zlength_nil in H. pose proof (Zlength_nonneg NS). lia.
  - rewrite !Zlength_cons in H. destruct x as [[a sh] P]. cbn. f_equal. apply IH. lia.
Qed.

Lemma hcl5_p7_Znth_snap T NS PS k : Zlength NS = Zlength PS -> 0 <= k < Zlength NS ->
  Znth k (hnodes_snapped4 T NS PS) = hn_snapshot4 T (Znth k NS) (Znth k PS).
Proof.
  intros H Hk. unfold hnodes_snapped4. rewrite Znth_map by (rewrite Zlength_combine; lia).
  rewrite Znth_combine by exact H. reflexivity.
Qed.

Lemma hcl5_p7_len NS PS : hnodes_peers4 NS PS -> Zlength NS = Zlength PS.
Proof.
  unfold hnodes_peers4. intros H.
  rewrite <- (Zlength_map _ _ hn_p NS), <- (Zlength_map _ _ peer_addr4 PS), H. reflexivity.
Qed.

Lemma hcl5_p7_hnp NS PS k : hnodes_peers4 NS PS -> 0 <= k < Zlength NS -> hn_p (Znth k NS) = peer_addr4 (Znth k PS).
Proof.
  intros H Hk. pose proof (hcl5_p7_len _ _ H) as HL. unfold hnodes_peers4 in H.
  rewrite <- (Znth_map k hn_p) by lia. rewrite H, Znth_map by lia. reflexivity.
Qed.

Lemma hcl5_p7_nh_snoc T p l x : hcl5_nh T p (l ++ [x]) =
  hcl5_nh T p l + (if andb (negb (veqb (peer_addr4 x) p)) (vin (hs_addr (peer_addr4 x)) (t_L T)) then 1 else 0).
Proof.
  unfold hcl5_nh. rewrite filter_app, Zlength_app. cbn [filter].
  destruct (andb _ _); reflexivity.
Qed.

Lemma hcl5_p7_firstn_S {A} {d: Inhabitant A} (l: list A) k : 0 <= k < Zlength l ->
  firstn (Z.to_nat (k + 1)) l = firstn (Z.to_nat k) l ++ [Znth k l].
Proof.
  intros Hk. rewrite <- !sublist_firstn. rewrite (sublist_split 0 k (k + 1)) by lia.
  rewrite sublist_len_1 by lia. reflexivity.
Qed.

Lemma hcl5_p7_skipn_S {A} {d: Inhabitant A} (l: list A) k : 0 <= k < Zlength l ->
  skipn (Z.to_nat k) l = Znth k l :: skipn (Z.to_nat (k + 1)) l.
Proof.
  intros Hk. rewrite <- !sublist_skip by lia. rewrite (sublist_split k (k + 1) (Zlength l)) by lia.
  rewrite sublist_len_1 by lia. reflexivity.
Qed.

Lemma hcl5_p7_skipn_end {A} (l: list A) : skipn (Z.to_nat (Zlength l)) l = [].
Proof. rewrite Zlength_correct, Nat2Z.id. apply skipn_all. Qed.

Lemma hcl5_p7_firstn_end {A} (l: list A) : firstn (Z.to_nat (Zlength l)) l = l.
Proof. rewrite Zlength_correct, Nat2Z.id. apply firstn_all. Qed.

Lemma hcl5_p7_head_map A B : map hn_addr A = map hn_addr B -> hcl5_head A = hcl5_head B.
Proof. destruct A, B; cbn; intros H; try discriminate; [reflexivity | injection H as H _; exact H]. Qed.

Lemma hcl5_p7_in_firstn {A} {d: Inhabitant A} (l: list A) i k : 0 <= i < k -> k <= Zlength l ->
  In (Znth i l) (firstn (Z.to_nat k) l).
Proof.
  intros Hi Hk. rewrite <- sublist_firstn.
  replace (Znth i l) with (Znth i (sublist 0 k l)) by (rewrite Znth_sublist by lia; f_equal; lia).
  apply Znth_In. rewrite Zlength_sublist by lia. lia.
Qed.

Lemma hcl5_p7_in_skipn {A} {d: Inhabitant A} (l: list A) i k : 0 <= k <= i -> i < Zlength l ->
  In (Znth i l) (skipn (Z.to_nat k) l).
Proof.
  intros Hi Hk. rewrite <- sublist_skip by lia.
  replace (Znth i l) with (Znth (i - k) (sublist k (Zlength l) l)) by (rewrite Znth_sublist by lia; f_equal; lia).
  apply Znth_In. rewrite Zlength_sublist by lia. lia.
Qed.

Lemma hcl5_p7_head_skip A B k : map hn_addr A = map hn_addr B ->
  hcl5_head (skipn k A) = hcl5_head (skipn k B).
Proof. intros H. apply hcl5_p7_head_map. rewrite <- !skipn_map, H. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* the node list                                                           *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hcl5_p7_cceK : change_composite_env CKS W_handshake_clear.
Proof. make_cs_preserve CKS W_handshake_clear. Defined.

Lemma hcl5_p7_seg_app l e NS1 NS2 :
  hcl5_p7_seg l e NS1 * hnodes_rep4 W_handshake_clear e NS2 |--
  hnodes_rep4 W_handshake_clear l (NS1 ++ NS2).
Proof.
  revert l; induction NS1 as [| N NS1 IH]; intros l; simpl.
  - Intros. subst. cancel.
  - Intros nx. Exists nx. entailer!. sep_apply (IH nx). cancel.
Qed.

Lemma hcl5_p7_seg_snoc l e N nx NS1 : e = hn_addr N ->
  hcl5_p7_seg l e NS1 *
  (@malloc_token W_handshake_clear Ews t_hnode4 e *
   @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) e *
   @malloc_token W_handshake_clear Ews t_peer (hn_p N)) |--
  hcl5_p7_seg l nx (NS1 ++ [N]).
Proof.
  intros He. revert l; induction NS1 as [| M NS1 IH]; intros l; simpl.
  - Intros. subst. Exists nx. entailer!.
  - Intros nx'. Exists nx'. entailer!. sep_apply (IH nx'). cancel.
Qed.

Lemma hcl5_p7_vp l NS : hnodes_rep4 W_handshake_clear l NS |-- valid_pointer l.
Proof.
  destruct NS as [| N NS]; simpl.
  - Intros. subst. apply valid_pointer_null.
  - Intros nx. subst.
    sep_apply (@data_at_valid_ptr CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N)).
    { apply readable_nonidentity, writable_readable, writable_Ews. }
    apply sepcon_valid_pointer1, derives_refl.
Qed.

Lemma hcl5_p7_pn l NS : hnodes_rep4 W_handshake_clear l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [| N NS]; simpl.
  - Intros. subst. entailer!.
  - Intros nx. subst. entailer!.
    match goal with Hf: field_compatible t_hnode4 [] _ |- _ => apply field_compatible_isptr in Hf end.
    destruct (hn_addr N); try contradiction; exact I.
Qed.

#[local] Hint Resolve hcl5_p7_vp : valid_pointer.

Lemma hcl5_p7_rep_head l NS : hnodes_rep4 W_handshake_clear l NS |-- !! (l = hcl5_head NS).
Proof. destruct NS as [| N NS]; simpl; [Intros; entailer! | Intros nx; entailer!]. Qed.

Lemma hcl5_p7_nin_aux a v l NS :
  @data_at CKS Ews t_hnode4 v a * hnodes_rep4 W_handshake_clear l NS |-- !! (~ In a (map hn_addr NS)).
Proof.
  revert l; induction NS as [| N NS IH]; intros l; simpl.
  - Intros. apply prop_right. auto.
  - Intros nx. subst l.
    destruct (eq_dec a (hn_addr N)) as [-> | Hne].
    + sep_apply (@data_at_conflict CKS Ews t_hnode4 v
                   (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N)).
      { apply readable_nonidentity, writable_readable, writable_Ews. }
      rewrite !FF_sepcon. apply FF_left.
    + sep_apply (IH nx). Intros. apply prop_right. intros [Hx | Hx]; [congruence | contradiction].
Qed.

Lemma hcl5_p7_nodup l NS : hnodes_rep4 W_handshake_clear l NS |-- !! NoDup (map hn_addr NS).
Proof.
  revert l; induction NS as [| N NS IH]; intros l; simpl.
  - Intros. apply prop_right. constructor.
  - Intros nx. subst l.
    match goal with |- ?A |-- _ => apply derives_trans with (!! (~ In (hn_addr N) (map hn_addr NS)) && A) end.
    { apply andp_right; [| apply derives_refl].
      sep_apply (hcl5_p7_nin_aux (hn_addr N) (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) nx NS).
      Intros. apply prop_right. assumption. }
    apply derives_extract_prop; intros Hn. sep_apply (IH nx). Intros. apply prop_right. constructor; assumption.
Qed.

Lemma hcl5_p7_seg_vp a l e NS : In a (map hn_addr NS) -> hcl5_p7_seg l e NS |-- valid_pointer a.
Proof.
  revert l; induction NS as [| N NS IH]; intros l Ha; simpl in *; [contradiction |].
  Intros nx. subst l. destruct Ha as [<- | Ha].
  - apply sepcon_valid_pointer1, sepcon_valid_pointer1, sepcon_valid_pointer2.
    apply data_at_valid_ptr; [apply readable_nonidentity, writable_readable, writable_Ews | simpl; lia].
  - apply sepcon_valid_pointer2, IH, Ha.
Qed.

Lemma hcl5_p7_rep_vp a l NS : In a (map hn_addr NS) -> hnodes_rep4 W_handshake_clear l NS |-- valid_pointer a.
Proof.
  revert l; induction NS as [| N NS IH]; intros l Ha; simpl in *; [contradiction |].
  Intros nx. subst l. destruct Ha as [<- | Ha].
  - apply sepcon_valid_pointer1, sepcon_valid_pointer1, sepcon_valid_pointer2.
    apply data_at_valid_ptr; [apply readable_nonidentity, writable_readable, writable_Ews | simpl; lia].
  - apply sepcon_valid_pointer2, IH, Ha.
Qed.

Lemma hcl5_p7_node_W v l :
  @data_at CKS Ews t_hnode4 v l = @data_at W_handshake_clear Ews t_hnode4 v l.
Proof.
  rewrite (@data_at_change_composite CKS W_handshake_clear _ Ews t_hnode4 v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hcl5_p7_seg_snocW l e N nx NS1 : e = hn_addr N ->
  hcl5_p7_seg l e NS1 *
  (@malloc_token W_handshake_clear Ews t_hnode4 e *
   @data_at W_handshake_clear Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) e *
   @malloc_token W_handshake_clear Ews t_peer (hn_p N)) |--
  hcl5_p7_seg l nx (NS1 ++ [N]).
Proof. intros He. rewrite <- hcl5_p7_node_W. apply hcl5_p7_seg_snoc, He. Qed.

(* the cell of the node of peer (q, Ews, Q) as the W constant hcl5_p7_nv (no reptype conversion in the loop) *)
Lemma hcl5_p7_nvN_eq q sn Q nx l :
  @data_at CKS Ews t_hnode4 (q, (hsnap_val sn, (Vint (p_refs Q), (prsnap_val Q, nx)))) l =
  @data_at W_handshake_clear Ews t_hnode4 (hcl5_p7_nv q sn Q nx) l.
Proof. unfold hcl5_p7_nv. apply hcl5_p7_node_W. Qed.

Lemma hcl5_p7_rep_cons_nv l a q sn Q NS :
  hnodes_rep4 W_handshake_clear l (mkHN4 a q (hsnap_val sn) (Vint (p_refs Q)) (prsnap_val Q) :: NS) =
  (!! (l = a) && EX nx: val,
     @malloc_token W_handshake_clear Ews t_hnode4 l *
     @data_at W_handshake_clear Ews t_hnode4 (hcl5_p7_nv q sn Q nx) l *
     @malloc_token W_handshake_clear Ews t_peer q *
     hnodes_rep4 W_handshake_clear nx NS).
Proof.
  unfold hnodes_rep4 at 1; fold (hnodes_rep4 W_handshake_clear). cbn [hn_p hn_snap hn_refs hn_rest hn_addr].
  apply pred_ext.
  - Intros nx. apply andp_right; [apply prop_right; auto |]. Exists nx.
    apply sepcon_derives; [| apply derives_refl]. apply sepcon_derives; [| apply derives_refl].
    apply sepcon_derives; [apply derives_refl |].
    apply derives_refl'. apply hcl5_p7_nvN_eq.
  - Intros nx. apply andp_right; [apply prop_right; auto |]. Exists nx.
    apply sepcon_derives; [| apply derives_refl]. apply sepcon_derives; [| apply derives_refl].
    apply sepcon_derives; [apply derives_refl |].
    apply derives_refl'. symmetry. apply hcl5_p7_nvN_eq.
Qed.

Lemma hcl5_p7_seg_snoc_nv l e q sn Q nx NS1 :
  hcl5_p7_seg l e NS1 *
  (@malloc_token W_handshake_clear Ews t_hnode4 e *
   @data_at W_handshake_clear Ews t_hnode4 (hcl5_p7_nv q sn Q nx) e *
   @malloc_token W_handshake_clear Ews t_peer q) |--
  hcl5_p7_seg l nx (NS1 ++ [mkHN4 e q (hsnap_val sn) (Vint (p_refs Q)) (prsnap_val Q)]).
Proof.
  unfold hcl5_p7_nv.
  exact (hcl5_p7_seg_snocW l e (mkHN4 e q (hsnap_val sn) (Vint (p_refs Q)) (prsnap_val Q)) nx NS1 eq_refl).
Qed.

(* the node without its link, and the link: the load of nd->next without unfolding hcl5_p7_nv *)
Definition hcl5_p7_nhead (q: val) (sn: hsnap) (Q: peer) (l: val) : mpred :=
  (@field_at W_handshake_clear Ews t_hnode4 (DOT HCL._p) q l *
  @field_at W_handshake_clear Ews t_hnode4 (DOT HCL._snap) (hsnap_val sn) l *
  @field_at W_handshake_clear Ews t_hnode4 (DOT HCL._refs) (Vint (p_refs Q)) l *
  spacer Ews 300 304 l *
  @field_at W_handshake_clear Ews t_hnode4 (DOT HCL._rest) (prsnap_val Q) l)%logic.

Lemma hcl5_p7_next_split q sn Q nx l :
  @data_at W_handshake_clear Ews t_hnode4 (hcl5_p7_nv q sn Q nx) l =
  (hcl5_p7_nhead q sn Q l * @field_at W_handshake_clear Ews t_hnode4 (DOT HCL._next) nx l)%logic.
Proof.
  unfold hcl5_p7_nv, hcl5_p7_nhead. unfold_data_at (data_at _ _ _ l).
  rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma hcl5_p7_seg_snoc_snap l T N x nx NS1 q Q : x = (q, Ews, Q) -> hn_p N = q ->
  hcl5_p7_seg l (hn_addr N) NS1 *
  (@malloc_token W_handshake_clear Ews t_hnode4 (hn_addr N) *
   @data_at W_handshake_clear Ews t_hnode4 (hcl5_p7_nv q (hs_snap_cur T q Q) Q nx) (hn_addr N) *
   @malloc_token W_handshake_clear Ews t_peer q) |--
  hcl5_p7_seg l nx (NS1 ++ [hn_snapshot4 T N x]).
Proof.
  intros -> Hq. unfold hn_snapshot4. rewrite <- Hq.
  apply hcl5_p7_seg_snoc_nv.
Qed.

Lemma hcl5_p7_next_join q sn Q nx l :
  hcl5_p7_nhead q sn Q l * @field_at W_handshake_clear Ews t_hnode4 (DOT HCL._next) nx l |--
  @data_at W_handshake_clear Ews t_hnode4 (hcl5_p7_nv q sn Q nx) l.
Proof. rewrite hcl5_p7_next_split. apply derives_refl. Qed.

(* a segment's postcondition (overridePost Q (hcl5_R gv)) inside the loop body *)
Lemma hcl5_p7_post_seg {Espec: OracleKind} Delta P c Q X Y gv :
  semax Delta P c (overridePost Q (hcl5_R gv)) ->
  semax Delta P c (overridePost Q (loop1_ret_assert X (overridePost Y (hcl5_R gv)))).
Proof.
  intros H. eapply semax_post; [| | | | apply H]; intros; unfold hcl5_R; simpl; intros rho;
    try (apply andp_left2; apply derives_refl).
  - apply andp_left2. normalize.
  - apply andp_left2. normalize.
Qed.

Lemma hcl5_p7_post_cont {Espec: OracleKind} Delta P c Q X Y gv :
  (Q |-- X) ->
  semax Delta P c (overridePost Q (hcl5_R gv)) ->
  semax Delta P c (loop1_ret_assert X (overridePost Y (hcl5_R gv))).
Proof.
  intros HQ H. eapply semax_post; [| | | | apply H]; intros; unfold hcl5_R; simpl; intros rho;
    try (apply andp_left2; apply derives_refl).
  - apply andp_left2. apply HQ.
  - apply andp_left2. normalize.
  - apply andp_left2. normalize.
Qed.

Section P7.
Variable x25519: list byte -> list byte -> list byte.

(* S5 with its existentials given *)
Definition hcl5_p7_S5i gv L FR R S w NS PS T head KE i : environ -> mpred :=
  PROPx [hcl5_run_ok R; hcl5_inv L NS PS KE T head; 0 <= i < Zlength NS]
  (LOCALx ([temp HC._kes (hcl5_khead KE); temp HC._target (hn_addr (Znth i NS));
            temp HC._h (hs_addr (hn_p (Znth i NS)))] ++ hcl5_lvars gv L)
  (SEPx (hcl5_world x25519 R L NS (hnodes_snapped4 T NS PS) (t_remove T (hs_addr (hn_p (Znth i NS)))) head ++
         [peers_rep (hcl5_clr i PS); kents_rep W (hcl5_khead KE) (map (kent_snapped T) KE);
          @data_at CKS Tsh t_devsnap (devsnap_val (hcl5_D x25519 R L) head) (l_ds L);
          @data_at CKS Tsh t_shimsnap (shimsnap_val S w) (l_ss L)] ++
         hcl5_globs gv S w FR ++ hcl5_scr L))).

Definition hcl5_p7_I gv L FR R S w NS PS T head KE i : environ -> mpred :=
  EX k: Z, hcl5_p7_inv x25519 gv L FR R S w NS PS T head KE i k.

(* after `if (!nd) break;`: at the node k, the count before it *)
Definition hcl5_p7_A gv L FR R S w NS PS T head KE i k : environ -> mpred :=
  EX nx: val, EX q: val, EX Q: peer,
  hcl5_p7_Q x25519 gv L FR R S w NS PS T head KE i k nx q Q (hcl5_nh T (hn_p (Znth i NS)) (firstn (Z.to_nat k) PS)) [].

(* the loop body's ret_assert *)
Definition hcl5_p7_RL gv L FR R S w NS PS T head KE i : ret_assert :=
  loop1_ret_assert (hcl5_p7_cont x25519 gv L FR R S w NS PS T head KE i)
    (overridePost (hcl5_S7 x25519 gv L FR) (hcl5_R gv)).

Lemma hcl5_p7_init_ok {Espec: OracleKind} gv L FR R S w NS PS T head KE i :
  semax (hcl5_Delta x25519) (hcl5_p7_S5i gv L FR R S w NS PS T head KE i) (Ssequence hcl5_p7_s0 hcl5_p7_s1)
    (overridePost (hcl5_p7_I gv L FR R S w NS PS T head KE i) (hcl5_R gv)).
Proof.
  unfold hcl5_p7_S5i, hcl5_Delta, hcl5_R, hcl5_p7_s0, hcl5_p7_s1. simplify_func_tycontext. abbreviate_semax.
  unfold hcl5_world, hcl5_globs, hcl5_lvars, hcl5_scr; cbn [app]. Intros.
  match goal with Hi: hcl5_inv _ _ _ _ _ _ |- _ => rename Hi into Hinv end.
  assert (HL: Zlength NS = Zlength PS) by (destruct Hinv as (_ & _ & _ & Hnp & _); apply hcl5_p7_len, Hnp).
  assert (HA: map hn_addr (hnodes_snapped4 T NS PS) = map hn_addr NS) by (apply hcl5_p7_addr_snap, HL).
  assert_PROP (NoDup (map hn_addr NS)) as Hnd.
  { sep_apply (hcl5_p7_nodup (hcl5_head NS) (hnodes_snapped4 T NS PS)). rewrite HA. entailer!. }
  assert_PROP (is_pointer_or_null (hcl5_head NS)) as Hpn.
  { sep_apply (hcl5_p7_pn (hcl5_head NS) (hnodes_snapped4 T NS PS)). entailer!. }
  forward. forward.
  unfold hcl5_p7_I. Exists 0. unfold hcl5_p7_inv, hcl5_p7_fix, hcl5_lvars; cbn [app].
  unfold hcl5_p7_at. simpl firstn. simpl skipn. simpl hcl5_p7_seg.
  entailer!.
Qed.

Lemma hcl5_p7_ifb_ok {Espec: OracleKind} gv L FR R S w NS PS T head KE i k :
  semax (hcl5_Delta x25519) (hcl5_p7_inv x25519 gv L FR R S w NS PS T head KE i k) hcl5_p7_ifb
    (overridePost (hcl5_p7_A gv L FR R S w NS PS T head KE i k) (hcl5_p7_RL gv L FR R S w NS PS T head KE i)).
Proof.
  unfold hcl5_p7_inv, hcl5_p7_RL, hcl5_Delta, hcl5_R, hcl5_p7_ifb. simplify_func_tycontext. abbreviate_semax.
  unfold hcl5_p7_fix, hcl5_lvars; cbn [app]. Intros.
  match goal with Hi: hcl5_inv _ _ _ _ _ _ |- _ => rename Hi into Hinv end.
  assert (HL: Zlength NS = Zlength PS) by (destruct Hinv as (_ & _ & _ & Hnp & _); apply hcl5_p7_len, Hnp).
  destruct (Z.eq_dec k (Zlength NS)) as [Hk | Hk].
  - subst k.
    assert (E1: skipn (Z.to_nat (Zlength NS)) (hnodes_snapped4 T NS PS) = []).
    { rewrite <- (hcl5_p7_len_snap T NS PS HL). apply hcl5_p7_skipn_end. }
    assert (E2: hcl5_p7_at NS (Zlength NS) = nullval).
    { unfold hcl5_p7_at. rewrite hcl5_p7_skipn_end. reflexivity. }
    assert (E3: firstn (Z.to_nat (Zlength NS)) (hnodes_snapped4 T NS PS) = hnodes_snapped4 T NS PS).
    { rewrite <- (hcl5_p7_len_snap T NS PS HL). apply hcl5_p7_firstn_end. }
    assert (E4: firstn (Z.to_nat (Zlength NS)) PS = PS) by (rewrite HL; apply hcl5_p7_firstn_end).
    rewrite E1, E2, E3, E4.
    forward_if; [contradiction |].
    forward. unfold hcl5_S7. Exists R S w NS PS T head KE i.
    unfold hcl5_world, hcl5_globs, hcl5_lvars, hcl5_scr; cbn [app].
    sep_apply (hcl5_p7_seg_app (hcl5_head NS) nullval (hnodes_snapped4 T NS PS) []). rewrite app_nil_r.
    entailer!.
  - assert (Hk': 0 <= k < Zlength NS) by lia. clear Hk.
    rewrite (hcl5_p7_skipn_S (hnodes_snapped4 T NS PS) k) by (rewrite hcl5_p7_len_snap by exact HL; lia).
    assert (E2: hcl5_p7_at NS k = hn_addr (Znth k NS)).
    { unfold hcl5_p7_at. rewrite (hcl5_p7_skipn_S NS k) by lia. reflexivity. }
    rewrite E2.
    rewrite (hcl5_p7_Znth_snap T NS PS k HL Hk').
    assert (Hpk: hn_p (Znth k NS) = peer_addr4 (Znth k PS)).
    { destruct Hinv as (_ & _ & _ & Hnp & _). apply hcl5_p7_hnp; assumption. }
    destruct (Znth k PS) as [[q sh] Q] eqn:HPk.
    assert (Hsh: sh = Ews).
    { destruct Hinv as (Hpok & _). rewrite Forall_forall in Hpok.
      assert (Hin: In (q, sh, Q) PS) by (rewrite <- HPk; apply Znth_In; lia).
      apply Hpok in Hin. destruct Hin as [Hs _]. exact Hs. }
    subst sh. cbn [hn_snapshot4 peer_addr4] in Hpk |- *. rewrite Hpk.
    rewrite hcl5_p7_rep_cons_nv. Intros nx.
    assert_PROP (isptr (hn_addr (Znth k NS))) as Hptr.
    { entailer!; match goal with Hf: field_compatible t_hnode4 [] _ |- _ => exact (field_compatible_isptr _ _ _ Hf) end. }
    forward_if.
    2: { match goal with Hn: _ = nullval |- _ => change (hn_addr (Znth k NS) = nullval) in Hn; rewrite Hn in Hptr;
           contradiction end. }
    forward. unfold hcl5_p7_A. Exists nx q Q.
    unfold hcl5_p7_Q, hcl5_p7_fix, hcl5_lvars; cbn [app]. entailer!.
Qed.

Lemma hcl5_p7_ifc_ok {Espec: OracleKind} gv L FR R S w NS PS T head KE i k nx q Q :
  semax (hcl5_Delta x25519)
    (hcl5_p7_Q x25519 gv L FR R S w NS PS T head KE i k nx q Q (hcl5_nh T (hn_p (Znth i NS)) (firstn (Z.to_nat k) PS)) [])
    hcl5_p7_ifc
    (overridePost (hcl5_p7_Q0 x25519 gv L FR R S w NS PS T head KE i k nx q Q) (hcl5_p7_RL gv L FR R S w NS PS T head KE i)).
Proof.
  unfold hcl5_p7_Q, hcl5_p7_RL, hcl5_Delta, hcl5_R, hcl5_p7_ifc. simplify_func_tycontext. abbreviate_semax.
  unfold hcl5_p7_fix, hcl5_lvars; cbn [app]. Intros.
  match goal with Hi: hcl5_inv _ _ _ _ _ _ |- _ => rename Hi into Hinv end.
  match goal with Hp: Znth k PS = _ |- _ => rename Hp into HPk end.
  assert (HL: Zlength NS = Zlength PS) by (destruct Hinv as (_ & _ & _ & Hnp & _); apply hcl5_p7_len, Hnp).
  assert (HA: map hn_addr (hnodes_snapped4 T NS PS) = map hn_addr NS) by (apply hcl5_p7_addr_snap, HL).
  assert (Hpk: hn_p (Znth k NS) = q).
  { destruct Hinv as (_ & _ & _ & Hnp & _). rewrite (hcl5_p7_hnp NS PS k Hnp), HPk by lia. reflexivity. }
  forward_if.
  { apply denote_tc_test_eq_split.
    - auto 50 with valid_pointer.
    - destruct (Z.lt_trichotomy i k) as [Hik | [Hik | Hik]].
      + assert (Hin: In (hn_addr (Znth i NS)) (map hn_addr (firstn (Z.to_nat k) (hnodes_snapped4 T NS PS)))).
        { rewrite <- firstn_map, HA. rewrite <- (Znth_map i hn_addr) by lia.
          apply hcl5_p7_in_firstn; [lia | rewrite Zlength_map; lia]. }
        sep_apply (hcl5_p7_seg_vp (hn_addr (Znth i NS)) (hcl5_head NS) (hn_addr (Znth k NS)) _ Hin).
        auto 50 with valid_pointer.
      + subst i. auto 50 with valid_pointer.
      + assert (Hin: In (hn_addr (Znth i NS))
                      (map hn_addr (skipn (Z.to_nat (k + 1)) (hnodes_snapped4 T NS PS)))).
        { rewrite <- skipn_map, HA. rewrite <- (Znth_map i hn_addr) by lia.
          apply hcl5_p7_in_skipn; [lia | rewrite Zlength_map; lia]. }
        sep_apply (hcl5_p7_rep_vp (hn_addr (Znth i NS)) nx _ Hin). auto 50 with valid_pointer. }
  { assert (k = i).
    { apply (NoDup_Znth_inj (map hn_addr NS) k i); auto; rewrite ?Zlength_map; try lia.
      rewrite !Znth_map by lia. assumption. }
    subst i. forward.
    unfold hcl5_p7_cont, hcl5_p7_Q1, hcl5_p7_Q, hcl5_p7_fix, hcl5_lvars; cbn [app]. Exists k nx q Q.
    rewrite (hcl5_p7_firstn_S PS k) by lia. rewrite hcl5_p7_nh_snoc, HPk. cbn [peer_addr4].
    assert (Hv: veqb q (hn_p (Znth k NS)) = true)
      by (rewrite Hpk; unfold veqb; destruct (eq_dec q q); congruence).
    rewrite Hv. cbn [negb andb]. rewrite Z.add_0_r.
    entailer!. }
  forward. unfold hcl5_p7_Q0, hcl5_p7_Q, hcl5_p7_fix, hcl5_lvars; cbn [app].
  entailer!.
Qed.

Lemma hcl5_p7_incr_ok {Espec: OracleKind} gv L FR R S w NS PS T head KE i k nx q Q :
  semax (hcl5_Delta x25519) (hcl5_p7_Q1 x25519 gv L FR R S w NS PS T head KE i k nx q Q) hcl5_p7_incr
    (loop2_ret_assert (hcl5_p7_I gv L FR R S w NS PS T head KE i)
       (overridePost (hcl5_S7 x25519 gv L FR) (hcl5_R gv))).
Proof.
  unfold hcl5_p7_Q1, hcl5_p7_Q, hcl5_Delta, hcl5_R, hcl5_p7_incr. simplify_func_tycontext. abbreviate_semax.
  unfold hcl5_p7_fix, hcl5_lvars; cbn [app]. Intros.
  match goal with Hi: hcl5_inv _ _ _ _ _ _ |- _ => rename Hi into Hinv end.
  match goal with Hp: Znth k PS = _ |- _ => rename Hp into HPk end.
  assert (HL: Zlength NS = Zlength PS) by (destruct Hinv as (_ & _ & _ & Hnp & _); apply hcl5_p7_len, Hnp).
  assert (HA: map hn_addr (hnodes_snapped4 T NS PS) = map hn_addr NS) by (apply hcl5_p7_addr_snap, HL).
  assert (Hk': 0 <= k < Zlength NS) by lia.
  assert (HLs: Zlength (hnodes_snapped4 T NS PS) = Zlength NS) by apply (hcl5_p7_len_snap T NS PS HL).
  assert (Hpk: hn_p (Znth k NS) = q).
  { destruct Hinv as (_ & _ & _ & Hnp & _). rewrite (hcl5_p7_hnp NS PS k Hnp Hk'), HPk. reflexivity. }
  assert_PROP (nx = hcl5_head (skipn (Z.to_nat (k + 1)) (hnodes_snapped4 T NS PS))) as Hnx.
  { sep_apply (hcl5_p7_rep_head nx (skipn (Z.to_nat (k + 1)) (hnodes_snapped4 T NS PS))). entailer!. }
  assert_PROP (is_pointer_or_null nx) as Hnxp.
  { sep_apply (hcl5_p7_pn nx (skipn (Z.to_nat (k + 1)) (hnodes_snapped4 T NS PS))). entailer!. }
  rewrite (hcl5_p7_next_split q (hs_snap_cur T q Q) Q nx (hn_addr (Znth k NS))). Intros.
  forward.
  sep_apply (hcl5_p7_next_join q (hs_snap_cur T q Q) Q nx (hn_addr (Znth k NS))).
  unfold hcl5_p7_I. Exists (k + 1). unfold hcl5_p7_inv, hcl5_p7_fix, hcl5_lvars; cbn [app].
  assert (E: hcl5_p7_at NS (k + 1) = nx).
  { unfold hcl5_p7_at. rewrite Hnx. symmetry. apply hcl5_p7_head_skip, HA. }
  rewrite E.
  rewrite (hcl5_p7_firstn_S (hnodes_snapped4 T NS PS) k) by lia.
  rewrite (hcl5_p7_Znth_snap T NS PS k HL Hk').
  sep_apply (hcl5_p7_seg_snoc_snap (hcl5_head NS) T (Znth k NS) (Znth k PS) nx
               (firstn (Z.to_nat k) (hnodes_snapped4 T NS PS)) q Q HPk Hpk).
  entailer!.
Qed.

Lemma hcl5_P7_ok {Espec: OracleKind} gv L FR :
  hcl5_hyps x25519 ->
  semax (hcl5_Delta x25519) (hcl5_S5 x25519 gv L FR) hcl5_P7
    (overridePost (hcl5_S7 x25519 gv L FR) (hcl5_R gv)).
Proof.
  intros HH. unfold hcl5_S5.
  apply extract_exists_pre; intro R. apply extract_exists_pre; intro S.
  apply extract_exists_pre; intro w. apply extract_exists_pre; intro NS.
  apply extract_exists_pre; intro PS. apply extract_exists_pre; intro T.
  apply extract_exists_pre; intro head. apply extract_exists_pre; intro KE.
  apply extract_exists_pre; intro i.
  rewrite hcl5_p7_P7_eq. apply <- seq_assoc.
  eapply semax_seq.
  { rewrite overridePost_overridePost. apply (hcl5_p7_init_ok gv L FR R S w NS PS T head KE i). }
  apply semax_loop with (Q' := hcl5_p7_cont x25519 gv L FR R S w NS PS T head KE i).
  - unfold hcl5_p7_I at 1. apply extract_exists_pre; intro k.
    rewrite hcl5_p7_body_eq.
    eapply semax_seq; [apply (hcl5_p7_ifb_ok gv L FR R S w NS PS T head KE i k) |].
    unfold hcl5_p7_A. apply extract_exists_pre; intro nx. apply extract_exists_pre; intro q.
    apply extract_exists_pre; intro Q.
    eapply semax_seq; [apply (hcl5_p7_ifc_ok gv L FR R S w NS PS T head KE i k nx q Q) |].
    eapply semax_seq.
    { apply hcl5_p7_post_seg, (hcl5_p7_chk_ok x25519 gv L FR R S w NS PS T head KE i k nx q Q HH). }
    eapply hcl5_p7_post_cont; [| apply (hcl5_p7_hif_ok x25519 gv L FR R S w NS PS T head KE i k nx q Q HH)].
    unfold hcl5_p7_cont. Exists k nx q Q. apply derives_refl.
  - unfold hcl5_p7_cont. apply extract_exists_pre; intro k. apply extract_exists_pre; intro nx.
    apply extract_exists_pre; intro q. apply extract_exists_pre; intro Q.
    apply (hcl5_p7_incr_ok gv L FR R S w NS PS T head KE i k nx q Q).
Qed.

End P7.
