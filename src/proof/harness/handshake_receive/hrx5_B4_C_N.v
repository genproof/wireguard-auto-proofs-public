(* law handshake_receive, phase B4, segment C, part N:
   the node search (sN): port of cookie_reply's hcy5_p11_B.  Cut and states: hrx5_B4_C_defs.v. *)
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
#[local] Existing Instance W_handshake_receive.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_C_defs.
Local Open Scope logic.

Require Import WgNoise.proof.protocol.prot_cs.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol.prot3_shim_table2_ilookup.
Module HRM := WgNoise.harness.x_handshake_receive.code.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* pure facts                                                              *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B4_C_N_nfind_found A B p :
  hrx5_nfind A p <> nullval -> hrx5_nfind (A ++ B) p = hrx5_nfind A p.
Proof.
  induction A as [| N A IH]; simpl; intros H; [contradiction |].
  destruct (EqDec_val (hn_p N) p); auto.
Qed.

Lemma hrx5_B4_C_N_nfind_null A B p :
  Forall isptr (map hn_addr A) -> hrx5_nfind A p = nullval -> hrx5_nfind (A ++ B) p = hrx5_nfind B p.
Proof.
  induction A as [| N A IH]; simpl; intros HF H; auto.
  inversion HF as [| ? ? Hc HF']; subst.
  destruct (EqDec_val (hn_p N) p).
  - rewrite H in Hc. contradiction.
  - auto.
Qed.

Lemma hrx5_B4_C_N_nfind_in A p :
  hrx5_nfind A p = nullval \/ In (hrx5_nfind A p) (map hn_addr A).
Proof.
  induction A as [| N A IH]; simpl; [auto |].
  destruct (EqDec_val (hn_p N) p); auto.
  destruct IH as [H | H]; auto.
Qed.

Lemma hrx5_B4_C_N_nfind_one N p :
  hrx5_nfind [N] p = if EqDec_val (hn_p N) p then hn_addr N else nullval.
Proof. reflexivity. Qed.

Lemma hrx5_B4_C_N_nfind_snapped T NS PS p :
  hnodes_peers4 NS PS -> hrx5_nfind (hnodes_snapped4 T NS PS) p = hrx5_nfind NS p.
Proof.
  unfold hnodes_peers4, hnodes_snapped4. revert PS.
  induction NS as [| N NS IH]; intros PS Hm; destruct PS as [| x PS]; simpl in *; try discriminate; auto.
  injection Hm as _ Hm. destruct x as [[q sh] P]. cbn [hn_snapshot4 hn_p hn_addr].
  destruct (EqDec_val (hn_p N) p); auto.
Qed.

Lemma hrx5_B4_C_N_p_snapped T NS PS :
  hnodes_peers4 NS PS -> map hn_p (hnodes_snapped4 T NS PS) = map peer_addr4 PS.
Proof.
  unfold hnodes_peers4, hnodes_snapped4. revert PS.
  induction NS as [| N NS IH]; intros PS Hm; destruct PS as [| x PS]; simpl in *; try discriminate; auto.
  injection Hm as H1 Hm. destruct x as [[q sh] P]. cbn [hn_snapshot4 hn_p]. simpl in H1.
  f_equal; auto.
Qed.

Lemma hrx5_B4_C_N_forall2_in {X Y: Type} (Rr: X -> Y -> Prop) l1 l2 y :
  Forall2 Rr l1 l2 -> In y l2 -> exists x, In x l1 /\ Rr x y.
Proof.
  intros HF. induction HF as [| x y' l1 l2 Hr HF IH]; simpl; intros Hin; [contradiction |].
  destruct Hin as [<- | Hin].
  - exists x. auto.
  - destruct (IH Hin) as (x' & ? & ?). exists x'. auto.
Qed.

Lemma hrx5_B4_C_N_pool_peer KA PS T a sh E :
  hrx5cr_pool KA PS T -> In (a, sh, E) (t_D T) -> In (e_peer E) (map peer_addr4 PS).
Proof.
  intros [H1 H2] Hin.
  rewrite <- (firstn_skipn (length KA) (t_D T)) in Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  - destruct (hrx5_B4_C_N_forall2_in _ _ _ _ H1 Hin) as (k & _ & (_ & _ & Hp & _)).
    replace (map peer_addr4 PS) with (map hrx5cr_paddr PS) by (apply map_ext; intros [[x s] P]; reflexivity).
    exact Hp.
  - destruct (hrx5_B4_C_N_forall2_in _ _ _ _ H2 Hin) as ([[p s] P] & Hy & (_ & _ & Hp & _)).
    rewrite Hp. apply in_map_iff. exists (p, s, P). auto.
Qed.

Lemma hrx5_B4_C_N_t0_none NS T M :
  t_find_index T (t_L T) (cm_receiver M) = None -> hrx5_B4_C_t0 NS T M = nullval.
Proof. intros H. unfold hrx5_B4_C_t0, t_lookup. rewrite H. reflexivity. Qed.

Lemma hrx5_B4_C_N_t0_some NS T M a E :
  t_find_index T (t_L T) (cm_receiver M) = Some (a, E) ->
  hrx5_B4_C_t0 NS T M =
  if Int.eq (Int.and (e_type E) (Int.or IDX_HANDSHAKE IDX_KEYPAIR)) Int.zero then nullval
  else hrx5_nfind NS (e_peer E).
Proof.
  intros H. unfold hrx5_B4_C_t0, t_lookup. rewrite H.
  destruct (Int.eq _ _); reflexivity.
Qed.

Lemma hrx5_B4_C_N_head_pn NS1 N NS2 :
  Forall isptr (map hn_addr (NS1 ++ N :: NS2)) -> is_pointer_or_null (hrx5_head NS2).
Proof.
  intros Hf. rewrite map_app, Forall_app in Hf. destruct Hf as [_ Hf]. inversion Hf; subst.
  destruct NS2 as [|N2 NS2]; simpl; auto. inversion H2; subst. destruct (hn_addr N2); try contradiction; exact I.
Qed.

(* ---------------------------------------------------------------------- *)
(* separation logic                                                        *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hrx5_B4_C_N_cceK : change_composite_env CKS W_handshake_receive.
Proof. make_cs_preserve CKS W_handshake_receive. Defined.
#[local] Instance hrx5_B4_C_N_cceN : change_composite_env Noise.CS W_handshake_receive.
Proof. make_cs_preserve Noise.CS W_handshake_receive. Defined.

Lemma hrx5_B4_C_N_peer_valid sh p P : readable_share sh -> peer_rep sh p P |-- valid_pointer p.
Proof.
  intros Hsh. unfold peer_rep. Intros.
  repeat apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; [apply readable_nonidentity; auto | simpl; lia | reflexivity].
Qed.

Lemma hrx5_B4_C_N_peers_valid PS q :
  Forall (fun x => readable_share (snd (fst x))) PS -> In q (map peer_addr4 PS) -> peers_rep PS |-- valid_pointer q.
Proof.
  unfold peers_rep. induction PS as [|[[a sh] P] PS IH]; simpl; intros Hwf Hq; [contradiction|].
  inversion Hwf; subst. destruct Hq as [<-|Hq].
  - apply sepcon_valid_pointer1. apply hrx5_B4_C_N_peer_valid; auto.
  - apply sepcon_valid_pointer2. apply IH; auto.
Qed.

Lemma hrx5_B4_C_N_peers_ptr PS : peers_rep PS |-- !! Forall (fun x => isptr (peer_addr4 x)) PS.
Proof.
  unfold peers_rep. induction PS as [| [[a sh] P] PS IH]; simpl.
  - entailer!.
  - sep_apply IH. unfold peer_rep. entailer!. constructor; auto. destruct H0 as [Hp _]. exact Hp.
Qed.

Lemma hrx5_B4_C_N_KW sh (v: @reptype CKS t_hnode4) x :
  @data_at CKS sh t_hnode4 v x = @data_at W_handshake_receive sh t_hnode4 v x.
Proof. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

Lemma hrx5_B4_C_N_hhead l NS : hnodes_rep4 W l NS |-- !! (l = hrx5_head NS).
Proof. destruct NS as [|N NS]; simpl; entailer!. Qed.

Lemma hrx5_B4_C_N_hn_valid l NS a : In a (map hn_addr NS) -> hnodes_rep4 W l NS |-- valid_pointer a.
Proof.
  revert l; induction NS as [|N NS IH]; intros l Hin; simpl in *; [contradiction|].
  Intros nx. destruct Hin as [<-|Hin].
  - subst l. auto with valid_pointer.
  - apply sepcon_valid_pointer2, IH, Hin.
Qed.

Lemma hrx5_B4_C_N_hn_isptr l NS : hnodes_rep4 W l NS |-- !! Forall isptr (map hn_addr NS).
Proof.
  revert l; induction NS as [|N NS IH]; intros l; simpl; [entailer!|].
  Intros nx. sep_apply (IH nx). entailer!.
  constructor; auto.
  match goal with Hf: field_compatible t_hnode4 [] _ |- _ => destruct Hf; auto end.
Qed.

(* a node's value as ONE constant at W *)
Definition hrx5_B4_C_N_nv (N: hnode4) (nx: val) : @reptype W_handshake_receive t_hnode4 :=
  (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))).

Lemma hrx5_B4_C_N_wand_frame (A B C F: mpred) : A * B |-- C -> A * (F * (F -* B)) |-- F * (F -* C).
Proof.
  intros H. rewrite <- sepcon_assoc, (sepcon_comm A F), sepcon_assoc.
  apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint. eapply derives_trans; [| exact H].
  rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl |].
  rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hrx5_B4_C_N_node NS1 N NS2 l :
  hnodes_rep4 W l (NS1 ++ N :: NS2) |--
  @data_at W_handshake_receive Ews t_hnode4 (hrx5_B4_C_N_nv N (hrx5_head NS2)) (hn_addr N) *
  (@data_at W_handshake_receive Ews t_hnode4 (hrx5_B4_C_N_nv N (hrx5_head NS2)) (hn_addr N) -*
   hnodes_rep4 W l (NS1 ++ N :: NS2)).
Proof.
  unfold hrx5_B4_C_N_nv. rewrite <- hrx5_B4_C_N_KW.
  revert l; induction NS1 as [|N0 NS1 IH]; intros l; simpl hnodes_rep4; simpl app.
  - Intros nx. subst l.
    sep_apply (hrx5_B4_C_N_hhead nx NS2). Intros. subst nx.
    apply derives_trans with
      (@malloc_token W Ews t_hnode4 (hn_addr N) * @malloc_token W Ews t_peer (hn_p N) *
       hnodes_rep4 W (hrx5_head NS2) NS2 *
       (@data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, hrx5_head NS2)))) (hn_addr N) *
        (@data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, hrx5_head NS2)))) (hn_addr N) -*
         @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, hrx5_head NS2)))) (hn_addr N))))%logic.
    + sep_apply (wand_refl_cancel_right (@data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, hrx5_head NS2)))) (hn_addr N))).
      cancel.
    + apply hrx5_B4_C_N_wand_frame. Exists (hrx5_head NS2). entailer!.
  - Intros nx. subst l.
    apply derives_trans with
      (@malloc_token W Ews t_hnode4 (hn_addr N0) *
       @data_at CKS Ews t_hnode4 (hn_p N0, (hn_snap N0, (hn_refs N0, (hn_rest N0, nx)))) (hn_addr N0) *
       @malloc_token W Ews t_peer (hn_p N0) *
       (@data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, hrx5_head NS2)))) (hn_addr N) *
        (@data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, hrx5_head NS2)))) (hn_addr N) -*
         hnodes_rep4 W nx (NS1 ++ N :: NS2))))%logic.
    + sep_apply (IH nx). cancel.
    + apply hrx5_B4_C_N_wand_frame. Exists nx. entailer!.
Qed.

Lemma hrx5_B4_C_N_wand1 (A Q: mpred) : A * (A -* Q) |-- Q.
Proof. apply wand_frame_elim. Qed.

(* ---- D's table: the entry at a focused at the world ---- *)
Lemma hrx5_B4_C_N_entry_W sh a E nx h :
  entry_at sh a E nx h = @data_at W_handshake_receive sh t_entry_s (entry_val E nx h) a.
Proof.
  unfold entry_at.
  rewrite (@data_at_change_composite Noise.CS W_handshake_receive hrx5_B4_C_N_cceN sh t_entry_s
    (entry_val E nx h) (entry_val E nx h) (JMeq_refl _) eq_refl). reflexivity.
Qed.

Definition hrx5_B4_C_N_trest (sht: share) (tab: val) (T: tstate) (a: val) : mpred :=
  (@data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab * iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) a))%logic.

Lemma hrx5_B4_C_N_open sht tab T a sh E : sfind (t_D T) a = Some (sh, E) -> In a (t_L T) ->
  itable sht tab T |--
  !! (itable_wf T /\ writable_share sh) &&
  (hrx5_B4_C_N_trest sht tab T a *
   @data_at W_handshake_receive sh t_entry_s (entry_val E (succ_in (t_L T) a) true) a).
Proof.
  intros Hs HL. unfold itable, hrx5_B4_C_N_trest. Intros.
  assert (WS: writable_share sh).
  { destruct H as (_ & _ & _ & H4). apply prot_rep3_sfind_In in Hs. rewrite Forall_forall in H4.
    apply (H4 _ Hs). }
  rewrite (prot_rep3_split _ _ _ _ _ Hs).
  change (pool_item_rep (t_L T) (a, sh, E)) with (entry_at sh a E (succ_in (t_L T) a) (vin a (t_L T))).
  assert (Hv: vin a (t_L T) = true) by (unfold vin; destruct (in_dec eq_dec a (t_L T)); [reflexivity|contradiction]).
  rewrite Hv, hrx5_B4_C_N_entry_W. entailer!.
Qed.

Lemma hrx5_B4_C_N_close sht tab T a sh E : sfind (t_D T) a = Some (sh, E) -> In a (t_L T) -> itable_wf T ->
  hrx5_B4_C_N_trest sht tab T a *
  @data_at W_handshake_receive sh t_entry_s (entry_val E (succ_in (t_L T) a) true) a
  |-- itable sht tab T.
Proof.
  intros Hs HL WF. unfold itable, hrx5_B4_C_N_trest.
  rewrite (prot_rep3_split _ _ _ _ _ Hs).
  change (pool_item_rep (t_L T) (a, sh, E)) with (entry_at sh a E (succ_in (t_L T) a) (vin a (t_L T))).
  assert (Hv: vin a (t_L T) = true) by (unfold vin; destruct (in_dec eq_dec a (t_L T)); [reflexivity|contradiction]).
  rewrite Hv, hrx5_B4_C_N_entry_W. entailer!.
Qed.

Lemma hrx5_B4_C_N_head_pn0 NS :
  Forall isptr (map hn_addr NS) -> is_pointer_or_null (hrx5_head NS).
Proof.
  intros Hf. destruct NS as [|N NS]; simpl; auto. inversion Hf; subst.
  destruct (hn_addr N); try contradiction; exact I.
Qed.

Lemma hrx5_B4_C_N_tg_valid l NS' NS1 NS2 p :
  NS' = NS1 ++ NS2 -> hnodes_rep4 W l NS' |-- valid_pointer (hrx5_nfind NS1 p).
Proof.
  intros HN. destruct (hrx5_B4_C_N_nfind_in NS1 p) as [H | H].
  - rewrite H. apply valid_pointer_null.
  - apply hrx5_B4_C_N_hn_valid. rewrite HN, map_app. apply in_or_app. left. exact H.
Qed.

Lemma hrx5_B4_C_N_snoc_eq NS1 N p :
  Forall isptr (map hn_addr NS1) -> hrx5_nfind NS1 p = nullval -> hn_p N = p ->
  hrx5_nfind (NS1 ++ [N]) p = hn_addr N.
Proof.
  intros HF Hn Heq. rewrite hrx5_B4_C_N_nfind_null by auto. simpl.
  destruct (EqDec_val (hn_p N) p); [reflexivity | contradiction].
Qed.

Lemma hrx5_B4_C_N_snoc_ne NS1 N p :
  Forall isptr (map hn_addr NS1) -> hn_p N <> p -> hrx5_nfind (NS1 ++ [N]) p = hrx5_nfind NS1 p.
Proof.
  intros HF Hne. destruct (EqDec_val (hrx5_nfind NS1 p) nullval) as [Hn | Hn].
  - rewrite hrx5_B4_C_N_nfind_null by auto. simpl.
    destruct (EqDec_val (hn_p N) p); [contradiction | auto].
  - apply hrx5_B4_C_N_nfind_found; auto.
Qed.

Lemma hrx5_B4_C_N_nfind_ptr NS1 p :
  Forall isptr (map hn_addr NS1) -> hrx5_nfind NS1 p <> nullval -> isptr (hrx5_nfind NS1 p).
Proof.
  intros HF Hn. destruct (hrx5_B4_C_N_nfind_in NS1 p) as [H | H]; [contradiction |].
  rewrite Forall_forall in HF. auto.
Qed.

Ltac hrx5_B4_C_N_absurd := exfalso; first
  [ match goal with H: ?x <> ?x |- _ => apply H; reflexivity end
  | match goal with H: Int.one = Int.zero |- _ => discriminate H end
  | match goal with H: Int.zero = Int.one |- _ => discriminate H end
  | match goal with H: false = true |- _ => discriminate H end
  | match goal with H: true = false |- _ => discriminate H end
  | contradiction | congruence ].

Ltac hrx5_B4_C_N_ent :=
  cbv beta iota delta [hrx5_RB loop1_ret_assert overridePost hrx5_R frame_ret_assert function_body_ret_assert
                       normal_ret_assert RA_break RA_normal]; entailer!.

Lemma hrx5_B4_C_N_ok : hrx5_B4_C_N_stmt.
Proof.
  unfold hrx5_B4_C_N_stmt. intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR
    R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img HH.
  unfold hrx5_B4_C_st, hrx5_B4_C_scr, hrx5_Delta, hrx5_RB, hrx5_B4_C_sN, hrx5_ltemps, hrx5_ptrs, hrx5_lvars,
    hrx5_wcore, hrx5_rest, hrx5_globs.
  cbn [app obj_bytes obj_kind obj_rep obj_ok].
  simplify_func_tycontext. abbreviate_semax. Intros.
  pose proof H0 as (Hpok & Hpwf & Hnd & Hch & Hnp & Hnk & Hpool).
  unfold hrx5_B4_C_ewalk.
  destruct (t_find_index T (t_L T) (cm_receiver M)) as [[a E]|] eqn:Hf.
  2: {
    match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HM._t'89 (Vint Int.zero) :: Lc) (SEPx Sp))) end.
    { hrx5_B4_C_N_absurd. }
    { forward. entailer!. }
    forward_if.
    { hrx5_B4_C_N_absurd. }
    forward.
    rewrite (hrx5_B4_C_N_t0_none NS T M Hf).
    hrx5_B4_C_N_ent. }
  destruct (prot3_ilookup_find_some _ _ _ _ _ Hf) as [HaL HtE].
  unfold t_entry in HtE. destruct (sfind (t_D T) a) as [[she E']|] eqn:Hsf; [| discriminate].
  injection HtE as HE. subst E'.
  assert (HpE: In (e_peer E) (map peer_addr4 PS)).
  { eapply hrx5_B4_C_N_pool_peer; [exact Hpool |]. eapply prot_rep3_sfind_In; eauto. }
  sep_apply (hrx5_B4_C_N_open Tsh (l_itd L) T a she E Hsf HaL). Intros.
  assert_PROP (isptr a) as Hpa by entailer!.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HM._t'89 (Vint (if Int.eq (Int.and (e_type E) (Int.or IDX_HANDSHAKE IDX_KEYPAIR)) Int.zero then Int.zero else Int.one)) :: Lc) (SEPx Sp))) end.
  { unfold entry_val. forward. forward. entailer!. }
  { exfalso. subst a. contradiction. }
  pose proof (hrx5_B4_C_N_t0_some NS T M a E Hf) as Ht0.
  destruct (Int.eq (Int.and (e_type E) (Int.or IDX_HANDSHAKE IDX_KEYPAIR)) Int.zero) eqn:Hty.
  { forward_if.
    { hrx5_B4_C_N_absurd. }
    forward.
    match goal with Hw: itable_wf T |- _ => sep_apply (hrx5_B4_C_N_close Tsh (l_itd L) T a she E Hsf HaL Hw) end.
    rewrite Ht0. hrx5_B4_C_N_ent. }
  forward_if; [| hrx5_B4_C_N_absurd].
  set (NS' := hnodes_snapped4 T NS PS) in *.
  assert_PROP (Forall isptr (map hn_addr NS')) as Hptrs.
  { sep_apply (hrx5_B4_C_N_hn_isptr (hrx5_head NS') NS'). entailer!. }
  pose proof (hrx5_B4_C_N_head_pn0 NS' Hptrs) as Hpn0.
  assert (HPSr: Forall (fun x => readable_share (snd (fst x))) PS).
  { rewrite Forall_forall in Hpok |- *. intros [[x sh] P] Hin. destruct (Hpok _ Hin) as (-> & _). cbn. auto. }
  assert (VP2 := hrx5_B4_C_N_peers_valid PS (e_peer E) HPSr HpE).
  assert (HNp: map hn_p NS' = map peer_addr4 PS) by (apply hrx5_B4_C_N_p_snapped; exact Hnp).
  assert_PROP (Forall (fun x => isptr (peer_addr4 x)) PS) as HPSp.
  { sep_apply (hrx5_B4_C_N_peers_ptr PS). entailer!. }
  assert (HpEp: isptr (e_peer E)).
  { apply in_map_iff in HpE. destruct HpE as (x & Hx & Hin). rewrite <- Hx. rewrite Forall_forall in HPSp. auto. }
  unfold entry_val.
  forward.
  match goal with |- semax _ (PROPx _ (LOCALx (temp HM._nd _ :: ?a1 :: ?a2 :: ?a3 :: ?a4 :: ?a5 :: ?a6 :: ?a7 :: ?a8 :: ?a9 :: ?a10 :: ?a11 :: ?a12 :: ?a13 :: ?a14 :: ?a15 :: ?a16 :: ?a17 :: ?a18 :: ?a19 :: temp HM._target _ :: ?Q) (SEPx ?Sp))) _ _ =>
  forward_loop (EX NS1: list hnode4, EX NS2: list hnode4,
     PROPx [NS' = NS1 ++ NS2]
     (LOCALx (temp HM._nd (hrx5_head NS2) :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 :: a13 :: a14 :: a15 :: a16 :: a17 :: a18 :: a19 :: temp HM._target (hrx5_nfind NS1 (e_peer E)) :: Q)
     (SEPx Sp)))
  continue: (EX NS1: list hnode4, EX N: hnode4, EX NS2: list hnode4,
     PROPx [NS' = NS1 ++ N :: NS2]
     (LOCALx (temp HM._nd (hn_addr N) :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 :: a13 :: a14 :: a15 :: a16 :: a17 :: a18 :: a19 :: temp HM._target (hrx5_nfind (NS1 ++ [N]) (e_peer E)) :: Q)
     (SEPx Sp)))
  break: (PROPx []
     (LOCALx (temp HM._nd nullval :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 :: a13 :: a14 :: a15 :: a16 :: a17 :: a18 :: a19 :: temp HM._target (hrx5_nfind NS' (e_peer E)) :: Q)
     (SEPx Sp)))
  end.
  { Exists (@nil hnode4) NS'. entailer!. }
  { Intros NS1 NS2.
    match goal with Ha: NS' = NS1 ++ NS2 |- _ => rename Ha into HN end.
    destruct NS2 as [|N NS2].
    - forward_if.
      { hrx5_B4_C_N_absurd. }
      forward. rewrite app_nil_r in HN. rewrite <- HN. entailer!.
    - assert (HinN: In (hn_addr N) (map hn_addr NS')).
      { rewrite HN, map_app. apply in_or_app. right. left. reflexivity. }
      assert (HpN: isptr (hn_addr N)). { rewrite Forall_forall in Hptrs. auto. }
      assert (HF1: Forall isptr (map hn_addr NS1)).
      { rewrite HN, map_app, Forall_app in Hptrs. apply Hptrs. }
      assert (HpNp: In (hn_p N) (map peer_addr4 PS)).
      { rewrite <- HNp, HN, map_app. apply in_or_app. right. left. reflexivity. }
      assert (VP1 := hrx5_B4_C_N_peers_valid PS (hn_p N) HPSr HpNp).
      assert (HpP: isptr (hn_p N)).
      { apply in_map_iff in HpNp. destruct HpNp as (x & <- & Hx). rewrite Forall_forall in HPSp. auto. }
      assert (VP3 := hrx5_B4_C_N_tg_valid (hrx5_head NS') NS' NS1 (N :: NS2) (e_peer E) HN).
      assert (VP0 := hrx5_B4_C_N_hn_valid (hrx5_head NS') NS' (hn_addr N) HinN).
      forward_if.
      2: { exfalso. match goal with Hn: _ = nullval |- _ => change (hn_addr N = nullval) in Hn;
             rewrite Hn in HpN; exact HpN end. }
      assert (Hnode: hnodes_rep4 W (hrx5_head NS') NS' |--
        (@data_at W Ews t_hnode4 (hrx5_B4_C_N_nv N (hrx5_head NS2)) (hn_addr N) *
         (@data_at W Ews t_hnode4 (hrx5_B4_C_N_nv N (hrx5_head NS2)) (hn_addr N) -*
          hnodes_rep4 W (hrx5_head NS') NS'))%logic).
      { rewrite HN. apply hrx5_B4_C_N_node. }
      sep_apply Hnode. Intros.
      change (hrx5_head (N :: NS2)) with (hn_addr N).
      forward.
      sep_apply (hrx5_B4_C_N_wand1 (@data_at W Ews t_hnode4 (hrx5_B4_C_N_nv N (hrx5_head NS2)) (hn_addr N))
                   (hnodes_rep4 W (hrx5_head NS') NS')).
      cbv beta iota delta [hrx5_B4_C_N_nv].
      forward.
      destruct (EqDec_val (hn_p N) (e_peer E)) as [Heq|Hne];
        [destruct (EqDec_val (hrx5_nfind NS1 (e_peer E)) nullval) as [Htn|Htn] |].
      + assert (Htg: hrx5_nfind (NS1 ++ [N]) (e_peer E) = hn_addr N) by (apply hrx5_B4_C_N_snoc_eq; auto).
        match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
          forward_if (PROPx P (LOCALx (temp HM._t'88 (Vint Int.one) :: Lc) (SEPx Sp))) end.
        { forward. rewrite Htn. entailer!. }
        { contradiction. }
        forward_if; [| hrx5_B4_C_N_absurd].
        forward.
        Exists NS1 N NS2. rewrite Htg. entailer!.
      + assert (Htg: hrx5_nfind (NS1 ++ [N]) (e_peer E) = hrx5_nfind NS1 (e_peer E))
          by (apply hrx5_B4_C_N_nfind_found; auto).
        pose proof (hrx5_B4_C_N_nfind_ptr NS1 (e_peer E) HF1 Htn) as Hp0.
        match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
          forward_if (PROPx P (LOCALx (temp HM._t'88 (Vint Int.zero) :: Lc) (SEPx Sp))) end.
        { forward. entailer!.
          destruct (hrx5_nfind NS1 (e_peer E)); try contradiction. reflexivity. }
        { contradiction. }
        forward_if; [hrx5_B4_C_N_absurd |].
        forward.
        Exists NS1 N NS2. rewrite Htg. entailer!.
      + assert (Htg: hrx5_nfind (NS1 ++ [N]) (e_peer E) = hrx5_nfind NS1 (e_peer E))
          by (apply hrx5_B4_C_N_snoc_ne; auto).
        match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
          forward_if (PROPx P (LOCALx (temp HM._t'88 (Vint Int.zero) :: Lc) (SEPx Sp))) end.
        { contradiction. }
        { forward. entailer!. }
        forward_if; [hrx5_B4_C_N_absurd |].
        forward.
        Exists NS1 N NS2. rewrite Htg. entailer!. }
  { Intros NS1 N NS2.
    match goal with Ha: NS' = NS1 ++ N :: NS2 |- _ => rename Ha into HN end.
    assert (Hnode: hnodes_rep4 W (hrx5_head NS') NS' |--
      (@data_at W Ews t_hnode4 (hrx5_B4_C_N_nv N (hrx5_head NS2)) (hn_addr N) *
       (@data_at W Ews t_hnode4 (hrx5_B4_C_N_nv N (hrx5_head NS2)) (hn_addr N) -*
        hnodes_rep4 W (hrx5_head NS') NS'))%logic).
    { rewrite HN. apply hrx5_B4_C_N_node. }
    assert (Hpn2: is_pointer_or_null (hrx5_head NS2)). { rewrite HN in Hptrs. eapply hrx5_B4_C_N_head_pn; eauto. }
    sep_apply Hnode. Intros.
    forward.
    sep_apply (hrx5_B4_C_N_wand1 (@data_at W Ews t_hnode4 (hrx5_B4_C_N_nv N (hrx5_head NS2)) (hn_addr N))
                 (hnodes_rep4 W (hrx5_head NS') NS')).
    cbv beta iota delta [hrx5_B4_C_N_nv].
    Exists (NS1 ++ [N]) NS2.
    entailer!.
    rewrite <- app_assoc. exact HN. }
  unfold POSTCONDITION, abbreviate.
  change (e_peer E, (succ_in (t_L T) a, (Val.of_bool true, (Vint (e_type E), Vint (e_index E)))))
    with (entry_val E (succ_in (t_L T) a) true).
  match goal with Hw: itable_wf T |- _ => sep_apply (hrx5_B4_C_N_close Tsh (l_itd L) T a she E Hsf HaL Hw) end.
  rewrite Ht0. subst NS'. rewrite (hrx5_B4_C_N_nfind_snapped T NS PS (e_peer E) Hnp).
  hrx5_B4_C_N_ent.
Qed.
