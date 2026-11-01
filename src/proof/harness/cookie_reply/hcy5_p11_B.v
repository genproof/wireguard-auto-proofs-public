(* law cookie_reply: phase P11, segment B (statement 68): the cnode search for the entry's peer.
   cookie_reply/hcy4_p11_B.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require WgNoise.harness.x_cookie_reply.code.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p11_defs.
Require Import WgNoise.proof.protocol.prot_body3_shim_table1.
Require Import WgNoise.proof.protocol.prot3_shim_table2_ilookup.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* pure facts: the model of the search                                     *)
(* ---------------------------------------------------------------------- *)

Lemma hcy5_p11_B_cfind_found NS A B p :
  hcy5_cfind NS A p <> nullval -> hcy5_cfind NS (A ++ B) p = hcy5_cfind NS A p.
Proof.
  induction A as [| [[c nd] o] A IH]; simpl; intros H; [contradiction |].
  destruct (EqDec_val (hcy5_nodepeer NS nd) p); auto.
Qed.

Lemma hcy5_p11_B_cfind_null NS A B p :
  Forall (fun x => isptr (fst (fst x))) A -> hcy5_cfind NS A p = nullval ->
  hcy5_cfind NS (A ++ B) p = hcy5_cfind NS B p.
Proof.
  induction A as [| [[c nd] o] A IH]; simpl; intros HF H; auto.
  inversion HF as [| ? ? Hc HF']; subst. simpl in Hc.
  destruct (EqDec_val (hcy5_nodepeer NS nd) p).
  - subst c. contradiction.
  - auto.
Qed.

Lemma hcy5_p11_B_cfind_snoc_ne NS A c nd o p :
  hcy5_nodepeer NS nd <> p -> hcy5_cfind NS (A ++ [(c, nd, o)]) p = hcy5_cfind NS A p.
Proof.
  intros Hne. induction A as [| [[c1 nd1] o1] A IH]; simpl.
  - destruct (EqDec_val (hcy5_nodepeer NS nd) p); [contradiction | reflexivity].
  - rewrite IH. reflexivity.
Qed.

Lemma hcy5_p11_B_cfind_snoc_eq NS A c nd o p :
  Forall (fun x => isptr (fst (fst x))) A -> hcy5_cfind NS A p = nullval -> hcy5_nodepeer NS nd = p ->
  hcy5_cfind NS (A ++ [(c, nd, o)]) p = c.
Proof.
  intros HF Hn Heq. rewrite hcy5_p11_B_cfind_null by auto. simpl.
  destruct (EqDec_val (hcy5_nodepeer NS nd) p); [reflexivity | contradiction].
Qed.

Lemma hcy5_p11_B_cfind_ptr NS A p :
  Forall (fun x => isptr (fst (fst x))) A -> hcy5_cfind NS A p = nullval \/ isptr (hcy5_cfind NS A p).
Proof.
  induction A as [| [[c nd] o] A IH]; simpl; intros HF; [auto |].
  inversion HF as [| ? ? Hc HF']; subst. simpl in Hc.
  destruct (EqDec_val (hcy5_nodepeer NS nd) p); auto.
Qed.

Lemma hcy5_p11_B_Forall_firstn {A: Type} (P: A -> Prop) (l: list A) n : Forall P l -> Forall P (firstn n l).
Proof.
  revert l; induction n as [| n IH]; intros l HF; simpl; [constructor |].
  destruct l as [| x l]; [constructor |]. inversion HF; subst. constructor; auto.
Qed.

Lemma hcy5_p11_B_skipn_S {A: Type} (l: list A) k x r : skipn k l = x :: r -> skipn (S k) l = r.
Proof.
  revert l; induction k as [| k IH]; intros l Hs.
  - destruct l; simpl in *; [discriminate | inv Hs; reflexivity].
  - destruct l as [| y l]; simpl in *; [discriminate |]. apply IH. exact Hs.
Qed.

Lemma hcy5_p11_B_firstn_snoc {A: Type} (l: list A) k x r :
  skipn k l = x :: r -> firstn (S k) l = firstn k l ++ [x].
Proof.
  revert l; induction k as [| k IH]; intros l Hs.
  - destruct l; simpl in *; [discriminate | inv Hs; reflexivity].
  - destruct l as [| y l]; simpl in *; [discriminate |]. f_equal. apply IH. exact Hs.
Qed.

Lemma hcy5_p11_B_skipn_lt {A: Type} (l: list A) k x r : skipn k l = x :: r -> (k < length l)%nat.
Proof.
  revert l; induction k as [| k IH]; intros l Hs.
  - destruct l; simpl in *; [discriminate | lia].
  - destruct l as [| y l]; simpl in *; [discriminate |]. specialize (IH l Hs). lia.
Qed.

Lemma hcy5_p11_B_skipn_nil {A: Type} (l: list A) k : skipn k l = [] -> (length l <= k)%nat.
Proof. intros Hs. pose proof (length_skipn k l) as Hl. rewrite Hs in Hl. simpl in Hl. lia. Qed.

Lemma hcy5_p11_B_skipn_in {A: Type} (l: list A) k x r : skipn k l = x :: r -> In x l.
Proof.
  intros Hs. rewrite <- (firstn_skipn k l), Hs. apply in_or_app. right. left. reflexivity.
Qed.

Lemma hcy5_p11_B_in_combine {A B: Type} (l1: list A) (l2: list B) x :
  In x l1 -> length l1 = length l2 -> exists y, In (x, y) (combine l1 l2).
Proof.
  revert l2; induction l1 as [| a l1 IH]; intros l2 Hin Hl; [contradiction |].
  destruct l2 as [| b l2]; [discriminate |]. simpl in Hl.
  destruct Hin as [-> | Hin].
  - exists b. left. reflexivity.
  - destruct (IH l2 Hin ltac:(lia)) as (y & Hy). exists y. right. exact Hy.
Qed.

(* the k-th cnode's node: a node of the snapped list, its peer the model's node peer, a peer of PS *)
Lemma hcy5_p11_B_pick T NS PS CL k c0 nd o B :
  hnodes_peers4 NS PS -> hcy5_cl_nodes CL NS -> skipn k CL = (c0, nd, o) :: B ->
  exists N, In N (hnodes_snapped4 T NS PS) /\ hn_addr N = nd /\ hn_p N = hcy5_nodepeer NS nd /\
            In (hn_p N) (map peer_addr4 PS).
Proof.
  intros Hnp [Hcl _] Hsk.
  assert (Hin: In nd (map hn_addr NS)).
  { apply in_rev. rewrite <- Hcl. apply in_map_iff. exists (c0, nd, o). split; [reflexivity |].
    eapply hcy5_p11_B_skipn_in; eauto. }
  unfold hcy5_nodepeer.
  destruct (find (fun N => if eq_dec (hn_addr N) nd then true else false) NS) as [N1|] eqn:Hf.
  - apply find_some in Hf. destruct Hf as [HN1 Hq].
    destruct (eq_dec (hn_addr N1) nd) as [Ha|]; [| discriminate].
    assert (Hl: length NS = length PS).
    { pose proof (f_equal (@length _) Hnp) as Hl. rewrite !length_map in Hl. exact Hl. }
    destruct (hcy5_p11_B_in_combine NS PS N1 HN1 Hl) as (x & Hc).
    exists (hn_snapshot4 T N1 x).
    assert (Hs: hn_addr (hn_snapshot4 T N1 x) = hn_addr N1 /\ hn_p (hn_snapshot4 T N1 x) = hn_p N1).
    { unfold hn_snapshot4. destruct x as [[q sh] P]. split; reflexivity. }
    destruct Hs as [Hs1 Hs2].
    split; [| split; [congruence | split; [exact Hs2 |]]].
    + unfold hnodes_snapped4. apply (in_map (fun '(N, x) => hn_snapshot4 T N x) _ _ Hc).
    + rewrite Hs2, <- Hnp. apply in_map. exact HN1.
  - exfalso. apply in_map_iff in Hin. destruct Hin as (N0 & HN0 & Hin0).
    pose proof (find_none _ _ Hf N0 Hin0) as H0. simpl in H0.
    destruct (EqDec_val (hn_addr N0) nd); [discriminate | contradiction].
Qed.

(* the target of the model *)
Lemma hcy5_p11_B_t0_none NS CL T idx :
  t_find_index T (t_L T) idx = None -> hcy5_p11_t0 NS CL T idx = nullval.
Proof. intros H. unfold hcy5_p11_t0, t_lookup. rewrite H. reflexivity. Qed.

Lemma hcy5_p11_B_t0_some NS CL T idx a E :
  t_find_index T (t_L T) idx = Some (a, E) ->
  hcy5_p11_t0 NS CL T idx =
  if Int.eq (Int.and (e_type E) (Int.or IDX_HANDSHAKE IDX_KEYPAIR)) Int.zero then nullval
  else hcy5_cfind NS CL (e_peer E).
Proof.
  intros H. unfold hcy5_p11_t0, t_lookup. rewrite H.
  destruct (Int.eq _ _); reflexivity.
Qed.

(* the pool's entries: their peers are peers of PS *)
Lemma hcy5_p11_B_pool_peer PS KE T a sh E :
  hcy5_T_ok PS KE T -> In (a, sh, E) (t_D T) -> In (e_peer E) (map peer_addr4 PS).
Proof.
  intros ((own & ix & HD & Hown) & _) Hin. rewrite HD in Hin. unfold hcy5_pool in Hin.
  apply in_app_or in Hin. destruct Hin as [Hin | Hin]; apply in_map_iff in Hin; destruct Hin as (x & Hx & Hin).
  - unfold hcy5_kentry in Hx. inv Hx. cbn [e_peer].
    rewrite Forall_forall in Hown. apply Hown. exact Hin.
  - unfold hcy5_hent in Hx. inv Hx. cbn [e_peer]. exact Hin.
Qed.

(* the peers after the consumption: same addresses and shares *)
Lemma hcy5_p11_B_supd_fst (PS: list (val * share * peer)) a P :
  map fst (supd PS a P) = map fst PS.
Proof.
  induction PS as [| [[x sh] Q] PS IH]; simpl; auto.
  destruct (EqDec_val x a); simpl; f_equal; auto.
Qed.

Lemma hcy5_p11_B_after_fst PS res : map fst (peers_after PS res) = map fst PS.
Proof. destruct res as [[a P]|]; simpl; [apply hcy5_p11_B_supd_fst | reflexivity]. Qed.

Lemma hcy5_p11_B_after_addr PS res : map peer_addr4 (peers_after PS res) = map peer_addr4 PS.
Proof.
  assert (E: forall l: list (val * share * peer), map peer_addr4 l = map fst (map fst l)).
  { intros l. rewrite map_map. apply map_ext. intros [[x sh] P]. reflexivity. }
  rewrite !E, hcy5_p11_B_after_fst. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* separation logic                                                        *)
(* ---------------------------------------------------------------------- *)

Lemma hcy5_p11_B_peer_valid sh p P : readable_share sh -> peer_rep sh p P |-- valid_pointer p.
Proof.
  intros Hsh. unfold peer_rep. Intros.
  repeat apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; [apply readable_nonidentity; auto | simpl; lia | reflexivity].
Qed.

Lemma hcy5_p11_B_peers_valid PS q :
  Forall (fun x => readable_share (snd (fst x))) PS -> In q (map peer_addr4 PS) -> peers_rep PS |-- valid_pointer q.
Proof.
  unfold peers_rep. induction PS as [|[[a sh] P] PS IH]; simpl; intros Hwf Hq; [contradiction|].
  inversion Hwf; subst. destruct Hq as [<-|Hq].
  - apply sepcon_valid_pointer1. apply hcy5_p11_B_peer_valid; auto.
  - apply sepcon_valid_pointer2. apply IH; auto.
Qed.

Lemma hcy5_p11_B_peers_ptr PS : peers_rep PS |-- !! Forall (fun x => isptr (peer_addr4 x)) PS.
Proof.
  unfold peers_rep. induction PS as [| [[a sh] P] PS IH]; simpl.
  - entailer!.
  - sep_apply IH. unfold peer_rep. entailer!. constructor; auto. destruct H0 as [Hp _]. exact Hp.
Qed.

(* the cnodes *)
Fixpoint hcy5_p11_B_seg (l e: val) (CL: list (val * val * option cookie)) : mpred :=
  match CL with
  | [] => !! (l = e) && emp
  | (c, nd, o) :: CL' =>
      !! (l = c) &&
      EX nx: val,
        (@malloc_token W_cookie_reply Ews t_cnode5 c *
         @field_at W_cookie_reply Ews t_cnode5 [StructField HY._n] nd c *
         hcy5_cs_rep o (offset_val 8 c) *
         @field_at W_cookie_reply Ews t_cnode5 [StructField HY._next] nx c *
         hcy5_p11_B_seg nx e CL')
  end.

Lemma hcy5_p11_B_cns_cons l c nd o B :
  hcy5_cns l ((c, nd, o) :: B) =
  (!! (l = c) &&
   (@malloc_token W_cookie_reply Ews t_cnode5 c *
    @field_at W_cookie_reply Ews t_cnode5 [StructField HY._n] nd c *
    hcy5_cs_rep o (offset_val 8 c) *
    @field_at W_cookie_reply Ews t_cnode5 [StructField HY._next] (hcy5_chead B) c *
    hcy5_cns (hcy5_chead B) B))%logic.
Proof. reflexivity. Qed.

Lemma hcy5_p11_B_cns_nil l : hcy5_cns l [] = (!! (l = nullval) && emp)%logic.
Proof. reflexivity. Qed.

Lemma hcy5_p11_B_cns_head l B : hcy5_cns l B |-- !! (l = hcy5_chead B).
Proof. destruct B as [| [[c nd] o] B]; simpl; entailer!. Qed.

Lemma hcy5_p11_B_cns_pn l B : hcy5_cns l B |-- !! is_pointer_or_null l.
Proof.
  destruct B as [| [[c nd] o] B]; simpl.
  - entailer!.
  - Intros. subst. entailer!.
Qed.

Lemma hcy5_p11_B_cns_ptrs l B : hcy5_cns l B |-- !! Forall (fun x => isptr (fst (fst x))) B.
Proof.
  revert l; induction B as [| [[c nd] o] B IH]; intros l; simpl.
  - entailer!.
  - Intros. subst. sep_apply (IH (hcy5_chead B)). entailer!.
Qed.

Lemma hcy5_p11_B_cns_tc F l B : F * hcy5_cns l B |-- denote_tc_test_eq l (Vlong Int64.zero).
Proof.
  destruct B as [| [[c nd] o] B]; simpl.
  - Intros. subst. entailer!.
  - Intros. subst. apply denote_tc_test_eq_split; [| apply valid_pointer_zero64; auto].
    apply sepcon_valid_pointer2.
    apply sepcon_valid_pointer1, sepcon_valid_pointer1, sepcon_valid_pointer1, sepcon_valid_pointer2.
    apply field_at_valid_ptr0; auto. vm_compute. reflexivity.
Qed.

Lemma hcy5_p11_B_seg_snoc l e A c nd o nx :
  e = c ->
  hcy5_p11_B_seg l e A *
  (@malloc_token W_cookie_reply Ews t_cnode5 c *
   @field_at W_cookie_reply Ews t_cnode5 [StructField HY._n] nd c *
   hcy5_cs_rep o (offset_val 8 c) *
   @field_at W_cookie_reply Ews t_cnode5 [StructField HY._next] nx c) |--
  hcy5_p11_B_seg l nx (A ++ [(c, nd, o)]).
Proof.
  intros He. revert l; induction A as [| [[c1 nd1] o1] A IH]; intros l; simpl.
  - Intros. subst. Exists nx. entailer!.
  - Intros nx1. Exists nx1. entailer!. sep_apply (IH nx1). cancel.
Qed.

Lemma hcy5_p11_B_seg_end l A : hcy5_p11_B_seg l nullval A |-- hcy5_cns l A.
Proof.
  revert l; induction A as [| [[c nd] o] A IH]; intros l; simpl.
  - entailer!.
  - Intros nx. sep_apply (IH nx). sep_apply (hcy5_p11_B_cns_head nx A). Intros. subst. entailer!.
Qed.

(* the target found so far is NULL or a cnode of the segment *)
Lemma hcy5_p11_B_seg_valid NS p l e A : hcy5_p11_B_seg l e A |-- valid_pointer (hcy5_cfind NS A p).
Proof.
  revert l; induction A as [| [[c nd] o] A IH]; intros l; cbn [hcy5_p11_B_seg hcy5_cfind].
  - apply andp_left2. apply valid_pointer_null.
  - Intros nx. destruct (eq_dec (hcy5_nodepeer NS nd) p).
    + subst l.
      apply sepcon_valid_pointer1, sepcon_valid_pointer1, sepcon_valid_pointer1, sepcon_valid_pointer2.
      apply field_at_valid_ptr0; auto. vm_compute. reflexivity.
    + apply sepcon_valid_pointer2. apply IH.
Qed.

(* ---- the field p of a node: focus with a wand ---- *)
#[local] Instance hcy5_p11_B_cce_K : change_composite_env CKS W_cookie_reply.
Proof. make_cs_preserve CKS W_cookie_reply. Defined.

Lemma hcy5_p11_B_wand_frame (A B C F: mpred) : A * B |-- C -> A * (F * (F -* B)) |-- F * (F -* C).
Proof.
  intros H. rewrite <- sepcon_assoc, (sepcon_comm A F), sepcon_assoc.
  apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint. eapply derives_trans; [| exact H].
  rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl |].
  rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hcy5_p11_B_node1 (N: hnode4) nx :
  @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N) |--
  @field_at W_cookie_reply Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) *
  (@field_at W_cookie_reply Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) -*
   @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N)).
Proof.
  rewrite (@data_at_change_composite CKS W_cookie_reply _ Ews t_hnode4 _ _ (JMeq_refl _)) by prove_cs_preserve_type.
  unfold_data_at (@data_at W_cookie_reply Ews t_hnode4 _ (hn_addr N)).
  apply sepcon_derives; [apply derives_refl | apply wand_frame_intro].
Qed.

Lemma hcy5_p11_B_node h NS N v :
  In N NS -> hn_p N = v ->
  hnodes_rep4 W_cookie_reply h NS |--
  @field_at W_cookie_reply Ews t_hnode4 (DOT HY._p) v (hn_addr N) *
  (@field_at W_cookie_reply Ews t_hnode4 (DOT HY._p) v (hn_addr N) -* hnodes_rep4 W_cookie_reply h NS).
Proof.
  intros Hin <-. revert h. induction NS as [| N0 NS IH]; intros h; [contradiction |].
  destruct Hin as [-> | Hin].
  - simpl hnodes_rep4. Intros nx. subst h.
    apply derives_trans with
      (@malloc_token W_cookie_reply Ews t_hnode4 (hn_addr N) * @malloc_token W_cookie_reply Ews t_peer (hn_p N) *
       hnodes_rep4 W_cookie_reply nx NS *
       (@field_at W_cookie_reply Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) *
        (@field_at W_cookie_reply Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) -*
         @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N))))%logic.
    + sep_apply (hcy5_p11_B_node1 N nx). cancel.
    + apply hcy5_p11_B_wand_frame. Exists nx. entailer!.
  - simpl hnodes_rep4. Intros nx. subst h.
    apply derives_trans with
      (@malloc_token W_cookie_reply Ews t_hnode4 (hn_addr N0) *
       @data_at CKS Ews t_hnode4 (hn_p N0, (hn_snap N0, (hn_refs N0, (hn_rest N0, nx)))) (hn_addr N0) *
       @malloc_token W_cookie_reply Ews t_peer (hn_p N0) *
       (@field_at W_cookie_reply Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) *
        (@field_at W_cookie_reply Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) -* hnodes_rep4 W_cookie_reply nx NS)))%logic.
    + sep_apply (IH Hin nx). cancel.
    + apply hcy5_p11_B_wand_frame. Exists nx. entailer!.
Qed.

(* ---- A's table: the entry at a focused at the world ---- *)
#[local] Instance hcy5_p11_B_cceN : change_composite_env Noise.CS W_cookie_reply.
Proof. make_cs_preserve Noise.CS W_cookie_reply. Defined.

Lemma hcy5_p11_B_entry_W sh a E nx h :
  entry_at sh a E nx h = @data_at W_cookie_reply sh t_entry_s (entry_val E nx h) a.
Proof.
  unfold entry_at.
  rewrite (@data_at_change_composite Noise.CS W_cookie_reply hcy5_p11_B_cceN sh t_entry_s
    (entry_val E nx h) (entry_val E nx h) (JMeq_refl _) eq_refl). reflexivity.
Qed.

Definition hcy5_p11_B_trest (sht: share) (tab: val) (T: tstate) (a: val) : mpred :=
  (@data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab * iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) a))%logic.

Lemma hcy5_p11_B_open sht tab T a sh E : sfind (t_D T) a = Some (sh, E) -> In a (t_L T) ->
  itable sht tab T |--
  !! (itable_wf T /\ writable_share sh) &&
  (hcy5_p11_B_trest sht tab T a *
   @data_at W_cookie_reply sh t_entry_s (entry_val E (succ_in (t_L T) a) true) a).
Proof.
  intros Hs HL. unfold itable, hcy5_p11_B_trest. Intros.
  assert (WS: writable_share sh).
  { destruct H as (_ & _ & _ & H4). apply prot_rep3_sfind_In in Hs. rewrite Forall_forall in H4.
    apply (H4 _ Hs). }
  rewrite (prot_rep3_split _ _ _ _ _ Hs).
  change (pool_item_rep (t_L T) (a, sh, E)) with (entry_at sh a E (succ_in (t_L T) a) (vin a (t_L T))).
  assert (Hv: vin a (t_L T) = true) by (unfold vin; destruct (in_dec eq_dec a (t_L T)); [reflexivity|contradiction]).
  rewrite Hv, hcy5_p11_B_entry_W. entailer!.
Qed.

Lemma hcy5_p11_B_close sht tab T a sh E : sfind (t_D T) a = Some (sh, E) -> In a (t_L T) -> itable_wf T ->
  hcy5_p11_B_trest sht tab T a *
  @data_at W_cookie_reply sh t_entry_s (entry_val E (succ_in (t_L T) a) true) a
  |-- itable sht tab T.
Proof.
  intros Hs HL WF. unfold itable, hcy5_p11_B_trest.
  rewrite (prot_rep3_split _ _ _ _ _ Hs).
  change (pool_item_rep (t_L T) (a, sh, E)) with (entry_at sh a E (succ_in (t_L T) a) (vin a (t_L T))).
  assert (Hv: vin a (t_L T) = true) by (unfold vin; destruct (in_dec eq_dec a (t_L T)); [reflexivity|contradiction]).
  rewrite Hv, hcy5_p11_B_entry_W. entailer!.
Qed.

Section Phase.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_p11_B_ok {Espec: OracleKind} gv L FR :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcy5_p11_TA x25519 xaead_enc xaead_dec gv L FR) hcy5_p11_sB
    (overridePost (hcy5_p11_TB x25519 xaead_enc xaead_dec gv L FR) (hcy5_R gv)).
Proof.
  intros HH. unfold hcy5_p11_TA, hcy5_Delta, hcy5_R, hcy5_p11_sB. simplify_func_tycontext. abbreviate_semax.
  Intros R Sh m c rp Q nonce rr CK CM.
  Intros NS PS T np CL KE CM' honest now2.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_lvars; cbn [app].
  pose proof H0 as (Hpok & Hnp & Hnd1 & Hnd2 & Hpkc).
  unfold hcy5_p11_ewalk.
  destruct (t_find_index T (t_L T) (cm_receiver CM')) as [[a E]|] eqn:Hf.
  - (* the walk found the entry at a *)
    destruct (prot3_ilookup_find_some _ _ _ _ _ Hf) as [HaL HtE].
    unfold t_entry in HtE. destruct (sfind (t_D T) a) as [[she E']|] eqn:Hsf; [| discriminate].
    injection HtE as HE. subst E'.
    assert (HpE: In (e_peer E) (map peer_addr4 PS)).
    { eapply hcy5_p11_B_pool_peer; [eassumption |]. eapply prot_rep3_sfind_In; eauto. }
    sep_apply (hcy5_p11_B_open Tsh (l_ita L) T a she E Hsf HaL). Intros.
    assert_PROP (isptr a) as Hpa by entailer!.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HY._t'48 (Vint (if Int.eq (Int.and (e_type E) (Int.or IDX_HANDSHAKE IDX_KEYPAIR)) Int.zero then Int.zero else Int.one)) :: Lc) (SEPx Sp))) end.
    { unfold entry_val. forward. forward. entailer!. }
    { subst a. contradiction. }
    pose proof (hcy5_p11_B_t0_some NS CL T (cm_receiver CM') a E Hf) as Ht0.
    destruct (Int.eq (Int.and (e_type E) (Int.or IDX_HANDSHAKE IDX_KEYPAIR)) Int.zero) eqn:Hty.
    + (* type not in the mask *)
      forward_if.
      { contradiction. }
      forward.
      sep_apply (hcy5_p11_B_close Tsh (l_ita L) T a she E Hsf HaL H8).
      unfold hcy5_p11_TB. Exists R Sh m c rp Q nonce rr CK CM. Exists NS PS T np CL KE CM' honest now2.
      rewrite Ht0.
      unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_lvars; cbn [app].
      entailer!.
    + (* the cnode search *)
      forward_if; [| discriminate].
      assert_PROP (Forall (fun x => isptr (fst (fst x))) CL) as HCLp.
      { sep_apply (hcy5_p11_B_cns_ptrs (hcy5_chead CL) CL). entailer!. }
      set (PS2 := peers_after PS (hcy5_res xaead_dec T PS CM' now2)).
      assert (HPS2: map peer_addr4 PS2 = map peer_addr4 PS) by apply hcy5_p11_B_after_addr.
      assert_PROP (Forall (fun x => isptr (peer_addr4 x)) PS2) as HPS2p.
      { sep_apply (hcy5_p11_B_peers_ptr PS2). entailer!. }
      assert (HPS2r: Forall (fun x => readable_share (snd (fst x))) PS2).
      { assert (Hf2: map fst PS2 = map fst PS) by apply hcy5_p11_B_after_fst.
        apply Forall_forall. intros [[q sh] P] Hin.
        assert (Hin2: In (q, sh) (map fst PS)) by (rewrite <- Hf2; apply in_map with (f := fst) in Hin; exact Hin).
        apply in_map_iff in Hin2. destruct Hin2 as ([[q' sh'] P'] & Hq & Hin').
        cbn in Hq. inv Hq. rewrite Forall_forall in Hpok. destruct (Hpok _ Hin') as (-> & _). cbn. auto. }
      assert (Hptr: forall q, In q (map peer_addr4 PS) -> isptr q).
      { intros q Hq. rewrite <- HPS2 in Hq. apply in_map_iff in Hq. destruct Hq as (x & <- & Hx).
        rewrite Forall_forall in HPS2p. apply HPS2p. exact Hx. }
      set (NS' := hnodes_snapped4 T NS PS).
      unfold entry_val.
      forward.
      freeze [0;2;3;4;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;24;25;26;27;28;29;30;31;32;33;34;35;36;37;38;39;40] Fr.
      match goal with |- semax _ (PROPx _ (LOCALx (_ :: _ :: _ :: ?Lr) (SEPx (?F :: ?En :: _)))) _ _ =>
      forward_loop (EX k: nat,
        PROPx [(k <= length CL)%nat]
        (LOCALx (temp HY._cn (hcy5_chead (skipn k CL)) :: temp HY._target (hcy5_cfind NS (firstn k CL) (e_peer E)) :: Lr)
        (SEPx [F; En; hnodes_rep4 W (hcy5_head NS') NS'; peers_rep PS2;
               hcy5_p11_B_seg (hcy5_chead CL) (hcy5_chead (skipn k CL)) (firstn k CL);
               hcy5_cns (hcy5_chead (skipn k CL)) (skipn k CL)])))
      continue: (EX k: nat, EX c0: val, EX nd: val, EX o: option cookie,
        PROPx [skipn k CL = (c0, nd, o) :: skipn (S k) CL]
        (LOCALx (temp HY._cn c0 :: temp HY._target (hcy5_cfind NS (firstn (S k) CL) (e_peer E)) :: Lr)
        (SEPx [F; En; hnodes_rep4 W (hcy5_head NS') NS'; peers_rep PS2;
               hcy5_p11_B_seg (hcy5_chead CL) c0 (firstn k CL);
               @malloc_token W Ews t_cnode5 c0;
               @field_at W Ews t_cnode5 [StructField HY._n] nd c0;
               hcy5_cs_rep o (offset_val 8 c0);
               @field_at W Ews t_cnode5 [StructField HY._next] (hcy5_chead (skipn (S k) CL)) c0;
               hcy5_cns (hcy5_chead (skipn (S k) CL)) (skipn (S k) CL)])))
      break: (PROPx []
        (LOCALx (temp HY._cn nullval :: temp HY._target (hcy5_cfind NS CL (e_peer E)) :: Lr)
        (SEPx [F; En; hnodes_rep4 W (hcy5_head NS') NS'; peers_rep PS2; hcy5_cns (hcy5_chead CL) CL])))
      end.
      { Exists 0%nat. cbn [skipn firstn hcy5_p11_B_seg hcy5_cfind]. entailer!. }
      { Intros k.
        assert_PROP (is_pointer_or_null (hcy5_chead (skipn k CL))) as Hpn.
        { sep_apply (hcy5_p11_B_cns_pn (hcy5_chead (skipn k CL)) (skipn k CL)). entailer!. }
        forward_if.
        - apply hcy5_p11_B_cns_tc.
        - destruct (skipn k CL) as [| [[c0 nd] o] B] eqn:Hsk; [simpl in H12; contradiction |].
          destruct (hcy5_p11_B_pick T NS PS CL k c0 nd o B Hnp H3 Hsk) as (N & HNin & HNa & HNp & HNps).
          fold NS' in HNin. subst nd.
          assert (Hc: hcy5_chead ((c0, hn_addr N, o) :: B) = c0) by reflexivity.
          rewrite Hc. rewrite hcy5_p11_B_cns_cons. Intros.
          assert (HpN: isptr (hn_p N)) by (apply Hptr; exact HNps).
          assert (HpE': isptr (e_peer E)) by (apply Hptr; exact HpE).
          sep_apply (hcy5_p11_B_node (hcy5_head NS') NS' N (hn_p N) HNin eq_refl). Intros.
          assert_PROP (isptr (hn_addr N)) as HNptr by entailer!.
          forward. forward.
          sep_apply (modus_ponens_wand (@field_at W Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N))).
          forward.
          assert (VP1 := hcy5_p11_B_peers_valid PS2 (hn_p N) HPS2r ltac:(rewrite HPS2; exact HNps)).
          assert (VP2 := hcy5_p11_B_peers_valid PS2 (e_peer E) HPS2r ltac:(rewrite HPS2; exact HpE)).
          assert (VP3 := hcy5_p11_B_seg_valid NS (e_peer E) (hcy5_chead CL) c0 (firstn k CL)).
          pose proof (hcy5_p11_B_skipn_S _ _ _ _ Hsk) as HskS.
          pose proof (hcy5_p11_B_firstn_snoc _ _ _ _ Hsk) as HfS.
          pose proof (hcy5_p11_B_Forall_firstn _ _ k HCLp) as HFk.
          destruct (eq_dec (hn_p N) (e_peer E)) as [Heq|Hne];
            [destruct (eq_dec (hcy5_cfind NS (firstn k CL) (e_peer E)) nullval) as [Htn|Htn] |].
          + (* the peer matches, no target yet: target = cn *)
            assert (Htg: hcy5_cfind NS (firstn (S k) CL) (e_peer E) = c0).
            { rewrite HfS. apply hcy5_p11_B_cfind_snoc_eq; auto. rewrite <- HNp. exact Heq. }
            match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
              forward_if (PROPx P (LOCALx (temp HY._t'47 (Vint Int.one) :: Lc) (SEPx Sp))) end.
            { forward. rewrite Htn. entailer!. }
            { contradiction. }
            forward_if; [| discriminate].
            forward.
            Exists k c0 (hn_addr N) o. rewrite Htg, HskS. entailer!.
          + (* the peer matches, a target already *)
            assert (Htg: hcy5_cfind NS (firstn (S k) CL) (e_peer E) = hcy5_cfind NS (firstn k CL) (e_peer E)).
            { rewrite HfS. apply hcy5_p11_B_cfind_found; auto. }
            destruct (hcy5_p11_B_cfind_ptr NS (firstn k CL) (e_peer E) HFk) as [Hn0 | Hp0]; [contradiction |].
            match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
              forward_if (PROPx P (LOCALx (temp HY._t'47 (Vint Int.zero) :: Lc) (SEPx Sp))) end.
            { forward. entailer!.
              destruct (hcy5_cfind NS (firstn k CL) (e_peer E)); try contradiction. reflexivity. }
            { contradiction. }
            forward_if; [contradiction |].
            forward.
            Exists k c0 (hn_addr N) o. rewrite Htg, HskS. entailer!.
          + (* another peer *)
            assert (Htg: hcy5_cfind NS (firstn (S k) CL) (e_peer E) = hcy5_cfind NS (firstn k CL) (e_peer E)).
            { rewrite HfS. apply hcy5_p11_B_cfind_snoc_ne. rewrite <- HNp. exact Hne. }
            match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
              forward_if (PROPx P (LOCALx (temp HY._t'47 (Vint Int.zero) :: Lc) (SEPx Sp))) end.
            { contradiction. }
            { forward. entailer!. }
            forward_if; [contradiction |].
            forward.
            Exists k c0 (hn_addr N) o. rewrite Htg, HskS. entailer!.
        - (* cn NULL: break *)
          assert_PROP (skipn k CL = []) as Hsk.
          { destruct (skipn k CL) as [| [[c0 nd] o] B] eqn:Hq; [entailer! |].
            rewrite hcy5_p11_B_cns_cons. Intros. subst. entailer!. }
          pose proof (hcy5_p11_B_skipn_nil CL k Hsk) as Hk.
          assert (Hn: hcy5_chead (@nil (val * val * option cookie)) = nullval) by reflexivity.
          rewrite Hsk, Hn.
          forward.
          rewrite firstn_all2 by lia.
          sep_apply (hcy5_p11_B_seg_end (hcy5_chead CL) CL).
          rewrite hcy5_p11_B_cns_nil. entailer!. }
      { Intros k c0 nd o.
        match goal with Hs: skipn k CL = _ |- _ => rename Hs into Hsk end.
        assert_PROP (is_pointer_or_null (hcy5_chead (skipn (Datatypes.S k) CL))) as Hpn.
        { sep_apply (hcy5_p11_B_cns_pn (hcy5_chead (skipn (Datatypes.S k) CL)) (skipn (Datatypes.S k) CL)). entailer!. }
        forward.
        Exists (Datatypes.S k).
        pose proof (hcy5_p11_B_skipn_lt CL k _ _ Hsk) as Hlt.
        entailer!.
        rewrite (hcy5_p11_B_firstn_snoc CL k _ _ Hsk).
        sep_apply (hcy5_p11_B_seg_snoc (hcy5_chead CL) c0 (firstn k CL) c0 nd o
                     (hcy5_chead (skipn (Datatypes.S k) CL)) eq_refl).
        cancel. }
      unfold POSTCONDITION, abbreviate. simpl_ret_assert. thaw Fr.
      change (e_peer E, (succ_in (t_L T) a, (Val.of_bool true, (Vint (e_type E), Vint (e_index E)))))
        with (entry_val E (succ_in (t_L T) a) true).
      sep_apply (hcy5_p11_B_close Tsh (l_ita L) T a she E Hsf HaL H8).
      unfold hcy5_p11_TB. Exists R Sh m c rp Q nonce rr CK CM. Exists NS PS T np CL KE CM' honest now2.
      rewrite Ht0.
      unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_lvars; cbn [app].
      entailer!.
      apply derives_refl.
  - (* not found: e = NULL *)
    match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HY._t'48 (Vint Int.zero) :: Lc) (SEPx Sp))) end.
    { discriminate. }
    { forward. entailer!. }
    forward_if.
    { contradiction. }
    forward.
    unfold hcy5_p11_TB. Exists R Sh m c rp Q nonce rr CK CM. Exists NS PS T np CL KE CM' honest now2.
    rewrite (hcy5_p11_B_t0_none NS CL T (cm_receiver CM') Hf).
    unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_lvars; cbn [app].
    entailer!.
Qed.

End Phase.
