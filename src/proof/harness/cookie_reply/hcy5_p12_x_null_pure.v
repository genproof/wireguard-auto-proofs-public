(* law cookie_reply, phase P12, segment X, the branch target == NULL: the pure facts of
   CHECK(hnodes_same_except(peers, NULL)) (port of consume_initiation's hci5_p8_A2_pure.v, v1 hcy4_p12_H.v):
   a NULL target means no peer accepted the reply (every peer has a cnode), so the peers are PS; the arguments
   sns / rs / prs / VO of hnodes_same_except4_spec, its premises, the result 1; and the separation helpers. *)
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

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

Ltac hcy5_p12_x_null_dif := match goal with |- context [if ?d then _ else _] => destruct d end.

(* ---- the target: NULL only when nothing was accepted ---- *)

Lemma hcy5_p12_x_null_sfind_in {A: Type} (l: list (val * share * A)) a sh v :
  sfind l a = Some (sh, v) -> In (a, sh, v) l.
Proof.
  induction l as [|[[x s] w] l IH]; simpl; intros H; [discriminate|].
  revert H; hcy5_p12_x_null_dif; intros H.
  - inv H. left; reflexivity.
  - right; auto.
Qed.

Lemma hcy5_p12_x_null_sfind_some {A: Type} (l: list (val * share * A)) a :
  In a (saddrs l) -> exists sh v, sfind l a = Some (sh, v).
Proof.
  induction l as [|[[x s] w] l IH]; simpl; intros H; [contradiction|].
  hcy5_p12_x_null_dif; [eauto|].
  destruct H as [H|H]; [contradiction | auto].
Qed.

Lemma hcy5_p12_x_null_nodepeer NS N : NoDup (map hn_addr NS) -> In N NS -> hcy5_nodepeer NS (hn_addr N) = hn_p N.
Proof.
  unfold hcy5_nodepeer. induction NS as [|N0 NS IH]; simpl; intros Hn Hin; [contradiction|].
  inv Hn. destruct (EqDec_val (hn_addr N0) (hn_addr N)) as [Ee|Ee].
  - destruct Hin as [<-|Hin]; [reflexivity|].
    exfalso. match goal with H: ~ In _ _ |- _ => apply H end. rewrite Ee. apply in_map, Hin.
  - destruct Hin as [<-|Hin]; [congruence | auto].
Qed.

Lemma hcy5_p12_x_null_cfind NS (CL: list (val * val * option cookie)) nd a :
  Forall (fun x => isptr (fst (fst x))) CL -> In nd (map (fun x => snd (fst x)) CL) -> hcy5_nodepeer NS nd = a ->
  hcy5_cfind NS CL a <> nullval.
Proof.
  induction CL as [|[[c nd0] o] CL IH]; simpl; intros Hp Hin Ha; [contradiction|].
  inv Hp. hcy5_p12_x_null_dif.
  - simpl in *. intros E; subst c. contradiction.
  - destruct Hin as [<-|Hin]; [congruence | auto].
Qed.

Section Res.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_p12_x_null_res L KS NS PS CL T M now :
  hcy5_lists_ok L KS NS PS -> hcy5_cl_nodes CL NS -> Forall (fun x => isptr (fst (fst x))) CL ->
  hcy5_tgt NS CL (hcy5_res xaead_dec T PS M now) = nullval -> hcy5_res xaead_dec T PS M now = None.
Proof.
  intros (_ & Hpeers & _ & HndN & _) (Hcl & _) Hp Ht.
  destruct (hcy5_res xaead_dec T PS M now) as [[a P']|] eqn:Hres; [exfalso|reflexivity].
  simpl in Ht.
  assert (Ha: In a (map peer_addr4 PS)).
  { unfold hcy5_res, message_consume_model in Hres.
    destruct (t_lookup _ _ _) as [[a0 E]|]; [|discriminate].
    destruct (sfind PS (e_peer E)) as [[sh P]|] eqn:Hs; [|discriminate].
    destruct (negb _); [discriminate|].
    destruct (xaead_dec _ _ _ _); [|discriminate].
    inv Hres. apply hcy5_p12_x_null_sfind_in in Hs. apply (in_map peer_addr4) in Hs. exact Hs. }
  unfold hnodes_peers4 in Hpeers. rewrite <- Hpeers in Ha.
  apply in_map_iff in Ha. destruct Ha as (N & HNa & HN).
  apply (hcy5_p12_x_null_cfind NS CL (hn_addr N) a Hp).
  - rewrite Hcl. apply -> in_rev. apply in_map, HN.
  - rewrite hcy5_p12_x_null_nodepeer; auto.
  - exact Ht.
Qed.

End Res.

(* ---- the arguments of the call ---- *)

Definition hcy5_p12_x_null_sns (T: tstate) (PS: list (val * share * peer)) : list hsnap :=
  map (fun x => match x with (p, _, P) => hs_snap_cur T p P end) PS.
Definition hcy5_p12_x_null_rs (PS: list (val * share * peer)) : list int :=
  map (fun x => match x with (_, _, P) => p_refs P end) PS.
Definition hcy5_p12_x_null_prs (PS: list (val * share * peer)) : list peer :=
  map (fun x => match x with (_, _, P) => P end) PS.

Lemma hcy5_p12_x_null_bytes_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

Lemma hcy5_p12_x_null_veqb_refl x : veqb x x = true.
Proof. unfold veqb. destruct (eq_dec x x); congruence. Qed.

Lemma hcy5_p12_x_null_snap_refl s : snap_eqb s s = true.
Proof.
  destruct s as [[p ty ix] nx hb H]. unfold snap_eqb, entry_eqb, hs_eqb; simpl.
  rewrite ?Int.eq_true, ?Int64.eq_true, ?Bool.eqb_reflx, ?hcy5_p12_x_null_bytes_refl.
  repeat (rewrite if_true by reflexivity). reflexivity.
Qed.

Lemma hcy5_p12_x_null_pr_refl P : pr_eqb P P = true.
Proof.
  unfold pr_eqb, pr_eqb_nc, cookie_eqb.
  rewrite ?hcy5_p12_x_null_veqb_refl, ?Int.eq_true, ?Int64.eq_true, ?Bool.eqb_reflx, ?hcy5_p12_x_null_bytes_refl.
  reflexivity.
Qed.

Lemma hcy5_p12_x_null_same T PS :
  hnodes_same4 T nullval (hcy5_p12_x_null_sns T PS) (hcy5_p12_x_null_rs PS) (hcy5_p12_x_null_prs PS) PS = true.
Proof.
  induction PS as [|[[p s] P] PS IH]; [reflexivity|].
  unfold hcy5_p12_x_null_sns, hcy5_p12_x_null_rs, hcy5_p12_x_null_prs in *.
  cbn [map hnodes_same4]. rewrite IH, andb_true_r.
  hcy5_p12_x_null_dif; auto.
  rewrite hcy5_p12_x_null_snap_refl, Int.eq_true, hcy5_p12_x_null_pr_refl. reflexivity.
Qed.

Lemma hcy5_p12_x_null_snapped_cons T N NS x PS :
  hnodes_snapped4 T (N :: NS) (x :: PS) = hn_snapshot4 T N x :: hnodes_snapped4 T NS PS.
Proof. reflexivity. Qed.

Lemma hcy5_p12_x_null_snapped_maps T NS PS : length NS = length PS ->
  map hn_p (hnodes_snapped4 T NS PS) = map hn_p NS /\
  map hn_snap (hnodes_snapped4 T NS PS) = map hsnap_val (hcy5_p12_x_null_sns T PS) /\
  map hn_refs (hnodes_snapped4 T NS PS) = map Vint (hcy5_p12_x_null_rs PS) /\
  map hn_rest (hnodes_snapped4 T NS PS) = map prsnap_val (hcy5_p12_x_null_prs PS) /\
  length (hnodes_snapped4 T NS PS) = length PS.
Proof.
  revert PS; induction NS as [|N NS IH]; destruct PS as [|x PS]; intros Hl; try discriminate; [simpl; auto|].
  injection Hl as Hl. destruct (IH PS Hl) as (H1 & H2 & H3 & H4 & H5).
  rewrite hcy5_p12_x_null_snapped_cons. destruct x as [[p sh] P]. cbn [map length].
  rewrite H1, H2, H3, H4, H5. simpl. auto.
Qed.

Lemma hcy5_p12_x_null_peers_len NS PS : hnodes_peers4 NS PS -> length NS = length PS.
Proof.
  intros H. unfold hnodes_peers4 in H.
  rewrite <- (map_length hn_p NS), H, map_length. reflexivity.
Qed.

(* the public-key chain: every pknext is NULL or a peer of the list *)
Lemma hcy5_p12_x_null_chain_hd h PS : pk_chain h PS -> h = nullval \/ In h (map peer_addr4 PS).
Proof.
  destruct PS as [|[[p s] P] PS]; simpl; intros H; [auto|]. destruct H as [-> _]. auto.
Qed.

Lemma hcy5_p12_x_null_chain h PS : pk_chain h PS ->
  Forall (fun x => match x with (_, _, P) => vp_ok (map peer_addr4 PS) (p_pknext P) end) PS.
Proof.
  revert h; induction PS as [|[[p s] P] PS IH]; simpl; intros h H; [constructor|].
  destruct H as [_ H]. constructor.
  - destruct (hcy5_p12_x_null_chain_hd _ _ H) as [E|E]; [left; exact E | right; simpl; auto].
  - eapply Forall_impl; [|exact (IH _ H)]. intros [[q t] Q] Hq. destruct Hq as [Hq|Hq]; [left; auto | right; simpl; auto].
Qed.

Lemma hcy5_p12_x_null_succ_in L a : succ_in L a = nullval \/ In (succ_in L a) L.
Proof.
  induction L as [|x L IH]; simpl; auto.
  hcy5_p12_x_null_dif.
  - destruct L; simpl; auto.
  - destruct IH; auto.
Qed.

Lemma hcy5_p12_x_null_kaddrs T KE : map ke_addr (map (kent_snapped T) KE) = map ke_addr KE.
Proof. rewrite map_map. reflexivity. Qed.

Lemma hcy5_p12_x_null_pool_addrs AS KS own ix :
  saddrs (hcy5_pool AS KS own ix) = KS ++ map hs_addr AS.
Proof.
  unfold hcy5_pool, saddrs. rewrite map_app, !map_map. f_equal.
  induction KS as [|k KS IH]; simpl; f_equal; auto.
Qed.

(* every entry of the pool belongs to a peer of the list *)
Lemma hcy5_p12_x_null_entry_peer T PS KE a :
  hcy5_T_ok PS KE T -> In a (saddrs (t_D T)) -> In (e_peer (t_entry_d T a)) (map peer_addr4 PS).
Proof.
  intros ((own & ix & HD & Hown) & _) Ha.
  destruct (hcy5_p12_x_null_sfind_some _ _ Ha) as (sh & E & Hs).
  unfold t_entry_d, t_entry. rewrite Hs.
  apply hcy5_p12_x_null_sfind_in in Hs. rewrite HD in Hs. unfold hcy5_pool in Hs.
  apply in_app_iff in Hs. destruct Hs as [Hs|Hs]; apply in_map_iff in Hs; destruct Hs as (k & Hk & Hin).
  - unfold hcy5_kentry in Hk. inv Hk. simpl.
    exact (proj1 (Forall_forall _ _) Hown _ Hin).
  - unfold hcy5_hent in Hk. inv Hk. simpl. exact Hin.
Qed.

Lemma hcy5_p12_x_null_cmp own T PS :
  (forall p sh P, In (p, sh, P) PS ->
     In (hs_addr p) (saddrs (t_D T)) /\
     Forall (vp_ok own) (hs_ptrs (hs_snap_cur T p P) (hs_snap_cur T p P) ++ pr_ptrs P P)) ->
  hn4_cmp_ok own T (hcy5_p12_x_null_sns T PS) (hcy5_p12_x_null_prs PS) PS.
Proof.
  induction PS as [|[[p s] P] PS IH]; intros H; [simpl; auto|].
  unfold hcy5_p12_x_null_sns, hcy5_p12_x_null_prs in *. cbn [map hn4_cmp_ok]. split.
  - apply (H p s P). left; reflexivity.
  - apply IH. intros q t Q Hq. apply (H q t Q). right; exact Hq.
Qed.

Section Pure.
Variable x25519: list byte -> list byte -> list byte.

(* the objects lent to hnodes_same_except: A's device (p_device, hs_sid) and the kents (keypair slots) *)
Definition hcy5_p12_x_null_VO (R: hcy5_run) (L: hcy5_loc) (T: tstate) (KE: list kent4) : list vobj :=
  [VDev Tsh (l_wa L) (hcy5_DA x25519 R L); VKents (hcy5_khead KE) (map (kent_snapped T) KE)].

Lemma hcy5_p12_x_null_facts R L NS PS KE T :
  hcy5_lists_ok L (map ke_addr KE) NS PS -> hcy5_T_ok PS KE T -> itable_wf T ->
  Forall vobj_ok (hcy5_p12_x_null_VO R L T KE) /\
  hnodes_peers4 (hnodes_snapped4 T NS PS) PS /\ peers_wf PS /\
  Zlength (hcy5_p12_x_null_sns T PS) = Zlength (hnodes_snapped4 T NS PS) /\
  Zlength (hcy5_p12_x_null_rs PS) = Zlength (hnodes_snapped4 T NS PS) /\
  Zlength (hcy5_p12_x_null_prs PS) = Zlength (hnodes_snapped4 T NS PS) /\
  map hn_snap (hnodes_snapped4 T NS PS) = map hsnap_val (hcy5_p12_x_null_sns T PS) /\
  map hn_refs (hnodes_snapped4 T NS PS) = map Vint (hcy5_p12_x_null_rs PS) /\
  map hn_rest (hnodes_snapped4 T NS PS) = map prsnap_val (hcy5_p12_x_null_prs PS) /\
  hn4_cmp_ok (map peer_addr4 PS ++ saddrs (t_D T) ++ vobjs_addrs (hcy5_p12_x_null_VO R L T KE)) T
    (hcy5_p12_x_null_sns T PS) (hcy5_p12_x_null_prs PS) PS /\
  hnodes_same4 T nullval (hcy5_p12_x_null_sns T PS) (hcy5_p12_x_null_rs PS) (hcy5_p12_x_null_prs PS) PS = true.
Proof.
  intros Hl HT Hw.
  destruct Hl as (Hpok & Hpeers & _ & _ & Hch).
  pose proof HT as HT'. destruct HT' as ((own0 & ix & HD & _) & _).
  destruct Hw as (_ & Hincl & _ & _).
  pose proof (hcy5_p12_x_null_peers_len _ _ Hpeers) as Hlen.
  destruct (hcy5_p12_x_null_snapped_maps T NS PS Hlen) as (H0 & H1 & H2 & H3 & H4).
  set (own := map peer_addr4 PS ++ saddrs (t_D T) ++ vobjs_addrs (hcy5_p12_x_null_VO R L T KE)).
  assert (Hown: forall v, In v (map peer_addr4 PS) \/ In v (saddrs (t_D T)) \/
                          In v [l_wa L; id_addr (l_wa L); cc_addr (l_wa L)] \/ In v (map ke_addr KE) ->
                vp_ok own v).
  { intros v Hv. right. unfold own.
    assert (Hk: In v (map ke_addr KE) -> In v (saddrs (t_D T))).
    { intros Hk. rewrite HD. unfold hcy5_pool, saddrs. rewrite map_app, in_app_iff. left.
      rewrite map_map. erewrite map_ext; [rewrite map_id; exact Hk | intros; reflexivity]. }
    unfold hcy5_p12_x_null_VO, vobjs_addrs. simpl.
    rewrite !in_app_iff. simpl. tauto. }
  assert (Hchain := hcy5_p12_x_null_chain _ _ Hch).
  clearbody own.
  split; [unfold hcy5_p12_x_null_VO; repeat constructor; simpl; auto|].
  split; [unfold hnodes_peers4; rewrite H0; exact Hpeers|].
  split.
  { unfold peers_wf. eapply Forall_impl; [|exact Hpok]. intros [[a sh] P] Hp. destruct Hp as (-> & _). auto. }
  split; [unfold hcy5_p12_x_null_sns; rewrite !Zlength_correct, map_length, H4; reflexivity|].
  split; [unfold hcy5_p12_x_null_rs; rewrite !Zlength_correct, map_length, H4; reflexivity|].
  split; [unfold hcy5_p12_x_null_prs; rewrite !Zlength_correct, map_length, H4; reflexivity|].
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [|apply hcy5_p12_x_null_same].
  apply hcy5_p12_x_null_cmp. intros p sh P Hin.
  assert (Hin_a: In (hs_addr p) (saddrs (t_D T))).
  { rewrite HD, hcy5_p12_x_null_pool_addrs, in_app_iff. right.
    apply (in_map (fun x => hs_addr (peer_addr4 x))) in Hin. rewrite <- map_map in Hin. exact Hin. }
  split; [exact Hin_a|].
  pose proof (proj1 (Forall_forall _ _) Hpok _ Hin) as Hk. simpl in Hk.
  destruct Hk as (_ & Hdev & Hsid & _ & _ & Hslots).
  pose proof (proj1 (Forall_forall _ _) Hchain _ Hin) as Hc. simpl in Hc.
  pose proof (hcy5_p12_x_null_entry_peer _ _ _ _ HT Hin_a) as He.
  assert (Hsucc: vp_ok own (succ_in (t_L T) (hs_addr p))).
  { destruct (hcy5_p12_x_null_succ_in (t_L T) (hs_addr p)) as [E|E]; [left; exact E|].
    apply Hown. right; left. apply Hincl, E. }
  assert (Hep: vp_ok own (e_peer (t_entry_d T (hs_addr p)))) by (apply Hown; tauto).
  assert (Hdv: vp_ok own (p_device P)) by (rewrite Hdev; apply Hown; simpl; tauto).
  assert (Hsd: vp_ok own (hs_sid (p_hs P))) by (rewrite Hsid; apply Hown; simpl; tauto).
  assert (Hpk: vp_ok own (p_pknext P)).
  { destruct Hc as [E|E]; [left; exact E | apply Hown; tauto]. }
  inv Hslots. match goal with Hx: Forall _ [_; _] |- _ => inv Hx end.
  match goal with Hx: Forall _ [_] |- _ => inv Hx end.
  assert (Hs1: vp_ok own (p_cur P)).
  { match goal with H: p_cur P = nullval \/ _ |- _ => destruct H as [E|E]; [left; exact E | apply Hown; tauto] end. }
  assert (Hs2: vp_ok own (p_prev P)).
  { match goal with H: p_prev P = nullval \/ _ |- _ => destruct H as [E|E]; [left; exact E | apply Hown; tauto] end. }
  assert (Hs3: vp_ok own (p_next P)).
  { match goal with H: p_next P = nullval \/ _ |- _ => destruct H as [E|E]; [left; exact E | apply Hown; tauto] end. }
  unfold hs_ptrs, hs_ptrs_nn, hs_snap_cur, snap_of, pr_ptrs. cbn [sn_next sn_entry sn_hs app].
  repeat first [apply Forall_nil | apply Forall_cons; [assumption|]].
Qed.

End Pure.

(* ---- separation helpers ---- *)

Lemma hcy5_p12_x_null_cns_ptr l CL : hcy5_cns l CL |-- !! Forall (fun x => isptr (fst (fst x))) CL.
Proof.
  revert l; induction CL as [|[[c nd] o] CL IH]; intros l; simpl.
  - entailer!.
  - Intros. subst l. sep_apply (IH (hcy5_chead CL)). entailer!.
Qed.

Lemma hcy5_p12_x_null_hn_pn l NS : hnodes_rep4 W l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [|N NS]; cbn [hnodes_rep4].
  - entailer!.
  - Intros nx. subst l. entailer!.
    match goal with Hf: field_compatible _ _ _ |- _ => destruct Hf as [Hp _] end.
    apply isptr_is_pointer_or_null; exact Hp.
Qed.

Local Open Scope logic.
Lemma hcy5_p12_x_null_vo sh wg D l KE :
  device_rep sh wg D * kents_rep W l KE = vobjs W [VDev sh wg D; VKents l KE].
Proof. unfold vobjs. cbn [iter_sepcon vobj_rep]. rewrite sepcon_emp. reflexivity. Qed.
