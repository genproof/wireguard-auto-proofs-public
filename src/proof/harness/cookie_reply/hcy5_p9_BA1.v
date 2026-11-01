(* law cookie_reply, phase P9, segment BA1.  h = &np->p->handshake; if (!h->entry.hashed) insert(&ita, &h->entry).
   Port of v1's *)
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
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p9_defs.
Require WgNoise.harness.x_cookie_reply.code.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

(* ---- pure helpers ---- *)
Lemma hcy5_p9_BA1_comb {A B C: Type} (f: A -> C) (g: B -> C) (l1: list A) (l2: list B) x y :
  In (x, y) (combine l1 l2) -> map f l1 = map g l2 -> f x = g y.
Proof.
  revert l2. induction l1 as [| x1 l1 IH]; intros [| x2 l2] Hin Hm; simpl in *; try contradiction;
    try discriminate.
  injection Hm as Hx Hm. destruct Hin as [Heq | Hin].
  - injection Heq as <- <-. exact Hx.
  - exact (IH l2 Hin Hm).
Qed.

(* A's pool (hcy5_T_ok): the handshake entry of a peer a of PS is found at hs_addr a (type HANDSHAKE, peer a);
   wg_index_hashtable_insert of it (raw = None) with a fresh index keeps hcy5_T_ok and gives it the index *)
Lemma hcy5_p9_BA1_pure_sfind_in_nodup (D: list (val * share * entry)) x sh E :
  NoDup (saddrs D) -> In (x, sh, E) D -> sfind D x = Some (sh, E).
Proof.
  induction D as [| [[y sh'] E'] D IH]; cbn; intros Hnd Hin; [contradiction |].
  inversion Hnd; subst. destruct (EqDec_val y x) as [-> | Hne].
  - destruct Hin as [Heq | Hin]; [inversion Heq; reflexivity |].
    exfalso. match goal with H: ~ In x _ |- _ => apply H end.
    unfold saddrs. apply in_map_iff. exists (x, sh, E). auto.
  - destruct Hin as [Heq | Hin]; [inversion Heq; congruence |]. auto.
Qed.

Lemma hcy5_p9_BA1_pure_nodup_app {B: Type} (l1 l2: list B) x :
  NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  induction l1 as [| y l1 IH]; cbn; intros Hnd H1 H2; [contradiction |].
  inversion Hnd; subst. destruct H1 as [-> | H1].
  - apply H3. apply in_or_app. auto.
  - eauto.
Qed.

Lemma hcy5_p9_BA1_pure_nodup_map_inj {B C: Type} (f: B -> C) l x y :
  NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [| z l IH]; cbn; intros Hnd Hx Hy Hf; [contradiction |].
  inversion Hnd; subst. destruct Hx as [-> | Hx]; destruct Hy as [-> | Hy]; auto.
  - exfalso. apply H1. rewrite Hf. apply in_map; auto.
  - exfalso. apply H1. rewrite <- Hf. apply in_map; auto.
Qed.

Lemma hcy5_p9_BA1_pure_supd_map (D: list (val * share * entry)) e v :
  NoDup (saddrs D) ->
  supd D e v = map (fun '(x, sh, w) => if eq_dec x e then (x, sh, v) else (x, sh, w)) D.
Proof.
  induction D as [| [[y sh] w] D IH]; cbn; intros Hnd; [reflexivity |].
  inversion Hnd; subst. destruct (EqDec_val y e) as [-> | Hne].
  - f_equal. transitivity (map (fun x => x) D); [symmetry; apply map_id |].
    apply map_ext_in. intros [[x shx] wx] Hx. destruct (EqDec_val x e) as [-> | _]; [| reflexivity].
    exfalso. match goal with H: ~ In e _ |- _ => apply H end.
    unfold saddrs. apply in_map_iff. exists (e, shx, wx). auto.
  - f_equal. auto.
Qed.

Lemma hcy5_p9_BA1_pure_sfind_supd_eq (D: list (val * share * entry)) e v :
  In e (saddrs D) -> exists sh, sfind (supd D e v) e = Some (sh, v).
Proof.
  induction D as [| [[y sh] w] D IH]; cbn; intros Hin; [contradiction |].
  destruct (EqDec_val y e) as [-> | Hne].
  - cbn. destruct (EqDec_val e e) as [_ | Hn]; [eauto | congruence].
  - cbn. destruct (EqDec_val y e) as [-> | _]; [congruence |].
    destruct Hin as [Heq | Hin]; [congruence | auto].
Qed.

Lemma hcy5_p9_BA1_pure_sfind_supd_ne (D: list (val * share * entry)) e v x :
  x <> e -> sfind (supd D e v) x = sfind D x.
Proof.
  intros Hx. induction D as [| [[y sh] w] D IH]; cbn; [reflexivity |].
  destruct (EqDec_val y e) as [-> | Hne].
  - cbn. destruct (EqDec_val e x) as [-> | _]; [congruence | reflexivity].
  - cbn. destruct (EqDec_val y x); [reflexivity | exact IH].
Qed.

Lemma hcy5_p9_BA1_pure_in_vremove a m L : In a (vremove m L) -> In a L /\ a <> m.
Proof.
  induction L as [| x L IH]; cbn; [tauto |].
  destruct (EqDec_val x m) as [-> | Hx]; intros H.
  - destruct (IH H); auto.
  - destruct H as [<- | H]; [auto |]. destruct (IH H); auto.
Qed.

Lemma hcy5_p9_BA1_pure_vremove_nodup {B: Type} (f: val -> B) m L :
  NoDup (map f L) -> NoDup (map f (vremove m L)).
Proof.
  induction L as [| x L IH]; cbn; intros H; [constructor |].
  inversion H; subst. destruct (EqDec_val x m); [auto |]. cbn. constructor; [| auto].
  intros Hin. apply in_map_iff in Hin. destruct Hin as (y & Hy & Hin).
  apply hcy5_p9_BA1_pure_in_vremove in Hin. destruct Hin as [Hin _]. apply H2. rewrite <- Hy. apply in_map; auto.
Qed.

Lemma hcy5_p9_BA1_pure_saddrs AS KS own ix :
  saddrs (hcy5_pool AS KS own ix) = KS ++ map hs_addr AS.
Proof.
  unfold hcy5_pool, saddrs. rewrite map_app, !map_map.
  rewrite <- (map_id KS) at 2. f_equal; apply map_ext; reflexivity.
Qed.

Lemma hcy5_p9_BA1_pure :
  (forall PS KE T a,
     hcy5_T_ok PS KE T -> itable_wf T -> In a (map peer_addr4 PS) ->
     exists i, sfind (t_D T) (hs_addr a) = Some (Ews, mkEntry a IDX_HANDSHAKE i)) /\
  (forall PS KE T a idx,
     hcy5_T_ok PS KE T -> itable_wf T -> In a (map peer_addr4 PS) -> t_fresh T (hs_addr a) idx ->
     hcy5_T_ok PS KE (t_insert T (hs_addr a) idx) /\
     t_entry (t_insert T (hs_addr a) idx) (hs_addr a) = Some (mkEntry a IDX_HANDSHAKE idx) /\
     In (hs_addr a) (t_L (t_insert T (hs_addr a) idx))).
Proof.
  assert (Hfind: forall PS KE T a, hcy5_T_ok PS KE T -> itable_wf T -> In a (map peer_addr4 PS) ->
    exists own ix, t_D T = hcy5_pool (map peer_addr4 PS) (map ke_addr KE) own ix /\
      Forall (fun k => In (own k) (map peer_addr4 PS)) (map ke_addr KE) /\
      sfind (t_D T) (hs_addr a) = Some (Ews, mkEntry a IDX_HANDSHAKE (ix (hs_addr a)))).
  { intros PS KE T a ((own & ix & HD & Hown) & _) (_ & _ & Hnd & _) Ha. exists own, ix.
    split; [exact HD |]. split; [exact Hown |].
    apply hcy5_p9_BA1_pure_sfind_in_nodup; [exact Hnd |]. rewrite HD. unfold hcy5_pool. apply in_or_app. right.
    apply in_map_iff. exists a. split; [reflexivity | exact Ha]. }
  split.
  { intros PS KE T a HT Hwf Ha. destruct (Hfind PS KE T a HT Hwf Ha) as (own & ix & _ & _ & H). eauto. }
  intros PS KE T a idx HT Hwf Ha Hf.
  destruct (Hfind PS KE T a HT Hwf Ha) as (own & ix & HD & Hown & Hs).
  destruct HT as (_ & Hnd). destruct Hwf as (_ & _ & Hnda & _).
  set (e := hs_addr a) in *.
  assert (Hti: t_insert T e idx = mkT (supd (t_D T) e (mkEntry a IDX_HANDSHAKE idx)) (e :: vremove e (t_L T))).
  { unfold t_insert, t_set_index, t_entry. rewrite Hs. reflexivity. }
  assert (He: t_entry (t_insert T e idx) e = Some (mkEntry a IDX_HANDSHAKE idx)).
  { rewrite Hti. unfold t_entry. cbn [t_D].
    destruct (hcy5_p9_BA1_pure_sfind_supd_eq (t_D T) e (mkEntry a IDX_HANDSHAKE idx)) as (sh & ->); [| reflexivity].
    rewrite HD, hcy5_p9_BA1_pure_saddrs. apply in_or_app; right. apply in_map; exact Ha. }
  split; [| split; [exact He | rewrite Hti; left; reflexivity]].
  split.
  - exists own, (fun v => if eq_dec v e then idx else ix v). split; [| exact Hown].
    rewrite Hti. cbn [t_D]. rewrite hcy5_p9_BA1_pure_supd_map by exact Hnda. rewrite HD.
    rewrite HD, hcy5_p9_BA1_pure_saddrs in Hnda.
    set (KS := map ke_addr KE) in *. set (AS := map peer_addr4 PS) in *. clearbody KS AS.
    unfold hcy5_pool. rewrite map_app, !map_map. f_equal.
    + apply map_ext_in. intros k Hk. unfold hcy5_kentry. cbv beta iota.
      destruct (eq_dec k e) as [-> | _]; [| reflexivity].
      exfalso. apply (hcy5_p9_BA1_pure_nodup_app _ _ e Hnda Hk). apply in_map; exact Ha.
    + apply map_ext_in. intros p Hp. unfold hcy5_hent. cbv beta iota.
      destruct (eq_dec (hs_addr p) e) as [Hee | _]; [| reflexivity].
      assert (p = a) as ->; [| reflexivity].
      apply (hcy5_p9_BA1_pure_nodup_map_inj hs_addr AS);
        [exact (NoDup_app_remove_l _ _ Hnda) | exact Hp | exact Ha | exact Hee].
  - rewrite Hti in He |- *. unfold t_indices. cbn [t_L map]. rewrite He. cbn [e_index].
    unfold t_fresh, t_indices in Hf.
    assert (Hm: map (fun x => match t_entry (mkT (supd (t_D T) e (mkEntry a IDX_HANDSHAKE idx)) (e :: vremove e (t_L T))) x
                              with Some E => e_index E | None => Int.zero end) (vremove e (t_L T)) =
                map (fun x => match t_entry T x with Some E => e_index E | None => Int.zero end) (vremove e (t_L T))).
    { apply map_ext_in. intros x Hx. apply hcy5_p9_BA1_pure_in_vremove in Hx. unfold t_entry. cbn [t_D].
      rewrite hcy5_p9_BA1_pure_sfind_supd_ne by tauto. reflexivity. }
    rewrite Hm. constructor; [exact Hf |]. apply hcy5_p9_BA1_pure_vremove_nodup; exact Hnd.
Qed.

Lemma hcy5_p9_BA1_find PS KE T a :
  hcy5_T_ok PS KE T -> itable_wf T -> In a (map peer_addr4 PS) ->
  exists i, sfind (t_D T) (hs_addr a) = Some (Ews, mkEntry a IDX_HANDSHAKE i).
Proof. apply hcy5_p9_BA1_pure. Qed.

Lemma hcy5_p9_BA1_ins PS KE T a idx :
  hcy5_T_ok PS KE T -> itable_wf T -> In a (map peer_addr4 PS) -> t_fresh T (hs_addr a) idx ->
  hcy5_T_ok PS KE (t_insert T (hs_addr a) idx) /\
  t_entry (t_insert T (hs_addr a) idx) (hs_addr a) = Some (mkEntry a IDX_HANDSHAKE idx) /\
  In (hs_addr a) (t_L (t_insert T (hs_addr a) idx)).
Proof. apply hcy5_p9_BA1_pure. Qed.

Lemma hcy5_p9_BA1_sfind_entry T x sh E : sfind (t_D T) x = Some (sh, E) -> t_entry T x = Some E.
Proof. intros H. unfold t_entry. rewrite H. reflexivity. Qed.

Lemma hcy5_p9_BA1_vin_true x L : vin x L = true -> In x L.
Proof. unfold vin. destruct (in_dec eq_dec x L); [auto | discriminate]. Qed.

Lemma hcy5_p9_BA1_sfind_in (D: list (val * share * entry)) x sh E : sfind D x = Some (sh, E) -> In x (saddrs D).
Proof.
  induction D as [| [[y shy] w] D IH]; simpl; intros H; [discriminate |].
  destruct (EqDec_val y x) as [-> | Hn]; [left; reflexivity | right; exact (IH H)].
Qed.

(* ---- separation-logic helpers ---- *)
Lemma hcy5_p9_BA1_wf sht tab T : itable sht tab T |-- !! itable_wf T.
Proof. unfold itable. entailer!. Qed.

Lemma hcy5_p9_BA1_pfc PS a sh P :
  In (a, sh, P) PS -> peers_rep PS |-- !! @field_compatible Noise.CS t_peer [] a.
Proof.
  intros Hin. apply in_split in Hin. destruct Hin as (l1 & l2 & ->).
  unfold peers_rep. rewrite iter_sepcon_app. simpl iter_sepcon. cbn [peer_item_rep].
  unfold peer_rep at 1. entailer!.
Qed.

#[local] Instance hcy5_p9_BA1_cce_N : change_composite_env Noise.CS W_cookie_reply.
Proof. make_cs_preserve Noise.CS W_cookie_reply. Defined.
#[local] Instance hcy5_p9_BA1_cce_K : change_composite_env CKS W_cookie_reply.
Proof. make_cs_preserve CKS W_cookie_reply. Defined.

Lemma hcy5_p9_BA1_wand_self (X F G: mpred) : X |-- F * G -> F * G |-- X -> X |-- F * (F -* X).
Proof.
  intros H1 H2. eapply derives_trans; [exact H1 |]. apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. exact H2.
Qed.

Lemma hcy5_p9_BA1_wand_frame (A B C F: mpred) : A * B |-- C -> A * (F * (F -* B)) |-- F * (F -* C).
Proof.
  intros H. rewrite <- sepcon_assoc, (sepcon_comm A F), sepcon_assoc.
  apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint. eapply derives_trans; [| exact H].
  rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl |].
  rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

(* the field p of a node *)
Lemma hcy5_p9_BA1_node1 (N: hnode4) nx :
  @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N) |--
  @field_at W Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) *
  (@field_at W Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) -*
   @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N)).
Proof.
  rewrite (@data_at_change_composite CKS W _ Ews t_hnode4 _ _ (JMeq_refl _)) by prove_cs_preserve_type.
  unfold_data_at (@data_at W Ews t_hnode4 _ (hn_addr N)).
  apply sepcon_derives; [apply derives_refl | apply wand_frame_intro].
Qed.

(* the field p of the node N (its peer v), the rest of the list as a wand *)
Lemma hcy5_p9_BA1_node h NS N v :
  In N NS -> hn_p N = v ->
  hnodes_rep4 W h NS |--
  @field_at W Ews t_hnode4 (DOT HY._p) v (hn_addr N) *
  (@field_at W Ews t_hnode4 (DOT HY._p) v (hn_addr N) -* hnodes_rep4 W h NS).
Proof.
  intros Hin <-. revert h. induction NS as [| N0 NS IH]; intros h; [contradiction |].
  destruct Hin as [-> | Hin].
  - simpl hnodes_rep4. Intros nx. subst h.
    apply derives_trans with
      (@malloc_token W Ews t_hnode4 (hn_addr N) * @malloc_token W Ews t_peer (hn_p N) * hnodes_rep4 W nx NS *
       (@field_at W Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) *
        (@field_at W Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) -*
         @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N))))%logic.
    + sep_apply (hcy5_p9_BA1_node1 N nx). cancel.
    + apply hcy5_p9_BA1_wand_frame. Exists nx. entailer!.
  - simpl hnodes_rep4. Intros nx. subst h.
    apply derives_trans with
      (@malloc_token W Ews t_hnode4 (hn_addr N0) *
       @data_at CKS Ews t_hnode4 (hn_p N0, (hn_snap N0, (hn_refs N0, (hn_rest N0, nx)))) (hn_addr N0) *
       @malloc_token W Ews t_peer (hn_p N0) *
       (@field_at W Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) *
        (@field_at W Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) -* hnodes_rep4 W nx NS)))%logic.
    + sep_apply (IH Hin nx). cancel.
    + apply hcy5_p9_BA1_wand_frame. Exists nx. entailer!.
Qed.

Lemma hcy5_p9_BA1_split (D: list (val * share * entry)) a sh E (f: val * share * entry -> mpred) :
  sfind D a = Some (sh, E) -> iter_sepcon f D = (f (a, sh, E) * iter_sepcon f (sdel D a))%logic.
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; reflexivity|].
  rewrite (IH H); simpl. rewrite <- !sepcon_assoc, (sepcon_comm (f _) (f _)). reflexivity.
Qed.

Lemma hcy5_p9_BA1_fc p : @field_compatible Noise.CS t_peer [] p -> @field_compatible W t_peer [] p.
Proof. intros. apply (@field_compatible_change_composite Noise.CS W _ t_peer); auto. Qed.

(* the pool item at hs_addr p (Noise.CS) = the field entry of the handshake at hs_addr p (W) *)
Lemma hcy5_p9_BA1_entry_fa sh v p :
  @field_compatible Noise.CS t_peer [] p ->
  @data_at Noise.CS sh t_entry_s v (hs_addr p) = @field_at W sh t_hs (DOT HY._entry) v (hs_addr p).
Proof.
  intros FC0. pose proof (hcy5_p9_BA1_fc p FC0) as FC.
  rewrite (@data_at_change_composite Noise.CS W _ sh t_entry_s v v (JMeq_refl v)) by reflexivity.
  assert (FC1: field_compatible t_peer (DOT HY._handshake) p) by auto with field_compatible.
  assert (FC2: field_compatible t_hs [] (hs_addr p)).
  { apply field_compatible_nested_field in FC1. exact FC1. }
  assert (FC3: field_compatible t_hs (DOT HY._entry) (hs_addr p)) by auto with field_compatible.
  rewrite field_at_data_at. rewrite field_address_offset by auto. simpl.
  rewrite isptr_offset_val_zero by (unfold hs_addr; destruct FC as [Hp _]; destruct p; try contradiction; exact I).
  reflexivity.
Qed.

(* the handshake entry of the peer at a (the pool item at hs_addr a) as the field entry of a's handshake *)
Lemma hcy5_p9_BA1_ent sht tab T a E :
  @field_compatible Noise.CS t_peer [] a -> itable_wf T -> sfind (t_D T) (hs_addr a) = Some (Ews, E) ->
  itable sht tab T |--
  @field_at W Ews t_hs (DOT HY._entry)
    (entry_val E (succ_in (t_L T) (hs_addr a)) (vin (hs_addr a) (t_L T))) (hs_addr a) *
  (@field_at W Ews t_hs (DOT HY._entry)
     (entry_val E (succ_in (t_L T) (hs_addr a)) (vin (hs_addr a) (t_L T))) (hs_addr a) -*
   itable sht tab T).
Proof.
  intros FC Hwf Hf.
  apply hcy5_p9_BA1_wand_self with
    (G := (@data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab *
           iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) (hs_addr a)))%logic).
  - unfold itable. Intros. rewrite (hcy5_p9_BA1_split _ _ _ _ _ Hf).
    change (pool_item_rep (t_L T) (hs_addr a, Ews, E)) with
      (entry_at Ews (hs_addr a) E (succ_in (t_L T) (hs_addr a)) (vin (hs_addr a) (t_L T))).
    unfold entry_at.
    rewrite hcy5_p9_BA1_entry_fa by auto. cancel.
  - unfold itable. rewrite (hcy5_p9_BA1_split _ _ _ _ _ Hf).
    change (pool_item_rep (t_L T) (hs_addr a, Ews, E)) with
      (entry_at Ews (hs_addr a) E (succ_in (t_L T) (hs_addr a)) (vin (hs_addr a) (t_L T))).
    unfold entry_at.
    rewrite hcy5_p9_BA1_entry_fa by auto. entailer!.
Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_p9_BA1_ok {Espec: OracleKind} gv L FR R S m c rp Q nonce rr CK CM NS PS T np CL KE md N a P :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hcy5_p9_inv x25519 xaead_enc R L Q m nonce rr CK CM NS PS T np CL KE ->
  In (N, (a, Ews, P)) (combine NS PS) -> hn_addr N = np ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hcy5_p9_PA x25519 gv L FR R S m c rp Q rr CK NS PS T np CL KE CM md [] [])
    hcy5_p9_BA1
    (normal_ret_assert
      (EX S1: shim, EX T1: tstate, EX idx: int,
       hcy5_p9_PA x25519 gv L FR R S1 m c rp Q rr CK NS PS T1 np CL KE CM md
         [hcy5_T_ok PS KE T1; t_entry T1 (hs_addr a) = Some (mkEntry a IDX_HANDSHAKE idx);
          In (hs_addr a) (t_L T1)]
         [temp HY._h (hs_addr a)])).
Proof.
  intros HH Hinv HIn HN.
  unfold hcy5_Delta, hcy5_p9_PA, hcy5_p9_loc, hcy5_p9_sep, hcy5_p9_BA1. simplify_func_tycontext. abbreviate_semax.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs, hcy5_lvars. simpl app.
  destruct Hinv as (Hrep & Hlists & Hnp & HTok & Hcl & Hcn).
  pose proof Hlists as (Hpok & Hpeers & HndP & HndN & Hpk).
  assert (Ha: hn_p N = a) by exact (hcy5_p9_BA1_comb hn_p peer_addr4 NS PS N (a, Ews, P) HIn Hpeers).
  assert (HNin: In N NS) by (eapply in_combine_l; eauto).
  assert (HPin: In (a, Ews, P) PS) by (eapply in_combine_r; eauto).
  assert (HaPS: In a (map peer_addr4 PS)) by (change a with (peer_addr4 (a, Ews, P)); apply in_map; auto).
  assert_PROP (@field_compatible Noise.CS t_peer [] a) as Hfc.
  { sep_apply (hcy5_p9_BA1_pfc PS a Ews P HPin). entailer!. }
  assert (Hpa: isptr a) by exact (field_compatible_isptr _ _ _ Hfc).
  subst np.
  sep_apply (hcy5_p9_BA1_node (hcy5_head NS) NS N a HNin Ha). Intros.
  forward.
  forward.
  match goal with |- context [temp HY._h (offset_val ?z a)] =>
    replace z with OFS_PEER_HANDSHAKE by reflexivity end.
  fold (hs_addr a).
  sep_apply (modus_ponens_wand (@field_at W Ews t_hnode4 (DOT HY._p) a (hn_addr N))).
  assert_PROP (itable_wf T) as Hwf.
  { sep_apply (hcy5_p9_BA1_wf Tsh (l_ita L) T). entailer!. }
  destruct (hcy5_p9_BA1_find PS KE T a HTok Hwf HaPS) as [i0 Hf].
  sep_apply (hcy5_p9_BA1_ent Tsh (l_ita L) T a _ Hfc Hwf Hf). Intros.
  unfold entry_val. cbn [e_peer e_type e_index].
  forward.
  { entailer!. match goal with |- context [Val.of_bool ?b] => destruct b; simpl; auto end. }
  sep_apply modus_ponens_wand.
  forward_if.
  - (* not hashed: insert *)
    assert (Hv: vin (hs_addr a) (t_L T) = false)
      by (destruct (vin (hs_addr a) (t_L T)); [inversion H | reflexivity]).
    assert (Hha: isptr (hs_addr a)) by (unfold hs_addr; destruct a; try contradiction; exact I).
    forward_call (gv, S, hcy5_w0, Tsh, l_ita L, T, hs_addr a, @None (share * entry)).
    { cbn [raw_rep]. cancel. }
    { cbn [raw_ok]. eapply hcy5_p9_BA1_sfind_in; eauto. }
    Intros idx. cbn [raw_add] in *.
    destruct (hcy5_p9_BA1_ins PS KE T a idx HTok Hwf HaPS H0) as (Hok1 & He1 & Hi1).
    Exists (shim_u32 S idx) (t_insert T (hs_addr a) idx) idx.
    unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs, hcy5_lvars. cbn [app].
    entailer!.
  - (* hashed *)
    assert (Hv: vin (hs_addr a) (t_L T) = true)
      by (destruct (vin (hs_addr a) (t_L T)); [reflexivity | inversion H]).
    forward.
    Exists S T i0.
    unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs, hcy5_lvars. cbn [app].
    entailer!.
    split; [eapply hcy5_p9_BA1_sfind_entry; eauto | apply hcy5_p9_BA1_vin_true; auto].
Qed.

End Seg.
