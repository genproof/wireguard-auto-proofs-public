(* law cookie_reply, phase P12, segment R:
   s75: the round trip CHECKs (v1 R: hcy4_p12_R.v + hcy4_p12_rt.v).
   St -> St over fixed values (hcy5_p12_defs.v). *)
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
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p12_defs.
Require WgNoise.harness.x_cookie_reply.code.
Require Import WgNoise.proof.libc.libc_bytes.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Pure facts                                                              *)
(* ---------------------------------------------------------------------- *)

Lemma hcy5_p12_r_eqb_refl l : bytes_eqb l l = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec l l); congruence. Qed.

Lemma hcy5_p12_r_pos NS PS N x :
  In (N, x) (combine NS PS) -> hnodes_peers4 NS PS ->
  In N NS /\ In x PS /\ hn_p N = peer_addr4 x.
Proof.
  revert PS; induction NS as [| M NS IH]; intros PS Hin Hp; destruct PS as [| y PS]; simpl in Hin;
    try contradiction.
  unfold hnodes_peers4 in Hp; simpl in Hp; injection Hp as Hy Hp'.
  destruct Hin as [Heq | Hin].
  - injection Heq as -> ->. simpl. auto.
  - destruct (IH PS Hin Hp') as (H1 & H2 & H3). simpl. auto.
Qed.

(* the snapped node of N: same address and peer *)
Lemma hcy5_p12_r_snap T NS PS N x :
  In (N, x) (combine NS PS) ->
  exists N', In N' (hnodes_snapped4 T NS PS) /\ hn_addr N' = hn_addr N /\ hn_p N' = hn_p N.
Proof.
  intros Hin. exists (hn_snapshot4 T N x). split.
  - unfold hnodes_snapped4. apply (in_map (fun '(N, x) => hn_snapshot4 T N x) _ _ Hin).
  - unfold hn_snapshot4. destruct x as [[q sh] P]. auto.
Qed.

Lemma hcy5_p12_r_supd_in (PS: list (val * share * peer)) a sh P P' :
  NoDup (map peer_addr4 PS) -> In (a, sh, P) PS -> In (a, sh, P') (supd PS a P').
Proof.
  induction PS as [| [[x shx] w] PS IH]; intros Hnd Hin; [contradiction |].
  simpl in Hnd. inversion Hnd as [| ? ? Hnin Hnd']; subst. simpl supd.
  destruct (EqDec_val x a) as [-> | Hne].
  - destruct Hin as [Heq | Hin].
    + injection Heq as -> ->. left. reflexivity.
    + exfalso. apply Hnin. apply (in_map peer_addr4) in Hin. exact Hin.
  - destruct Hin as [Heq | Hin]; [injection Heq as -> _ _; contradiction |].
    right. apply IH; auto.
Qed.

Lemma hcy5_p12_r_focus (A B C: mpred) : A = (B * C)%logic -> A |-- (B * (B -* A))%logic.
Proof.
  intros ->. apply sepcon_derives; [apply derives_refl |].
  apply (proj1 (wand_sepcon_adjoint _ _ _)). rewrite sepcon_comm. apply derives_refl.
Qed.

(* ---------------------------------------------------------------------- *)
(* The peers: the cookie bytes of one peer                                 *)
(* ---------------------------------------------------------------------- *)

Lemma hcy5_p12_r_pfocus PS x :
  In x PS -> peers_rep PS |-- (peer_item_rep x * (peer_item_rep x -* peers_rep PS))%logic.
Proof.
  unfold peers_rep. induction PS as [| y PS IH]; intros Hin; [contradiction |].
  simpl iter_sepcon. destruct Hin as [-> | Hin].
  - cancel. apply (proj1 (wand_sepcon_adjoint _ _ _)). rewrite sepcon_comm. apply derives_refl.
  - sep_apply (IH Hin). cancel.
    apply (proj1 (wand_sepcon_adjoint _ _ _)).
    sep_apply (modus_ponens_wand (peer_item_rep x) (iter_sepcon peer_item_rep PS)). cancel.
Qed.

Section NoiseCS.
#[local] Existing Instance Noise.CS.
(* a peer without its cookie (Noise.CS) *)
Definition hcy5_p12_r_prest (sh: share) (p: val) (P: peer) : mpred :=
  (!! field_compatible t_peer [] p &&
  (field_at sh t_peer [StructField I._device] (p_device P) p *
   field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   field_at sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   field_at sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   field_at sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   field_at sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p))%logic.

Lemma hcy5_p12_r_peer_split sh p P :
  peer_rep sh p P = (hcy5_p12_r_prest sh p P * cookie_rep sh (cookie_addr p) (p_cookie P))%logic.
Proof.
  unfold peer_rep, hcy5_p12_r_prest. apply pred_ext.
  - Intros. entailer!.
  - Intros. entailer!.
Qed.
End NoiseCS.

#[local] Instance hcy5_p12_r_cce_N : change_composite_env Noise.CS W_cookie_reply.
Proof. make_cs_preserve Noise.CS W_cookie_reply. Defined.

Lemma hcy5_p12_r_test sh p v :
  field_compatible t_peer [] p ->
  data_at sh t_cookie v (cookie_addr p) = field_at sh t_peer (DOT HY._latest_cookie) v p.
Proof.
  intros Hfc.
  rewrite field_at_data_at. f_equal.
  rewrite field_address_offset by auto with field_compatible. reflexivity.
Qed.

(* the cookie of the peer at W: the cookie bytes (offset 369) apart *)
Definition hcy5_p12_r_ckrest (sh: share) (p: val) (C: cookie) (lk: val) : mpred :=
  (field_at sh t_peer (DOT HY._latest_cookie DOT HY._birthdate) (Vlong (ck_birth C)) p *
   field_at sh t_peer (DOT HY._latest_cookie DOT HY._is_valid) (Val.of_bool (ck_valid C)) p *
   field_at sh t_peer (DOT HY._latest_cookie DOT HY._have_sent_mac1) (Val.of_bool (ck_sent C)) p *
   field_at sh t_peer (DOT HY._latest_cookie DOT HY._last_mac1_sent) (bytes (ck_last_mac1 C)) p *
   field_at sh t_peer (DOT HY._latest_cookie DOT HY._cookie_decryption_key) (bytes (ck_dkey C)) p *
   field_at sh t_peer (DOT HY._latest_cookie DOT HY._message_mac1_key) (bytes (ck_mkey C)) p *
   spacer sh 466 468 p *
   field_at sh t_peer (DOT HY._latest_cookie DOT HY._lock) lk p)%logic.

Lemma hcy5_p12_r_ck_open sh p C lk :
  @field_compatible Noise.CS t_peer [] p ->
  @data_at Noise.CS sh t_cookie (cookie_val C lk) (cookie_addr p) =
  (data_at sh (tarray tuchar 16) (bytes (ck_cookie C)) (offset_val 369 p) *
   hcy5_p12_r_ckrest sh p C lk)%logic.
Proof.
  intros Hfc0.
  assert (Hfc: field_compatible t_peer [] p).
  { revert Hfc0. apply field_compatible_change_composite. reflexivity. }
  rewrite (@data_at_change_composite Noise.CS W_cookie_reply _ sh t_cookie (cookie_val C lk) (cookie_val C lk)
             (JMeq_refl _)) by prove_cs_preserve_type.
  rewrite hcy5_p12_r_test by auto.
  unfold_field_at 1%nat.
  rewrite (field_at_data_at sh t_peer (DOT HY._latest_cookie DOT HY._cookie)).
  rewrite !field_address_offset by auto with field_compatible.
  unfold hcy5_p12_r_ckrest. simpl. apply pred_ext; cancel.
Qed.

Lemma hcy5_p12_r_peer_ck sh p P :
  peer_rep sh p P |--
  (!! (isptr p /\ Zlength (ck_cookie (p_cookie P)) = 16) &&
   (hbytes sh (ck_cookie (p_cookie P)) (offset_val 369 p) *
    (hbytes sh (ck_cookie (p_cookie P)) (offset_val 369 p) -* peer_rep sh p P)))%logic.
Proof.
  rewrite hcy5_p12_r_peer_split.
  assert_PROP (@field_compatible Noise.CS t_peer [] p) as Hfc.
  { unfold hcy5_p12_r_prest. entailer!. }
  unfold cookie_rep. Intros lk.
  assert (Hl: Zlength (ck_cookie (p_cookie P)) = 16) by apply H.
  rewrite (hcy5_p12_r_ck_open sh p (p_cookie P) lk Hfc).
  apply andp_right.
  { apply prop_right. split; [destruct Hfc; auto | exact Hl]. }
  unfold hbytes. rewrite Hl. rewrite (@data_at_tarray_tuchar_cs HCS W_cookie_reply).
  cancel. apply (proj1 (wand_sepcon_adjoint _ _ _)).
  Exists lk. rewrite (hcy5_p12_r_ck_open sh p (p_cookie P) lk Hfc). entailer!.
Qed.

Lemma hcy5_p12_r_peers_ck PS a sh P :
  In (a, sh, P) PS ->
  peers_rep PS |--
  (!! (isptr a /\ Zlength (ck_cookie (p_cookie P)) = 16) &&
   (hbytes sh (ck_cookie (p_cookie P)) (offset_val 369 a) *
    (hbytes sh (ck_cookie (p_cookie P)) (offset_val 369 a) -* peers_rep PS)))%logic.
Proof.
  intros Hin. sep_apply (hcy5_p12_r_pfocus PS (a, sh, P) Hin). simpl peer_item_rep.
  sep_apply (hcy5_p12_r_peer_ck sh a P). Intros. apply andp_right; [apply prop_right; auto |].
  cancel. apply (proj1 (wand_sepcon_adjoint _ _ _)).
  sep_apply (modus_ponens_wand (hbytes sh (ck_cookie (p_cookie P)) (offset_val 369 a)) (peer_rep sh a P)).
  sep_apply (modus_ponens_wand (peer_rep sh a P) (peers_rep PS)). cancel.
Qed.

(* ---------------------------------------------------------------------- *)
(* The nodes: field p of the node N                                        *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hcy5_p12_r_cce_K : change_composite_env CKS W_cookie_reply.
Proof. make_cs_preserve CKS W_cookie_reply. Defined.

Lemma hcy5_p12_r_wand_frame (A B C F: mpred) : (A * B |-- C -> A * (F * (F -* B)) |-- F * (F -* C))%logic.
Proof.
  intros H. rewrite <- sepcon_assoc, (sepcon_comm A F), sepcon_assoc.
  apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint. eapply derives_trans; [| exact H].
  rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl |].
  rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hcy5_p12_r_node1 (N: hnode4) nx :
  (@data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N) |--
  @field_at W_cookie_reply Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) *
  (@field_at W_cookie_reply Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) -*
   @data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N)))%logic.
Proof.
  rewrite (@data_at_change_composite CKS W_cookie_reply _ Ews t_hnode4 _ _ (JMeq_refl _)) by prove_cs_preserve_type.
  unfold_data_at (@data_at W_cookie_reply Ews t_hnode4 _ (hn_addr N)).
  apply sepcon_derives; [apply derives_refl | apply wand_frame_intro].
Qed.

Lemma hcy5_p12_r_node h NS N v :
  In N NS -> hn_p N = v ->
  (hnodes_rep4 W_cookie_reply h NS |--
  @field_at W_cookie_reply Ews t_hnode4 (DOT HY._p) v (hn_addr N) *
  (@field_at W_cookie_reply Ews t_hnode4 (DOT HY._p) v (hn_addr N) -* hnodes_rep4 W_cookie_reply h NS))%logic.
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
    + sep_apply (hcy5_p12_r_node1 N nx). cancel.
    + apply hcy5_p12_r_wand_frame. Exists nx. entailer!.
  - simpl hnodes_rep4. Intros nx. subst h.
    apply derives_trans with
      (@malloc_token W_cookie_reply Ews t_hnode4 (hn_addr N0) *
       @data_at CKS Ews t_hnode4 (hn_p N0, (hn_snap N0, (hn_refs N0, (hn_rest N0, nx)))) (hn_addr N0) *
       @malloc_token W_cookie_reply Ews t_peer (hn_p N0) *
       (@field_at W_cookie_reply Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) *
        (@field_at W_cookie_reply Ews t_hnode4 (DOT HY._p) (hn_p N) (hn_addr N) -* hnodes_rep4 W_cookie_reply nx NS)))%logic.
    + sep_apply (IH Hin nx). cancel.
    + apply hcy5_p12_r_wand_frame. Exists nx. entailer!.
Qed.

Lemma hcy5_p12_r_node_ptr l NS N :
  In N NS -> hnodes_rep4 W_cookie_reply l NS |-- !! isptr (hn_addr N).
Proof.
  intros Hin. sep_apply (hcy5_p12_r_node l NS N (hn_p N) Hin eq_refl). entailer!.
Qed.

Lemma hcy5_p12_r_hsz : sizeof (nested_field_type t_hnode4 (DOT HY._p)) > 0.
Proof. vm_compute. reflexivity. Qed.

Lemma hcy5_p12_r_node_valid l NS N :
  In N NS -> hnodes_rep4 W_cookie_reply l NS |-- valid_pointer (hn_addr N).
Proof.
  intros Hin. sep_apply (hcy5_p12_r_node l NS N (hn_p N) Hin eq_refl).
  apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; [apply readable_nonidentity; auto | apply hcy5_p12_r_hsz | reflexivity].
Qed.

(* ---------------------------------------------------------------------- *)
(* The cnodes: field n of the cnode c                                      *)
(* ---------------------------------------------------------------------- *)

Lemma hcy5_p12_r_cn l CL c nd o :
  In (c, nd, o) CL ->
  hcy5_cns l CL |--
  (field_at Ews t_cnode5 (DOT HY._n) nd c * (field_at Ews t_cnode5 (DOT HY._n) nd c -* hcy5_cns l CL))%logic.
Proof.
  revert l; induction CL as [| [[c1 nd1] o1] CL IH]; intros l Hin; [contradiction |].
  simpl hcy5_cns. Intros. subst l.
  destruct Hin as [Heq | Hin].
  - inv Heq. cancel. apply (proj1 (wand_sepcon_adjoint _ _ _)). entailer!.
  - sep_apply (IH (hcy5_chead CL) Hin). cancel.
    apply (proj1 (wand_sepcon_adjoint _ _ _)).
    sep_apply (modus_ponens_wand (field_at Ews t_cnode5 (DOT HY._n) nd c) (hcy5_cns (hcy5_chead CL) CL)).
    entailer!.
Qed.

Lemma hcy5_p12_r_cn_ptr l CL c nd o :
  In (c, nd, o) CL -> hcy5_cns l CL |-- !! isptr c.
Proof.
  intros Hin. sep_apply (hcy5_p12_r_cn l CL c nd o Hin). entailer!.
Qed.

Lemma hcy5_p12_r_csz : sizeof (nested_field_type t_cnode5 (DOT HY._n)) > 0.
Proof. vm_compute. reflexivity. Qed.

Lemma hcy5_p12_r_cn_valid l CL c nd o :
  In (c, nd, o) CL -> hcy5_cns l CL |-- valid_pointer c.
Proof.
  intros Hin. sep_apply (hcy5_p12_r_cn l CL c nd o Hin).
  apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; [apply readable_nonidentity; auto | apply hcy5_p12_r_csz | reflexivity].
Qed.

(* ---------------------------------------------------------------------- *)
(* The round trip, pure part: the statement of hcy5_p12_rt_ok (hcy5_p12_rt.v), *)
(* (a copy of its proof)                                                  *)
(* ---------------------------------------------------------------------- *)

Lemma hcy5_p12_r_rt_nodup_inj {A B: Type} (f: A -> B) (l: list A) x y :
  NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|z l IH]; simpl; intros Hnd Hx Hy Hf; [contradiction|].
  inversion Hnd as [|? ? Hnin Hnd']; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; auto.
  - exfalso. apply Hnin. rewrite Hf. apply in_map. exact Hy.
  - exfalso. apply Hnin. rewrite <- Hf. apply in_map. exact Hx.
Qed.

Lemma hcy5_p12_r_rt_combine_map {A B C: Type} (f: A -> C) (g: B -> C) (l1: list A) (l2: list B) x y :
  In (x, y) (combine l1 l2) -> map f l1 = map g l2 -> f x = g y.
Proof.
  revert l2; induction l1 as [|z l1 IH]; intros [|w l2]; simpl; intros Hin Hm; try contradiction.
  inversion Hm as [[Hzw Hm']].
  destruct Hin as [Heq|Hin].
  - inversion Heq; subst. exact Hzw.
  - apply (IH l2); auto.
Qed.

Lemma hcy5_p12_r_rt_sfind {A: Type} (PS: list (val * share * A)) a sh P :
  NoDup (map (fun '(x, _, _) => x) PS) -> In (a, sh, P) PS -> sfind PS a = Some (sh, P).
Proof.
  induction PS as [|[[x sh'] w] PS IH]; simpl; intros Hnd Hin; [contradiction|].
  inversion Hnd as [|? ? Hnin Hnd']; subst.
  destruct Hin as [Heq|Hin].
  - inversion Heq; subst. destruct (EqDec_val a a); [reflexivity | congruence].
  - destruct (EqDec_val x a) as [->|Hne].
    + exfalso. apply Hnin. change a with ((fun '(x, _, _) => x) (a, sh, P)). apply in_map. exact Hin.
    + apply IH; auto.
Qed.

Lemma hcy5_p12_r_rt_find_index (T: tstate) (L: list val) x E :
  NoDup (t_indices T L) -> In x L -> t_entry T x = Some E -> t_find_index T L (e_index E) = Some (x, E).
Proof.
  induction L as [|y L IH]; simpl; intros Hnd Hin HE; [contradiction|].
  unfold t_indices in Hnd; simpl in Hnd. inversion Hnd as [|? ? Hnin Hnd']; subst.
  destruct Hin as [<-|Hin].
  - rewrite HE. rewrite Int.eq_true. reflexivity.
  - destruct (t_entry T y) as [E'|] eqn:HE'.
    + destruct (Int.eq (e_index E') (e_index E)) eqn:Hq.
      * exfalso. apply Int.same_if_eq in Hq. apply Hnin. rewrite Hq.
        apply (in_map (fun a => match t_entry T a with Some E => e_index E | None => Int.zero end)) in Hin.
        rewrite HE in Hin. exact Hin.
      * apply IH; auto.
    + apply IH; auto.
Qed.

(* the first cnode whose node's peer is a has node address np *)
Lemma hcy5_p12_r_rt_cfind (NS: list hnode4) (CL: list (val * val * option cookie)) (a np: val) :
  (forall c nd o, In (c, nd, o) CL -> hcy5_nodepeer NS nd = a -> nd = np) ->
  hcy5_nodepeer NS np = a ->
  In np (map (fun x => snd (fst x)) CL) ->
  exists o, In (hcy5_cfind NS CL a, np, o) CL.
Proof.
  induction CL as [|[[c nd] o] CL IH]; simpl; intros Hall Hnp Hin; [contradiction|].
  destruct (EqDec_val (hcy5_nodepeer NS nd) a) as [Heq|Hne].
  - rewrite (Hall c nd o (or_introl eq_refl) Heq). exists o. left. reflexivity.
  - destruct Hin as [Hin|Hin].
    + subst nd. contradiction.
    + destruct (IH (fun c' nd' o' H => Hall c' nd' o' (or_intror H)) Hnp Hin) as [o' Ho'].
      exists o'. right. exact Ho'.
Qed.

(* the peer of a node address *)
Lemma hcy5_p12_r_rt_nodepeer (NS: list hnode4) nd :
  In nd (map hn_addr NS) -> exists N', In N' NS /\ hn_addr N' = nd /\ hcy5_nodepeer NS nd = hn_p N'.
Proof.
  intros Hin. unfold hcy5_nodepeer.
  destruct (find (fun N => if eq_dec (hn_addr N) nd then true else false) NS) as [N'|] eqn:Hf.
  - apply find_some in Hf. destruct Hf as [HN' Hf].
    match type of Hf with context [if ?d then _ else _] => destruct d as [He|]; [|discriminate] end.
    exists N'. auto.
  - exfalso. apply in_map_iff in Hin. destruct Hin as [N'' [He HN'']].
    pose proof (find_none _ _ Hf N'' HN'') as Hc. simpl in Hc.
    match type of Hc with context [if ?d then _ else _] => destruct d; [discriminate | contradiction] end.
Qed.

Lemma hcy5_p12_r_rt x25519 aead_enc aead_dec xaead_enc xaead_dec R L Q m nonce rr CK CM NS PS T np CL KE CM' now2 :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hcy5_p12_inv x25519 xaead_enc R L Q m nonce rr CK CM NS PS T np CL KE CM' true now2 ->
  mi_ok (hcy5_IB x25519 R) = true ->
  exists N a P o,
    In (N, (a, Ews, P)) (combine NS PS) /\ hn_addr N = np /\ hn_p N = a /\
    hcy5_res xaead_dec T PS CM' now2 =
      Some (a, p_set_cookie P (mkCookie now2 true CK false (ck_last_mac1 (p_cookie P)) (ck_dkey (p_cookie P))
                                        (ck_mkey (p_cookie P)))) /\
    In (hcy5_tgt NS CL (hcy5_res xaead_dec T PS CM' now2), np, o) CL.
Proof.
  intros [_ [_ Hxa]] (Hrep & Hlists & _ & HT & Hcl & _ & _ & Hhon & _) Hmi.
  destruct (Hhon eq_refl) as (N & a & P & HIn & HNnp & Hrs & Hsent & Hmac & Hent & HinL & Hnonce & Henc).
  clear Hhon.
  destruct Hlists as (Hpok & Hpeers & HndP & HndN & _).
  destruct HT as (_ & HndI).
  destruct Hrep as (_ & _ & _ & _ & _ & HCM).
  unfold hcy5_is in HCM.
  assert (HNa: hn_p N = a) by exact (hcy5_p12_r_rt_combine_map hn_p peer_addr4 NS PS N (a, Ews, P) HIn Hpeers).
  assert (HinN: In N NS) by (eapply in_combine_l; eauto).
  assert (HinP: In (a, Ews, P) PS) by (eapply in_combine_r; eauto).
  (* the lookup finds P's handshake entry *)
  assert (Hlk: t_lookup T (Int.or IDX_HANDSHAKE IDX_KEYPAIR) (cm_receiver CM') =
               Some (hs_addr a, mkEntry a IDX_HANDSHAKE (cm_receiver CM'))).
  { unfold t_lookup.
    pose proof (hcy5_p12_r_rt_find_index T (t_L T) (hs_addr a) _ HndI HinL Hent) as Hf.
    cbn [e_index] in Hf. rewrite Hf. cbn [e_type].
    assert (Hz: Int.eq (Int.and IDX_HANDSHAKE (Int.or IDX_HANDSHAKE IDX_KEYPAIR)) Int.zero = false)
      by (vm_compute; reflexivity).
    rewrite Hz. reflexivity. }
  assert (Hsf: sfind PS a = Some (Ews, P)) by (apply hcy5_p12_r_rt_sfind; [exact HndP | exact HinP]).
  (* P's cookie key is B's cookie encryption key *)
  assert (Hdk: ck_dkey (p_cookie P) = label_key cookie_label (hs_rstatic (p_hs P))).
  { rewrite Forall_forall in Hpok. specialize (Hpok _ HinP). unfold hcy5_pok in Hpok.
    destruct Hpok as (_ & _ & _ & _ & Hd & _). exact Hd. }
  assert (Hhas: id_has (setup_identity x25519 (r_rawb R)) = true) by exact Hmi.
  assert (Hek: cc_ekey (hcy5_CC1 x25519 R L) = label_key cookie_label (hcy5_pubB x25519 R L)).
  { unfold hcy5_CC1, hcy5_pubB, hcy5_DB, setup_dev. cbn [cc_ekey d_cc d_id].
    unfold checker_keys. rewrite Hhas. reflexivity. }
  assert (Hdec: xaead_dec (ck_dkey (p_cookie P)) (cm_nonce CM') (ck_last_mac1 (p_cookie P)) (cm_enc CM') = Some CK).
  { rewrite Hnonce, Henc, Hmac, Hdk, Hrs, HCM. unfold hcy5_CM. cbn [cm_nonce cm_enc].
    rewrite Hek. apply (xaead_dec_enc _ _ Hxa). }
  assert (Hres: hcy5_res xaead_dec T PS CM' now2 =
      Some (a, p_set_cookie P (mkCookie now2 true CK false (ck_last_mac1 (p_cookie P)) (ck_dkey (p_cookie P))
                                        (ck_mkey (p_cookie P))))).
  { unfold hcy5_res, message_consume_model. rewrite Hlk. cbv beta iota zeta. cbn [e_peer].
    rewrite Hsf. cbv beta iota zeta. rewrite Hsent. cbn [negb]. rewrite Hdec. reflexivity. }
  (* the target is the cnode of np *)
  assert (HndPN: NoDup (map hn_p NS)) by (rewrite Hpeers; exact HndP).
  destruct Hcl as [Hcl _].
  assert (Hnp: hcy5_nodepeer NS np = a).
  { assert (Hin: In np (map hn_addr NS)) by (rewrite <- HNnp; apply in_map; exact HinN).
    destruct (hcy5_p12_r_rt_nodepeer NS np Hin) as (N' & HN' & HaN' & Hpe).
    rewrite Hpe. rewrite (hcy5_p12_r_rt_nodup_inj hn_addr NS N' N HndN HN' HinN); [exact HNa | congruence]. }
  assert (Hall: forall c nd o, In (c, nd, o) CL -> hcy5_nodepeer NS nd = a -> nd = np).
  { intros c nd o Hin Hpe.
    apply (in_map (fun x => snd (fst x))) in Hin. cbn in Hin. rewrite Hcl, <- in_rev in Hin.
    destruct (hcy5_p12_r_rt_nodepeer NS nd Hin) as (N' & HN' & HaN' & Hpe').
    rewrite Hpe' in Hpe.
    rewrite <- HaN', <- HNnp. f_equal.
    apply (hcy5_p12_r_rt_nodup_inj hn_p NS N' N HndPN HN' HinN). congruence. }
  assert (Hinnp: In np (map (fun x => snd (fst x)) CL)).
  { rewrite Hcl, <- in_rev, <- HNnp. apply in_map. exact HinN. }
  destruct (hcy5_p12_r_rt_cfind NS CL a np Hall Hnp Hinnp) as [o Ho].
  exists N, a, P, o.
  split; [exact HIn|]. split; [exact HNnp|]. split; [exact HNa|]. split; [exact Hres|].
  rewrite Hres. exact Ho.
Qed.

(* B's model identity at the world *)
#[local] Instance hcy5_p12_r_cce_H : change_composite_env HCS W_cookie_reply.
Proof. make_cs_preserve HCS W_cookie_reply. Defined.

Lemma hcy5_p12_r_mident_W sh I p :
  @data_at HCS sh t_mident (mident_val I) p = @data_at W_cookie_reply sh t_mident (mident_val I) p.
Proof.
  assert (E := @data_at_change_composite HCS W_cookie_reply hcy5_p12_r_cce_H sh t_mident (mident_val I)
                 (mident_val I) (JMeq_refl _)).
  rewrite E; [reflexivity | prove_cs_preserve_type].
Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_p12_R_ok {Espec: OracleKind} gv L FR R S m c rp Q nonce rr CK CM NS PS T np CL KE CM' honest now2 :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hcy5_p12_inv x25519 xaead_enc R L Q m nonce rr CK CM NS PS T np CL KE CM' honest now2 ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hcy5_p12_St x25519 xaead_dec gv L FR R S m c rp Q rr CK NS PS T np CL KE CM' honest now2)
    hcy5_p12_s75
    (normal_ret_assert (hcy5_p12_St x25519 xaead_dec gv L FR R S m c rp Q rr CK NS PS T np CL KE CM' honest now2)).
Proof.
  intros HH Hinv.
  pose proof Hinv as (Hrep & Hlists & Hnp & HT & Hcl & Hsnap & Hcm & Hhon & Hnow).
  unfold hcy5_p12_St, hcy5_Delta. simplify_func_tycontext. abbreviate_semax.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_lvars; cbn [app].
  unfold hcy5_p12_s75.
  set (res := hcy5_res xaead_dec T PS CM' now2) in *.
  set (tg := hcy5_tgt NS CL res) in *.
  set (NS' := hnodes_snapped4 T NS PS) in *.
  destruct honest.
  - (* honest *)
    destruct (mi_ok (hcy5_IB x25519 R)) eqn:Eok.
    + (* B has an identity: the round trip *)
      destruct (hcy5_p12_r_rt x25519 aead_enc aead_dec xaead_enc xaead_dec R L Q m nonce rr CK CM NS PS T np CL KE
                  CM' now2 HH Hinv Eok) as (N & a & P & o & Hin & HNa & HNp & Hres & Hcl0).
      fold res in Hres, Hcl0. fold tg in Hcl0.
      destruct Hlists as (Hpok & Hnps & Hndp & Hndn & _).
      destruct (hcy5_p12_r_pos NS PS N (a, Ews, P) Hin Hnps) as (HinN & HinP & _).
      destruct (hcy5_p12_r_snap T NS PS N (a, Ews, P) Hin) as (N' & HN'in & HN'a & HN'p).
      match type of Hres with _ = Some (_, ?X) => set (P' := X) in Hres end.
      assert (HinA: In (a, Ews, P') (peers_after PS res)).
      { rewrite Hres. cbn [peers_after]. eapply hcy5_p12_r_supd_in; eauto. }
      assert (HCK: ck_cookie (p_cookie P') = CK) by reflexivity.
      clearbody P'.
      assert (VPnp: hnodes_rep4 W (hcy5_head NS') NS' |-- valid_pointer np)
        by (rewrite <- HNa, <- HN'a; apply hcy5_p12_r_node_valid; exact HN'in).
      assert (VPtg: hcy5_cns (hcy5_chead CL) CL |-- valid_pointer tg) by (eapply hcy5_p12_r_cn_valid; eauto).
      assert_PROP (isptr np) as Hnpp.
      { rewrite <- HNa, <- HN'a. sep_apply (hcy5_p12_r_node_ptr (hcy5_head NS') NS' N' HN'in). entailer!. }
      assert_PROP (isptr tg) as Htgp.
      { sep_apply (hcy5_p12_r_cn_ptr (hcy5_chead CL) CL tg np o Hcl0). entailer!. }
      match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
        forward_if (PROPx P (LOCALx (temp HY._t'77 (Vint Int.one) :: Lc) (SEPx Sp))) end.
      { forward. entailer!.
        match goal with H: isptr ?p |- context [sem_cmp_pp Cne ?p _] =>
          destruct p; try contradiction; reflexivity end. }
      { exfalso. exact (Int.one_not_zero H). }
      match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
        forward_if (PROPx P (LOCALx (temp HY._t'78 (Vint Int.one) :: Lc) (SEPx Sp))) end.
      2: { exfalso. exact (Int.one_not_zero H). }
      { rewrite hcy5_p12_r_mident_W. forward. rewrite <- hcy5_p12_r_mident_W.
        match goal with |- context [temp HY._t'82 ?v] =>
          replace v with (Vint Int.one) by (unfold mident_val; cbv beta iota; rewrite Eok; reflexivity) end.
        forward. entailer!. }
      forward_if.
      2: { exfalso. exact (Int.one_not_zero H). }
      (* CHECK(target != NULL && target->n == np) *)
      match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
      { apply ENTAIL_refl. }
      { match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
          forward_if (PROPx P (LOCALx (temp HY._t'75 (Vint Int.one) :: Lc) (SEPx Sp))) end.
        { sep_apply (hcy5_p12_r_cn (hcy5_chead CL) CL tg np o Hcl0). Intros.
          forward. forward.
          sep_apply (modus_ponens_wand (field_at Ews t_cnode5 (DOT HY._n) np tg) (hcy5_cns (hcy5_chead CL) CL)).
          entailer!. destruct (eq_dec (hn_addr N) (hn_addr N)); [reflexivity | contradiction]. }
        { exfalso. rewrite H0 in Htgp. exact Htgp. }
        forward_if.
        { exfalso. match goal with Hx: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hx) end. }
        forward. entailer!. }
      { forward. entailer!. }
      (* CHECK(bytes_eq(np->p->latest_cookie.cookie, cookie, 16)) *)
      match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
      { apply ENTAIL_refl. }
      { sep_apply (hcy5_p12_r_peers_ck (peers_after PS res) a Ews P' HinA). Intros.
        rewrite HCK in *.
        assert (HnpN: hn_addr N' = np) by congruence. assert (HpN: hn_p N' = a) by congruence.
        sep_apply (hcy5_p12_r_node (hcy5_head NS') NS' N' a HN'in HpN). rewrite HnpN. Intros.
        forward.
        forward_call (Ews, offset_val 369 a, CK, Tsh, l_cookie L, CK).
        { entailer!.
          match goal with Hz: Zlength _ = 16 |- _ => rewrite Hz end.
          match goal with Hp: isptr ?p |- context [offset_val 369 ?p] => destruct p; try contradiction end.
          simpl. rewrite Ptrofs.add_assoc. reflexivity. }
        rewrite hcy5_p12_r_eqb_refl.
        forward_if.
        { exfalso. match goal with Hx: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hx) end. }
        forward.
        sep_apply (modus_ponens_wand (field_at Ews t_hnode4 (DOT HY._p) a np) (hnodes_rep4 W (hcy5_head NS') NS')).
        sep_apply (modus_ponens_wand (hbytes Ews CK (offset_val 369 a)) (peers_rep (peers_after PS res))).
        entailer!. }
      { forward. entailer!. }
      unfold POSTCONDITION, abbreviate.
      match goal with |- context [RA_normal (normal_ret_assert ?X)] =>
        change (RA_normal (normal_ret_assert X)) with X end.
      unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_lvars; cbn [app].
      entailer!.
    + (* no identity *)
      destruct (Hhon eq_refl) as (N & a & P & Hin & HNa & _).
      destruct (hcy5_p12_r_snap T NS PS N (a, Ews, P) Hin) as (N' & HN'in & HN'a & HN'p).
      assert (VPnp: hnodes_rep4 W (hcy5_head NS') NS' |-- valid_pointer np)
        by (rewrite <- HNa, <- HN'a; apply hcy5_p12_r_node_valid; exact HN'in).
      assert_PROP (isptr np) as Hnpp.
      { rewrite <- HNa, <- HN'a. sep_apply (hcy5_p12_r_node_ptr (hcy5_head NS') NS' N' HN'in). entailer!. }
      match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
        forward_if (PROPx P (LOCALx (temp HY._t'77 (Vint Int.one) :: Lc) (SEPx Sp))) end.
      { forward. entailer!.
        match goal with H: isptr ?p |- context [sem_cmp_pp Cne ?p _] =>
          destruct p; try contradiction; reflexivity end. }
      { exfalso. exact (Int.one_not_zero H). }
      match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
        forward_if (PROPx P (LOCALx (temp HY._t'78 (Vint Int.zero) :: Lc) (SEPx Sp))) end.
      2: { exfalso. exact (Int.one_not_zero H). }
      rewrite hcy5_p12_r_mident_W. forward. rewrite <- hcy5_p12_r_mident_W.
      match goal with |- context [temp HY._t'82 ?v] =>
        replace v with (Vint Int.zero) by (unfold mident_val; cbv beta iota; rewrite Eok; reflexivity) end.
      forward. entailer!.
      forward_if.
      { exfalso. apply H. reflexivity. }
      unfold POSTCONDITION, abbreviate.
      unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_lvars; cbn [app].
      forward.
      entailer!.
  - (* not honest *)
    match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HY._t'77 (Vint Int.zero) :: Lc) (SEPx Sp))) end.
    { exfalso. apply H. reflexivity. }
    { forward. entailer!. }
    match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HY._t'78 (Vint Int.zero) :: Lc) (SEPx Sp))) end.
    { exfalso. apply H. reflexivity. }
    { forward. entailer!. }
    forward_if.
    { exfalso. apply H. reflexivity. }
    unfold POSTCONDITION, abbreviate.
    unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_lvars; cbn [app].
    forward.
    entailer!.
Qed.

End Seg.
