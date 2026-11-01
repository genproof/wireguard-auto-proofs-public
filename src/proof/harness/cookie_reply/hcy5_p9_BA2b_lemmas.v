(* (port of v1 hcy4_p9_BA2b_lemmas.v), law cookie_reply, phase P9, segment BA2b: helpers.
   - the node N of the peer a: its field p alone at W, the rest of the node list behind a wand;
   - the peer a in peers_rep PS, the rest behind a wand that takes the updated peer (supd);
   - the peer's cookie at W: have_sent_mac1 (field_at) and last_mac1_sent (offset 386) apart, the rest
     (the peer without its cookie, the other cookie fields) as one predicate;
   - byte buffers: the message split in three around its mac1, the pointer msg + len - 32. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p9_defs.
Require Import WgNoise.proof.libc.libc_bytes.
Require WgNoise.harness.x_cookie_reply.code.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Pure facts                                                              *)
(* ---------------------------------------------------------------------- *)

Lemma hcy5_p9_BA2b_pos NS PS N x :
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

Lemma hcy5_p9_BA2b_phead PS a v : hcy5_phead (supd PS a v) = hcy5_phead PS.
Proof.
  destruct PS as [| [[x sh] w] PS]; simpl; [reflexivity |].
  destruct (EqDec_val x a); reflexivity.
Qed.

Lemma hcy5_p9_BA2b_focus (A B C: mpred) : A = (B * C)%logic -> A |-- (B * (B -* A))%logic.
Proof.
  intros ->. apply sepcon_derives; [apply derives_refl |].
  apply (proj1 (wand_sepcon_adjoint _ _ _)). rewrite sepcon_comm. apply derives_refl.
Qed.

(* ---------------------------------------------------------------------- *)
(* The peers                                                               *)
(* ---------------------------------------------------------------------- *)

Lemma hcy5_p9_BA2b_peers PS a sh P P' :
  NoDup (map peer_addr4 PS) -> In (a, sh, P) PS ->
  peers_rep PS |-- (peer_rep sh a P * (peer_rep sh a P' -* peers_rep (supd PS a P')))%logic.
Proof.
  induction PS as [| [[x shx] w] PS IH]; intros Hnd Hin; [contradiction |].
  simpl in Hnd. inversion Hnd as [| ? ? Hnin Hnd']; subst.
  unfold peers_rep; simpl iter_sepcon. simpl supd. destruct (EqDec_val x a) as [-> | Hne].
  - destruct Hin as [Heq | Hin].
    + injection Heq as -> ->. simpl. cancel. apply (proj1 (wand_sepcon_adjoint _ _ _)). simpl. cancel.
    + exfalso. apply Hnin. apply (in_map peer_addr4) in Hin. exact Hin.
  - destruct Hin as [Heq | Hin]; [injection Heq as -> _ _; contradiction |].
    change (iter_sepcon peer_item_rep PS) with (peers_rep PS).
    sep_apply (IH Hnd' Hin). simpl iter_sepcon.
    change (iter_sepcon peer_item_rep (supd PS a P')) with (peers_rep (supd PS a P')).
    rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl |].
    apply (proj1 (wand_sepcon_adjoint _ _ _)).
    sep_apply (modus_ponens_wand (peer_rep sh a P') (peers_rep (supd PS a P'))). cancel.
Qed.

(* a peer without its cookie (Noise.CS) *)
Section NoiseCS.
#[local] Existing Instance Noise.CS.
Definition hcy5_p9_BA2b_prest (sh: share) (p: val) (P: peer) : mpred :=
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

Lemma hcy5_p9_BA2b_peer_split sh p P :
  peer_rep sh p P = (hcy5_p9_BA2b_prest sh p P * cookie_rep sh (cookie_addr p) (p_cookie P))%logic.
Proof.
  unfold peer_rep, hcy5_p9_BA2b_prest. apply pred_ext.
  - Intros. entailer!.
  - Intros. entailer!.
Qed.

Lemma hcy5_p9_BA2b_peer_fold sh p P C :
  (hcy5_p9_BA2b_prest sh p P * cookie_rep sh (cookie_addr p) C)%logic |-- peer_rep sh p (p_set_cookie P C).
Proof.
  unfold peer_rep, hcy5_p9_BA2b_prest, p_set_cookie.
  cbn [p_device p_dead p_cur p_prev p_next p_hs p_lsh p_cookie p_refs p_id p_pknext].
  Intros. entailer!.
Qed.
End NoiseCS.

(* ---------------------------------------------------------------------- *)
(* At the world                                                            *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hcy5_p9_BA2b_cce_HN : change_composite_env CKS W_cookie_reply.
Proof. make_cs_preserve CKS W_cookie_reply. Defined.

#[local] Instance hcy5_p9_BA2b_cce_N : change_composite_env Noise.CS W_cookie_reply.
Proof. make_cs_preserve Noise.CS W_cookie_reply. Defined.

Section W.
#[local] Existing Instance W_cookie_reply.

(* the node: its field p *)
Lemma hcy5_p9_BA2b_node1 l p s r rs nx :
  @data_at CKS Ews t_hnode4 (p, (s, (r, (rs, nx)))) l |--
  (field_at Ews t_hnode4 (DOT HC._p) p l *
   (field_at Ews t_hnode4 (DOT HC._p) p l -* @data_at CKS Ews t_hnode4 (p, (s, (r, (rs, nx)))) l))%logic.
Proof.
  (* not unfold_data_at: the hnode's snapshot makes it time out *)
  rewrite <- (@field_at_change_composite CKS W_cookie_reply _ Ews t_hnode4 [StructField HC._p] p p (JMeq_refl p))
    by (vm_compute; reflexivity).
  eapply derives_trans; [apply andp_right; [apply (@data_at_local_facts CKS) | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  (eapply derives_trans; [apply (@gfield_ramif CKS Ews t_hnode4 [] (StructField HC._p) _ p l);
     [apply JMeq_refl | auto with field_compatible] |]).
  apply sepcon_derives; [apply derives_refl|].
  apply (allp_left _ p).
  apply derives_refl.
Qed.

(* accessors P |-- Q * (Q -* P) (as hci5_P6's; entailer! on the nodes is slow) *)
Definition hcy5_p9_BA2b_acc (Q P: mpred) : Prop := (P |-- Q * (Q -* P))%logic.

Lemma hcy5_p9_BA2b_acc_l Q A F : hcy5_p9_BA2b_acc Q A -> hcy5_p9_BA2b_acc Q (A * F)%logic.
Proof.
  unfold hcy5_p9_BA2b_acc. intros H. apply derives_trans with (Q * (Q -* A) * F)%logic.
  { apply sepcon_derives; [exact H | apply derives_refl]. }
  rewrite (sepcon_assoc Q). apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_assoc (Q -* A)), (sepcon_comm F Q), <- (sepcon_assoc (Q -* A)), (sepcon_comm (Q -* A) Q).
  apply sepcon_derives; [apply modus_ponens_wand | apply derives_refl].
Qed.

Lemma hcy5_p9_BA2b_acc_r Q A F : hcy5_p9_BA2b_acc Q A -> hcy5_p9_BA2b_acc Q (F * A)%logic.
Proof. intros H. rewrite sepcon_comm. apply hcy5_p9_BA2b_acc_l, H. Qed.

Lemma hcy5_p9_BA2b_acc_prop Q (c: Prop) A : (c -> hcy5_p9_BA2b_acc Q A) -> hcy5_p9_BA2b_acc Q (!! c && A)%logic.
Proof.
  unfold hcy5_p9_BA2b_acc. intros H. apply derives_extract_prop. intros Hc.
  eapply derives_trans; [apply H, Hc|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. apply andp_right; [apply prop_right, Hc|]. rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hcy5_p9_BA2b_acc_ex {X: Type} Q (A: X -> mpred) :
  (forall x, hcy5_p9_BA2b_acc Q (A x)) -> hcy5_p9_BA2b_acc Q (EX x, A x)%logic.
Proof.
  unfold hcy5_p9_BA2b_acc. intros H. apply exp_left. intros x.
  eapply derives_trans; [apply H|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. eapply derives_trans; [apply modus_ponens_wand|].
  apply (exp_right x), derives_refl.
Qed.

Lemma hcy5_p9_BA2b_node l NS N p :
  In N NS -> hn_p N = p ->
  hnodes_rep4 W_cookie_reply l NS |--
  (field_at Ews t_hnode4 (DOT HC._p) p (hn_addr N) *
   (field_at Ews t_hnode4 (DOT HC._p) p (hn_addr N) -* hnodes_rep4 W_cookie_reply l NS))%logic.
Proof.
  intros Hin <-. change (hcy5_p9_BA2b_acc (field_at Ews t_hnode4 (DOT HC._p) (hn_p N) (hn_addr N))
                                          (hnodes_rep4 W_cookie_reply l NS)).
  revert l; induction NS as [|N0 NS IH]; intros l; [destruct Hin|]. cbn [hnodes_rep4].
  apply hcy5_p9_BA2b_acc_prop; intros Hl. apply hcy5_p9_BA2b_acc_ex; intros nx.
  destruct Hin as [<-|Hin].
  - subst l. apply hcy5_p9_BA2b_acc_l, hcy5_p9_BA2b_acc_l, hcy5_p9_BA2b_acc_r. apply hcy5_p9_BA2b_node1.
  - apply hcy5_p9_BA2b_acc_r, IH, Hin.
Qed.

(* the cookie of the peer p at W *)
Lemma hcy5_p9_BA2b_test sh p v :
  field_compatible t_peer [] p ->
  data_at sh t_cookie v (cookie_addr p) = field_at sh t_peer (DOT HY._latest_cookie) v p.
Proof.
  intros Hfc.
  rewrite field_at_data_at. f_equal.
  rewrite field_address_offset by auto with field_compatible. reflexivity.
Qed.

Definition hcy5_p9_BA2b_ckrest (sh: share) (p: val) (C: cookie) (lk: val) : mpred :=
  (field_at sh t_peer (DOT HY._latest_cookie DOT HY._cookie_decryption_key) (bytes (ck_dkey C)) p *
   field_at sh t_peer (DOT HY._latest_cookie DOT HY._message_mac1_key) (bytes (ck_mkey C)) p *
   spacer sh 466 468 p *
   field_at sh t_peer (DOT HY._latest_cookie DOT HY._lock) lk p)%logic.

Lemma hcy5_p9_BA2b_ck_open sh p C lk :
  @field_compatible Noise.CS t_peer [] p ->
  @data_at Noise.CS sh t_cookie (cookie_val C lk) (cookie_addr p) =
  (field_at sh t_peer (DOT HY._latest_cookie DOT HY._birthdate) (Vlong (ck_birth C)) p *
   field_at sh t_peer (DOT HY._latest_cookie DOT HY._is_valid) (Val.of_bool (ck_valid C)) p *
   data_at sh (tarray tuchar 16) (bytes (ck_cookie C)) (offset_val 369 p) *
   field_at sh t_peer (DOT HY._latest_cookie DOT HY._have_sent_mac1) (Val.of_bool (ck_sent C)) p *
   data_at sh (tarray tuchar 16) (bytes (ck_last_mac1 C)) (offset_val 386 p) *
   hcy5_p9_BA2b_ckrest sh p C lk)%logic.
Proof.
  intros Hfc0.
  assert (Hfc: field_compatible t_peer [] p).
  { revert Hfc0. apply field_compatible_change_composite. reflexivity. }
  rewrite (@data_at_change_composite Noise.CS W_cookie_reply _ sh t_cookie (cookie_val C lk) (cookie_val C lk)
             (JMeq_refl _)) by prove_cs_preserve_type.
  rewrite hcy5_p9_BA2b_test by auto.
  unfold_field_at 1%nat.
  rewrite (field_at_data_at sh t_peer (DOT HY._latest_cookie DOT HY._cookie)).
  rewrite (field_at_data_at sh t_peer (DOT HY._latest_cookie DOT HY._last_mac1_sent)).
  rewrite !field_address_offset by auto with field_compatible.
  unfold hcy5_p9_BA2b_ckrest. simpl. apply pred_ext; cancel.
Qed.

(* the peer at W: everything but have_sent_mac1 and last_mac1_sent *)
Definition hcy5_p9_BA2b_rest (sh: share) (p: val) (P: peer) (lk: val) : mpred :=
  (hcy5_p9_BA2b_prest sh p P *
   field_at sh t_peer (DOT HY._latest_cookie DOT HY._birthdate) (Vlong (ck_birth (p_cookie P))) p *
   field_at sh t_peer (DOT HY._latest_cookie DOT HY._is_valid) (Val.of_bool (ck_valid (p_cookie P))) p *
   data_at sh (tarray tuchar 16) (bytes (ck_cookie (p_cookie P))) (offset_val 369 p) *
   hcy5_p9_BA2b_ckrest sh p (p_cookie P) lk)%logic.

Lemma hcy5_p9_BA2b_peer_open sh p P :
  peer_rep sh p P |--
  EX lk: val, (!! cookie_ok (p_cookie P) &&
  (field_at_ sh t_peer (DOT HY._latest_cookie DOT HY._have_sent_mac1) p *
   hout sh 16 (offset_val 386 p) *
   hcy5_p9_BA2b_rest sh p P lk))%logic.
Proof.
  rewrite hcy5_p9_BA2b_peer_split.
  assert_PROP (@field_compatible Noise.CS t_peer [] p) as Hfc.
  { unfold hcy5_p9_BA2b_prest. entailer!. }
  unfold cookie_rep. Intros lk. Exists lk.
  rewrite (hcy5_p9_BA2b_ck_open sh p (p_cookie P) lk Hfc).
  unfold hcy5_p9_BA2b_rest, hout.
  rewrite <- (@data_at__tarray_tuchar_cs W_cookie_reply HCS).
  sep_apply (field_at_field_at_ sh t_peer (DOT HY._latest_cookie DOT HY._have_sent_mac1)).
  sep_apply (data_at_data_at_ sh (tarray tuchar 16) (bytes (ck_last_mac1 (p_cookie P))) (offset_val 386 p)).
  entailer!.
Qed.

Lemma hcy5_p9_BA2b_peer_close p P lk m1 :
  cookie_ok (p_cookie P) -> Zlength m1 = 16 ->
  (field_at Ews t_peer (DOT HY._latest_cookie DOT HY._have_sent_mac1) (Vint Int.one) p *
   hbytes Ews m1 (offset_val 386 p) *
   hcy5_p9_BA2b_rest Ews p P lk)%logic
  |-- peer_rep Ews p (p_set_cookie P (hcy5_p9_ck (p_cookie P) m1)).
Proof.
  intros Hok Hm1.
  unfold hcy5_p9_BA2b_rest.
  assert_PROP (@field_compatible Noise.CS t_peer [] p) as Hfc.
  { unfold hcy5_p9_BA2b_prest. entailer!. }
  assert (Hok': cookie_ok (hcy5_p9_ck (p_cookie P) m1)).
  { destruct Hok as (L1 & L2 & L3 & L4). unfold cookie_ok, hcy5_p9_ck. cbn [ck_cookie ck_last_mac1 ck_dkey ck_mkey].
    auto. }
  eapply derives_trans; [| apply hcy5_p9_BA2b_peer_fold].
  unfold cookie_rep.
  apply derives_trans with (hcy5_p9_BA2b_prest Ews p P *
    (!! cookie_ok (hcy5_p9_ck (p_cookie P) m1) &&
     @data_at Noise.CS Ews t_cookie (cookie_val (hcy5_p9_ck (p_cookie P) m1) lk) (cookie_addr p)))%logic.
  2: { apply sepcon_derives; [apply derives_refl |].
       apply andp_derives; [apply derives_refl |]. apply (exp_right lk). apply derives_refl. }
  rewrite (hcy5_p9_BA2b_ck_open Ews p (hcy5_p9_ck (p_cookie P) m1) lk Hfc).
  unfold hcy5_p9_ck, hcy5_p9_BA2b_ckrest.
  cbn [ck_birth ck_valid ck_cookie ck_sent ck_last_mac1 ck_dkey ck_mkey].
  change (Val.of_bool true) with (Vint Int.one).
  unfold hbytes. rewrite Hm1. rewrite (@data_at_tarray_tuchar_cs HCS W_cookie_reply).
  entailer!.
Qed.

End W.

(* ---------------------------------------------------------------------- *)
(* Byte buffers (templates hcy5_p5_c_split / _split3 / _fc_shrink / _ptr)  *)
(* ---------------------------------------------------------------------- *)

Section HCSb.
#[local] Existing Instance HCS.

Lemma hcy5_p9_BA2b_split sh l k p : 0 <= k <= Zlength l ->
  field_compatible (tarray tuchar (Zlength l)) [] p ->
  hbytes sh l p = (hbytes sh (sublist 0 k l) p * hbytes sh (sublist k (Zlength l) l) (offset_val k p))%logic.
Proof.
  intros Hk FC. unfold hbytes.
  rewrite (split2_data_at_Tarray_tuchar sh (Zlength l) k) by (unfold bytes; try rewrite Zlength_map; lia).
  rewrite !Zlength_sublist by lia. unfold bytes. rewrite !sublist_map.
  replace (k - 0) with k by lia.
  rewrite field_address0_offset.
  2: { apply field_compatible_field_compatible0 in FC.
       destruct FC as (?&?&?&?&?); repeat split; auto; simpl; lia. }
  simpl. rewrite Z.mul_1_l. reflexivity.
Qed.

Lemma hcy5_p9_BA2b_fc_shrink k n p : 0 <= k <= n ->
  field_compatible (tarray tuchar n) [] p -> field_compatible (tarray tuchar k) [] p.
Proof.
  intros Hk (H1 & H2 & H3 & H4 & H5).
  assert (A: forall (ce: composite_env) z, align_compatible_rec ce (tarray tuchar k) z).
  { intros. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  repeat split; auto.
  - destruct p; try contradiction. unfold size_compatible in *. simpl sizeof in *.
    rewrite Z.max_r in * by lia. lia.
  - destruct p; try contradiction. apply A.
Qed.

Lemma hcy5_p9_BA2b_split3 sh l a b p : 0 <= a <= b -> b <= Zlength l ->
  field_compatible (tarray tuchar (Zlength l)) [] p ->
  hbytes sh l p =
  (hbytes sh (sublist 0 a l) p * hbytes sh (sublist a b l) (offset_val a p) *
   hbytes sh (sublist b (Zlength l) l) (offset_val b p))%logic.
Proof.
  intros Ha Hb FC.
  rewrite (hcy5_p9_BA2b_split sh l b p) by (auto; lia).
  assert (L0: Zlength (sublist 0 b l) = b) by (rewrite Zlength_sublist; lia).
  assert (FC0: field_compatible (tarray tuchar (Zlength (sublist 0 b l))) [] p)
    by (rewrite L0; apply (hcy5_p9_BA2b_fc_shrink _ (Zlength l)); [lia | exact FC]).
  rewrite (hcy5_p9_BA2b_split sh (sublist 0 b l) a p) by (auto; lia).
  rewrite L0, !sublist_sublist by lia. rewrite !Z.add_0_r. reflexivity.
Qed.

Lemma hcy5_p9_BA2b_hbytes_fc sh l p : hbytes sh l p |-- !! field_compatible (tarray tuchar (Zlength l)) [] p.
Proof. unfold hbytes. entailer!. Qed.

End HCSb.

Lemma hcy5_p9_BA2b_ptr i n k : 0 <= n <= Int64.max_unsigned -> 0 <= k <= Int.max_signed ->
  Ptrofs.sub (Ptrofs.add i (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.repr n))))
    (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr k))) =
  Ptrofs.add i (Ptrofs.repr (n - k)).
Proof.
  intros Hn Hk. rewrite !(Ptrofs.mul_commut (Ptrofs.repr 1)), !Ptrofs.mul_one.
  rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc. f_equal.
  unfold Ptrofs.of_ints, Ptrofs.of_int64. rewrite Int.signed_repr by rep_lia.
  rewrite Int64.unsigned_repr by rep_lia.
  rewrite Ptrofs.neg_repr, ptrofs_add_repr. f_equal; lia.
Qed.
