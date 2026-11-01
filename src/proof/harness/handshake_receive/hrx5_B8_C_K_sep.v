(* law handshake_receive, phase B8 branch C, part K: helpers of
   hrx5_B8_C_K.v.  The target node (found by hrx5_nfind, its peer a, its rest = prsnap_val P) focused with a wand on
   its field p or on the three byte arrays of its cookie snapshot rest.cookie the CHECK compares (last_mac1_sent 378,
   cookie_decryption_key 394, message_mac1_key 426); the accepted peer's cookie at the world with explicit fields.
   Ports of hrx5_B4_C_D_sep.v, hrx5_B3_K0_I2_lem.v (v2hrx-K0-I2) and cookie_reply's
   hcy5_p11_C_lemmas.v / hcy5_p11_C.v (v2cr-P11). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require Import WgNoise.proof.libc.libc_bytes.
Require WgNoise.harness.x_handshake_receive.code.
Local Open Scope logic.

Module HRK := WgNoise.harness.x_handshake_receive.code.
Local Notation W := W_handshake_receive.

#[local] Instance hrx5_B8CK_cceK : change_composite_env CKS W_handshake_receive.
Proof. make_cs_preserve CKS W_handshake_receive. Defined.
#[local] Instance hrx5_B8CK_cceN : change_composite_env Noise.CS W_handshake_receive.
Proof. make_cs_preserve Noise.CS W_handshake_receive. Defined.

(* ---------------------------------------------------------------------- *)
(* access: P gives Q and takes it back                                     *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_B8CK_acc (Q P: mpred) : Prop := P |-- Q * (Q -* P).

Lemma hrx5_B8CK_acc_refl Q : hrx5_B8CK_acc Q Q.
Proof.
  unfold hrx5_B8CK_acc. eapply derives_trans; [apply (derives_refl' _ _ (eq_sym (sepcon_emp Q)))|].
  apply sepcon_derives; [apply derives_refl|]. rewrite <- wand_sepcon_adjoint. rewrite emp_sepcon. apply derives_refl.
Qed.

Lemma hrx5_B8CK_acc_l Q A F : hrx5_B8CK_acc Q A -> hrx5_B8CK_acc Q (A * F).
Proof.
  unfold hrx5_B8CK_acc. intros H. apply derives_trans with (Q * (Q -* A) * F).
  { apply sepcon_derives; [exact H | apply derives_refl]. }
  rewrite (sepcon_assoc Q). apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_assoc (Q -* A)), (sepcon_comm F Q), <- (sepcon_assoc (Q -* A)), (sepcon_comm (Q -* A) Q).
  apply sepcon_derives; [apply modus_ponens_wand | apply derives_refl].
Qed.

Lemma hrx5_B8CK_acc_r Q A F : hrx5_B8CK_acc Q A -> hrx5_B8CK_acc Q (F * A).
Proof. intros H. rewrite sepcon_comm. apply hrx5_B8CK_acc_l, H. Qed.

Lemma hrx5_B8CK_acc_prop Q (c: Prop) A : (c -> hrx5_B8CK_acc Q A) -> hrx5_B8CK_acc Q (!! c && A).
Proof.
  unfold hrx5_B8CK_acc. intros H. apply derives_extract_prop. intros Hc.
  eapply derives_trans; [apply H, Hc|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. eapply derives_trans; [apply modus_ponens_wand|].
  apply andp_right; [apply prop_right, Hc | apply derives_refl].
Qed.

Lemma hrx5_B8CK_acc_ex {X: Type} Q (A: X -> mpred) : (forall x, hrx5_B8CK_acc Q (A x)) -> hrx5_B8CK_acc Q (EX x, A x).
Proof.
  unfold hrx5_B8CK_acc. intros H. apply exp_left. intros x.
  eapply derives_trans; [apply H|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. eapply derives_trans; [apply modus_ponens_wand|].
  apply exp_right with x. apply derives_refl.
Qed.

Lemma hrx5_B8CK_acc_pure Q (c: Prop) A : (A |-- !! c) -> (c -> hrx5_B8CK_acc Q A) -> hrx5_B8CK_acc Q A.
Proof.
  unfold hrx5_B8CK_acc. intros H1 H2.
  eapply derives_trans; [apply andp_right; [exact H1 | apply derives_refl]|].
  apply derives_extract_prop. intros Hc. apply H2, Hc.
Qed.

Lemma hrx5_B8CK_acc_trans Q B P : hrx5_B8CK_acc Q B -> hrx5_B8CK_acc B P -> hrx5_B8CK_acc Q P.
Proof.
  unfold hrx5_B8CK_acc. intros H1 H2. eapply derives_trans; [exact H2|].
  eapply derives_trans; [apply sepcon_derives; [exact H1 | apply derives_refl]|].
  rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_comm (Q -* B) (B -* P)), sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | rewrite sepcon_comm; apply modus_ponens_wand]|].
  rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hrx5_B8CK_acc_eq Q G P : P = Q * G -> hrx5_B8CK_acc Q P.
Proof.
  unfold hrx5_B8CK_acc. intros E. rewrite E at 1. apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm, <- E. apply derives_refl.
Qed.

Lemma hrx5_B8CK_acc_split Q G P : (P |-- Q * G) -> (Q * G |-- P) -> hrx5_B8CK_acc Q P.
Proof.
  unfold hrx5_B8CK_acc. intros H1 H2. eapply derives_trans; [exact H1 |]. apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. exact H2.
Qed.

Lemma hrx5_B8CK_wand1 (A Q: mpred) : A * (A -* Q) |-- Q.
Proof. apply wand_frame_elim. Qed.

(* ---------------------------------------------------------------------- *)
(* small facts                                                             *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B8CK_eqb_refl l : bytes_eqb l l = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec l l); congruence. Qed.

Lemma hrx5_B8CK_supd_in (PS: list (val * share * peer)) a sh P P' :
  sfind PS a = Some (sh, P) -> In (a, sh, P') (supd PS a P').
Proof.
  induction PS as [| [[x shx] Px] PS IH]; simpl; [discriminate |].
  match goal with |- context [if ?d then _ else _] => destruct d as [-> | Hne] end; intros Hs.
  - inv Hs. left. reflexivity.
  - right. apply IH. exact Hs.
Qed.

(* the node search and the peer search stop at the same position *)
Lemma hrx5_B8CK_find T (NS: list hnode4) (PS: list (val * share * peer)) a sh P :
  map hn_p NS = map peer_addr4 PS -> hrx5_nfind NS a <> nullval -> sfind PS a = Some (sh, P) ->
  exists NS1 N NS2, hnodes_snapped4 T NS PS = NS1 ++ N :: NS2 /\
    hn_addr N = hrx5_nfind NS a /\ hn_p N = a /\ hn_rest N = prsnap_val P.
Proof.
  revert PS; induction NS as [|N0 NS IH]; intros [|[[p shp] P0] PS] Hm Hn Hs; simpl in Hm; try discriminate.
  all: try (simpl in Hn; congruence).
  - inversion Hm as [[H1 H2]]. subst p. simpl in Hn, Hs.
    destruct (EqDec_val (hn_p N0) a) as [e|ne].
    + inv Hs. exists [], (hn_snapshot4 T N0 (hn_p N0, sh, P)), (hnodes_snapped4 T NS PS).
      split; [reflexivity|]. simpl. rewrite if_true by reflexivity. auto.
    + destruct (IH PS H2 Hn Hs) as (NS1 & N & NS2 & HS & Ha & Hp & Hr).
      exists (hn_snapshot4 T N0 (hn_p N0, shp, P0) :: NS1), N, NS2.
      split; [unfold hnodes_snapped4 in *; simpl; rewrite HS; reflexivity |].
      simpl. rewrite if_false by exact ne. auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* the nodes                                                               *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B8CK_head l NS : hnodes_rep4 W l NS |-- !! (l = hrx5_head NS).
Proof. destruct NS as [|N NS]; simpl; entailer!. Qed.

Lemma hrx5_B8CK_node NS1 N NS2 l :
  hrx5_B8CK_acc (@data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, hrx5_head NS2)))) (hn_addr N))
    (hnodes_rep4 W l (NS1 ++ N :: NS2)).
Proof.
  revert l; induction NS1 as [|M NS1 IH]; intros l; simpl.
  - apply hrx5_B8CK_acc_prop; intros ->. apply hrx5_B8CK_acc_ex; intros nx.
    apply hrx5_B8CK_acc_pure with (c := nx = hrx5_head NS2).
    { sep_apply (hrx5_B8CK_head nx NS2). entailer!. }
    intros ->. do 2 apply hrx5_B8CK_acc_l. apply hrx5_B8CK_acc_r, hrx5_B8CK_acc_refl.
  - apply hrx5_B8CK_acc_prop; intros _. apply hrx5_B8CK_acc_ex; intros nx.
    apply hrx5_B8CK_acc_r, IH.
Qed.

Section Wsec.
#[local] Existing Instance W_handshake_receive.

(* the node's field p *)
Lemma hrx5_B8CK_p_acc p sn r rs nx x :
  hrx5_B8CK_acc (@field_at W Ews t_hnode4 (DOT HRK._p) p x)
    (@data_at CKS Ews t_hnode4 (p, (sn, (r, (rs, nx)))) x).
Proof.
  unfold hrx5_B8CK_acc.
  rewrite (@data_at_change_composite CKS W _ Ews t_hnode4 _ _ (JMeq_refl _)) by prove_cs_preserve_type.
  unfold_data_at (@data_at W Ews t_hnode4 _ x).
  apply sepcon_derives; [apply derives_refl | apply wand_frame_intro].
Qed.

(* the node's cookie snapshot rest.cookie *)
Lemma hrx5_B8CK_ck_ramif p sn r P nx x :
  hrx5_B8CK_acc
    (@field_at CKS Ews t_hnode4 [StructField HRK._cookie; StructField HRK._rest] (cksnap_val (p_cookie P)) x)
    (@data_at CKS Ews t_hnode4 (p, (sn, (r, (prsnap_val P, nx)))) x).
Proof.
  apply hrx5_B8CK_acc_pure with (c := @field_compatible CKS t_hnode4 [] x); [entailer! | intros FC].
  unfold hrx5_B8CK_acc.
  eapply derives_trans; [apply (@nested_field_ramif CKS Ews t_hnode4 [] [StructField HRK._cookie; StructField HRK._rest]
     _ (cksnap_val (p_cookie P)) x); [apply JMeq_refl | destruct FC as (?&?&?&?&?); repeat split; auto; compute; tauto] |].
  apply sepcon_derives; [apply derives_refl|].
  apply (allp_left _ (cksnap_val (p_cookie P))). apply (allp_left _ (cksnap_val (p_cookie P))).
  rewrite prop_imp by apply JMeq_refl.
  apply derives_refl.
Qed.

End Wsec.

(* the three arrays of the snapshot the CHECK compares *)
Definition hrx5_B8CK_ckq (C: cookie) (x: val) : mpred :=
  hbytes Ews (ck_last_mac1 C) (offset_val 378 x) * hbytes Ews (ck_dkey C) (offset_val 394 x) *
  hbytes Ews (ck_mkey C) (offset_val 426 x).

(* the lengths of these three arrays *)
Definition hrx5_B8CK_ck3 (C: cookie) : Prop :=
  Zlength (ck_last_mac1 C) = 16 /\ Zlength (ck_dkey C) = 32 /\ Zlength (ck_mkey C) = 32.

Section Wsec2.
#[local] Existing Instance W_handshake_receive.

Lemma hrx5_B8CK_snap_acc C x : hrx5_B8CK_ck3 C ->
  hrx5_B8CK_acc (hrx5_B8CK_ckq C x)
    (@field_at CKS Ews t_hnode4 [StructField HRK._cookie; StructField HRK._rest] (cksnap_val C) x).
Proof.
  intros (L2 & L3 & L4).
  rewrite (@field_at_change_composite CKS W _ Ews t_hnode4 [StructField HRK._cookie; StructField HRK._rest]
    (cksnap_val C) (cksnap_val C) (JMeq_refl _)) by reflexivity.
  apply hrx5_B8CK_acc_pure with
    (c := @field_compatible W t_hnode4 [StructField HRK._cookie; StructField HRK._rest] x); [entailer! | intros FCW].
  assert (E8: @field_address W t_hnode4 [StructField HRK._cookie; StructField HRK._rest] x = offset_val 352 x)
    by (rewrite field_address_offset by exact FCW; reflexivity).
  assert (FCs: @field_compatible W t_cksnap [] (offset_val 352 x)).
  { exact (field_compatible_nested_field _ _ _ FCW). }
  rewrite (@field_at_data_at W). rewrite E8.
  change (@nested_field_type W t_hnode4 [StructField HRK._cookie; StructField HRK._rest]) with t_cksnap.
  unfold hrx5_B8CK_ckq.
  apply hrx5_B8CK_acc_split with
    (G := (@field_at W Ews t_cksnap (DOT HRK._birthdate) (Vlong (ck_birth C)) (offset_val 352 x) *
           @field_at W Ews t_cksnap (DOT HRK._is_valid) (Val.of_bool (ck_valid C)) (offset_val 352 x) *
           @field_at W Ews t_cksnap (DOT HRK._cookie) (bytes (ck_cookie C)) (offset_val 352 x) *
           @field_at W Ews t_cksnap (DOT HRK._have_sent_mac1) (Val.of_bool (ck_sent C)) (offset_val 352 x) *
           spacer Ews 106 112 (offset_val 352 x))%logic).
  { unfold t_cksnap. unfold_data_at (data_at _ _ _ (offset_val 352 x)).
    rewrite (field_at_data_at Ews (Tstruct HK._ck_snap noattr) (DOT HRK._last_mac1_sent)),
      (field_at_data_at Ews (Tstruct HK._ck_snap noattr) (DOT HRK._cookie_decryption_key)),
      (field_at_data_at Ews (Tstruct HK._ck_snap noattr) (DOT HRK._message_mac1_key)).
    rewrite !field_address_offset by (destruct FCs as (?&?&?&?&?); repeat split; auto; compute; tauto).
    unfold hbytes. rewrite L2, L3, L4. rewrite !(@data_at_tarray_tuchar_cs HCS W).
    unfold cksnap_val. cbn [fst snd]. simpl nested_field_type. simpl nested_field_offset.
    rewrite !offset_offset_val. simpl Z.add.
    cancel. }
  { unfold t_cksnap. unfold_data_at (data_at _ _ _ (offset_val 352 x)).
    rewrite (field_at_data_at Ews (Tstruct HK._ck_snap noattr) (DOT HRK._last_mac1_sent)),
      (field_at_data_at Ews (Tstruct HK._ck_snap noattr) (DOT HRK._cookie_decryption_key)),
      (field_at_data_at Ews (Tstruct HK._ck_snap noattr) (DOT HRK._message_mac1_key)).
    rewrite !field_address_offset by (destruct FCs as (?&?&?&?&?); repeat split; auto; compute; tauto).
    unfold hbytes. rewrite L2, L3, L4. rewrite !(@data_at_tarray_tuchar_cs HCS W).
    unfold cksnap_val. cbn [fst snd]. simpl nested_field_type. simpl nested_field_offset.
    rewrite !offset_offset_val. simpl Z.add.
    cancel. }
Qed.

End Wsec2.

(* the target node, opened at its field p *)
Lemma hrx5_B8CK_open_p NSS NS1 N NS2 l :
  NSS = NS1 ++ N :: NS2 ->
  hnodes_rep4 W l NSS |--
  @field_at W Ews t_hnode4 (DOT HRK._p) (hn_p N) (hn_addr N) *
  (@field_at W Ews t_hnode4 (DOT HRK._p) (hn_p N) (hn_addr N) -* hnodes_rep4 W l NSS).
Proof.
  intros ->. eapply hrx5_B8CK_acc_trans; [| apply hrx5_B8CK_node]. apply hrx5_B8CK_p_acc.
Qed.

(* the target node, opened at its cookie snapshot *)
Lemma hrx5_B8CK_open_ck NSS NS1 N NS2 l P :
  NSS = NS1 ++ N :: NS2 -> hn_rest N = prsnap_val P -> hrx5_B8CK_ck3 (p_cookie P) ->
  hnodes_rep4 W l NSS |--
  hrx5_B8CK_ckq (p_cookie P) (hn_addr N) * (hrx5_B8CK_ckq (p_cookie P) (hn_addr N) -* hnodes_rep4 W l NSS).
Proof.
  intros -> Hr Hok. eapply hrx5_B8CK_acc_trans; [| apply hrx5_B8CK_node].
  rewrite Hr. eapply hrx5_B8CK_acc_trans; [| apply hrx5_B8CK_ck_ramif].
  apply hrx5_B8CK_snap_acc, Hok.
Qed.

(* ---------------------------------------------------------------------- *)
(* a peer's cookie (port of hcy5_p11_C_peer / cookie_split / ck_open)      *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_B8CK_tck := Tstruct HRK._cookie noattr.

Definition hrx5_B8CK_prest (sh: share) (p: val) (P: peer) : mpred :=
  (!! @field_compatible Noise.CS t_peer [] p &&
  (@field_at Noise.CS sh t_peer [StructField I._device] (p_device P) p *
   @field_at Noise.CS sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   @field_at Noise.CS sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   @field_at Noise.CS sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   @field_at Noise.CS sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p))%logic.

Lemma hrx5_B8CK_peer_split sh a P :
  peer_rep sh a P = (cookie_rep sh (cookie_addr a) (p_cookie P) * hrx5_B8CK_prest sh a P)%logic.
Proof.
  unfold peer_rep, hrx5_B8CK_prest. apply pred_ext; entailer!; cancel.
Qed.

Lemma hrx5_B8CK_wand_eq (X F G: mpred) : X = (F * G)%logic -> X |-- F * (F -* X).
Proof.
  intros E. rewrite E at 1. apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm, <- E. apply derives_refl.
Qed.

Lemma hrx5_B8CK_peer PS a sh P :
  In (a, sh, P) PS ->
  peers_rep PS |-- cookie_rep sh (cookie_addr a) (p_cookie P) *
                   (cookie_rep sh (cookie_addr a) (p_cookie P) -* peers_rep PS).
Proof.
  intros Hin. destruct (in_split _ _ Hin) as (l1 & l2 & ->).
  apply hrx5_B8CK_wand_eq with (G := (hrx5_B8CK_prest sh a P * iter_sepcon peer_item_rep l1 *
                                         iter_sepcon peer_item_rep l2)%logic).
  unfold peers_rep. rewrite iter_sepcon_app. simpl iter_sepcon. cbn [peer_item_rep].
  rewrite hrx5_B8CK_peer_split. apply pred_ext; cancel.
Qed.

Lemma hrx5_B8CK_peers_ck PS a sh P : In (a, sh, P) PS -> peers_rep PS |-- !! cookie_ok (p_cookie P).
Proof.
  intros Hin. destruct (in_split _ _ Hin) as (l1 & l2 & ->).
  unfold peers_rep. rewrite iter_sepcon_app. simpl iter_sepcon. cbn [peer_item_rep].
  unfold peer_rep at 1, cookie_rep. entailer!.
Qed.

Section Wsec3.
#[local] Existing Instance W_handshake_receive.

Lemma hrx5_B8CK_cookie_split sh C lk c : cookie_ok C ->
  @data_at Noise.CS sh t_cookie (cookie_val C lk) c =
  (field_at sh hrx5_B8CK_tck (DOT HRK._birthdate) (Vlong (ck_birth C)) c *
   field_at sh hrx5_B8CK_tck (DOT HRK._is_valid) (Val.of_bool (ck_valid C)) c *
   hbytes sh (ck_cookie C) (field_address hrx5_B8CK_tck (DOT HRK._cookie) c) *
   field_at sh hrx5_B8CK_tck (DOT HRK._have_sent_mac1) (Val.of_bool (ck_sent C)) c *
   hbytes sh (ck_last_mac1 C) (field_address hrx5_B8CK_tck (DOT HRK._last_mac1_sent) c) *
   hbytes sh (ck_dkey C) (field_address hrx5_B8CK_tck (DOT HRK._cookie_decryption_key) c) *
   hbytes sh (ck_mkey C) (field_address hrx5_B8CK_tck (DOT HRK._message_mac1_key) c) *
   spacer sh 106 108 c * field_at sh hrx5_B8CK_tck (DOT HRK._lock) lk c)%logic.
Proof.
  intros (L1 & L2 & L3 & L4).
  erewrite (@data_at_change_composite Noise.CS W _ sh t_cookie _ _ (JMeq_refl _)) by reflexivity.
  unfold t_cookie. unfold_data_at (data_at _ _ _ c).
  rewrite !(field_at_data_at sh (Tstruct I._cookie noattr) (DOT HRK._cookie)).
  rewrite (field_at_data_at sh (Tstruct I._cookie noattr) (DOT HRK._last_mac1_sent)),
    (field_at_data_at sh (Tstruct I._cookie noattr) (DOT HRK._cookie_decryption_key)),
    (field_at_data_at sh (Tstruct I._cookie noattr) (DOT HRK._message_mac1_key)).
  unfold hbytes. rewrite L1, L2, L3, L4.
  rewrite !(@data_at_tarray_tuchar_cs HCS W).
  unfold hrx5_B8CK_tck, cookie_val. cbn [fst snd]. simpl nested_field_type.
  apply pred_ext; cancel.
Qed.

(* the accepted peer's cookie at the world, with explicit field values *)
Definition hrx5_B8CK_ckp (ca: val) (b: int64) (v: bool) (ck: list byte) (s: bool) (lm dk mk: list byte) (lk: val)
  : mpred :=
  (@field_at W Ews hrx5_B8CK_tck (DOT HRK._birthdate) (Vlong b) ca *
   @field_at W Ews hrx5_B8CK_tck (DOT HRK._is_valid) (Val.of_bool v) ca *
   hbytes Ews ck (offset_val 9 ca) *
   @field_at W Ews hrx5_B8CK_tck (DOT HRK._have_sent_mac1) (Val.of_bool s) ca *
   hbytes Ews lm (offset_val 26 ca) *
   hbytes Ews dk (offset_val 42 ca) *
   hbytes Ews mk (offset_val 74 ca) *
   spacer Ews 106 108 ca * @field_at W Ews hrx5_B8CK_tck (DOT HRK._lock) lk ca)%logic.

Lemma hrx5_B8CK_ck_eq b v ck s lm dk mk lk ca :
  cookie_ok (mkCookie b v ck s lm dk mk) -> @field_compatible W hrx5_B8CK_tck [] ca ->
  @data_at Noise.CS Ews t_cookie (cookie_val (mkCookie b v ck s lm dk mk) lk) ca =
  hrx5_B8CK_ckp ca b v ck s lm dk mk lk.
Proof.
  intros Hok FC. rewrite (hrx5_B8CK_cookie_split Ews _ lk ca Hok).
  rewrite !field_address_offset by (destruct FC as (?&?&?&?&?); repeat split; auto; compute; tauto).
  unfold hrx5_B8CK_ckp. reflexivity.
Qed.

Lemma hrx5_B8CK_ck_open PS a P b v ck s lm dk mk :
  In (a, Ews, P) PS -> p_cookie P = mkCookie b v ck s lm dk mk ->
  peers_rep PS |--
  EX lk: val, !! (cookie_ok (mkCookie b v ck s lm dk mk) /\ @field_compatible W hrx5_B8CK_tck [] (cookie_addr a)) &&
   (hrx5_B8CK_ckp (cookie_addr a) b v ck s lm dk mk lk *
    (cookie_rep Ews (cookie_addr a) (mkCookie b v ck s lm dk mk) -* peers_rep PS)).
Proof.
  intros Hin HC.
  sep_apply (hrx5_B8CK_peer PS a Ews P Hin). rewrite HC.
  unfold cookie_rep at 1. Intros lk. Exists lk.
  rewrite (hrx5_B8CK_cookie_split Ews _ lk (cookie_addr a) H).
  assert_PROP (@field_compatible W hrx5_B8CK_tck [] (cookie_addr a)) as FC.
  { entailer!.
    match goal with Hf: field_compatible hrx5_B8CK_tck (DOT HRK._birthdate) _ |- _ =>
      destruct Hf as (A1 & A2 & A3 & A4 & _) end.
    repeat split; auto. }
  rewrite !field_address_offset by (destruct FC as (?&?&?&?&?); repeat split; auto; compute; tauto).
  unfold hrx5_B8CK_ckp. apply andp_right; [apply prop_right; split; auto |].
  cbn [ck_birth ck_valid ck_cookie ck_sent ck_last_mac1 ck_dkey ck_mkey]. simpl nested_field_offset. cancel.
Qed.

Lemma hrx5_B8CK_ck_close ca b v ck s lm dk mk lk X :
  cookie_ok (mkCookie b v ck s lm dk mk) -> @field_compatible W hrx5_B8CK_tck [] ca ->
  (hrx5_B8CK_ckp ca b v ck s lm dk mk lk * (cookie_rep Ews ca (mkCookie b v ck s lm dk mk) -* X) |-- X)%logic.
Proof.
  intros Hok FC.
  eapply derives_trans; [| apply (modus_ponens_wand (cookie_rep Ews ca (mkCookie b v ck s lm dk mk)) X)].
  apply sepcon_derives; [| apply derives_refl].
  unfold cookie_rep. Exists lk. rewrite (hrx5_B8CK_ck_eq b v ck s lm dk mk lk ca Hok FC). entailer!.
Qed.

End Wsec3.
