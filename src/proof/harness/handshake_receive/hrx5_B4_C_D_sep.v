(* law handshake_receive, phase B4, segment C, part D:
   separation-logic helpers of hrx5_B4_C_D.v (the decryption of a cookie reply for the target node): the node of the
   list focused with a wand, its cookie snapshot (rest.cookie) split into have_sent_mac1 and the two byte arrays the
   decryption reads, the reply at the world, byte buffers at the world.  Port of cookie_reply's hcy5_p11_C_lemmas.v.
   Offsets (x86_64): hnode: rest 304, rest.cookie 352, its last_mac1_sent 378, cookie_decryption_key 394. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_cs.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require Import WgNoise.proof.libc.libc_bytes.
Require WgNoise.harness.x_handshake_receive.code.
Local Open Scope logic.

Module HRM := WgNoise.harness.x_handshake_receive.code.
Local Notation W := W_handshake_receive.

#[local] Instance hrx5_B4_C_D_cceK : change_composite_env CKS W_handshake_receive.
Proof. make_cs_preserve CKS W_handshake_receive. Defined.
#[local] Instance hrx5_B4_C_D_cceC : change_composite_env Cookie.CS W_handshake_receive.
Proof. make_cs_preserve Cookie.CS W_handshake_receive. Defined.

(* ---------------------------------------------------------------------- *)
(* access: P gives Q and takes it back                                     *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_B4_C_D_acc (Q P: mpred) : Prop := P |-- Q * (Q -* P).

Lemma hrx5_B4_C_D_acc_refl Q : hrx5_B4_C_D_acc Q Q.
Proof.
  unfold hrx5_B4_C_D_acc. eapply derives_trans; [apply (derives_refl' _ _ (eq_sym (sepcon_emp Q)))|].
  apply sepcon_derives; [apply derives_refl|]. rewrite <- wand_sepcon_adjoint. rewrite emp_sepcon. apply derives_refl.
Qed.

Lemma hrx5_B4_C_D_acc_l Q A F : hrx5_B4_C_D_acc Q A -> hrx5_B4_C_D_acc Q (A * F).
Proof.
  unfold hrx5_B4_C_D_acc. intros H. apply derives_trans with (Q * (Q -* A) * F).
  { apply sepcon_derives; [exact H | apply derives_refl]. }
  rewrite (sepcon_assoc Q). apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_assoc (Q -* A)), (sepcon_comm F Q), <- (sepcon_assoc (Q -* A)), (sepcon_comm (Q -* A) Q).
  apply sepcon_derives; [apply modus_ponens_wand | apply derives_refl].
Qed.

Lemma hrx5_B4_C_D_acc_r Q A F : hrx5_B4_C_D_acc Q A -> hrx5_B4_C_D_acc Q (F * A).
Proof. intros H. rewrite sepcon_comm. apply hrx5_B4_C_D_acc_l, H. Qed.

Lemma hrx5_B4_C_D_acc_prop Q (c: Prop) A : (c -> hrx5_B4_C_D_acc Q A) -> hrx5_B4_C_D_acc Q (!! c && A).
Proof.
  unfold hrx5_B4_C_D_acc. intros H. apply derives_extract_prop. intros Hc.
  eapply derives_trans; [apply H, Hc|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. eapply derives_trans; [apply modus_ponens_wand|].
  apply andp_right; [apply prop_right, Hc | apply derives_refl].
Qed.

Lemma hrx5_B4_C_D_acc_ex {X: Type} Q (A: X -> mpred) : (forall x, hrx5_B4_C_D_acc Q (A x)) -> hrx5_B4_C_D_acc Q (EX x, A x).
Proof.
  unfold hrx5_B4_C_D_acc. intros H. apply exp_left. intros x.
  eapply derives_trans; [apply H|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. eapply derives_trans; [apply modus_ponens_wand|].
  apply exp_right with x. apply derives_refl.
Qed.

Lemma hrx5_B4_C_D_acc_pure Q (c: Prop) A : (A |-- !! c) -> (c -> hrx5_B4_C_D_acc Q A) -> hrx5_B4_C_D_acc Q A.
Proof.
  unfold hrx5_B4_C_D_acc. intros H1 H2.
  eapply derives_trans; [apply andp_right; [exact H1 | apply derives_refl]|].
  apply derives_extract_prop. intros Hc. apply H2, Hc.
Qed.

Lemma hrx5_B4_C_D_acc_trans Q B P : hrx5_B4_C_D_acc Q B -> hrx5_B4_C_D_acc B P -> hrx5_B4_C_D_acc Q P.
Proof.
  unfold hrx5_B4_C_D_acc. intros H1 H2. eapply derives_trans; [exact H2|].
  eapply derives_trans; [apply sepcon_derives; [exact H1 | apply derives_refl]|].
  rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_comm (Q -* B) (B -* P)), sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | rewrite sepcon_comm; apply modus_ponens_wand]|].
  rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hrx5_B4_C_D_acc_eq Q G P : P = Q * G -> hrx5_B4_C_D_acc Q P.
Proof.
  unfold hrx5_B4_C_D_acc. intros E. rewrite E at 1. apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm, <- E. apply derives_refl.
Qed.

Lemma hrx5_B4_C_D_acc_split Q G P : (P |-- Q * G) -> (Q * G |-- P) -> hrx5_B4_C_D_acc Q P.
Proof.
  unfold hrx5_B4_C_D_acc. intros H1 H2. eapply derives_trans; [exact H1 |]. apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. exact H2.
Qed.

Lemma hrx5_B4_C_D_wand1 (A Q: mpred) : A * (A -* Q) |-- Q.
Proof. apply wand_frame_elim. Qed.

(* ---------------------------------------------------------------------- *)
(* small facts                                                             *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B4_C_D_sfind_in (PS: list (val * share * peer)) a sh P :
  sfind PS a = Some (sh, P) -> In (a, sh, P) PS.
Proof.
  induction PS as [| [[x shx] Px] PS IH]; simpl; [discriminate |].
  match goal with |- context [if ?d then _ else _] => destruct d as [-> | Hne] end; intros Hs.
  - inv Hs. left. reflexivity.
  - right. apply IH. exact Hs.
Qed.

Lemma hrx5_B4_C_D_peers_ck PS a sh P : In (a, sh, P) PS -> peers_rep PS |-- !! cookie_ok (p_cookie P).
Proof.
  intros Hin. destruct (in_split _ _ Hin) as (l1 & l2 & ->).
  unfold peers_rep. rewrite iter_sepcon_app. simpl iter_sepcon. cbn [peer_item_rep].
  unfold peer_rep at 1, cookie_rep. entailer!.
Qed.

(* ---------------------------------------------------------------------- *)
(* the nodes                                                               *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B4_C_D_head l NS : hnodes_rep4 W l NS |-- !! (l = hrx5_head NS).
Proof. destruct NS as [|N NS]; simpl; entailer!. Qed.

Lemma hrx5_B4_C_D_node NS1 N NS2 l :
  hrx5_B4_C_D_acc (@data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, hrx5_head NS2)))) (hn_addr N))
    (hnodes_rep4 W l (NS1 ++ N :: NS2)).
Proof.
  revert l; induction NS1 as [|M NS1 IH]; intros l; simpl.
  - apply hrx5_B4_C_D_acc_prop; intros ->. apply hrx5_B4_C_D_acc_ex; intros nx.
    apply hrx5_B4_C_D_acc_pure with (c := nx = hrx5_head NS2).
    { sep_apply (hrx5_B4_C_D_head nx NS2). entailer!. }
    intros ->. do 2 apply hrx5_B4_C_D_acc_l. apply hrx5_B4_C_D_acc_r, hrx5_B4_C_D_acc_refl.
  - apply hrx5_B4_C_D_acc_prop; intros _. apply hrx5_B4_C_D_acc_ex; intros nx.
    apply hrx5_B4_C_D_acc_r, IH.
Qed.

Lemma hrx5_B4_C_D_hn_valid l NS a : In a (map hn_addr NS) -> hnodes_rep4 W l NS |-- valid_pointer a.
Proof.
  revert l; induction NS as [|N NS IH]; intros l Hin; simpl in *; [contradiction|].
  Intros nx. destruct Hin as [<-|Hin].
  - subst l. auto with valid_pointer.
  - apply sepcon_valid_pointer2, IH, Hin.
Qed.

(* the node's cookie snapshot rest.cookie *)
Lemma hrx5_B4_C_D_ck_ramif p sn r P nx x :
  hrx5_B4_C_D_acc
    (@field_at CKS Ews t_hnode4 [StructField HRM._cookie; StructField HRM._rest] (cksnap_val (p_cookie P)) x)
    (@data_at CKS Ews t_hnode4 (p, (sn, (r, (prsnap_val P, nx)))) x).
Proof.
  apply hrx5_B4_C_D_acc_pure with (c := @field_compatible CKS t_hnode4 [] x); [entailer! | intros FC].
  unfold hrx5_B4_C_D_acc.
  eapply derives_trans; [apply (@nested_field_ramif CKS Ews t_hnode4 [] [StructField HRM._cookie; StructField HRM._rest]
     _ (cksnap_val (p_cookie P)) x); [apply JMeq_refl | destruct FC as (?&?&?&?&?); repeat split; auto; compute; tauto] |].
  apply sepcon_derives; [apply derives_refl|].
  apply (allp_left _ (cksnap_val (p_cookie P))). apply (allp_left _ (cksnap_val (p_cookie P))).
  rewrite prop_imp by apply JMeq_refl.
  apply derives_refl.
Qed.

(* the snapshot's have_sent_mac1 as a field of the node, the two arrays the decryption reads as byte buffers *)
Definition hrx5_B4_C_D_ckq (C: cookie) (x: val) : mpred :=
  @field_at W Ews t_hnode4 [StructField HRM._have_sent_mac1; StructField HRM._cookie; StructField HRM._rest]
    (Val.of_bool (ck_sent C)) x *
  hbytes Ews (ck_last_mac1 C) (offset_val 378 x) * hbytes Ews (ck_dkey C) (offset_val 394 x).

Section Wsec.
#[local] Existing Instance W_handshake_receive.

Lemma hrx5_B4_C_D_snap_acc C x : cookie_ok C ->
  hrx5_B4_C_D_acc (hrx5_B4_C_D_ckq C x)
    (@field_at CKS Ews t_hnode4 [StructField HRM._cookie; StructField HRM._rest] (cksnap_val C) x).
Proof.
  intros (L1 & L2 & L3 & L4).
  rewrite (@field_at_change_composite CKS W _ Ews t_hnode4 [StructField HRM._cookie; StructField HRM._rest]
    (cksnap_val C) (cksnap_val C) (JMeq_refl _)) by reflexivity.
  apply hrx5_B4_C_D_acc_pure with
    (c := @field_compatible W t_hnode4 [StructField HRM._cookie; StructField HRM._rest] x); [entailer! | intros FCW].
  assert (E8: @field_address W t_hnode4 [StructField HRM._cookie; StructField HRM._rest] x = offset_val 352 x)
    by (rewrite field_address_offset by exact FCW; reflexivity).
  assert (FCs: @field_compatible W t_cksnap [] (offset_val 352 x)).
  { exact (field_compatible_nested_field _ _ _ FCW). }
  rewrite (@field_at_data_at W). rewrite E8.
  change (@nested_field_type W t_hnode4 [StructField HRM._cookie; StructField HRM._rest]) with t_cksnap.
  unfold hrx5_B4_C_D_ckq.
  change [StructField HRM._have_sent_mac1; StructField HRM._cookie; StructField HRM._rest]
    with ([StructField HRM._have_sent_mac1] ++ [StructField HRM._cookie; StructField HRM._rest]).
  rewrite (@field_at_app W Ews t_hnode4 [StructField HRM._have_sent_mac1] [StructField HRM._cookie; StructField HRM._rest] _
             (Val.of_bool (ck_sent C)) x (JMeq_refl _)).
  rewrite E8. change (@nested_field_type W t_hnode4 [StructField HRM._cookie; StructField HRM._rest]) with t_cksnap.
  apply hrx5_B4_C_D_acc_split with
    (G := (@field_at W Ews t_cksnap (DOT HRM._birthdate) (Vlong (ck_birth C)) (offset_val 352 x) *
           @field_at W Ews t_cksnap (DOT HRM._is_valid) (Val.of_bool (ck_valid C)) (offset_val 352 x) *
           @field_at W Ews t_cksnap (DOT HRM._cookie) (bytes (ck_cookie C)) (offset_val 352 x) *
           @field_at W Ews t_cksnap (DOT HRM._message_mac1_key) (bytes (ck_mkey C)) (offset_val 352 x) *
           spacer Ews 106 112 (offset_val 352 x))%logic).
  { unfold t_cksnap. unfold_data_at (data_at _ _ _ (offset_val 352 x)).
    rewrite (field_at_data_at Ews (Tstruct HK._ck_snap noattr) (DOT HRM._last_mac1_sent)),
      (field_at_data_at Ews (Tstruct HK._ck_snap noattr) (DOT HRM._cookie_decryption_key)).
    rewrite !field_address_offset by (destruct FCs as (?&?&?&?&?); repeat split; auto; compute; tauto).
    unfold hbytes. rewrite L2, L3. rewrite !(@data_at_tarray_tuchar_cs HCS W).
    unfold cksnap_val. cbn [fst snd]. simpl nested_field_type. simpl nested_field_offset.
    rewrite !offset_offset_val. simpl Z.add.
    cancel. }
  { unfold t_cksnap. unfold_data_at (data_at _ _ _ (offset_val 352 x)).
    rewrite (field_at_data_at Ews (Tstruct HK._ck_snap noattr) (DOT HRM._last_mac1_sent)),
      (field_at_data_at Ews (Tstruct HK._ck_snap noattr) (DOT HRM._cookie_decryption_key)).
    rewrite !field_address_offset by (destruct FCs as (?&?&?&?&?); repeat split; auto; compute; tauto).
    unfold hbytes. rewrite L2, L3. rewrite !(@data_at_tarray_tuchar_cs HCS W).
    unfold cksnap_val. cbn [fst snd]. simpl nested_field_type. simpl nested_field_offset.
    rewrite !offset_offset_val. simpl Z.add.
    cancel. }
Qed.

End Wsec.

(* the target node, opened at its cookie snapshot *)
Lemma hrx5_B4_C_D_open NSS NS1 N NS2 l P :
  NSS = NS1 ++ N :: NS2 -> hn_rest N = prsnap_val P -> cookie_ok (p_cookie P) ->
  hnodes_rep4 W l NSS |--
  hrx5_B4_C_D_ckq (p_cookie P) (hn_addr N) * (hrx5_B4_C_D_ckq (p_cookie P) (hn_addr N) -* hnodes_rep4 W l NSS).
Proof.
  intros -> Hr Hok. eapply hrx5_B4_C_D_acc_trans; [| apply hrx5_B4_C_D_node].
  rewrite Hr. eapply hrx5_B4_C_D_acc_trans; [| apply hrx5_B4_C_D_ck_ramif].
  apply hrx5_B4_C_D_snap_acc, Hok.
Qed.

Lemma hrx5_B4_C_D_close C x X :
  @field_at W Ews t_hnode4 [StructField HRM._have_sent_mac1; StructField HRM._cookie; StructField HRM._rest]
    (Val.of_bool (ck_sent C)) x *
  hbytes Ews (ck_last_mac1 C) (offset_val 378 x) * hbytes Ews (ck_dkey C) (offset_val 394 x) *
  (hrx5_B4_C_D_ckq C x -* X) |-- X.
Proof. apply hrx5_B4_C_D_wand1. Qed.

(* ---------------------------------------------------------------------- *)
(* byte buffers at the world (the AEAD's specification is at W)            *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B4_C_D_hW sh bs p :
  hbytes sh bs p = @data_at W sh (tarray tuchar (Zlength bs)) (map Vubyte bs) p.
Proof. unfold hbytes, bytes. apply data_at_tarray_tuchar_cs. Qed.

Lemma hrx5_B4_C_D_hprim sh bs p : 0 < Zlength bs -> hbytes sh bs p = @prim_bytes W sh bs p.
Proof. intros Hl. unfold prim_bytes. rewrite if_false by lia. apply hrx5_B4_C_D_hW. Qed.

Lemma hrx5_B4_C_D_zp gv : @zero_page Noise.CS gv = @zero_page W gv.
Proof. unfold zero_page. apply data_at_tarray_tuchar_cs. Qed.

Lemma hrx5_B4_C_D_hout16 sh p : hout sh 16 p = @prim_out W sh (Zrepeat Vundef 16) p.
Proof.
  unfold hout, prim_out. rewrite if_false by (cbv; discriminate).
  unfold data_at_. rewrite <- (@data_at_tarray_tuchar_cs HCS W).
  reflexivity.
Qed.

Lemma hrx5_B4_C_D_pout sh bs p : 0 < Zlength bs -> @prim_out W sh (map Vubyte bs) p = hbytes sh bs p.
Proof.
  intros Hl. unfold prim_out. rewrite Zlength_map, if_false by lia. rewrite hrx5_B4_C_D_hW. reflexivity.
Qed.

Lemma hrx5_B4_C_D_hbytes_out sh bs p : hbytes sh bs p |-- hout sh (Zlength bs) p.
Proof. unfold hbytes, hout. apply data_at_data_at_. Qed.

(* ---------------------------------------------------------------------- *)
(* the reply at the world (copy of hcy5_p11_C_cm_open)                     *)
(* ---------------------------------------------------------------------- *)

Section Wsec2.
#[local] Existing Instance W_handshake_receive.

Definition hrx5_B4_C_D_cm (sh: share) (rp: val) (CM: cookie_msg) : mpred :=
  (@field_at W sh t_cmsg (DOT HRM._header DOT HRM._type) (Vint (cm_type CM)) rp *
   @field_at W sh t_cmsg (DOT HRM._receiver_index) (Vint (cm_receiver CM)) rp *
   hbytes sh (cm_nonce CM) (offset_val 8 rp) *
   hbytes sh (cm_enc CM) (offset_val 32 rp))%logic.

Lemma hrx5_B4_C_D_cm_open sh rp CM :
  cmsg_rep sh rp CM = (!! (cm_ok CM /\ @field_compatible W t_cmsg [] rp) && hrx5_B4_C_D_cm sh rp CM)%logic.
Proof.
  unfold cmsg_rep, hrx5_B4_C_D_cm, cmsg_val.
  erewrite (@data_at_change_composite Cookie.CS W _ sh t_cmsg _ _ (JMeq_refl _))
    by prove_cs_preserve_type.
  apply pred_ext.
  - Intros. pose proof H as (L1 & L2).
    assert_PROP (@field_compatible W t_cmsg [] rp) as FC by entailer!.
    unfold hbytes. rewrite L1, L2. rewrite !(@data_at_tarray_tuchar_cs HCS W).
    unfold_data_at (@data_at W _ t_cmsg _ rp).
    rewrite (@field_at_data_at W sh t_cmsg (DOT HRM._nonce)), (@field_at_data_at W sh t_cmsg (DOT HRM._encrypted_cookie)).
    rewrite !field_address_offset by (destruct FC as (?&?&?&?&?); repeat split; auto; compute; tauto).
    simpl nested_field_type. simpl nested_field_offset.
    unfold_field_at 1%nat.
    entailer!.
  - Intros. pose proof H as (L1 & L2).
    unfold hbytes. rewrite L1, L2. rewrite !(@data_at_tarray_tuchar_cs HCS W).
    unfold_data_at (@data_at W _ t_cmsg _ rp).
    rewrite (@field_at_data_at W sh t_cmsg (DOT HRM._nonce)), (@field_at_data_at W sh t_cmsg (DOT HRM._encrypted_cookie)).
    rewrite !field_address_offset by (destruct H0 as (?&?&?&?&?); repeat split; auto; compute; tauto).
    simpl nested_field_type. simpl nested_field_offset.
    unfold_field_at 3%nat.
    entailer!.
Qed.

Lemma hrx5_B4_C_D_cm_fold sh rp CM : cm_ok CM -> @field_compatible W t_cmsg [] rp ->
  hrx5_B4_C_D_cm sh rp CM |-- cmsg_rep sh rp CM.
Proof. intros Hok FC. rewrite hrx5_B4_C_D_cm_open. entailer!. Qed.

End Wsec2.
