(* v2, law handshake_receive, B8 R B part K: copy of hrx5_B8_R_B_C3_sep.v renamed hrx5_B8RBC3_ -> hrx5_B8RBK_, plus the keypair accessors at the end. *)
(* law handshake_receive, phase B8 branch I: separation-logic access to what the
   CHECKs of branch I read: a PORT of consume_initiation_any's hci5_p8_A3_sep.v.  Original header follows. *)
(* law consume_initiation_any, phase P8, segment A3: separation-logic access to everything the
   CHECKs of A3 read (port of v1's hci3_p8_A3_sep.v to the v2 states).  Each accessor is `P |-- Q * (Q -* P)`
   (hrx5_B8RBK_acc Q P): sep_apply it to the SEP item P, use Q (load / call), then sep_apply (hrx5_B8RBK_mp Q P)
   to put P back.
   Offsets (x86_64): wg_peer: handshake 48; from the PEER a: ephemeral_private 104, remote_static 136,
   remote_ephemeral 168, precomputed_static_static 200, preshared_key 232, hash 264, chaining_key 296,
   latest_timestamp 328.  hs_snap (at s = offset_val 8 node): ephemeral_private 48, remote_static 80,
   precomputed_static_static 144, preshared_key 176.  m_consumed_initiation: st.ck 0, st.h 32, ts 128.
   message: unencrypted_ephemeral 8.
   v2: a node (struct hnode: p, snap, refs, rest, next) is ONE data_at CKS in hnodes_rep4; its fields are reached
   one at a time by VST's gfield_ramif, the other fields stay
   inside the wand. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_cs.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Local Open Scope logic.

Notation W := W_handshake_receive.
#[export] Instance hrx5_B8RBK_cceN : change_composite_env Noise.CS W.
Proof. make_cs_preserve Noise.CS W. Defined.
#[export] Instance hrx5_B8RBK_cceNH : change_composite_env Noise.CS HCS.
Proof. make_cs_preserve Noise.CS HCS. Defined.
#[export] Instance hrx5_B8RBK_cceHW : change_composite_env HCS W.
Proof. make_cs_preserve HCS W. Defined.
#[export] Instance hrx5_B8RBK_cceKW : change_composite_env CKS W.
Proof. make_cs_preserve CKS W. Defined.

(* ---- generic ---- *)
Definition hrx5_B8RBK_acc (Q P: mpred) : Prop := P |-- Q * (Q -* P).

Lemma hrx5_B8RBK_mp (Q P: mpred) : Q * (Q -* P) |-- P.
Proof. apply wand_frame_elim. Qed.

Lemma hrx5_B8RBK_acc_refl Q : hrx5_B8RBK_acc Q Q.
Proof.
  unfold hrx5_B8RBK_acc. eapply derives_trans; [apply (derives_refl' _ _ (eq_sym (sepcon_emp Q)))|].
  apply sepcon_derives; [apply derives_refl|]. rewrite <- wand_sepcon_adjoint. rewrite emp_sepcon. apply derives_refl.
Qed.

Lemma hrx5_B8RBK_acc_eq Q A : Q = A -> hrx5_B8RBK_acc Q A.
Proof. intros ->. apply hrx5_B8RBK_acc_refl. Qed.

Lemma hrx5_B8RBK_acc_l Q A F : hrx5_B8RBK_acc Q A -> hrx5_B8RBK_acc Q (A * F).
Proof.
  unfold hrx5_B8RBK_acc. intros H. apply derives_trans with (Q * (Q -* A) * F).
  { apply sepcon_derives; [exact H | apply derives_refl]. }
  rewrite (sepcon_assoc Q). apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_assoc (Q -* A)), (sepcon_comm F Q), <- (sepcon_assoc (Q -* A)), (sepcon_comm (Q -* A) Q).
  apply sepcon_derives; [apply modus_ponens_wand | apply derives_refl].
Qed.

Lemma hrx5_B8RBK_acc_r Q A F : hrx5_B8RBK_acc Q A -> hrx5_B8RBK_acc Q (F * A).
Proof. intros H. rewrite sepcon_comm. apply hrx5_B8RBK_acc_l, H. Qed.

Lemma hrx5_B8RBK_acc_prop Q (c: Prop) A : (c -> hrx5_B8RBK_acc Q A) -> hrx5_B8RBK_acc Q (!! c && A).
Proof.
  unfold hrx5_B8RBK_acc. intros H. apply derives_extract_prop. intros Hc.
  eapply derives_trans; [apply H, Hc|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. apply andp_right; [apply prop_right, Hc|]. rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hrx5_B8RBK_acc_ex {X: Type} Q (A: X -> mpred) : (forall x, hrx5_B8RBK_acc Q (A x)) -> hrx5_B8RBK_acc Q (EX x, A x).
Proof.
  unfold hrx5_B8RBK_acc. intros H. apply exp_left. intros x.
  eapply derives_trans; [apply H|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_comm. eapply derives_trans; [apply modus_ponens_wand|].
  apply (exp_right x), derives_refl.
Qed.

Lemma hrx5_B8RBK_acc_pure Q (c: Prop) A : (A |-- !! c) -> (c -> hrx5_B8RBK_acc Q A) -> hrx5_B8RBK_acc Q A.
Proof.
  unfold hrx5_B8RBK_acc. intros H1 H2. apply derives_trans with (!! c && A).
  - apply andp_right; [exact H1 | apply derives_refl].
  - apply derives_extract_prop. intros Hc. apply H2, Hc.
Qed.

Lemma hrx5_B8RBK_acc_iter {X: Type} Q (f: X -> mpred) x l :
  In x l -> hrx5_B8RBK_acc Q (f x) -> hrx5_B8RBK_acc Q (iter_sepcon f l).
Proof.
  intros Hin H. induction l as [|y l IH]; [contradiction|]. simpl.
  destruct Hin as [<-|Hin]; [apply hrx5_B8RBK_acc_l, H | apply hrx5_B8RBK_acc_r, IH, Hin].
Qed.

Lemma hrx5_B8RBK_acc_trans Q B P : hrx5_B8RBK_acc Q B -> hrx5_B8RBK_acc B P -> hrx5_B8RBK_acc Q P.
Proof.
  unfold hrx5_B8RBK_acc. intros H1 H2. eapply derives_trans; [exact H2|].
  eapply derives_trans; [apply sepcon_derives; [exact H1 | apply derives_refl]|].
  rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_comm (Q -* B) (B -* P)), sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | rewrite sepcon_comm; apply modus_ponens_wand]|].
  rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hrx5_B8RBK_NH sh n (v: list val) p :
  @data_at Noise.CS sh (tarray tuchar n) v p = @data_at HCS sh (tarray tuchar n) v p.
Proof. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

Lemma hrx5_B8RBK_HW sh (v: @reptype HCS t_hsnap) y :
  @data_at HCS sh t_hsnap v y = @data_at W sh t_hsnap v y.
Proof. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

Lemma hrx5_B8RBK_fW sh t gfs (v: @reptype Noise.CS (@nested_field_type Noise.CS t gfs))
  (v': @reptype W (@nested_field_type W t gfs)) p :
  JMeq v v' -> cs_preserve_type Noise.CS W (@coeq _ _ hrx5_B8RBK_cceN) t = true ->
  @field_at Noise.CS sh t gfs v p = @field_at W sh t gfs v' p.
Proof. intros H1 H2. exact (f_equal (fun f => f p) (@field_at_change_composite Noise.CS W _ sh t gfs v v' H1 H2)). Qed.

(* ---- the peer ---- *)
Lemma hrx5_B8RBK_peers PS a sh P Q : sfind PS a = Some (sh, P) ->
  peers_rep (supd PS a Q) = peer_rep sh a Q * peers_rep (sdel PS a).
Proof.
  induction PS as [| [[x sh0] w] PS IH]; simpl; intros Hf; [discriminate |].
  unfold peers_rep in *. destruct (EqDec_val x a) as [Ex | Hne]; [subst x |].
  - inversion Hf; subst. simpl. reflexivity.
  - simpl. rewrite IH by exact Hf. unfold peer_item_rep.
    rewrite <- !sepcon_assoc, (sepcon_comm (peer_rep sh0 x w)). reflexivity.
Qed.

Lemma hrx5_B8RBK_acc_hs sh a Q : hrx5_B8RBK_acc (hs_rep sh (hs_addr a) (p_hs Q)) (peer_rep sh a Q).
Proof.
  unfold peer_rep. apply hrx5_B8RBK_acc_prop; intros _.
  do 7 apply hrx5_B8RBK_acc_l. apply hrx5_B8RBK_acc_r, hrx5_B8RBK_acc_refl.
Qed.

Lemma hrx5_B8RBK_vp_peer sh a Q : sepalg.nonidentity sh -> peer_rep sh a Q |-- valid_pointer a.
Proof.
  intros Hsh. unfold peer_rep. Intros.
  do 10 apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; auto; vm_compute; reflexivity.
Qed.

Lemma hrx5_B8RBK_peer_fc sh a Q : peer_rep sh a Q |-- !! (@field_compatible Noise.CS t_hs [] (hs_addr a)).
Proof.
  unfold peer_rep, hs_rep. Intros. entailer!.
  match goal with H: @field_compatible Noise.CS t_hs [StructField I._state] (hs_addr a) |- _ =>
    destruct H as (? & ? & ? & ? & ?) end.
  repeat split; auto.
Qed.

Section NoiseCS.
#[local] Existing Instance Noise.CS.

Lemma hrx5_B8RBK_acc_state sh h H :
  hrx5_B8RBK_acc (field_at sh t_hs [StructField I._state] (Vint (hs_state H)) h) (hs_rep sh h H).
Proof.
  unfold hs_rep. apply hrx5_B8RBK_acc_prop; intros _.
  do 14 apply hrx5_B8RBK_acc_l. apply hrx5_B8RBK_acc_refl.
Qed.
Lemma hrx5_B8RBK_acc_lic sh h H :
  hrx5_B8RBK_acc (field_at sh t_hs [StructField I._last_initiation_consumption] (Vlong (hs_lic H)) h) (hs_rep sh h H).
Proof.
  unfold hs_rep. apply hrx5_B8RBK_acc_prop; intros _.
  do 13 apply hrx5_B8RBK_acc_l. apply hrx5_B8RBK_acc_r, hrx5_B8RBK_acc_refl.
Qed.
Lemma hrx5_B8RBK_acc_sid sh h H :
  hrx5_B8RBK_acc (field_at sh t_hs [StructField I._static_identity] (hs_sid H) h) (hs_rep sh h H).
Proof.
  unfold hs_rep. apply hrx5_B8RBK_acc_prop; intros _.
  do 12 apply hrx5_B8RBK_acc_l. apply hrx5_B8RBK_acc_r, hrx5_B8RBK_acc_refl.
Qed.
Lemma hrx5_B8RBK_acc_rindex sh h H :
  hrx5_B8RBK_acc (field_at sh t_hs [StructField I._remote_index] (Vint (hs_rindex H)) h) (hs_rep sh h H).
Proof.
  unfold hs_rep. apply hrx5_B8RBK_acc_prop; intros _.
  do 3 apply hrx5_B8RBK_acc_l. apply hrx5_B8RBK_acc_r, hrx5_B8RBK_acc_refl.
Qed.

Ltac hrx5_B8RBK_arr0 :=
  unfold hs_rep; apply hrx5_B8RBK_acc_prop; intros (? & ? & ? & ? & ? & ? & ? & ?).
Ltac hrx5_B8RBK_arr1 :=
  apply hrx5_B8RBK_acc_r;
  match goal with |- hrx5_B8RBK_acc _ (field_at _ _ ?gfs _ ?p) =>
    apply hrx5_B8RBK_acc_pure with (c := field_compatible t_hs gfs p); [entailer! | intros FC] end;
  apply hrx5_B8RBK_acc_eq; rewrite field_at_data_at, field_address_offset by auto;
  unfold hbytes, hs_addr; repeat match goal with H: Zlength ?x = _ |- context [Zlength ?x] => rewrite H end;
  rewrite offset_offset_val, <- hrx5_B8RBK_NH;
  reflexivity.

Lemma hrx5_B8RBK_acc_eph sh a H : hrx5_B8RBK_acc (hbytes sh (hs_eph H) (offset_val 104 a)) (hs_rep sh (hs_addr a) H).
Proof. hrx5_B8RBK_arr0. do 11 apply hrx5_B8RBK_acc_l. hrx5_B8RBK_arr1. Qed.
Lemma hrx5_B8RBK_acc_rstatic sh a H : hrx5_B8RBK_acc (hbytes sh (hs_rstatic H) (offset_val 136 a)) (hs_rep sh (hs_addr a) H).
Proof. hrx5_B8RBK_arr0. do 10 apply hrx5_B8RBK_acc_l. hrx5_B8RBK_arr1. Qed.
Lemma hrx5_B8RBK_acc_reph sh a H : hrx5_B8RBK_acc (hbytes sh (hs_reph H) (offset_val 168 a)) (hs_rep sh (hs_addr a) H).
Proof. hrx5_B8RBK_arr0. do 9 apply hrx5_B8RBK_acc_l. hrx5_B8RBK_arr1. Qed.
Lemma hrx5_B8RBK_acc_ss sh a H : hrx5_B8RBK_acc (hbytes sh (hs_ss H) (offset_val 200 a)) (hs_rep sh (hs_addr a) H).
Proof. hrx5_B8RBK_arr0. do 8 apply hrx5_B8RBK_acc_l. hrx5_B8RBK_arr1. Qed.
Lemma hrx5_B8RBK_acc_psk sh a H : hrx5_B8RBK_acc (hbytes sh (hs_psk H) (offset_val 232 a)) (hs_rep sh (hs_addr a) H).
Proof. hrx5_B8RBK_arr0. do 7 apply hrx5_B8RBK_acc_l. hrx5_B8RBK_arr1. Qed.
Lemma hrx5_B8RBK_acc_hash sh a H : hrx5_B8RBK_acc (hbytes sh (hs_hash H) (offset_val 264 a)) (hs_rep sh (hs_addr a) H).
Proof. hrx5_B8RBK_arr0. do 6 apply hrx5_B8RBK_acc_l. hrx5_B8RBK_arr1. Qed.
Lemma hrx5_B8RBK_acc_ck sh a H : hrx5_B8RBK_acc (hbytes sh (hs_ck H) (offset_val 296 a)) (hs_rep sh (hs_addr a) H).
Proof. hrx5_B8RBK_arr0. do 5 apply hrx5_B8RBK_acc_l. hrx5_B8RBK_arr1. Qed.
Lemma hrx5_B8RBK_acc_ts sh a H : hrx5_B8RBK_acc (hbytes sh (hs_ts H) (offset_val 328 a)) (hs_rep sh (hs_addr a) H).
Proof. hrx5_B8RBK_arr0. do 4 apply hrx5_B8RBK_acc_l. hrx5_B8RBK_arr1. Qed.

End NoiseCS.

(* ---- the accessors from a peer (h = hs_addr a), at the world for main's loads ---- *)
Lemma hrx5_B8RBK_pk_state sh a Q : peer_rep sh a Q |--
  @field_at W sh t_hs [StructField I._state] (Vint (hs_state (p_hs Q))) (hs_addr a) *
  (@field_at W sh t_hs [StructField I._state] (Vint (hs_state (p_hs Q))) (hs_addr a) -* peer_rep sh a Q).
Proof.
  rewrite <- (hrx5_B8RBK_fW sh t_hs [StructField I._state] (Vint (hs_state (p_hs Q))) (Vint (hs_state (p_hs Q)))
    (hs_addr a) (JMeq_refl _)) by (vm_compute; reflexivity).
  exact (hrx5_B8RBK_acc_trans _ _ _ (hrx5_B8RBK_acc_state sh (hs_addr a) (p_hs Q)) (hrx5_B8RBK_acc_hs sh a Q)).
Qed.
Lemma hrx5_B8RBK_pk_lic sh a Q : peer_rep sh a Q |--
  @field_at W sh t_hs [StructField I._last_initiation_consumption] (Vlong (hs_lic (p_hs Q))) (hs_addr a) *
  (@field_at W sh t_hs [StructField I._last_initiation_consumption] (Vlong (hs_lic (p_hs Q))) (hs_addr a) -*
   peer_rep sh a Q).
Proof.
  rewrite <- (hrx5_B8RBK_fW sh t_hs [StructField I._last_initiation_consumption] (Vlong (hs_lic (p_hs Q)))
    (Vlong (hs_lic (p_hs Q))) (hs_addr a) (JMeq_refl _)) by (vm_compute; reflexivity).
  exact (hrx5_B8RBK_acc_trans _ _ _ (hrx5_B8RBK_acc_lic sh (hs_addr a) (p_hs Q)) (hrx5_B8RBK_acc_hs sh a Q)).
Qed.
Lemma hrx5_B8RBK_pk_sid sh a Q : peer_rep sh a Q |--
  @field_at W sh t_hs [StructField I._static_identity] (hs_sid (p_hs Q)) (hs_addr a) *
  (@field_at W sh t_hs [StructField I._static_identity] (hs_sid (p_hs Q)) (hs_addr a) -* peer_rep sh a Q).
Proof.
  rewrite <- (hrx5_B8RBK_fW sh t_hs [StructField I._static_identity] (hs_sid (p_hs Q)) (hs_sid (p_hs Q))
    (hs_addr a) (JMeq_refl _)) by (vm_compute; reflexivity).
  exact (hrx5_B8RBK_acc_trans _ _ _ (hrx5_B8RBK_acc_sid sh (hs_addr a) (p_hs Q)) (hrx5_B8RBK_acc_hs sh a Q)).
Qed.
Lemma hrx5_B8RBK_pk_rindex sh a Q : peer_rep sh a Q |--
  @field_at W sh t_hs [StructField I._remote_index] (Vint (hs_rindex (p_hs Q))) (hs_addr a) *
  (@field_at W sh t_hs [StructField I._remote_index] (Vint (hs_rindex (p_hs Q))) (hs_addr a) -* peer_rep sh a Q).
Proof.
  rewrite <- (hrx5_B8RBK_fW sh t_hs [StructField I._remote_index] (Vint (hs_rindex (p_hs Q)))
    (Vint (hs_rindex (p_hs Q))) (hs_addr a) (JMeq_refl _)) by (vm_compute; reflexivity).
  exact (hrx5_B8RBK_acc_trans _ _ _ (hrx5_B8RBK_acc_rindex sh (hs_addr a) (p_hs Q)) (hrx5_B8RBK_acc_hs sh a Q)).
Qed.
Lemma hrx5_B8RBK_pk_refs sh a Q : peer_rep sh a Q |--
  @field_at W sh t_peer [StructField I._refcount] (Vint (p_refs Q)) a *
  (@field_at W sh t_peer [StructField I._refcount] (Vint (p_refs Q)) a -* peer_rep sh a Q).
Proof.
  rewrite <- (hrx5_B8RBK_fW sh t_peer [StructField I._refcount] (Vint (p_refs Q)) (Vint (p_refs Q)) a (JMeq_refl _))
    by (vm_compute; reflexivity).
  change (hrx5_B8RBK_acc (@field_at Noise.CS sh t_peer [StructField I._refcount] (Vint (p_refs Q)) a) (peer_rep sh a Q)).
  unfold peer_rep. apply hrx5_B8RBK_acc_prop; intros _.
  do 4 apply hrx5_B8RBK_acc_l. apply hrx5_B8RBK_acc_r, hrx5_B8RBK_acc_refl.
Qed.

Lemma hrx5_B8RBK_pk_eph sh a Q : peer_rep sh a Q |--
  hbytes sh (hs_eph (p_hs Q)) (offset_val 104 a) * (hbytes sh (hs_eph (p_hs Q)) (offset_val 104 a) -* peer_rep sh a Q).
Proof. exact (hrx5_B8RBK_acc_trans _ _ _ (hrx5_B8RBK_acc_eph sh a (p_hs Q)) (hrx5_B8RBK_acc_hs sh a Q)). Qed.
Lemma hrx5_B8RBK_pk_rstatic sh a Q : peer_rep sh a Q |--
  hbytes sh (hs_rstatic (p_hs Q)) (offset_val 136 a) * (hbytes sh (hs_rstatic (p_hs Q)) (offset_val 136 a) -* peer_rep sh a Q).
Proof. exact (hrx5_B8RBK_acc_trans _ _ _ (hrx5_B8RBK_acc_rstatic sh a (p_hs Q)) (hrx5_B8RBK_acc_hs sh a Q)). Qed.
Lemma hrx5_B8RBK_pk_reph sh a Q : peer_rep sh a Q |--
  hbytes sh (hs_reph (p_hs Q)) (offset_val 168 a) * (hbytes sh (hs_reph (p_hs Q)) (offset_val 168 a) -* peer_rep sh a Q).
Proof. exact (hrx5_B8RBK_acc_trans _ _ _ (hrx5_B8RBK_acc_reph sh a (p_hs Q)) (hrx5_B8RBK_acc_hs sh a Q)). Qed.
Lemma hrx5_B8RBK_pk_ss sh a Q : peer_rep sh a Q |--
  hbytes sh (hs_ss (p_hs Q)) (offset_val 200 a) * (hbytes sh (hs_ss (p_hs Q)) (offset_val 200 a) -* peer_rep sh a Q).
Proof. exact (hrx5_B8RBK_acc_trans _ _ _ (hrx5_B8RBK_acc_ss sh a (p_hs Q)) (hrx5_B8RBK_acc_hs sh a Q)). Qed.
Lemma hrx5_B8RBK_pk_psk sh a Q : peer_rep sh a Q |--
  hbytes sh (hs_psk (p_hs Q)) (offset_val 232 a) * (hbytes sh (hs_psk (p_hs Q)) (offset_val 232 a) -* peer_rep sh a Q).
Proof. exact (hrx5_B8RBK_acc_trans _ _ _ (hrx5_B8RBK_acc_psk sh a (p_hs Q)) (hrx5_B8RBK_acc_hs sh a Q)). Qed.
Lemma hrx5_B8RBK_pk_hash sh a Q : peer_rep sh a Q |--
  hbytes sh (hs_hash (p_hs Q)) (offset_val 264 a) * (hbytes sh (hs_hash (p_hs Q)) (offset_val 264 a) -* peer_rep sh a Q).
Proof. exact (hrx5_B8RBK_acc_trans _ _ _ (hrx5_B8RBK_acc_hash sh a (p_hs Q)) (hrx5_B8RBK_acc_hs sh a Q)). Qed.
Lemma hrx5_B8RBK_pk_ck sh a Q : peer_rep sh a Q |--
  hbytes sh (hs_ck (p_hs Q)) (offset_val 296 a) * (hbytes sh (hs_ck (p_hs Q)) (offset_val 296 a) -* peer_rep sh a Q).
Proof. exact (hrx5_B8RBK_acc_trans _ _ _ (hrx5_B8RBK_acc_ck sh a (p_hs Q)) (hrx5_B8RBK_acc_hs sh a Q)). Qed.
Lemma hrx5_B8RBK_pk_ts sh a Q : peer_rep sh a Q |--
  hbytes sh (hs_ts (p_hs Q)) (offset_val 328 a) * (hbytes sh (hs_ts (p_hs Q)) (offset_val 328 a) -* peer_rep sh a Q).
Proof. exact (hrx5_B8RBK_acc_trans _ _ _ (hrx5_B8RBK_acc_ts sh a (p_hs Q)) (hrx5_B8RBK_acc_hs sh a Q)). Qed.

(* ---- the nodes: one field of one node (the others stay in the wand) ---- *)
Definition hrx5_B8RBK_nv (N: hnode4) (nx: val) : @reptype CKS t_hnode4 :=
  (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))).

(* the node N of the list, given an accessor of its value Q *)
Lemma hrx5_B8RBK_nodes_acc (Q: mpred) N : forall NS l, In N NS ->
  (forall nx, hrx5_B8RBK_acc Q (@data_at CKS Ews t_hnode4 (hrx5_B8RBK_nv N nx) (hn_addr N))) ->
  hrx5_B8RBK_acc Q (hnodes_rep4 W l NS).
Proof.
  induction NS as [|N0 NS IH]; intros l Hin HQ; [destruct Hin|]. cbn [hnodes_rep4].
  apply hrx5_B8RBK_acc_prop; intros Hl. apply hrx5_B8RBK_acc_ex; intros nx.
  destruct Hin as [<-|Hin].
  - subst l. apply hrx5_B8RBK_acc_l, hrx5_B8RBK_acc_l, hrx5_B8RBK_acc_r. apply HQ.
  - apply hrx5_B8RBK_acc_r, IH; auto.
Qed.

Lemma hrx5_B8RBK_nfld_p N nx :
  hrx5_B8RBK_acc (@field_at W Ews t_hnode4 [StructField HC._p] (hn_p N) (hn_addr N))
    (@data_at CKS Ews t_hnode4 (hrx5_B8RBK_nv N nx) (hn_addr N)).
Proof.
  unfold hrx5_B8RBK_acc, hrx5_B8RBK_nv.
  rewrite <- (@field_at_change_composite CKS W _ Ews t_hnode4 [StructField HC._p] (hn_p N) (hn_p N) (JMeq_refl _))
    by (vm_compute; reflexivity).
  eapply derives_trans; [apply andp_right; [apply (@data_at_local_facts CKS) | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  eapply derives_trans; [apply (@gfield_ramif CKS Ews t_hnode4 [] (StructField HC._p) _ (hn_p N) (hn_addr N));
    [apply JMeq_refl | auto with field_compatible] |].
  apply sepcon_derives; [apply derives_refl|]. apply (allp_left _ (hn_p N)). apply derives_refl.
Qed.

Lemma hrx5_B8RBK_nfld_refs N nx :
  hrx5_B8RBK_acc (@field_at W Ews t_hnode4 [StructField HC._refs] (hn_refs N) (hn_addr N))
    (@data_at CKS Ews t_hnode4 (hrx5_B8RBK_nv N nx) (hn_addr N)).
Proof.
  unfold hrx5_B8RBK_acc, hrx5_B8RBK_nv.
  rewrite <- (@field_at_change_composite CKS W _ Ews t_hnode4 [StructField HC._refs] (hn_refs N) (hn_refs N) (JMeq_refl _))
    by (vm_compute; reflexivity).
  eapply derives_trans; [apply andp_right; [apply (@data_at_local_facts CKS) | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  eapply derives_trans; [apply (@gfield_ramif CKS Ews t_hnode4 [] (StructField HC._refs) _ (hn_refs N) (hn_addr N));
    [apply JMeq_refl | auto with field_compatible] |].
  apply sepcon_derives; [apply derives_refl|]. apply (allp_left _ (hn_refs N)). apply derives_refl.
Qed.

(* the rest snapshot, at CKS (pr_same's specification) *)
Lemma hrx5_B8RBK_nfld_rest N nx :
  hrx5_B8RBK_acc (@field_at CKS Ews t_hnode4 [StructField HC._rest] (hn_rest N) (hn_addr N))
    (@data_at CKS Ews t_hnode4 (hrx5_B8RBK_nv N nx) (hn_addr N)).
Proof.
  unfold hrx5_B8RBK_acc, hrx5_B8RBK_nv.
  eapply derives_trans; [apply andp_right; [apply (@data_at_local_facts CKS) | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  eapply derives_trans; [apply (@gfield_ramif CKS Ews t_hnode4 [] (StructField HC._rest) _ (hn_rest N) (hn_addr N));
    [apply JMeq_refl | auto with field_compatible] |].
  apply sepcon_derives; [apply derives_refl|]. apply (allp_left _ (hn_rest N)). apply derives_refl.
Qed.

(* the handshake snapshot, at CKS *)
Lemma hrx5_B8RBK_nfld_snap N nx :
  hrx5_B8RBK_acc (@field_at CKS Ews t_hnode4 [StructField HC._snap] (hn_snap N) (hn_addr N))
    (@data_at CKS Ews t_hnode4 (hrx5_B8RBK_nv N nx) (hn_addr N)).
Proof.
  unfold hrx5_B8RBK_acc, hrx5_B8RBK_nv.
  eapply derives_trans; [apply andp_right; [apply (@data_at_local_facts CKS) | apply derives_refl]|].
  apply derives_extract_prop. intros [FC _].
  eapply derives_trans; [apply (@gfield_ramif CKS Ews t_hnode4 [] (StructField HC._snap) _ (hn_snap N) (hn_addr N));
    [apply JMeq_refl | auto with field_compatible] |].
  apply sepcon_derives; [apply derives_refl|]. apply (allp_left _ (hn_snap N)). apply derives_refl.
Qed.

(* the field snap as a t_hsnap at s = offset_val 8 node, at W *)
Lemma hrx5_B8RBK_snap_at (v: @reptype CKS t_hsnap) x : @field_compatible CKS t_hnode4 [] x ->
  @field_at CKS Ews t_hnode4 [StructField HC._snap] v x = @data_at W Ews t_hsnap v (offset_val 8 x).
Proof.
  intros FC. rewrite (@field_at_data_at CKS), (@field_address_offset CKS) by auto with field_compatible.
  change (@nested_field_offset CKS t_hnode4 [StructField HC._snap]) with 8.
  change (@nested_field_type CKS t_hnode4 [StructField HC._snap]) with t_hsnap.
  apply data_at_cs_eq; [apply JMeq_refl | reflexivity].
Qed.

(* ---- byte arrays of a handshake snapshot (at s = offset_val 8 node) ---- *)
Section HCSsnap.
#[local] Existing Instance HCS.
Ltac hrx5_B8RBK_snap_tac f :=
  intros L; rewrite <- hrx5_B8RBK_HW;
  match goal with |- data_at ?sh _ _ ?y |-- _ =>
    assert_PROP (field_compatible t_hsnap [] y) by entailer!;
    unfold hsnap_val; unfold_data_at (data_at _ _ _ y);
    rewrite (field_at_data_at sh t_hsnap [StructField f])
  end;
  rewrite !field_address_offset by auto with field_compatible; simpl; unfold hbytes; rewrite L; cancel;
  rewrite <- wand_sepcon_adjoint; cancel.

Lemma hrx5_B8RBK_sn_eph sh sn y : Zlength (hs_eph (sn_hs sn)) = 32 ->
  @data_at W sh t_hsnap (hsnap_val sn) y |--
  hbytes sh (hs_eph (sn_hs sn)) (offset_val 48 y) *
  (hbytes sh (hs_eph (sn_hs sn)) (offset_val 48 y) -* @data_at W sh t_hsnap (hsnap_val sn) y).
Proof. hrx5_B8RBK_snap_tac HH._ephemeral_private. Qed.
Lemma hrx5_B8RBK_sn_rstatic sh sn y : Zlength (hs_rstatic (sn_hs sn)) = 32 ->
  @data_at W sh t_hsnap (hsnap_val sn) y |--
  hbytes sh (hs_rstatic (sn_hs sn)) (offset_val 80 y) *
  (hbytes sh (hs_rstatic (sn_hs sn)) (offset_val 80 y) -* @data_at W sh t_hsnap (hsnap_val sn) y).
Proof. hrx5_B8RBK_snap_tac HH._remote_static. Qed.
Lemma hrx5_B8RBK_sn_ss sh sn y : Zlength (hs_ss (sn_hs sn)) = 32 ->
  @data_at W sh t_hsnap (hsnap_val sn) y |--
  hbytes sh (hs_ss (sn_hs sn)) (offset_val 144 y) *
  (hbytes sh (hs_ss (sn_hs sn)) (offset_val 144 y) -* @data_at W sh t_hsnap (hsnap_val sn) y).
Proof. hrx5_B8RBK_snap_tac HH._precomputed_static_static. Qed.
Lemma hrx5_B8RBK_sn_psk sh sn y : Zlength (hs_psk (sn_hs sn)) = 32 ->
  @data_at W sh t_hsnap (hsnap_val sn) y |--
  hbytes sh (hs_psk (sn_hs sn)) (offset_val 176 y) *
  (hbytes sh (hs_psk (sn_hs sn)) (offset_val 176 y) -* @data_at W sh t_hsnap (hsnap_val sn) y).
Proof. hrx5_B8RBK_snap_tac HH._preshared_key. Qed.

(* ci.st.ck (offset 0) and ci.st.h (offset 32) *)
Lemma hrx5_B8RBK_ci_st sh ck h key spub ts ci : Zlength ck = 32 -> Zlength h = 32 ->
  data_at sh t_mcinit (mcinit_val ck h key spub ts) ci |--
  hbytes sh ck ci * hbytes sh h (offset_val 32 ci) *
  (hbytes sh ck ci * hbytes sh h (offset_val 32 ci) -* data_at sh t_mcinit (mcinit_val ck h key spub ts) ci).
Proof.
  intros L1 L2. assert_PROP (field_compatible t_mcinit [] ci) by entailer!.
  unfold mcinit_val. unfold_data_at (data_at _ _ _ ci).
  rewrite (field_at_data_at sh t_mcinit [StructField HH._st]).
  rewrite !field_address_offset by auto with field_compatible.
  change (nested_field_type t_mcinit (DOT HH._st)) with t_mstate.
  change (nested_field_offset t_mcinit (DOT HH._st)) with 0.
  rewrite isptr_offset_val_zero by (destruct H; auto).
  assert_PROP (field_compatible t_mstate [] ci) as FCs by entailer!.
  unfold_data_at (data_at _ t_mstate _ ci).
  rewrite (field_at_data_at sh t_mstate [StructField HH._ck]), (field_at_data_at sh t_mstate [StructField HH._h]).
  rewrite !field_address_offset by auto with field_compatible.
  simpl. rewrite isptr_offset_val_zero by (destruct H; auto). unfold hbytes. rewrite L1, L2. cancel.
  rewrite <- wand_sepcon_adjoint. cancel.
Qed.
End HCSsnap.

(* ---- the handshake's entry (in the pool of B's index table T, links from T), at h = hs_addr a, at W ---- *)
Lemma hrx5_B8RBK_entry_eq sh h (v: @reptype Noise.CS t_entry_s) : @field_compatible Noise.CS t_hs [] h ->
  @data_at Noise.CS sh t_entry_s v h = @field_at W sh t_hs [StructField I._entry] v h.
Proof.
  intros FC. rewrite <- (hrx5_B8RBK_fW sh t_hs [StructField I._entry] v v h (JMeq_refl _)) by (vm_compute; reflexivity).
  rewrite (@field_at_data_at Noise.CS sh t_hs [StructField I._entry]), field_address_offset by auto with field_compatible.
  simpl. rewrite isptr_offset_val_zero by (destruct FC; auto). reflexivity.
Qed.

Lemma hrx5_B8RBK_in_saddrs {A: Type} : forall (D: list (val * share * A)) x, In x (saddrs D) ->
  exists sh v, In (x, sh, v) D /\ sfind D x = Some (sh, v).
Proof.
  induction D as [|[[y sh] v] D IH]; simpl; intros x Hin; [contradiction|].
  destruct (EqDec_val y x) as [<-|Hne].
  - exists sh, v. auto.
  - destruct Hin as [->|Hin]; [congruence|]. destruct (IH x Hin) as (sh' & v' & H1 & H2). exists sh', v'. auto.
Qed.

Lemma hrx5_B8RBK_entry tab T x : In x (saddrs (t_D T)) ->
  Forall (fun d => match d with (_, sh, _) => sh = Ews end) (t_D T) ->
  @field_compatible Noise.CS t_hs [] x ->
  itable Tsh tab T |--
  @field_at W Ews t_hs [StructField I._entry] (entry_val (t_entry_d T x) (succ_in (t_L T) x) (vin x (t_L T))) x *
  (@field_at W Ews t_hs [StructField I._entry] (entry_val (t_entry_d T x) (succ_in (t_L T) x) (vin x (t_L T))) x -*
   itable Tsh tab T).
Proof.
  intros Hin Hsh FC.
  destruct (hrx5_B8RBK_in_saddrs (t_D T) x Hin) as (sh & E & HinE & Hf).
  assert (Hs: sh = Ews) by (rewrite Forall_forall in Hsh; exact (Hsh _ HinE)). subst sh.
  assert (HE: t_entry_d T x = E) by (unfold t_entry_d, t_entry; rewrite Hf; reflexivity). rewrite HE.
  change (hrx5_B8RBK_acc
    (@field_at W Ews t_hs [StructField I._entry] (entry_val E (succ_in (t_L T) x) (vin x (t_L T))) x)
    (itable Tsh tab T)).
  unfold itable. apply hrx5_B8RBK_acc_prop; intros _. apply hrx5_B8RBK_acc_r.
  apply (hrx5_B8RBK_acc_iter _ _ (x, Ews, E)); [exact HinE |].
  apply hrx5_B8RBK_acc_eq. unfold pool_item_rep, entry_at.
  rewrite hrx5_B8RBK_entry_eq by exact FC. reflexivity.
Qed.

(* ---- valid pointers for the pointer comparisons ---- *)
Lemma hrx5_B8RBK_vp_sid sh wg D : sepalg.nonidentity sh -> device_rep sh wg D |-- valid_pointer (id_addr wg).
Proof.
  intros Hsh. unfold device_rep, identity_rep. Intros. Intros lk.
  apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
  apply sepcon_valid_pointer2. apply data_at_valid_ptr; auto. vm_compute; reflexivity.
Qed.

(* ---- the message ---- *)
Section NM.
#[local] Existing Instance Noise.CS.
Lemma hrx5_B8RBK_msg_eph sh m M : init_rep sh m M |--
  hbytes sh (im_eph M) (offset_val 8 m) * (hbytes sh (im_eph M) (offset_val 8 m) -* init_rep sh m M).
Proof.
  unfold init_rep. Intros. destruct H as (L1 & L2 & L3 & L4 & L5).
  assert_PROP (field_compatible t_init [] m) by entailer!. unfold_data_at (data_at _ _ _ m).
  rewrite (field_at_data_at sh t_init [StructField I._unencrypted_ephemeral]).
  rewrite !field_address_offset by auto with field_compatible. simpl. unfold hbytes.
  rewrite L1, <- !hrx5_B8RBK_NH. cancel.
  rewrite <- wand_sepcon_adjoint. apply andp_right; [apply prop_right; repeat split; auto | cancel].
Qed.
End NM.

Lemma hrx5_B8RBK_cs_eq {cs1 cs2} {CCE: change_composite_env cs1 cs2} (sh: share) (t: type) (v1: @reptype cs1 t)
  (v2: @reptype cs2 t) (p: val) :
  JMeq v1 v2 -> cs_preserve_type cs1 cs2 (coeq _ _) t = true ->
  @data_at cs1 sh t v1 p = @data_at cs2 sh t v2 p.
Proof. intros. exact (f_equal (fun f => f p) (@data_at_change_composite cs1 cs2 CCE sh t v1 v2 H H0)). Qed.

(* the message at the world compspecs (for the load of msg->sender_index) *)
Lemma hrx5_B8RBK_init_W sh m M :
  init_rep sh m M = !! im_ok M && @data_at W sh t_init (init_val M) m.
Proof.
  unfold init_rep.
  rewrite (@hrx5_B8RBK_cs_eq Noise.CS W _ sh t_init (init_val M) (init_val M) m)
    by (apply JMeq_refl || prove_cs_preserve_type).
  reflexivity.
Qed.

