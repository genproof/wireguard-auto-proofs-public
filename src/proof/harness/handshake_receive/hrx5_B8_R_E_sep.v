(* law handshake_receive, phase B8 branch R segment E: separation-logic access to
   the handshake's entry of the accepted peer in the index table's pool. *)
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
Local Open Scope logic.

Notation W := W_handshake_receive.
#[local] Instance hrx5_B8RES_cceN : change_composite_env Noise.CS W.
Proof. make_cs_preserve Noise.CS W. Defined.

Definition hrx5_B8RES_acc (Q P: mpred) : Prop := P |-- Q * (Q -* P).

Lemma hrx5_B8RES_mp (Q P: mpred) : Q * (Q -* P) |-- P.
Proof. apply wand_frame_elim. Qed.

Lemma hrx5_B8RES_acc_refl Q : hrx5_B8RES_acc Q Q.
Proof.
  unfold hrx5_B8RES_acc. eapply derives_trans; [apply (derives_refl' _ _ (eq_sym (sepcon_emp Q)))|].
  apply sepcon_derives; [apply derives_refl|]. rewrite <- wand_sepcon_adjoint. rewrite emp_sepcon. apply derives_refl.
Qed.

Lemma hrx5_B8RES_acc_eq Q A : Q = A -> hrx5_B8RES_acc Q A.
Proof. intros ->. apply hrx5_B8RES_acc_refl. Qed.

Lemma hrx5_B8RES_acc_l Q A F : hrx5_B8RES_acc Q A -> hrx5_B8RES_acc Q (A * F).
Proof.
  unfold hrx5_B8RES_acc. intros H. apply derives_trans with (Q * (Q -* A) * F).
  { apply sepcon_derives; [exact H | apply derives_refl]. }
  rewrite (sepcon_assoc Q). apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  rewrite (sepcon_assoc (Q -* A)), (sepcon_comm F Q), <- (sepcon_assoc (Q -* A)), (sepcon_comm (Q -* A) Q).
  apply sepcon_derives; [apply modus_ponens_wand | apply derives_refl].
Qed.

Lemma hrx5_B8RES_acc_r Q A F : hrx5_B8RES_acc Q A -> hrx5_B8RES_acc Q (F * A).
Proof. intros H. rewrite sepcon_comm. apply hrx5_B8RES_acc_l, H. Qed.

Lemma hrx5_B8RES_acc_prop Q (c: Prop) A : (c -> hrx5_B8RES_acc Q A) -> hrx5_B8RES_acc Q (!! c && A).
Proof.
  unfold hrx5_B8RES_acc. intros H. apply derives_extract_prop. intros Hc.
  eapply derives_trans; [apply H, Hc|]. apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. apply andp_right; [apply prop_right, Hc|]. rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

Lemma hrx5_B8RES_acc_iter {X: Type} Q (f: X -> mpred) x l :
  In x l -> hrx5_B8RES_acc Q (f x) -> hrx5_B8RES_acc Q (iter_sepcon f l).
Proof.
  intros Hin H. induction l as [|y l IH]; [contradiction|]. simpl.
  destruct Hin as [<-|Hin]; [apply hrx5_B8RES_acc_l, H | apply hrx5_B8RES_acc_r, IH, Hin].
Qed.

Lemma hrx5_B8RES_fW sh t gfs (v: @reptype Noise.CS (@nested_field_type Noise.CS t gfs))
  (v': @reptype W (@nested_field_type W t gfs)) p :
  JMeq v v' -> cs_preserve_type Noise.CS W (@coeq _ _ hrx5_B8RES_cceN) t = true ->
  @field_at Noise.CS sh t gfs v p = @field_at W sh t gfs v' p.
Proof. intros H1 H2. exact (f_equal (fun f => f p) (@field_at_change_composite Noise.CS W _ sh t gfs v v' H1 H2)). Qed.

Lemma hrx5_B8RES_entry_eq sh h (v: @reptype Noise.CS t_entry_s) : @field_compatible Noise.CS t_hs [] h ->
  @data_at Noise.CS sh t_entry_s v h = @field_at W sh t_hs [StructField I._entry] v h.
Proof.
  intros FC. rewrite <- (hrx5_B8RES_fW sh t_hs [StructField I._entry] v v h (JMeq_refl _)) by (vm_compute; reflexivity).
  rewrite (@field_at_data_at Noise.CS sh t_hs [StructField I._entry]), field_address_offset by auto with field_compatible.
  simpl. rewrite isptr_offset_val_zero by (destruct FC; auto). reflexivity.
Qed.

Lemma hrx5_B8RES_in_saddrs {A: Type} : forall (D: list (val * share * A)) x, In x (saddrs D) ->
  exists sh v, In (x, sh, v) D /\ sfind D x = Some (sh, v).
Proof.
  induction D as [|[[y sh] v] D IH]; simpl; intros x Hin; [contradiction|].
  destruct (EqDec_val y x) as [<-|Hne].
  - exists sh, v. auto.
  - destruct Hin as [->|Hin]; [congruence|]. destruct (IH x Hin) as (sh' & v' & H1 & H2). exists sh', v'. auto.
Qed.

Lemma hrx5_B8RES_entry tab T x : In x (saddrs (t_D T)) ->
  Forall (fun d => match d with (_, sh, _) => sh = Ews end) (t_D T) ->
  @field_compatible Noise.CS t_hs [] x ->
  itable Tsh tab T |--
  @field_at W Ews t_hs [StructField I._entry] (entry_val (t_entry_d T x) (succ_in (t_L T) x) (vin x (t_L T))) x *
  (@field_at W Ews t_hs [StructField I._entry] (entry_val (t_entry_d T x) (succ_in (t_L T) x) (vin x (t_L T))) x -*
   itable Tsh tab T).
Proof.
  intros Hin Hsh FC.
  destruct (hrx5_B8RES_in_saddrs (t_D T) x Hin) as (sh & E & HinE & Hf).
  assert (Hs: sh = Ews) by (rewrite Forall_forall in Hsh; exact (Hsh _ HinE)). subst sh.
  assert (HE: t_entry_d T x = E) by (unfold t_entry_d, t_entry; rewrite Hf; reflexivity). rewrite HE.
  change (hrx5_B8RES_acc
    (@field_at W Ews t_hs [StructField I._entry] (entry_val E (succ_in (t_L T) x) (vin x (t_L T))) x)
    (itable Tsh tab T)).
  unfold itable. apply hrx5_B8RES_acc_prop; intros _. apply hrx5_B8RES_acc_r.
  apply (hrx5_B8RES_acc_iter _ _ (x, Ews, E)); [exact HinE |].
  apply hrx5_B8RES_acc_eq. unfold pool_item_rep, entry_at.
  rewrite hrx5_B8RES_entry_eq by exact FC. reflexivity.
Qed.

(* the peers: the updated one apart *)
Lemma hrx5_B8RES_peers PS a sh P Q : sfind PS a = Some (sh, P) ->
  peers_rep (supd PS a Q) = peer_rep sh a Q * peers_rep (sdel PS a).
Proof.
  induction PS as [| [[x sh0] w] PS IH]; simpl; intros Hf; [discriminate |].
  unfold peers_rep in *. destruct (EqDec_val x a) as [Ex | Hne]; [subst x |].
  - inversion Hf; subst. simpl. reflexivity.
  - simpl. rewrite IH by exact Hf. unfold peer_item_rep.
    rewrite <- !sepcon_assoc, (sepcon_comm (peer_rep sh0 x w)). reflexivity.
Qed.

(* the handshake of a peer in the list is a field_compatible t_hs *)
Lemma hrx5_B8RES_hs_fc PS a sh P Q : sfind PS a = Some (sh, P) ->
  peers_rep (supd PS a Q) |-- !! @field_compatible Noise.CS t_hs [] (hs_addr a).
Proof.
  intros Hf. rewrite (hrx5_B8RES_peers PS a sh P Q Hf). unfold peer_rep, hs_rep. Intros.
  sep_apply (@field_at_local_facts Noise.CS sh t_hs [StructField I._state]). Intros.
  apply prop_right. apply field_compatible_cons in H1. simpl in H1. tauto.
Qed.

(* the peers' addresses are pointers *)
Lemma hrx5_B8RES_ptrs PS : peers_rep PS |-- !! Forall (fun x => match x with (a, _, _) => isptr a end) PS.
Proof.
  induction PS as [| [[a sh] P] PS IH]; unfold peers_rep in *; simpl.
  - entailer!.
  - sep_apply IH. unfold peer_item_rep at 1, peer_rep. entailer!.
Qed.
