(* law config_any: the separation-logic facts of the stack peer q and of the
   returns (hcf5_sepH, hcf5_defs.v): q's memory split into its handshake, cookie, device field and the rest, and
   joined back; the device and the index table back to memory. The statement is
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.config_any.hcf5_world.
Require Import WgNoise.proof.harness.config_any.hcf5_cut.
Require Import WgNoise.proof.harness.config_any.hcf5_globals.
Require Import WgNoise.proof.harness.config_any.hcf5_spec.
Require Import WgNoise.proof.harness.config_any.hcf5_defs.
Require Import WgNoise.proof.harness.config_any.hcf5_conv.
Require Import WgNoise.proof.harness.config_any.hcf5_pure.
Require WgNoise.harness.x_config_any.code.

#[local] Existing Instance W_config_any.
Local Open Scope Z_scope.

Local Open Scope logic.

(* ---- (1) and (2): q's struct, split and joined ---- *)
Section NoiseSep.
#[local] Existing Instance Noise.CS.

Lemma hcf5_sep_fc_dev sh q : field_at_ sh t_peer [StructField I._device] q |-- !! field_compatible t_peer [] q.
Proof.
  unfold field_at_. rewrite field_at_compatible'. Intros. apply prop_right.
  apply field_compatible_cons in H. destruct H; auto.
Qed.

Lemma hcf5_sep_hs_field sh q : field_compatible t_peer [] q ->
  field_at_ sh t_peer [StructField I._handshake] q = data_at_ sh t_hs (hs_addr q).
Proof.
  intros FC. unfold field_at_. rewrite field_at_data_at.
  rewrite field_address_offset by auto with field_compatible. reflexivity.
Qed.

Lemma hcf5_sep_ck_field sh q : field_compatible t_peer [] q ->
  field_at_ sh t_peer [StructField I._latest_cookie] q = data_at_ sh t_cookie (cookie_addr q).
Proof.
  intros FC. unfold field_at_. rewrite field_at_data_at.
  rewrite field_address_offset by auto with field_compatible. reflexivity.
Qed.

Lemma hcf5_sep_unfold q : data_at_ Tsh t_peer q =
  field_at_ Tsh t_peer [StructField I._device] q * field_at_ Tsh t_peer [StructField I._handshake] q *
  field_at_ Tsh t_peer [StructField I._latest_cookie] q * hcf5_qrest q.
Proof.
  unfold data_at_ at 1, field_at_ at 1.
  unfold_field_at 1%nat.
  unfold hcf5_qrest.
  repeat match goal with |- ?L = _ => match L with context [@field_at Noise.CS Tsh t_peer ?g ?v q] =>
    change (@field_at Noise.CS Tsh t_peer g v q) with (@field_at_ Noise.CS Tsh t_peer g q) end end.
  apply pred_ext; cancel.
Qed.

Lemma hcf5_sep_q_split q : data_at_ Tsh t_peer q =
  field_at_ Tsh t_peer [StructField I._device] q * data_at_ Tsh t_hs (hs_addr q) *
  data_at_ Tsh t_cookie (cookie_addr q) * hcf5_qrest q.
Proof.
  apply pred_ext.
  - assert_PROP (field_compatible t_peer [] q) as FC by entailer!.
    rewrite hcf5_sep_unfold, <- hcf5_sep_hs_field, <- hcf5_sep_ck_field by exact FC. cancel.
  - assert_PROP (field_compatible t_peer [] q) as FC by (sep_apply (hcf5_sep_fc_dev Tsh q); entailer!).
    rewrite hcf5_sep_unfold, <- hcf5_sep_hs_field, <- hcf5_sep_ck_field by exact FC. cancel.
Qed.

Lemma hcf5_sep_q_join q H E n h C : hs_mem false Tsh q (hcf5_qpeer H) * entry_at Tsh (hs_addr q) E n h *
  cookie_rep Tsh (cookie_addr q) C * hcf5_qrest q |-- data_at_ Tsh t_peer q.
Proof.
  unfold hs_mem. simpl.
  sep_apply (prot_rep3_hs_whole Tsh (hs_addr q) H E n h).
  unfold cookie_rep. Intros lk. sep_apply (data_at_data_at_ Tsh t_cookie (cookie_val C lk) (cookie_addr q)).
  rewrite hcf5_sep_q_split. cancel.
Qed.

(* (3): the device, as law consume_initiation_any's hci5_close_dev *)
Lemma hcf5_sep_dev sh wg D : device_rep sh wg D |-- data_at_ sh t_dev wg.
Proof.
  unfold device_rep, identity_rep, checker_rep. Intros lk1 lk2.
  pose (v := (d_dev D, ((bytes (id_pub (d_id D)), (bytes (id_priv (d_id D)), (lk2, Val.of_bool (id_has (d_id D))))),
         ((bytes (cc_secret (d_cc D)), (bytes (cc_ekey (d_cc D)), (bytes (cc_mkey (d_cc D)),
           (Vlong (cc_birth (d_cc D)), (lk1, cc_dev (d_cc D)))))), (d_ptab D, d_itab D)))) : @reptype Noise.CS t_dev).
  eapply derives_trans; [| apply (@data_at_data_at_ Noise.CS sh t_dev v wg)].
  unfold id_addr, cc_addr, OFS_DEV_IDENTITY, OFS_DEV_CHECKER.
  unfold_data_at (data_at sh t_dev v wg).
  rewrite (field_at_data_at sh t_dev (DOT I._static_identity)), (field_at_data_at sh t_dev (DOT I._cookie_checker)).
  rewrite !field_address_offset by auto with field_compatible.
  subst v. simpl. cancel.
Qed.

End NoiseSep.

(* ---- (4): the index table back to memory ---- *)
Lemma hcf5_sep_sfind (D: list (val * share * entry)) a sh E :
  NoDup (saddrs D) -> In (a, sh, E) D -> sfind D a = Some (sh, E).
Proof.
  induction D as [| [[x shx] Ex] D IH]; simpl; intros ND HI; [contradiction |].
  inv ND. destruct (EqDec_val x a) as [e | n].
  - subst x. destruct HI as [HI | HI]; [inv HI; reflexivity |].
    exfalso. apply H1. apply (prot_rep3_saddrs_in D a sh E HI).
  - destruct HI as [HI | HI]; [inv HI; congruence |]. apply IH; auto.
Qed.

Lemma hcf5_sep_kents (L': list val) (f: val -> share) : forall (D: list (val * share * entry)) (KE: list kent4),
  saddrs D = map ke_addr KE -> (forall x sh E, In (x, sh, E) D -> sh = f x) ->
  Forall (fun e => f (ke_addr e) = Ews) KE ->
  iter_sepcon (pool_item_rep L') D |-- iter_sepcon (fun e => @data_at_ Noise.CS Ews t_entry_s (ke_addr e)) KE.
Proof.
  induction D as [| [[a sh] E] D IH]; intros KE HA HS HF; destruct KE as [| e KE]; try discriminate HA.
  - simpl. apply derives_refl.
  - simpl in HA. inv HA. inv HF.
    assert (sh = Ews) by (rewrite (HS (ke_addr e) sh E) by (left; reflexivity); assumption). subst sh.
    simpl. apply sepcon_derives.
    + unfold pool_item_rep, entry_at. apply data_at_data_at_.
    + apply IH; auto. intros x sh' E' HI. apply (HS x sh' E'). right; exact HI.
Qed.

Lemma hcf5_sep_one (L': list val) (f: val -> share) (D: list (val * share * entry)) a :
  saddrs D = [a] -> (forall x sh E, In (x, sh, E) D -> sh = f x) -> f a = Tsh ->
  iter_sepcon (pool_item_rep L') D |-- EX E: entry, EX n: val, EX h: bool, entry_at Tsh a E n h.
Proof.
  intros HA HS HT. destruct D as [| [[x sh] E] [| d D]]; try discriminate HA. simpl in HA. inv HA.
  assert (sh = Tsh) by (rewrite (HS a sh E) by (left; reflexivity); assumption). subst sh.
  simpl. rewrite sepcon_emp. unfold pool_item_rep. Exists E (succ_in L' a) (vin a L'). apply derives_refl.
Qed.

Lemma hcf5_sep_itab L KE qin T : hcf5_T_ok L KE qin T ->
  itable Tsh (l_it L) T |--
  @data_at_ Noise.CS Tsh t_itab (l_it L) *
  iter_sepcon (fun e => @data_at_ Noise.CS Ews t_entry_s (ke_addr e)) KE *
  (EX E: entry, EX n: val, EX h: bool, entry_at Tsh (hs_addr (l_p L)) E n h) *
  (if qin then EX E: entry, EX n: val, EX h: bool, entry_at Tsh (hs_addr (l_q L)) E n h else emp).
Proof.
  intros (HA & HK & HP & _ & HQ).
  unfold itable. Intros. rename H into WF. destruct WF as (_ & _ & ND & _).
  assert (HS: forall x sh E, In (x, sh, E) (t_D T) -> sh = hcf5_tsh T x).
  { intros x sh E HI. unfold hcf5_tsh. rewrite (hcf5_sep_sfind _ x sh E ND HI). reflexivity. }
  unfold saddrs in HA. apply map_eq_app in HA. destruct HA as (D1 & D23 & HD & H1 & H23).
  apply map_eq_app in H23. destruct H23 as (D2 & D3 & HD23 & H2 & H3).
  rewrite HD, HD23 in HS. rewrite HD, HD23. rewrite !iter_sepcon_app.
  sep_apply (@data_at_data_at_ Noise.CS Tsh t_itab (hd nullval (t_L T)) (l_it L)).
  sep_apply (hcf5_sep_kents (t_L T) (hcf5_tsh T) D2 KE H2
               ltac:(intros x sh E HI; apply (HS x sh E); apply in_or_app; right; apply in_or_app; left; exact HI)
               ltac:(eapply Forall_impl; [| exact HK]; intros e [He _]; exact He)).
  sep_apply (hcf5_sep_one (t_L T) (hcf5_tsh T) D3 (hs_addr (l_p L)) H3
               ltac:(intros x sh E HI; apply (HS x sh E); apply in_or_app; right; apply in_or_app; right; exact HI) HP).
  destruct qin.
  - destruct (HQ eq_refl) as (HQ1 & _ & _).
    sep_apply (hcf5_sep_one (t_L T) (hcf5_tsh T) D1 (hs_addr (l_q L)) H1
                 ltac:(intros x sh E HI; apply (HS x sh E); apply in_or_app; left; exact HI) HQ1).
    cancel.
  - destruct D1; [| discriminate H1]. simpl. cancel.
Qed.

Theorem hcf5_sep_ok : hcf5_sepH.
Proof.
  split; [| split; [| split]].
  - apply hcf5_sep_q_split.
  - apply hcf5_sep_q_join.
  - apply hcf5_sep_dev.
  - apply hcf5_sep_itab.
Qed.
