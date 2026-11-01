(* law consume_response_any: the return's separation logic (the port of v1's
   hcr3_close.v): the device back to its struct, the index table and the peers back to the table's struct, each
   peer's whole struct at the world (hnodes_free) and each kent's entry (kents_free). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_model.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_conv.
Local Open Scope logic.

Section Dev.
#[local] Existing Instance Noise.CS.
Lemma hcr5_close_dev sh wg D : device_rep sh wg D |-- data_at_ sh t_dev wg.
Proof.
  unfold device_rep, identity_rep, checker_rep. Intros lk1 lk2.
  (* no padding at t_dev's level: the identity's (69..72) is inside its data_at t_sid *)
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
End Dev.

(* the kents' pool entries give back their structs *)
Lemma hcr5_close_kents PS : forall KE D,
  Forall2 (hcr5_ke_ok PS) (hcr5_ka KE) D ->
  iter_sepcon hcr5_pool_entry D |--
  iter_sepcon (fun e => @data_at_ Noise.CS Ews t_entry_s (ke_addr e)) KE.
Proof.
  induction KE as [| e KE IH]; intros D H; simpl in H; inv H.
  - apply derives_refl.
  - destruct y as [[a sh] E]. destruct H2 as (-> & -> & _ & _). simpl.
    unfold hcr5_pool_entry at 1. Intros n h.
    unfold entry_at. sep_apply (@data_at_data_at_ Noise.CS Ews t_entry_s). apply sepcon_derives; [apply derives_refl | exact (IH _ H4)].
Qed.

(* the peers' pool entries and their peer_rep give back the peers' structs (at the world) *)
Lemma hcr5_close_peers (Hrep: hcr5_rep) : forall PS D NS,
  Forall2 hcr5_hs_ok PS D ->
  Forall (fun x => match x with (_, sh, _) => sh = Ews end) PS -> hnodes_peers4 NS PS ->
  iter_sepcon hcr5_pool_entry D * peers_rep PS |--
  iter_sepcon (fun N => @data_at_ W_consume_response_any Ews t_peer (hn_p N)) NS.
Proof.
  destruct Hrep as (_ & _ & _ & _ & _ & _ & Hpeer & _).
  intros PS D NS H. revert NS. induction H as [| [[p sh] P] [[a she] E] PS D HK _ IH]; intros NS HF HN;
    unfold hnodes_peers4 in HN; destruct NS as [| N NS]; try discriminate HN.
  - simpl. unfold peers_rep. simpl. rewrite sepcon_emp. apply derives_refl.
  - simpl in HN. inv HN. inv HF. destruct HK as (-> & -> & _ & _).
    unfold peers_rep. simpl. unfold hcr5_pool_entry at 1. Intros n h.
    rewrite <- hcr5_conv_peer.
    sep_apply (Hpeer Ews (hn_p N) P E n h).
    cancel. apply IH; auto.
Qed.

Lemma hcr5_close_ok : hcr5_rep -> hcr5_closeH.
Proof.
  intros Hrep. split.
  - apply hcr5_close_dev.
  - intros tab KE PS NS T (HK & HP) HN HF.
    sep_apply (hcr5_itable_dissolve Tsh tab T).
    unfold hcr5_ka in HK, HP. rewrite map_length in HK, HP.
    rewrite <- (firstn_skipn (length KE) (t_D T)), iter_sepcon_app.
    sep_apply (hcr5_close_kents PS KE _ HK).
    sep_apply (hcr5_close_peers Hrep PS _ NS HP HF HN).
    cancel.
Qed.
