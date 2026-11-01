(* law handshake_clear: the returns' separation facts (hcl5_closeH of hcl5_defs.v:
   device_rep back to its struct; the index table, the peers and the kents' entries back to the table's struct,
   each peer's whole struct at the world (hnodes_free4) and each kent's entry (kents_free4)), from
   prot_rep_lemmas3's statement hcl5_rep.  Same statement as consume_initiation_any's hci5_close.v (port it when
   that one is proved, or prove it directly). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_world.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_defs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_conv.

Local Open Scope logic.

(* a pool item with any list fields *)
Definition hcl5_close_pe (x: val * share * entry) : mpred :=
  match x with (a, sh, E) => EX n: val, EX h: bool, entry_at sh a E n h end.

Lemma hcl5_close_dissolve sht tab T :
  itable sht tab T |-- @data_at_ Noise.CS sht t_itab tab * iter_sepcon hcl5_close_pe (t_D T).
Proof.
  unfold itable. Intros. apply sepcon_derives; [apply data_at_data_at_ |].
  apply iter_sepcon_derives. intros [[a sh] E] _. unfold pool_item_rep, hcl5_close_pe.
  Exists (succ_in (t_L T) a) (vin a (t_L T)). apply derives_refl.
Qed.

Lemma hcl5_close_split (D: list (val * share * entry)) l1 l2 :
  saddrs D = l1 ++ l2 -> exists D1 D2, D = D1 ++ D2 /\ saddrs D1 = l1 /\ saddrs D2 = l2.
Proof. unfold saddrs. intros H. apply map_eq_app in H. exact H. Qed.

Lemma hcl5_close_kents : forall (D: list (val * share * entry)) (KE: list kent4),
  saddrs D = map ke_addr KE ->
  Forall (fun d => match d with (_, sh, _) => sh = Ews end) D ->
  iter_sepcon hcl5_close_pe D |-- iter_sepcon (fun e => @data_at_ Noise.CS Ews t_entry_s (ke_addr e)) KE.
Proof.
  induction D as [| [[a sh] E] D IH]; intros KE HA HF; destruct KE as [| e KE]; try discriminate HA.
  - simpl. apply derives_refl.
  - simpl in HA. inv HA. inv HF. simpl. unfold hcl5_close_pe at 1. Intros n h.
    apply sepcon_derives; [| apply IH; auto].
    unfold entry_at. apply data_at_data_at_.
Qed.

Lemma hcl5_close_peers (Hrep: hcl5_rep) : forall (D: list (val * share * entry)) PS0 PS NS,
  saddrs D = map (fun x => hs_addr (peer_addr4 x)) PS0 ->
  Forall (fun d => match d with (_, sh, _) => sh = Ews end) D ->
  map peer_addr4 PS = map peer_addr4 PS0 ->
  Forall (fun x => match x with (_, sh, _) => sh = Ews end) PS -> hnodes_peers4 NS PS ->
  iter_sepcon hcl5_close_pe D * peers_rep PS |--
  iter_sepcon (fun N => @data_at_ W Ews t_peer (hn_p N)) NS.
Proof.
  destruct Hrep as (_ & _ & _ & _ & _ & _ & Hpeer & _).
  induction D as [| [[a sh] E] D IH]; intros PS0 PS NS HA HF HP HFP HN;
    destruct PS0 as [| x0 PS0]; try discriminate HA;
    destruct PS as [| [[p shp] P] PS]; try discriminate HP;
    unfold hnodes_peers4 in HN; destruct NS as [| N NS]; try discriminate HN.
  - simpl. unfold peers_rep. simpl. rewrite sepcon_emp. apply derives_refl.
  - simpl in HA, HP, HN. inv HA. inv HP. inv HN. inv HF. inv HFP.
    unfold peers_rep. simpl. unfold hcl5_close_pe at 1. Intros n h.
    rewrite <- hcl5_conv_peer.
    sep_apply (Hpeer Ews (hn_p N) P E n h).
    cancel. apply (IH PS0 PS NS); auto.
Qed.

Section Dev.
#[local] Existing Instance Noise.CS.
Lemma hcl5_close_dev sh wg D : device_rep sh wg D |-- data_at_ sh t_dev wg.
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

Lemma hcl5_close_ok : hcl5_rep -> hcl5_closeH.
Proof.
  intros Hrep. split.
  - apply hcl5_close_dev.
  - intros tab T PS0 PS KE NS HA HFD HP HF HN.
    destruct (hcl5_close_split (t_D T) _ _ HA) as (D1 & D2 & HD & H1 & H2).
    sep_apply (hcl5_close_dissolve Tsh tab T). rewrite HD in *.
    rewrite iter_sepcon_app. apply Forall_app in HFD. destruct HFD as [HF1 HF2].
    sep_apply (hcl5_close_kents D1 KE H1 HF1).
    sep_apply (hcl5_close_peers Hrep D2 PS0 PS NS H2 HF2 HP HF HN).
    cancel.
Qed.
