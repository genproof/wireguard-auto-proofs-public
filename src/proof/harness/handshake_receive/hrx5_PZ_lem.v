(* law handshake_receive, phase PZ: the separation facts of main's return
   (port of handshake_clear's hcl5_close.v / consume_initiation_any's hci5_close.v for hrx5_inv's pool
   hrx5cr_pool): device_rep back to its struct; the index table, the peers and the kents' entries back to the
   table's struct, each peer's whole struct at the world (hnodes_free4) and each kent's entry (kents_free4); the
   byte lengths of mk1 / ss_k. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.model.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_conv.

Local Open Scope logic.

(* a pool item with any list fields *)
Definition hrx5_PZ_pe (x: val * share * entry) : mpred :=
  match x with (a, sh, E) => EX n: val, EX h: bool, entry_at sh a E n h end.

Lemma hrx5_PZ_dissolve sht tab T :
  itable sht tab T |-- @data_at_ Noise.CS sht t_itab tab * iter_sepcon hrx5_PZ_pe (t_D T).
Proof.
  unfold itable. Intros. apply sepcon_derives; [apply data_at_data_at_ |].
  apply iter_sepcon_derives. intros [[a sh] E] _. unfold pool_item_rep, hrx5_PZ_pe.
  Exists (succ_in (t_L T) a) (vin a (t_L T)). apply derives_refl.
Qed.

Lemma hrx5_PZ_kents PS : forall (KE: list kent4) (D: list (val * share * entry)),
  Forall2 (hrx5cr_ke_ok PS) (map ke_addr KE) D ->
  iter_sepcon hrx5_PZ_pe D |-- iter_sepcon (fun e => @data_at_ Noise.CS Ews t_entry_s (ke_addr e)) KE.
Proof.
  induction KE as [| e KE IH]; intros D HF; inv HF.
  - simpl. apply derives_refl.
  - match goal with Hy: hrx5cr_ke_ok _ _ ?y |- _ => destruct y as [[a sh] E]; destruct Hy as (-> & -> & _ & _) end.
    simpl. unfold hrx5_PZ_pe at 1. Intros n h.
    apply sepcon_derives; [| apply IH; auto].
    unfold entry_at. apply data_at_data_at_.
Qed.

Lemma hrx5_PZ_peers : forall (PS: list (val * share * peer)) (D: list (val * share * entry)) NS,
  Forall2 hrx5cr_hs_ok PS D ->
  Forall (fun x => match x with (_, sh, _) => sh = Ews end) PS -> hnodes_peers4 NS PS ->
  iter_sepcon hrx5_PZ_pe D * peers_rep PS |--
  iter_sepcon (fun N => @data_at_ W Ews t_peer (hn_p N)) NS.
Proof.
  induction PS as [| [[p shp] P] PS IH]; intros D NS HF HFP HN; inv HF;
    unfold hnodes_peers4 in HN; destruct NS as [| N NS]; try discriminate HN.
  - simpl. unfold peers_rep. simpl. rewrite sepcon_emp. apply derives_refl.
  - match goal with Hy: hrx5cr_hs_ok _ ?y |- _ => destruct y as [[a sh] E]; destruct Hy as (-> & -> & _ & _) end.
    simpl in HN. inv HN. inv HFP.
    unfold peers_rep. simpl. unfold hrx5_PZ_pe at 1. Intros n h.
    rewrite <- hrx5_conv_peer.
    sep_apply (prot_rep3_peer_whole Ews (hn_p N) P E n h).
    cancel. apply (IH l' NS); auto.
Qed.

Lemma hrx5_PZ_pool tab T PS KE NS :
  hrx5cr_pool (map ke_addr KE) PS T ->
  Forall (fun x => match x with (_, sh, _) => sh = Ews end) PS -> hnodes_peers4 NS PS ->
  itable Tsh tab T * peers_rep PS |--
  @data_at_ Noise.CS Tsh t_itab tab * iter_sepcon (fun N => @data_at_ W Ews t_peer (hn_p N)) NS *
  iter_sepcon (fun e => @data_at_ Noise.CS Ews t_entry_s (ke_addr e)) KE.
Proof.
  intros [H1 H2] HF HN.
  sep_apply (hrx5_PZ_dissolve Tsh tab T).
  rewrite <- (firstn_skipn (length (map ke_addr KE)) (t_D T)), iter_sepcon_app.
  sep_apply (hrx5_PZ_kents PS KE _ H1).
  sep_apply (hrx5_PZ_peers PS _ NS H2 HF HN).
  cancel.
Qed.

Section Dev.
#[local] Existing Instance Noise.CS.
Lemma hrx5_PZ_dev sh wg D : device_rep sh wg D |-- data_at_ sh t_dev wg.
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
End Dev.

Lemma hrx5_PZ_dev_W sh wg D : device_rep sh wg D |-- @data_at_ W sh t_dev wg.
Proof. rewrite <- hrx5_conv_dev. apply hrx5_PZ_dev. Qed.

Lemma hrx5_PZ_ptable p head : ptable Tsh p head |-- @data_at_ W Tsh t_ptab p.
Proof. unfold ptable. rewrite <- hrx5_conv_ptab. apply data_at_data_at_. Qed.

Lemma hrx5_PZ_hbytes32 bs p : Zlength bs = 32 -> hbytes Tsh bs p |-- @data_at_ W Tsh (tarray tuchar 32) p.
Proof. intros Hl. unfold hbytes. rewrite Hl, <- hrx5_conv_bytes. unfold hout. apply data_at_data_at_. Qed.

Lemma hrx5_PZ_mident v p : @data_at HCS Tsh t_mident v p |-- @data_at_ W Tsh t_mident p.
Proof. rewrite <- hrx5_conv_mident. apply data_at_data_at_. Qed.

Lemma hrx5_PZ_b2s_len key m : Zlength (blake2s key 32 m) = 32.
Proof. unfold blake2s, b2s_digest_stream, b2s_out. rewrite Zlength_map. reflexivity. Qed.

Lemma hrx5_PZ_mk1_len x25519 R : Zlength (hrx5_mk1 x25519 R) = 32.
Proof.
  unfold hrx5_mk1, checker_keys. destruct (id_has _); simpl; [unfold label_key; apply hrx5_PZ_b2s_len | reflexivity].
Qed.

Lemma hrx5_PZ_ssk_len x25519 R : x25519_props x25519 -> Zlength (hrx5_ssk x25519 R) = 32.
Proof.
  intros Hx. unfold hrx5_ssk, m_precomputed_model.
  destruct (_ && _)%bool; [apply Hx | reflexivity].
Qed.

Lemma hrx5_PZ_pn l NS : hnodes_rep4 W l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [| N NS]; cbn [hnodes_rep4].
  - entailer!.
  - Intros nx. subst l. sep_apply (@data_at_local_facts CKS). entailer!.
Qed.
