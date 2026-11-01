(* law cookie_mac: the setup's objects dissolve into main's stack frame (hck5_defs.v's
   hck5_freeH: A's side with the kents and p's handshake entry in the index table's pool; B's side), used by the
   returns of P2 and P8.
   (hck3_free_dev, _drest,
   _peer, hck3_bside_free); p's peer_rep and its handshake entry give data_at_ of the peer by prot_rep_lemmas3
   (src/proof/protocol/prot_rep_lemmas3.v, proved; v1 used its conjunct as hck3_rep). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.cookie_mac.hck5_defs.
Require Import WgNoise.proof.harness.cookie_mac.hck5_conv.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Local Open Scope logic.

Section Helpers.
#[local] Existing Instance Noise.CS.

Lemma hck5_free_dev sh wg D : device_rep sh wg D |-- data_at_ sh t_dev wg.
Proof.
  unfold device_rep, identity_rep, checker_rep. Intros lk1 lk2.
  unfold_data_at (data_at_ sh t_dev wg).
  assert (E1: id_addr wg = field_address t_dev (DOT I._static_identity) wg) by
    (unfold id_addr, OFS_DEV_IDENTITY; rewrite field_address_offset by auto with field_compatible; reflexivity).
  assert (E2: cc_addr wg = field_address t_dev (DOT I._cookie_checker) wg) by
    (unfold cc_addr, OFS_DEV_CHECKER; rewrite field_address_offset by auto with field_compatible; reflexivity).
  rewrite E1, E2.
  rewrite (field_at_data_at sh t_dev (DOT noise.code._static_identity)),
          (field_at_data_at sh t_dev (DOT noise.code._cookie_checker)).
  rewrite <- !sepcon_assoc.
  repeat apply sepcon_derives;
    first [ (eapply derives_trans; [apply field_at_field_at_|]; apply derives_refl)
          | (eapply derives_trans; [apply data_at_data_at_|]; apply derives_refl) ].
Qed.

Lemma hck5_free_drest sh wg D CC :
  hck5_drest sh wg D * checker_rep sh (cc_addr wg) CC |-- data_at_ sh t_dev wg.
Proof.
  eapply derives_trans; [| apply (hck5_free_dev sh wg (mkDev (d_dev D) (d_id D) CC (d_ptab D) (d_itab D)))].
  unfold hck5_drest, device_rep. simpl. Intros. entailer!.
Qed.

Lemma hck5_free_itab sh tab : itable sh tab (mkT [] []) |-- data_at_ sh t_itab tab.
Proof. unfold itable. Intros. simpl. rewrite sepcon_emp. apply data_at_data_at_. Qed.

Lemma hck5_free_peer sh p P C :
  hck5_prest sh p P * cookie_rep sh (cookie_addr p) C |-- peer_rep sh p (p_set_cookie P C).
Proof. unfold hck5_prest, peer_rep. destruct P; simpl. Intros. entailer!. Qed.

(* the pool: the kents' entries (Ews) and one last entry *)
Lemma hck5_free_pool Lt a sh (KE: list kent4) : forall (D: list (val * share * entry)),
  saddrs D = map ke_addr KE ++ [a] ->
  map (fun x => snd (fst x)) D = map (fun _ => Ews) KE ++ [sh] ->
  iter_sepcon (pool_item_rep Lt) D |--
  iter_sepcon (fun e => data_at_ Ews t_entry_s (ke_addr e)) KE * EX E: entry, EX n: val, EX h: bool, entry_at sh a E n h.
Proof.
  induction KE as [|e KE IH]; intros D HA HS.
  - destruct D as [|[[a0 s0] E0] [|x D]]; simpl in HA, HS; try discriminate.
    + inv HA; inv HS. simpl. Exists E0 (succ_in Lt a) (vin a Lt). cancel.
  - destruct D as [|[[a0 s0] E0] D]; simpl in HA, HS; [discriminate|].
    inv HA; inv HS. simpl.
    sep_apply (IH D H1 H2). unfold entry_at. sep_apply (data_at_data_at_ Ews t_entry_s). cancel.
Qed.

End Helpers.

Lemma hck5_free_ok x25519 : hck5_freeH x25519.
Proof.
  split.
  - intros R L A C HOK.
    destruct HOK as (FC & _ & _ & _ & _ & _ & HA & HS & _).
    unfold hck5_A. destruct A as [T P KE kes head0]; simpl in *.
    unfold itable. Intros.
    sep_apply (hck5_free_pool (t_L T) (hs_addr (l_p L)) Tsh KE (t_D T) HA HS).
    Intros E n h.
    sep_apply (hck5_free_dev Tsh (l_wa L) (hck5_DA x25519 R L)).
    sep_apply (@data_at_data_at_ Noise.CS Tsh t_itab (hd nullval (t_L T)) (l_ita L)).
    unfold ptable. sep_apply (@data_at_data_at_ Noise.CS Tsh t_ptab (l_p L) (l_pta L)).
    sep_apply (hck5_free_peer Tsh (l_p L) P C).
    destruct prot_rep_lemmas3 as (_ & _ & _ & _ & _ & _ & Hpeer & _).
    sep_apply (Hpeer Tsh (l_p L) (p_set_cookie P C) E n h).
    rewrite <- hck5_conv_dev, <- hck5_conv_itab, <- hck5_conv_ptab, <- hck5_conv_peer. cancel.
  - intros R L CC.
    unfold hck5_bside. simpl fold_right. rewrite sepcon_emp.
    sep_apply (hck5_free_drest Tsh (l_wb L) (hck5_DB x25519 R L) CC).
    sep_apply (hck5_free_itab Tsh (l_itb L)).
    unfold ptable. sep_apply (@data_at_data_at_ Noise.CS Tsh t_ptab nullval (l_ptb L)).
    rewrite <- hck5_conv_dev, <- hck5_conv_itab, <- hck5_conv_ptab. cancel.
Qed.
