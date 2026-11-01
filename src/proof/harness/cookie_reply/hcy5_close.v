(* law cookie_reply: the conversions of the returns. (the same statement up to names). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.

Local Open Scope logic.

#[local] Instance hcy5_cl_cce_N : change_composite_env Noise.CS W_cookie_reply.
Proof. make_cs_preserve Noise.CS W_cookie_reply. Defined.
#[local] Instance hcy5_cl_cce_C : change_composite_env Cookie.CS W_cookie_reply.
Proof. make_cs_preserve Cookie.CS W_cookie_reply. Defined.
#[local] Instance hcy5_cl_cce_H : change_composite_env HCS W_cookie_reply.
Proof. make_cs_preserve HCS W_cookie_reply. Defined.

Lemma hcy5_cl_conv_dev sh p : @data_at_ Noise.CS sh t_dev p = @data_at_ W_cookie_reply sh t_dev p.
Proof. rewrite (@data_at__change_composite Noise.CS W_cookie_reply _ sh t_dev); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcy5_cl_conv_itab sh p : @data_at_ Noise.CS sh t_itab p = @data_at_ W_cookie_reply sh t_itab p.
Proof. rewrite (@data_at__change_composite Noise.CS W_cookie_reply _ sh t_itab); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcy5_cl_conv_ptab sh p : @data_at_ Noise.CS sh t_ptab p = @data_at_ W_cookie_reply sh t_ptab p.
Proof. rewrite (@data_at__change_composite Noise.CS W_cookie_reply _ sh t_ptab); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcy5_cl_conv_skb sh p : @data_at_ Cookie.CS sh t_skb p = @data_at_ W_cookie_reply sh t_skb p.
Proof. rewrite (@data_at__change_composite Cookie.CS W_cookie_reply _ sh t_skb); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcy5_cl_conv_mident sh p : @data_at_ HCS sh t_mident p = @data_at_ W_cookie_reply sh t_mident p.
Proof. rewrite (@data_at__change_composite HCS W_cookie_reply _ sh t_mident); [reflexivity | prove_cs_preserve_type]. Qed.
Lemma hcy5_cl_conv_bytes sh n p : hout sh n p = @data_at_ W_cookie_reply sh (tarray tuchar n) p.
Proof. unfold hout. rewrite (@data_at__change_composite HCS W_cookie_reply _ sh (tarray tuchar n)); [reflexivity | prove_cs_preserve_type]. Qed.

Section Dev.
#[local] Existing Instance Noise.CS.
Lemma hcy5_cl_dev sh wg D : device_rep sh wg D |-- data_at_ sh t_dev wg.
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

Lemma hcy5_cl_drest sh wg D CC :
  hcy5_drest sh wg D * checker_rep sh (cc_addr wg) CC |-- data_at_ sh t_dev wg.
Proof.
  eapply derives_trans; [| apply (hcy5_cl_dev sh wg (mkDev (d_dev D) (d_id D) CC (d_ptab D) (d_itab D)))].
  unfold hcy5_drest, device_rep. simpl. Intros. entailer!.
Qed.

Lemma hcy5_cl_itab sht tab T :
  itable sht tab T |-- data_at_ sht t_itab tab * iter_sepcon hcy5_pool_item (t_D T).
Proof.
  unfold itable. Intros. apply sepcon_derives; [apply data_at_data_at_ |].
  apply iter_sepcon_derives. intros [[a sh] E] _. unfold pool_item_rep, hcy5_pool_item.
  Exists (succ_in (t_L T) a) (vin a (t_L T)). apply derives_refl.
Qed.
End Dev.

Lemma hcy5_close_ok : hcy5_closeH.
Proof.
  split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
  - intros sh wg D. rewrite <- hcy5_cl_conv_dev. apply hcy5_cl_dev.
  - intros sh wg D CC. rewrite <- hcy5_cl_conv_dev. apply hcy5_cl_drest.
  - intros sh tab T. rewrite <- hcy5_cl_conv_itab. apply hcy5_cl_itab.
  - intros sh tab h. rewrite <- hcy5_cl_conv_ptab. unfold ptable. apply data_at_data_at_.
  - intros sh p s. rewrite <- hcy5_cl_conv_skb. unfold skb_rep. Intros. apply data_at_data_at_.
  - intros sh p. rewrite <- hcy5_cl_conv_skb. apply derives_refl.
  - intros sh v p. rewrite <- hcy5_cl_conv_mident. apply data_at_data_at_.
  - intros sh n p. rewrite <- hcy5_cl_conv_bytes. apply derives_refl.
  - intros sh bs p. rewrite <- hcy5_cl_conv_bytes. unfold hout, hbytes. apply data_at_data_at_.
Qed.
