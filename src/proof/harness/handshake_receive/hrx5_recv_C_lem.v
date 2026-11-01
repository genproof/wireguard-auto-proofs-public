Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_recv_lem.
Local Open Scope logic.

Module CK := WgNoise.cookie.code.

Lemma hrx5_rvC_fc_cs (cs1 cs2: compspecs) n p :
  @field_compatible cs1 (tarray tuchar n) [] p -> @field_compatible cs2 (tarray tuchar n) [] p.
Proof.
  unfold field_compatible, size_compatible, align_compatible.
  assert (forall (ce: composite_env) z, align_compatible_rec ce (tarray tuchar n) z).
  { intros. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  destruct p; simpl; try tauto.
  pose proof (H (@cenv_cs cs2) (Ptrofs.unsigned i)). tauto.
Qed.

Section CookieCS.
#[local] Existing Instance Cookie.CS.

Lemma hrx5_rvC_field sh t gfs v m :
  field_compatible t gfs m ->
  field_at sh t gfs v m = data_at sh (nested_field_type t gfs) v (offset_val (nested_field_offset t gfs) m).
Proof.
  intros FC. rewrite field_at_data_at, field_address_offset by auto. reflexivity.
Qed.

Lemma hrx5_rvC_cm_eq sh m M :
  field_compatible t_cmsg [] m -> cm_ok M ->
  data_at sh t_cmsg (cmsg_val M) m = bytes_at sh (cookie_msg_bytes M) m.
Proof.
  intros FC OK.
  unfold_data_at (data_at _ _ _ m).
  assert (EH: forall v, field_at sh t_cmsg (DOT CK._header) v m =
                        field_at sh t_cmsg (DOT CK._header DOT CK._type) v m).
  { intros v. apply pred_ext. unfold_field_at 1%nat. cancel. unfold_field_at 2%nat. cancel. }
  rewrite EH; clear EH.
  rewrite !hrx5_rvC_field by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset. unfold cmsg_val; simpl fst; simpl snd.
  rewrite (prot_rep3_u32_le sh (cm_type M) (offset_val 0 m))
    by exact (field_compatible_nested_field t_cmsg (DOT CK._header DOT CK._type) m
                ltac:(auto with field_compatible)).
  rewrite (prot_rep3_u32_le sh (cm_receiver M) (offset_val 4 m))
    by exact (field_compatible_nested_field t_cmsg (DOT CK._receiver_index) m
                ltac:(auto with field_compatible)).
  destruct OK as (L1 & L2).
  replace (bytes_at sh (cookie_msg_bytes M) m) with (bytes_at sh (cookie_msg_bytes M) (offset_val 0 m))
    by (rewrite isptr_offset_val_zero by (destruct FC; auto); reflexivity).
  unfold cookie_msg_bytes.
  rewrite (prot_rep3_bytes_app_at sh (le32 (cm_type M)) _ m 0 4 4 60)
    by (rewrite ?Zlength_app, ?prot_rep3_le32_len, ?L1, ?L2; try lia;
        apply (hrx5_rvC_fc_cs Cookie.CS); apply (prot_rep3_fc_bytes t_cmsg); auto; simpl; lia).
  rewrite (prot_rep3_bytes_app_at sh (le32 (cm_receiver M)) _ m 4 8 4 56)
    by (rewrite ?Zlength_app, ?prot_rep3_le32_len, ?L1, ?L2; try lia;
        apply (hrx5_rvC_fc_cs Cookie.CS); apply (prot_rep3_fc_bytes t_cmsg); auto; simpl; lia).
  rewrite (prot_rep3_bytes_app_at sh (cm_nonce M) _ m 8 32 24 32)
    by (rewrite ?Zlength_app, ?prot_rep3_le32_len, ?L1, ?L2; try lia;
        apply (hrx5_rvC_fc_cs Cookie.CS); apply (prot_rep3_fc_bytes t_cmsg); auto; simpl; lia).
  unfold bytes_at. rewrite !prot_rep3_le32_len, L1, L2.
  rewrite !(@data_at_tarray_tuchar_cs Cookie.CS Noise.CS). reflexivity.
Qed.
End CookieCS.

Lemma hrx5_rvC_cm_ok msg : Zlength msg = 64 -> cm_ok (cm_of msg).
Proof. intros H. unfold cm_ok, cm_of; cbn [cm_nonce cm_enc]. rewrite !Zlength_sublist by lia. lia. Qed.

Lemma hrx5_rvC_bytes msg : Zlength msg = 64 -> cookie_msg_bytes (cm_of msg) = msg.
Proof.
  intros H. unfold cookie_msg_bytes, cm_of; cbn [cm_type cm_receiver cm_nonce cm_enc].
  rewrite !hrx5_rvl_le32_inv by (rewrite Zlength_sublist; lia).
  rewrite <- !sublist_split by lia. apply sublist_same; lia.
Qed.

Lemma hrx5_rvC_fc (msg: list byte) p : Zlength msg = 64 -> malloc_compatible (Zlength msg) p ->
  @field_compatible Cookie.CS t_cmsg [] p.
Proof.
  intros Hn Hm. apply malloc_compatible_field_compatible; [| reflexivity | reflexivity].
  destruct p; try contradiction. destruct Hm as [Ha Hs]. split; auto.
  replace (sizeof _) with 64 by reflexivity. lia.
Qed.

(* the message's bytes are the cookie reply struct cm_of msg *)
Lemma hrx5_rvC_msg sh msg p : Zlength msg = 64 -> malloc_compatible (Zlength msg) p ->
  bytes_at sh msg p = cmsg_rep sh p (cm_of msg).
Proof.
  intros Hn Hm. unfold cmsg_rep. rewrite prop_true_andp by (apply hrx5_rvC_cm_ok; auto).
  rewrite <- (hrx5_rvC_bytes msg) at 1 by auto. symmetry.
  apply hrx5_rvC_cm_eq; [apply (hrx5_rvC_fc msg); auto | apply hrx5_rvC_cm_ok; auto].
Qed.
