(* law handshake_receive, body recv: helpers.
   Copies of the proven hrx5_vhl_* (hrx5_body_vhl.v), renamed hrx5_rvl_*: the skb at
   Cookie.CS = at HRX, the type word of the message buffer (hrx5_rvl_split). *)
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
Local Open Scope logic.

#[local] Existing Instance HRX.

(* ---- helpers ---- *)
#[export] Instance hrx5_rvl_CCE_c2h : change_composite_env Cookie.CS HRX.
Proof. make_cs_preserve Cookie.CS HRX. Defined.
#[export] Instance hrx5_rvl_CCE_h2c : change_composite_env HRX Cookie.CS.
Proof. make_cs_preserve HRX Cookie.CS. Defined.

Lemma hrx5_rvl_skb_cs sh s p :
  @data_at Cookie.CS sh t_skb (skb_val s) p = @data_at HRX sh t_skb (skb_val s) p.
Proof.
  apply (f_equal (fun f => f p)). apply (@data_at_change_composite Cookie.CS HRX _); [apply JMeq_refl | reflexivity].
Qed.

Lemma hrx5_rvl_le32_inv l : Zlength l = 4 -> le32 (le32_val l) = l.
Proof.
  intros Hl. assert (Hn: length l = 4%nat) by (rewrite Zlength_correct in Hl; lia).
  destruct l as [|a [|b [|c [|d [|e l]]]]]; simpl in Hn; try discriminate.
  rewrite prot_rep3_le32_encode. unfold le32_val.
  pose proof (Byte.unsigned_range a). pose proof (Byte.unsigned_range b).
  pose proof (Byte.unsigned_range c). pose proof (Byte.unsigned_range d).
  change Byte.modulus with 256 in *.
  replace (Byte.unsigned (Znth 0 [a;b;c;d]) + Byte.unsigned (Znth 1 [a;b;c;d]) * 2 ^ 8 +
           Byte.unsigned (Znth 2 [a;b;c;d]) * 2 ^ 16 + Byte.unsigned (Znth 3 [a;b;c;d]) * 2 ^ 24)
    with (int_of_bytes [a;b;c;d]) by (cbn [int_of_bytes]; cbv [Znth]; simpl; lia).
  rewrite Int.unsigned_repr by (cbn [int_of_bytes]; rep_lia).
  unfold encode_int, rev_if_be. change Archi.big_endian with false. cbv iota.
  exact (prot_rep3_bytes_of_int_of_bytes [a;b;c;d]).
Qed.

Lemma hrx5_rvl_hdr_u32 sh v p : @field_compatible HRX (Tstruct HRC._message_header noattr) [] p ->
  @data_at HRX sh (Tstruct HRC._message_header noattr) v p = @data_at HRX sh tuint v p.
Proof.
  intros FC. unfold_data_at (data_at _ _ _ p).
  rewrite field_at_data_at, field_compatible_field_address by auto with field_compatible.
  replace (nested_field_offset _ _) with 0 by reflexivity.
  rewrite isptr_offset_val_zero by (destruct FC; auto). reflexivity.
Qed.

Lemma hrx5_rvl_mc_hdr n p : 4 <= n -> malloc_compatible n p ->
  @field_compatible HRX (Tstruct HRC._message_header noattr) [] p.
Proof.
  intros Hn Hm. apply malloc_compatible_field_compatible; [| reflexivity | reflexivity].
  destruct p; try contradiction. destruct Hm as [Ha Hs]. split; auto.
  replace (sizeof _) with 4 by reflexivity. lia.
Qed.

Lemma hrx5_rvl_split sh msg p : 4 <= Zlength msg -> malloc_compatible (Zlength msg) p ->
  bytes_at sh msg p =
  @data_at HRX sh (Tstruct HRC._message_header noattr) (Vint (hrx5_tw msg)) p *
  bytes_at sh (sublist 4 (Zlength msg) msg) (offset_val 4 p).
Proof.
  intros Hn Hm.
  assert (FCh := hrx5_rvl_mc_hdr _ _ Hn Hm).
  assert (FCu: @field_compatible HRX tuint [] p).
  { apply malloc_compatible_field_compatible; [| reflexivity | reflexivity].
    destruct p; try contradiction. destruct Hm as [Ha Hs]. split; auto. simpl. lia. }
  assert (FCa: @field_compatible Noise.CS (tarray tuchar (Zlength msg)) [] p).
  { destruct p; try contradiction. destruct Hm as [Ha Hs].
    repeat split; auto.
    - simpl. rewrite Z.max_r by lia. lia.
    - apply align_compatible_rec_Tarray. intros.
      eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  rewrite <- (sublist_same 0 (Zlength msg) msg) at 1 by auto.
  rewrite (sublist_split 0 4 (Zlength msg)) by lia.
  rewrite prot_rep3_bytes_app
    by (rewrite !Zlength_sublist by lia; replace (4 - 0 + (Zlength msg - 4)) with (Zlength msg) by lia; exact FCa).
  rewrite Zlength_sublist by lia. replace (4 - 0) with 4 by lia.
  f_equal.
  rewrite hrx5_rvl_hdr_u32 by auto. unfold hrx5_tw.
  rewrite (prot_rep3_u32_le sh _ p FCu). rewrite hrx5_rvl_le32_inv by list_solve.
  unfold bytes_at. rewrite Zlength_sublist by lia. replace (4 - 0) with 4 by lia.
  apply data_at_tarray_tuchar_cs.
Qed.

