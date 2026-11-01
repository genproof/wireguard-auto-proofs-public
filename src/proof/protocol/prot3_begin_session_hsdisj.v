(* Helper lemma of the group begin_session: a handshake (writable) is not at the
   address of a live keypair (their memories overlap at offset 32: the handshake's state, the keypair's sending key). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

Lemma prot3_begin_session_hsdisj_glb sh :
  writable_share sh -> sepalg.nonidentity (Share.glb sh Ews).
Proof.
  intros [_ HW] N.
  assert (HR: readable_share Ews) by auto.
  apply HR.
  apply leq_join_sub, Share.ord_spec1 in HW.
  apply identity_share_bot in N.
  rewrite HW, Share.glb_assoc, N, Share.glb_bot.
  apply bot_identity.
Qed.

Lemma prot3_begin_session_hsdisj_conflict sh p :
  writable_share sh ->
  @data_at_ Noise.CS sh (tarray tuchar 4) p * @data_at_ Noise.CS Ews (tarray tuchar 4) p |-- FF.
Proof.
  intros. unfold data_at_. apply data_at_conflict_glb.
  - apply prot3_begin_session_hsdisj_glb; auto.
  - simpl. lia.
Qed.

Lemma prot3_begin_session_hsdisj_one CSw sh h K H :
  writable_share sh ->
  keypair_rep CSw h K * hs_rep sh h H |-- FF.
Proof.
  intros WS.
  unfold keypair_rep, hs_rep. Intros.
  sep_apply (@field_at_field_at_ Noise.CS Ews t_kp (DOT I._sending) (symkey_val (kp_send K)) h).
  sep_apply (@field_at_field_at_ Noise.CS sh t_hs (DOT I._state) (Vint (hs_state H)) h).
  rewrite !field_at__memory_block.
  unfold field_address.
  simpl nested_field_type. simpl nested_field_offset.
  destruct (field_compatible_dec t_hs (DOT I._state) h) as [Fh|Fh];
    [| assert_PROP (isptr Vundef) by entailer!; contradiction].
  destruct (field_compatible_dec t_kp (DOT I._sending) h) as [Fk|Fk];
    [| exfalso; apply Fk; auto with field_compatible].
  destruct H0 as (Hp & _ & Hsz & _ & _).
  destruct h as [| | | | | b i]; try contradiction.
  unfold size_compatible in Hsz. simpl sizeof in Hsz |- *.
  simpl offset_val.
  rewrite <- (Ptrofs.repr_unsigned (Ptrofs.add i (Ptrofs.repr 32))).
  rewrite Ptrofs.add_unsigned, (Ptrofs.unsigned_repr 32) by rep_lia.
  rewrite (Ptrofs.unsigned_repr (Ptrofs.unsigned i + 32)) by rep_lia.
  change 48 with (4 + 44).
  rewrite (memory_block_split Ews b (Ptrofs.unsigned i + 32) 4 44) by rep_lia.
  rewrite !(@memory_block_data_at__tarray_tuchar_eq Noise.CS) by rep_lia.
  sep_apply (prot3_begin_session_hsdisj_conflict sh (Vptr b (Ptrofs.repr (Ptrofs.unsigned i + 32))) WS).
  rewrite !FF_sepcon. auto.
Qed.

Lemma prot3_begin_session_hs_notin CSw KS sh h H :
  writable_share sh ->
  keypairs_rep CSw KS * hs_rep sh h H |-- !! (~ In h (map fst KS)).
Proof.
  intros WS.
  destruct (in_dec Val.eq h (map fst KS)) as [IN|NIN]; [| apply prop_right; auto].
  apply in_map_iff in IN. destruct IN as [[k K] [Ek IN]]. simpl in Ek; subst k.
  unfold keypairs_rep.
  sep_apply (iter_sepcon_in_true (keypair_item_rep CSw) KS (h, K) IN).
  simpl keypair_item_rep.
  sep_apply (prot3_begin_session_hsdisj_one CSw sh h K H WS).
  rewrite !FF_sepcon. apply FF_left.
Qed.
