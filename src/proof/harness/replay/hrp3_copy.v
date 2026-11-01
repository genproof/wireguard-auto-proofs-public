(* law replay: the body of copy_init (harness/replay.c) against hrp3_copy_init_spec, with its only callee
   bytes_copy (hc_specs3.v, stated at HCS); lifted to the unit by the parent (hrp3_lift).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.protocol.prot_prog3.
Require Import WgNoise.proof.harness.common.hc_prog3.
Require Import WgNoise.proof.harness.replay.hrp3_spec.
Require Import WgNoise.proof.harness.replay.hrp3_model.
Require Import WgNoise.proof.harness.replay.hrp3_defs.
Require WgNoise.contracts.x_replay.
Require WgNoise.harness.x_replay.code.
Require Import WgNoise.proof.libc.libc_bytes.

#[local] Existing Instance W_replay.
Local Open Scope Z_scope.

#[local] Instance CCE_rp3c_nw : change_composite_env Noise.CS W_replay.
Proof. make_cs_preserve Noise.CS W_replay. Defined.
#[local] Instance CCE_rp3c_wn : change_composite_env W_replay Noise.CS.
Proof. make_cs_preserve W_replay Noise.CS. Defined.

(* the message struct (at the world) as its two scalar fields and its five byte arrays (at HCS) *)
Definition rp3c_pieces (sh: share) (a b: val) (e es et m1 m2: list val) (p: val) : mpred :=
  (field_at sh t_init [StructField RC._header] a p *
  field_at sh t_init [StructField RC._sender_index] b p *
  @data_at HCS sh (tarray tuchar 32) e (offset_val 8 p) *
  @data_at HCS sh (tarray tuchar 48) es (offset_val 40 p) *
  @data_at HCS sh (tarray tuchar 28) et (offset_val 88 p) *
  @data_at HCS sh (tarray tuchar 16) m1 (offset_val 116 p) *
  @data_at HCS sh (tarray tuchar 16) m2 (offset_val 132 p))%logic.

Lemma rp3c_hbytes: forall sh A n p, Zlength A = n ->
  @data_at HCS sh (tarray tuchar n) (bytes A) p = hbytes sh A p.
Proof. intros. subst. reflexivity. Qed.

Lemma rp3c_hout: forall sh n p,
  @data_at HCS sh (tarray tuchar n) (default_val (tarray tuchar n)) p = hout sh n p.
Proof. reflexivity. Qed.

Lemma hrp3_copy_init_body :
  @semax_body [] [bytes_copy_spec] W_replay RC.f_copy_init hrp3_copy_init_spec.
Proof.
  start_function.
  unfold init_rep. Intros.
  destruct H as (Le & Ls & Lt & L1 & L2).
  rewrite (@data_at_change_composite Noise.CS W_replay CCE_rp3c_nw shs t_init (init_val M) (init_val M) (JMeq_refl _) eq_refl).
  rewrite (@data_at__change_composite Noise.CS W_replay CCE_rp3c_nw shd t_init eq_refl).
  forward. forward. forward. forward.
  assert_PROP (field_compatible t_init [] d /\ field_compatible t_init [] s) as FC by entailer!.
  destruct FC as [FCd FCs].
  unfold_data_at (data_at shd t_init _ d).
  unfold_data_at (data_at shs t_init _ s).
  rewrite (field_at_data_at shd t_init (DOT RC._unencrypted_ephemeral)), (field_at_data_at shd t_init (DOT RC._encrypted_static)), (field_at_data_at shd t_init (DOT RC._encrypted_timestamp)), (field_at_data_at shd t_init (DOT RC._macs)).
  rewrite (field_at_data_at shs t_init (DOT RC._unencrypted_ephemeral)), (field_at_data_at shs t_init (DOT RC._encrypted_static)), (field_at_data_at shs t_init (DOT RC._encrypted_timestamp)), (field_at_data_at shs t_init (DOT RC._macs)).
  rewrite !field_address_offset by auto with field_compatible.
  change (nested_field_type t_init (DOT RC._unencrypted_ephemeral)) with (tarray tuchar 32).
  change (nested_field_type t_init (DOT RC._encrypted_static)) with (tarray tuchar 48).
  change (nested_field_type t_init (DOT RC._encrypted_timestamp)) with (tarray tuchar 28).
  change (nested_field_type t_init (DOT RC._macs)) with (Tstruct RC._message_macs noattr).
  change (nested_field_offset t_init (DOT RC._unencrypted_ephemeral)) with 8.
  change (nested_field_offset t_init (DOT RC._encrypted_static)) with 40.
  change (nested_field_offset t_init (DOT RC._encrypted_timestamp)) with 88.
  change (nested_field_offset t_init (DOT RC._macs)) with 116.
  assert_PROP (field_compatible (Tstruct RC._message_macs noattr) [] (offset_val 116 d) /\
    field_compatible (Tstruct RC._message_macs noattr) [] (offset_val 116 s)) as FC by entailer!.
  destruct FC as [FMd FMs].
  unfold_data_at (data_at shd (Tstruct RC._message_macs noattr) _ (offset_val 116 d)).
  unfold_data_at (data_at shs (Tstruct RC._message_macs noattr) _ (offset_val 116 s)).
  rewrite (field_at_data_at shd (Tstruct RC._message_macs noattr) (DOT RC._mac1)),
    (field_at_data_at shd (Tstruct RC._message_macs noattr) (DOT RC._mac2)),
    (field_at_data_at shs (Tstruct RC._message_macs noattr) (DOT RC._mac1)),
    (field_at_data_at shs (Tstruct RC._message_macs noattr) (DOT RC._mac2)).
  rewrite !field_address_offset by auto with field_compatible.
  change (nested_field_type (Tstruct RC._message_macs noattr) (DOT RC._mac1)) with (tarray tuchar 16).
  change (nested_field_type (Tstruct RC._message_macs noattr) (DOT RC._mac2)) with (tarray tuchar 16).
  change (nested_field_offset (Tstruct RC._message_macs noattr) (DOT RC._mac1)) with 0.
  change (nested_field_offset (Tstruct RC._message_macs noattr) (DOT RC._mac2)) with 16.
  rewrite !offset_offset_val. simpl Z.add.
  rewrite !(@data_at_tarray_tuchar_cs W_replay HCS).
  cbn [fst snd init_val].
  rewrite (rp3c_hbytes shs (im_eph M) 32 _ Le), (rp3c_hbytes shs (im_encs M) 48 _ Ls),
    (rp3c_hbytes shs (im_enct M) 28 _ Lt), (rp3c_hbytes shs (im_mac1 M) 16 (offset_val 116 s) L1),
    (rp3c_hbytes shs (im_mac2 M) 16 _ L2).
  rewrite !rp3c_hout.
  replace (hout shd 32 (offset_val 8 d)) with (hout shd (Zlength (im_eph M)) (offset_val 8 d)) by (rewrite Le; auto).
  forward_call (shd, offset_val 8 d, shs, offset_val 8 s, im_eph M).
  { entailer!. rewrite Le. pose proof (field_compatible_isptr _ _ _ FCd); pose proof (field_compatible_isptr _ _ _ FCs). destruct d; try contradiction; destruct s; try contradiction; simpl; rewrite ?Ptrofs.add_zero, ?Ptrofs.add_assoc; reflexivity. }
  replace (hout shd 48 (offset_val 40 d)) with (hout shd (Zlength (im_encs M)) (offset_val 40 d)) by (rewrite Ls; auto).
  forward_call (shd, offset_val 40 d, shs, offset_val 40 s, im_encs M).
  { entailer!. rewrite Ls. pose proof (field_compatible_isptr _ _ _ FCd); pose proof (field_compatible_isptr _ _ _ FCs). destruct d; try contradiction; destruct s; try contradiction; simpl; rewrite ?Ptrofs.add_zero, ?Ptrofs.add_assoc; reflexivity. }
  replace (hout shd 28 (offset_val 88 d)) with (hout shd (Zlength (im_enct M)) (offset_val 88 d)) by (rewrite Lt; auto).
  forward_call (shd, offset_val 88 d, shs, offset_val 88 s, im_enct M).
  { entailer!. rewrite Lt. pose proof (field_compatible_isptr _ _ _ FCd); pose proof (field_compatible_isptr _ _ _ FCs). destruct d; try contradiction; destruct s; try contradiction; simpl; rewrite ?Ptrofs.add_zero, ?Ptrofs.add_assoc; reflexivity. }
  replace (hout shd 16 (offset_val 116 d)) with (hout shd (Zlength (im_mac1 M)) (offset_val 116 d)) by (rewrite L1; auto).
  forward_call (shd, offset_val 116 d, shs, offset_val 116 s, im_mac1 M).
  { entailer!. rewrite L1. pose proof (field_compatible_isptr _ _ _ FCd); pose proof (field_compatible_isptr _ _ _ FCs). destruct d; try contradiction; destruct s; try contradiction; simpl; rewrite ?Ptrofs.add_zero, ?Ptrofs.add_assoc; reflexivity. }
  replace (hout shd 16 (offset_val 132 d)) with (hout shd (Zlength (im_mac2 M)) (offset_val 132 d)) by (rewrite L2; auto).
  forward_call (shd, offset_val 132 d, shs, offset_val 132 s, im_mac2 M).
  { entailer!. rewrite L2. pose proof (field_compatible_isptr _ _ _ FCd); pose proof (field_compatible_isptr _ _ _ FCs). destruct d; try contradiction; destruct s; try contradiction; simpl; rewrite ?Ptrofs.add_zero, ?Ptrofs.add_assoc; reflexivity. }
  forward.
  unfold init_rep.
  rewrite (@data_at_change_composite Noise.CS W_replay CCE_rp3c_nw shd t_init (init_val M) (init_val M) (JMeq_refl _) eq_refl).
  rewrite (@data_at_change_composite Noise.CS W_replay CCE_rp3c_nw shs t_init (init_val M) (init_val M) (JMeq_refl _) eq_refl).
  rewrite !prop_true_andp by (repeat split; auto).
  unfold_data_at (data_at shd t_init _ d).
  unfold_data_at (data_at shs t_init _ s).
  rewrite (field_at_data_at shd t_init (DOT RC._unencrypted_ephemeral)), (field_at_data_at shd t_init (DOT RC._encrypted_static)), (field_at_data_at shd t_init (DOT RC._encrypted_timestamp)), (field_at_data_at shd t_init (DOT RC._macs)).
  rewrite (field_at_data_at shs t_init (DOT RC._unencrypted_ephemeral)), (field_at_data_at shs t_init (DOT RC._encrypted_static)), (field_at_data_at shs t_init (DOT RC._encrypted_timestamp)), (field_at_data_at shs t_init (DOT RC._macs)).
  rewrite !field_address_offset by auto with field_compatible.
  change (nested_field_type t_init (DOT RC._unencrypted_ephemeral)) with (tarray tuchar 32).
  change (nested_field_type t_init (DOT RC._encrypted_static)) with (tarray tuchar 48).
  change (nested_field_type t_init (DOT RC._encrypted_timestamp)) with (tarray tuchar 28).
  change (nested_field_type t_init (DOT RC._macs)) with (Tstruct RC._message_macs noattr).
  change (nested_field_offset t_init (DOT RC._unencrypted_ephemeral)) with 8.
  change (nested_field_offset t_init (DOT RC._encrypted_static)) with 40.
  change (nested_field_offset t_init (DOT RC._encrypted_timestamp)) with 88.
  change (nested_field_offset t_init (DOT RC._macs)) with 116.
  unfold_data_at (data_at shd (Tstruct RC._message_macs noattr) _ (offset_val 116 d)).
  unfold_data_at (data_at shs (Tstruct RC._message_macs noattr) _ (offset_val 116 s)).
  rewrite (field_at_data_at shd (Tstruct RC._message_macs noattr) (DOT RC._mac1)),
    (field_at_data_at shd (Tstruct RC._message_macs noattr) (DOT RC._mac2)),
    (field_at_data_at shs (Tstruct RC._message_macs noattr) (DOT RC._mac1)),
    (field_at_data_at shs (Tstruct RC._message_macs noattr) (DOT RC._mac2)).
  rewrite !field_address_offset by auto with field_compatible.
  change (nested_field_type (Tstruct RC._message_macs noattr) (DOT RC._mac1)) with (tarray tuchar 16).
  change (nested_field_type (Tstruct RC._message_macs noattr) (DOT RC._mac2)) with (tarray tuchar 16).
  change (nested_field_offset (Tstruct RC._message_macs noattr) (DOT RC._mac1)) with 0.
  change (nested_field_offset (Tstruct RC._message_macs noattr) (DOT RC._mac2)) with 16.
  rewrite !offset_offset_val. simpl Z.add.
  rewrite !(@data_at_tarray_tuchar_cs W_replay HCS).
  cbn [fst snd init_val].
  rewrite (rp3c_hbytes shs (im_eph M) 32 _ Le), (rp3c_hbytes shs (im_encs M) 48 _ Ls),
    (rp3c_hbytes shs (im_enct M) 28 _ Lt), (rp3c_hbytes shs (im_mac1 M) 16 (offset_val 116 s) L1),
    (rp3c_hbytes shs (im_mac2 M) 16 _ L2).
  rewrite (rp3c_hbytes shd (im_eph M) 32 _ Le), (rp3c_hbytes shd (im_encs M) 48 _ Ls),
    (rp3c_hbytes shd (im_enct M) 28 _ Lt), (rp3c_hbytes shd (im_mac1 M) 16 (offset_val 116 d) L1),
    (rp3c_hbytes shd (im_mac2 M) 16 _ L2).
  cancel.
Qed.
