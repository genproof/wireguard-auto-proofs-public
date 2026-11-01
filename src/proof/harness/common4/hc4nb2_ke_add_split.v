(* nb port of the hc4b_ke_add_split.v., (kents_add): the malloc'd struct kent split into the pieces the body fills. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4a_nb_cs.
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require Import WgNoise.proof.harness.common4.hc4a_nb_ctx.
Require Import WgNoise.proof.harness.common4.hc4nb2_ke_add_defs.
Require WgNoise.harness.x_cookie_mac.code.
Local Open Scope logic.

Require Import WgNoise.proof.harness.common4.hc4nb2_ke_hf.

#[local] Instance hc4nb2_ke_add_split_cce1 : change_composite_env CKS CS4nb.
Proof. make_cs_preserve CKS CS4nb. Defined.
#[local] Instance hc4nb2_ke_add_split_cce2 : change_composite_env Noise.CS CS4nb.
Proof. make_cs_preserve Noise.CS CS4nb. Defined.

Lemma hc4nb2_ke_add_split_mb_split bl o a b c :
  0 <= a <= b -> b <= c -> Ptrofs.unsigned o + c < Ptrofs.modulus ->
  hc4nb2_ke_hf_mb (Vptr bl o) a c |-- hc4nb2_ke_hf_mb (Vptr bl o) a b * hc4nb2_ke_hf_mb (Vptr bl o) b c.
Proof.
  intros Ha Hb Hm. unfold hc4nb2_ke_hf_mb, offset_val.
  pose proof (Ptrofs.unsigned_range o).
  assert (E: forall x, 0 <= x <= c -> Ptrofs.add o (Ptrofs.repr x) = Ptrofs.repr (Ptrofs.unsigned o + x)).
  { intros x Hx. unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr x) by (unfold Ptrofs.max_unsigned; lia).
    reflexivity. }
  rewrite !E by lia.
  replace (c - a) with ((b - a) + (c - b)) by lia.
  rewrite (memory_block_split Ews bl (Ptrofs.unsigned o + a) (b - a) (c - b)) by lia.
  replace (Ptrofs.unsigned o + a + (b - a)) with (Ptrofs.unsigned o + b) by lia.
  apply derives_refl.
Qed.

Lemma hc4nb2_ke_add_split_fa_eq {cs: compspecs} t gfs p a b :
  @field_compatible cs t gfs p ->
  @nested_field_offset cs t gfs = a -> @sizeof cs (@nested_field_type cs t gfs) = b - a ->
  @field_at_ cs Ews t gfs p = hc4nb2_ke_hf_mb p a b.
Proof.
  intros FC Ea Eb. rewrite (@field_at__memory_block cs), (@field_address_offset cs) by auto.
  unfold hc4nb2_ke_hf_mb. rewrite Eb, Ea. reflexivity.
Qed.

Lemma hc4nb2_ke_add_split_spacer_eq a b p :
  a < b -> spacer Ews a b p = hc4nb2_ke_hf_mb p a b.
Proof.
  intros H. unfold spacer. destruct (Z.eq_dec (b - a) 0); [lia|].
  unfold at_offset, hc4nb2_ke_hf_mb. reflexivity.
Qed.

(* the whole uninitialized struct kent at k (body compspecs CS4nb) = its keypair's entry (raw, at Noise.CS), the
   keypair's other fields (hc4nb2_ke_add_body0, Noise.CS), the snapshot fields (kent_snap_rep None, CKS), the list
   link (CKS) and the padding *)
Ltac hc4nb2_ke_add_split_fc :=
  apply field_compatible_cons; split;
  [unfold in_members; simpl; solve [repeat (first [left; reflexivity | right])] | assumption].

Ltac hc4nb2_ke_add_split_rw cs t gfs p a b :=
  rewrite (@hc4nb2_ke_add_split_fa_eq cs t gfs p a b) by (first [assumption | hc4nb2_ke_add_split_fc | reflexivity]).

Lemma hc4nb2_ke_add_split (k: val) :
  @data_at_ CS4nb Ews t_kent k |--
  !! (@field_compatible CKS t_kent [] k /\ @field_compatible Noise.CS t_kp [] k /\
      @field_compatible Noise.CS t_entry_s [] k) &&
  (@data_at_ Noise.CS Ews t_entry_s k * hc4nb2_ke_add_body0 k * kent_snap_rep k None *
   @field_at_ CKS Ews t_kent [StructField HC._next] k * kent_pads k).
Proof.
  rewrite (@data_at__memory_block CS4nb). Intros. rename H into FC.
  change (@sizeof CS4nb t_kent) with 2392.
  assert (FCK: @field_compatible CKS t_kent [] k).
  { apply (@field_compatible_change_composite CKS CS4nb _ t_kent); [reflexivity | auto]. }
  assert (FKP4: @field_compatible CS4nb t_kent [StructField HC._kp] k) by hc4nb2_ke_add_split_fc.
  assert (FE4: @field_compatible CS4nb t_kent [StructField I._entry; StructField HC._kp] k)
    by hc4nb2_ke_add_split_fc.
  assert (Hp: isptr k) by (destruct FC; auto).
  apply field_compatible_nested_field in FKP4. apply field_compatible_nested_field in FE4.
  change (@nested_field_type CS4nb t_kent [StructField HC._kp]) with t_kp in FKP4.
  change (@nested_field_offset CS4nb t_kent [StructField HC._kp]) with 0 in FKP4.
  change (@nested_field_type CS4nb t_kent [StructField I._entry; StructField HC._kp]) with t_entry_s in FE4.
  change (@nested_field_offset CS4nb t_kent [StructField I._entry; StructField HC._kp]) with 0 in FE4.
  rewrite isptr_offset_val_zero in FKP4, FE4 by exact Hp.
  assert (FKP: @field_compatible Noise.CS t_kp [] k).
  { apply (@field_compatible_change_composite Noise.CS CS4nb _ t_kp); [reflexivity | auto]. }
  assert (FE: @field_compatible Noise.CS t_entry_s [] k).
  { apply (@field_compatible_change_composite Noise.CS CS4nb _ t_entry_s); [reflexivity | auto]. }
  apply andp_right; [apply prop_right; auto|].
  clear FKP4 FE4.
  destruct FC as (_ & _ & Hsz & _). destruct k as [| | | | | bl o]; try contradiction.
  simpl in Hsz. change (@sizeof CS4nb t_kent) with 2392 in Hsz.
  replace (memory_block Ews 2392 (Vptr bl o)) with (hc4nb2_ke_hf_mb (Vptr bl o) 0 2392)
    by (unfold hc4nb2_ke_hf_mb; rewrite isptr_offset_val_zero by exact I; reflexivity).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 2384 2392 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 2376 2384 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 2372 2376 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 2368 2372 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 2365 2368 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 2364 2365 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 2360 2364 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 1336 2360 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 1328 1336 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 1320 1328 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 1314 1320 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 1313 1314 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 1312 1313 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 1304 1312 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 1296 1304 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 1289 1296 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 1257 1289 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 1225 1257 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 1224 1225 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 1220 1224 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 1216 1220 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 1208 1216 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 1200 1208 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 1192 1200 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 1188 1192 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 1184 1188 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 1181 1184 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 1180 1181 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 1176 1180 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 136 1176 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 88 136 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 80 88 ltac:(lia) ltac:(lia) ltac:(lia)).
  sep_apply (hc4nb2_ke_add_split_mb_split bl o 0 32 80 ltac:(lia) ltac:(lia) ltac:(lia)).
  unfold hc4nb2_ke_add_body0, kent_snap_rep, kent_pads, data_at_.
  hc4nb2_ke_add_split_rw Noise.CS t_entry_s (@nil gfield) (Vptr bl o) 0 32.
  hc4nb2_ke_add_split_rw Noise.CS t_kp [StructField I._sending] (Vptr bl o) 32 80.
  hc4nb2_ke_add_split_rw Noise.CS t_kp [StructField I._sending_counter] (Vptr bl o) 80 88.
  hc4nb2_ke_add_split_rw Noise.CS t_kp [StructField I._receiving] (Vptr bl o) 88 136.
  hc4nb2_ke_add_split_rw Noise.CS t_kp [StructField I._receiving_counter] (Vptr bl o) 136 1176.
  hc4nb2_ke_add_split_rw Noise.CS t_kp [StructField I._remote_index] (Vptr bl o) 1176 1180.
  hc4nb2_ke_add_split_rw Noise.CS t_kp [StructField I._i_am_the_initiator] (Vptr bl o) 1180 1181.
  hc4nb2_ke_add_split_rw Noise.CS t_kp [StructField I._refcount] (Vptr bl o) 1184 1188.
  hc4nb2_ke_add_split_rw Noise.CS t_kp [StructField I._rcu] (Vptr bl o) 1188 1192.
  hc4nb2_ke_add_split_rw Noise.CS t_kp [StructField I._internal_id] (Vptr bl o) 1192 1200.
  hc4nb2_ke_add_split_rw CKS t_kent [StructField HC._peer0] (Vptr bl o) 1200 1208.
  hc4nb2_ke_add_split_rw CKS t_kent [StructField HC._next0] (Vptr bl o) 1208 1216.
  hc4nb2_ke_add_split_rw CKS t_kent [StructField HC._type0] (Vptr bl o) 1216 1220.
  hc4nb2_ke_add_split_rw CKS t_kent [StructField HC._index0] (Vptr bl o) 1220 1224.
  hc4nb2_ke_add_split_rw CKS t_kent [StructField HC._hashed0] (Vptr bl o) 1224 1225.
  hc4nb2_ke_add_split_rw CKS t_kent [StructField HC._skey0] (Vptr bl o) 1225 1257.
  hc4nb2_ke_add_split_rw CKS t_kent [StructField HC._rkey0] (Vptr bl o) 1257 1289.
  hc4nb2_ke_add_split_rw CKS t_kent [StructField HC._sbirth0] (Vptr bl o) 1296 1304.
  hc4nb2_ke_add_split_rw CKS t_kent [StructField HC._rbirth0] (Vptr bl o) 1304 1312.
  hc4nb2_ke_add_split_rw CKS t_kent [StructField HC._svalid0] (Vptr bl o) 1312 1313.
  hc4nb2_ke_add_split_rw CKS t_kent [StructField HC._rvalid0] (Vptr bl o) 1313 1314.
  hc4nb2_ke_add_split_rw CKS t_kent [StructField HC._scnt0] (Vptr bl o) 1320 1328.
  hc4nb2_ke_add_split_rw CKS t_kent [StructField HC._rcnt0] (Vptr bl o) 1328 1336.
  hc4nb2_ke_add_split_rw CKS t_kent [StructField HC._bt0] (Vptr bl o) 1336 2360.
  hc4nb2_ke_add_split_rw CKS t_kent [StructField HC._remote_index0] (Vptr bl o) 2360 2364.
  hc4nb2_ke_add_split_rw CKS t_kent [StructField HC._initiator0] (Vptr bl o) 2364 2365.
  hc4nb2_ke_add_split_rw CKS t_kent [StructField HC._refs0] (Vptr bl o) 2368 2372.
  hc4nb2_ke_add_split_rw CKS t_kent [StructField HC._id0] (Vptr bl o) 2376 2384.
  hc4nb2_ke_add_split_rw CKS t_kent [StructField HC._next] (Vptr bl o) 2384 2392.
  rewrite (hc4nb2_ke_add_split_spacer_eq 1181 1184 (Vptr bl o)) by lia.
  rewrite (hc4nb2_ke_add_split_spacer_eq 1289 1296 (Vptr bl o)) by lia.
  rewrite (hc4nb2_ke_add_split_spacer_eq 1314 1320 (Vptr bl o)) by lia.
  rewrite (hc4nb2_ke_add_split_spacer_eq 2365 2368 (Vptr bl o)) by lia.
  rewrite (hc4nb2_ke_add_split_spacer_eq 2372 2376 (Vptr bl o)) by lia.
  cancel.
Qed.
