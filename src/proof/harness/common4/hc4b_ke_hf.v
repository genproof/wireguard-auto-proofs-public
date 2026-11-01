(* (common4 group kents): helpers of kents_free / kents_hashed.
   - hc4b_ke_hf_data_at__cssub: data_at_ of a malloc'd struct is the same at a compspecs and any super-compspecs;
   - hc4b_ke_hf_whole: a kent's cell and its entry make the whole struct kent (with its token). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Local Open Scope logic.

Lemma hc4b_ke_hf_natural_aligned {cs1 cs2: compspecs} (H: cspecs_sub cs1 cs2) id a :
  @complete_type (@cenv_cs cs1) (Tstruct id a) = true ->
  @natural_aligned cs1 natural_alignment (Tstruct id a) = true ->
  @natural_aligned cs2 natural_alignment (Tstruct id a) = true.
Proof.
  destruct H as [_ [Hha Hla]]. intros Hc Hn.
  simpl in Hc. destruct (Maps.PTree.get id (@cenv_cs cs1)) as [co|] eqn:Ec; [|discriminate].
  destruct (proj1 (@ha_env_cs_complete cs1 id) (ex_intro _ co Ec)) as [h Eh].
  destruct (proj1 (@la_env_cs_complete cs1 id) (ex_intro _ co Ec)) as [l El].
  specialize (Hha id). rewrite Eh in Hha. simpl in Hha.
  specialize (Hla id). rewrite El in Hla. simpl in Hla.
  unfold natural_aligned, is_aligned in *. simpl in *.
  unfold legal_alignas_obs in *. rewrite Hha, Hla. rewrite Eh, El in Hn. exact Hn.
Qed.

(* the size and field compatibility of a malloc'd object of type t, at two compspecs *)
Lemma hc4b_ke_hf_data_at__cssub {cs1 cs2: compspecs} (H: cspecs_sub cs1 cs2) sh id a p :
  let t := Tstruct id a in
  @complete_type (@cenv_cs cs1) t = true ->
  @complete_legal_cosu_type (@cenv_cs cs1) t = true ->
  @natural_aligned cs1 natural_alignment t = true ->
  malloc_compatible (@sizeof cs1 t) p ->
  @data_at_ cs1 sh t p = @data_at_ cs2 sh t p.
Proof.
  intros t Hc Hl Hn Hm.
  assert (Hs: @sizeof cs2 t = @sizeof cs1 t).
  { destruct H as [Hce _]. apply (expr_lemmas4.cenv_sub_sizeof Hce); auto. }
  assert (F1: @field_compatible cs1 t nil p) by (apply malloc_compatible_field_compatible; auto).
  assert (F2: @field_compatible cs2 t nil p).
  { apply malloc_compatible_field_compatible.
    - rewrite Hs; auto.
    - destruct H as [Hce _]. apply (semax.cenv_sub_complete_legal_cosu_type _ _ Hce); auto.
    - apply (hc4b_ke_hf_natural_aligned H); auto. }
  rewrite <- (@memory_block_data_at_ cs1) by auto. rewrite <- (@memory_block_data_at_ cs2) by auto.
  rewrite Hs. reflexivity.
Qed.

Section Whole.
#[local] Existing Instance CS4.

#[local] Instance hc4b_ke_hf_cce1 : change_composite_env CKS CS4.
Proof. make_cs_preserve CKS CS4. Defined.
#[local] Instance hc4b_ke_hf_cce2 : change_composite_env Noise.CS CS4.
Proof. make_cs_preserve Noise.CS CS4. Defined.

Lemma hc4b_ke_hf_fa_mb {cs: compspecs} sh t gfs v p :
  @field_at cs sh t gfs v p |--
  memory_block sh (@sizeof cs (@nested_field_type cs t gfs)) (offset_val (@nested_field_offset cs t gfs) p).
Proof.
  assert_PROP (@field_compatible cs t gfs p) as FC by entailer!.
  rewrite <- (@field_address_offset cs) by auto.
  sep_apply (@field_at_field_at_ cs). rewrite (@field_at__memory_block cs). auto.
Qed.

Definition hc4b_ke_hf_mb (k: val) (a b: Z) : mpred := memory_block Ews (b - a) (offset_val a k).

Lemma hc4b_ke_hf_fa_mb_at {cs: compspecs} t gfs v p a b :
  @nested_field_offset cs t gfs = a -> @sizeof cs (@nested_field_type cs t gfs) = b - a ->
  @field_at cs Ews t gfs v p |-- hc4b_ke_hf_mb p a b.
Proof.
  intros <- E. unfold hc4b_ke_hf_mb. rewrite <- E. apply hc4b_ke_hf_fa_mb.
Qed.

Lemma hc4b_ke_hf_spacer_mb a b p :
  a < b -> spacer Ews a b p |-- hc4b_ke_hf_mb p a b.
Proof.
  intros H. unfold spacer. destruct (Z.eq_dec (b - a) 0); [lia|].
  unfold at_offset, hc4b_ke_hf_mb. apply derives_refl.
Qed.

Lemma hc4b_ke_hf_merge bl o a b c :
  0 <= a <= b -> b <= c -> Ptrofs.unsigned o + c < Ptrofs.modulus ->
  hc4b_ke_hf_mb (Vptr bl o) a b * hc4b_ke_hf_mb (Vptr bl o) b c |-- hc4b_ke_hf_mb (Vptr bl o) a c.
Proof.
  intros Ha Hb Hm. unfold hc4b_ke_hf_mb, offset_val.
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

Ltac hc4b_ke_hf_pc cs t gfs k a b :=
  match goal with |- context [@field_at cs Ews t gfs ?v k] =>
    sep_apply (@hc4b_ke_hf_fa_mb_at cs t gfs v k a b eq_refl eq_refl) end.

(* the pieces of a kent at k (as kent_cell, its entry included) -> memory blocks, merged *)
Ltac hc4b_ke_hf_pieces k :=
  hc4b_ke_hf_pc Noise.CS t_entry_s (@nil gfield) k 0 32;
  hc4b_ke_hf_pc Noise.CS t_kp [StructField I._sending] k 32 80;
  hc4b_ke_hf_pc Noise.CS t_kp [StructField I._sending_counter] k 80 88;
  hc4b_ke_hf_pc Noise.CS t_kp [StructField I._receiving] k 88 136;
  hc4b_ke_hf_pc Noise.CS t_kp [StructField I._receiving_counter] k 136 1176;
  hc4b_ke_hf_pc Noise.CS t_kp [StructField I._remote_index] k 1176 1180;
  hc4b_ke_hf_pc Noise.CS t_kp [StructField I._i_am_the_initiator] k 1180 1181;
  sep_apply (hc4b_ke_hf_spacer_mb 1181 1184 k ltac:(lia));
  hc4b_ke_hf_pc Noise.CS t_kp [StructField I._refcount] k 1184 1188;
  hc4b_ke_hf_pc Noise.CS t_kp [StructField I._rcu] k 1188 1192;
  hc4b_ke_hf_pc Noise.CS t_kp [StructField I._internal_id] k 1192 1200;
  hc4b_ke_hf_pc CKS t_kent [StructField HC._peer0] k 1200 1208;
  hc4b_ke_hf_pc CKS t_kent [StructField HC._next0] k 1208 1216;
  hc4b_ke_hf_pc CKS t_kent [StructField HC._type0] k 1216 1220;
  hc4b_ke_hf_pc CKS t_kent [StructField HC._index0] k 1220 1224;
  hc4b_ke_hf_pc CKS t_kent [StructField HC._hashed0] k 1224 1225;
  hc4b_ke_hf_pc CKS t_kent [StructField HC._skey0] k 1225 1257;
  hc4b_ke_hf_pc CKS t_kent [StructField HC._rkey0] k 1257 1289;
  sep_apply (hc4b_ke_hf_spacer_mb 1289 1296 k ltac:(lia));
  hc4b_ke_hf_pc CKS t_kent [StructField HC._sbirth0] k 1296 1304;
  hc4b_ke_hf_pc CKS t_kent [StructField HC._rbirth0] k 1304 1312;
  hc4b_ke_hf_pc CKS t_kent [StructField HC._svalid0] k 1312 1313;
  hc4b_ke_hf_pc CKS t_kent [StructField HC._rvalid0] k 1313 1314;
  sep_apply (hc4b_ke_hf_spacer_mb 1314 1320 k ltac:(lia));
  hc4b_ke_hf_pc CKS t_kent [StructField HC._scnt0] k 1320 1328;
  hc4b_ke_hf_pc CKS t_kent [StructField HC._rcnt0] k 1328 1336;
  hc4b_ke_hf_pc CKS t_kent [StructField HC._bt0] k 1336 2360;
  hc4b_ke_hf_pc CKS t_kent [StructField HC._remote_index0] k 2360 2364;
  hc4b_ke_hf_pc CKS t_kent [StructField HC._initiator0] k 2364 2365;
  sep_apply (hc4b_ke_hf_spacer_mb 2365 2368 k ltac:(lia));
  hc4b_ke_hf_pc CKS t_kent [StructField HC._refs0] k 2368 2372;
  sep_apply (hc4b_ke_hf_spacer_mb 2372 2376 k ltac:(lia));
  hc4b_ke_hf_pc CKS t_kent [StructField HC._id0] k 2376 2384;
  hc4b_ke_hf_pc CKS t_kent [StructField HC._next] k 2384 2392.

Ltac hc4b_ke_hf_merges bl o :=
  let m a b c := sep_apply (hc4b_ke_hf_merge bl o a b c ltac:(lia) ltac:(lia) ltac:(lia)) in
  m 0 32 80; m 0 80 88; m 0 88 136; m 0 136 1176; m 0 1176 1180; m 0 1180 1181; m 0 1181 1184;
  m 0 1184 1188; m 0 1188 1192; m 0 1192 1200; m 0 1200 1208; m 0 1208 1216; m 0 1216 1220;
  m 0 1220 1224; m 0 1224 1225; m 0 1225 1257; m 0 1257 1289; m 0 1289 1296; m 0 1296 1304;
  m 0 1304 1312; m 0 1312 1313; m 0 1313 1314; m 0 1314 1320; m 0 1320 1328; m 0 1328 1336;
  m 0 1336 2360; m 0 2360 2364; m 0 2364 2365; m 0 2365 2368; m 0 2368 2372; m 0 2372 2376;
  m 0 2376 2384; m 0 2384 2392.

Section CSw.
Variable CSw: compspecs.

(* a kent's cell and its entry: the whole struct kent (and its token) *)
Lemma hc4b_ke_hf_whole4 e nx :
  kent_cell CSw e nx * @data_at_ Noise.CS Ews t_entry_s (ke_addr e) |--
  @malloc_token CSw Ews t_kent (ke_addr e) * @data_at_ CS4 Ews t_kent (ke_addr e).
Proof.
  destruct e as [k K s]. unfold kent_cell, kp_body_rep, kent_pads; simpl ke_addr; simpl ke_K; simpl ke_snap.
  Intros. Intros lk r.
  assert (FC: @field_compatible CS4 t_kent [] k).
  { apply (@field_compatible_change_composite CKS CS4 _ t_kent); [reflexivity | auto]. }
  rewrite <- (@memory_block_data_at_ CS4) by auto.
  destruct FC as (Hp & _ & Hsz & _). destruct k as [| | | | | bl o]; try contradiction.
  change (@sizeof CS4 t_kent) with 2392 in *. simpl in Hsz.
  replace (memory_block Ews 2392 (Vptr bl o)) with (hc4b_ke_hf_mb (Vptr bl o) 0 2392)
    by (unfold hc4b_ke_hf_mb; rewrite isptr_offset_val_zero by exact I; reflexivity).
  unfold data_at_, field_at_.
  destruct s as [s|]; unfold kent_snap_rep.
  - hc4b_ke_hf_pieces (Vptr bl o). hc4b_ke_hf_merges bl o. cancel.
  - unfold field_at_. hc4b_ke_hf_pieces (Vptr bl o). hc4b_ke_hf_merges bl o. cancel.
Qed.
End CSw.

End Whole.
