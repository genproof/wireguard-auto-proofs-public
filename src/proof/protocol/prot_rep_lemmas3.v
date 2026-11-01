(* Lemmas about the protocol representation (prot_repr3.v) for the harness pieces and body proofs.  Target: prot_rep_lemmas3 (one conjunction; named corollaries are derived after it). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Local Open Scope logic.

#[local] Existing Instance Noise.CS.

(* ---- a u32 in memory is the 4 bytes of its little-endian encoding (x86_64) ---- *)
Lemma prot_rep3_bytes_of_int_of_bytes l :
  bytes_of_int (length l) (int_of_bytes l) = l.
Proof.
  induction l as [|a l IH]; cbn [bytes_of_int int_of_bytes length]; auto.
  pose proof (Byte.unsigned_range a) as Ha. change Byte.modulus with 256 in Ha.
  f_equal.
  - rewrite <- (Byte.repr_unsigned a) at 2. apply Byte.eqm_samerepr.
    exists (int_of_bytes l). change Byte.modulus with 256. lia.
  - replace ((Byte.unsigned a + int_of_bytes l * 256) / 256) with (int_of_bytes l); auto.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma prot_rep3_le32_encode i : le32 i = encode_int 4 (Int.unsigned i).
Proof.
  unfold le32, encode_int, rev_if_be. cbn [map bytes_of_int Archi.big_endian].
  rewrite !Z.div_div by lia.
  change (2^(8*0)) with 1; change (2^(8*1)) with 256; change (2^(8*2)) with (256*256)%Z;
  change (2^(8*3)) with (256*256*256)%Z. rewrite Z.div_1_r. reflexivity.
Qed.

Lemma prot_rep3_decode32 bl i :
  length bl = 4%nat -> decode_val Mint32 bl = Vint i -> bl = map Byte (le32 i).
Proof.
  intros Hl Hd. unfold decode_val in Hd.
  destruct (proj_bytes bl) as [bs|] eqn:E; [| discriminate].
  apply inj_proj_bytes in E. subst bl. unfold inj_bytes in *. rewrite map_length in Hl.
  inv Hd. f_equal. rewrite prot_rep3_le32_encode.
  unfold decode_int. rewrite Int.unsigned_repr.
  2: { pose proof (int_of_bytes_range (rev_if_be bs)) as R. rewrite rev_if_be_length, Hl in R.
       change (two_p (Z.of_nat 4 * 8)) with (Int.max_unsigned + 1) in R. lia. }
  unfold encode_int. rewrite <- Hl, <- (rev_if_be_length bs), prot_rep3_bytes_of_int_of_bytes.
  apply rev_if_be_involutive.
Qed.

Lemma prot_rep3_encode32 i : decode_val Mint32 (map Byte (le32 i)) = Vint i.
Proof.
  rewrite prot_rep3_le32_encode. unfold decode_val.
  change (map Byte ?l) with (inj_bytes l). rewrite proj_inj_bytes.
  f_equal. apply decode_encode_int_4.
Qed.

Lemma prot_rep3_decode_int1 b : decode_int [b] = Byte.unsigned b.
Proof. unfold decode_int, rev_if_be. cbn [Archi.big_endian int_of_bytes]. lia. Qed.

Lemma prot_rep3_decode8 m c :
  decode_val Mint8unsigned [m] = Vubyte c -> m = Byte c.
Proof.
  intros Hd. unfold decode_val in Hd. destruct m; cbn [proj_bytes] in Hd; try discriminate Hd.
  rewrite prot_rep3_decode_int1 in Hd. unfold Vubyte in Hd.
  assert (Hd': Int.zero_ext 8 (Int.repr (Byte.unsigned i)) = Int.repr (Byte.unsigned c)) by congruence.
  clear Hd; rename Hd' into Hd.
  pose proof (Byte.unsigned_range i) as Hi. pose proof (Byte.unsigned_range c) as Hc.
  change Byte.modulus with 256 in *.
  apply (f_equal Int.unsigned) in Hd. rewrite Int.zero_ext_mod in Hd by rep_lia.
  change (two_p 8) with 256 in Hd. rewrite !Int.unsigned_repr in Hd by rep_lia.
  rewrite Z.mod_small in Hd by lia.
  f_equal. rewrite <- (Byte.repr_unsigned i), Hd. apply Byte.repr_unsigned.
Qed.

Lemma prot_rep3_encode8 c : decode_val Mint8unsigned [Byte c] = Vubyte c.
Proof.
  unfold decode_val. cbn [proj_bytes]. rewrite prot_rep3_decode_int1. unfold Vubyte.
  pose proof (Byte.unsigned_range c) as Hc. change Byte.modulus with 256 in *.
  f_equal. rewrite <- (Int.repr_unsigned (Int.zero_ext 8 (Int.repr (Byte.unsigned c)))).
  rewrite Int.zero_ext_mod by rep_lia. change (two_p 8) with 256.
  rewrite Int.unsigned_repr by rep_lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma prot_rep3_allp_jam_ext {S': address -> Prop} (S: forall l, {S' l}+{~ S' l})
    (P Q: address -> mpred) :
  (forall l, S' l -> P l = Q l) ->
  predicates_hered.allp (res_predicates.jam S P res_predicates.noat) =
  predicates_hered.allp (res_predicates.jam S Q res_predicates.noat).
Proof.
  intros H. apply predicates_hered.pred_ext; intros w Hw l; specialize (Hw l); simpl in *;
  destruct (S l); auto; [rewrite <- H | rewrite H]; auto.
Qed.

Lemma prot_rep3_split1 sh (v: address -> memval) b z n r : n >= 0 -> r = 1 + n ->
  predicates_hered.allp (res_predicates.jam (adr_range_dec (b,z) r)
    (fun loc => res_predicates.yesat compcert_rmaps.R.NoneP (compcert_rmaps.VAL (v loc)) sh loc)
    res_predicates.noat) =
  predicates_hered.allp (res_predicates.jam (adr_range_dec (b,z) 1)
    (fun loc => res_predicates.yesat compcert_rmaps.R.NoneP (compcert_rmaps.VAL (v loc)) sh loc)
    res_predicates.noat) *
  predicates_hered.allp (res_predicates.jam (adr_range_dec (b,z+1) n)
    (fun loc => res_predicates.yesat compcert_rmaps.R.NoneP (compcert_rmaps.VAL (v loc)) sh loc)
    res_predicates.noat).
Proof.
  intros.
  assert (exists resp, res_predicates.is_resource_pred
     (fun l' => res_predicates.yesat compcert_rmaps.R.NoneP (compcert_rmaps.VAL (v l')) sh l') resp)
    by (eexists; apply res_predicates.is_resource_pred_YES_VAL').
  apply res_predicates.allp_jam_split2; auto.
  + split; intros [? ?]; unfold adr_range.
    - assert (z <= z0 < z + r <-> z <= z0 < z + 1 \/ z + 1 <= z0 < z + 1 + n) by lia.
      tauto.
    - lia.
  + intros l m sh0 k _ Hy Hr. destruct Hy as [rsh Hy]. simpl in Hy. rewrite Hy in Hr. inv Hr. auto.
Qed.

Lemma prot_rep3_am32 sh i b z : (4 | z) ->
  res_predicates.address_mapsto Mint32 (Vint i) sh (b,z) =
  predicates_hered.allp (res_predicates.jam (adr_range_dec (b,z) 4)
    (fun loc => res_predicates.yesat compcert_rmaps.R.NoneP
       (compcert_rmaps.VAL (nth (Z.to_nat (snd loc - z)) (map Byte (le32 i)) Undef)) sh loc)
    res_predicates.noat).
Proof.
  intros Ha. apply predicates_hered.pred_ext.
  - intros w [bl [[Hl [Hd _]] H]]. apply prot_rep3_decode32 in Hd; [subst bl; exact H | exact Hl].
  - intros w H. exists (map Byte (le32 i)).
    split; [split; [reflexivity | split; [apply prot_rep3_encode32 | exact Ha]] | exact H].
Qed.

Lemma prot_rep3_am8 sh c b z :
  res_predicates.address_mapsto Mint8unsigned (Vubyte c) sh (b,z) =
  predicates_hered.allp (res_predicates.jam (adr_range_dec (b,z) 1)
    (fun loc => res_predicates.yesat compcert_rmaps.R.NoneP (compcert_rmaps.VAL (Byte c)) sh loc)
    res_predicates.noat).
Proof.
  rewrite <- (prot_rep3_allp_jam_ext _ (fun loc => res_predicates.yesat compcert_rmaps.R.NoneP
       (compcert_rmaps.VAL (nth (Z.to_nat (snd loc - z)) [Byte c] Undef)) sh loc)).
  2: { intros [b' z'] [_ Hr]. simpl. replace (Z.to_nat (z' - z)) with 0%nat by lia. reflexivity. }
  apply predicates_hered.pred_ext.
  - intros w [bl [[Hl [Hd _]] H]]. destruct bl as [|m [|]]; simpl in Hl; try discriminate.
    apply prot_rep3_decode8 in Hd. subst m. exact H.
  - intros w H. exists [Byte c].
    split; [split; [reflexivity | split; [apply prot_rep3_encode8 | apply Z.divide_1_l]] | exact H].
Qed.

Lemma prot_rep3_am32_split sh i b z c0 c1 c2 c3 : le32 i = [c0;c1;c2;c3] -> (4 | z) ->
  res_predicates.address_mapsto Mint32 (Vint i) sh (b,z) =
  res_predicates.address_mapsto Mint8unsigned (Vubyte c0) sh (b,z) *
  (res_predicates.address_mapsto Mint8unsigned (Vubyte c1) sh (b,z+1) *
   (res_predicates.address_mapsto Mint8unsigned (Vubyte c2) sh (b,z+2) *
    res_predicates.address_mapsto Mint8unsigned (Vubyte c3) sh (b,z+3))).
Proof.
  intros Hle Ha. rewrite prot_rep3_am32 by auto. rewrite !prot_rep3_am8. rewrite Hle.
  rewrite (prot_rep3_split1 _ _ b z 3 4) by lia.
  rewrite (prot_rep3_split1 _ _ b (z+1) 2 3) by lia.
  rewrite (prot_rep3_split1 _ _ b (z+1+1) 1 2) by lia.
  replace (z+1+1) with (z+2) by lia. replace (z+2+1) with (z+3) by lia.
  f_equal; [| f_equal; [| f_equal]]; apply prot_rep3_allp_jam_ext; intros [b' z'] [_ Hr];
    simpl snd.
  - replace (Z.to_nat (z' - z)) with 0%nat by lia. reflexivity.
  - replace (Z.to_nat (z' - z)) with 1%nat by lia. reflexivity.
  - replace (Z.to_nat (z' - z)) with 2%nat by lia. reflexivity.
  - replace (Z.to_nat (z' - z)) with 3%nat by lia. reflexivity.
Qed.

Lemma prot_rep3_or_simpl (P Q: Prop) (X Y: mpred) : P -> ~ Q -> (!!P && X) || (!!Q && Y) = X.
Proof.
  intros HP HQ. apply pred_ext.
  - apply orp_left; [apply andp_left2, derives_refl |].
    apply derives_extract_prop; intro; contradiction.
  - apply orp_right1. apply andp_right; [apply prop_right; auto | apply derives_refl].
Qed.

Lemma prot_rep3_tc_ubyte c : tc_val tuchar (Vubyte c).
Proof.
  simpl. pose proof (Byte.unsigned_range_2 c). rewrite Int.unsigned_repr; rep_lia.
Qed.

Lemma prot_rep3_mapsto_u32 sh i b o c0 c1 c2 c3 : le32 i = [c0;c1;c2;c3] ->
  Ptrofs.unsigned o + 4 <= Ptrofs.modulus -> (4 | Ptrofs.unsigned o) ->
  mapsto sh tuint (Vptr b o) (Vint i) =
  mapsto sh tuchar (Vptr b o) (Vubyte c0) *
  (mapsto sh tuchar (offset_val 1 (Vptr b o)) (Vubyte c1) *
   (mapsto sh tuchar (offset_val 2 (Vptr b o)) (Vubyte c2) *
    mapsto sh tuchar (offset_val 3 (Vptr b o)) (Vubyte c3))).
Proof.
  intros Hle Hs Ha.
  assert (Hk: forall k, 0 <= k <= 3 -> Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr k)) = Ptrofs.unsigned o + k).
  { intros k Hk. pose proof (Ptrofs.unsigned_range o).
    rewrite Ptrofs.add_unsigned, (Ptrofs.unsigned_repr k), Ptrofs.unsigned_repr; rep_lia. }
  unfold mapsto, offset_val. simpl access_mode. simpl type_is_volatile. cbv iota beta.
  rewrite !Hk by lia. set (z := Ptrofs.unsigned o) in *.
  destruct (readable_share_dec sh).
  - rewrite !prot_rep3_or_simpl by (first [apply prot_rep3_tc_ubyte | exact I | discriminate]).
    apply prot_rep3_am32_split; auto.
  - rewrite !prop_true_andp
      by (split; [intros _; first [apply prot_rep3_tc_ubyte | exact I] | first [exact Ha | apply Z.divide_1_l]]).
    simpl size_chunk.
    rewrite (res_predicates.nonlock_permission_bytes_split2 1 3 4) by lia.
    rewrite (res_predicates.nonlock_permission_bytes_split2 1 2 3) by lia.
    rewrite (res_predicates.nonlock_permission_bytes_split2 1 1 2) by lia.
    replace (z+1+1) with (z+2) by lia. replace (z+2+1) with (z+3) by lia. reflexivity.
Qed.

Lemma prot_rep3_le32_shape i : exists c0 c1 c2 c3, le32 i = [c0;c1;c2;c3].
Proof. do 4 eexists. reflexivity. Qed.

Lemma prot_rep3_u32_le {cs: compspecs} sh i p :
  field_compatible tuint [] p ->
  data_at sh tuint (Vint i) p = data_at sh (tarray tuchar 4) (bytes (le32 i)) p.
Proof.
  intros Hfc.
  destruct (prot_rep3_le32_shape i) as (c0 & c1 & c2 & c3 & Hle). rewrite Hle. unfold bytes. cbn [map].
  rewrite <- (mapsto_data_at' sh tuint (Vint i) (Vint i) p) by auto.
  destruct p; try (destruct Hfc; contradiction).
  assert (Hfc2: field_compatible (tarray tuchar 4) [] (Vptr b i0)).
  { destruct Hfc as (? & ? & ? & ? & ?). repeat split; auto.
    apply align_compatible_rec_Tarray; intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  unfold data_at, field_at. rewrite data_at_rec_eq. simpl.
  unfold at_offset, aggregate_pred.aggregate_pred.array_pred, aggregate_pred.array_pred,
    aggregate_pred.rangespec.
  simpl. rewrite !by_value_data_at_rec_nonvolatile by reflexivity.
  unfold unfold_reptype; simpl. rewrite sepcon_emp.
  rewrite !prop_true_andp by (auto; reflexivity).
  unfold Znth; simpl.
  destruct Hfc as (_ & _ & Hsz & Hal & _). simpl in Hsz.
  apply align_compatible_rec_by_value_inv with (ch := Mint32) in Hal; [| reflexivity].
  rewrite (prot_rep3_mapsto_u32 sh i b i0 c0 c1 c2 c3 Hle) by (first [lia | exact Hal]).
  unfold offset_val. change (Ptrofs.repr 0) with Ptrofs.zero. rewrite !Ptrofs.add_zero. reflexivity.
Qed.

(* ---- byte buffers ---- *)
Lemma prot_rep3_bytes_app sh l1 l2 p :
  field_compatible (tarray tuchar (Zlength l1 + Zlength l2)) [] p ->
  bytes_at sh (l1 ++ l2) p = bytes_at sh l1 p * bytes_at sh l2 (offset_val (Zlength l1) p).
Proof.
  intros FC. unfold bytes_at, bytes. rewrite map_app, Zlength_app.
  rewrite (split2_data_at_Tarray_app (Zlength l1)) by list_solve.
  rewrite field_address0_offset by (apply arr_field_compatible0; [exact FC | list_solve]).
  change (nested_field_offset (tarray tuchar (Zlength l1 + Zlength l2)) (SUB Zlength l1)) with (0 + 1 * Zlength l1).
  rewrite Z.add_simpl_l. f_equal. f_equal. f_equal. lia.
Qed.

Lemma prot_rep3_field sh t gfs v m :
  field_compatible t gfs m ->
  field_at sh t gfs v m = data_at sh (nested_field_type t gfs) v (offset_val (nested_field_offset t gfs) m).
Proof.
  intros FC. rewrite field_at_data_at, field_address_offset by auto. reflexivity.
Qed.

Lemma prot_rep3_fc_bytes {cs: compspecs} t p k len :
  field_compatible t [] p -> 0 <= k -> 0 <= len -> k + len <= sizeof t ->
  field_compatible (tarray tuchar len) [] (offset_val k p).
Proof.
  intros (P1 & P2 & P3 & P4 & P5) Hk Hl Hn. destruct p; try contradiction.
  unfold size_compatible in P3. pose proof (Ptrofs.unsigned_range i).
  split3; [|reflexivity|split3].
  - exact I.
  - unfold size_compatible; simpl offset_val. unfold Ptrofs.add.
    rewrite (Ptrofs.unsigned_repr k) by rep_lia. rewrite Ptrofs.unsigned_repr by rep_lia.
    simpl sizeof. rewrite Z.max_r by lia. lia.
  - unfold align_compatible; simpl offset_val. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l].
  - exact I.
Qed.

Lemma prot_rep3_bytes_app_at sh l1 l2 p k k2 n1 n2 :
  Zlength l1 = n1 -> Zlength l2 = n2 -> k2 = k + n1 ->
  field_compatible (tarray tuchar (n1 + n2)) [] (offset_val k p) ->
  bytes_at sh (l1 ++ l2) (offset_val k p) = bytes_at sh l1 (offset_val k p) * bytes_at sh l2 (offset_val k2 p).
Proof.
  intros; subst. rewrite prot_rep3_bytes_app by auto. rewrite offset_offset_val. reflexivity.
Qed.

Lemma prot_rep3_le32_len v : Zlength (le32 v) = 4.
Proof. reflexivity. Qed.

Ltac prot_rep3_lens :=
  repeat rewrite ?Zlength_app, ?prot_rep3_le32_len;
  repeat match goal with H: Zlength _ = _ |- _ => rewrite H end; try lia.

Lemma prot_rep3_init_eq sh m M :
  field_compatible t_init [] m -> im_ok M ->
  data_at sh t_init (init_val M) m = bytes_at sh (init_bytes M) m.
Proof.
  intros FC OK.
  unfold_data_at (data_at _ _ _ m).
  assert (EH: forall v, field_at sh t_init (DOT noise.code._header) v m =
                        field_at sh t_init (DOT noise.code._header DOT noise.code._type) v m).
  { intros v. apply pred_ext. unfold_field_at 1%nat. cancel. unfold_field_at 2%nat. cancel. }
  assert (EM: forall v, field_at sh t_init (DOT noise.code._macs) v m =
                        field_at sh t_init (DOT noise.code._macs DOT noise.code._mac1) (fst v) m *
                        field_at sh t_init (DOT noise.code._macs DOT noise.code._mac2) (snd v) m).
  { intros v. apply pred_ext.
    unfold_field_at (field_at _ _ (DOT noise.code._macs) _ _). cancel.
    unfold_field_at (field_at _ _ (DOT noise.code._macs) _ _). cancel. }
  rewrite EH, EM; clear EH EM.
  rewrite !prot_rep3_field by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset. unfold init_val; simpl fst; simpl snd.
  rewrite (prot_rep3_u32_le sh (im_type M) (offset_val 0 m))
    by exact (field_compatible_nested_field t_init (DOT noise.code._header DOT noise.code._type) m
                ltac:(auto with field_compatible)).
  rewrite (prot_rep3_u32_le sh (im_sender M) (offset_val 4 m))
    by exact (field_compatible_nested_field t_init (DOT code._sender_index) m
                ltac:(auto with field_compatible)).
  destruct OK as (L1 & L2 & L3 & L4 & L5).
  replace (bytes_at sh (init_bytes M) m) with (bytes_at sh (init_bytes M) (offset_val 0 m))
    by (rewrite isptr_offset_val_zero by (destruct FC; auto); reflexivity).
  unfold init_bytes.
  rewrite (prot_rep3_bytes_app_at sh (le32 (im_type M)) _ m 0 4 4 144)
    by (prot_rep3_lens; apply (prot_rep3_fc_bytes t_init); auto; simpl; lia).
  rewrite (prot_rep3_bytes_app_at sh (le32 (im_sender M)) _ m 4 8 4 140)
    by (prot_rep3_lens; apply (prot_rep3_fc_bytes t_init); auto; simpl; lia).
  rewrite (prot_rep3_bytes_app_at sh (im_eph M) _ m 8 40 32 108)
    by (prot_rep3_lens; apply (prot_rep3_fc_bytes t_init); auto; simpl; lia).
  rewrite (prot_rep3_bytes_app_at sh (im_encs M) _ m 40 88 48 60)
    by (prot_rep3_lens; apply (prot_rep3_fc_bytes t_init); auto; simpl; lia).
  rewrite (prot_rep3_bytes_app_at sh (im_enct M) _ m 88 116 28 32)
    by (prot_rep3_lens; apply (prot_rep3_fc_bytes t_init); auto; simpl; lia).
  rewrite (prot_rep3_bytes_app_at sh (im_mac1 M) _ m 116 132 16 16)
    by (prot_rep3_lens; apply (prot_rep3_fc_bytes t_init); auto; simpl; lia).
  unfold bytes_at. rewrite !prot_rep3_le32_len, L1, L2, L3, L4, L5. reflexivity.
Qed.

Lemma prot_rep3_resp_eq sh m M :
  field_compatible t_resp [] m -> rm_ok M ->
  data_at sh t_resp (resp_val M) m = bytes_at sh (resp_bytes M) m.
Proof.
  intros FC OK.
  unfold_data_at (data_at _ _ _ m).
  assert (EH: forall v, field_at sh t_resp (DOT noise.code._header) v m =
                        field_at sh t_resp (DOT noise.code._header DOT noise.code._type) v m).
  { intros v. apply pred_ext. unfold_field_at 1%nat. cancel. unfold_field_at 2%nat. cancel. }
  assert (EM: forall v, field_at sh t_resp (DOT noise.code._macs) v m =
                        field_at sh t_resp (DOT noise.code._macs DOT noise.code._mac1) (fst v) m *
                        field_at sh t_resp (DOT noise.code._macs DOT noise.code._mac2) (snd v) m).
  { intros v. apply pred_ext.
    unfold_field_at (field_at _ _ (DOT noise.code._macs) _ _). cancel.
    unfold_field_at (field_at _ _ (DOT noise.code._macs) _ _). cancel. }
  rewrite EH, EM; clear EH EM.
  rewrite !prot_rep3_field by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset. unfold resp_val; simpl fst; simpl snd.
  rewrite (prot_rep3_u32_le sh (rm_type M) (offset_val 0 m))
    by exact (field_compatible_nested_field t_resp (DOT noise.code._header DOT noise.code._type) m
                ltac:(auto with field_compatible)).
  rewrite (prot_rep3_u32_le sh (rm_sender M) (offset_val 4 m))
    by exact (field_compatible_nested_field t_resp (DOT code._sender_index) m
                ltac:(auto with field_compatible)).
  rewrite (prot_rep3_u32_le sh (rm_receiver M) (offset_val 8 m))
    by exact (field_compatible_nested_field t_resp (DOT code._receiver_index) m
                ltac:(auto with field_compatible)).
  destruct OK as (L1 & L2 & L3 & L4).
  replace (bytes_at sh (resp_bytes M) m) with (bytes_at sh (resp_bytes M) (offset_val 0 m))
    by (rewrite isptr_offset_val_zero by (destruct FC; auto); reflexivity).
  unfold resp_bytes.
  rewrite (prot_rep3_bytes_app_at sh (le32 (rm_type M)) _ m 0 4 4 88)
    by (prot_rep3_lens; apply (prot_rep3_fc_bytes t_resp); auto; simpl; lia).
  rewrite (prot_rep3_bytes_app_at sh (le32 (rm_sender M)) _ m 4 8 4 84)
    by (prot_rep3_lens; apply (prot_rep3_fc_bytes t_resp); auto; simpl; lia).
  rewrite (prot_rep3_bytes_app_at sh (le32 (rm_receiver M)) _ m 8 12 4 80)
    by (prot_rep3_lens; apply (prot_rep3_fc_bytes t_resp); auto; simpl; lia).
  rewrite (prot_rep3_bytes_app_at sh (rm_eph M) _ m 12 44 32 48)
    by (prot_rep3_lens; apply (prot_rep3_fc_bytes t_resp); auto; simpl; lia).
  rewrite (prot_rep3_bytes_app_at sh (rm_encn M) _ m 44 60 16 32)
    by (prot_rep3_lens; apply (prot_rep3_fc_bytes t_resp); auto; simpl; lia).
  rewrite (prot_rep3_bytes_app_at sh (rm_mac1 M) _ m 60 76 16 16)
    by (prot_rep3_lens; apply (prot_rep3_fc_bytes t_resp); auto; simpl; lia).
  unfold bytes_at. rewrite !prot_rep3_le32_len, L1, L2, L3, L4. reflexivity.
Qed.

(* ---- the pool ---- *)
Section Pool.
Context {A: Type}.

Lemma prot_rep3_split (D: list (val * share * A)) a sh E (f: val * share * A -> mpred) :
  sfind D a = Some (sh, E) -> iter_sepcon f D = f (a, sh, E) * iter_sepcon f (sdel D a).
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; reflexivity|].
  rewrite (IH H); simpl. rewrite <- !sepcon_assoc, (sepcon_comm (f _) (f _)). reflexivity.
Qed.

Lemma prot_rep3_sfind_in (D: list (val * share * A)) a :
  In a (saddrs D) -> exists sh E, sfind D a = Some (sh, E).
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [contradiction|].
  destruct (EqDec_val x a); [eauto|]. destruct H; [congruence|auto].
Qed.

Lemma prot_rep3_sfind_In (D: list (val * share * A)) a sh E :
  sfind D a = Some (sh, E) -> In (a, sh, E) D.
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); [inv H; auto|auto].
Qed.

Lemma prot_rep3_saddrs_in (D: list (val * share * A)) x sh E : In (x, sh, E) D -> In x (saddrs D).
Proof. intros H. unfold saddrs. apply in_map_iff. exists (x, sh, E). split; auto. Qed.

Lemma prot_rep3_sdel_in (D: list (val * share * A)) a x sh E : In (x, sh, E) (sdel D a) -> In (x, sh, E) D.
Proof.
  induction D as [|[[y shy] w] D IH]; simpl; intros H; auto.
  destruct (EqDec_val y a); [right; auto|]. destruct H; [left; auto | right; auto].
Qed.

Lemma prot_rep3_sdel_saddrs (D: list (val * share * A)) a x : In x (saddrs (sdel D a)) -> In x (saddrs D).
Proof.
  induction D as [|[[y shy] w] D IH]; simpl; intros H; auto.
  destruct (EqDec_val y a); [right; auto|]. destruct H; [left; auto | right; auto].
Qed.

Lemma prot_rep3_sdel_nodup (D: list (val * share * A)) a : NoDup (saddrs D) -> NoDup (saddrs (sdel D a)).
Proof.
  induction D as [|[[y shy] w] D IH]; simpl; intros H; auto. inv H.
  destruct (EqDec_val y a); auto. simpl. constructor; auto.
  intros H. apply H2. eapply prot_rep3_sdel_saddrs; eauto.
Qed.

Lemma prot_rep3_saddrs_sdel (D: list (val * share * A)) a x :
  In x (saddrs D) -> x <> a -> In x (saddrs (sdel D a)).
Proof.
  induction D as [|[[y shy] w] D IH]; simpl; intros H Hne; [contradiction|].
  destruct (EqDec_val y a).
  - subst. destruct H; [congruence|auto].
  - simpl. destruct H; [auto|right; auto].
Qed.
End Pool.

Lemma prot_rep3_vremove_notin e L : ~ In e L -> vremove e L = L.
Proof.
  induction L as [|x L IH]; simpl; intros H; auto.
  destruct (EqDec_val x e); [subst; exfalso; auto|]. rewrite IH; auto.
Qed.

Lemma prot_rep3_succ_notin a L : ~ In a L -> succ_in L a = nullval.
Proof.
  induction L as [|x L IH]; simpl; intros H; auto.
  destruct (EqDec_val x a); [subst; exfalso; auto|]. auto.
Qed.

Lemma prot_rep3_vin_notin a L : ~ In a L -> vin a L = false.
Proof. intros H. unfold vin. destruct (in_dec eq_dec a L); [contradiction|reflexivity]. Qed.

Lemma prot_rep3_glb sh1 sh2 :
  writable_share sh1 -> readable_share sh2 -> sepalg.nonidentity (Share.glb sh1 sh2).
Proof.
  intros [_ HW] HR N.
  apply HR.
  apply leq_join_sub, Share.ord_spec1 in HW.
  apply identity_share_bot in N.
  rewrite HW, Share.glb_assoc, N, Share.glb_bot.
  apply bot_identity.
Qed.

Lemma prot_rep3_pool_add sht tab T a sh E :
  writable_share sh -> itable sht tab T * entry_out sh a E |-- itable sht tab (t_add T a sh E).
Proof.
  intros W. unfold itable. Intros. destruct H as (H1 & H2 & H3 & H4).
  destruct (in_dec eq_dec a (saddrs (t_D T))) as [Hin|Hnin].
  - destruct (prot_rep3_sfind_in _ _ Hin) as (sh' & E' & HE).
    assert (W': writable_share sh').
    { apply prot_rep3_sfind_In in HE. rewrite Forall_forall in H4. apply (H4 _ HE). }
    rewrite (prot_rep3_split _ _ _ _ _ HE). unfold pool_item_rep at 1, entry_out, entry_at.
    sep_apply (data_at_conflict_glb sh' sh t_entry_s (entry_val E' (succ_in (t_L T) a) (vin a (t_L T)))
                 (entry_val E nullval false) a (prot_rep3_glb _ _ W' (writable_readable W))
                 ltac:(simpl; lia)).
    rewrite !FF_sepcon. apply FF_left.
  - assert (HL: ~ In a (t_L T)) by auto.
    unfold t_add; simpl. apply andp_right.
    + apply prop_right. split3; [auto | | split].
      * intros x Hx. right. auto.
      * constructor; auto.
      * constructor; auto.
    + unfold pool_item_rep at 1, entry_out.
      rewrite (prot_rep3_succ_notin _ _ HL), (prot_rep3_vin_notin _ _ HL). cancel.
      apply derives_refl.
Qed.

Lemma prot_rep3_pool_free sht tab T a sh E :
  sfind (t_D T) a = Some (sh, E) -> ~ In a (t_L T) ->
  itable sht tab T |-- itable sht tab (t_free T a) * entry_out sh a E.
Proof.
  intros HE HL. unfold itable. Intros.
  rewrite (prot_rep3_split _ _ _ _ _ HE).
  unfold t_free; simpl. rewrite (prot_rep3_vremove_notin _ _ HL).
  unfold pool_item_rep at 1, entry_out.
  rewrite (prot_rep3_succ_notin _ _ HL), (prot_rep3_vin_notin _ _ HL).
  destruct H as (H1 & H2 & H3 & H4).
  apply andp_right.
  - apply prop_right. unfold itable_wf; simpl. split; [auto|split; [|split]].
    + intros x Hx. apply prot_rep3_saddrs_sdel; [auto|]. intro; subst; contradiction.
    + apply prot_rep3_sdel_nodup; auto.
    + rewrite Forall_forall in *. intros [[x shx] w] Hin. apply (H4 (x, shx, w)).
      eapply prot_rep3_sdel_in; eauto.
  - unfold pool_item_rep. cancel.
Qed.

(* ---- whole objects ---- *)
Lemma prot_rep3_kp_entry k E n h :
  field_compatible t_kp [] k -> entry_at Ews k E n h |-- field_at_ Ews t_kp (DOT I._entry) k.
Proof.
  intros FC. unfold entry_at, field_at_. rewrite field_at_data_at.
  rewrite field_address_offset by auto with field_compatible. simpl.
  rewrite isptr_offset_val_zero by (destruct FC; auto). apply data_at_data_at_.
Qed.

Lemma prot_rep3_kp_whole CSw k K E n h :
  keypair_rep CSw k K * entry_at Ews k E n h |--
  @malloc_token CSw Ews (tarray tuchar SIZEOF_KEYPAIR) k * @data_at_ Noise.CS Ews (tarray tuchar SIZEOF_KEYPAIR) k.
Proof.
  assert_PROP (@field_compatible Noise.CS t_kp [] k) as FC by (unfold keypair_rep; Intros lk r; apply prop_right; tauto).
  sep_apply (prot_rep3_kp_entry k E n h FC).
  unfold keypair_rep. Intros lk r. cancel.
  eapply derives_trans with (@data_at_ Noise.CS Ews t_kp k).
  2:{ rewrite data_at__memory_block by auto. Intros. unfold SIZEOF_KEYPAIR.
      change (@sizeof Noise.CS t_kp) with 1200.
      rewrite (@memory_block_data_at__tarray_tuchar_eq Noise.CS) by (simpl; rep_lia). auto. }
  unfold_data_at (@data_at_ Noise.CS Ews t_kp k).
  repeat match goal with |- _ |-- ?R => match R with context [@field_at Noise.CS Ews t_kp ?g ?v k] =>
    change (@field_at Noise.CS Ews t_kp g v k) with (@field_at_ Noise.CS Ews t_kp g k) end end.
  repeat match goal with |- context [@field_at Noise.CS Ews t_kp ?g ?v k] =>
    sep_apply (@field_at_field_at_ Noise.CS Ews t_kp g v k) end.
  cancel.
Qed.

Lemma prot_rep3_hs_entry sh h E n hd :
  field_compatible t_hs [] h -> entry_at sh h E n hd |-- field_at_ sh t_hs (DOT I._entry) h.
Proof.
  intros FC. unfold entry_at, field_at_. rewrite field_at_data_at.
  rewrite field_address_offset by auto with field_compatible. simpl.
  rewrite isptr_offset_val_zero by (destruct FC; auto). apply data_at_data_at_.
Qed.

Lemma prot_rep3_hs_fc sh h H : hs_rep sh h H |-- !! field_compatible t_hs [] h.
Proof.
  unfold hs_rep. Intros lk.
  assert_PROP (field_compatible t_hs (DOT I._state) h) by entailer!.
  apply prop_right. destruct H1 as (? & ? & ? & ? & ?); split3; auto; split3; auto; exact I.
Qed.

Lemma prot_rep3_hs_whole sh h H E n hd :
  hs_rep sh h H * entry_at sh h E n hd |-- data_at_ sh t_hs h.
Proof.
  assert_PROP (field_compatible t_hs [] h) as FC by (sep_apply (prot_rep3_hs_fc sh h H); entailer!).
  sep_apply (prot_rep3_hs_entry sh h E n hd FC).
  unfold hs_rep. Intros lk.
  unfold_data_at (data_at_ sh t_hs h).
  repeat match goal with |- _ |-- ?R => match R with context [@field_at Noise.CS sh t_hs ?g ?v h] =>
    change (@field_at Noise.CS sh t_hs g v h) with (@field_at_ Noise.CS sh t_hs g h) end end.
  repeat match goal with |- context [@field_at Noise.CS sh t_hs ?g ?v h] =>
    sep_apply (@field_at_field_at_ Noise.CS sh t_hs g v h) end.
  cancel.
Qed.

Lemma prot_rep3_peer_whole sh p P E n h :
  peer_rep sh p P * entry_at sh (hs_addr p) E n h |-- data_at_ sh t_peer p.
Proof.
  unfold peer_rep. Intros.
  sep_apply (prot_rep3_hs_whole sh (hs_addr p) (p_hs P) E n h).
  assert (FH: data_at_ sh t_hs (hs_addr p) |-- field_at_ sh t_peer (DOT I._handshake) p).
  { unfold field_at_. rewrite field_at_data_at. rewrite field_address_offset by auto with field_compatible.
    apply derives_refl. }
  assert (FK: kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) |-- field_at_ sh t_peer (DOT I._keypairs) p).
  { unfold kps_rep. Intros lk. unfold field_at_. rewrite field_at_data_at.
    rewrite field_address_offset by auto with field_compatible. apply data_at_data_at_. }
  assert (FC: cookie_rep sh (cookie_addr p) (p_cookie P) |-- field_at_ sh t_peer (DOT I._latest_cookie) p).
  { unfold cookie_rep. Intros lk. unfold field_at_. rewrite field_at_data_at.
    rewrite field_address_offset by auto with field_compatible. apply data_at_data_at_. }
  sep_apply FH. sep_apply FK. sep_apply FC.
  unfold_data_at (data_at_ sh t_peer p).
  repeat match goal with |- _ |-- ?R => match R with context [@field_at Noise.CS sh t_peer ?g ?v p] =>
    change (@field_at Noise.CS sh t_peer g v p) with (@field_at_ Noise.CS sh t_peer g p) end end.
  repeat match goal with |- context [@field_at Noise.CS sh t_peer ?g ?v p] =>
    sep_apply (@field_at_field_at_ Noise.CS sh t_peer g v p) end.
  cancel.
Qed.

(* a byte array is the same predicate in every compspecs (as libc_bytes.v) *)
Lemma prot_rep3_data_at__cs (cs1 cs2: compspecs) sh n p :
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof.
  unfold data_at_, field_at_, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible, size_compatible, align_compatible.
  assert (forall (ce: composite_env) z, align_compatible_rec ce (tarray tuchar n) z).
  { intros. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  destruct p; simpl; try tauto.
  pose proof (H (@cenv_cs cs1) (Ptrofs.unsigned i)). pose proof (H (@cenv_cs cs2) (Ptrofs.unsigned i)). tauto.
Qed.

Theorem prot_rep_lemmas3 :
  (* a handshake message struct and its byte image (x86_64: little-endian u32 fields, no padding) *)
  (forall sh m M, init_rep sh m M |-- bytes_at sh (init_bytes M) m) /\
  (forall sh m M, field_compatible t_init [] m -> im_ok M ->
     bytes_at sh (init_bytes M) m |-- init_rep sh m M) /\
  (forall sh m M, resp_rep sh m M |-- bytes_at sh (resp_bytes M) m) /\
  (forall sh m M, field_compatible t_resp [] m -> rm_ok M ->
     bytes_at sh (resp_bytes M) m |-- resp_rep sh m M) /\
  (* an entry outside the table joins the pool; an unhashed entry leaves it *)
  (forall sht tab T a sh E, writable_share sh ->
     itable sht tab T * entry_out sh a E |-- itable sht tab (t_add T a sh E)) /\
  (forall sht tab T a sh E, sfind (t_D T) a = Some (sh, E) -> ~ In a (t_L T) ->
     itable sht tab T |-- itable sht tab (t_free T a) * entry_out sh a E) /\
  (* a whole peer / keypair *)
  (forall sh p P E n h, peer_rep sh p P * entry_at sh (hs_addr p) E n h |-- data_at_ sh t_peer p) /\
  (forall CSw k K E n h, keypair_rep CSw k K * entry_at Ews k E n h |--
     @malloc_token CSw Ews (tarray tuchar SIZEOF_KEYPAIR) k * data_at_ Ews (tarray tuchar SIZEOF_KEYPAIR) k).
Proof.
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - intros sh m M. unfold init_rep. Intros.
    assert_PROP (field_compatible t_init [] m) by entailer!.
    rewrite prot_rep3_init_eq by auto. apply derives_refl.
  - intros sh m M FC OK. unfold init_rep. rewrite prot_rep3_init_eq by auto. entailer!.
  - intros sh m M. unfold resp_rep. Intros.
    assert_PROP (field_compatible t_resp [] m) by entailer!.
    rewrite prot_rep3_resp_eq by auto. apply derives_refl.
  - intros sh m M FC OK. unfold resp_rep. rewrite prot_rep3_resp_eq by auto. entailer!.
  - exact prot_rep3_pool_add.
  - exact prot_rep3_pool_free.
  - intros. apply prot_rep3_peer_whole.
  - intros. rewrite (prot_rep3_data_at__cs CSw Noise.CS). apply prot_rep3_kp_whole.
Qed.
