(* body proof of poly1305_update, against aead_spec3.aead_G3.
   The code is the series patch P22: size_t nbytes, and the loop over chunks of at most UINT_MAX bytes. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.chacha.code WgNoise.chacha_block.code WgNoise.poly1305.code WgNoise.poly1305_donna32.code
        WgNoise.chacha20poly1305.code WgNoise.shim.code.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.common.wg3_iface.
Require Import WgNoise.proof.aead.aead_spec3.
Require Import WgNoise.proof.aead.aead_cce.
Require Import WgNoise.proof.aead.aead_bytes.
Require Import WgNoise.proof.aead.aead_poly_small_ctx.
Require Import WgNoise.proof.aead.aead_poly_update3_model.

Local Open Scope Z_scope.

(* byte arrays cut at offsets (as chc_split2/3 of aead_chacha_body.v) *)
Lemma pu3_split3 {cs: compspecs} sh n i j (v: list val) p :
  0 <= i -> 0 <= j -> i + j <= n -> Zlength v = n -> field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) v p =
  (data_at sh (tarray tuchar i) (sublist 0 i v) p *
   data_at sh (tarray tuchar j) (sublist i (i + j) v) (offset_val i p) *
   data_at sh (tarray tuchar (n - (i + j))) (sublist (i + j) n v) (offset_val (i + j) p))%logic.
Proof.
  intros. unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh n i (i + j)) by lia.
  fold (tarray tuchar n). rewrite !arr_field_address0 by (auto; lia).
  change (sizeof tuchar) with 1. rewrite !Z.mul_1_l. replace (i + j - i) with j by lia. reflexivity.
Qed.

Lemma pu3_split2 {cs: compspecs} sh n i (v: list val) p :
  0 <= i <= n -> Zlength v = n -> field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) v p =
  (data_at sh (tarray tuchar i) (sublist 0 i v) p *
   data_at sh (tarray tuchar (n - i)) (sublist i n v) (offset_val i p))%logic.
Proof.
  intros. unfold tarray. rewrite (split2_data_at_Tarray_tuchar sh n i) by lia.
  fold (tarray tuchar n). rewrite arr_field_address0 by (auto; lia).
  change (sizeof tuchar) with 1. rewrite Z.mul_1_l. reflexivity.
Qed.

Lemma pu3_join2 {cs: compspecs} sh n i (a b: list val) p :
  0 <= i <= n -> Zlength a = i -> Zlength b = n - i -> field_compatible (tarray tuchar n) [] p ->
  (data_at sh (tarray tuchar i) a p * data_at sh (tarray tuchar (n - i)) b (offset_val i p))%logic =
  data_at sh (tarray tuchar n) (a ++ b) p.
Proof.
  intros. rewrite (pu3_split2 sh n i (a ++ b) p) by (auto; list_solve).
  f_equal; f_equal; list_solve.
Qed.

Lemma pu3_r_ok (key: list byte) : p1305_r_ok (p1305_r key).
Proof.
  unfold p1305_r_ok, p1305_r. split.
  - rewrite <- Z.land_assoc, Z.land_diag. reflexivity.
  - apply Z.land_nonneg. right. lia.
Qed.

Lemma pu3_modu (n: Z) :
  0 <= n <= Int.max_unsigned -> Int.modu (Int.repr n) (Int.repr 16) = Int.repr (n mod 16).
Proof. intros. unfold Int.modu. rewrite !Int.unsigned_repr by rep_lia. reflexivity. Qed.

(* bulk_len = round_down(min(nbytes, UINT_MAX), POLY1305_BLOCK_SIZE) in size_t *)
Lemma pu4_round_down64 (x: Z) :
  0 <= x <= Int64.max_unsigned ->
  Int64.and (Int64.repr x) (Int64.repr (-16)) = Int64.repr (x / 16 * 16).
Proof.
  intros Hn. apply Int64.same_bits_eq. intros i Hi.
  rewrite Int64.bits_and by lia. rewrite !Int64.testbit_repr by lia.
  replace (x / 16 * 16) with (Z.shiftl (Z.shiftr x 4) 4)
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; reflexivity).
  destruct (Z_lt_le_dec i 4).
  - rewrite Z.shiftl_spec_low by lia.
    assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) as [-> | [-> | [-> | ->]]] by lia;
      simpl; apply andb_false_r.
  - rewrite Z.shiftl_spec_high, Z.shiftr_spec by lia.
    change (-16) with (Z.lnot 15). rewrite Z.lnot_spec by lia.
    rewrite (Z.bits_above_log2 15 i) by (try lia; change (Z.log2 15) with 3; lia).
    rewrite andb_true_r. f_equal. lia.
Qed.

(* bulk_len = round_down(min(nbytes, UINT_MAX), 16) for nbytes >= 16 *)
Lemma pu4_bulk_range (m: Z) :
  16 <= m -> 16 <= Z.min m 4294967295 / 16 * 16 <= m /\ Z.min m 4294967295 / 16 * 16 <= 4294967280 /\
  (Z.min m 4294967295 / 16 * 16) mod 16 = 0.
Proof.
  intros Hm. set (x := Z.min m 4294967295).
  assert (Hx: 16 <= x <= 4294967295) by (subst x; lia).
  pose proof (Z.mul_div_le x 16 ltac:(lia)).
  assert (16 <= x / 16 * 16).
  { assert (1 <= x / 16) by (apply Z.div_le_lower_bound; lia). lia. }
  assert (x / 16 < 268435456) by (apply Z.div_lt_upper_bound; lia).
  split; [subst x; lia |]. split; [lia | apply Z_mod_mult].
Qed.

Lemma pu4_add_ptr_uint {cs: compspecs} p k l :
  isptr p -> 0 <= l <= Int.max_unsigned ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tuint (offset_val k p) (Vint (Int.repr l))) =
  offset_val (k + l) p.
Proof.
  intros Hp Hl. destruct p; try contradiction. simpl.
  f_equal. rewrite Ptrofs.add_assoc. f_equal. unfold Ptrofs.of_intu, Ptrofs.of_int.
  rewrite Int.unsigned_repr by auto. rewrite Ptrofs.mul_commut, Ptrofs.mul_one. rewrite Ptrofs.add_unsigned.
  apply Ptrofs.eqm_samerepr. apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym; apply Ptrofs.eqm_unsigned_repr.
Qed.

Section PolyUpdate3.
#[local] Existing Instance Poly1305.CS.

(* folding the streaming state back from the fields of the context *)
Lemma pu3_fold sh key m h junk desc :
  Zlength key = 32 -> p1305_limbs_ok h ->
  p1305_limbs_val h mod p1305_p = p1305_acc (p1305_r key) 0 (sublist 0 (Zlength m / 16 * 16) m) ->
  Zlength junk = 16 - Zlength (sublist (Zlength m / 16 * 16) (Zlength m) m) ->
  (field_at sh t_p1305_ctx (DOT poly1305.code._buf)
     (map Vubyte (sublist (Zlength m / 16 * 16) (Zlength m) m) ++ junk) desc *
   field_at sh t_p1305_ctx (DOT poly1305.code._buflen)
     (Vint (Int.repr (Zlength (sublist (Zlength m / 16 * 16) (Zlength m) m)))) desc *
   field_at sh t_p1305_ctx (DOT poly1305.code._s) (map Vint (p1305_s_words key)) desc *
   spacer sh 36 40 desc *
   field_at sh t_p1305_ctx (DOT poly1305.code._state) (p1305_bstate_val h (p1305_r key)) desc)%logic
  |-- p1305_state sh key m desc.
Proof.
  intros. unfold p1305_state. Exists h junk. rewrite aead_ps_ctx_split.
  apply andp_right; [apply prop_right; auto | apply derives_refl].
Qed.

(* the same with an empty rest (a whole number of blocks) *)
Lemma pu3_fold0 sh key m h (junk: list val) desc :
  Zlength key = 32 -> p1305_limbs_ok h -> Zlength m mod 16 = 0 ->
  p1305_limbs_val h mod p1305_p = p1305_acc (p1305_r key) 0 m ->
  Zlength junk = 16 ->
  (@field_at Poly1305.CS sh t_p1305_ctx (DOT poly1305.code._buf) junk desc *
   field_at sh t_p1305_ctx (DOT poly1305.code._buflen) (Vint (Int.repr 0)) desc *
   field_at sh t_p1305_ctx (DOT poly1305.code._s) (map Vint (p1305_s_words key)) desc *
   spacer sh 36 40 desc *
   field_at sh t_p1305_ctx (DOT poly1305.code._state) (p1305_bstate_val h (p1305_r key)) desc)%logic
  |-- p1305_state sh key m desc.
Proof.
  intros HK Hh Hm Hacc Hj.
  pose proof (pu3_whole m Hm) as (Hw1 & Hw2 & Hw3).
  eapply derives_trans; [| apply (pu3_fold sh key m h junk desc)];
    rewrite ?Hw3, ?Hw2; auto.
  apply derives_refl.
Qed.

(* the body of the series' poly1305_update (patch P22: size_t nbytes, the test
   `nbytes >= POLY1305_BLOCK_SIZE - desc->buflen`, and the loop
   `while (nbytes >= 16) { bulk_len = round_down(min(nbytes, UINT_MAX), 16); poly1305_blocks(.., bulk_len, 1); .. }`)
   against poly1305_update_spec3 (= aead_spec.poly1305_update_spec: size_t, ANY length).  an earlier proof of the
   one-call body, with nbytes a tulong; the bulk call became a forward_while whose invariant is the state after the
   buffer completion (k1 bytes of data absorbed, buflen 0, a whole number of blocks), each iteration absorbing
   bulk_len = round_down(min(nbytes, 2^32 - 1), 16) bytes (pu4_bulk_range, pu4_round_down64, pu3_bulk). *)
Theorem aead_poly_update_bodies3 :
  @semax_body (QPvarspecs Poly1305.qp) (aead_imports3 Poly1305.CS ++ aead_G3) Poly1305.CS
    WgNoise.poly1305.code.f_poly1305_update poly1305_update_spec3.
Proof.
  start_function.
  unfold p1305_state. Intros h junk.
  rewrite aead_ps_ctx_split.
  flatten_sepcon_in_SEP. flatten_sepcon_in_SEP. flatten_sepcon_in_SEP. flatten_sepcon_in_SEP.
  pose proof (Zlength_nonneg msg) as Hm0.
  pose proof (Zlength_nonneg data) as Hd0.
  pose proof (Z.mod_pos_bound (Zlength msg) 16 ltac:(lia)) as Hb16.
  assert (Hn: 0 <= Zlength msg / 16 * 16 <= Zlength msg).
  { pose proof (Z.mul_div_le (Zlength msg) 16 ltac:(lia)). pose proof (Z.div_pos (Zlength msg) 16 Hm0 ltac:(lia)). lia. }
  assert (Hb: Zlength (sublist (Zlength msg / 16 * 16) (Zlength msg) msg) = Zlength msg mod 16).
  { rewrite Zlength_sublist by lia. rewrite (Z.mod_eq (Zlength msg) 16) by lia. lia. }
  set (rest := sublist (Zlength msg / 16 * 16) (Zlength msg) msg) in *.
  assert_PROP (0 < Zlength data -> isptr src) as Psrc.
  { unfold prim_bytes. if_tac; entailer!. }
  assert_PROP (field_compatible t_p1305_ctx (DOT poly1305.code._buf) desc) as FCb by entailer!.
  forward.
  forward_if (EX k: Z, EX src': val,
     PROP (0 <= k <= Zlength data;
           Zlength (msg ++ sublist 0 k data) mod 16 + (Zlength data - k) < 16;
           0 < Zlength data - k -> src' = offset_val k src)
     LOCAL (temp poly1305.code._desc desc; temp poly1305.code._src src';
            temp poly1305.code._nbytes (Vlong (Int64.repr (Zlength data - k))))
     SEP (p1305_state sh key (msg ++ sublist 0 k data) desc; prim_bytes dsh data src)).
  2: {
    match goal with H: Zlength data < Int.unsigned (Int.sub (Int.repr 16) (Int.repr (Zlength rest))) |- _ =>
      rewrite sub_repr, Int.unsigned_repr in H by rep_lia end.
    forward. Exists 0 src.
    rewrite sublist_nil, app_nil_r, Z.sub_0_r.
    sep_apply (pu3_fold sh key msg h junk desc); auto.
    entailer!. }
  { (* nbytes >= 16 - buflen *)
  match goal with H: Zlength data >= Int.unsigned (Int.sub (Int.repr 16) (Int.repr (Zlength rest))) |- _ =>
    rewrite sub_repr, Int.unsigned_repr in H by rep_lia end.
  forward.
  forward_if (EX k1: Z, EX src1: val, EX h1: list Z, EX junk1: list val,
     PROP (0 <= k1 <= Zlength data; Zlength (msg ++ sublist 0 k1 data) mod 16 = 0;
           p1305_limbs_ok h1;
           p1305_limbs_val h1 mod p1305_p = p1305_acc (p1305_r key) 0 (msg ++ sublist 0 k1 data);
           Zlength junk1 = 16; 0 < Zlength data - k1 -> src1 = offset_val k1 src)
     LOCAL (temp poly1305.code._desc desc; temp poly1305.code._src src1;
            temp poly1305.code._nbytes (Vlong (Int64.repr (Zlength data - k1))))
     SEP (@field_at Poly1305.CS sh t_p1305_ctx (DOT poly1305.code._buf) junk1 desc;
          @field_at Poly1305.CS sh t_p1305_ctx (DOT poly1305.code._buflen) (Vint (Int.repr 0)) desc;
          @field_at Poly1305.CS sh t_p1305_ctx (DOT poly1305.code._s) (map Vint (p1305_s_words key)) desc;
          spacer sh 36 40 desc;
          @field_at Poly1305.CS sh t_p1305_ctx (DOT poly1305.code._state) (p1305_bstate_val h1 (p1305_r key)) desc;
          prim_bytes dsh data src)).
  { (* buflen <> 0: complete the buffer *)
    forward. forward. forward.
    rewrite sub_repr.
    rewrite (field_at_data_at sh t_p1305_ctx (DOT poly1305.code._buf)).
    rewrite field_compatible_field_address by auto.
    simpl nested_field_type. simpl nested_field_offset. rewrite isptr_offset_val_zero by auto.
    assert_PROP (field_compatible (tarray tuchar 16) [] desc) as FCa by entailer!.
    rewrite (pu3_split2 sh 16 (Zlength rest) (map Vubyte rest ++ junk) desc) by (auto; try list_solve; lia).
    replace (sublist 0 (Zlength rest) (map Vubyte rest ++ junk)) with (map Vubyte rest) by list_solve.
    replace (sublist (Zlength rest) 16 (map Vubyte rest ++ junk)) with junk by list_solve.
    sep_apply (data_at_data_at_ sh (tarray tuchar (16 - Zlength rest)) junk (offset_val (Zlength rest) desc)).
    unfold prim_bytes. rewrite if_false by lia.
    assert_PROP (field_compatible (tarray tuchar (Zlength data)) [] src) as FCs by entailer!.
    rewrite (pu3_split2 dsh (Zlength data) (16 - Zlength rest) (map Vubyte data) src) by (auto; try list_solve; lia).
    rewrite !sublist_map.
    Intros.
    forward_call (sh, dsh, offset_val (Zlength rest) desc, src, 16 - Zlength rest,
                  sublist 0 (16 - Zlength rest) data).
    { list_solve. }
    assert (FC: field_compatible t_p1305_ctx [] desc) by (destruct FCb as (?&?&?&?&?); repeat split; auto).
    pose proof (pu3_join2 sh 16 (Zlength rest) (map Vubyte rest) (map Vubyte (sublist 0 (16 - Zlength rest) data))
                 desc ltac:(lia) ltac:(list_solve) ltac:(list_solve) FCa) as Ej.
    sep_apply Ej. clear Ej.
    rewrite <- map_app.
    set (bs := rest ++ sublist 0 (16 - Zlength rest) data).
    assert (Hbs: Zlength bs = 16) by (subst bs; list_solve).
    replace (data_at sh (tarray tuchar 16) (map Vubyte bs) desc) with (prim_bytes sh bs desc)
      by (unfold prim_bytes; rewrite Hbs; reflexivity).
    forward. forward.
    rewrite (field_at_data_at sh t_p1305_ctx (DOT poly1305.code._state)).
    rewrite field_compatible_field_address by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset.
    forward_call (sh, offset_val 40 desc, h, p1305_r key, sh, desc, bs, 1).
    { rewrite Hbs; entailer!. simpl. rewrite isptr_offset_val_zero; auto. }
    { split; [apply pu3_r_ok | rewrite Hbs; reflexivity]. }
    Intros h1.
    forward.
    destruct (pu3_fill (p1305_r key) msg data (p1305_limbs_val h) (p1305_limbs_val h1)) as [Hf1 Hf2];
      [lia | lia | exact H2 | rewrite <- Hb; exact H7 |].
    Exists (16 - Zlength rest) (offset_val (16 - Zlength rest) src) h1 (map Vubyte bs).
    rewrite Hb in *.
    unfold prim_bytes. rewrite !if_false by lia. rewrite Hbs.
    rewrite (pu3_split2 dsh (Zlength data) (16 - Zlength msg mod 16) (map Vubyte data) src) by (auto; try list_solve; lia).
    rewrite !sublist_map.
    rewrite (field_at_data_at sh t_p1305_ctx (DOT poly1305.code._buf)).
    rewrite (field_at_data_at sh t_p1305_ctx (DOT poly1305.code._state)).
    rewrite !field_compatible_field_address by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset. rewrite isptr_offset_val_zero by auto.
    entailer!. }
  { (* buflen = 0 *)
    forward.
    assert (Hr00: Zlength rest = 0).
    { apply (f_equal Int.unsigned) in H5. rewrite Int.unsigned_repr in H5 by rep_lia. exact H5. }
    assert (Hr0: rest = []) by (apply Zlength_nil_inv; lia).
    pose proof (pu3_whole msg ltac:(lia)) as (Hw1 & Hw2 & Hw3).
    Exists 0 src h junk.
    rewrite sublist_nil, app_nil_r, Z.sub_0_r.
    rewrite Hr0 in *. simpl map. simpl app.
    entailer!. }
  (* the whole blocks of the rest of the chunk: the series' loop, at most round_down(min(nbytes, UINT_MAX), 16)
     bytes per poly1305_blocks call *)
  assert (FC: field_compatible t_p1305_ctx [] desc) by (destruct FCb as (?&?&?&?&?); repeat split; auto).
  forward_while (EX k1: Z, EX src1: val, EX h1: list Z, EX junk1: list val,
     PROP (0 <= k1 <= Zlength data; Zlength (msg ++ sublist 0 k1 data) mod 16 = 0;
           p1305_limbs_ok h1;
           p1305_limbs_val h1 mod p1305_p = p1305_acc (p1305_r key) 0 (msg ++ sublist 0 k1 data);
           Zlength junk1 = 16; 0 < Zlength data - k1 -> src1 = offset_val k1 src)
     LOCAL (temp poly1305.code._desc desc; temp poly1305.code._src src1;
            temp poly1305.code._nbytes (Vlong (Int64.repr (Zlength data - k1))))
     SEP (@field_at Poly1305.CS sh t_p1305_ctx (DOT poly1305.code._buf) junk1 desc;
          @field_at Poly1305.CS sh t_p1305_ctx (DOT poly1305.code._buflen) (Vint (Int.repr 0)) desc;
          @field_at Poly1305.CS sh t_p1305_ctx (DOT poly1305.code._s) (map Vint (p1305_s_words key)) desc;
          spacer sh 36 40 desc;
          @field_at Poly1305.CS sh t_p1305_ctx (DOT poly1305.code._state) (p1305_bstate_val h1 (p1305_r key)) desc;
          prim_bytes dsh data src)).
  { Intros k1 src1 h1 junk1. Exists k1 src1 h1 junk1. entailer!. }
  { entailer!. }
  { (* nbytes >= 16: one call of poly1305_blocks with bulk_len = round_down(min(nbytes, UINT_MAX), 16) bytes *)
    rename HRE into Hge.
    set (m := Zlength data - k1) in *.
    forward_if (temp poly1305.code._t'1 (Vlong (Int64.repr (Z.min m 4294967295)))).
    { forward. entailer!.
      change (Int.unsigned (Int.not (Int.repr 0))) with 4294967295 in *.
      try (match goal with H: Int64.ltu _ _ = _ |- _ =>
             unfold Int64.ltu in H; rewrite !Int64.unsigned_repr in H by rep_lia end;
           repeat match goal with H: context [zlt ?a ?b] |- _ => destruct (zlt a b); try discriminate end).
      f_equal. f_equal. lia. }
    { forward. entailer!.
      change (Int.unsigned (Int.not (Int.repr 0))) with 4294967295 in *.
      try (match goal with H: Int64.ltu _ _ = _ |- _ =>
             unfold Int64.ltu in H; rewrite !Int64.unsigned_repr in H by rep_lia end;
           repeat match goal with H: context [zlt ?a ?b] |- _ => destruct (zlt a b); try discriminate end).
      f_equal. f_equal. lia. }
    forward.
    pose proof (pu4_bulk_range m ltac:(lia)) as (Hb1 & Hb2 & Hb3).
    assert (Ebl: Int64.unsigned (Int64.and (Int64.repr (Z.min m 4294967295))
                   (Int64.repr (Int.signed (Int.not (Int.sub (Int.repr 16) (Int.repr 1)))))) =
                 Z.min m 4294967295 / 16 * 16).
    { change (Int.signed (Int.not (Int.sub (Int.repr 16) (Int.repr 1)))) with (-16).
      rewrite pu4_round_down64 by rep_lia. rewrite Int64.unsigned_repr by rep_lia. reflexivity. }
    rewrite Ebl. clear Ebl.
    set (b := Z.min m 4294967295 / 16 * 16) in *.
    match goal with H: 0 < m -> src1 = offset_val k1 src |- _ => rewrite H by lia end.
    unfold prim_bytes at 1. rewrite if_false by lia.
    assert_PROP (field_compatible (tarray tuchar (Zlength data)) [] src) as FCs by entailer!.
    rewrite (pu3_split3 dsh (Zlength data) k1 b (map Vubyte data) src) by (auto; try list_solve; lia).
    rewrite !sublist_map.
    set (bs := sublist k1 (k1 + b) data).
    assert (Hbs: Zlength bs = b) by (subst bs; list_solve).
    replace (data_at dsh (tarray tuchar b) (map Vubyte bs) (offset_val k1 src))
      with (prim_bytes dsh bs (offset_val k1 src)) by (unfold prim_bytes; rewrite if_false, Hbs by lia; reflexivity).
    Intros.
    rewrite (field_at_data_at sh t_p1305_ctx (DOT poly1305.code._state)).
    rewrite field_compatible_field_address by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset.
    forward_call (sh, offset_val 40 desc, h1, p1305_r key, dsh, offset_val k1 src, bs, 1).
    { rewrite Hbs; entailer!. }
    { pose proof (pu3_r_ok key) as Hr. unfold p1305_r_ok in *. rewrite ?Hbs.
      repeat split; first [exact Hb3 | tauto]. }
    Intros h2.
    forward. forward.
    assert (HM: msg ++ sublist 0 (k1 + b) data = (msg ++ sublist 0 k1 data) ++ bs)
      by (subst bs; rewrite <- app_assoc; f_equal; list_solve).
    assert (HMb: Zlength ((msg ++ sublist 0 k1 data) ++ bs) mod 16 = 0).
    { rewrite Zlength_app, Hbs, Z.add_mod, H6, Hb3 by lia. reflexivity. }
    match goal with H: p1305_limbs_val h2 mod p1305_p = _ |- _ =>
      pose proof (pu3_bulk (p1305_r key) (msg ++ sublist 0 k1 data) bs (p1305_limbs_val h1) (p1305_limbs_val h2)
                    H6 ltac:(rewrite Hbs; exact Hb3) H8 H) as Hacc end.
    assert (Psrc': isptr src) by (apply Psrc; lia).
    assert (Hb32: 0 <= b <= Int.max_unsigned) by rep_lia.
    Exists (k1 + b, offset_val (k1 + b) src, h2, junk1).
    cbv [fst snd].
    rewrite HM.
    assert (Est: field_at sh t_p1305_ctx (DOT poly1305.code._state) (p1305_bstate_val h2 (p1305_r key)) desc =
                 data_at sh t_p1305_block_state (p1305_bstate_val h2 (p1305_r key)) (offset_val 40 desc)).
    { rewrite field_at_data_at, field_compatible_field_address by auto with field_compatible. reflexivity. }
    rewrite <- Est. clear Est.
    unfold prim_bytes. rewrite !if_false by lia. rewrite Hbs.
    rewrite (pu3_split3 dsh (Zlength data) k1 b (map Vubyte data) src) by (auto; try list_solve; lia).
    rewrite !sublist_map.
    rewrite Int.unsigned_repr by rep_lia. rewrite sub64_repr.
    rewrite (pu4_add_ptr_uint src k1 b Psrc' Hb32).
    replace (m - b) with (Zlength data - (k1 + b)) by (subst m; lia).
    entailer!. }
  (* nbytes < 16: the whole blocks are done *)
  forward.
  Exists k1 src1.
  sep_apply (pu3_fold0 sh key (msg ++ sublist 0 k1 data) h1 junk1 desc); auto.
  entailer!.
  }
  (* the tail: buffer the remaining 0..15 bytes *)
  clear dependent h. clear dependent junk. clear Hb Hn Hb16.
  Intros k src'.
  unfold p1305_state. Intros h3 junk3.
  rewrite aead_ps_ctx_split.
  flatten_sepcon_in_SEP. flatten_sepcon_in_SEP. flatten_sepcon_in_SEP. flatten_sepcon_in_SEP.
  set (msg' := msg ++ sublist 0 k data) in *.
  pose proof (Zlength_nonneg msg') as Hm0'.
  pose proof (Z.mod_pos_bound (Zlength msg') 16 ltac:(lia)) as Hb16.
  assert (Hn: 0 <= Zlength msg' / 16 * 16 <= Zlength msg').
  { pose proof (Z.mul_div_le (Zlength msg') 16 ltac:(lia)). pose proof (Z.div_pos (Zlength msg') 16 Hm0' ltac:(lia)). lia. }
  assert (Hb: Zlength (sublist (Zlength msg' / 16 * 16) (Zlength msg') msg') = Zlength msg' mod 16).
  { rewrite Zlength_sublist by lia. rewrite (Z.mod_eq (Zlength msg') 16) by lia. lia. }
  set (rest3 := sublist (Zlength msg' / 16 * 16) (Zlength msg') msg') in *.
  assert (Hmsg: msg ++ data = msg' ++ sublist k (Zlength data) data).
  { subst msg'. rewrite <- app_assoc. f_equal. list_solve. }
  pose proof (pu3_tail msg' (sublist k (Zlength data) data) ltac:(rewrite Zlength_sublist by lia; lia))
    as (Ht1 & Ht2 & Ht3).
  forward_if.
  { (* nbytes <> 0: append to the buffer *)
    match goal with H: 0 < Zlength data - k -> src' = offset_val k src |- _ => rewrite H by lia end.
    forward.
    rewrite (field_at_data_at sh t_p1305_ctx (DOT poly1305.code._buf)).
    rewrite field_compatible_field_address by auto.
    simpl nested_field_type. simpl nested_field_offset. rewrite isptr_offset_val_zero by auto.
    assert_PROP (field_compatible (tarray tuchar 16) [] desc) as FCa by entailer!.
    rewrite (pu3_split3 sh 16 (Zlength rest3) (Zlength data - k) (map Vubyte rest3 ++ junk3) desc)
      by (auto; try list_solve; lia).
    replace (sublist 0 (Zlength rest3) (map Vubyte rest3 ++ junk3)) with (map Vubyte rest3) by list_solve.
    sep_apply (data_at_data_at_ sh (tarray tuchar (Zlength data - k))
                 (sublist (Zlength rest3) (Zlength rest3 + (Zlength data - k)) (map Vubyte rest3 ++ junk3))
                 (offset_val (Zlength rest3) desc)).
    unfold prim_bytes. rewrite if_false by lia.
    assert_PROP (field_compatible (tarray tuchar (Zlength data)) [] src) as FCs by entailer!.
    rewrite (pu3_split2 dsh (Zlength data) k (map Vubyte data) src) by (auto; try list_solve; lia).
    rewrite !sublist_map.
    Intros.
    forward_call (sh, dsh, offset_val (Zlength rest3) desc, offset_val k src, Zlength data - k,
                  sublist k (Zlength data) data).
    { list_solve. }
    forward. forward.
    assert (Ebl: Int64.Z_mod_modulus (Int64.Z_mod_modulus (Int.unsigned (Int.repr (Zlength rest3))) +
                   Int64.Z_mod_modulus (Zlength data - k)) = Zlength rest3 + (Zlength data - k)).
    { assert (B1: 0 <= Zlength rest3 < 16) by (rewrite Hb; lia).
      assert (B2: 0 <= Zlength data - k /\ Zlength rest3 + (Zlength data - k) < 16) by (rewrite Hb; lia).
      rewrite Int.unsigned_repr by rep_lia. rewrite !Int64.Z_mod_modulus_eq.
      rewrite (Z.mod_small (Zlength rest3)) by rep_lia.
      rewrite (Z.mod_small (Zlength data - k)) by rep_lia.
      apply Z.mod_small. rep_lia. }
    rewrite Ebl. clear Ebl.
    rewrite Hmsg.
    change (sublist (Zlength msg' / 16 * 16) (Zlength msg') msg') with rest3 in Ht3.
    assert (Hx: Zlength (sublist k (Zlength data) data) = Zlength data - k) by list_solve.
    set (x := sublist k (Zlength data) data) in *.
    set (J := sublist (Zlength rest3 + (Zlength data - k)) 16 (map Vubyte rest3 ++ junk3)).
    assert (HJ: Zlength J = 16 - (Zlength rest3 + (Zlength data - k))) by (subst J; list_solve).
    unfold p1305_state. Exists h3 J.
    rewrite Ht2, Ht3.
    rewrite aead_ps_ctx_split.
    rewrite (field_at_data_at sh t_p1305_ctx (DOT poly1305.code._buf)).
    rewrite field_compatible_field_address by auto.
    simpl nested_field_type. simpl nested_field_offset. rewrite isptr_offset_val_zero by auto.
    rewrite (pu3_split3 sh 16 (Zlength rest3) (Zlength data - k) (map Vubyte (rest3 ++ x) ++ J) desc)
      by (auto; try list_solve; lia).
    replace (sublist 0 (Zlength rest3) (map Vubyte (rest3 ++ x) ++ J)) with (map Vubyte rest3) by list_solve.
    replace (sublist (Zlength rest3) (Zlength rest3 + (Zlength data - k)) (map Vubyte (rest3 ++ x) ++ J))
      with (map Vubyte x) by list_solve.
    replace (sublist (Zlength rest3 + (Zlength data - k)) 16 (map Vubyte (rest3 ++ x) ++ J)) with J by list_solve.
    replace (Zlength (rest3 ++ x)) with (Zlength rest3 + (Zlength data - k)) by list_solve.
    unfold prim_bytes. rewrite if_false by lia.
    rewrite (pu3_split2 dsh (Zlength data) k (map Vubyte data) src) by (auto; try list_solve; lia).
    rewrite !sublist_map.
    entailer!. }
  { (* nbytes = 0 *)
    forward.
    assert (Hk0: Zlength data - k = 0) by (apply repr_inj_unsigned64; [rep_lia | rep_lia | assumption]).
    assert (Hk: k = Zlength data) by lia.
    replace (msg ++ data) with msg' by (subst msg'; rewrite Hk, sublist_same by lia; reflexivity).
    sep_apply (pu3_fold sh key msg' h3 junk3 desc); auto.
    entailer!. }
Qed.

End PolyUpdate3.
