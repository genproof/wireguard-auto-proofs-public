(* The bodies of poly1305_update and poly1305_final (poly1305.c) with a context of their callees only, against
   the specifications of aead_spec3.v (the same as aead_poly_update_body3.v / aead_poly_final_body3.v, whose
   context is the whole AEAD piece).  A program that links poly1305.c without the ChaCha20 and AEAD units (law
   ae_split_poly1305) can take these bodies: every function of their contexts is in it. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.poly1305.code WgNoise.poly1305_donna32.code.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.common.wg3_iface.
Require Import WgNoise.proof.aead.aead_spec3.
Require Import WgNoise.proof.aead.aead_cce.
Require Import WgNoise.proof.aead.aead_bytes.
Require Import WgNoise.proof.aead.aead_poly_small_ctx.
Require Import WgNoise.proof.aead.aead_poly_small_body.
Require Import WgNoise.proof.aead.aead_poly_update3_model.
Require Import WgNoise.proof.aead.aead_poly_final3_model.
Require Import WgNoise.proof.aead.aead_poly_final3_ctx.
Require Import WgNoise.proof.aead.aead_poly_update_body3.
Require Import WgNoise.proof.aead.aead_poly_final_body3.

Local Open Scope Z_scope.

#[local] Existing Instance Poly1305.CS.

Lemma body_poly1305_update_callee :
  @semax_body (QPvarspecs Poly1305.qp) [@memcpy_spec Poly1305.CS; poly1305_blocks_generic_spec] Poly1305.CS
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

Lemma body_poly1305_final_callee :
  @semax_body (QPvarspecs Poly1305.qp)
    [@memset_spec Poly1305.CS; poly1305_blocks_generic_spec; poly1305_emit_generic_spec] Poly1305.CS
    WgNoise.poly1305.code.f_poly1305_final poly1305_final_spec.
Proof.
  start_function.
  unfold p1305_state. Intros h junk.
  set (n := Zlength msg / 16 * 16) in *.
  set (rest := sublist n (Zlength msg) msg) in *.
  assert_PROP (field_compatible t_p1305_ctx [] desc) as FC by entailer!.
  rewrite aead_ps_ctx_split. Intros.
  assert (Hrest: Zlength rest = Zlength msg - n /\ 0 <= Zlength msg - n < 16).
  { pose proof (Zlength_nonneg msg). pose proof (Z.mod_pos_bound (Zlength msg) 16 ltac:(lia)).
    pose proof (Z_div_mod_eq_full (Zlength msg) 16).
    assert (0 <= n <= Zlength msg) by (subst n; lia).
    subst rest. rewrite Zlength_sublist by lia. lia. }
  forward.
  forward_if (EX h': list Z, EX bufv: list val, EX blv: val,
    PROP (p1305_limbs_ok h'; p1305_limbs_val h' mod p1305_p = p1305_acc (p1305_r key) 0 msg)
    LOCAL (temp poly1305.code._desc desc; temp poly1305.code._dst dst)
    SEP (field_at sh t_p1305_ctx (DOT poly1305.code._buf) bufv desc;
         field_at sh t_p1305_ctx (DOT poly1305.code._buflen) blv desc;
         field_at sh t_p1305_ctx (DOT poly1305.code._s) (map Vint (p1305_s_words key)) desc;
         spacer sh 36 40 desc;
         field_at sh t_p1305_ctx (DOT poly1305.code._state) (p1305_bstate_val h' (p1305_r key)) desc;
         data_at_ osh (tarray tuchar 16) dst))%assert.
  - forward. forward. forward.
    destruct Hrest as [Hk Hk'].
    assert (Hb: upd_Znth (Zlength rest) (map Vubyte rest ++ junk) (Vint (Int.zero_ext 8 (Int.repr 1))) =
                map Vubyte (rest ++ [Byte.one]) ++ sublist 1 (Zlength junk) junk).
    { rewrite upd_Znth_app2 by (rewrite Zlength_map; lia). rewrite Zlength_map, Z.sub_diag.
      rewrite map_app. rewrite <- app_assoc. f_equal.
      destruct junk as [| j junk']; [rewrite Zlength_nil in H2; lia |].
      rewrite upd_Znth0, Zlength_cons. simpl. rewrite sublist_1_cons. f_equal. rewrite sublist_same by lia. reflexivity. }
    rewrite Hb, add_repr.
    forward. forward.
    rewrite field_at_data_at, field_compatible_field_address by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset. rewrite isptr_offset_val_zero by auto with field_compatible.
    assert (Hl: Zlength (map Vubyte (rest ++ [Byte.one]) ++ sublist 1 (Zlength junk) junk) = 16).
    { rewrite Zlength_app, Zlength_map, Zlength_app, Zlength_sublist by lia. rewrite Zlength_cons, Zlength_nil. lia. }
    rewrite (split2_data_at_Tarray_tuchar sh 16 (Zlength rest + 1)) by lia.
    assert (F1: field_compatible (tarray tuchar 16) [] desc).
    { pose proof (field_compatible_nested_field t_p1305_ctx (DOT poly1305.code._buf) desc
                ltac:(auto with field_compatible)) as X.
      simpl in X. rewrite isptr_offset_val_zero in X by auto with field_compatible. exact X. }
    rewrite field_address0_offset by auto with field_compatible.
    assert (Hs1: sublist 0 (Zlength rest + 1) (map Vubyte (rest ++ [Byte.one]) ++ sublist 1 (Zlength junk) junk) =
                 map Vubyte (rest ++ [Byte.one])) by list_solve.
    assert (Hs2: sublist (Zlength rest + 1) 16 (map Vubyte (rest ++ [Byte.one]) ++ sublist 1 (Zlength junk) junk) =
                 sublist 1 (Zlength junk) junk) by list_solve.
    rewrite Hs1, Hs2.
    simpl nested_field_offset. replace (0 + 1 * (Zlength rest + 1)) with (Zlength rest + 1) by lia.
    Intros.
    forward_call (sh, offset_val (Zlength rest + 1) desc, 0, 16 - (Zlength rest + 1)).
    set (bs := rest ++ [Byte.one] ++ Zrepeat Byte.zero (15 - Zlength rest)).
    assert (Hbs: Zlength bs = 16) by (subst bs; list_solve).
    gather_SEP 0 1.
    replace_SEP 0 (prim_bytes sh bs desc).
    { unfold prim_bytes. rewrite Hbs. rewrite if_false by lia.
      rewrite (split2_data_at_Tarray_tuchar sh 16 (Zlength rest + 1)) by (rewrite ?Zlength_map; lia).
      rewrite field_address0_offset by auto with field_compatible.
      simpl nested_field_offset. replace (0 + 1 * (Zlength rest + 1)) with (Zlength rest + 1) by lia.
      replace (sublist 0 (Zlength rest + 1) (map Vubyte bs)) with (map Vubyte (rest ++ [Byte.one]))
        by (subst bs; list_solve).
      replace (sublist (Zlength rest + 1) 16 (map Vubyte bs))
        with (Zrepeat (Vubyte (Byte.repr 0)) (16 - (Zlength rest + 1))) by (subst bs; list_solve).
      entailer!. }
    assert (F5: field_compatible t_p1305_block_state [] (offset_val 40 desc)).
    { pose proof (field_compatible_nested_field t_p1305_ctx (DOT poly1305.code._state) desc
                ltac:(auto with field_compatible)) as X.
      simpl in X. exact X. }
    rewrite (field_at_data_at sh t_p1305_ctx (DOT poly1305.code._state)).
    rewrite field_compatible_field_address by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset.
    forward_call (sh, offset_val 40 desc, h, p1305_r key, sh, desc, bs, 0).
    { rewrite Hbs. entailer!. cbv [eval_field typeof]. simpl.
      rewrite isptr_offset_val_zero by auto with field_compatible. reflexivity. }
    { split; [apply pf3_r_ok | rewrite Hbs; reflexivity]. }
    Intros h'.
    assert (HM: p1305_limbs_val h' mod p1305_p = p1305_acc (p1305_r key) 0 msg).
    { rewrite H5. unfold bs. rewrite pf3_core_last_mod by lia. rewrite H1.
      pose proof (pf3_acc_split (p1305_r key) msg) as HA. cbv zeta in HA.
      change (Zlength msg / 16 * 16) with n in HA. fold rest in HA.
      rewrite if_true in HA by lia. rewrite HA. reflexivity. }
    Exists h' (map Vubyte bs) (Vint (Int.repr (Zlength rest + 1))).
    unfold prim_bytes. rewrite Hbs, if_false by lia.
    rewrite (field_at_data_at sh t_p1305_ctx (DOT poly1305.code._buf)),
      (field_at_data_at sh t_p1305_ctx (DOT poly1305.code._state)).
    rewrite !field_compatible_field_address by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset. rewrite isptr_offset_val_zero by auto with field_compatible.
    entailer!.
  - forward.
    destruct Hrest as [Hk Hk'].
    assert (Hk0: Zlength rest = 0).
    { apply repr_inj_unsigned in H3; rep_lia. }
    assert (HM: p1305_limbs_val h mod p1305_p = p1305_acc (p1305_r key) 0 msg).
    { rewrite H1.
      pose proof (pf3_acc_split (p1305_r key) msg) as HA. cbv zeta in HA.
      change (Zlength msg / 16 * 16) with n in HA.
      rewrite if_false in HA by lia. rewrite HA. reflexivity. }
    Exists h (map Vubyte rest ++ junk) (Vint (Int.repr (Zlength rest))).
    entailer!.
  - Intros h' bufv blv.
    assert (F5: field_compatible t_p1305_block_state [] (offset_val 40 desc)).
    { pose proof (field_compatible_nested_field t_p1305_ctx (DOT poly1305.code._state) desc
                ltac:(auto with field_compatible)) as X.
      simpl in X. exact X. }
    rewrite (field_at_data_at sh t_p1305_ctx (DOT poly1305.code._state)),
      (field_at_data_at sh t_p1305_ctx (DOT poly1305.code._s)).
    rewrite !field_compatible_field_address by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset.
    change (p1305_bstate_val h' (p1305_r key)) with (pf3_bstate_val h' (p1305_key_val (p1305_r key))).
    rewrite pf3_bstate_split by auto. Intros.
    forward_call (sh, offset_val 40 desc, h', sh, offset_val 20 desc, p1305_s_words key, osh, dst).
    sep_apply (pf3_final_fold sh h' (p1305_key_val (p1305_r key)) bufv blv (map Vint (p1305_s_words key)) desc FC).
    rewrite H4, pf3_s_words by auto.
    change (le_bytes 16 ((p1305_acc (p1305_r key) 0 msg + p1305_s key) mod 2 ^ 128)) with (poly1305_tag key msg).
    remember (poly1305_tag key msg) as tag.
    forward_call (sh, desc, 0, 112).
    sep_apply (pf3_ctx_zero sh desc); auto.
    entailer!.
Qed.

(* all of them *)
Theorem p1305_update_final_callee_bodies :
  (@semax_body (QPvarspecs Poly1305.qp) [@memcpy_spec Poly1305.CS; poly1305_blocks_generic_spec] Poly1305.CS WgNoise.poly1305.code.f_poly1305_update poly1305_update_spec3)
  /\ (@semax_body (QPvarspecs Poly1305.qp) [@memset_spec Poly1305.CS; poly1305_blocks_generic_spec; poly1305_emit_generic_spec] Poly1305.CS WgNoise.poly1305.code.f_poly1305_final poly1305_final_spec).
Proof. exact (conj body_poly1305_update_callee body_poly1305_final_callee). Qed.
