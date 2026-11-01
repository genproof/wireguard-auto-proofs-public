(* main of law prim_blake2s, segment C (statement 16): the chunk loop
   while (pos < n) { c = nondet_size(); if (c > n - pos) c = n - pos; blake2s_update(&ctx, msg + pos, c); pos += c; }. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.harness.prim_blake2s.hb2s_spec.
Require Import WgNoise.proof.harness.prim_blake2s.hb2s_main_defs.
Require Import WgNoise.proof.libc.libc_bytes.
Require WgNoise.harness.x_prim_blake2s.code.

#[local] Existing Instance W_prim_blake2s.
Local Open Scope Z_scope.

(* the message buffer without the chunk [pos, pos + c) *)
Definition hb2s_rest (sh: share) (n: Z) (mb: list byte) (pos c: Z) (msg: val) : mpred :=
  !! field_compatible (tarray tuchar n) [] msg &&
  (data_at sh (tarray tuchar pos) (map Vubyte (sublist 0 pos mb)) msg *
   data_at sh (tarray tuchar (n - (pos + c))) (map Vubyte (sublist (pos + c) n mb))
     (field_address0 (tarray tuchar n) (SUB (pos + c)) msg))%logic.

Lemma hb2s_chunk_split sh n mb pos c msg :
  0 <= pos -> 0 <= c -> pos + c <= n -> Zlength mb = n ->
  data_at sh (tarray tuchar n) (map Vubyte mb) msg =
  (b2s_bytes sh (sublist pos (pos + c) mb) (offset_val pos msg) * hb2s_rest sh n mb pos c msg)%logic.
Proof.
  intros Hp Hc Hn Hl. unfold hb2s_rest, b2s_bytes.
  rewrite Zlength_sublist by lia.
  destruct (Z.eq_dec (pos + c - pos) 0).
  - assert (c = 0) by lia. subst c. rewrite Z.add_0_r, emp_sepcon.
    apply pred_ext; [assert_PROP (field_compatible (tarray tuchar n) [] msg) by entailer! |];
    rewrite (split2_data_at_Tarray_tuchar sh n pos (map Vubyte mb)) by (rewrite ?Zlength_map; lia);
    rewrite !sublist_map; entailer!.
  - rewrite (@data_at_tarray_tuchar_cs Blake2s.CS W_prim_blake2s).
    replace (pos + c - pos) with c by lia.
    apply pred_ext; [assert_PROP (field_compatible (tarray tuchar n) [] msg) by entailer! |];
    rewrite (split3_data_at_Tarray_tuchar sh n pos (pos + c) (map Vubyte mb)) by (rewrite ?Zlength_map; lia);
    rewrite !sublist_map; replace (pos + c - pos) with c by lia;
    Intros; saturate_local;
      (rewrite (field_address0_offset (tarray tuchar n) (SUB pos)) by auto with field_compatible;
       simpl nested_field_offset; rewrite Z.mul_1_l, Z.add_0_l; entailer!).
Qed.

Lemma hb2s_segC_ok {Espec: OracleKind} gv vctx vkey vkc FR outlen keylen n kb mb msg copy out ref out2 :
  semax hb2s_Delta (hb2s_PC gv vctx vkey vkc FR outlen keylen n kb mb msg copy out ref out2 0) hb2s_segC
    (overridePost (hb2s_PC gv vctx vkey vkc FR outlen keylen n kb mb msg copy out ref out2 n) (hb2s_R gv)).
Proof.
  unfold hb2s_Delta, hb2s_segC, hb2s_R.
  simplify_func_tycontext. abbreviate_semax.
  forward_while (EX pos: Z, hb2s_PC gv vctx vkey vkc FR outlen keylen n kb mb msg copy out ref out2 pos).
  { Exists 0. apply ENTAIL_refl. }
  { unfold hb2s_PC, hb2s_tv. entailer!. }
  { unfold hb2s_PC, hb2s_tv, hb2s_lv, hb2s_buf, hb2s_ranges. simpl app. Intros.
    forward_call tt.
    Intros c.
    match goal with H: hb2s_ranges _ _ _ _ |- _ => pose proof H as (Hol & Hkl & Hkb & Hnr) end.
    assert (Hpn: pos < n).
    { unfold Int64.ltu in HRE. rewrite !Int64.unsigned_repr in HRE by rep_lia.
      destruct (zlt pos n); [lia | discriminate]. }
    forward_if (temp HC._c (Vlong (Int64.repr (Z.min c (n - pos))))).
    { forward. entailer!.
      match goal with H: Int64.ltu (Int64.repr ?a) (Int64.repr c) = _ |- _ =>
        unfold Int64.ltu in H; rewrite !Int64.unsigned_repr in H by rep_lia; destruct (zlt a c); try discriminate end.
      f_equal. f_equal. lia. }
    { forward. entailer!.
      match goal with H: Int64.ltu (Int64.repr ?a) (Int64.repr c) = _ |- _ =>
        unfold Int64.ltu in H; rewrite !Int64.unsigned_repr in H by rep_lia; destruct (zlt a c); try discriminate end.
      f_equal. f_equal. lia. }
    assert_PROP (isptr msg) by entailer!.
    set (c' := Z.min c (n - pos)).
    assert (Hc': 0 <= c' <= n - pos) by (subst c'; lia).
    assert (Hlc: Zlength (sublist pos (pos + c') mb) = c') by (rewrite Zlength_sublist; lia).
    rewrite (hb2s_chunk_split Ews n mb pos c' msg) by lia. flatten_sepcon_in_SEP.
    forward_call (Tsh, vctx, sublist 0 keylen kb, outlen, sublist 0 pos mb, Ews, offset_val pos msg,
                  sublist pos (pos + c') mb, gv).
    { entailer!. rewrite Hlc. destruct vctx; try contradiction; destruct msg; try contradiction; reflexivity. }
    forward.
    Exists (pos + c').
    unfold hb2s_PC, hb2s_tv, hb2s_lv, hb2s_buf. simpl app.
    rewrite <- sublist_split by lia.
    rewrite (hb2s_chunk_split Ews n mb pos c' msg) by lia.
    entailer!. }
  match goal with H: hb2s_ranges _ _ _ _ |- _ => pose proof H as (Hol & Hkl & Hkb & Hnr) end.
  assert (pos = n).
  { unfold Int64.ltu in HRE. rewrite !Int64.unsigned_repr in HRE by rep_lia.
    destruct (zlt pos n); [discriminate | lia]. }
  subst pos.
  forward.
  unfold hb2s_PC, hb2s_tv, hb2s_lv. simpl app. entailer!.
Qed.
