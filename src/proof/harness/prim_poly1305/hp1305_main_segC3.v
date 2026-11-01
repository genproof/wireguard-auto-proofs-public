(* main of law prim_poly1305, segment C (statement 12): the chunk loop of poly1305_update.  the chunk is ANY size_t
   min(c, n - pos), passed as a size_t (the clamp to 0xffffffff and the cast to unsigned int are gone). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.harness.prim_poly1305.hp1305_spec3.
Require Import WgNoise.proof.harness.prim_poly1305.hp1305_main_defs3.
Require Import WgNoise.proof.libc.libc_bytes.
Require WgNoise.harness.x_prim_poly1305.code.

#[local] Existing Instance W_prim_poly1305.
Local Open Scope Z_scope.

(* the message buffer without the chunk [pos, pos + c) *)
Definition hp1305m_rest (sh: share) (n: Z) (mb: list byte) (pos c: Z) (msg: val) : mpred :=
  !! field_compatible (tarray tuchar n) [] msg &&
  (data_at sh (tarray tuchar pos) (map Vubyte (sublist 0 pos mb)) msg *
   data_at sh (tarray tuchar (n - (pos + c))) (map Vubyte (sublist (pos + c) n mb))
     (field_address0 (tarray tuchar n) (SUB (pos + c)) msg))%logic.

Lemma hp1305m_chunk_split sh n mb pos c msg :
  0 <= pos -> 0 <= c -> pos + c <= n -> Zlength mb = n ->
  data_at sh (tarray tuchar n) (map Vubyte mb) msg =
  (@WgNoise.proof.prims.prim_api.prim_bytes Poly1305.CS sh (sublist pos (pos + c) mb) (offset_val pos msg) *
   hp1305m_rest sh n mb pos c msg)%logic.
Proof.
  intros Hp Hc Hn Hl. unfold hp1305m_rest, WgNoise.proof.prims.prim_api.prim_bytes.
  rewrite Zlength_sublist by lia.
  destruct (Z.eq_dec (pos + c - pos) 0).
  - assert (c = 0) by lia. subst c. rewrite Z.add_0_r, emp_sepcon.
    apply pred_ext; [assert_PROP (field_compatible (tarray tuchar n) [] msg) by entailer! |];
    rewrite (split2_data_at_Tarray_tuchar sh n pos (map Vubyte mb)) by (rewrite ?Zlength_map; lia);
    rewrite !sublist_map; entailer!.
  - rewrite (@data_at_tarray_tuchar_cs Poly1305.CS W_prim_poly1305).
    replace (pos + c - pos) with c by lia.
    apply pred_ext; [assert_PROP (field_compatible (tarray tuchar n) [] msg) by entailer! |];
    rewrite (split3_data_at_Tarray_tuchar sh n pos (pos + c) (map Vubyte mb)) by (rewrite ?Zlength_map; lia);
    rewrite !sublist_map; replace (pos + c - pos) with c by lia;
    Intros; saturate_local;
      (rewrite (field_address0_offset (tarray tuchar n) (SUB pos)) by auto with field_compatible;
       simpl nested_field_offset; rewrite Z.mul_1_l, Z.add_0_l; entailer!).
Qed.

Lemma hp1305m_segC_ok {Espec: OracleKind} gv vd vkey vkey0 vref FR n kb mb msg copy tag :
  semax hp1305m_Delta (hp1305m_PC gv vd vkey vkey0 vref FR n kb mb msg copy tag 0) hp1305m_segC
    (overridePost (hp1305m_PC gv vd vkey vkey0 vref FR n kb mb msg copy tag n) (hp1305m_R gv)).
Proof.
  unfold hp1305m_Delta, hp1305m_segC, hp1305m_R.
  simplify_func_tycontext. abbreviate_semax.
  forward_while (EX pos: Z, hp1305m_PC gv vd vkey vkey0 vref FR n kb mb msg copy tag pos).
  { Exists 0. apply ENTAIL_refl. }
  { unfold hp1305m_PC, hp1305m_tv. entailer!. }
  { unfold hp1305m_PC, hp1305m_tv, hp1305m_lv, hp1305m_buf, hp1305m_ranges. simpl app. Intros.
    forward_call tt.
    Intros c.
    match goal with H: hp1305m_ranges _ _ |- _ => pose proof H as (Hkl & Hnr) end.
    assert (Hpn: pos < n).
    { unfold Int64.ltu in HRE. rewrite !Int64.unsigned_repr in HRE by rep_lia.
      destruct (zlt pos n); [lia | discriminate]. }
    forward_if (temp HPC._c (Vlong (Int64.repr (Z.min c (n - pos))))).
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
    assert (Hc': 0 <= c' <= n - pos) by (subst c'; rep_lia).
    assert (Hlc: Zlength (sublist pos (pos + c') mb) = c') by (rewrite Zlength_sublist; lia).
    rewrite (hp1305m_chunk_split Ews n mb pos c' msg) by lia. flatten_sepcon_in_SEP.
    forward_call (Tsh, vd, kb, sublist 0 pos mb, Ews, offset_val pos msg, sublist pos (pos + c') mb).
    { entailer!. rewrite Hlc.
      destruct vd; try contradiction; destruct msg; try contradiction; simpl. reflexivity. }
    forward.
    Exists (pos + c').
    unfold hp1305m_PC, hp1305m_tv, hp1305m_lv, hp1305m_buf. simpl app.
    rewrite <- sublist_split by lia.
    rewrite (hp1305m_chunk_split Ews n mb pos c' msg) by lia.
    entailer!. }
  match goal with H: hp1305m_ranges _ _ |- _ => pose proof H as (Hkl & Hnr) end.
  assert (pos = n).
  { unfold Int64.ltu in HRE. rewrite !Int64.unsigned_repr in HRE by rep_lia.
    destruct (zlt pos n); [discriminate | lia]. }
  subst pos.
  forward.
  unfold hp1305m_PC, hp1305m_tv, hp1305m_lv. simpl app. entailer!.
Qed.
