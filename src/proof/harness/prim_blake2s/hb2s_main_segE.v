(* main of law prim_blake2s, segment E (statements 19..23): ref_blake2s, CHECK(out == ref), the checks
   that the context is all zero (h[0..8), t, f, buf, buflen, outlen). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.harness.prim_blake2s.hb2s_spec.
Require Import WgNoise.proof.harness.prim_blake2s.hb2s_main_defs.
Require WgNoise.harness.x_prim_blake2s.code.

#[local] Existing Instance W_prim_blake2s.
Local Open Scope Z_scope.

#[local] Instance hb2s_segE_CCE : change_composite_env Blake2s.CS W_prim_blake2s.
Proof. make_cs_preserve Blake2s.CS W_prim_blake2s. Defined.

Lemma hb2s_segE_digest_len key outlen msg :
  0 <= outlen -> Zlength (blake2s key outlen msg) = outlen.
Proof.
  intros H. unfold blake2s, b2s_digest_stream, b2s_out. cbv zeta.
  rewrite Zlength_map, Zlength_correct, upto_length. lia.
Qed.

Lemma hb2s_segE_ok {Espec: OracleKind} gv vctx vkey vkc FR :
  semax hb2s_Delta (hb2s_PD gv vctx vkey vkc FR) hb2s_segE
    (overridePost (hb2s_PE gv vctx vkey vkc FR) (hb2s_R gv)).
Proof.
  unfold hb2s_PD. Intros outlen keylen n kb mb msg copy out ref out2.
  unfold hb2s_Delta, hb2s_segE, hb2s_R.
  simplify_func_tycontext. abbreviate_semax.
  unfold hb2s_buf, hb2s_ranges, hb2s_tv, hb2s_lv in *. Intros. simpl app.
  destruct H as (Hol & Hkl & Hkb & Hn). subst n.
  replace (data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey) with
    (data_at Tsh (tarray tuchar (Zlength kb)) (map Vubyte kb) vkey) by (rewrite Hkb; reflexivity).
  forward_call (Ews, ref, outlen, Tsh, vkey, kb, keylen, Ews, msg, mb, gv).
  remember (blake2s (sublist 0 keylen kb) outlen mb) as d eqn:Ed.
  assert (Hd: Zlength d = outlen) by (subst d; apply hb2s_segE_digest_len; lia).
  subst outlen.
  (* CHECK(bytes_eq(out, ref, outlen)) *)
  match goal with |- semax _ ?P (Ssequence (Sloop _ _) _) _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward_call (Ews, out, d, Ews, ref, d).
    destruct (list_eq_dec Byte.eq_dec d d) as [_|C]; [| congruence].
    forward_if.
    + discriminate.
    + forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  (* the context, seen in W *)
  erewrite (@data_at_change_composite Blake2s.CS W_prim_blake2s hb2s_segE_CCE Tsh t_blake2s_ctx b2s_ctx_zero);
    [| apply JMeq_refl | prove_cs_preserve_type].
  change t_blake2s_ctx with t_hctx. unfold b2s_ctx_zero.
  (* for (i = 0; i < 8; i++) CHECK(ctx.h[i] == 0) *)
  match goal with |- semax _ (PROPx ?Pr (LOCALx ?L (SEPx ?S))) _ _ =>
    forward_for_simple_bound 8 (EX i:Z, PROPx Pr (LOCALx L (SEPx S)))%assert end.
  { entailer!. }
  { cbv beta.
    match goal with |- semax _ ?P (Sloop _ _) _ => apply semax_loop with (Q' := P) end.
    { forward.
      { entailer!. rewrite Znth_Zrepeat by lia. exact I. }
      rewrite Znth_Zrepeat by lia.
      forward_if.
      + discriminate.
      + forward. entailer!. }
    { forward. apply ENTAIL_refl. } }
  (* CHECK(ctx.t[0] == 0 && ctx.t[1] == 0 && ctx.f[0] == 0 && ctx.f[1] == 0) *)
  match goal with |- semax _ ?P (Ssequence (Sloop _ _) _) _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward. forward_if (temp HC._t'16 (Vint Int.one)).
    { forward. forward. entailer!. }
    { congruence. }
    forward_if (temp HC._t'17 (Vint Int.one)).
    { forward. forward. entailer!. }
    { discriminate. }
    forward_if (temp HC._t'18 (Vint Int.one)).
    { forward. forward. entailer!. }
    { discriminate. }
    forward_if.
    { discriminate. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  (* CHECK(bytes_zero(ctx.buf, 64) && ctx.buflen == 0 && ctx.outlen == 0) *)
  match goal with |- semax _ ?P (Sloop _ _) _ => apply semax_loop with (Q' := P) end.
  { unfold_data_at (data_at _ t_hctx _ vctx).
    rewrite (field_at_data_at _ t_hctx (DOT HC._buf)).
    assert (Ez: Zrepeat (Vubyte Byte.zero) 64 = map Vubyte (Zrepeat Byte.zero 64)) by reflexivity.
    simpl nested_field_type. rewrite Ez.
    forward_call (Tsh, field_address t_hctx (DOT HC._buf) vctx, Zrepeat Byte.zero 64).
    { rewrite Zlength_Zrepeat by lia. rep_lia. }
    replace (Zlength (Zrepeat Byte.zero 64)) with 64 by reflexivity.
    destruct (list_eq_dec Byte.eq_dec (Zrepeat Byte.zero 64) (Zrepeat Byte.zero 64)) as [_|C];
      [| congruence].
    forward_if (temp HC._t'20 (Vint Int.one)).
    { forward. forward. entailer!. }
    { discriminate. }
    forward_if (temp HC._t'21 (Vint Int.one)).
    { forward. forward. entailer!. }
    { discriminate. }
    forward_if.
    { discriminate. }
    forward. entailer!. }
  { forward.
    unfold hb2s_PE. Exists (Zlength d) keylen (Zlength mb) kb mb msg copy out ref out2.
    unfold hb2s_buf, hb2s_ranges, hb2s_tv, hb2s_lv. rewrite Hkb, <- Ed. simpl app.
    sep_apply (data_at_data_at_ Tsh t_hctx). entailer!. }
Qed.
