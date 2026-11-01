(* main of law prim_blake2s, segment D (statements 17..18: the optional empty update
   if (nondet_u8() & 1) blake2s_update(&ctx, msg, 0), then blake2s_final(&ctx, out)). *)
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

Lemma hb2s_segD_post_canon {Espec: OracleKind} {cs: compspecs} Delta P c Q gv F :
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (PROP () LOCAL () SEP (TT))) F)) ->
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (hb2s_post gv)) F)).
Proof.
  intros H. eapply semax_post; [| | | | apply H]; intros; simpl; intros rho; apply andp_left2;
    try apply derives_refl.
  apply sepcon_derives; [| apply derives_refl]. revert rho. apply bind_ret_derives. intros rho. apply TT_right.
Qed.

(* byte arrays are the same predicates in every compspecs (as libc_bytes.v) *)
Lemma hb2s_segD_fc_cs {cs1 cs2: compspecs} n p :
  @field_compatible cs1 (tarray tuchar n) nil p <-> @field_compatible cs2 (tarray tuchar n) nil p.
Proof.
  assert (A: forall (ce: composite_env) z, align_compatible_rec ce (tarray tuchar n) z).
  { intros. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  unfold field_compatible, size_compatible, align_compatible.
  destruct p; simpl; try tauto.
  pose proof (A (@cenv_cs cs1) (Ptrofs.unsigned i)). pose proof (A (@cenv_cs cs2) (Ptrofs.unsigned i)).
  tauto.
Qed.

Lemma hb2s_segD_data_at_cs {cs1 cs2: compspecs} sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext. apply hb2s_segD_fc_cs.
Qed.

Lemma hb2s_segD_data_at__cs {cs1 cs2: compspecs} sh n p :
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof. unfold data_at_, field_at_. apply hb2s_segD_data_at_cs. Qed.

Lemma hb2s_segD_ok {Espec: OracleKind} gv vctx vkey vkc FR outlen keylen n kb mb msg copy out ref out2 :
  semax hb2s_Delta (hb2s_PC gv vctx vkey vkc FR outlen keylen n kb mb msg copy out ref out2 n) hb2s_segD
    (overridePost (hb2s_PD gv vctx vkey vkc FR) (hb2s_R gv)).
Proof.
  unfold hb2s_PC.
  unfold hb2s_Delta, hb2s_segD, hb2s_R.
  apply hb2s_segD_post_canon.
  simplify_func_tycontext. abbreviate_semax.
  unfold hb2s_buf, hb2s_ranges, hb2s_tv, hb2s_lv in *. Intros. simpl app.
  rewrite (sublist_same 0 n mb) by lia.
  forward_call. Intros b.
  forward_if (PROP () LOCAL (temp HC._pos (Vlong (Int64.repr n));
   temp HC._outlen (Vlong (Int64.repr outlen));
   temp HC._keylen (Vlong (Int64.repr keylen));
   temp HC._n (Vlong (Int64.repr n)); temp HC._msg msg;
   temp HC._copy copy; temp HC._out out; temp HC._ref ref;
   temp HC._out2 out2; lvar HC._ctx t_hctx vctx;
   lvar HC._key (tarray tuchar 32) vkey;
   lvar HC._key_copy (tarray tuchar 32) vkc; gvars gv)
   SEP (blake2s_state Tsh (sublist 0 keylen kb) outlen mb vctx;
   data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey;
   data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkc;
   malloc_token Ews (tarray tuchar n) msg;
   data_at Ews (tarray tuchar n) (map Vubyte mb) msg;
   malloc_token Ews (tarray tuchar n) copy;
   data_at Ews (tarray tuchar n) (map Vubyte mb) copy;
   malloc_token Ews (tarray tuchar outlen) out;
   data_at Ews (tarray tuchar outlen) (Zrepeat Vundef outlen) out;
   malloc_token Ews (tarray tuchar outlen) ref;
   data_at Ews (tarray tuchar outlen) (Zrepeat Vundef outlen) ref;
   malloc_token Ews (tarray tuchar outlen) out2;
   data_at Ews (tarray tuchar outlen) (Zrepeat Vundef outlen) out2;
   mem_mgr gv; hb2s_globals gv; blake2s_globals gv; FR)).
  - forward_call (Tsh, vctx, sublist 0 keylen kb, outlen, mb, Ews, msg, @nil byte, gv).
    { rewrite b2s_bytes_nil. cancel. }
    { rewrite Zlength_nil. rep_lia. }
    rewrite app_nil_r, b2s_bytes_nil. entailer!.
  - forward. entailer!.
  - forward_call (Tsh, vctx, sublist 0 keylen kb, outlen, mb, Ews, out, gv).
    { sep_apply (data_at_data_at_ Ews (tarray tuchar outlen) (Zrepeat Vundef outlen) out).
      rewrite (@hb2s_segD_data_at__cs W_prim_blake2s Blake2s.CS). cancel. }
    unfold hb2s_PD, hb2s_buf, hb2s_tv, hb2s_lv, hb2s_ranges. simpl app.
    Exists outlen keylen n kb mb msg copy out ref out2.
    rewrite (@hb2s_segD_data_at_cs Blake2s.CS W_prim_blake2s). entailer!.
Qed.
