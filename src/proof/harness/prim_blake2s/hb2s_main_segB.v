(* main of law prim_blake2s, segment B (statements 12..15: draw the message, copy it, init / init_key,
   pos = 0). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.harness.prim_blake2s.hb2s_spec.
Require Import WgNoise.proof.harness.prim_blake2s.hb2s_main_defs.
Require WgNoise.harness.x_prim_blake2s.code.
Require Import WgNoise.proof.libc.libc_bytes.

#[local] Existing Instance W_prim_blake2s.
Local Open Scope Z_scope.

#[local] Instance CCE_hb2s_b2s : change_composite_env W_prim_blake2s Blake2s.CS.
Proof. make_cs_preserve W_prim_blake2s Blake2s.CS. Defined.

Lemma hb2s_segB_bytes (bs: list Z) :
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  map (fun b => Vint (Int.repr b)) bs = map Vubyte (map Byte.repr bs).
Proof.
  induction 1; simpl; [reflexivity |]. f_equal; auto.
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

(* the 32-byte key array split at keylen > 0: the key prefix (as init_key wants it) and the rest *)
Lemma hb2s_segB_key_split sh kb k p :
  0 < k <= 32 -> Zlength kb = 32 ->
  data_at sh (tarray tuchar 32) (map Vubyte kb) p =
  (b2s_bytes sh (sublist 0 k kb) p *
   data_at sh (tarray tuchar (32 - k)) (map Vubyte (sublist k 32 kb))
     (field_address0 (tarray tuchar 32) (SUB k) p))%logic.
Proof.
  intros Hk Hkb. rewrite b2s_bytes_nonempty by (rewrite Zlength_sublist; lia).
  rewrite Zlength_sublist by lia.
  unfold tarray. rewrite (split2_data_at_Tarray_tuchar sh 32 k) by (try rewrite Zlength_map; lia).
  rewrite !sublist_map, Z.sub_0_r.
  rewrite (@data_at_tarray_tuchar_cs W_prim_blake2s Blake2s.CS sh k). reflexivity.
Qed.

Lemma hb2s_segB_ok {Espec: OracleKind} gv vctx vkey vkc FR :
  semax hb2s_Delta (hb2s_PA gv vctx vkey vkc FR) hb2s_segB
    (overridePost (hb2s_PB gv vctx vkey vkc FR) (hb2s_R gv)).
Proof.
  unfold hb2s_PA. Intros outlen keylen n kb msg copy out ref out2.
  unfold hb2s_Delta, hb2s_segB, hb2s_R.
  simplify_func_tycontext. abbreviate_semax.
  unfold hb2s_buf, hb2s_ranges, hb2s_tv, hb2s_lv in *. Intros. simpl app.
  destruct H as (Hout & Hkey & Hkb & Hn).
  forward_call (msg, n, Ews).
  Intros bs. rewrite (hb2s_segB_bytes bs) by auto.
  set (mb := map Byte.repr bs).
  assert (Hmb: Zlength mb = n) by (subst mb; rewrite Zlength_map; auto).
  clearbody mb. clear dependent bs. subst n.
  forward_call (Ews, copy, Ews, msg, mb).
  forward_if (PROP () LOCAL (temp HC._outlen (Vlong (Int64.repr outlen));
     temp HC._keylen (Vlong (Int64.repr keylen));
     temp HC._n (Vlong (Int64.repr (Zlength mb))); temp HC._msg msg;
     temp HC._copy copy; temp HC._out out; temp HC._ref ref;
     temp HC._out2 out2; lvar HC._ctx t_hctx vctx;
     lvar HC._key (tarray tuchar 32) vkey;
     lvar HC._key_copy (tarray tuchar 32) vkc; gvars gv)
     SEP (blake2s_state Tsh (sublist 0 keylen kb) outlen [] vctx;
     data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey;
     data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkc;
     malloc_token Ews (tarray tuchar (Zlength mb)) msg;
     data_at Ews (tarray tuchar (Zlength mb)) (map Vubyte mb) msg;
     malloc_token Ews (tarray tuchar (Zlength mb)) copy;
     data_at Ews (tarray tuchar (Zlength mb)) (map Vubyte mb) copy;
     malloc_token Ews (tarray tuchar outlen) out;
     data_at Ews (tarray tuchar outlen) (Zrepeat Vundef outlen) out;
     malloc_token Ews (tarray tuchar outlen) ref;
     data_at Ews (tarray tuchar outlen) (Zrepeat Vundef outlen) ref;
     malloc_token Ews (tarray tuchar outlen) out2;
     data_at Ews (tarray tuchar outlen) (Zrepeat Vundef outlen) out2;
     mem_mgr gv; hb2s_globals gv; blake2s_globals gv; FR)).
  - (* keylen > 0: blake2s_init_key *)
    rewrite Int64.unsigned_repr in H by rep_lia. rewrite Int64.unsigned_repr in H by rep_lia.
    erewrite (@data_at__change_composite W_prim_blake2s Blake2s.CS _ Tsh t_hctx); [| prove_cs_preserve_type].
    rewrite (hb2s_segB_key_split Tsh kb keylen vkey) by lia.
    forward_call (Tsh, vctx, outlen, Tsh, vkey, sublist 0 keylen kb).
    { entailer!. simpl. rewrite Zlength_sublist by lia. rewrite Z.sub_0_r. reflexivity. }
    { cancel. }
    { rewrite Zlength_sublist by lia. lia. }
    rewrite (hb2s_segB_key_split Tsh kb keylen vkey) by lia. entailer!.
  - (* keylen = 0: blake2s_init *)
    rewrite Int64.unsigned_repr in H by rep_lia. rewrite Int64.unsigned_repr in H by rep_lia.
    assert (keylen = 0) by lia. subst keylen.
    erewrite (@data_at__change_composite W_prim_blake2s Blake2s.CS _ Tsh t_hctx); [| prove_cs_preserve_type].
    forward_call (Tsh, vctx, outlen).
    rewrite sublist_nil. entailer!.
  - forward.
    unfold hb2s_PB, hb2s_PC, hb2s_ranges, hb2s_tv, hb2s_lv, hb2s_buf.
    Exists outlen keylen (Zlength mb) kb mb msg copy out ref out2.
    rewrite sublist_nil. simpl app. entailer!.
Qed.
