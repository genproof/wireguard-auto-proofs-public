(* main of law prim_poly1305, segment D (statements 13..15): poly1305_final, ref_poly1305,
   CHECK(bytes_eq(tag, ref, 16)). *)
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

Lemma hp1305m_segD_le_bytes_len k z : Zlength (le_bytes k z) = Z.of_nat k.
Proof.
  revert z. induction k as [|k IH]; intros z; simpl le_bytes; [reflexivity |].
  rewrite Zlength_cons, IH. lia.
Qed.

Lemma hp1305m_segD_tag_len key msg : Zlength (poly1305_tag key msg) = 16.
Proof. unfold poly1305_tag. apply hp1305m_segD_le_bytes_len. Qed.

Lemma hp1305m_segD_ok {Espec: OracleKind} gv vd vkey vkey0 vref FR n kb mb msg copy tag :
  semax hp1305m_Delta (hp1305m_PC gv vd vkey vkey0 vref FR n kb mb msg copy tag n) hp1305m_segD
    (overridePost (hp1305m_PD gv vd vkey vkey0 vref FR) (hp1305m_R gv)).
Proof.
  unfold hp1305m_PC.
  unfold hp1305m_Delta, hp1305m_segD, hp1305m_R.
  apply hp1305m_post_canon.
  simplify_func_tycontext. abbreviate_semax.
  unfold hp1305m_buf, hp1305m_ranges, hp1305m_tv, hp1305m_lv in *. Intros. simpl app.
  rewrite (sublist_same 0 n mb) by lia.
  (* poly1305_final(&d, tag) *)
  sep_apply (data_at_data_at_ Ews (tarray tuchar 16) (Zrepeat Vundef 16) tag).
  rewrite (@data_at__tarray_tuchar_cs W_prim_poly1305 Poly1305.CS Ews 16 tag).
  forward_call (Tsh, vd, kb, mb, Ews, tag).
  rewrite (@data_at_tarray_tuchar_cs Poly1305.CS W_prim_poly1305 Ews 16 _ tag).
  subst n.
  (* ref_poly1305(ref, key, msg, n) *)
  freeze FZ := (@data_at Poly1305.CS Tsh t_p1305_ctx p1305_ctx_zero vd)
    (data_at Ews (tarray tuchar 16) (map Vubyte (poly1305_tag kb mb)) tag)
    (data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey0)
    (malloc_token Ews (tarray tuchar (Zlength mb)) msg) (malloc_token Ews (tarray tuchar (Zlength mb)) copy)
    (data_at Ews (tarray tuchar (Zlength mb)) (map Vubyte mb) copy) (malloc_token Ews (tarray tuchar 16) tag)
    (mem_mgr gv) FR.
  forward_call (Tsh, vref, Tsh, vkey, kb, Ews, msg, mb, gv).
  thaw FZ.
  (* CHECK(bytes_eq(tag, ref, 16)) *)
  remember (poly1305_tag kb mb) as d eqn:Ed.
  assert (Hd: Zlength d = 16) by (subst d; apply hp1305m_segD_tag_len).
  freeze FY := (@data_at Poly1305.CS Tsh t_p1305_ctx p1305_ctx_zero vd)
    (data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey)
    (data_at Ews (tarray tuchar (Zlength mb)) (map Vubyte mb) msg) (hp1305_globals gv).
  freeze FZ := (FRZL FY) (data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey0)
    (malloc_token Ews (tarray tuchar (Zlength mb)) msg) (malloc_token Ews (tarray tuchar (Zlength mb)) copy)
    (data_at Ews (tarray tuchar (Zlength mb)) (map Vubyte mb) copy) (malloc_token Ews (tarray tuchar 16) tag)
    (mem_mgr gv) FR.
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { replace (data_at Ews (tarray tuchar 16) (map Vubyte d) tag)
      with (data_at Ews (tarray tuchar (Zlength d)) (map Vubyte d) tag) by (rewrite Hd; reflexivity).
    replace (data_at Tsh (tarray tuchar 16) (map Vubyte d) vref)
      with (data_at Tsh (tarray tuchar (Zlength d)) (map Vubyte d) vref) by (rewrite Hd; reflexivity).
    forward_call (Ews, tag, d, Tsh, vref, d).
    { rewrite Hd. entailer!. }
    destruct (list_eq_dec Byte.eq_dec d d) as [_|C]; [| congruence].
    forward_if.
    + discriminate.
    + forward. rewrite Hd. entailer!. }
  { forward. apply ENTAIL_refl. }
  thaw FZ. thaw FY.
  unfold hp1305m_PD, hp1305m_buf, hp1305m_tv, hp1305m_lv, hp1305m_ranges. simpl app.
  Exists (Zlength mb) kb mb msg copy tag. subst d.
  unfold hp1305m_buf, hp1305m_tv, hp1305m_lv, hp1305m_ranges. simpl app. entailer!.
Qed.
