(* main of law prim_poly1305, segment F (statements 20..24): CHECK(msg == copy && key == key0), the
   frees, return 0. *)
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

Lemma hp1305m_segF_ok {Espec: OracleKind} gv vd vkey vkey0 vref FR :
  semax hp1305m_Delta (hp1305m_PE gv vd vkey vkey0 vref FR) hp1305m_segF (overridePost FF (hp1305m_R gv)).
Proof.
  unfold hp1305m_PE. Intros n kb mb msg copy tag.
  unfold hp1305m_Delta, hp1305m_segF, hp1305m_R. apply hp1305m_post_canon.
  simplify_func_tycontext. abbreviate_semax.
  unfold hp1305m_buf, hp1305m_ranges, hp1305m_tv, hp1305m_lv in *. Intros. simpl app.
  destruct H as (Hkb & Hn). subst n.
  remember (poly1305_tag kb mb) as T eqn:ET; clear ET.
  assert_PROP (isptr msg /\ isptr copy /\ isptr tag) as Hp by entailer!.
  destruct Hp as (Pm & Pc & Pt).
  freeze FZ := (data_at_ Tsh t_hpctx vd) (data_at Tsh (tarray tuchar 16) (map Vubyte T) vref)
    (malloc_token Ews (tarray tuchar (Zlength mb)) msg) (malloc_token Ews (tarray tuchar (Zlength mb)) copy)
    (malloc_token Ews (tarray tuchar 16) tag) (data_at Ews (tarray tuchar 16) (map Vubyte T) tag)
    (mem_mgr gv) (hp1305_globals gv) FR.
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
  { apply ENTAIL_refl. }
  { forward_call (Ews, msg, mb, Ews, copy, mb).
    rewrite if_true by auto.
    forward_if (temp HPC._t'13 (Vint Int.one)).
    - replace (data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey)
        with (data_at Tsh (tarray tuchar (Zlength kb)) (map Vubyte kb) vkey) by (rewrite Hkb; reflexivity).
      replace (data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey0)
        with (data_at Tsh (tarray tuchar (Zlength kb)) (map Vubyte kb) vkey0) by (rewrite Hkb; reflexivity).
      forward_call (Tsh, vkey, kb, Tsh, vkey0, kb).
      + entailer!. rewrite Hkb. reflexivity.
      + rewrite if_true by auto. rewrite Hkb. forward. entailer!.
    - discriminate.
    - forward_if True; [ discriminate | forward; entailer! | ].
      forward. entailer!. }
  thaw FZ.
  freeze FZ := (data_at_ Tsh t_hpctx vd) (data_at Tsh (tarray tuchar 16) (map Vubyte T) vref)
    (malloc_token Ews (tarray tuchar (Zlength mb)) copy) (data_at Ews (tarray tuchar (Zlength mb)) (map Vubyte mb) copy)
    (malloc_token Ews (tarray tuchar 16) tag) (data_at Ews (tarray tuchar 16) (map Vubyte T) tag)
    (hp1305_globals gv) FR (data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey)
    (data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey0).
  forward_call (tarray tuchar (Zlength mb), msg, gv).
  { rewrite if_false by (destruct msg; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength mb)) (map Vubyte mb) msg). cancel. }
  thaw FZ.
  freeze FZ := (data_at_ Tsh t_hpctx vd) (data_at Tsh (tarray tuchar 16) (map Vubyte T) vref)
    (malloc_token Ews (tarray tuchar 16) tag) (data_at Ews (tarray tuchar 16) (map Vubyte T) tag)
    (hp1305_globals gv) FR (data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey)
    (data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey0).
  forward_call (tarray tuchar (Zlength mb), copy, gv).
  { rewrite if_false by (destruct copy; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength mb)) (map Vubyte mb) copy). cancel. }
  thaw FZ.
  freeze FZ := (data_at_ Tsh t_hpctx vd) (data_at Tsh (tarray tuchar 16) (map Vubyte T) vref)
    (hp1305_globals gv) FR (data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey)
    (data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey0).
  forward_call (tarray tuchar 16, tag, gv).
  { rewrite if_false by (destruct tag; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar 16) (map Vubyte T) tag). cancel. }
  thaw FZ.
  forward.
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (map Vubyte kb) vkey).
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (map Vubyte kb) vkey0).
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 16) (map Vubyte T) vref).
  unfold t_hpctx. cancel.
Qed.
