(* main of law prim_poly1305, segment B (statements 8..11): nondet msg, copy, poly1305_init(&d, key),
   pos = 0. *)
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

#[local] Instance CCE_hp1305_p1305 : change_composite_env W_prim_poly1305 Poly1305.CS.
Proof. make_cs_preserve W_prim_poly1305 Poly1305.CS. Defined.

Lemma hp1305m_segB_bytes (bs: list Z) :
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  map (fun b => Vint (Int.repr b)) bs = map Vubyte (map Byte.repr bs).
Proof.
  induction 1; simpl; [reflexivity |]. f_equal; auto.
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma hp1305m_segB_ok {Espec: OracleKind} gv vd vkey vkey0 vref FR :
  semax hp1305m_Delta (hp1305m_PA gv vd vkey vkey0 vref FR) hp1305m_segB
    (overridePost (hp1305m_PB gv vd vkey vkey0 vref FR) (hp1305m_R gv)).
Proof.
  unfold hp1305m_PA. Intros n kb msg copy tag.
  unfold hp1305m_Delta, hp1305m_segB, hp1305m_R.
  simplify_func_tycontext. abbreviate_semax.
  unfold hp1305m_buf, hp1305m_ranges, hp1305m_tv, hp1305m_lv in *. Intros. simpl app.
  destruct H as (Hkb & Hn).
  forward_call (msg, n, Ews).
  Intros bs. rewrite (hp1305m_segB_bytes bs) by auto.
  set (mb := map Byte.repr bs).
  assert (Hmb: Zlength mb = n) by (subst mb; rewrite Zlength_map; auto).
  clearbody mb. clear dependent bs. subst n.
  forward_call (Ews, copy, Ews, msg, mb).
  erewrite (@data_at__change_composite W_prim_poly1305 Poly1305.CS _ Tsh t_hpctx); [| prove_cs_preserve_type].
  forward_call (Tsh, vd, Tsh, vkey, kb).
  forward.
  unfold hp1305m_PB, hp1305m_PC, hp1305m_ranges, hp1305m_tv, hp1305m_lv, hp1305m_buf.
  Exists (Zlength mb) kb mb msg copy tag.
  rewrite sublist_nil. simpl app. entailer!.
  rewrite (@data_at_tarray_tuchar_cs W_prim_poly1305 Poly1305.CS Tsh 32). apply derives_refl.
Qed.
