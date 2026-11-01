(* law prim_aead: main of prim_aead.h, segment C (statements 17..20: nondet ad / pt and their copies); main.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.harness.prim_aead.haead_spec3.
Require Import WgNoise.proof.harness.prim_aead.haead_lemmas3.
Require Import WgNoise.proof.harness.prim_aead.haead_main_body3_defs.
Require WgNoise.harness.x_prim_aead.code.

#[local] Existing Instance W_prim_aead.
Local Open Scope Z_scope.

Lemma hm3C_bytes (bs: list Z) :
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  map (fun b => Vint (Int.repr b)) bs = map Vubyte (map Byte.repr bs).
Proof.
  induction 1; simpl; [reflexivity |]. f_equal; auto.
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma hm3_segC_ok {Espec: OracleKind} gv vk vxn FR :
  semax hm3_Delta (hm3_PB gv vk vxn FR) hm3_segC (overridePost (hm3_PC gv vk vxn FR) (hm3_R gv)).
Proof.
  unfold hm3_PB. Intros x key nonce xn adlen n. Intros ad ad_copy pt pt_copy ct rct dec.
  unfold hm3_Delta, hm3_segC, hm3_R. apply hm3_post_canon.
  simplify_func_tycontext. abbreviate_semax.
  match goal with H: hm3_ranges _ _ _ _ _ _ |- _ => pose proof H as Hr; destruct H as (Hx & Hk & Hno & Hxn & Had & Hn) end.
  unfold hm3_tB, hm3_tA, hm3_lv, hm3_buf. simpl app. Intros.
  forward_call (ad, adlen, Ews).
  Intros bs. rewrite (hm3C_bytes bs) by auto.
  set (a := map Byte.repr bs).
  assert (Ha: Zlength a = adlen) by (subst a; rewrite Zlength_map; auto).
  clearbody a. clear dependent bs. subst adlen.
  forward_call (Ews, ad_copy, Ews, ad, a).
  forward_call (pt, n, Ews).
  Intros bs. rewrite (hm3C_bytes bs) by auto.
  set (m := map Byte.repr bs).
  assert (Hm: Zlength m = n) by (subst m; rewrite Zlength_map; auto).
  clearbody m. clear dependent bs. subst n.
  forward_call (Ews, pt_copy, Ews, pt, m).
  unfold hm3_PC. Exists x key nonce xn a m ad ad_copy pt pt_copy ct rct dec.
  unfold hm3_tB, hm3_tA, hm3_lv, hm3_buf. simpl app. entailer!.
Qed.
