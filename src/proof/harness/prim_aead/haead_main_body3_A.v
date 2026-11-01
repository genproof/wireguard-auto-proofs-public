(* law prim_aead: main of prim_aead.h, segment A (statements 0..8: x = nondet_u8() & 1, nondet key / xnonce, nonce, adlen, n, the PTRDIFF_MAX returns and the LEN_LIMIT test); main.
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

Lemma hm3A_bytes kz : Forall (fun b => 0 <= b <= Byte.max_unsigned) kz ->
  map (fun b => Vint (Int.repr b)) kz = map Vubyte (map Byte.repr kz).
Proof.
  induction 1; simpl; f_equal; auto.
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma hm3A_ltu_m1 n : 0 <= n <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr (-1)) (Int64.repr n) = false.
Proof.
  intros Hn. unfold Int64.ltu. change (Int64.unsigned (Int64.repr (-1))) with Int64.max_unsigned.
  rewrite Int64.unsigned_repr by rep_lia. destruct zlt; [rep_lia | reflexivity].
Qed.

Lemma hm3A_ltu_m17 n : 0 <= n <= Int64.max_unsigned - 16 ->
  Int64.ltu (Int64.repr (-1 - 16)) (Int64.repr n) = false.
Proof.
  intros Hn. unfold Int64.ltu.
  change (Int64.unsigned (Int64.repr (-1 - 16))) with (Int64.max_unsigned - 16).
  rewrite Int64.unsigned_repr by rep_lia. destruct zlt; [rep_lia | reflexivity].
Qed.

Lemma hm3A_and1 b : 0 <= b <= Byte.max_unsigned ->
  Int.and (Int.repr b) (Int.repr 1) = Int.repr (Z.land b 1).
Proof. intros Hb. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma hm3A_land1 b : 0 <= Z.land b 1 <= 1.
Proof.
  change (Z.land b 1) with (Z.land b (Z.ones 1)). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound b (2 ^ 1) ltac:(lia)). lia.
Qed.

Lemma hm3_segA_ok {Espec: OracleKind} gv vk vxn FR :
  semax hm3_Delta (hm3_P0 gv vk vxn FR) hm3_segA (overridePost (hm3_PA gv vk vxn FR) (hm3_R gv)).
Proof.
  unfold hm3_P0, hm3_Delta, hm3_segA, hm3_R.
  apply hm3_post_canon.
  simplify_func_tycontext. abbreviate_semax.
  unfold hm3_lv.
  forward_call. Intros b. forward.
  forward_call (vk, 32, Tsh). Intros kz.
  forward_call (vxn, 24, Tsh). Intros xz.
  forward_call. Intros nonce.
  forward_call. Intros adlen.
  forward_if.
  { forward. sep_apply (data_at_data_at_ Tsh (tarray tuchar 32)). sep_apply (data_at_data_at_ Tsh (tarray tuchar 24)). cancel. }
  forward_call. Intros n.
  forward_if.
  { forward. sep_apply (data_at_data_at_ Tsh (tarray tuchar 32)). sep_apply (data_at_data_at_ Tsh (tarray tuchar 24)). cancel. }
  change (Int64.unsigned (Int64.sub (Int64.repr 9223372036854775807) (Int64.repr 16))) with (9223372036854775807 - 16) in *.
  rewrite Int64.unsigned_repr in * by rep_lia.
  forward_if (temp HAC._t'5 (Vint Int.zero)).
  { rewrite hm3A_ltu_m1 in * by rep_lia. discriminate. }
  { forward. entailer!. unfold Int64.cmpu. rewrite hm3A_ltu_m1 by rep_lia. reflexivity. }
  forward_if (temp HAC._t'6 (Vint Int.zero)).
  { congruence. }
  { forward. entailer!. unfold Int64.cmpu. rewrite hm3A_ltu_m17 by rep_lia. reflexivity. }
  forward_if.
  { congruence. }
  forward.
  rewrite hm3A_and1 by auto. rewrite !hm3A_bytes by auto.
  pose proof (hm3A_land1 b).
  unfold hm3_PA. Exists (Z.land b 1) (map Byte.repr kz) nonce (map Byte.repr xz) adlen n.
  unfold hm3_ranges, hm3_tA, hm3_lv. simpl app.
  entailer!. rewrite !Zlength_map. rep_lia.
Qed.
