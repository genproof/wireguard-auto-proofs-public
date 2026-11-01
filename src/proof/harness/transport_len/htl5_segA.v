
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.units.DataHeader.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.harness.common4t.ht4_worlds.
Require Import WgNoise.proof.harness.common4t.ht4c_spec.
Require Import WgNoise.proof.harness.common4t.ht4r_spec.
Require Import WgNoise.proof.harness.common4t.ht4a_aead.
Require Import WgNoise.proof.data_header.dh4_spec.
Require Import WgNoise.proof.harness.transport_len.htl5_defs.
Require WgNoise.harness.x_transport_len.code.

#[local] Existing Instance W_transport_len.
Local Open Scope Z_scope.

Lemma htl5_segA_bytes kz : Forall (fun b => 0 <= b <= Byte.max_unsigned) kz ->
  map (fun b => Vint (Int.repr b)) kz = map Vubyte (map Byte.repr kz).
Proof.
  induction 1; simpl; f_equal; auto.
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma htl5_segA_mods b m : 0 <= b <= Int.max_signed -> 0 < m <= Int.max_signed ->
  Int.mods (Int.repr b) (Int.repr m) = Int.repr (b mod m).
Proof.
  intros Hb Hm. unfold Int.mods. rewrite !Int.signed_repr by rep_lia.
  rewrite Z.rem_mod_nonneg by lia. reflexivity.
Qed.

Ltac htl5_segA_mone :=
  match goal with H: _ /\ Int.repr _ = Int.mone |- _ =>
    destruct H as [_ H]; apply (f_equal Int.unsigned) in H; vm_compute in H; discriminate end.

Ltac htl5_segA_tc := entailer!; htl5_segA_mone.

Lemma htl5_segA_ok {Espec: OracleKind} gv vk FR :
  semax htl5_Delta (htl5_P0 gv vk FR) htl5_segA (overridePost (htl5_PA gv vk FR) (htl5_R gv)).
Proof.
  unfold htl5_P0, htl5_Delta, htl5_segA, htl5_R.
  apply htl5_post_canon.
  simplify_func_tycontext. abbreviate_semax.
  unfold htl5_lv.
  forward_call (vk, 32, Tsh). Intros kz.
  forward_call. Intros nonce.
  rewrite htl5_segA_bytes by auto.
  forward_call. Intros b.
  apply semax_seq with (EX tot: Z,
    PROP (0 <= tot <= Int64.max_unsigned)
    LOCAL (temp TLC._tot (Vlong (Int64.repr tot)); temp TLC._nonce (Vlong (Int64.repr nonce));
           lvar TLC._key (tarray tuchar 32) vk; gvars gv)
    SEP (data_at Tsh (tarray tuchar 32) (map Vubyte (map Byte.repr kz)) vk; mem_mgr gv; zero_page gv;
         htl5_minusp gv; FR)).
  { eapply (semax_switch_PQR (b mod 4)); [reflexivity | entailer! | entailer! | ].
    { htl5_segA_mone. }
    { f_equal. apply htl5_segA_mods; rep_lia. }
    pose proof (Z.mod_pos_bound b 4 ltac:(lia)).
    unfold select_switch at 1; unfold select_switch_default at 1.
    process_cases Signed.
    - forward_call. Intros c. forward; [htl5_segA_tc |].
      rewrite htl5_segA_mods by rep_lia. pose proof (Z.mod_pos_bound c 40 ltac:(lia)).
      rewrite Int.signed_repr by rep_lia.
      forward.
      Exists (c mod 40). entailer!.
    - forward_call. Intros c. pose proof (Z.mod_pos_bound c 8 ltac:(lia)).
      forward.
      { entailer!. rewrite htl5_segA_mods by rep_lia. rewrite Int.signed_repr by rep_lia. split; [rep_lia |].
        intros [_ Hm]. apply (f_equal Int.unsigned) in Hm. vm_compute in Hm. discriminate. }
      rewrite htl5_segA_mods by rep_lia. rewrite add_repr, Int.signed_repr by rep_lia.
      forward.
      Exists (32 + c mod 8). entailer!.
    - forward_call. Intros c. forward; [htl5_segA_tc |].
      rewrite htl5_segA_mods by rep_lia. pose proof (Z.mod_pos_bound c 300 ltac:(lia)).
      rewrite Int.signed_repr by rep_lia.
      forward.
      Exists (c mod 300). entailer!.
    - forward_call. Intros n. forward.
      Exists n. entailer!. }
  abbreviate_semax. Intros tot.
  forward_if.
  { forward. sep_apply (data_at_data_at_ Tsh (tarray tuchar 32)). cancel. }
  change (Int64.unsigned (Int64.sub (Int64.repr 9223372036854775807) (Int64.repr 32)))
    with (9223372036854775807 - 32) in *.
  rewrite Int64.unsigned_repr in * by rep_lia.
  forward_call. Intros b2.
  eapply (semax_switch_PQR (b2 mod 4)); [reflexivity | entailer! | entailer! | ].
  { htl5_segA_mone. }
  { f_equal. apply htl5_segA_mods; rep_lia. }
  pose proof (Z.mod_pos_bound b2 4 ltac:(lia)).
  unfold select_switch at 1; unfold select_switch_default at 1.
  process_cases Signed.
  - forward. forward.
    unfold htl5_PA. Exists (map Byte.repr kz) nonce tot 1.
    unfold htl5_ranges, htl5_lv. simpl app.
    entailer!. rewrite Zlength_map. rep_lia.
  - forward. forward.
    unfold htl5_PA. Exists (map Byte.repr kz) nonce tot 3.
    unfold htl5_ranges, htl5_lv. simpl app.
    entailer!. rewrite Zlength_map. rep_lia.
  - forward_call. Intros t. forward.
    unfold htl5_PA. Exists (map Byte.repr kz) nonce tot t.
    unfold htl5_ranges, htl5_lv. simpl app.
    entailer!. rewrite Zlength_map. rep_lia.
  - forward. forward.
    unfold htl5_PA. Exists (map Byte.repr kz) nonce tot 4.
    unfold htl5_ranges, htl5_lv. simpl app.
    entailer!. rewrite Zlength_map. rep_lia.
Qed.
