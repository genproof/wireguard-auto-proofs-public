
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

(* a malloc'd non-NULL buffer of n bytes is a valid pointer (also for n = 0: the token) *)
Lemma htl5_segB_mres_valid (n: Z) (p: val) :
  (malloc_token Ews (tarray tuchar n) p * data_at_ Ews (tarray tuchar n) p)%logic |-- valid_pointer p.
Proof.
  destruct (zlt 0 n).
  - apply sepcon_valid_pointer2. unfold data_at_. apply data_at_valid_ptr; auto.
    simpl. rewrite Z.max_r by lia. lia.
  - apply sepcon_valid_pointer1. apply malloc_token_valid_pointer. simpl. lia.
Qed.

Lemma htl5_segB_bytes (bs: list Z) :
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  map (fun b => Vint (Int.repr b)) bs = map Vubyte (map Byte.repr bs).
Proof.
  induction 1; simpl; [reflexivity |]. f_equal; auto.
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

(* le32_store over a byte buffer gives a byte buffer again *)
Lemma htl5_segB_splice (pk: list byte) (w: int) :
  4 <= Zlength pk ->
  haead_splice 0 (le32_bytes w) (map Vubyte pk) = map Vubyte (le32_bytes w ++ sublist 4 (Zlength pk) pk).
Proof.
  intros H. unfold haead_splice. rewrite !map_app, Zlength_map.
  replace (Zlength (le32_bytes w)) with 4 by reflexivity.
  rewrite sublist_nil, app_nil_l. f_equal. rewrite sublist_map. reflexivity.
Qed.

#[local] Hint Resolve htl5_segB_mres_valid : valid_pointer.

Lemma htl5_segB_ok {Espec: OracleKind} gv vk FR :
  semax htl5_Delta (htl5_PA gv vk FR) htl5_segB (overridePost (htl5_PB gv vk FR) (htl5_R gv)).
Proof.
  unfold htl5_PA. Intros key nonce tot type.
  unfold htl5_Delta, htl5_segB, htl5_R. apply htl5_post_canon.
  simplify_func_tycontext. abbreviate_semax.
  match goal with H: htl5_ranges _ _ _ |- _ => pose proof H as Hr; destruct H as (Hk & Hno & Htot) end.
  unfold htl5_lv. simpl app.
  forward_call (tarray tuchar tot, gv).
  { simpl sizeof. rewrite Z.max_r by lia. rep_lia. }
  Intros pkt.
  destruct (eq_dec pkt nullval) as [Hnull | Hnn].
  { subst pkt. forward_if.
    - forward. sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (map Vubyte key) vk). cancel.
    - contradiction H. reflexivity. }
  forward_if.
  { contradiction. }
  Intros.
  forward_call (pkt, tot, Ews).
  Intros bs. rewrite (htl5_segB_bytes bs) by auto.
  set (pk := map Byte.repr bs).
  assert (Hpk: Zlength pk = tot) by (subst pk; rewrite Zlength_map; auto).
  clearbody pk. clear dependent bs.
  forward_if (PROP () LOCAL (temp TLC._pkt pkt; temp TLC._nonce (Vlong (Int64.repr nonce));
     temp TLC._tot (Vlong (Int64.repr tot)); temp TLC._type (Vint (Int.repr type));
     lvar TLC._key (tarray tuchar 32) vk; gvars gv)
    SEP (EX pk': list byte, !! (Zlength pk' = tot) && data_at Ews (tarray tuchar tot) (map Vubyte pk') pkt;
         mem_mgr gv; malloc_token Ews (tarray tuchar tot) pkt;
         data_at Tsh (tarray tuchar 32) (map Vubyte key) vk; zero_page gv; htl5_minusp gv; FR)).
  - assert (H4: 4 <= tot) by (rewrite !Int64.unsigned_repr in H1 by rep_lia; lia).
    forward_call (Ews, pkt, 0, map Vubyte pk, Int.repr type).
    { entailer!. }
    { rewrite Zlength_map, Hpk. cancel. }
    { rewrite Zlength_map. lia. }
    rewrite Zlength_map, Hpk. rewrite htl5_segB_splice by lia.
    entailer!. Exists (le32_bytes (Int.repr type) ++ sublist 4 (Zlength pk) pk).
    entailer!. rewrite Zlength_app, Zlength_sublist by lia. change (Zlength (le32_bytes _)) with 4. lia.
  - forward. entailer!. Exists pk. entailer!.
  - Intros pk'. unfold htl5_PB. Exists key nonce tot type pkt pk'.
    unfold htl5_lv, htl5_buf. simpl app. entailer!.
Qed.
