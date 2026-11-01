(* law handshake, phase P6, segment G = statements 112..113: keypairs_clear(pb), keypairs_clear(pa).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.handshake.hhs3_spec.
Require Import WgNoise.proof.harness.handshake.hhs3_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_conv.
Require Import WgNoise.proof.harness.handshake.hhs3_p6_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Lemma hhs3_p6_G_hmac_len key m : Zlength (hmac key m) = 32.
Proof. unfold hmac, HASH, model.blake2s, model.b2s_digest_stream, model.b2s_out. rewrite Zlength_map. reflexivity. Qed.

Lemma hhs3_p6_G_hout sh bs p n : Zlength bs = n -> hbytes sh bs p |-- hout sh n p.
Proof. intros <-. unfold hbytes, hout. apply data_at_data_at_. Qed.

Lemma hhs3_p6_G_snap_out sh v p : @data_at HCS sh t_hsnap v p |-- @data_at_ HCS sh t_hsnap p.
Proof. apply data_at_data_at_. Qed.

(* one keypair k (in the pool of T at k with e_peer p), in one slot *)
Lemma hhs3_p6_G_kps T p k K E :
  sfind (t_D T) k = Some (Ews, E) -> e_peer E = p -> kps_in_pool T p [(k, K)].
Proof.
  intros H1 H2. split.
  - constructor; [intros [] | constructor].
  - constructor; [| constructor]. exists E. auto.
Qed.

Lemma hhs3_p6_G_slots P k K :
  k <> nullval -> p_prev P = nullval ->
  ((p_cur P = k /\ p_next P = nullval) \/ (p_cur P = nullval /\ p_next P = k)) ->
  slots_ok P [(k, K)].
Proof.
  intros Hk Hp Hcn. unfold slots_ok. rewrite Hp.
  destruct Hcn as [[Hc Hn] | [Hc Hn]]; rewrite Hc, Hn; cbn [filter map fst];
    rewrite ?if_true by reflexivity; rewrite ?if_false by assumption;
    (split; [repeat constructor; auto; left; reflexivity | repeat constructor; auto]).
Qed.

Lemma hhs3_p6_G_sfind_hd {A: Type} k (E: A) l : sfind ((k, Ews, E) :: l) k = Some (Ews, E).
Proof. simpl. rewrite if_true by reflexivity. reflexivity. Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p6_G_ok {Espec: OracleKind} gv L FR V :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hhs3_p6_pure x25519 aead_enc aead_dec -> hhs3_p6_free_stmt x25519 ->
  hhs3_p6_ctx x25519 aead_enc aead_dec L V ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p6_SF x25519 gv L FR V) hhs3_p6_G
    (overridePost (hhs3_p6_SG x25519 gv L FR V) (hhs3_R gv)).
Proof.
  intros HH HP HF HC. unfold hhs3_p6_SF, hhs3_p6_SEF, hhs3_Delta, hhs3_R, hhs3_p6_G.
  simplify_func_tycontext. abbreviate_semax.
  Intros ka kb.
  destruct HH as [Hx [Ha HHr]]. destruct HP as [HfA [HfB [Hck Hmod]]].
  destruct (HfA Hx Ha L V HC) as [EPB _].
  destruct (HfB Hx Ha L V HC) as (_ & _ & _ & _ & Hdead & Hcur & Hprev & Hnext & Hdev).
  destruct (Hmod Hx Ha L V HC HfA HfB) as (_ & _ & _ & _ & Hclr1 & Hclr2).
  assert (DB: p_device (hhs3_p6_PB3 V ka) = l_wa L).
  { unfold hhs3_p6_PB3, hhs3_p6_PBa. rewrite EPB. unfold hhs3_p6_PB2n. destruct (w_ST2 V). reflexivity. }
  assert (DA: p_device (hhs3_p6_PA4 x25519 V kb) = l_wb L).
  { unfold hhs3_p6_PA4, hhs3_p6_PAa, hhs3_PA3, hhs3_PA2. exact Hdev. }
  unfold hhs3_p6_sep, hhs3_globs, hhs3_p6_locals, hhs3_lvars, hhs3_cnt_temps, hhs3_setup_sep. cbn [app].
  (* wg_noise_keypairs_clear(&pb.keypairs) *)
  change (l_ita L) with (d_itab (hhs3_DA x25519 (w_R V) L)).
  forward_call (gv, hhs3_p6_S2 V, [(ka, hhs3_p6_KA V)], hhs3_p6_TA2 L V ka, Tsh, l_pb L, hhs3_p6_PB3 V ka,
    Tsh, l_wa L, hhs3_DA x25519 (w_R V) L, Tsh).
  { split.
    - apply hhs3_p6_G_kps with (E := mkEntry (l_pb L) IDX_KEYPAIR (i_idx (w_I V)));
        [apply hhs3_p6_G_sfind_hd | reflexivity].
    - apply hhs3_p6_G_slots; [assumption | reflexivity | left; split; reflexivity]. }
  rewrite (Hclr1 ka (hhs3_p6_S2 V) H). cbn [fst snd kw_S kw_KS kw_T].
  (* wg_noise_keypairs_clear(&pa.keypairs) *)
  change (l_itb L) with (d_itab (hhs3_DB x25519 (w_R V) L)).
  forward_call (gv, shim_free (hhs3_p6_S2 V), [(kb, hhs3_p6_KB V)], hhs3_p6_TB2 L V kb, Tsh, l_pa L,
    hhs3_p6_PA4 x25519 V kb, Tsh, l_wb L, hhs3_DB x25519 (w_R V) L, Tsh).
  { split.
    - apply hhs3_p6_G_kps with (E := mkEntry (l_pa L) IDX_KEYPAIR (s_idx (w_Q V)));
        [apply hhs3_p6_G_sfind_hd | reflexivity].
    - apply hhs3_p6_G_slots; [assumption | reflexivity | right; split; reflexivity]. }
  rewrite (Hclr2 kb (shim_free (hhs3_p6_S2 V)) H1). cbn [fst snd kw_S kw_KS kw_T].
  (* SG *)
  unfold hhs3_p6_SG, hhs3_p6_sep, hhs3_p6_locals, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps, hhs3_lvars.
  cbn [app]. Exists ka kb.
  change (keypairs_rep W_handshake []) with (@emp mpred _ _).
  change (d_itab (hhs3_DA x25519 (w_R V) L)) with (l_ita L).
  change (d_itab (hhs3_DB x25519 (w_R V) L)) with (l_itb L).
  unfold hhs3_p6_snapB, hhs3_p6_first, hhs3_p6_second.
  sep_apply (hhs3_p6_G_snap_out Tsh
    (hsnap_val (snap_of (hhs3_TB1 L (w_Q V)) (hs_addr (l_pa L)) (hhs3_p6_EA1 L V) (p_hs (hhs3_p6_PAa x25519 V))))
    (l_snap L)).
  sep_apply (hhs3_p6_G_hout Tsh (kdf1 (hhs3_p6_ck V) []) (l_first L) 32 (hhs3_p6_G_hmac_len _ _)).
  sep_apply (hhs3_p6_G_hout Tsh (kdf2 (hhs3_p6_ck V) []) (l_second L) 32 (hhs3_p6_G_hmac_len _ _)).
  entailer!.
Qed.

End Seg.
