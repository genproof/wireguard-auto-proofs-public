(* law create_any: segment F1b, piece L2 (hca5_F1b_defs.v): from hca5_F1b_S2 through BODY2 (incl. its if; uses hca5_F1b_L3 for BODY3),
   to the expectation hca5_F1b_res. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.create_any.hca3_model.
Require Import WgNoise.proof.harness.create_any.hca5_spec.
Require Import WgNoise.proof.harness.create_any.hca5_defs.
Require Import WgNoise.proof.harness.create_any.hca5_conv.
Require Import WgNoise.proof.harness.create_any.hca5_fdefs.
Require Import WgNoise.proof.harness.create_any.hca5_F1b_defs.
Require Import WgNoise.proof.harness.create_any.hca5_F1b_L3.
Require WgNoise.harness.x_create_any.code.

#[local] Existing Instance W_create_any.
Local Open Scope logic.

(* the piece with the sequential post (abbreviate_semax makes the post normal_ret_assert); the previous piece
   uses it *)
Lemma hca5_F1b_L2_res x25519 aead_enc H S before rr :
  Int.eq (hs_state H) HS_CONSUMED_INITIATION = true ->
  is_zero (hca5_F1b_E x25519 rr) = false ->
  dh_ok x25519 (hca5_F1b_eph rr) (hs_reph H) = false ->
  hca5_F1b_res x25519 aead_enc H S before rr = (false, hca5_F1b_exp1 x25519 H before rr, hca5_F1b_x1 x25519 H rr).
Proof.
  intros CI EZ D1. unfold hca5_F1b_E, hca5_F1b_eph in *.
  unfold hca5_F1b_res, hca3_resp_exp. cbv zeta. rewrite CI, EZ, D1. cbn [negb]. reflexivity.
Qed.
Lemma hca5_F1b_L2_x0 H rr :
  hs_eph (hca5_F1b_x0 H rr) = hca5_F1b_eph rr /\ hs_hash (hca5_F1b_x0 H rr) = hs_hash H /\
  hs_ck (hca5_F1b_x0 H rr) = hs_ck H /\ hs_state (hca5_F1b_x0 H rr) = hs_state H.
Proof. split; [reflexivity | split; [reflexivity | split; reflexivity]]. Qed.
Lemma hca5_F1b_L2_x1 x25519 H rr :
  hs_eph (hca5_F1b_x1 x25519 H rr) = hca5_F1b_eph rr /\
  hs_hash (hca5_F1b_x1 x25519 H rr) = hca5_F1b_h1 x25519 H rr /\
  hs_ck (hca5_F1b_x1 x25519 H rr) = hca5_F1b_ck1 x25519 H rr /\
  hs_state (hca5_F1b_x1 x25519 H rr) = hs_state H.
Proof. split; [reflexivity | split; [reflexivity | split; reflexivity]]. Qed.
Lemma hca5_F1b_L2_h1 x25519 H rr : mix_hash (hs_hash H) (hca5_F1b_E x25519 rr) = hca5_F1b_h1 x25519 H rr.
Proof. reflexivity. Qed.
Lemma hca5_F1b_L2_ck1 x25519 H rr : kdf1 (hs_ck H) (hca5_F1b_E x25519 rr) = hca5_F1b_ck1 x25519 H rr.
Proof. reflexivity. Qed.
Lemma hca5_F1b_L2_dh1 x25519 H rr : x25519 (hca5_F1b_eph rr) (hs_reph H) = hca5_F1b_dh1 x25519 H rr.
Proof. reflexivity. Qed.

Lemma hca5_F1b_L2n {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec (gv: globals) (L: hca5_loc)
    (m rv kv r0: val) (Fr: mpred) (H: handshake) (S: shim) (before rr: list byte) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hca5_F1b_facts x25519 aead_enc L H S before rr ->
  is_zero (hca5_F1b_E x25519 rr) = false ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_F1b_S2 x25519 gv L m rv kv r0 Fr H S before rr)
    hca5_F1b_BODY2
    (normal_ret_assert (hca5_F1b_fin gv L m rv kv r0 Fr H S (hca5_F1b_res x25519 aead_enc H S before rr))).
Proof.
  intros HH HF EZ.
  pose proof HF as (Hx & Haead & Hok & Lrr & Ls & Lbef & CI & FCx & FCs & FCst).
  pose proof Hok as (Leph & Lrs & Lreph & Lss & Lpsk & Lhash & Lck & Lts0).
  unfold hca5_F1b_S2, hca5_F1b_Q, hca5_Delta, hca5_F1b_BODY2, hca5_F1b_xs, hca5_F1b_ss.
  simplify_func_tycontext. abbreviate_semax.
  unfold hca5_lvars, wg_consts; cbn [app]. Intros.
  destruct (hca5_F1b_L2_x0 H rr) as (B1 & B2 & B3 & B4). rewrite B1, B2, B3, B4.
  assert (Lck1: Zlength (hca5_F1b_ck1 x25519 H rr) = 32) by apply hca5_F1b_kdf1_len.
  assert (Lh1: Zlength (hca5_F1b_h1 x25519 H rr) = 32) by apply hca5_F1b_mix_hash_len.
  assert (Ldh1: Zlength (hca5_F1b_dh1 x25519 H rr) = 32) by apply Hx.
  assert (LE: Zlength (hca5_F1b_E x25519 rr) = 32) by apply Hx.
  assert (Leph0: Zlength (hca5_F1b_eph rr) = 32) by (apply hca5_F1b_clamp_len; auto).
  rewrite <- (hca5_F1b_hin Tsh (hca5_F1b_E x25519 rr) (l_E L)) by lia.
  forward_call (gv, Tsh, l_st L, hs_ck H, hs_hash H, Tsh, l_E L, hca5_F1b_E x25519 rr).
  all: try (entailer!; simpl; rewrite ?LE; normalize).
  rewrite hca5_F1b_L2_h1.
  forward_call (gv, Tsh, l_st L, hs_ck H, hca5_F1b_h1 x25519 H rr, Tsh, l_E L, hca5_F1b_E x25519 rr).
  all: try (entailer!; simpl; rewrite ?LE; normalize).
  rewrite hca5_F1b_L2_ck1.
  rewrite (hca5_F1b_st_split Tsh (hca5_F1b_ck1 x25519 H rr) (hca5_F1b_h1 x25519 H rr) (l_st L) FCst Lck1 Lh1).
  assert (E1: Zlength (hs_ck H) = Zlength (hca5_F1b_ck1 x25519 H rr)) by lia.
  sep_apply (hca5_F1b_hout Tsh (hs_ck H) (Zlength (hca5_F1b_ck1 x25519 H rr)) (offset_val 240 (l_x L)) E1).
  forward_call (Tsh, offset_val 240 (l_x L), Tsh, offset_val 0 (l_st L), hca5_F1b_ck1 x25519 H rr).
  all: try (entailer!; simpl; rewrite ?Lck1; normalize).
  assert (E2: Zlength (hs_hash H) = Zlength (hca5_F1b_h1 x25519 H rr)) by lia.
  sep_apply (hca5_F1b_hout Tsh (hs_hash H) (Zlength (hca5_F1b_h1 x25519 H rr)) (offset_val 208 (l_x L)) E2).
  forward_call (Tsh, offset_val 208 (l_x L), Tsh, offset_val 32 (l_st L), hca5_F1b_h1 x25519 H rr).
  all: try (entailer!; simpl; rewrite ?Lh1; normalize).
  forward_call (Tsh, l_dh L, Tsh, l_eph L, hca5_F1b_eph rr, Tsh, offset_val 112 (l_s L), hs_reph H).
  rewrite hca5_F1b_L2_dh1.
  rewrite (hca5_F1b_hin Tsh (hca5_F1b_E x25519 rr) (l_E L)) by lia.
  destruct (dh_ok x25519 (hca5_F1b_eph rr) (hs_reph H)) eqn:D1.
  - forward_if.
    2: { exfalso; first [ match goal with Hn: Int.one = Int.zero |- _ => apply Int.one_not_zero; exact Hn end | match goal with Hn: _ = Int.zero |- _ => apply Int.one_not_zero; exact Hn end | match goal with Hn: _ <> _ |- _ => apply Hn; reflexivity end ]. }
    unfold POSTCONDITION, abbreviate.
    assert (HD: Delta = hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
      by (unfold Delta, Delta_specs, abbreviate; reflexivity).
    rewrite HD; clear HD.
    eapply semax_pre; [| apply (hca5_F1b_L3n x25519 aead_enc aead_dec xaead_enc xaead_dec gv L m rv kv r0 Fr H S
                               before rr HH HF EZ D1)].
    unfold hca5_F1b_S3, hca5_F1b_Q, hca5_F1b_xs, hca5_F1b_ss, hca5_lvars. cbn [app].
    destruct (hca5_F1b_L2_x1 x25519 H rr) as (C1 & C2 & C3 & C4). rewrite C1, C2, C3, C4.
    unfold wg_consts.
    rewrite (hca5_F1b_st_split Tsh (hca5_F1b_ck1 x25519 H rr) (hca5_F1b_h1 x25519 H rr) (l_st L) FCst Lck1 Lh1).
    entailer!.
  - forward_if.
    { exfalso; first [ match goal with Hn: Int.one = Int.zero |- _ => apply Int.one_not_zero; exact Hn end | match goal with Hn: _ = Int.zero |- _ => apply Int.one_not_zero; exact Hn end | match goal with Hn: _ <> _ |- _ => apply Hn; reflexivity end ]. }
    forward.
    rewrite (hca5_F1b_L2_res x25519 aead_enc H S before rr CI EZ D1).
    unfold hca5_F1b_fin, hca5_F1b_Q, hca5_F1b_xs, hca5_F1b_ss, hca5_lvars. cbn [fst snd app].
    destruct (hca5_F1b_L2_x1 x25519 H rr) as (C1 & C2 & C3 & C4). rewrite C1, C2, C3, C4.
    unfold wg_consts.
    sep_apply (derives_refl' _ _ (eq_sym (hca5_F1b_st_split Tsh (hca5_F1b_ck1 x25519 H rr) (hca5_F1b_h1 x25519 H rr) (l_st L) FCst Lck1 Lh1))).
    sep_apply (data_at_data_at_ Tsh t_mstate (mstate_val (hca5_F1b_ck1 x25519 H rr) (hca5_F1b_h1 x25519 H rr)) (l_st L)).
    sep_apply (hca5_F1b_hout Tsh (hca5_F1b_dh1 x25519 H rr) 32 (l_dh L) Ldh1).
    sep_apply (hca5_F1b_hout Tsh (hca5_F1b_eph rr) 32 (l_eph L) Leph0).
    sep_apply (hca5_F1b_hout Tsh (hca5_F1b_E x25519 rr) 32 (l_E L) LE).
    entailer!.
Qed.

Lemma hca5_F1b_L2 {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec (gv: globals) (L: hca5_loc)
    (m rv kv r0: val) (Fr: mpred) (H: handshake) (S: shim) (before rr: list byte) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hca5_F1b_facts x25519 aead_enc L H S before rr ->
  is_zero (hca5_F1b_E x25519 rr) = false ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_F1b_S2 x25519 gv L m rv kv r0 Fr H S before rr)
    hca5_F1b_BODY2
    (overridePost (hca5_F1b_fin gv L m rv kv r0 Fr H S (hca5_F1b_res x25519 aead_enc H S before rr))
       (hca5_R gv)).
Proof.
  intros. apply sequential'. eapply hca5_F1b_L2n; eauto.
Qed.
