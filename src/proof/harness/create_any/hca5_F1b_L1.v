(* law create_any: segment F1b, piece L1 (hca5_F1b_defs.v): from hca5_F1b_S1 (s.state = CONSUMED_INITIATION) through THEN (incl. its if on E; uses hca5_F1b_L2 for BODY2),
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
Require Import WgNoise.proof.harness.create_any.hca5_F1b_L2.
Require WgNoise.harness.x_create_any.code.

#[local] Existing Instance W_create_any.
Local Open Scope logic.

(* the piece with the sequential post (abbreviate_semax makes the post normal_ret_assert); the previous piece
   uses it *)
Lemma hca5_F1b_L1_res x25519 aead_enc H S before rr :
  Int.eq (hs_state H) HS_CONSUMED_INITIATION = true ->
  is_zero (hca5_F1b_E x25519 rr) = true ->
  hca5_F1b_res x25519 aead_enc H S before rr = (false, hca5_F1b_exp1 x25519 H before rr, hca5_F1b_x0 H rr).
Proof.
  intros CI EZ. unfold hca5_F1b_E, hca5_F1b_eph in *.
  unfold hca5_F1b_res, hca3_resp_exp. cbv zeta. rewrite CI, EZ. cbn [negb]. reflexivity.
Qed.
Lemma hca5_F1b_L1_eph rr : clamp rr = hca5_F1b_eph rr.
Proof. reflexivity. Qed.
Lemma hca5_F1b_L1_E x25519 rr : x25519 (hca5_F1b_eph rr) basepoint9 = hca5_F1b_E x25519 rr.
Proof. reflexivity. Qed.
Lemma hca5_F1b_L1_exp0 H before :
  hca3_put (hca3_put before 0 (le32 (Int.repr 2))) 8 (le32 (hs_rindex H)) = hca5_F1b_exp0 H before.
Proof. reflexivity. Qed.
Lemma hca5_F1b_L1_exp1 x25519 H before rr :
  hca3_put (hca5_F1b_exp0 H before) 12 (hca5_F1b_E x25519 rr) = hca5_F1b_exp1 x25519 H before rr.
Proof. reflexivity. Qed.

Lemma hca5_F1b_L1n {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec (gv: globals) (L: hca5_loc)
    (m rv kv r0: val) (Fr: mpred) (H: handshake) (S: shim) (before rr: list byte) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hca5_F1b_facts x25519 aead_enc L H S before rr ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_F1b_S1 gv L m rv kv r0 Fr H S before)
    hca5_F1b_THEN
    (normal_ret_assert (hca5_F1b_fin gv L m rv kv r0 Fr H S (hca5_F1b_res x25519 aead_enc H S before rr))).
Proof.
  intros HH HF.
  pose proof HF as (Hx & Haead & Hok & Lrr & Ls & Lbef & CI & FCx & FCs & FCst).
  pose proof Hok as (Leph & Lrs & Lreph & Lss & Lpsk & Lhash & Lck & Lts0).
  subst rr.
  unfold hca5_F1b_S1, hca5_F1b_Q, hca5_Delta, hca5_F1b_THEN, hca5_F1b_xs, hca5_F1b_ss.
  simplify_func_tycontext. abbreviate_semax.
  unfold hca5_lvars, wg_consts; cbn [app]. rewrite hca5_F1b_consts. Intros.
  assert (Leph0: Zlength (hca5_F1b_eph (s_log S)) = 32) by (apply hca5_F1b_clamp_len; auto).
  assert (LE: Zlength (hca5_F1b_E x25519 (s_log S)) = 32) by apply Hx.
  sep_apply (hca5_F1b_split Tsh before 0 4 (l_exp1 L)); try lia.
  forward_call (Tsh, offset_val 0 (l_exp1 L), Int.repr 2).
  all: try (cancel; fail).
  replace (hca5_F1b_hole Tsh before 0 4 (l_exp1 L)) with (hca5_F1b_hole Tsh before 0 (Zlength (le32 (Int.repr 2))) (l_exp1 L))
    by (rewrite hca5_F1b_le32_len; reflexivity).
  sep_apply (hca5_F1b_merge Tsh before 0 (le32 (Int.repr 2)) (l_exp1 L)).
  forward.
  assert (Lb0: Zlength (hca3_put before 0 (le32 (Int.repr 2))) = 92) by (rewrite hca5_F1b_put_len; rewrite ?hca5_F1b_le32_len; lia).
  sep_apply (hca5_F1b_split Tsh (hca3_put before 0 (le32 (Int.repr 2))) 8 4 (l_exp1 L)); try lia.
  forward_call (Tsh, offset_val 8 (l_exp1 L), hs_rindex H).
  all: try (cancel; fail).
  replace (hca5_F1b_hole Tsh (hca3_put before 0 (le32 (Int.repr 2))) 8 4 (l_exp1 L))
    with (hca5_F1b_hole Tsh (hca3_put before 0 (le32 (Int.repr 2))) 8 (Zlength (le32 (hs_rindex H))) (l_exp1 L))
    by (rewrite hca5_F1b_le32_len; reflexivity).
  sep_apply (hca5_F1b_merge Tsh (hca3_put before 0 (le32 (Int.repr 2))) 8 (le32 (hs_rindex H)) (l_exp1 L)).
  rewrite hca5_F1b_L1_exp0.
  rewrite (hca5_F1b_st_split_ Tsh (l_st L) FCst).
  replace (hout Tsh 32 (offset_val 0 (l_st L))) with (hout Tsh (Zlength (hs_ck H)) (offset_val 0 (l_st L)))
    by (rewrite Lck; reflexivity).
  forward_call (Tsh, offset_val 0 (l_st L), Tsh, offset_val 240 (l_s L), hs_ck H).
  all: try (entailer!; simpl; rewrite ?Lck; normalize).
  replace (hout Tsh 32 (offset_val 32 (l_st L))) with (hout Tsh (Zlength (hs_hash H)) (offset_val 32 (l_st L)))
    by (rewrite Lhash; reflexivity).
  forward_call (Tsh, offset_val 32 (l_st L), Tsh, offset_val 208 (l_s L), hs_hash H).
  all: try (entailer!; simpl; rewrite ?Lhash; normalize).
  replace (hout Tsh 32 (l_eph L)) with (hout Tsh (Zlength (s_log S)) (l_eph L)) by (rewrite Lrr; reflexivity).
  forward_call (Tsh, l_eph L, Ews, gv HC._wg_shim_random_log, s_log S).
  all: try (entailer!; simpl; rewrite ?Lrr; normalize).
  all: try (rewrite ?Lrr; rep_lia).
  forward_call (Tsh, l_eph L, (s_log S)).
  rewrite hca5_F1b_L1_eph.
  assert (E4: Zlength (hs_eph H) = Zlength (hca5_F1b_eph (s_log S))) by lia.
  sep_apply (hca5_F1b_hout Tsh (hs_eph H) (Zlength (hca5_F1b_eph (s_log S))) (offset_val 48 (l_x L)) E4).
  forward_call (Tsh, offset_val 48 (l_x L), Tsh, l_eph L, hca5_F1b_eph (s_log S)).
  all: try (entailer!; simpl; rewrite ?Leph0; normalize).
  forward_call (Tsh, l_E L, Tsh, l_eph L, hca5_F1b_eph (s_log S), Ers, gv HC._x_create_any__M_BASEPOINT, basepoint9).
  rewrite hca5_F1b_L1_E.
  assert (Lb1: Zlength (hca5_F1b_exp0 H before) = 92)
    by (unfold hca5_F1b_exp0; rewrite !hca5_F1b_put_len; rewrite ?hca5_F1b_le32_len; try lia).
  sep_apply (hca5_F1b_split Tsh (hca5_F1b_exp0 H before) 12 32 (l_exp1 L)); try lia.
  replace (hout Tsh 32 (offset_val 12 (l_exp1 L))) with (hout Tsh (Zlength (hca5_F1b_E x25519 (s_log S))) (offset_val 12 (l_exp1 L)))
    by (rewrite LE; reflexivity).
  forward_call (Tsh, offset_val 12 (l_exp1 L), Tsh, l_E L, hca5_F1b_E x25519 (s_log S)).
  all: try (entailer!; simpl; rewrite ?LE; normalize).
  replace (hca5_F1b_hole Tsh (hca5_F1b_exp0 H before) 12 32 (l_exp1 L))
    with (hca5_F1b_hole Tsh (hca5_F1b_exp0 H before) 12 (Zlength (hca5_F1b_E x25519 (s_log S))) (l_exp1 L))
    by (rewrite LE; reflexivity).
  sep_apply (hca5_F1b_merge Tsh (hca5_F1b_exp0 H before) 12 (hca5_F1b_E x25519 (s_log S)) (l_exp1 L)).
  rewrite hca5_F1b_L1_exp1.
  forward_call (Tsh, l_E L, hca5_F1b_E x25519 (s_log S)).
  all: try (entailer!; simpl; rewrite ?LE; normalize).
  destruct (is_zero (hca5_F1b_E x25519 (s_log S))) eqn:EZ.
  - forward_if.
    { exfalso; first [ match goal with Hn: Int.one = Int.zero |- _ => apply Int.one_not_zero; exact Hn end | match goal with Hn: _ = Int.zero |- _ => apply Int.one_not_zero; exact Hn end | match goal with Hn: _ <> _ |- _ => apply Hn; reflexivity end ]. }
    forward.
    rewrite (hca5_F1b_L1_res x25519 aead_enc H S before (s_log S) CI EZ).
    unfold hca5_F1b_fin, hca5_F1b_Q, hca5_F1b_xs, hca5_F1b_ss, hca5_lvars. cbn [fst snd app].
    destruct (hca5_F1b_L2_x0 H (s_log S)) as (C1 & C2 & C3 & C4). rewrite C1, C2, C3, C4.
    unfold wg_consts. rewrite hca5_F1b_consts.
    sep_apply (derives_refl' _ _ (eq_sym (hca5_F1b_st_split Tsh (hs_ck H) (hs_hash H) (l_st L) FCst Lck Lhash))).
    sep_apply (data_at_data_at_ Tsh t_mstate (mstate_val (hs_ck H) (hs_hash H)) (l_st L)).
    sep_apply (hca5_F1b_hout Tsh (hca5_F1b_eph (s_log S)) 32 (l_eph L) Leph0).
    sep_apply (hca5_F1b_hout Tsh (hca5_F1b_E x25519 (s_log S)) 32 (l_E L) LE).
    entailer!.
  - forward_if.
    2: { exfalso; first [ match goal with Hn: Int.one = Int.zero |- _ => apply Int.one_not_zero; exact Hn end | match goal with Hn: _ = Int.zero |- _ => apply Int.one_not_zero; exact Hn end | match goal with Hn: _ <> _ |- _ => apply Hn; reflexivity end ]. }
    unfold POSTCONDITION, abbreviate.
    assert (HD: Delta = hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
      by (unfold Delta, Delta_specs, abbreviate; reflexivity).
    rewrite HD; clear HD.
    eapply semax_pre; [| apply (hca5_F1b_L2n x25519 aead_enc aead_dec xaead_enc xaead_dec gv L m rv kv r0 Fr H S
                               before (s_log S) HH HF EZ)].
    unfold hca5_F1b_S2, hca5_F1b_Q, hca5_F1b_xs, hca5_F1b_ss, hca5_lvars. cbn [app].
    destruct (hca5_F1b_L2_x0 H (s_log S)) as (C1 & C2 & C3 & C4). rewrite C1, C2, C3, C4.
    unfold wg_consts. rewrite hca5_F1b_consts.
    rewrite (hca5_F1b_st_split Tsh (hs_ck H) (hs_hash H) (l_st L) FCst Lck Lhash).
    entailer!.
Qed.

Lemma hca5_F1b_L1 {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec (gv: globals) (L: hca5_loc)
    (m rv kv r0: val) (Fr: mpred) (H: handshake) (S: shim) (before rr: list byte) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hca5_F1b_facts x25519 aead_enc L H S before rr ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_F1b_S1 gv L m rv kv r0 Fr H S before)
    hca5_F1b_THEN
    (overridePost (hca5_F1b_fin gv L m rv kv r0 Fr H S (hca5_F1b_res x25519 aead_enc H S before rr))
       (hca5_R gv)).
Proof.
  intros. apply sequential'. eapply hca5_F1b_L1n; eauto.
Qed.
