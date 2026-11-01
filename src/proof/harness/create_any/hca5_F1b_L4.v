(* law create_any: segment F1b, piece L4 (hca5_F1b_defs.v): from hca5_F1b_S4 through BODY4 (the success path),
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
Require WgNoise.harness.x_create_any.code.

#[local] Existing Instance W_create_any.
Local Open Scope logic.

(* the piece with the sequential post (abbreviate_semax makes the post normal_ret_assert); the previous piece
   uses it *)
Lemma hca5_F1b_L4_res x25519 aead_enc H S before rr :
  Int.eq (hs_state H) HS_CONSUMED_INITIATION = true ->
  is_zero (hca5_F1b_E x25519 rr) = false ->
  dh_ok x25519 (hca5_F1b_eph rr) (hs_reph H) = true ->
  dh_ok x25519 (hca5_F1b_eph rr) (hs_rstatic H) = true ->
  hca5_F1b_res x25519 aead_enc H S before rr =
  (true,
   hca3_put (hca3_put (hca5_F1b_exp1 x25519 H before rr) 44
       (aead_enc (kdf3 (kdf1 (hca5_F1b_ck2 x25519 H rr) (hca5_F1b_dh2 x25519 H rr)) (hs_psk H)) 0
          (mix_hash (hca5_F1b_h1 x25519 H rr) (kdf2 (kdf1 (hca5_F1b_ck2 x25519 H rr) (hca5_F1b_dh2 x25519 H rr)) (hs_psk H))) []))
     4 (le32 (s_u32 S)),
   hs_set_state
     (hs_set_ckh (hca5_F1b_x2 x25519 H rr)
        (kdf1 (kdf1 (hca5_F1b_ck2 x25519 H rr) (hca5_F1b_dh2 x25519 H rr)) (hs_psk H))
        (mix_hash (mix_hash (hca5_F1b_h1 x25519 H rr) (kdf2 (kdf1 (hca5_F1b_ck2 x25519 H rr) (hca5_F1b_dh2 x25519 H rr)) (hs_psk H)))
           (aead_enc (kdf3 (kdf1 (hca5_F1b_ck2 x25519 H rr) (hca5_F1b_dh2 x25519 H rr)) (hs_psk H)) 0
              (mix_hash (hca5_F1b_h1 x25519 H rr) (kdf2 (kdf1 (hca5_F1b_ck2 x25519 H rr) (hca5_F1b_dh2 x25519 H rr)) (hs_psk H))) [])))
     HS_CREATED_RESPONSE).
Proof.
  intros CI EZ D1 D2. unfold hca5_F1b_E, hca5_F1b_eph in *.
  unfold hca5_F1b_res, hca3_resp_exp. cbv zeta. rewrite CI, EZ, D1, D2. cbn [negb]. reflexivity.
Qed.

Lemma hca5_F1b_L4_x3 H ck h st :
  hs_eph (hs_set_state (hs_set_ckh H ck h) st) = hs_eph H /\
  hs_hash (hs_set_state (hs_set_ckh H ck h) st) = h /\
  hs_ck (hs_set_state (hs_set_ckh H ck h) st) = ck /\
  hs_state (hs_set_state (hs_set_ckh H ck h) st) = st.
Proof. repeat split. Qed.

Lemma hca5_F1b_L4n {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec (gv: globals) (L: hca5_loc)
    (m rv kv r0: val) (Fr: mpred) (H: handshake) (S: shim) (before rr: list byte) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hca5_F1b_facts x25519 aead_enc L H S before rr ->
  is_zero (hca5_F1b_E x25519 rr) = false ->
  dh_ok x25519 (hca5_F1b_eph rr) (hs_reph H) = true ->
  dh_ok x25519 (hca5_F1b_eph rr) (hs_rstatic H) = true ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_F1b_S4 x25519 gv L m rv kv r0 Fr H S before rr)
    hca5_F1b_BODY4
    (normal_ret_assert (hca5_F1b_fin gv L m rv kv r0 Fr H S (hca5_F1b_res x25519 aead_enc H S before rr))).
Proof.
  intros HH HF EZ D1 D2.
  pose proof HF as (Hx & Haead & Hok & Lrr & Ls & Lbef & CI & FCx & FCs & FCst).
  pose proof Hok as (Leph & Lrs & Lreph & Lss & Lpsk & Lhash & Lck & Lts0).
  subst rr.
  unfold hca5_F1b_S4, hca5_F1b_Q, hca5_Delta, hca5_F1b_BODY4, hca5_F1b_xs, hca5_F1b_ss.
  simplify_func_tycontext. abbreviate_semax.
  unfold hca5_lvars, wg_consts; cbn [app]. Intros.
  set (ck2 := hca5_F1b_ck2 x25519 H (s_log S)) in *. set (h1 := hca5_F1b_h1 x25519 H (s_log S)) in *.
  set (dh2 := hca5_F1b_dh2 x25519 H (s_log S)) in *. set (x2 := hca5_F1b_x2 x25519 H (s_log S)) in *.
  assert (Lck2: Zlength ck2 = 32) by apply hca5_F1b_kdf1_len.
  assert (Lh1: Zlength h1 = 32) by apply hca5_F1b_mix_hash_len.
  assert (Ldh2: Zlength dh2 = 32) by apply Hx.
  rewrite <- (hca5_F1b_hin Tsh dh2 (l_dh L)) by lia.
  forward_call (gv, Tsh, l_st L, ck2, h1, Tsh, l_dh L, dh2).
  all: try (entailer!; simpl; rewrite ?Ldh2; normalize).
  set (ck3 := kdf1 ck2 dh2).
  assert (Lck3: Zlength ck3 = 32) by apply hca5_F1b_kdf1_len.
  forward_call (gv, Tsh, l_st L, ck3, h1, Tsh, l_key L, Tsh, offset_val 176 (l_s L), hs_psk H).
  all: try (entailer!; simpl; normalize).
  set (ck4 := kdf1 ck3 (hs_psk H)). set (h2 := mix_hash h1 (kdf2 ck3 (hs_psk H))). set (key := kdf3 ck3 (hs_psk H)).
  assert (Lck4: Zlength ck4 = 32) by apply hca5_F1b_kdf1_len.
  assert (Lh2: Zlength h2 = 32) by apply hca5_F1b_mix_hash_len.
  assert (Lkey: Zlength key = 32) by apply hca5_F1b_kdf3_len.
  set (exp1 := hca5_F1b_exp1 x25519 H before (s_log S)) in *.
  assert (Lexp1: Zlength exp1 = 92).
  { unfold exp1, hca5_F1b_exp1, hca5_F1b_exp0.
    assert (A0: Zlength (hca3_put before 0 (le32 (Int.repr 2))) = 92)
      by (rewrite hca5_F1b_put_len; rewrite ?hca5_F1b_le32_len; lia).
    assert (A1: Zlength (hca3_put (hca3_put before 0 (le32 (Int.repr 2))) 8 (le32 (hs_rindex H))) = 92)
      by (rewrite hca5_F1b_put_len; rewrite ?hca5_F1b_le32_len; lia).
    rewrite hca5_F1b_put_len; unfold hca5_F1b_E; rewrite ?Hx; lia. }
  sep_apply (hca5_F1b_split Tsh exp1 44 16 (l_exp1 L)); try lia.
  assert (Hnil: hin Tsh (@nil byte) (l_nothing L) = emp) by (unfold hin; rewrite if_true; auto).
  rewrite <- (emp_sepcon (hout Tsh 16 (offset_val 44 (l_exp1 L)))). rewrite <- Hnil.
  replace (hout Tsh 16 (offset_val 44 (l_exp1 L))) with (hout Tsh (Zlength (@nil byte) + 16) (offset_val 44 (l_exp1 L)))
    by reflexivity.
  forward_call (gv, Tsh, l_st L, ck4, h2, Tsh, offset_val 44 (l_exp1 L), Tsh, l_nothing L, @nil byte, Tsh, l_key L, key).
  all: try (entailer!; simpl; normalize).
  all: try (rewrite Zlength_nil; rep_lia).
  set (encn := aead_enc key 0 h2 []).
  set (h3 := mix_hash h2 encn).
  assert (Lenc: Zlength encn = 16) by (unfold encn; rewrite Haead; reflexivity).
  assert (Lh3: Zlength h3 = 32) by apply hca5_F1b_mix_hash_len.
  replace (hca5_F1b_hole Tsh exp1 44 16 (l_exp1 L)) with (hca5_F1b_hole Tsh exp1 44 (Zlength encn) (l_exp1 L))
    by (rewrite Lenc; reflexivity).
  sep_apply (hca5_F1b_merge Tsh exp1 44 encn (l_exp1 L)).
  set (exp2 := hca3_put exp1 44 encn).
  assert (Lexp2: Zlength exp2 = 92) by (unfold exp2; rewrite hca5_F1b_put_len; lia).
  rewrite (hca5_F1b_st_split Tsh ck4 h3 (l_st L) FCst Lck4 Lh3).
  assert (E1: Zlength (hs_ck x2) = Zlength ck4).
  { unfold x2, hca5_F1b_x2. cbn [hs_set_ckh hs_ck]. rewrite Lck4. apply hca5_F1b_kdf1_len. }
  sep_apply (hca5_F1b_hout Tsh (hs_ck x2) (Zlength ck4) (offset_val 240 (l_x L)) E1).
  forward_call (Tsh, offset_val 240 (l_x L), Tsh, offset_val 0 (l_st L), ck4).
  all: try (entailer!; simpl; rewrite ?Lck4; normalize).
  assert (E2: Zlength (hs_hash x2) = Zlength h3).
  { unfold x2, hca5_F1b_x2. cbn [hs_set_ckh hs_hash]. rewrite Lh3. apply hca5_F1b_mix_hash_len. }
  sep_apply (hca5_F1b_hout Tsh (hs_hash x2) (Zlength h3) (offset_val 208 (l_x L)) E2).
  forward_call (Tsh, offset_val 208 (l_x L), Tsh, offset_val 32 (l_st L), h3).
  all: try (entailer!; simpl; rewrite ?Lh3; normalize).
  forward.
  forward.
  sep_apply (hca5_F1b_split Tsh exp2 4 4 (l_exp1 L)); try lia.
  forward_call (Tsh, offset_val 4 (l_exp1 L), s_u32 S).
  { cancel. }
  replace (hca5_F1b_hole Tsh exp2 4 4 (l_exp1 L)) with (hca5_F1b_hole Tsh exp2 4 (Zlength (le32 (s_u32 S))) (l_exp1 L))
    by (rewrite hca5_F1b_le32_len; reflexivity).
  sep_apply (hca5_F1b_merge Tsh exp2 4 (le32 (s_u32 S)) (l_exp1 L)).
  forward.
  rewrite (hca5_F1b_L4_res x25519 aead_enc H S before (s_log S) CI EZ D1 D2).
  change (hca5_F1b_ck2 x25519 H (s_log S)) with ck2. change (hca5_F1b_h1 x25519 H (s_log S)) with h1.
  change (hca5_F1b_dh2 x25519 H (s_log S)) with dh2. change (hca5_F1b_x2 x25519 H (s_log S)) with x2.
  change (kdf1 ck2 dh2) with ck3. change (kdf1 ck3 (hs_psk H)) with ck4.
  change (mix_hash h1 (kdf2 ck3 (hs_psk H))) with h2. change (kdf3 ck3 (hs_psk H)) with key.
  change (aead_enc key 0 h2 []) with encn. change (mix_hash h2 encn) with h3.
  change (hca5_F1b_exp1 x25519 H before (s_log S)) with exp1. change (hca3_put exp1 44 encn) with exp2.
  unfold hca5_F1b_fin, hca5_F1b_Q, hca5_F1b_xs, hca5_F1b_ss, hca5_lvars. cbn [fst snd app].
  destruct (hca5_F1b_L4_x3 x2 ck4 h3 HS_CREATED_RESPONSE) as (C1 & C2 & C3 & C4). rewrite C1, C2, C3, C4.
  unfold HS_CREATED_RESPONSE, wg_consts.
  sep_apply (derives_refl' _ _ (eq_sym (hca5_F1b_st_split Tsh ck4 h3 (l_st L) FCst Lck4 Lh3))).
  sep_apply (data_at_data_at_ Tsh t_mstate (mstate_val ck4 h3) (l_st L)).
  sep_apply (hca5_F1b_hout Tsh key 32 (l_key L) Lkey).
  rewrite (hca5_F1b_hin Tsh dh2 (l_dh L)) by lia.
  sep_apply (hca5_F1b_hout Tsh dh2 32 (l_dh L) Ldh2).
  sep_apply (hca5_F1b_hout Tsh (hca5_F1b_eph (s_log S)) 32 (l_eph L) (hca5_F1b_clamp_len _ Lrr)).
  sep_apply (hca5_F1b_hout Tsh (hca5_F1b_E x25519 (s_log S)) 32 (l_E L) (Hx _ _)).
  entailer!.
Qed.

Lemma hca5_F1b_L4 {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec (gv: globals) (L: hca5_loc)
    (m rv kv r0: val) (Fr: mpred) (H: handshake) (S: shim) (before rr: list byte) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hca5_F1b_facts x25519 aead_enc L H S before rr ->
  is_zero (hca5_F1b_E x25519 rr) = false ->
  dh_ok x25519 (hca5_F1b_eph rr) (hs_reph H) = true ->
  dh_ok x25519 (hca5_F1b_eph rr) (hs_rstatic H) = true ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_F1b_S4 x25519 gv L m rv kv r0 Fr H S before rr)
    hca5_F1b_BODY4
    (overridePost (hca5_F1b_fin gv L m rv kv r0 Fr H S (hca5_F1b_res x25519 aead_enc H S before rr))
       (hca5_R gv)).
Proof.
  intros. apply sequential'. eapply hca5_F1b_L4n; eauto.
Qed.
