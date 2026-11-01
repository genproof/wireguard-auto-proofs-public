(* (port of v1 hca3_F0b_L3.v), law create_any: segment F0b, piece L3 (hca5_F0b_defs.v): from hca5_F0b_S3 through BODY3 (m_mix_key(dh), m_encrypt_and_hash(exp+40, static public), 2 copies, t'12 = bytes_zero(s.pss); if (!t'12) BODY4), given BODY4 as a hypothesis.
   The ends are hca5_F0b_fin of the expectation hca5_F0b_res.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
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
Require Import WgNoise.proof.harness.create_any.hca5_fdefs.
Require Import WgNoise.proof.harness.create_any.hca5_F0b_defs.
Require Import WgNoise.proof.harness.create_any.hca5_F0b_lib.
Require WgNoise.harness.x_create_any.code.

#[local] Existing Instance W_create_any.
Local Open Scope logic.

Lemma hca5_F0b_L3_hash_len m : Zlength (HASH m) = 32.
Proof. unfold HASH, model.blake2s, model.b2s_digest_stream, model.b2s_out. rewrite Zlength_map. reflexivity. Qed.
Lemma hca5_F0b_L3_kdf1_len a b : Zlength (kdf1 a b) = 32.
Proof. unfold kdf1, hmac. cbv zeta. apply hca5_F0b_L3_hash_len. Qed.
Lemma hca5_F0b_L3_kdf2_len a b : Zlength (kdf2 a b) = 32.
Proof. unfold kdf2, hmac. cbv zeta. apply hca5_F0b_L3_hash_len. Qed.
Lemma hca5_F0b_L3_mix_hash_len a b : Zlength (mix_hash a b) = 32.
Proof. unfold mix_hash. apply hca5_F0b_L3_hash_len. Qed.
Lemma hca5_F0b_L3_clamp_len r : Zlength r = 32 -> Zlength (hca5_F0b_eph r) = 32.
Proof. intros. unfold hca5_F0b_eph, clamp. rewrite !Zlength_upd_Znth. auto. Qed.

Lemma hca5_F0b_L3_exp1_len x25519 before rr :
  x25519_props x25519 -> Zlength before = 148 -> Zlength (hca5_F0b_exp1 x25519 before rr) = 148.
Proof.
  intros Hx Lb. unfold hca5_F0b_exp1, hca5_F0b_E.
  assert (L0: Zlength (hca3_put before 0 (le32 (Int.repr 1))) = 148)
    by (rewrite hca5_F0b_Zlength_put; rewrite ?hca3_Zlength_le32; lia).
  rewrite hca5_F0b_Zlength_put; rewrite ?Hx; lia.
Qed.

Lemma hca5_F0b_L3_x1_ok x25519 H rr : hs_ok H -> Zlength rr = 32 -> hs_ok (hca5_F0b_x1 x25519 H rr).
Proof.
  intros (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8) Lr.
  unfold hs_ok, hca5_F0b_x1, hca5_F0b_x0.
  cbn [hs_set_ckh hs_set_eph hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts].
  unfold hca5_F0b_h1, hca5_F0b_ck1.
  rewrite hca5_F0b_L3_mix_hash_len, hca5_F0b_L3_kdf1_len, hca5_F0b_L3_clamp_len by auto.
  repeat split; auto.
Qed.

Lemma hca5_F0b_L3_x2_ok H ck h : hs_ok H -> Zlength ck = 32 -> Zlength h = 32 -> hs_ok (hs_set_ckh H ck h).
Proof. intros (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8) Lc Lh. repeat split; auto. Qed.

Lemma hca5_F0b_L3_res x25519 aead_enc H D S before rr ts :
  is_zero (hca5_F0b_E x25519 rr) = false ->
  dh_ok x25519 (hca5_F0b_eph rr) (hs_rstatic H) = true ->
  is_zero (hs_ss H) = true ->
  hca5_F0b_res x25519 aead_enc H D S before rr ts =
  (false, hca5_F0b_exp2 x25519 aead_enc H D before rr, hca5_F0b_x2 x25519 aead_enc H D rr).
Proof.
  intros EZ DH SS. unfold hca5_F0b_E, hca5_F0b_eph in *.
  unfold hca5_F0b_res, hca3_init_exp. cbv zeta. cbn [negb].
  rewrite EZ, DH, SS. reflexivity.
Qed.

Lemma hca5_F0b_L3_sn T a E Hs : sn_hs (snap_of T a E Hs) = Hs.
Proof. reflexivity. Qed.
Lemma hca5_F0b_L3_ckh H ck h :
  hs_eph (hs_set_ckh H ck h) = hs_eph H /\ hs_rstatic (hs_set_ckh H ck h) = hs_rstatic H /\
  hs_ss (hs_set_ckh H ck h) = hs_ss H /\ hs_hash (hs_set_ckh H ck h) = h /\
  hs_ck (hs_set_ckh H ck h) = ck /\ hs_state (hs_set_ckh H ck h) = hs_state H.
Proof. repeat split. Qed.

Lemma hca5_F0b_L3_srest sh T a E H ck h p :
  hca5_F0b_srest sh (snap_of T a E (hs_set_ckh H ck h)) p = hca5_F0b_srest sh (snap_of T a E H) p.
Proof. reflexivity. Qed.

Lemma hca5_F0b_L3_st_close sh ck h p : Zlength ck = 32 -> Zlength h = 32 -> @field_compatible HCS t_mstate [] p ->
  hbytes sh ck p * hbytes sh h (offset_val 32 p) |-- @data_at_ HCS sh t_mstate p.
Proof.
  intros Lc Lh FC. eapply derives_trans; [| apply data_at_data_at_].
  rewrite (hca5_F0b_st_split sh ck h p Lc Lh). apply andp_right; [apply prop_right; auto | auto].
Qed.

(* the piece with the sequential post; the then-branch uses hca5_F0b_L4n *)
Lemma hca5_F0b_L3n {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec (gv: globals) (L: hca5_loc)
    (m rv kv rf: val) (Fr: mpred) (T: tstate) (E: entry) (H: handshake) (D: device) (S: shim) (w: list int64) (before rr ts: list byte) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hca5_F0b_facts x25519 aead_enc H D S before rr ts ->
  is_zero (hca5_F0b_E x25519 rr) = false ->
  dh_ok x25519 (hca5_F0b_eph rr) (hs_rstatic H) = true ->
  (is_zero (hs_ss H) = false ->
   semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
     (hca5_F0b_S4 x25519 aead_enc gv L m rv kv rf Fr T E H D S w before rr ts)
     hca5_F0b_BODY4
     (normal_ret_assert (hca5_F0b_fin gv L m rv kv rf Fr T E H D S w ts (hca5_F0b_res x25519 aead_enc H D S before rr ts)))) ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_F0b_S3 x25519 gv L m rv kv rf Fr T E H D S w before rr ts)
    hca5_F0b_BODY3
    (normal_ret_assert (hca5_F0b_fin gv L m rv kv rf Fr T E H D S w ts (hca5_F0b_res x25519 aead_enc H D S before rr ts))).
Proof.
  intros HH HF EZ DH HN. pose proof HF as (Hx & Haead & Hok & Lrr & Ls & Lts & Lbef & Lpub).
  unfold hca5_F0b_S3, hca5_F0b_Q, hca5_Delta, hca5_F0b_BODY3.
  simplify_func_tycontext. abbreviate_semax.
  unfold hca5_lvars; cbn [app].
  assert (Hx1: hs_ok (hca5_F0b_x1 x25519 H rr)) by (apply hca5_F0b_L3_x1_ok; auto).
  rewrite (hca5_F0b_snap_split Tsh (hca5_F0b_snap L T E H) (l_s L) Hok).
  rewrite (hca5_F0b_snap_split Tsh (hca5_F0b_snap L T E (hca5_F0b_x1 x25519 H rr)) (l_x L) Hx1).
  unfold hca5_F0b_snap; cbn [snap_of sn_hs]. rewrite (hca5_F0b_dev_split Tsh (l_wa L) D). unfold wg_consts. Intros.
  pose proof Hok as (Leph & Lrs & Lreph & Lss & Lpsk & Lhash & Lck & Lts0).
  set (x1 := hca5_F0b_x1 x25519 H rr) in *.
  pose proof Hx1 as (Xeph & Xrs & Xreph & Xss & Xpsk & Xhash & Xck & Xts).
  set (ck1 := hca5_F0b_ck1 x25519 rr) in *. set (h1 := hca5_F0b_h1 x25519 H rr) in *.
  set (dh := hca5_F0b_dh x25519 H rr) in *.
  assert (Lck1: Zlength ck1 = 32) by apply hca5_F0b_L3_kdf1_len.
  assert (Lh1: Zlength h1 = 32) by apply hca5_F0b_L3_mix_hash_len.
  assert (Ldh: Zlength dh = 32) by apply Hx.
  rewrite <- (hca5_F0b_hin Tsh dh (l_dh L)) by lia.
  forward_call (gv, Tsh, l_st L, ck1, h1, Tsh, l_key L, Tsh, l_dh L, dh).
  { entailer!. simpl. rewrite Ldh. reflexivity. }
  set (ck2 := kdf1 ck1 dh). set (key2 := kdf2 ck1 dh).
  assert (Lck2: Zlength ck2 = 32) by apply hca5_F0b_L3_kdf1_len.
  assert (Lk2: Zlength key2 = 32) by apply hca5_F0b_L3_kdf2_len.
  set (exp1 := hca5_F0b_exp1 x25519 before rr) in *.
  assert (Lexp1: Zlength exp1 = 148) by (apply hca5_F0b_L3_exp1_len; auto).
  sep_apply (hca5_F0b_open Tsh exp1 40 48 (l_exp L)); try lia. Intros.
  set (pub := id_pub (d_id D)) in *.
  rewrite <- (hca5_F0b_hin Tsh pub (offset_val 8 (l_wa L))) by lia.
  replace (hout Tsh 48 (offset_val 40 (l_exp L))) with (hout Tsh (Zlength pub + 16) (offset_val 40 (l_exp L)))
    by (rewrite Lpub; reflexivity).
  forward_call (gv, Tsh, l_st L, ck2, h1, Tsh, offset_val 40 (l_exp L), Tsh, offset_val 8 (l_wa L), pub, Tsh, l_key L, key2).
  { entailer!. simpl. rewrite Lpub, offset_offset_val. reflexivity. }
  set (encs := aead_enc key2 0 h1 pub).
  set (h2 := mix_hash h1 encs).
  assert (Le: Zlength encs = 48) by (unfold encs; rewrite Haead; lia).
  assert (Lh2: Zlength h2 = 32) by apply hca5_F0b_L3_mix_hash_len.
  replace (40 + 48) with (40 + Zlength encs) by (rewrite Le; reflexivity).
  sep_apply (hca5_F0b_close Tsh exp1 40 encs (l_exp L)); try lia.
  assert_PROP (@field_compatible HCS t_mstate [] (l_st L)) as FCst by entailer!.
  rewrite (hca5_F0b_st_split Tsh ck2 h2 (l_st L) Lck2 Lh2). Intros.
  assert (E1: Zlength (hs_ck x1) = Zlength ck2) by lia.
  sep_apply (hca5_F0b_hout Tsh (hs_ck x1) (Zlength ck2) (offset_val 240 (l_x L)) E1).
  forward_call (Tsh, offset_val 240 (l_x L), Tsh, l_st L, ck2).
  assert (E2: Zlength (hs_hash x1) = Zlength h2) by lia.
  sep_apply (hca5_F0b_hout Tsh (hs_hash x1) (Zlength h2) (offset_val 208 (l_x L)) E2).
  forward_call (Tsh, offset_val 208 (l_x L), Tsh, offset_val 32 (l_st L), h2).
  forward_call (Tsh, offset_val 144 (l_s L), hs_ss H).
  { entailer!. simpl. rewrite Lss. reflexivity. }
  destruct (is_zero (hs_ss H)) eqn:SS.
  - forward_if.
    { exfalso. match goal with Hn: Int.one = Int.zero |- _ => apply Int.one_not_zero; exact Hn end. }
    forward.
    rewrite (hca5_F0b_L3_res x25519 aead_enc H D S before rr ts EZ DH SS).
    change (hca5_F0b_exp2 x25519 aead_enc H D before rr) with (hca3_put exp1 40 encs).
    change (hca5_F0b_x2 x25519 aead_enc H D rr) with (hs_set_ckh x1 ck2 h2).
    unfold hca5_F0b_fin, hca5_F0b_Q, hca5_lvars. cbn [fst snd app].
    assert (Hx2: hs_ok (hs_set_ckh x1 ck2 h2)) by (apply hca5_F0b_L3_x2_ok; auto).
    unfold hca5_F0b_snap.
    rewrite (hca5_F0b_snap_split Tsh (snap_of T (hs_addr (l_p L)) E (hs_set_ckh x1 ck2 h2)) (l_x L) Hx2).
    rewrite (hca5_F0b_snap_split Tsh (snap_of T (hs_addr (l_p L)) E H) (l_s L) Hok).
    rewrite hca5_F0b_L3_srest.
    rewrite !hca5_F0b_L3_sn.
    destruct (hca5_F0b_L3_ckh x1 ck2 h2) as (C1 & C2 & C3 & C4 & C5 & C6). rewrite C1, C2, C3, C4, C5, C6.
    rewrite (hca5_F0b_dev_split Tsh (l_wa L) D). change (id_pub (d_id D)) with pub. unfold wg_consts.
    rewrite (hca5_F0b_hin Tsh pub (offset_val 8 (l_wa L))) by lia.
    rewrite (hca5_F0b_hin Tsh dh (l_dh L)) by lia.
    sep_apply (hca5_F0b_L3_st_close Tsh ck2 h2 (l_st L) Lck2 Lh2 FCst).
    sep_apply (hca5_F0b_hout Tsh key2 32 (l_key L) Lk2).
    sep_apply (hca5_F0b_hout Tsh dh 32 (l_dh L) Ldh).
    sep_apply (hca5_F0b_hout Tsh (hca5_F0b_eph rr) 32 (l_eph L) (hca5_F0b_L3_clamp_len rr Lrr)).
    sep_apply (hca5_F0b_hout Tsh (hca5_F0b_E x25519 rr) 32 (l_E L) (Hx _ _)).
    entailer!.
  - forward_if.
    2: { exfalso. match goal with Hn: Int.repr 0 <> Int.zero |- _ => apply Hn; reflexivity end. }
    unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
    assert (HD: Delta = hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
      by (unfold Delta, Delta_specs, abbreviate; reflexivity).
    rewrite HD; clear HD.
    eapply semax_pre; [| apply (HN eq_refl)].
    unfold hca5_F0b_S4, hca5_F0b_Q, hca5_lvars. cbn [app].
    change (hca5_F0b_exp2 x25519 aead_enc H D before rr) with (hca3_put exp1 40 encs).
    change (hca5_F0b_x2 x25519 aead_enc H D rr) with (hs_set_ckh x1 ck2 h2).
    change (hca5_F0b_ck2 x25519 H rr) with ck2. change (hca5_F0b_h2 x25519 aead_enc H D rr) with h2.
    change (hca5_F0b_key2 x25519 H rr) with key2.
    change (hca5_F0b_dh x25519 H rr) with dh.
    assert (Hx2: hs_ok (hs_set_ckh x1 ck2 h2)) by (apply hca5_F0b_L3_x2_ok; auto).
    unfold hca5_F0b_snap.
    rewrite (hca5_F0b_snap_split Tsh (snap_of T (hs_addr (l_p L)) E (hs_set_ckh x1 ck2 h2)) (l_x L) Hx2).
    rewrite (hca5_F0b_snap_split Tsh (snap_of T (hs_addr (l_p L)) E H) (l_s L) Hok).
    rewrite hca5_F0b_L3_srest.
    rewrite !hca5_F0b_L3_sn.
    destruct (hca5_F0b_L3_ckh x1 ck2 h2) as (C1 & C2 & C3 & C4 & C5 & C6). rewrite C1, C2, C3, C4, C5, C6.
    rewrite (hca5_F0b_dev_split Tsh (l_wa L) D). change (id_pub (d_id D)) with pub. unfold wg_consts.
    rewrite (hca5_F0b_hin Tsh pub (offset_val 8 (l_wa L))) by lia.
    rewrite (hca5_F0b_hin Tsh dh (l_dh L)) by lia.
    rewrite (hca5_F0b_st_split Tsh ck2 h2 (l_st L) Lck2 Lh2).
    entailer!.
Qed.

