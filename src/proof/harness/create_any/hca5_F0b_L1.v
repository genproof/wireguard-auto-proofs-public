(* (port of v1 hca3_F0b_L1.v), law create_any: segment F0b, piece L1 (hca5_F0b_defs.v): from hca5_F0b_S0 (ia.ok = 1) through THEN (le32_store .. bytes_zero(E); if (!t'14) BODY2), given BODY2 as a hypothesis.
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

Lemma hca5_F0b_L1h_hash_len m : Zlength (HASH m) = 32.
Proof. unfold HASH, model.blake2s, model.b2s_digest_stream, model.b2s_out. rewrite Zlength_map. reflexivity. Qed.
Lemma hca5_F0b_L1h_kdf1_len a b : Zlength (kdf1 a b) = 32.
Proof. unfold kdf1, hmac. cbv zeta. apply hca5_F0b_L1h_hash_len. Qed.
Lemma hca5_F0b_L1h_mix_hash_len a b : Zlength (mix_hash a b) = 32.
Proof. unfold mix_hash. apply hca5_F0b_L1h_hash_len. Qed.
Lemma hca5_F0b_L1h_clamp_len r : Zlength r = 32 -> Zlength (hca5_F0b_eph r) = 32.
Proof. intros. unfold hca5_F0b_eph, clamp. rewrite !Zlength_upd_Znth. auto. Qed.
Lemma hca5_F0b_L1h_init_ck_len : Zlength init_ck = 32.
Proof. unfold init_ck. apply hca5_F0b_L1h_hash_len. Qed.

Lemma hca5_F0b_L1h_x0_ok H rr : hs_ok H -> Zlength rr = 32 -> hs_ok (hca5_F0b_x0 H rr).
Proof.
  intros (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8) Lr.
  unfold hs_ok, hca5_F0b_x0.
  cbn [hs_set_ckh hs_set_eph hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts].
  unfold hca5_F0b_h0.
  rewrite hca5_F0b_L1h_mix_hash_len, hca5_F0b_L1h_init_ck_len, hca5_F0b_L1h_clamp_len by auto.
  repeat split; auto.
Qed.

Lemma hca5_F0b_L1h_x1_ok H ck h : hs_ok H -> Zlength ck = 32 -> Zlength h = 32 -> hs_ok (hs_set_ckh H ck h).
Proof. intros (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8) Lc Lh. repeat split; auto. Qed.

Lemma hca5_F0b_L1h_res x25519 aead_enc H D S before rr ts :
  is_zero (hca5_F0b_E x25519 rr) = false ->
  dh_ok x25519 (hca5_F0b_eph rr) (hs_rstatic H) = false ->
  hca5_F0b_res x25519 aead_enc H D S before rr ts =
  (false, hca5_F0b_exp1 x25519 before rr, hca5_F0b_x1 x25519 H rr).
Proof.
  intros EZ DH. unfold hca5_F0b_E, hca5_F0b_eph in *.
  unfold hca5_F0b_res, hca3_init_exp. cbv zeta. cbn [negb].
  rewrite EZ, DH. reflexivity.
Qed.

Lemma hca5_F0b_L1h_ckh H ck h :
  hs_eph (hs_set_ckh H ck h) = hs_eph H /\ hs_rstatic (hs_set_ckh H ck h) = hs_rstatic H /\
  hs_ss (hs_set_ckh H ck h) = hs_ss H /\ hs_hash (hs_set_ckh H ck h) = h /\
  hs_ck (hs_set_ckh H ck h) = ck /\ hs_state (hs_set_ckh H ck h) = hs_state H.
Proof. repeat split. Qed.
Lemma hca5_F0b_L1h_sn T a E Hs : sn_hs (snap_of T a E Hs) = Hs.
Proof. reflexivity. Qed.
Lemma hca5_F0b_L1h_x1 x25519 H rr :
  hca5_F0b_x1 x25519 H rr = hs_set_ckh (hca5_F0b_x0 H rr) (hca5_F0b_ck1 x25519 rr) (hca5_F0b_h1 x25519 H rr).
Proof. reflexivity. Qed.
Lemma hca5_F0b_L1h_h1 x25519 H rr : mix_hash (hca5_F0b_h0 H) (hca5_F0b_E x25519 rr) = hca5_F0b_h1 x25519 H rr.
Proof. reflexivity. Qed.
Lemma hca5_F0b_L1h_ck1 x25519 rr : kdf1 init_ck (hca5_F0b_E x25519 rr) = hca5_F0b_ck1 x25519 rr.
Proof. reflexivity. Qed.
Lemma hca5_F0b_L1h_dh x25519 H rr : x25519 (hca5_F0b_eph rr) (hs_rstatic H) = hca5_F0b_dh x25519 H rr.
Proof. reflexivity. Qed.

Lemma hca5_F0b_L1h_srest sh T a E H ck h p :
  hca5_F0b_srest sh (snap_of T a E (hs_set_ckh H ck h)) p = hca5_F0b_srest sh (snap_of T a E H) p.
Proof. reflexivity. Qed.

Lemma hca5_F0b_L1h_st_close sh ck h p : Zlength ck = 32 -> Zlength h = 32 -> @field_compatible HCS t_mstate [] p ->
  hbytes sh ck p * hbytes sh h (offset_val 32 p) |-- @data_at_ HCS sh t_mstate p.
Proof.
  intros Lc Lh FC. eapply derives_trans; [| apply data_at_data_at_].
  rewrite (hca5_F0b_st_split sh ck h p Lc Lh). apply andp_right; [apply prop_right; auto | auto].
Qed.

(* the piece with the sequential post (abbreviate_semax makes the post normal_ret_assert); the then-branch uses
   hca5_F0b_L2n *)
Lemma hca5_F0b_L1_h0 H : mix_hash init_hash (hs_rstatic H) = hca5_F0b_h0 H.
Proof. reflexivity. Qed.
Lemma hca5_F0b_L1_eph rr : clamp rr = hca5_F0b_eph rr.
Proof. reflexivity. Qed.
Lemma hca5_F0b_L1_E x25519 rr : x25519 (hca5_F0b_eph rr) basepoint9 = hca5_F0b_E x25519 rr.
Proof. reflexivity. Qed.
Lemma hca5_F0b_L1_exp1 x25519 before rr :
  hca3_put (hca3_put before 0 (le32 (Int.repr 1))) 8 (hca5_F0b_E x25519 rr) = hca5_F0b_exp1 x25519 before rr.
Proof. reflexivity. Qed.
Lemma hca5_F0b_L1_x0 H rr :
  hs_eph (hca5_F0b_x0 H rr) = hca5_F0b_eph rr /\ hs_rstatic (hca5_F0b_x0 H rr) = hs_rstatic H /\
  hs_ss (hca5_F0b_x0 H rr) = hs_ss H /\ hs_hash (hca5_F0b_x0 H rr) = hca5_F0b_h0 H /\
  hs_ck (hca5_F0b_x0 H rr) = init_ck /\ hs_state (hca5_F0b_x0 H rr) = hs_state H.
Proof. repeat split. Qed.
Lemma hca5_F0b_L1_srest sh T a E H rr p :
  hca5_F0b_srest sh (snap_of T a E (hca5_F0b_x0 H rr)) p = hca5_F0b_srest sh (snap_of T a E H) p.
Proof. reflexivity. Qed.
Lemma hca5_F0b_L1_res x25519 aead_enc H D S before rr ts :
  is_zero (hca5_F0b_E x25519 rr) = true ->
  hca5_F0b_res x25519 aead_enc H D S before rr ts =
  (false, hca5_F0b_exp1 x25519 before rr, hca5_F0b_x0 H rr).
Proof.
  intros EZ. unfold hca5_F0b_E, hca5_F0b_eph in *.
  unfold hca5_F0b_res, hca3_init_exp. cbv zeta. cbn [negb].
  rewrite EZ. reflexivity.
Qed.

Lemma hca5_F0b_L1n {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec (gv: globals) (L: hca5_loc)
    (m rv kv rf: val) (Fr: mpred) (T: tstate) (E: entry) (H: handshake) (D: device) (S: shim) (w: list int64) (before rr ts: list byte) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hca5_F0b_facts x25519 aead_enc H D S before rr ts ->
  (is_zero (hca5_F0b_E x25519 rr) = false ->
   semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
     (hca5_F0b_S2 x25519 gv L m rv kv rf Fr T E H D S w before rr ts)
     hca5_F0b_BODY2
     (normal_ret_assert (hca5_F0b_fin gv L m rv kv rf Fr T E H D S w ts (hca5_F0b_res x25519 aead_enc H D S before rr ts)))) ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_F0b_S0 gv L m rv kv rf Fr T E H D S w before ts)
    hca5_F0b_THEN
    (normal_ret_assert (hca5_F0b_fin gv L m rv kv rf Fr T E H D S w ts (hca5_F0b_res x25519 aead_enc H D S before rr ts))).
Proof.
  intros HH HF HN. pose proof HF as (Hx & Haead & Hok & Lrr & Ls & Lts & Lbef & Lpub).
  unfold hca5_F0b_S0, hca5_F0b_Q, hca5_Delta, hca5_F0b_THEN.
  simplify_func_tycontext. abbreviate_semax.
  unfold hca5_lvars; cbn [app].
  pose proof Hok as (Leph & Lrs & Lreph & Lss & Lpsk & Lhash & Lck & Lts0).
  sep_apply (hca5_F0b_open Tsh before 0 4 (l_exp L)); try lia. Intros.
  forward_call (Tsh, offset_val 0 (l_exp L), Int.repr 1).
  replace (0 + 4) with (0 + Zlength (le32 (Int.repr 1))) by (rewrite hca3_Zlength_le32; reflexivity).
  sep_apply (hca5_F0b_close Tsh before 0 (le32 (Int.repr 1)) (l_exp L)); try (rewrite ?hca3_Zlength_le32; lia).
  set (exp0 := hca3_put before 0 (le32 (Int.repr 1))).
  assert (Lexp0: Zlength exp0 = 148) by (unfold exp0; rewrite hca5_F0b_Zlength_put; rewrite ?hca3_Zlength_le32; lia).
  rewrite (hca5_F0b_snap_split Tsh (hca5_F0b_snap L T E H) (l_s L) Hok).
  rewrite (hca5_F0b_snap_split Tsh (hca5_F0b_snap L T E H) (l_x L) Hok).
  unfold hca5_F0b_snap. rewrite !hca5_F0b_L1h_sn. rewrite hca5_F0b_consts. unfold wg_consts. Intros.
  forward_call (gv, Tsh, l_st L, Tsh, offset_val 80 (l_s L), hs_rstatic H).
  rewrite hca5_F0b_L1_h0.
  pose proof hca5_F0b_L1h_init_ck_len as Lck0.
  assert (Lh0: Zlength (hca5_F0b_h0 H) = 32) by exact (hca5_F0b_L1h_mix_hash_len init_hash (hs_rstatic H)).
  remember init_ck as ck0 eqn:Eck0.
  set (h0 := hca5_F0b_h0 H) in *.
  assert_PROP (@field_compatible HCS t_mstate [] (l_st L)) as FCst by entailer!.
  rewrite (hca5_F0b_st_split Tsh ck0 h0 (l_st L) Lck0 Lh0). Intros.
  assert (E1: Zlength (hs_ck H) = Zlength ck0) by lia.
  sep_apply (hca5_F0b_hout Tsh (hs_ck H) (Zlength ck0) (offset_val 240 (l_x L)) E1).
  forward_call (Tsh, offset_val 240 (l_x L), Tsh, l_st L, ck0).
  all: try (entailer!; simpl; rewrite ?Lck0; normalize).
  assert (E2: Zlength (hs_hash H) = Zlength h0) by lia.
  sep_apply (hca5_F0b_hout Tsh (hs_hash H) (Zlength h0) (offset_val 208 (l_x L)) E2).
  forward_call (Tsh, offset_val 208 (l_x L), Tsh, offset_val 32 (l_st L), h0).
  all: try (entailer!; simpl; rewrite ?Lh0; normalize).
  rewrite (hca5_F0b_shim_split gv S w). Intros.
  replace (hout Tsh 32 (l_eph L)) with (hout Tsh (Zlength (s_log S)) (l_eph L)) by (rewrite Ls, Lrr; reflexivity).
  forward_call (Tsh, l_eph L, Ews, gv HC._wg_shim_random_log, s_log S).
  all: try (entailer!; simpl; rewrite ?Ls, ?Lrr; normalize).
  rewrite Ls.
  forward_call (Tsh, l_eph L, rr).
  rewrite hca5_F0b_L1_eph.
  assert (Leph0: Zlength (hca5_F0b_eph rr) = 32) by (apply hca5_F0b_L1h_clamp_len; auto).
  assert (E4: Zlength (hs_eph H) = Zlength (hca5_F0b_eph rr)) by lia.
  sep_apply (hca5_F0b_hout Tsh (hs_eph H) (Zlength (hca5_F0b_eph rr)) (offset_val 48 (l_x L)) E4).
  forward_call (Tsh, offset_val 48 (l_x L), Tsh, l_eph L, hca5_F0b_eph rr).
  all: try (entailer!; simpl; rewrite ?Leph0; normalize).
  assert (NZ: is_zero (hca5_F0b_eph rr) = false) by (apply hca3_clamp_nonzero; auto).
  match goal with |- semax _ ?P _ _ => eapply semax_seq with (Q := P) end.
  2: abbreviate_semax.
  1: { match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { entailer!. }
  { forward_call (Tsh, l_eph L, hca5_F0b_eph rr).
    all: try (entailer!; simpl; rewrite ?Leph0; normalize).
    rewrite NZ.
    forward_if.
    { exfalso; first [ match goal with Hn: Int.one = Int.zero |- _ => apply Int.one_not_zero; exact Hn end | match goal with Hn: _ = Int.zero |- _ => apply Int.one_not_zero; exact Hn end | match goal with Hn: _ <> _ |- _ => apply Hn; reflexivity end ]. }
    forward. unfold hca5_F0b_srest; entailer!. }
  { forward. try (unfold hca5_F0b_srest; entailer!). }
  apply andp_left2, derives_refl. }
  forward_call (Tsh, l_E L, Tsh, l_eph L, hca5_F0b_eph rr, Ers, gv HC._x_create_any__M_BASEPOINT, basepoint9).
  rewrite hca5_F0b_L1_E.
  assert (LE: Zlength (hca5_F0b_E x25519 rr) = 32) by apply Hx.
  sep_apply (hca5_F0b_open Tsh exp0 8 32 (l_exp L)); try lia. Intros.
  replace (hout Tsh 32 (offset_val 8 (l_exp L))) with (hout Tsh (Zlength (hca5_F0b_E x25519 rr)) (offset_val 8 (l_exp L)))
    by (rewrite LE; reflexivity).
  forward_call (Tsh, offset_val 8 (l_exp L), Tsh, l_E L, hca5_F0b_E x25519 rr).
  all: try (entailer!; simpl; rewrite ?LE; normalize).
  replace (8 + 32) with (8 + Zlength (hca5_F0b_E x25519 rr)) by (rewrite LE; reflexivity).
  sep_apply (hca5_F0b_close Tsh exp0 8 (hca5_F0b_E x25519 rr) (l_exp L)); try lia.
  unfold exp0. rewrite hca5_F0b_L1_exp1. fold exp0.
  forward_call (Tsh, l_E L, hca5_F0b_E x25519 rr).
  all: try (entailer!; simpl; rewrite ?LE; normalize).
  destruct (is_zero (hca5_F0b_E x25519 rr)) eqn:EZ.
  - forward_if.
    { exfalso; first [ match goal with Hn: Int.one = Int.zero |- _ => apply Int.one_not_zero; exact Hn end | match goal with Hn: _ = Int.zero |- _ => apply Int.one_not_zero; exact Hn end | match goal with Hn: _ <> _ |- _ => apply Hn; reflexivity end ]. }
    forward.
    rewrite (hca5_F0b_L1_res x25519 aead_enc H D S before rr ts EZ).
    unfold hca5_F0b_fin, hca5_F0b_Q, hca5_lvars. cbn [fst snd app].
    subst ck0 h0 exp0.
    assert (Hx0: hs_ok (hca5_F0b_x0 H rr)) by (apply hca5_F0b_L1h_x0_ok; auto).
    unfold hca5_F0b_snap.
    rewrite (hca5_F0b_snap_split Tsh (snap_of T (hs_addr (l_p L)) E (hca5_F0b_x0 H rr)) (l_x L) Hx0).
    rewrite (hca5_F0b_snap_split Tsh (snap_of T (hs_addr (l_p L)) E H) (l_s L) Hok).
    rewrite hca5_F0b_L1_srest, !hca5_F0b_L1h_sn.
    destruct (hca5_F0b_L1_x0 H rr) as (C1 & C2 & C3 & C4 & C5 & C6). rewrite C1, C2, C3, C4, C5, C6.
    rewrite (hca5_F0b_shim_split gv S w). rewrite hca5_F0b_consts. unfold wg_consts.
    sep_apply (hca5_F0b_L1h_st_close Tsh init_ck (hca5_F0b_h0 H) (l_st L) Lck0 Lh0 FCst).
    sep_apply (hca5_F0b_hout Tsh (hca5_F0b_eph rr) 32 (l_eph L) Leph0).
    sep_apply (hca5_F0b_hout Tsh (hca5_F0b_E x25519 rr) 32 (l_E L) LE).
    entailer!.
  - forward_if.
    2: { exfalso; first [ match goal with Hn: Int.one = Int.zero |- _ => apply Int.one_not_zero; exact Hn end | match goal with Hn: _ = Int.zero |- _ => apply Int.one_not_zero; exact Hn end | match goal with Hn: _ <> _ |- _ => apply Hn; reflexivity end ]. }
    unfold POSTCONDITION, abbreviate. subst ck0.
    assert (HD: Delta = hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
      by (unfold Delta, Delta_specs, abbreviate; reflexivity).
    rewrite HD; clear HD.
    eapply semax_pre; [| apply (HN eq_refl)].
    unfold hca5_F0b_S2, hca5_F0b_Q, hca5_lvars. cbn [app].
    subst h0 exp0.
    assert (Hx0: hs_ok (hca5_F0b_x0 H rr)) by (apply hca5_F0b_L1h_x0_ok; auto).
    unfold hca5_F0b_snap.
    rewrite (hca5_F0b_snap_split Tsh (snap_of T (hs_addr (l_p L)) E (hca5_F0b_x0 H rr)) (l_x L) Hx0).
    rewrite (hca5_F0b_snap_split Tsh (snap_of T (hs_addr (l_p L)) E H) (l_s L) Hok).
    rewrite hca5_F0b_L1_srest, !hca5_F0b_L1h_sn.
    destruct (hca5_F0b_L1_x0 H rr) as (C1 & C2 & C3 & C4 & C5 & C6). rewrite C1, C2, C3, C4, C5, C6.
    rewrite (hca5_F0b_shim_split gv S w). rewrite hca5_F0b_consts. unfold wg_consts.
    rewrite (hca5_F0b_st_split Tsh init_ck (hca5_F0b_h0 H) (l_st L) Lck0 Lh0).
    entailer!.
Qed.

