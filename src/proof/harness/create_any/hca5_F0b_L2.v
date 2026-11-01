(* (port of v1 hca3_F0b_L2.v), law create_any: segment F0b, piece L2 (hca5_F0b_defs.v): from hca5_F0b_S2 through BODY2 (m_mix_hash, m_mix_ck, 2 copies, t'13 = m_dh(dh, eph, s.remote_static); if (t'13) BODY3), given BODY3 as a hypothesis.
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

Lemma hca5_F0b_L2_hash_len m : Zlength (HASH m) = 32.
Proof. unfold HASH, model.blake2s, model.b2s_digest_stream, model.b2s_out. rewrite Zlength_map. reflexivity. Qed.
Lemma hca5_F0b_L2_kdf1_len a b : Zlength (kdf1 a b) = 32.
Proof. unfold kdf1, hmac. cbv zeta. apply hca5_F0b_L2_hash_len. Qed.
Lemma hca5_F0b_L2_mix_hash_len a b : Zlength (mix_hash a b) = 32.
Proof. unfold mix_hash. apply hca5_F0b_L2_hash_len. Qed.
Lemma hca5_F0b_L2_clamp_len r : Zlength r = 32 -> Zlength (hca5_F0b_eph r) = 32.
Proof. intros. unfold hca5_F0b_eph, clamp. rewrite !Zlength_upd_Znth. auto. Qed.
Lemma hca5_F0b_L2_init_ck_len : Zlength init_ck = 32.
Proof. unfold init_ck. apply hca5_F0b_L2_hash_len. Qed.

Lemma hca5_F0b_L2_x0_ok H rr : hs_ok H -> Zlength rr = 32 -> hs_ok (hca5_F0b_x0 H rr).
Proof.
  intros (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8) Lr.
  unfold hs_ok, hca5_F0b_x0.
  cbn [hs_set_ckh hs_set_eph hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts].
  unfold hca5_F0b_h0.
  rewrite hca5_F0b_L2_mix_hash_len, hca5_F0b_L2_init_ck_len, hca5_F0b_L2_clamp_len by auto.
  repeat split; auto.
Qed.

Lemma hca5_F0b_L2_x1_ok H ck h : hs_ok H -> Zlength ck = 32 -> Zlength h = 32 -> hs_ok (hs_set_ckh H ck h).
Proof. intros (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8) Lc Lh. repeat split; auto. Qed.

Lemma hca5_F0b_L2_res x25519 aead_enc H D S before rr ts :
  is_zero (hca5_F0b_E x25519 rr) = false ->
  dh_ok x25519 (hca5_F0b_eph rr) (hs_rstatic H) = false ->
  hca5_F0b_res x25519 aead_enc H D S before rr ts =
  (false, hca5_F0b_exp1 x25519 before rr, hca5_F0b_x1 x25519 H rr).
Proof.
  intros EZ DH. unfold hca5_F0b_E, hca5_F0b_eph in *.
  unfold hca5_F0b_res, hca3_init_exp. cbv zeta. cbn [negb].
  rewrite EZ, DH. reflexivity.
Qed.

Lemma hca5_F0b_L2_ckh H ck h :
  hs_eph (hs_set_ckh H ck h) = hs_eph H /\ hs_rstatic (hs_set_ckh H ck h) = hs_rstatic H /\
  hs_ss (hs_set_ckh H ck h) = hs_ss H /\ hs_hash (hs_set_ckh H ck h) = h /\
  hs_ck (hs_set_ckh H ck h) = ck /\ hs_state (hs_set_ckh H ck h) = hs_state H.
Proof. repeat split. Qed.
Lemma hca5_F0b_L2_sn T a E Hs : sn_hs (snap_of T a E Hs) = Hs.
Proof. reflexivity. Qed.
Lemma hca5_F0b_L2_x1 x25519 H rr :
  hca5_F0b_x1 x25519 H rr = hs_set_ckh (hca5_F0b_x0 H rr) (hca5_F0b_ck1 x25519 rr) (hca5_F0b_h1 x25519 H rr).
Proof. reflexivity. Qed.
Lemma hca5_F0b_L2_h1 x25519 H rr : mix_hash (hca5_F0b_h0 H) (hca5_F0b_E x25519 rr) = hca5_F0b_h1 x25519 H rr.
Proof. reflexivity. Qed.
Lemma hca5_F0b_L2_ck1 x25519 rr : kdf1 init_ck (hca5_F0b_E x25519 rr) = hca5_F0b_ck1 x25519 rr.
Proof. reflexivity. Qed.
Lemma hca5_F0b_L2_dh x25519 H rr : x25519 (hca5_F0b_eph rr) (hs_rstatic H) = hca5_F0b_dh x25519 H rr.
Proof. reflexivity. Qed.

Lemma hca5_F0b_L2_srest sh T a E H ck h p :
  hca5_F0b_srest sh (snap_of T a E (hs_set_ckh H ck h)) p = hca5_F0b_srest sh (snap_of T a E H) p.
Proof. reflexivity. Qed.

Lemma hca5_F0b_L2_st_close sh ck h p : Zlength ck = 32 -> Zlength h = 32 -> @field_compatible HCS t_mstate [] p ->
  hbytes sh ck p * hbytes sh h (offset_val 32 p) |-- @data_at_ HCS sh t_mstate p.
Proof.
  intros Lc Lh FC. eapply derives_trans; [| apply data_at_data_at_].
  rewrite (hca5_F0b_st_split sh ck h p Lc Lh). apply andp_right; [apply prop_right; auto | auto].
Qed.

(* the piece with the sequential post; the then-branch uses hca5_F0b_L3n *)
Lemma hca5_F0b_L2n {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec (gv: globals) (L: hca5_loc)
    (m rv kv rf: val) (Fr: mpred) (T: tstate) (E: entry) (H: handshake) (D: device) (S: shim) (w: list int64) (before rr ts: list byte) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hca5_F0b_facts x25519 aead_enc H D S before rr ts ->
  is_zero (hca5_F0b_E x25519 rr) = false ->
  (dh_ok x25519 (hca5_F0b_eph rr) (hs_rstatic H) = true ->
   semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
     (hca5_F0b_S3 x25519 gv L m rv kv rf Fr T E H D S w before rr ts)
     hca5_F0b_BODY3
     (normal_ret_assert (hca5_F0b_fin gv L m rv kv rf Fr T E H D S w ts (hca5_F0b_res x25519 aead_enc H D S before rr ts)))) ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_F0b_S2 x25519 gv L m rv kv rf Fr T E H D S w before rr ts)
    hca5_F0b_BODY2
    (normal_ret_assert (hca5_F0b_fin gv L m rv kv rf Fr T E H D S w ts (hca5_F0b_res x25519 aead_enc H D S before rr ts))).
Proof.
  intros HH HF EZ HN. pose proof HF as (Hx & Haead & Hok & Lrr & Ls & Lts & Lbef & Lpub).
  unfold hca5_F0b_S2, hca5_F0b_Q, hca5_Delta, hca5_F0b_BODY2.
  simplify_func_tycontext. abbreviate_semax.
  unfold hca5_lvars; cbn [app].
  assert (Hx0: hs_ok (hca5_F0b_x0 H rr)) by (apply hca5_F0b_L2_x0_ok; auto).
  rewrite (hca5_F0b_snap_split Tsh (hca5_F0b_snap L T E H) (l_s L) Hok).
  rewrite (hca5_F0b_snap_split Tsh (hca5_F0b_snap L T E (hca5_F0b_x0 H rr)) (l_x L) Hx0).
  unfold hca5_F0b_snap; cbn [snap_of sn_hs]. unfold wg_consts. Intros.
  pose proof Hok as (Leph & Lrs & Lreph & Lss & Lpsk & Lhash & Lck & Lts0).
  set (x0 := hca5_F0b_x0 H rr) in *.
  pose proof Hx0 as (Xeph & Xrs & Xreph & Xss & Xpsk & Xhash & Xck & Xts).
  set (h0 := hca5_F0b_h0 H) in *.
  set (EE := hca5_F0b_E x25519 rr) in *. set (eph := hca5_F0b_eph rr) in *.
  pose proof hca5_F0b_L2_init_ck_len as Lck0.
  assert (Lh0: Zlength h0 = 32) by exact (hca5_F0b_L2_mix_hash_len init_hash (hs_rstatic H)).
  assert (LE: Zlength EE = 32) by apply Hx.
  assert (Leph': Zlength eph = 32) by (apply hca5_F0b_L2_clamp_len; auto).
  rewrite <- (hca5_F0b_hin Tsh EE (l_E L)) by lia.
  forward_call (gv, Tsh, l_st L, init_ck, h0, Tsh, l_E L, EE).
  { entailer!. simpl. rewrite LE. reflexivity. }
  subst h0 EE eph. rewrite hca5_F0b_L2_h1.
  set (h1 := hca5_F0b_h1 x25519 H rr).
  assert (Lh1: Zlength h1 = 32) by exact (hca5_F0b_L2_mix_hash_len (hca5_F0b_h0 H) (hca5_F0b_E x25519 rr)).
  forward_call (gv, Tsh, l_st L, init_ck, h1, Tsh, l_E L, hca5_F0b_E x25519 rr).
  { entailer!. simpl. rewrite LE. reflexivity. }
  rewrite hca5_F0b_L2_ck1.
  set (ck1 := hca5_F0b_ck1 x25519 rr).
  assert (Lck1: Zlength ck1 = 32) by exact (hca5_F0b_L2_kdf1_len init_ck (hca5_F0b_E x25519 rr)).
  assert_PROP (@field_compatible HCS t_mstate [] (l_st L)) as FCst by entailer!.
  rewrite (hca5_F0b_st_split Tsh ck1 h1 (l_st L) Lck1 Lh1). Intros.
  assert (E1: Zlength (hs_ck x0) = Zlength ck1) by lia.
  sep_apply (hca5_F0b_hout Tsh (hs_ck x0) (Zlength ck1) (offset_val 240 (l_x L)) E1).
  forward_call (Tsh, offset_val 240 (l_x L), Tsh, l_st L, ck1).
  assert (E2: Zlength (hs_hash x0) = Zlength h1) by lia.
  sep_apply (hca5_F0b_hout Tsh (hs_hash x0) (Zlength h1) (offset_val 208 (l_x L)) E2).
  forward_call (Tsh, offset_val 208 (l_x L), Tsh, offset_val 32 (l_st L), h1).
  forward_call (Tsh, l_dh L, Tsh, l_eph L, hca5_F0b_eph rr, Tsh, offset_val 80 (l_s L), hs_rstatic H).
  rewrite hca5_F0b_L2_dh.
  assert (Ldh: Zlength (hca5_F0b_dh x25519 H rr) = 32) by apply Hx.
  destruct (dh_ok x25519 (hca5_F0b_eph rr) (hs_rstatic H)) eqn:DH.
  - forward_if.
    2: { exfalso; first [ match goal with Hn: Int.one = Int.zero |- _ => apply Int.one_not_zero; exact Hn end | match goal with Hn: _ <> _ |- _ => apply Hn; reflexivity end ]. }
    unfold POSTCONDITION, abbreviate.
    assert (HD: Delta = hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
      by (unfold Delta, Delta_specs, abbreviate; reflexivity).
    rewrite HD; clear HD.
    eapply semax_pre; [| apply (HN eq_refl)].
    unfold hca5_F0b_S3, hca5_F0b_Q, hca5_lvars. cbn [app].
    subst x0 h1 ck1.
    rewrite hca5_F0b_L2_x1.
    assert (Hx1: hs_ok (hs_set_ckh (hca5_F0b_x0 H rr) (hca5_F0b_ck1 x25519 rr) (hca5_F0b_h1 x25519 H rr)))
      by (apply hca5_F0b_L2_x1_ok; auto).
    unfold hca5_F0b_snap.
    rewrite (hca5_F0b_snap_split Tsh (snap_of T (hs_addr (l_p L)) E
               (hs_set_ckh (hca5_F0b_x0 H rr) (hca5_F0b_ck1 x25519 rr) (hca5_F0b_h1 x25519 H rr))) (l_x L) Hx1).
    rewrite (hca5_F0b_snap_split Tsh (snap_of T (hs_addr (l_p L)) E H) (l_s L) Hok).
    rewrite hca5_F0b_L2_srest, !hca5_F0b_L2_sn.
    destruct (hca5_F0b_L2_ckh (hca5_F0b_x0 H rr) (hca5_F0b_ck1 x25519 rr) (hca5_F0b_h1 x25519 H rr))
      as (C1 & C2 & C3 & C4 & C5 & C6). rewrite C1, C2, C3, C4, C5, C6.
    unfold wg_consts.
    rewrite (hca5_F0b_hin Tsh (hca5_F0b_E x25519 rr) (l_E L)) by lia.
    rewrite (hca5_F0b_st_split Tsh (hca5_F0b_ck1 x25519 rr) (hca5_F0b_h1 x25519 H rr) (l_st L) Lck1 Lh1).
    entailer!.
  - forward_if.
    { exfalso; first [ match goal with Hn: Int.one = Int.zero |- _ => apply Int.one_not_zero; exact Hn end | match goal with Hn: _ <> _ |- _ => apply Hn; reflexivity end ]. }
    forward.
    rewrite (hca5_F0b_L2_res x25519 aead_enc H D S before rr ts EZ DH).
    unfold hca5_F0b_fin, hca5_F0b_Q, hca5_lvars. cbn [fst snd app].
    subst x0 h1 ck1.
    rewrite hca5_F0b_L2_x1.
    assert (Hx1: hs_ok (hs_set_ckh (hca5_F0b_x0 H rr) (hca5_F0b_ck1 x25519 rr) (hca5_F0b_h1 x25519 H rr)))
      by (apply hca5_F0b_L2_x1_ok; auto).
    unfold hca5_F0b_snap.
    rewrite (hca5_F0b_snap_split Tsh (snap_of T (hs_addr (l_p L)) E
               (hs_set_ckh (hca5_F0b_x0 H rr) (hca5_F0b_ck1 x25519 rr) (hca5_F0b_h1 x25519 H rr))) (l_x L) Hx1).
    rewrite (hca5_F0b_snap_split Tsh (snap_of T (hs_addr (l_p L)) E H) (l_s L) Hok).
    rewrite hca5_F0b_L2_srest, !hca5_F0b_L2_sn.
    destruct (hca5_F0b_L2_ckh (hca5_F0b_x0 H rr) (hca5_F0b_ck1 x25519 rr) (hca5_F0b_h1 x25519 H rr))
      as (C1 & C2 & C3 & C4 & C5 & C6). rewrite C1, C2, C3, C4, C5, C6.
    unfold wg_consts.
    rewrite (hca5_F0b_hin Tsh (hca5_F0b_E x25519 rr) (l_E L)) by lia.
    sep_apply (hca5_F0b_L2_st_close Tsh (hca5_F0b_ck1 x25519 rr) (hca5_F0b_h1 x25519 H rr) (l_st L) Lck1 Lh1 FCst).
    sep_apply (hca5_F0b_hout Tsh (hca5_F0b_dh x25519 H rr) 32 (l_dh L) Ldh).
    sep_apply (hca5_F0b_hout Tsh (hca5_F0b_eph rr) 32 (l_eph L) Leph').
    sep_apply (hca5_F0b_hout Tsh (hca5_F0b_E x25519 rr) 32 (l_E L) LE).
    entailer!.
Qed.

