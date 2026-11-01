(* (port of v1 hca3_F0b_L4.v), law create_any: segment F0b, piece L4 (hca5_F0b_defs.v): from hca5_F0b_S4 through BODY4 (m_mix_key(ss), m_encrypt_and_hash(exp+88, ts), 2 copies, ok = 1, le32_store(exp+4, random_u32), x.state = 1).
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

Lemma hca5_F0b_L4_hash_len m : Zlength (HASH m) = 32.
Proof. unfold HASH, model.blake2s, model.b2s_digest_stream, model.b2s_out. rewrite Zlength_map. reflexivity. Qed.
Lemma hca5_F0b_L4_kdf1_len a b : Zlength (kdf1 a b) = 32.
Proof. unfold kdf1, hmac. cbv zeta. apply hca5_F0b_L4_hash_len. Qed.
Lemma hca5_F0b_L4_kdf2_len a b : Zlength (kdf2 a b) = 32.
Proof. unfold kdf2, hmac. cbv zeta. apply hca5_F0b_L4_hash_len. Qed.
Lemma hca5_F0b_L4_mix_hash_len a b : Zlength (mix_hash a b) = 32.
Proof. unfold mix_hash. apply hca5_F0b_L4_hash_len. Qed.

Lemma hca5_F0b_L4_exp2_len x25519 aead_enc H D before rr :
  x25519_props x25519 -> (forall k n ad m, Zlength (aead_enc k n ad m) = Zlength m + 16) ->
  Zlength before = 148 -> Zlength (id_pub (d_id D)) = 32 ->
  Zlength (hca5_F0b_exp2 x25519 aead_enc H D before rr) = 148.
Proof.
  intros Hx Ha Lb Lp. unfold hca5_F0b_exp2, hca5_F0b_exp1, hca5_F0b_encs, hca5_F0b_E.
  assert (L0: Zlength (hca3_put before 0 (le32 (Int.repr 1))) = 148)
    by (rewrite hca5_F0b_Zlength_put; rewrite ?hca3_Zlength_le32; lia).
  assert (L1: Zlength (hca3_put (hca3_put before 0 (le32 (Int.repr 1))) 8 (x25519 (hca5_F0b_eph rr) basepoint9)) = 148)
    by (rewrite hca5_F0b_Zlength_put; rewrite ?Hx; lia).
  rewrite hca5_F0b_Zlength_put; rewrite ?Ha; lia.
Qed.

Lemma hca5_F0b_L4_x2_ok x25519 aead_enc H D rr : hs_ok H -> Zlength rr = 32 ->
  hs_ok (hca5_F0b_x2 x25519 aead_enc H D rr).
Proof.
  intros (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8) Lr.
  unfold hs_ok, hca5_F0b_x2, hca5_F0b_x1, hca5_F0b_x0.
  cbn [hs_set_ckh hs_set_eph hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts].
  unfold hca5_F0b_h2, hca5_F0b_ck2, hca5_F0b_eph.
  rewrite hca5_F0b_L4_mix_hash_len, hca5_F0b_L4_kdf1_len.
  unfold clamp. rewrite !Zlength_upd_Znth. repeat split; auto.
Qed.

Lemma hca5_F0b_L4_res x25519 aead_enc H D S before rr ts :
  is_zero (hca5_F0b_E x25519 rr) = false ->
  dh_ok x25519 (hca5_F0b_eph rr) (hs_rstatic H) = true ->
  is_zero (hs_ss H) = false ->
  hca5_F0b_res x25519 aead_enc H D S before rr ts =
  (true,
   hca3_put (hca3_put (hca5_F0b_exp2 x25519 aead_enc H D before rr) 88
       (aead_enc (kdf2 (hca5_F0b_ck2 x25519 H rr) (hs_ss H)) 0 (hca5_F0b_h2 x25519 aead_enc H D rr) ts)) 4
     (le32 (s_u32 S)),
   hs_set_state
     (hs_set_ckh (hca5_F0b_x2 x25519 aead_enc H D rr) (kdf1 (hca5_F0b_ck2 x25519 H rr) (hs_ss H))
        (mix_hash (hca5_F0b_h2 x25519 aead_enc H D rr)
           (aead_enc (kdf2 (hca5_F0b_ck2 x25519 H rr) (hs_ss H)) 0 (hca5_F0b_h2 x25519 aead_enc H D rr) ts)))
     HS_CREATED_INITIATION).
Proof.
  intros EZ DH SS. unfold hca5_F0b_E, hca5_F0b_eph in *.
  unfold hca5_F0b_res, hca3_init_exp. cbv zeta. cbn [negb].
  rewrite EZ, DH, SS. reflexivity.
Qed.

Lemma hca5_F0b_L4_st_close sh ck h p : Zlength ck = 32 -> Zlength h = 32 -> @field_compatible HCS t_mstate [] p ->
  hbytes sh ck p * hbytes sh h (offset_val 32 p) |-- @data_at_ HCS sh t_mstate p.
Proof.
  intros Lc Lh FC. eapply derives_trans; [| apply data_at_data_at_].
  rewrite (hca5_F0b_st_split sh ck h p Lc Lh). apply andp_right; [apply prop_right; auto | auto].
Qed.

Lemma hca5_F0b_L4_srest sh T a E H ck h st p :
  hca5_F0b_srest sh (snap_of T a E (hs_set_state (hs_set_ckh H ck h) st)) p = hca5_F0b_srest sh (snap_of T a E H) p.
Proof. reflexivity. Qed.

Lemma hca5_F0b_L4_x3_ok H ck h st : hs_ok H -> Zlength ck = 32 -> Zlength h = 32 ->
  hs_ok (hs_set_state (hs_set_ckh H ck h) st).
Proof. intros (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8) Lc Lh. repeat split; auto. Qed.

Lemma hca5_F0b_L4_clamp_len r : Zlength r = 32 -> Zlength (hca5_F0b_eph r) = 32.
Proof. intros. unfold hca5_F0b_eph, clamp. rewrite !Zlength_upd_Znth. auto. Qed.

(* the piece with the sequential post (what abbreviate_semax makes of every piece's goal; the previous pieces use it) *)
Lemma hca5_F0b_L4n {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec (gv: globals) (L: hca5_loc)
    (m rv kv rf: val) (Fr: mpred) (T: tstate) (E: entry) (H: handshake) (D: device) (S: shim) (w: list int64) (before rr ts: list byte) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hca5_F0b_facts x25519 aead_enc H D S before rr ts ->
  is_zero (hca5_F0b_E x25519 rr) = false ->
  dh_ok x25519 (hca5_F0b_eph rr) (hs_rstatic H) = true ->
  is_zero (hs_ss H) = false ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_F0b_S4 x25519 aead_enc gv L m rv kv rf Fr T E H D S w before rr ts)
    hca5_F0b_BODY4
    (normal_ret_assert (hca5_F0b_fin gv L m rv kv rf Fr T E H D S w ts (hca5_F0b_res x25519 aead_enc H D S before rr ts))).
Proof.
  intros HH HF EZ DH SS.
  destruct HF as (Hx & Haead & Hok & Lrr & Ls & Lts & Lbef & Lpub).
  unfold hca5_F0b_S4, hca5_F0b_Q, hca5_Delta, hca5_F0b_BODY4.
  simplify_func_tycontext. abbreviate_semax.
  unfold hca5_lvars; cbn [app].
  rewrite (hca5_F0b_snap_split Tsh (hca5_F0b_snap L T E H) (l_s L) Hok).
  unfold hca5_F0b_snap; cbn [snap_of sn_hs]. unfold wg_consts. Intros.
  pose proof Hok as (Leph & Lrs & Lreph & Lss & Lpsk & Lhash & Lck & Lts0).
  assert (Lck2: Zlength (hca5_F0b_ck2 x25519 H rr) = 32) by apply hca5_F0b_L4_kdf1_len.
  assert (Lh2: Zlength (hca5_F0b_h2 x25519 aead_enc H D rr) = 32) by apply hca5_F0b_L4_mix_hash_len.
  assert (Lk2: Zlength (hca5_F0b_key2 x25519 H rr) = 32) by apply hca5_F0b_L4_kdf2_len.
  sep_apply (hca5_F0b_hout Tsh (hca5_F0b_key2 x25519 H rr) 32 (l_key L) Lk2).
  rewrite <- (hca5_F0b_hin Tsh (hs_ss H) (offset_val 144 (l_s L))) by lia.
  forward_call (gv, Tsh, l_st L, hca5_F0b_ck2 x25519 H rr, hca5_F0b_h2 x25519 aead_enc H D rr, Tsh, l_key L,
                Tsh, offset_val 144 (l_s L), hs_ss H).
  { unfold hca5_F0b_srest; entailer!. simpl. rewrite Lss. reflexivity. }
  set (ck2 := hca5_F0b_ck2 x25519 H rr) in *. set (h2 := hca5_F0b_h2 x25519 aead_enc H D rr) in *.
  set (ck3 := kdf1 ck2 (hs_ss H)). set (key3 := kdf2 ck2 (hs_ss H)).
  set (exp2 := hca5_F0b_exp2 x25519 aead_enc H D before rr) in *.
  assert (Lenc: forall k ad, Zlength (aead_enc k 0 ad ts) = 28) by (intros; rewrite Haead; lia).
  assert (Lexp2: Zlength exp2 = 148) by (apply hca5_F0b_L4_exp2_len; auto).
  sep_apply (hca5_F0b_open Tsh exp2 88 28 (l_exp L)); try lia. Intros.
  rewrite <- (hca5_F0b_hin Tsh ts (l_ts L)) by lia.
  replace (hout Tsh 28 (offset_val 88 (l_exp L))) with (hout Tsh (Zlength ts + 16) (offset_val 88 (l_exp L)))
    by (rewrite Lts; reflexivity).
  forward_call (gv, Tsh, l_st L, ck3, h2, Tsh, offset_val 88 (l_exp L), Tsh, l_ts L, ts, Tsh, l_key L, key3).
  { entailer!. simpl. rewrite Lts. reflexivity. }
  set (enct := aead_enc key3 0 h2 ts).
  set (h3 := mix_hash h2 enct).
  assert (Le: Zlength enct = 28) by apply Lenc.
  assert (Lck3: Zlength ck3 = 32) by apply hca5_F0b_L4_kdf1_len.
  assert (Lh3: Zlength h3 = 32) by apply hca5_F0b_L4_mix_hash_len.
  replace (88 + 28) with (88 + Zlength enct) by (rewrite Le; reflexivity).
  sep_apply (hca5_F0b_close Tsh exp2 88 enct (l_exp L)); try lia.
  set (exp3 := hca3_put exp2 88 enct).
  assert (Lexp3: Zlength exp3 = 148) by (unfold exp3; rewrite hca5_F0b_Zlength_put; lia).
  (* x and st opened for the two copies *)
  set (x2 := hca5_F0b_x2 x25519 aead_enc H D rr) in *.
  assert (Hx2: hs_ok x2) by (apply hca5_F0b_L4_x2_ok; auto).
  pose proof Hx2 as (Xeph & Xrs & Xreph & Xss & Xpsk & Xhash & Xck & Xts).
  rewrite (hca5_F0b_snap_split Tsh (snap_of T (hs_addr (l_p L)) E x2) (l_x L) Hx2).
  cbn [snap_of sn_hs].
  rewrite (hca5_F0b_st_split Tsh ck3 h3 (l_st L) Lck3 Lh3). Intros.
  assert (E1: Zlength (hs_ck x2) = Zlength ck3) by lia.
  sep_apply (hca5_F0b_hout Tsh (hs_ck x2) (Zlength ck3) (offset_val 240 (l_x L)) E1).
  forward_call (Tsh, offset_val 240 (l_x L), Tsh, l_st L, ck3).
  assert (E2: Zlength (hs_hash x2) = Zlength h3) by lia.
  sep_apply (hca5_F0b_hout Tsh (hs_hash x2) (Zlength h3) (offset_val 208 (l_x L)) E2).
  forward_call (Tsh, offset_val 208 (l_x L), Tsh, offset_val 32 (l_st L), h3).
  forward.
  rewrite (hca5_F0b_shim_split gv S w). Intros.
  forward.
  sep_apply (hca5_F0b_open Tsh exp3 4 4 (l_exp L)); try lia. Intros.
  forward_call (Tsh, offset_val 4 (l_exp L), s_u32 S).
  replace (4 + 4) with (4 + Zlength (le32 (s_u32 S))) by (rewrite hca3_Zlength_le32; reflexivity).
  sep_apply (hca5_F0b_close Tsh exp3 4 (le32 (s_u32 S)) (l_exp L)); try (rewrite ?hca3_Zlength_le32; lia).
  forward.
  rewrite (hca5_F0b_L4_res x25519 aead_enc H D S before rr ts EZ DH SS).
  change (hca5_F0b_x2 x25519 aead_enc H D rr) with x2. change (hca5_F0b_exp2 x25519 aead_enc H D before rr) with exp2.
  change (hca5_F0b_ck2 x25519 H rr) with ck2. change (hca5_F0b_h2 x25519 aead_enc H D rr) with h2.
  change (kdf1 ck2 (hs_ss H)) with ck3. change (kdf2 ck2 (hs_ss H)) with key3.
  change (aead_enc key3 0 h2 ts) with enct. change (mix_hash h2 enct) with h3. change (hca3_put exp2 88 enct) with exp3.
  unfold hca5_F0b_fin, hca5_F0b_Q, hca5_lvars. cbn [fst snd app].
  assert (Hx3: hs_ok (hs_set_state (hs_set_ckh x2 ck3 h3) HS_CREATED_INITIATION))
    by (apply hca5_F0b_L4_x3_ok; auto).
  unfold hca5_F0b_snap.
  rewrite (hca5_F0b_snap_split Tsh (snap_of T (hs_addr (l_p L)) E (hs_set_state (hs_set_ckh x2 ck3 h3) HS_CREATED_INITIATION)) (l_x L) Hx3).
  rewrite (hca5_F0b_snap_split Tsh (snap_of T (hs_addr (l_p L)) E H) (l_s L) Hok).
  rewrite hca5_F0b_L4_srest.
  cbn [snap_of sn_hs hs_set_state hs_set_ckh hs_eph hs_rstatic hs_ss hs_hash hs_ck hs_state].
  unfold HS_CREATED_INITIATION.
  rewrite (hca5_F0b_shim_split gv S w). unfold wg_consts.
  rewrite (hca5_F0b_hin Tsh (hs_ss H) (offset_val 144 (l_s L))) by lia.
  rewrite (hca5_F0b_hin Tsh ts (l_ts L)) by lia.
  sep_apply (hca5_F0b_L4_st_close Tsh ck3 h3 (l_st L) Lck3 Lh3 H1).
  assert (Lkey3: Zlength key3 = 32) by apply hca5_F0b_L4_kdf2_len.
  sep_apply (hca5_F0b_hout Tsh key3 32 (l_key L) Lkey3).
  sep_apply (hca5_F0b_hout Tsh (hca5_F0b_dh x25519 H rr) 32 (l_dh L) (Hx _ _)).
  sep_apply (hca5_F0b_hout Tsh (hca5_F0b_eph rr) 32 (l_eph L) (hca5_F0b_L4_clamp_len rr Lrr)).
  sep_apply (hca5_F0b_hout Tsh (hca5_F0b_E x25519 rr) 32 (l_E L) (Hx _ _)).
  entailer!.
Qed.

