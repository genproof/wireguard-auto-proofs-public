(* law handshake_receive, B8 branch R segment A: the pure facts of the world after
   an accepted response (rx_resp_accepted from hrx5_W0), used by the CHECKs of segment A. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_cut.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mspec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require WgNoise.contracts.x_handshake_receive.
Require WgNoise.harness.x_handshake_receive.code.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_conv.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_ilem.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_defs.
#[local] Existing Instance W_handshake_receive.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Lemma hrx5_B8RA_find_inL T L idx x E : t_find_index T L idx = Some (x, E) -> In x L.
Proof.
  induction L as [|b L IH]; simpl; [discriminate|].
  destruct (t_entry T b) eqn:HE; [destruct (Int.eq (e_index e) idx)|].
  - intros H; inv H; left; reflexivity.
  - intros H; right; auto.
  - intros H; right; auto.
Qed.

Lemma hrx5_B8RA_pool_hs KA PS T x sh E :
  hrx5cr_pool KA PS T -> In (x, sh, E) (t_D T) -> e_type E = IDX_HANDSHAKE -> x = hs_addr (e_peer E).
Proof.
  intros [H1 H2] HIn Ht.
  rewrite <- (firstn_skipn (length KA) (t_D T)) in HIn.
  apply in_app_or in HIn as [HIn|HIn].
  - destruct (hrx5cr_model_F2_in_r _ _ _ _ H1 HIn) as [K [_ HK]].
    simpl in HK. destruct HK as (_ & _ & _ & HK). rewrite Ht in HK. discriminate.
  - destruct (hrx5cr_model_F2_in_r _ _ _ _ H2 HIn) as [[[p sp] P] [_ HK]].
    simpl in HK. destruct HK as (-> & _ & -> & _). reflexivity.
Qed.

(* the accepted peer's handshake entry is in the table's list *)
Lemma hrx5_B8RA_vin x25519 aead_dec R L NS PS KE T head nk M a P ck h :
  hrx5_inv x25519 R L NS PS KE T head nk ->
  hrx5cr_tgt x25519 aead_dec (hrx5_ID x25519 R) T PS M = Some (a, P, ck, h) ->
  vin (hs_addr a) (t_L T) = true.
Proof.
  intros Hinv. destruct Hinv as (_ & _ & _ & _ & _ & _ & Hpool).
  unfold hrx5cr_tgt. destruct (mi_ok _); [|discriminate].
  destruct (t_find_index T (t_L T) _) as [[x E]|] eqn:Hf; [|discriminate].
  destruct (Int.eq (e_type E) IDX_HANDSHAKE) eqn:Ht; [|discriminate].
  destruct (sfind PS (e_peer E)) as [[sh0 P0]|]; [|discriminate].
  destruct (Int.eq (hs_state _) _); [|discriminate].
  destruct (m_consume_response_model _ _ _ _ _ _ _ _ _) as [[ck0 h0]|]; [|discriminate].
  intros H; inv H.
  apply Int.same_if_eq in Ht.
  pose proof (hrx5_B8RA_find_inL _ _ _ _ _ Hf) as HL.
  apply hrx5cr_model_find_in in Hf. unfold t_entry in Hf.
  destruct (sfind (t_D T) x) as [[sh E0]|] eqn:Hs; [|discriminate]. inv Hf.
  apply hrx5cr_model_sfind_in in Hs.
  rewrite <- (hrx5_B8RA_pool_hs _ _ _ _ _ _ Hpool Hs Ht).
  unfold vin. destruct (in_dec eq_dec x (t_L T)); [reflexivity | contradiction].
Qed.

Lemma hrx5_B8RA_rc r : 0 < Int.unsigned r < 2147483647 ->
  rc_sub1 (rc_add1 r) = r /\ rc_dec_warn (rc_add1 r) = (fun w => w) /\ Int.eq r Int.zero = false.
Proof.
  intros Hr. rewrite rc_add1_small by lia.
  assert (E: Int.unsigned (Int.add r Int.one) = Int.unsigned r + 1).
  { unfold Int.add. rewrite Int.unsigned_one, Int.unsigned_repr; [reflexivity | rep_lia]. }
  assert (N: rc_neg (Int.add r Int.one) = false).
  { unfold rc_neg. unfold Int.ltu. rewrite E, Int.unsigned_repr by rep_lia.
    destruct (zlt _ _); [reflexivity | lia]. }
  assert (E1: Int.eq (Int.add r Int.one) Int.one = false).
  { apply Int.eq_false. intros H. apply (f_equal Int.unsigned) in H. rewrite E, Int.unsigned_one in H. lia. }
  assert (E0: Int.eq (Int.add r Int.one) Int.zero = false).
  { apply Int.eq_false. intros H. apply (f_equal Int.unsigned) in H. rewrite E, Int.unsigned_zero in H. lia. }
  assert (Z0: Int.eq r Int.zero = false).
  { apply Int.eq_false. intros H. subst r. rewrite Int.unsigned_zero in Hr. lia. }
  unfold rc_sub1, rc_dec_warn. rewrite N, E1, E0. cbn [negb andb orb].
  split; [| split; [reflexivity | exact Z0]].
  rewrite Int.sub_add_opp, Int.add_assoc, Int.add_neg_zero, Int.add_zero. reflexivity.
Qed.

Lemma hrx5_B8RA_succ (x: int64) : Int64.eq (Int64.add x Int64.one) x = false.
Proof.
  apply Int64.eq_false. intros H.
  assert (H2: Int64.sub (Int64.add x Int64.one) x = Int64.sub x x) by (rewrite H; reflexivity).
  rewrite Int64.sub_idem, Int64.sub_add_l, Int64.sub_idem, Int64.add_zero_l in H2. discriminate.
Qed.

Lemma hrx5_B8RA_note X p : rx_peer X = p -> rx_note X p = X.
Proof.
  destruct X as [c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 pp ob]; simpl; intros <-. unfold rx_note; simpl.
  destruct (EqDec_val pp nullval); [subst; reflexivity|].
  destruct (EqDec_val pp pp); [reflexivity | congruence].
Qed.

Lemma hrx5_B8RA_sd c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 p o :
  rx_session_derived (mkRx c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 p o) p = mkRx c1 c2 c3 c4 c5 (inc c6) c7 c8 c9 c10 c11 c12 p o.
Proof. unfold rx_session_derived. apply hrx5_B8RA_note. reflexivity. Qed.

Lemma hrx5_B8RA_hc c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 p o :
  rx_handshake_complete (mkRx c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 p o) p = mkRx c1 c2 c3 c4 c5 c6 (inc c7) c8 c9 c10 c11 c12 p o.
Proof. unfold rx_handshake_complete. apply hrx5_B8RA_note. reflexivity. Qed.

Lemma hrx5_B8RA_ka c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 p o :
  rx_send_keepalive (mkRx c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 p o) p = mkRx c1 c2 c3 c4 c5 c6 c7 (inc c8) c9 c10 c11 c12 p o.
Proof. unfold rx_send_keepalive. apply hrx5_B8RA_note. reflexivity. Qed.

Lemma hrx5_B8RA_us c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 p o l :
  rx_update_stats (mkRx c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 p o) p l = mkRx c1 c2 c3 c4 c5 c6 c7 c8 (inc c9) l c11 c12 p o.
Proof. unfold rx_update_stats. apply hrx5_B8RA_note. reflexivity. Qed.

Lemma hrx5_B8RA_ar c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 p o :
  rx_auth_received (mkRx c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 p o) p = mkRx c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 (inc c11) c12 p o.
Proof. unfold rx_auth_received. apply hrx5_B8RA_note. reflexivity. Qed.

Lemma hrx5_B8RA_at c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 p o :
  rx_auth_traversal (mkRx c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 p o) p = mkRx c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 (inc c12) p o.
Proof. unfold rx_auth_traversal. apply hrx5_B8RA_note. reflexivity. Qed.

Lemma hrx5_B8RA_log a sp len (b: bool) :
  let X := rx_tail (if b then rx_send_keepalive (rx_handshake_complete (rx_session_derived
             (rx_set_endpoint rx0 a sp) a) a) a else rx_set_endpoint rx0 a sp) a len in
  rx_authenticated_b X a sp len Int.zero (if b then Int.one else Int.zero) = true /\
  rx_peer X = a /\ rx_eskb X = sp.
Proof.
  intros X. subst X.
  assert (H0: rx_set_endpoint rx0 a sp = mkRx Int.zero Int.zero (inc Int.zero) sp Int.zero Int.zero Int.zero Int.zero
     Int.zero Int64.zero Int.zero Int.zero a false).
  { unfold rx_set_endpoint, rx_note, rx0. cbn [rx_cookie rx_cindex rx_endpoint rx_eskb rx_response rx_session rx_complete rx_keepalive rx_stats rx_len rx_received rx_traversal rx_peer rx_other].
    destruct (eq_dec nullval nullval); [reflexivity | congruence]. }
  rewrite H0. unfold rx_tail.
  destruct b; rewrite ?hrx5_B8RA_sd, ?hrx5_B8RA_hc, ?hrx5_B8RA_ka, hrx5_B8RA_us, hrx5_B8RA_ar, hrx5_B8RA_at.
  all: split; [| split; reflexivity].
  all: unfold rx_authenticated_b; cbn [rx_cookie rx_cindex rx_endpoint rx_eskb rx_response rx_session rx_complete rx_keepalive rx_stats rx_len rx_received rx_traversal rx_peer rx_other].
  all: destruct (eq_dec sp sp) as [_|n]; [|congruence]; destruct (eq_dec a a) as [_|n]; [|congruence].
  all: rewrite Int64.eq_true; vm_compute; reflexivity.
Qed.

Lemma hrx5_B8RA_put0 u W : kp_put nullval u W = W.
Proof. unfold kp_put. destruct (eq_dec nullval nullval) as [e|n]; [reflexivity | congruence]. Qed.

Lemma hrx5_B8RA_bs P M ck h a k kc T S1 ok P2 W2 kc2 :
  p_next P = nullval -> p_prev P = nullval -> vin (hs_addr a) (t_L T) = true ->
  bs_res (hrx5cr_new P M ck h) a k kc [] T S1 = (ok, P2, W2, kc2) ->
  ok = (if eq_dec k nullval then false else negb (p_dead P)) /\ p_refs P2 = rc_add1 (p_refs P) /\
  s_fails (kw_S W2) = (if eq_dec k nullval then Int64.add (s_fails S1) Int64.one else s_fails S1).
Proof.
  intros Hn Hp Hvin. unfold bs_res, begin_session_model.
  cbn [p_hs p_set_hs p_set_refs hrx5cr_new hs_state].
  rewrite Int.eq_true, orb_true_r. cbn [negb].
  destruct (eq_dec k nullval) as [Hk|Hk].
  { intros H; inv H. split; [reflexivity|]. split; reflexivity. }
  change (p_dead (hrx5cr_new P M ck h)) with (p_dead P).
  destruct (p_dead P).
  { intros H; inv H. split; [reflexivity|]. split; reflexivity. }
  unfold add_new_keypair_model, kp_init, kp_new. cbn [hs_state p_next p_prev p_cur p_set_hs hrx5cr_new p_set_refs].
  rewrite Int.eq_true, Hn, Hp. destruct (eq_dec nullval nullval) as [e|n]; [|congruence].
  cbn [negb proj_sumbool]. rewrite hrx5_B8RA_put0.
  unfold t_replace. cbn [kw_T]. change (t_L (t_add T ?k ?sh ?E)) with (t_L T). rewrite Hvin.
  intros H; inv H. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma hrx5_B8RA_bsw P M ck h a k kc T S1 w :
  p_next P = nullval -> p_prev P = nullval ->
  begin_session_warn (hrx5cr_new P M ck h) (hs_addr a) k kc (mkKW [] T S1) w = w.
Proof.
  intros Hn Hp. unfold begin_session_warn.
  cbn [p_hs p_set_hs p_set_refs hrx5cr_new hs_state].
  rewrite Int.eq_true, orb_true_r. cbn [negb].
  destruct (eq_dec k nullval) as [Hk|Hk]; [reflexivity|].
  change (p_dead (hrx5cr_new P M ck h)) with (p_dead P).
  destruct (p_dead P); [reflexivity|].
  unfold add_new_keypair_warn, kp_init, kp_new. cbn [hs_state p_next p_prev p_cur p_set_hs hrx5cr_new p_set_refs].
  rewrite Int.eq_true, Hn, Hp. destruct (eq_dec nullval nullval) as [e|n]; [|congruence].
  cbn [negb proj_sumbool]. unfold kp_put_warn.
  destruct (eq_dec nullval nullval) as [e'|n]; [reflexivity | congruence].
Qed.

(* the world after the accepted response: the shim's allocation failures, the log, the warnings, the peer's
   reference count *)
Lemma hrx5_B8RA_pure (D D1: device) (T: tstate) (PS: list (val * share * peer)) (S S1: shim) (w: list int64)
  (kc lul lul1: int64) (a: val) (P: peer) (M: resp_msg) (ck h: list byte) (d: rxdraw) (sp: val) (len: int) :
  vin (hs_addr a) (t_L T) = true ->
  0 < Int.unsigned (p_refs P) < 2147483647 ->
  p_cur P = nullval -> p_prev P = nullval -> p_next P = nullval ->
  s_fails S1 = s_fails S ->
  let W1 := rx_resp_accepted (hrx5_W0 D T PS S w kc lul) D1 S1 lul1 a (hrx5cr_new P M ck h) (rd_k d) sp len in
  Int64.eq (s_fails (rw_S W1)) (s_fails S) = hrx5_B8R_alloc d /\
  rx_authenticated_b (rw_rx W1) a sp len Int.zero (if hrx5_B8R_sess d P then Int.one else Int.zero) = true /\
  rx_peer (rw_rx W1) = a /\ rx_eskb (rw_rx W1) = sp /\
  rw_w W1 = w /\
  exists P', rw_PS W1 = supd PS a P' /\ p_refs P' = p_refs P.
Proof.
  intros Hvin Hr Hc Hp Hn Hf W1. subst W1.
  destruct (hrx5_B8RA_rc _ Hr) as (E1 & E2 & E3).
  unfold rx_resp_accepted, hrx5_W0.
  cbn [rw_rx rw_kc rw_KS rw_T rw_PS rw_w rw_S kw_KS kw_T kw_S].
  rewrite hrx5_B8RA_bsw by assumption.
  destruct (bs_res (hrx5cr_new P M ck h) a (rd_k d) kc [] T S1) as [[[ok P2] W2] kc2] eqn:HB.
  destruct (hrx5_B8RA_bs _ _ _ _ _ _ _ _ _ _ _ _ _ Hn Hp Hvin HB) as (Hok & HP2 & HS2).
  cbn [fst snd rw_S rw_rx rw_w rw_PS]. rewrite HP2, E1, E2, E3.
  assert (Hsess: ok = hrx5_B8R_sess d P).
  { rewrite Hok. unfold hrx5_B8R_sess, hrx5_B8R_alloc. destruct (eq_dec (rd_k d) nullval); reflexivity. }
  rewrite Hsess.
  destruct (hrx5_B8RA_log a sp len (hrx5_B8R_sess d P)) as (L1 & L2 & L3).
  split.
  { rewrite HS2, Hf. unfold hrx5_B8R_alloc.
    destruct (eq_dec (rd_k d) nullval); [apply hrx5_B8RA_succ | apply Int64.eq_true]. }
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [reflexivity|].
  eexists; split; reflexivity.
Qed.
