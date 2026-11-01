(* law handshake_receive: B8 branch R segment B: the pure facts of the three cases (G, FF, FA, FS).
*)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_defs.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* reference counts                                                        *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B8RBP_rc r : 0 < Int.unsigned r < 2147483647 -> rc_sub1 (rc_add1 r) = r.
Proof.
  intros Hr. rewrite rc_add1_small by lia.
  assert (E: Int.unsigned (Int.add r Int.one) = Int.unsigned r + 1).
  { unfold Int.add. rewrite Int.unsigned_one, Int.unsigned_repr; [reflexivity|rep_lia]. }
  unfold rc_sub1, rc_neg.
  assert (H1: Int.ltu (Int.add r Int.one) (Int.repr 2147483648) = true).
  { unfold Int.ltu. rewrite E, Int.unsigned_repr by (cbn; lia). destruct (zlt _ _); [reflexivity|lia]. }
  assert (H2: Int.eq (Int.add r Int.one) Int.one = false).
  { unfold Int.eq. rewrite E, Int.unsigned_one. destruct (zeq _ _); [lia|reflexivity]. }
  assert (H3: Int.eq (Int.add r Int.one) Int.zero = false).
  { unfold Int.eq. rewrite E, Int.unsigned_zero. destruct (zeq _ _); [lia|reflexivity]. }
  rewrite H1, H2, H3. cbn [negb andb orb].
  rewrite Int.add_commut, Int.sub_add_l, Int.sub_idem, Int.add_zero_l. reflexivity.
Qed.

Lemma hrx5_B8RBP_rc_nz r : 0 < Int.unsigned r -> Int.eq r Int.zero = false.
Proof. intros H. unfold Int.eq. rewrite Int.unsigned_zero. destruct (zeq _ _); [lia|reflexivity]. Qed.

(* ---------------------------------------------------------------------- *)
(* lists of addresses                                                      *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B8RBP_vrep_in h k L : In h L -> In k (vreplace h k L).
Proof.
  induction L as [|x L IH]; simpl; [tauto|]. intros Hin.
  destruct (EqDec_val x h) as [->|Hne]; [left; reflexivity|].
  right. apply IH. destruct Hin as [->|?]; [contradiction|assumption].
Qed.

Lemma hrx5_B8RBP_vrep_notin h k L : NoDup L -> k <> h -> ~ In h (vreplace h k L).
Proof.
  induction L as [|x L IH]; simpl; [tauto|]. intros HN Hk.
  inv HN. destruct (EqDec_val x h) as [->|Hne].
  - simpl. intros [?|?]; [congruence|contradiction].
  - simpl. intros [?|?]; [congruence|]. apply IH; assumption.
Qed.

Lemma hrx5_B8RBP_vrep_k h k L : NoDup (vreplace h k L) -> In h L -> k <> h -> ~ In k L.
Proof.
  induction L as [|x L IH]; simpl; [tauto|]. intros HN Hin Hk.
  destruct (EqDec_val x h) as [->|Hne].
  - inv HN. intros [?|?]; [congruence|contradiction].
  - inv HN. destruct Hin as [->|Hin]; [contradiction|].
    intros [->|HkL].
    + apply H1. apply hrx5_B8RBP_vrep_in. assumption.
    + apply (IH H2 Hin Hk HkL).
Qed.

Lemma hrx5_B8RBP_vremove_notin a L : ~ In a L -> vremove a L = L.
Proof.
  induction L as [|x L IH]; simpl; [reflexivity|]. intros Hn.
  destruct (EqDec_val x a) as [->|Hne]; [exfalso; tauto|]. f_equal. apply IH. tauto.
Qed.

Lemma hrx5_B8RBP_vremove_idem a L : vremove a (vremove a L) = vremove a L.
Proof.
  induction L as [|x L IH]; simpl; [reflexivity|].
  destruct (EqDec_val x a) as [->|Hne]; [exact IH|]. simpl. destruct (EqDec_val x a); [contradiction|]. f_equal; exact IH.
Qed.

Lemma hrx5_B8RBP_vremove_vrep h k L : NoDup L -> ~ In k L -> vremove k (vreplace h k L) = vremove h L.
Proof.
  induction L as [|x L IH]; simpl; [reflexivity|]. intros HN Hk. inv HN.
  destruct (EqDec_val x h) as [->|Hne].
  - simpl. destruct (EqDec_val k k); [|congruence].
    rewrite !hrx5_B8RBP_vremove_notin by tauto. reflexivity.
  - simpl. destruct (EqDec_val x k) as [->|Hxk]; [exfalso; tauto|]. f_equal. apply IH; tauto.
Qed.

(* ---------------------------------------------------------------------- *)
(* the target's handshake entry                                            *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B8RBP_find_L T L idx x E : t_find_index T L idx = Some (x, E) -> In x L.
Proof.
  induction L as [|b L IH]; simpl; [discriminate|].
  destruct (t_entry T b) eqn:HE; [|intros H; right; auto].
  destruct (Int.eq (e_index e) idx); [intros H; inv H; left; reflexivity | intros H; right; auto].
Qed.

Lemma hrx5_B8RBP_tgt x25519 aead_dec IA T KA PS M a P ck h :
  hrx5cr_tgt x25519 aead_dec IA T PS M = Some (a, P, ck, h) -> hrx5cr_pool KA PS T ->
  sfind (t_D T) (hs_addr a) = Some (Ews, t_entry_d T (hs_addr a)) /\ vin (hs_addr a) (t_L T) = true /\
  e_peer (t_entry_d T (hs_addr a)) = a /\ e_type (t_entry_d T (hs_addr a)) = IDX_HANDSHAKE.
Proof.
  intros Ht [H1 H2]. unfold hrx5cr_tgt in Ht. destruct (mi_ok IA); [|discriminate].
  destruct (t_find_index T (t_L T) (rm_receiver M)) as [[x E]|] eqn:Hf; [|discriminate].
  destruct (Int.eq (e_type E) IDX_HANDSHAKE) eqn:Hty; [|discriminate].
  destruct (sfind PS (e_peer E)) as [[sh P0]|]; [|discriminate].
  destruct (Int.eq (hs_state (p_hs P0)) _); [|discriminate].
  destruct (m_consume_response_model _ _ _ _ _ _ _ _ _) as [[ck0 h0]|]; [|discriminate].
  inv Ht.
  pose proof (hrx5cr_model_find_in _ _ _ _ _ Hf) as HE.
  pose proof (hrx5_B8RBP_find_L _ _ _ _ _ Hf) as HL.
  unfold t_entry in HE. destruct (sfind (t_D T) x) as [[shx Ex]|] eqn:Hs; [|discriminate]. inv HE.
  pose proof (hrx5cr_model_sfind_in _ _ _ _ Hs) as HIn.
  rewrite <- (firstn_skipn (length KA) (t_D T)) in HIn.
  apply in_app_or in HIn as [HIn|HIn].
  - destruct (hrx5cr_model_F2_in_r _ _ _ _ H1 HIn) as [K [_ HK]]. simpl in HK.
    destruct HK as (_ & _ & _ & HK). rewrite HK in Hty. vm_compute in Hty. discriminate.
  - destruct (hrx5cr_model_F2_in_r _ _ _ _ H2 HIn) as [[[p sp] P1] [_ HK]]. simpl in HK.
    destruct HK as (-> & -> & Hp & HT). subst p.
    unfold t_entry_d, t_entry. rewrite Hs. split; [reflexivity|]. split; [|split; auto].
    unfold vin. destruct (in_dec _ _ _); [reflexivity|contradiction].
Qed.

(* ---------------------------------------------------------------------- *)
(* begin_session on the accepted peer                                      *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B8RBP_cr : negb (orb (Int.eq HS_CONSUMED_RESPONSE HS_CREATED_RESPONSE)
  (Int.eq HS_CONSUMED_RESPONSE HS_CONSUMED_RESPONSE)) = false.
Proof. reflexivity. Qed.

(* destruct the first decision on equality in the goal *)
Ltac hrx5_B8RBP_dec :=
  match goal with |- context [?e] =>
    match type of e with sumbool (?x = ?y) _ => destruct e; try contradiction; try congruence end end.

Lemma hrx5_B8RBP_state P M ck h : hs_state (p_hs (hrx5cr_new P M ck h)) = HS_CONSUMED_RESPONSE.
Proof. reflexivity. Qed.

Lemma hrx5_B8RBP_bs_null P M ck h hs kc W :
  begin_session_model (hrx5cr_new P M ck h) hs nullval kc W =
  (false, hrx5cr_new P M ck h, mkKW (kw_KS W) (kw_T W) (shim_alloc_fail (kw_S W)), kc).
Proof.
  unfold begin_session_model. rewrite hrx5_B8RBP_state. cbv [negb orb Int.eq HS_CONSUMED_RESPONSE HS_CREATED_RESPONSE].
  rewrite !Int.unsigned_repr by (cbn; lia). cbn [zeq]. destruct (EqDec_val nullval nullval); [|congruence].
  simpl. reflexivity.
Qed.

Lemma hrx5_B8RBP_bs_dead P M ck h hs k kc W :
  k <> nullval -> p_dead P = true ->
  begin_session_model (hrx5cr_new P M ck h) hs k kc W =
  (false, p_set_hs (hrx5cr_new P M ck h) (hs_zero (p_hs (hrx5cr_new P M ck h))),
   mkKW (kw_KS W) (kw_T W) (shim_free (shim_alloc_ok (kw_S W))), Int64.add kc Int64.one).
Proof.
  intros Hk Hd. unfold begin_session_model. rewrite hrx5_B8RBP_state.
  rewrite hrx5_B8RBP_cr. hrx5_B8RBP_dec.
  cbv zeta. replace (p_dead (hrx5cr_new P M ck h)) with true by (rewrite <- Hd; reflexivity). reflexivity.
Qed.

Lemma hrx5_B8RBP_put_null u W : kp_put nullval u W = W.
Proof. unfold kp_put. hrx5_B8RBP_dec; reflexivity. Qed.

Lemma hrx5_B8RBP_epeer W hs E : t_entry (kw_T W) hs = Some E -> e_peer_of_hs W hs = e_peer E.
Proof. intros H. unfold e_peer_of_hs. rewrite H. reflexivity. Qed.

Lemma hrx5_B8RBP_bs_sess P M ck h hs k kc T S1 a :
  k <> nullval -> p_dead P = false -> p_cur P = nullval -> p_prev P = nullval -> p_next P = nullval ->
  vin hs (t_L T) = true -> e_peer_of_hs (mkKW [] T S1) hs = a ->
  begin_session_model (hrx5cr_new P M ck h) hs k kc (mkKW [] T S1) =
  (true, p_set_slots (p_set_hs (hrx5cr_new P M ck h) (hs_zero (p_hs (hrx5cr_new P M ck h)))) k nullval nullval,
   mkKW [(k, kp_new (p_hs (hrx5cr_new P M ck h)) (Int64.add kc Int64.one) (s_boot S1))]
     (snd (t_replace (t_add T k Ews (mkEntry a IDX_KEYPAIR Int.zero)) hs k)) (shim_alloc_ok S1),
   Int64.add kc Int64.one).
Proof.
  intros Hk Hd Hc Hp Hn Hv He. unfold begin_session_model. rewrite hrx5_B8RBP_state.
  rewrite hrx5_B8RBP_cr. hrx5_B8RBP_dec.
  cbv zeta. replace (p_dead (hrx5cr_new P M ck h)) with false by (rewrite <- Hd; reflexivity).
  rewrite He. cbn [kw_KS kw_T kw_S].
  unfold add_new_keypair_model.
  replace (kp_init (kp_new (p_hs (hrx5cr_new P M ck h)) (Int64.add kc Int64.one) (s_boot S1))) with true
    by (unfold kp_new; rewrite hrx5_B8RBP_state; reflexivity).
  replace (p_next (p_set_hs (hrx5cr_new P M ck h) (hs_zero (p_hs (hrx5cr_new P M ck h))))) with nullval
    by (rewrite <- Hn; reflexivity).
  replace (p_prev (p_set_hs (hrx5cr_new P M ck h) (hs_zero (p_hs (hrx5cr_new P M ck h))))) with nullval
    by (rewrite <- Hp; reflexivity).
  replace (p_cur (p_set_hs (hrx5cr_new P M ck h) (hs_zero (p_hs (hrx5cr_new P M ck h))))) with nullval
    by (rewrite <- Hc; reflexivity).
  rewrite !hrx5_B8RBP_put_null.
  match goal with |- context [if negb ?b then _ else _] => destruct (negb b) end;
  cbv beta iota; unfold t_replace; cbn [kw_T t_add t_L kw_KS kw_S]; rewrite Hv; reflexivity.
Qed.

(* the table after the session's replace *)
Lemma hrx5_B8RBP_T3 T a k E :
  vin (hs_addr a) (t_L T) = true -> k <> hs_addr a -> t_entry T (hs_addr a) = Some E ->
  hrx5_B8RB_T3 T a k = mkT ((k, Ews, mkEntry a IDX_KEYPAIR (e_index E)) :: t_D T) (vreplace (hs_addr a) k (t_L T)).
Proof.
  intros Hv Hk HE. unfold hrx5_B8RB_T3, t_replace. cbn [t_add t_L]. rewrite Hv.
  unfold t_entry at 1. unfold t_add at 2. cbn [t_D sfind]. destruct (eq_dec k (hs_addr a)); [contradiction|].
  unfold t_entry in HE. destruct (sfind (t_D T) (hs_addr a)) as [[sh E0]|]; [|discriminate]. inv HE.
  unfold t_set_index, t_entry, t_upd, t_add. cbn [t_D sfind supd snd fst]. destruct (eq_dec k k); [|congruence].
  cbn [t_D supd]. destruct (eq_dec k k); [|congruence]. reflexivity.
Qed.

(* the world after consume_response accepted and begin_session ran *)
Lemma hrx5_B8RBP_resp W D1 S1 lul a P1 k sp len ok P2 W2 kc2 r0 :
  bs_res P1 a k (rw_kc W) (rw_KS W) (rw_T W) S1 = (ok, P2, W2, kc2) ->
  rc_sub1 (p_refs P2) = r0 -> Int.eq r0 Int.zero = false ->
  let W' := rx_resp_accepted W D1 S1 lul a P1 k sp len in
  rw_D W' = D1 /\ rw_T W' = kw_T W2 /\ rw_PS W' = supd (rw_PS W) a (p_set_refs P2 r0) /\
  rw_KS W' = kw_KS W2 /\ rw_S W' = kw_S W2.
Proof.
  intros HB Hr Hz W'. subst W'. unfold rx_resp_accepted. cbv zeta. rewrite HB. cbn [fst snd rw_D rw_T rw_PS rw_KS rw_S].
  rewrite Hr, Hz. auto.
Qed.

Lemma hrx5_B8RBP_eta W : W = mkRW (rw_D W) (rw_T W) (rw_PS W) (rw_KS W) (rw_S W) (rw_w W) (rw_kc W) (rw_lul W) (rw_rx W).
Proof. destruct W; reflexivity. Qed.

(* begin_session's zeroing *)
Lemma hrx5_B8RBP_bytes_refl b : bytes_eqb b b = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec _ _ _); congruence. Qed.

Lemma hrx5_B8RBP_zeroed T0 T1 x E P M ck h :
  zeroed_from (snap_of T0 x E (p_hs P)) (snap_of T1 x E (hs_zero (p_hs (hrx5cr_new P M ck h)))) = true.
Proof.
  unfold zeroed_from, snap_of, hs_zero, hrx5cr_new. cbn [sn_hs sn_entry p_hs p_set_hs p_set_refs
    hs_state hs_rindex hs_eph hs_reph hs_hash hs_ck hs_lic hs_sid hs_rstatic hs_ss hs_psk hs_ts].
  rewrite !hrx5_B8RBP_bytes_refl, !Int.eq_true, Int64.eq_true.
  destruct (eq_dec (e_peer E) (e_peer E)); [|congruence].
  destruct (eq_dec (hs_sid (p_hs P)) (hs_sid (p_hs P))); [|congruence].
  replace (is_zero (zeros 32)) with true by (vm_compute; reflexivity). reflexivity.
Qed.

(* wg_noise_keypairs_clear after a session: the one keypair (refs 1) is freed *)
Lemma hrx5_B8RBP_rc1 : Int.eq (rc_sub1 Int.one) Int.zero = true.
Proof. reflexivity. Qed.

Lemma hrx5_B8RBP_clear Z k K T3 S' :
  k <> nullval -> kp_refs K = Int.one ->
  keypairs_clear_model (p_set_slots Z k nullval nullval) (mkKW [(k, K)] T3 S') =
  (p_set_slots Z nullval nullval nullval, mkKW [] (t_free (t_remove T3 k) k) (shim_free S')).
Proof.
  intros Hk HK. unfold keypairs_clear_model. cbn [p_set_slots p_next p_prev p_cur].
  rewrite !hrx5_B8RBP_put_null. unfold kp_put. destruct (eq_dec k nullval); [contradiction|].
  cbn [kw_KS kw_T kw_S afind]. destruct (eq_dec k k); [|congruence].
  rewrite HK, hrx5_B8RBP_rc1. cbn [adel]. destruct (eq_dec k k); [|congruence].
  unfold p_set_slots. cbn. reflexivity.
Qed.

Lemma hrx5_B8RBP_clear_warn Z k K T3 S' w :
  kp_refs K = Int.one ->
  keypairs_clear_warn (p_set_slots Z k nullval nullval) (mkKW [(k, K)] T3 S') w = w.
Proof.
  intros HK. unfold keypairs_clear_warn. cbn [p_set_slots p_next p_prev p_cur].
  rewrite !hrx5_B8RBP_put_null. cbn [kw_KS].
  rewrite !kp_put_warn_small; [reflexivity | ..];
  intros K0 HE; cbn [afind] in HE;
    match type of HE with context [eq_dec ?x ?y] => destruct (eq_dec x y) end; inv HE;
    rewrite HK, Int.unsigned_one; lia.
Qed.

(* the shim after validate: the counters are S's *)
Lemma hrx5_B8RBP_S1 D S q lul msg d :
  let S1 := hrx5_B8R_S1 D S q lul msg d in
  s_allocs S1 = s_allocs S /\ s_fails S1 = s_fails S /\ s_frees S1 = s_frees S.
Proof. unfold hrx5_B8R_S1. destruct (validate_rotates _ _ _ _); cbn; auto. Qed.

Lemma hrx5_B8RBP_snapped T NS PS j :
  0 <= j < Zlength PS -> Zlength NS = Zlength PS ->
  Znth j (hnodes_snapped4 T NS PS) = hn_snapshot4 T (Znth j NS) (Znth j PS).
Proof.
  intros Hj HL. unfold hnodes_snapped4.
  revert j PS Hj HL. induction NS as [|N NS IH]; intros j [|x PS] Hj HL;
    rewrite ?Zlength_nil, ?Zlength_cons in *; try lia.
  cbn [combine map]. destruct (zeq j 0) as [->|Hne].
  - rewrite !Znth_0_cons. destruct x as [[p sh] P]. reflexivity.
  - rewrite !Znth_pos_cons by lia. apply IH; lia.
Qed.

Ltac hrx5_B8RBP_eta_tac :=
  match goal with |- _ = ?W1 =>
    transitivity (mkRW (rw_D W1) (rw_T W1) (rw_PS W1) (rw_KS W1) (rw_S W1) (rw_w W1) (rw_kc W1) (rw_lul W1)
                    (rw_rx W1));
    [| symmetry; apply hrx5_B8RBP_eta] end.

Lemma hrx5_B8RB_pure_ok : hrx5_B8RB_pure_stmt.
Proof.
  unfold hrx5_B8RB_pure_stmt.
  intros x25519 aead_enc aead_dec xaead_enc xaead_dec L R sec birth S w NS PS T head nk KE st i kc lul q proto
    ip4 ip6 port o dp tg ai ar d a P M ck h j HY Hb Hinv Hst Hi Hok Hmc Hacc Hd HF.
  cbv zeta. intros Hwf.
  cbn [fold_right] in HF.
  destruct HF as (Ho & Hfwd & Hai & Har & Ht & Hj & HZ & Hnp & Htg & HW1 & _).
  rewrite HW1 in Hwf |- *. clear HW1.
  change (hrx5_B8RB_S1 x25519 R L sec birth S q lul o d) with
    (hrx5_B8R_S1 (hrx5_DL x25519 R L sec birth) S q lul (obj_bytes o) d).
  pose proof (hrx5_B8RBP_S1 (hrx5_DL x25519 R L sec birth) S q lul (obj_bytes o) d) as HS1. cbv zeta in HS1.
  set (S1 := hrx5_B8R_S1 (hrx5_DL x25519 R L sec birth) S q lul (obj_bytes o) d) in *.
  set (D1 := hrx5_B8R_D1 (hrx5_DL x25519 R L sec birth) S q lul (hrx5_skb dp o proto ip4 ip6 port) (obj_bytes o) d)
    in *.
  set (lul1 := hrx5_B8R_lul1 S q lul) in *.
  set (len := sk_len (hrx5_skb dp o proto ip4 ip6 port)) in *.
  clearbody S1 D1 lul1 len.
  (* the peer and its entry *)
  assert (Hpok: hrx5_pok x25519 R L (a, Ews, P)).
  { destruct Hinv as (HFa & _). rewrite Forall_forall in HFa. apply HFa. rewrite <- HZ. apply Znth_In. exact Hj. }
  destruct Hpok as (_ & _ & _ & _ & _ & Hrefs & _ & _ & Hc & Hp & Hn).
  assert (HNL: Zlength NS = Zlength PS).
  { destruct Hinv as (_ & _ & _ & _ & Hnp' & _). unfold hnodes_peers4 in Hnp'.
    rewrite <- (Zlength_map _ _ hn_p NS), Hnp', Zlength_map. reflexivity. }
  destruct (hrx5_B8RBP_tgt _ _ _ _ _ _ _ _ _ _ _ Ht (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hinv)))))))
    as (Hsf & Hvin & Hep & Hety).
  assert (HE: t_entry T (hs_addr a) = Some (t_entry_d T (hs_addr a))) by (unfold t_entry; rewrite Hsf; reflexivity).
  assert (Hin: In (hs_addr a) (saddrs (t_D T))).
  { unfold saddrs. apply (in_map (fun '(x, _, _) => x) _ _ (hrx5cr_model_sfind_in _ _ _ _ Hsf)). }
  pose proof (hrx5_B8RBP_rc _ Hrefs) as Hrc.
  pose proof (hrx5_B8RBP_rc_nz (p_refs P) (proj1 Hrefs)) as Hnz.
  destruct Hd as (_ & _ & _ & Hkf).
  split.
  { unfold hrx5_B8RB_G. cbn [fold_right].
    rewrite hrx5_B8RBP_snapped, HZ by assumption. unfold hn_snapshot4. rewrite Hnp, <- Htg.
    destruct HS1 as (HS1a & HS1b & HS1c).
    repeat (split; [assumption || reflexivity|]). repeat split; assumption. }
  set (W0 := hrx5_W0 (hrx5_DL x25519 R L sec birth) T PS S w kc lul) in *.
  set (Pn := hrx5cr_new P M ck h) in *.
  unfold hrx5_B8R_Wx, hrx5_B8R_Tf, hrx5_B8R_Sf, hrx5_B8R_Pf, hrx5_B8RB_FF, hrx5_B8RB_FA, hrx5_B8RB_FS, hrx5_B8RB_Pz,
    hrx5_B8R_sess, hrx5_B8R_alloc in *.
  fold Pn.
  destruct (eq_dec (rd_k d) nullval) as [Hk0|Hk0].
  - (* the allocation failed *)
    pose proof (hrx5_B8RBP_resp W0 D1 S1 lul1 a Pn (rd_k d) (l_skb L) len false Pn (mkKW [] T (shim_alloc_fail S1)) kc
      (p_refs P)) as HR.
    destruct HR as (HRD & HRT & HRPS & HRKS & HRS).
    { unfold bs_res. rewrite Hk0. apply hrx5_B8RBP_bs_null. }
    { exact Hrc. }
    { exact Hnz. }
    set (W1 := rx_resp_accepted W0 D1 S1 lul1 a Pn (rd_k d) (l_skb L) len) in *.
    cbn [andb negb].
    split; [|split; intros; discriminate].
    intros _. cbn [fold_right kw_T kw_KS kw_S] in *.
    rewrite HRT, HRPS, HRKS, HRS. repeat (split; [reflexivity|]). split; [|exact I].
    hrx5_B8RBP_eta_tac. rewrite HRT, HRPS, HRKS, HRS. reflexivity.
  - assert (Hka: rd_k d <> hs_addr a) by (intros Heq; apply (Hkf Hk0); rewrite Heq; exact Hin).
    assert (HinL: In (hs_addr a) (t_L T)) by (unfold vin in Hvin; destruct (in_dec _ _ _); [assumption|discriminate]).
    cbn [andb negb].
    split; [intros; discriminate|].
    destruct (p_dead P) eqn:Hdead.
    + (* P dead: zeroed, no session *)
      pose proof (hrx5_B8RBP_resp W0 D1 S1 lul1 a Pn (rd_k d) (l_skb L) len false
        (p_set_hs Pn (hs_zero (p_hs Pn))) (mkKW [] T (shim_free (shim_alloc_ok S1))) (Int64.add kc Int64.one)
        (p_refs P)) as HR.
      destruct HR as (HRD & HRT & HRPS & HRKS & HRS).
      { unfold bs_res. apply hrx5_B8RBP_bs_dead; assumption. }
      { exact Hrc. }
      { exact Hnz. }
      set (W1 := rx_resp_accepted W0 D1 S1 lul1 a Pn (rd_k d) (l_skb L) len) in *.
      cbn [andb negb].
      split; [|intros; discriminate].
      intros _. cbn [fold_right kw_T kw_KS kw_S] in *.
      rewrite HRT, HRPS, HRKS, HRS.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [exact Hin|]. split; [exact Hsf|].
      split; [unfold hs_snap_cur; apply hrx5_B8RBP_zeroed|]. split; [|exact I].
      intros _. hrx5_B8RBP_eta_tac. rewrite HRT, HRPS, HRKS, HRS. reflexivity.
    + (* a session *)
      pose proof (hrx5_B8RBP_T3 T a (rd_k d) _ Hvin Hka HE) as HT3.
      pose proof (hrx5_B8RBP_resp W0 D1 S1 lul1 a Pn (rd_k d) (l_skb L) len true
        (p_set_slots (p_set_hs Pn (hs_zero (p_hs Pn))) (rd_k d) nullval nullval)
        (mkKW [(rd_k d, kp_new (p_hs Pn) (Int64.add kc Int64.one) (s_boot S1))] (hrx5_B8RB_T3 T a (rd_k d))
           (shim_alloc_ok S1)) (Int64.add kc Int64.one)
        (p_refs P)) as HR.
      destruct HR as (HRD & HRT & HRPS & HRKS & HRS).
      { unfold bs_res. apply hrx5_B8RBP_bs_sess; try assumption.
        erewrite hrx5_B8RBP_epeer; [exact Hep | exact HE]. }
      { exact Hrc. }
      { exact Hnz. }
      set (W1 := rx_resp_accepted W0 D1 S1 lul1 a Pn (rd_k d) (l_skb L) len) in *.
      cbn [kw_T kw_KS kw_S] in *.
      assert (Hsf3: sfind (t_D (hrx5_B8RB_T3 T a (rd_k d))) (hs_addr a) = Some (Ews, t_entry_d T (hs_addr a))).
      { rewrite HT3. cbn [t_D sfind]. destruct (eq_dec (rd_k d) (hs_addr a)); [contradiction|exact Hsf]. }
      assert (He3: t_entry_d (hrx5_B8RB_T3 T a (rd_k d)) (hs_addr a) = t_entry_d T (hs_addr a)).
      { unfold t_entry_d, t_entry. rewrite Hsf3. reflexivity. }
      assert (HkL: ~ In (rd_k d) (t_L T)).
      { rewrite HRT, HT3 in Hwf. destruct Hwf as (HND3 & _). cbn [t_L] in HND3.
        exact (hrx5_B8RBP_vrep_k _ _ _ HND3 HinL Hka). }
      cbn [andb negb].
      split.
      * intros _. cbn [fold_right].
        rewrite HRT, HRPS, HRKS, HRS.
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|].
        split; [rewrite HT3; right; exact Hin|]. split; [exact Hsf3|].
        split; [unfold hs_snap_cur; rewrite He3; apply hrx5_B8RBP_zeroed|]. split; [intros; discriminate|exact I].
      * intros _ HND. cbn [fold_right].
        split; [exact Hk0|].
        split; [rewrite HT3; cbn [t_L]; unfold vin; destruct (in_dec _ _ _) as [Hx|]; [|reflexivity];
                exfalso; exact (hrx5_B8RBP_vrep_notin _ _ _ HND Hka Hx)|].
        split; [rewrite HT3; cbn [t_L]; unfold vin; destruct (in_dec _ _ _) as [|Hx]; [reflexivity|];
                exfalso; exact (Hx (hrx5_B8RBP_vrep_in _ _ _ HinL))|].
        split; [rewrite HT3; cbn [t_D sfind]; destruct (eq_dec (rd_k d) (rd_k d)); [reflexivity|congruence]|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split.
        { rewrite hrx5_B8RBP_clear by (auto; reflexivity). f_equal.
          - unfold hrx5_B8R_Pf, hrx5_B8R_alloc. destruct (eq_dec (rd_k d) nullval); [contradiction|].
            unfold p_set_slots, p_set_refs, p_set_hs, Pn, hrx5cr_new. cbn. rewrite Hc, Hp, Hn. reflexivity.
          - f_equal. rewrite HT3. unfold t_free, t_remove. cbn [t_D t_L sdel].
            destruct (eq_dec (rd_k d) (rd_k d)); [|congruence].
            rewrite hrx5_B8RBP_vremove_idem, hrx5_B8RBP_vremove_vrep by assumption. reflexivity. }
        split; [apply hrx5_B8RBP_clear_warn; reflexivity|].
        split; [|exact I].
        rewrite HRS. unfold hrx5_B8R_Pf, hrx5_B8R_alloc. destruct (eq_dec (rd_k d) nullval); [contradiction|].
        reflexivity.
Qed.
