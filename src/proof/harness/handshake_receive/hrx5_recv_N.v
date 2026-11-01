(* law handshake_receive, body recv:
   segment N of wg_receive_handshake_packet: the cookie reply sent under load (cases 1 and 2): wg_packet_send_handshake_cookie, return.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_recv_defs.
Require Import WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_recv_lem.
Local Open Scope logic.

#[local] Existing Instance HRX.

Definition hrx5_rvN_hide : Type := compspecs.

Lemma hrx5_rvN_fc_sub m p k n : 0 <= k -> 0 <= n -> k + n <= m -> malloc_compatible m p ->
  @field_compatible Noise.CS (tarray tuchar n) [] (offset_val k p).
Proof.
  intros Hk Hn Hkn Hm. destruct p; try contradiction. destruct Hm as [Ha Hs].
  pose proof (Ptrofs.unsigned_range i).
  assert (Hu: Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr k)) = Ptrofs.unsigned i + k).
  { rewrite Ptrofs.add_unsigned, (Ptrofs.unsigned_repr k) by rep_lia. rewrite Ptrofs.unsigned_repr; rep_lia. }
  repeat split; auto.
  - simpl. rewrite Hu, Z.max_r by lia. lia.
  - apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l].
Qed.

(* the message bytes = bytes 0..4 * the sender index (field of the message struct) * bytes 8.. *)
Lemma hrx5_rvN_bytes3 sh msg p : 8 <= Zlength msg -> malloc_compatible (Zlength msg) p ->
  bytes_at sh msg p =
  bytes_at sh (sublist 0 4 msg) p * bytes_at sh (sublist 4 8 msg) (offset_val 4 p) *
  bytes_at sh (sublist 8 (Zlength msg) msg) (offset_val 8 p).
Proof.
  intros Hn Hm.
  assert (FCa: @field_compatible Noise.CS (tarray tuchar (Zlength msg)) [] p).
  { destruct p; try contradiction. destruct Hm as [Ha Hs].
    repeat split; auto.
    - simpl. rewrite Z.max_r by lia. lia.
    - apply align_compatible_rec_Tarray. intros.
      eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  rewrite <- (sublist_same 0 (Zlength msg) msg) at 1 by auto.
  rewrite (sublist_split 0 4 (Zlength msg)) by lia.
  rewrite prot_rep3_bytes_app
    by (rewrite !Zlength_sublist by lia; replace (4 - 0 + (Zlength msg - 4)) with (Zlength msg) by lia; exact FCa).
  rewrite Zlength_sublist by lia. replace (4 - 0) with 4 by lia.
  rewrite (sublist_split 4 8 (Zlength msg)) by lia.
  rewrite (prot_rep3_bytes_app_at sh _ _ p 4 8 4 (Zlength msg - 8)) by
    (rewrite ?Zlength_sublist by lia; try lia; apply (hrx5_rvN_fc_sub (Zlength msg)); auto; lia).
  rewrite sepcon_assoc. reflexivity.
Qed.

Lemma hrx5_rvN_w4_u32 sh msg p : 8 <= Zlength msg -> malloc_compatible (Zlength msg) p ->
  bytes_at sh (sublist 4 8 msg) (offset_val 4 p) = @data_at HRX sh tuint (Vint (hrx5_w4 msg)) (offset_val 4 p).
Proof.
  intros Hn Hm.
  assert (FCu: @field_compatible HRX tuint [] (offset_val 4 p)).
  { destruct p; try contradiction. destruct Hm as [Ha Hs]. pose proof (Ptrofs.unsigned_range i).
    assert (Hu: Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 4)) = Ptrofs.unsigned i + 4).
    { rewrite Ptrofs.add_unsigned, (Ptrofs.unsigned_repr 4) by rep_lia. rewrite Ptrofs.unsigned_repr; rep_lia. }
    repeat split; auto.
    - simpl. rewrite Hu. lia.
    - eapply align_compatible_rec_by_value; [reflexivity |]. simpl. rewrite Hu.
      apply Z.divide_add_r; [| apply Z.divide_refl].
      eapply Z.divide_trans; [| exact Ha]. exists 2. reflexivity. }
  rewrite (prot_rep3_u32_le sh _ _ FCu). unfold hrx5_w4. rewrite hrx5_rvl_le32_inv by list_solve.
  unfold bytes_at. rewrite Zlength_sublist by lia. replace (8 - 4) with 4 by lia.
  apply data_at_tarray_tuchar_cs.
Qed.

Lemma hrx5_rvN_fc_init p : malloc_compatible 148 p ->
  @field_compatible HRX (Tstruct HRC._message_handshake_initiation noattr) [] p.
Proof. intros Hm. apply malloc_compatible_field_compatible; [exact Hm | reflexivity | reflexivity]. Qed.

Lemma hrx5_rvN_fc_resp p : malloc_compatible 92 p ->
  @field_compatible HRX (Tstruct HRC._message_handshake_response noattr) [] p.
Proof. intros Hm. apply malloc_compatible_field_compatible; [exact Hm | reflexivity | reflexivity]. Qed.

Lemma hrx5_rvN_fld_init sh v p : @field_compatible HRX (Tstruct HRC._message_handshake_initiation noattr) [] p ->
  @field_at HRX sh (Tstruct HRC._message_handshake_initiation noattr) (DOT HRC._sender_index) v p =
  @data_at HRX sh tuint v (offset_val 4 p).
Proof.
  intros FC. rewrite field_at_data_at, field_compatible_field_address by auto with field_compatible.
  reflexivity.
Qed.

Lemma hrx5_rvN_fld_resp sh v p : @field_compatible HRX (Tstruct HRC._message_handshake_response noattr) [] p ->
  @field_at HRX sh (Tstruct HRC._message_handshake_response noattr) (DOT HRC._sender_index) v p =
  @data_at HRX sh tuint v (offset_val 4 p).
Proof.
  intros FC. rewrite field_at_data_at, field_compatible_field_address by auto with field_compatible.
  reflexivity.
Qed.

Lemma hrx5_rvN_len1 msg : hrx5_fwd msg = true -> Int.eq (hrx5_tw msg) Int.one = true -> Zlength msg = 148.
Proof.
  unfold hrx5_fwd. intros H E. apply int_eq_e in E. rewrite E in H.
  change (Int.eq Int.one (Int.repr 2)) with false in H. change (Int.eq Int.one (Int.repr 3)) with false in H.
  rewrite Int.eq_true in H. cbn [andb orb] in H.
  rewrite andb_true_iff in H. destruct H as [_ H]. rewrite !orb_false_r in H. apply Z.eqb_eq in H. exact H.
Qed.

Lemma hrx5_rvN_len2 msg : hrx5_fwd msg = true -> Int.eq (hrx5_tw msg) (Int.repr 2) = true -> Zlength msg = 92.
Proof.
  unfold hrx5_fwd. intros H E. apply int_eq_e in E. rewrite E in H.
  change (Int.eq (Int.repr 2) Int.one) with false in H. change (Int.eq (Int.repr 2) (Int.repr 3)) with false in H.
  rewrite Int.eq_true in H. cbn [andb orb] in H.
  rewrite andb_true_iff in H. destruct H as [_ H]. rewrite !orb_false_r in H. apply Z.eqb_eq in H. exact H.
Qed.

#[local] Instance hrx5_rvN_CCE_n2h : change_composite_env Noise.CS HRX.
Proof. make_cs_preserve Noise.CS HRX. Defined.

Lemma hrx5_rvN_fc_dev wg : @field_compatible Noise.CS t_dev [] wg -> @field_compatible HRX t_dev [] wg.
Proof. intros. apply (@field_compatible_change_composite Noise.CS HRX _ t_dev); [prove_cs_preserve_type | auto]. Qed.

(* the world after the cookie reply: rx_packet's needs-cookie branch *)
Definition hrx5_rvN_world (xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte)
  (W1: rxw) (s: skb) (msg nonce r2: list byte) : rxw :=
  let CC := d_cc (rw_D W1) in let S := rw_S W1 in let idx := hrx5_w4 msg in
  mkRW (dev_set_cc (rw_D W1) (snd (mc_res xaead_enc CC s idx nonce msg S r2))) (rw_T W1) (rw_PS W1) (rw_KS W1)
       (if checker_rotates CC (s_boot S) then shim_draw (shim_draw S nonce) r2 else shim_draw S nonce)
       (rw_w W1) (rw_kc W1) (rw_lul W1) (rx_send_cookie (rw_rx W1) idx).

Lemma hrx5_rvN_model x25519 aead_dec xaead_enc xaead_dec W q sp s msg r nonce r2 :
  Int.eq (hrx5_tw msg) (Int.repr 3) = false -> hrx5_rv_nc W q s msg r = true ->
  rx_packet x25519 aead_dec xaead_enc xaead_dec W q sp s msg (mkRD r nonce r2 nullval) =
  hrx5_rvN_world xaead_enc (hrx5_rv_W1 W q s msg r) s msg nonce r2.
Proof.
  intros H3 Hnc. unfold rx_packet, hrx5_rvN_world, hrx5_rv_W1.
  unfold hrx5_rv_nc, hrx5_rv_vm, hrx5_rv_ul, hrx5_rv_lul in *.
  rewrite H3. cbn [rd_r rd_nonce rd_r2 rw_D rw_S rw_T rw_PS rw_KS rw_w rw_kc rw_lul rw_rx].
  destruct (load_model q (rw_lul W) (s_boot (rw_S W))) as [ul lul]. cbn [fst snd] in *.
  destruct (validate_model (d_cc (rw_D W)) s msg ul (s_boot (rw_S W)) (s_rlallow (rw_S W)) r) as [v CC1].
  cbn [fst snd] in *.
  assert (Hc: rx_consumes ul v = false).
  { unfold rx_needs_cookie, rx_consumes in *. destruct ul; cbn in *; [| discriminate].
    apply Z.eqb_eq in Hnc. subst v. reflexivity. }
  rewrite Hc, Hnc.
  destruct (validate_rotates (d_cc (rw_D W)) msg ul (s_boot (rw_S W))); reflexivity.
Qed.

Lemma hrx5_rv_N1_ok : hrx5_rv_N1_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec CSw gv W q shd wg head shs sp s shm msg r HY.
  change hrx5_rvN_hide in CSw.
  unfold hrx5_rv_Delta, hrx5_rv_SC, hrx5_rv_NC1, hrx5_rv_retonly, hrx5_rv_R, hrx5_rv_post.
  simplify_func_tycontext. abbreviate_semax.
  destruct HY as (Hx & Ha & Hxa & Hshd & Hshs & Hshm & Hfwd & [Hlen Hmc] & Hok).
  Intros. rename H into Hr, H0 into Htw, H1 into Hnc.
  assert (H148: Zlength msg = 148) by (apply hrx5_rvN_len1; auto).
  rewrite (hrx5_rvN_bytes3 shm msg (sk_data s)) by (auto; lia).
  rewrite (hrx5_rvN_w4_u32 shm msg (sk_data s)) by (auto; lia).
  rewrite <- (hrx5_rvN_fld_init shm _ (sk_data s)) by (apply hrx5_rvN_fc_init; rewrite <- H148; auto).
  Intros.
  forward.
  rewrite (hrx5_rvN_fld_init shm _ (sk_data s)) by (apply hrx5_rvN_fc_init; rewrite <- H148; auto).
  rewrite <- (hrx5_rvN_w4_u32 shm msg (sk_data s)) by (auto; lia).
  gather_SEP 3 4 5. rewrite <- sepcon_assoc. rewrite <- (hrx5_rvN_bytes3 shm msg (sk_data s)) by (auto; lia).
  remember (hrx5_rv_W1 W q s msg r) as W1 eqn:EW1.
  unfold rxw_rep, device_rep. Intros.
  forward_call (gv, rw_S W1, rw_w W1, rw_rx W1, shd, wg, d_cc (rw_D W1), shs, sp, s, shm, msg, hrx5_w4 msg).
  { apply hrx5_rvN_fc_dev; auto. }
  Intros vret. destruct vret as [nonce r2]. cbn [fst snd] in *.
  forward.
  Exists (mkRD r nonce r2 nullval).
  rewrite hrx5_rvN_model by (auto; apply int_eq_e in Htw; rewrite Htw; reflexivity).
  unfold rxw_rep, hrx5_rvN_world, device_rep.
  cbn [rw_D rw_T rw_PS rw_KS rw_S rw_w rw_kc rw_lul rw_rx dev_set_cc d_dev d_id d_cc d_ptab d_itab].
  entailer!.
  unfold rxdraw_ok; cbn [rd_r rd_nonce rd_r2 rd_k]. repeat split; auto; congruence.
Qed.

Lemma hrx5_rv_N2_ok : hrx5_rv_N2_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec CSw gv W q shd wg head shs sp s shm msg r HY.
  change hrx5_rvN_hide in CSw.
  unfold hrx5_rv_Delta, hrx5_rv_SC, hrx5_rv_NC2, hrx5_rv_retonly, hrx5_rv_R, hrx5_rv_post.
  simplify_func_tycontext. abbreviate_semax.
  destruct HY as (Hx & Ha & Hxa & Hshd & Hshs & Hshm & Hfwd & [Hlen Hmc] & Hok).
  Intros. rename H into Hr, H0 into Htw, H1 into Hnc.
  assert (H92: Zlength msg = 92) by (apply hrx5_rvN_len2; auto).
  rewrite (hrx5_rvN_bytes3 shm msg (sk_data s)) by (auto; lia).
  rewrite (hrx5_rvN_w4_u32 shm msg (sk_data s)) by (auto; lia).
  rewrite <- (hrx5_rvN_fld_resp shm _ (sk_data s)) by (apply hrx5_rvN_fc_resp; rewrite <- H92; auto).
  Intros.
  forward.
  rewrite (hrx5_rvN_fld_resp shm _ (sk_data s)) by (apply hrx5_rvN_fc_resp; rewrite <- H92; auto).
  rewrite <- (hrx5_rvN_w4_u32 shm msg (sk_data s)) by (auto; lia).
  gather_SEP 3 4 5. rewrite <- sepcon_assoc. rewrite <- (hrx5_rvN_bytes3 shm msg (sk_data s)) by (auto; lia).
  remember (hrx5_rv_W1 W q s msg r) as W1 eqn:EW1.
  unfold rxw_rep, device_rep. Intros.
  forward_call (gv, rw_S W1, rw_w W1, rw_rx W1, shd, wg, d_cc (rw_D W1), shs, sp, s, shm, msg, hrx5_w4 msg).
  { apply hrx5_rvN_fc_dev; auto. }
  Intros vret. destruct vret as [nonce r2]. cbn [fst snd] in *.
  forward.
  Exists (mkRD r nonce r2 nullval).
  rewrite hrx5_rvN_model by (auto; apply int_eq_e in Htw; rewrite Htw; reflexivity).
  unfold rxw_rep, hrx5_rvN_world, device_rep.
  cbn [rw_D rw_T rw_PS rw_KS rw_S rw_w rw_kc rw_lul rw_rx dev_set_cc d_dev d_id d_cc d_ptab d_itab].
  entailer!.
  unfold rxdraw_ok; cbn [rd_r rd_nonce rd_r2 rd_k]. repeat split; auto; congruence.
Qed.

(* the child's target *)
Lemma hrx5_rv_N_ok : hrx5_rv_N1_stmt /\ hrx5_rv_N2_stmt.
Proof. exact (conj hrx5_rv_N1_ok hrx5_rv_N2_ok). Qed.
