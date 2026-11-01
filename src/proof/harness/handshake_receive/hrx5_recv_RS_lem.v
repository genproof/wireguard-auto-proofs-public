(* law handshake_receive, body recv segment RS: helpers of hrx5_recv_RS.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_recv_lem.
Local Open Scope logic.

(* ---- the message: 92 bytes, its struct ---- *)

Lemma hrx5_rvRS_len msg : hrx5_fwd msg = true -> Int.eq (hrx5_tw msg) (Int.repr 2) = true -> Zlength msg = 92.
Proof.
  intros F T. apply Int.same_if_eq in T. unfold hrx5_fwd in F. rewrite T in F.
  apply andb_prop in F as [_ F]. cbn in F. apply Z.eqb_eq. destruct (Zlength msg =? 92); auto.
Qed.

Lemma hrx5_rvRS_rm_ok msg : Zlength msg = 92 -> rm_ok (rm_of msg).
Proof. intros H. unfold rm_ok, rm_of; cbn [rm_eph rm_encn rm_mac1 rm_mac2]. repeat split; list_solve. Qed.

Lemma hrx5_rvRS_bytes msg : Zlength msg = 92 -> resp_bytes (rm_of msg) = msg.
Proof.
  intros H. unfold resp_bytes, rm_of; cbn [rm_type rm_sender rm_receiver rm_eph rm_encn rm_mac1 rm_mac2].
  rewrite !hrx5_rvl_le32_inv by list_solve.
  rewrite !sublist_rejoin by lia. rewrite <- H. apply sublist_same; lia.
Qed.

Section NoiseCS.
#[local] Existing Instance Noise.CS.

Lemma hrx5_rvRS_fc p : malloc_compatible 92 p -> field_compatible t_resp [] p.
Proof. intros Hm. apply malloc_compatible_field_compatible; [exact Hm | reflexivity | reflexivity]. Qed.

Lemma hrx5_rvRS_resp sh msg p : Zlength msg = 92 -> malloc_compatible (Zlength msg) p ->
  bytes_at sh msg p = resp_rep sh p (rm_of msg).
Proof.
  intros H Hm. rewrite H in Hm. unfold resp_rep.
  rewrite prop_true_andp by (apply hrx5_rvRS_rm_ok; auto).
  rewrite prot_rep3_resp_eq by (auto using hrx5_rvRS_fc, hrx5_rvRS_rm_ok).
  rewrite hrx5_rvRS_bytes by auto. reflexivity.
Qed.

(* peer_rep = its device field * the rest *)
Definition hrx5_rvRS_prest (sh: share) (p: val) (P: peer) : mpred :=
  !! field_compatible t_peer [] p &&
  (field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   field_at sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   field_at sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   field_at sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   field_at sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Lemma hrx5_rvRS_peer_split sh p P :
  peer_rep sh p P = rx_pfield sh p (p_device P) * hrx5_rvRS_prest sh p P.
Proof.
  unfold peer_rep, hrx5_rvRS_prest, rx_pfield.
  apply pred_ext; Intros; entailer!.
Qed.
End NoiseCS.

Lemma hrx5_rvRS_pfield_valid sh p d :
  readable_share sh -> rx_pfield sh p d |-- valid_pointer p.
Proof.
  intros Hsh. unfold rx_pfield.
  apply field_at_valid_ptr0.
  - apply readable_nonidentity; auto.
  - reflexivity.
  - reflexivity.
Qed.

(* ---- association lists ---- *)

Section Assoc.
Context {A: Type}.
Lemma hrx5_rvRS_sfind_supd (l: list (val * share * A)) a sh v0 v :
  sfind l a = Some (sh, v0) -> sfind (supd l a v) a = Some (sh, v).
Proof.
  induction l as [|[[x shx] w] l IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); simpl.
  - inv H. destruct (EqDec_val a a); [reflexivity | congruence].
  - destruct (EqDec_val x a); [congruence | auto].
Qed.
Lemma hrx5_rvRS_supd_supd (l: list (val * share * A)) a v w : supd (supd l a v) a w = supd l a w.
Proof.
  induction l as [|[[x shx] u] l IH]; simpl; [reflexivity|].
  destruct (EqDec_val x a); simpl.
  - destruct (EqDec_val x a); [reflexivity | congruence].
  - destruct (EqDec_val x a); [congruence | rewrite IH; reflexivity].
Qed.
Lemma hrx5_rvRS_sdel_supd (l: list (val * share * A)) a v : sdel (supd l a v) a = sdel l a.
Proof.
  induction l as [|[[x shx] u] l IH]; simpl; [reflexivity|].
  destruct (EqDec_val x a); simpl.
  - destruct (EqDec_val x a); [reflexivity | congruence].
  - destruct (EqDec_val x a); [congruence | rewrite IH; reflexivity].
Qed.
End Assoc.

Lemma hrx5_rvRS_wf PS a sh P : peers_wf PS -> sfind PS a = Some (sh, P) -> writable_share sh.
Proof.
  intros Hwf Hf. apply prot_rep3_sfind_In in Hf. unfold peers_wf in Hwf.
  rewrite Forall_forall in Hwf. exact (Hwf _ Hf).
Qed.

Lemma hrx5_rvRS_pok wg T PS a sh P : Forall (rx_peer_ok wg T) PS -> sfind PS a = Some (sh, P) ->
  rx_peer_ok wg T (a, sh, P).
Proof.
  intros Hall Hf. apply prot_rep3_sfind_In in Hf. rewrite Forall_forall in Hall. exact (Hall _ Hf).
Qed.

(* peers_rep over supd: the updated item * the rest *)
Lemma hrx5_rvRS_peers_supd PS a sh P P1 : sfind PS a = Some (sh, P) ->
  peers_rep (supd PS a P1) = peer_rep sh a P1 * iter_sepcon peer_item_rep (sdel PS a).
Proof.
  intros Hf. unfold peers_rep.
  rewrite (prot_rep3_split (supd PS a P1) a sh P1) by (eapply hrx5_rvRS_sfind_supd; eauto).
  rewrite hrx5_rvRS_sdel_supd. reflexivity.
Qed.

(* ---- the model ---- *)

Section Model.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* consume_response accepts a peer of PS; its state keeps the device and the slots *)
Lemma hrx5_rvRS_cre_in D T PS M a P1 :
  cre_res x25519 aead_dec D T PS M = Some (a, P1) ->
  exists sh P, sfind PS a = Some (sh, P) /\ p_device P1 = p_device P /\ p_cur P1 = p_cur P /\
    p_prev P1 = p_prev P /\ p_next P1 = p_next P.
Proof.
  unfold cre_res, consume_response_model. intros H.
  destruct (negb _); [discriminate|].
  destruct (t_lookup _ _ _) as [[x E]|]; [|discriminate].
  destruct (sfind PS (e_peer E)) as [[sh P]|] eqn:HF; [|discriminate].
  destruct (peer_get P) as [P0|] eqn:HG; [|discriminate].
  destruct (negb _); [discriminate|].
  destruct (consume_resp_crypto _ _ _ _ _) as [[ck h]|]; [|discriminate].
  inv H. exists sh, P. split; [exact HF|].
  unfold peer_get in HG. destruct (Int.eq _ _); [discriminate|]. inv HG.
  unfold p_set_hs, p_set_refs. cbn. auto.
Qed.

Lemma hrx5_rvRS_model W q sp s msg d :
  Int.eq (hrx5_tw msg) (Int.repr 2) = true -> hrx5_rv_cons W q s msg (rd_r d) = true ->
  rx_packet x25519 aead_dec xaead_enc xaead_dec W q sp s msg d =
  match cre_res x25519 aead_dec (rw_D (hrx5_rv_W1 W q s msg (rd_r d))) (rw_T W) (rw_PS W) (rm_of msg) with
  | None => hrx5_rv_W1 W q s msg (rd_r d)
  | Some (a, P1) => rx_resp_accepted W (rw_D (hrx5_rv_W1 W q s msg (rd_r d)))
                      (rw_S (hrx5_rv_W1 W q s msg (rd_r d))) (rw_lul (hrx5_rv_W1 W q s msg (rd_r d))) a P1
                      (rd_k d) sp (sk_len s)
  end.
Proof.
  intros T C. apply Int.same_if_eq in T.
  unfold hrx5_rv_cons, hrx5_rv_vm, hrx5_rv_ul in C.
  unfold rx_packet, hrx5_rv_W1, hrx5_rv_vm, hrx5_rv_ul, hrx5_rv_lul. cbv zeta. rewrite T.
  change (Int.eq (Int.repr 2) (Int.repr 3)) with false. change (Int.eq (Int.repr 2) Int.one) with false.
  cbv iota. rewrite C. cbn [rw_D rw_S rw_lul]. reflexivity.
Qed.

(* the world before the tail *)
Definition hrx5_rvRS_W2 (W: rxw) (D1: device) (S1: shim) (lul: int64) (a: val) (P1: peer) (k: val) (sp: val)
  : rxw :=
  let X1 := rx_set_endpoint (rw_rx W) a sp in
  let B := bs_res P1 a k (rw_kc W) (rw_KS W) (rw_T W) S1 in
  let ok := fst (fst (fst B)) in
  let P2 := snd (fst (fst B)) in
  let W2 := snd (fst B) in
  let w2 := begin_session_warn P1 (hs_addr a) k (rw_kc W) (mkKW (rw_KS W) (rw_T W) S1) (rw_w W) in
  let X2 := if ok then rx_send_keepalive (rx_handshake_complete (rx_session_derived X1 a) a) a else X1 in
  mkRW D1 (kw_T W2) (supd (rw_PS W) a P2) (kw_KS W2) (kw_S W2) w2 (snd B) lul X2.

Lemma hrx5_rvRS_tail W D1 S1 lul a P1 k sp len sh P :
  sfind (rw_PS W) a = Some (sh, P) ->
  rx_resp_accepted W D1 S1 lul a P1 k sp len = hrx5_rv_tailw (hrx5_rvRS_W2 W D1 S1 lul a P1 k sp) a len.
Proof.
  intros Hf. unfold hrx5_rv_tailw, hrx5_rvRS_W2, rx_resp_accepted.
  cbn [rw_PS rw_D rw_T rw_KS rw_S rw_w rw_kc rw_lul rw_rx].
  rewrite (hrx5_rvRS_sfind_supd _ _ _ _ _ Hf). rewrite hrx5_rvRS_supd_supd. reflexivity.
Qed.

Lemma hrx5_rvRS_note_same X a : rx_peer X = nullval \/ rx_peer X = a -> a <> nullval ->
  rx_peer (rx_note X a) = a.
Proof.
  intros [H|H] Ha; unfold rx_note.
  - rewrite H. destruct (eq_dec nullval nullval); [reflexivity|congruence].
  - destruct (eq_dec (rx_peer X) nullval); [reflexivity|]. rewrite if_true by auto. exact H.
Qed.

Lemma hrx5_rvRS_tail_ok W D1 S1 lul a P1 k sp sh P :
  a <> nullval -> rx_peer (rw_rx W) = nullval -> sfind (rw_PS W) a = Some (sh, P) -> writable_share sh ->
  hrx5_rv_tail_ok (hrx5_rvRS_W2 W D1 S1 lul a P1 k sp) a.
Proof.
  intros Ha Hx Hf Hw. unfold hrx5_rv_tail_ok, hrx5_rvRS_W2. cbn [rw_PS rw_rx]. split; [exact Ha|]. split.
  - assert (E1: rx_peer (rx_set_endpoint (rw_rx W) a sp) = a).
    { unfold rx_set_endpoint. apply hrx5_rvRS_note_same; auto. }
    destruct (fst (fst (fst _))); [|exact E1].
    unfold rx_send_keepalive, rx_handshake_complete, rx_session_derived.
    apply hrx5_rvRS_note_same; [cbn [rx_peer]|auto]. right.
    apply hrx5_rvRS_note_same; [cbn [rx_peer]|auto]. right.
    apply hrx5_rvRS_note_same; [cbn [rx_peer]|auto]. right. exact E1.
  - eexists sh, _. split; [eapply hrx5_rvRS_sfind_supd; eauto | exact Hw].
Qed.
End Model.
