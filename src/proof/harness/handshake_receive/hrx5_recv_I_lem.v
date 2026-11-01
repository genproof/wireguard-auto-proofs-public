(* law handshake_receive, body recv segment I: helpers of hrx5_recv_I.v. *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_recv_lem.
Local Open Scope logic.

(* law handshake_receive, body recv segment I: pure and representation helpers. *)

Lemma hrx5_rvI_len msg : hrx5_fwd msg = true -> Int.eq (hrx5_tw msg) Int.one = true -> Zlength msg = 148.
Proof.
  intros F T. apply Int.same_if_eq in T. unfold hrx5_fwd in F. rewrite T in F.
  apply andb_prop in F as [_ F]. cbn in F. apply Z.eqb_eq. destruct (Zlength msg =? 148); auto.
Qed.

Lemma hrx5_rvI_im_ok msg : Zlength msg = 148 -> im_ok (im_of msg).
Proof. intros H. unfold im_ok, im_of; cbn [im_eph im_encs im_enct im_mac1 im_mac2]. repeat split; list_solve. Qed.

Lemma hrx5_rvI_bytes msg : Zlength msg = 148 -> init_bytes (im_of msg) = msg.
Proof.
  intros H. unfold init_bytes, im_of; cbn [im_type im_sender im_eph im_encs im_enct im_mac1 im_mac2].
  rewrite !hrx5_rvl_le32_inv by list_solve.
  rewrite !sublist_rejoin by lia. rewrite <- H. apply sublist_same; lia.
Qed.

Section NoiseCS.
#[local] Existing Instance Noise.CS.

Lemma hrx5_rvI_fc p : malloc_compatible 148 p -> field_compatible t_init [] p.
Proof. intros Hm. apply malloc_compatible_field_compatible; [exact Hm | reflexivity | reflexivity]. Qed.

Lemma hrx5_rvI_init sh msg p : Zlength msg = 148 -> malloc_compatible (Zlength msg) p ->
  bytes_at sh msg p = init_rep sh p (im_of msg).
Proof.
  intros H Hm. rewrite H in Hm. unfold init_rep.
  rewrite prop_true_andp by (apply hrx5_rvI_im_ok; auto).
  rewrite prot_rep3_init_eq by (auto using hrx5_rvI_fc, hrx5_rvI_im_ok).
  rewrite hrx5_rvI_bytes by auto. reflexivity.
Qed.

(* peer_rep = its device field * the rest *)
Definition hrx5_rvI_prest (sh: share) (p: val) (P: peer) : mpred :=
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

Lemma hrx5_rvI_peer_split sh p P :
  peer_rep sh p P = rx_pfield sh p (p_device P) * hrx5_rvI_prest sh p P.
Proof.
  unfold peer_rep, hrx5_rvI_prest, rx_pfield.
  apply pred_ext; Intros; entailer!.
Qed.
Lemma hrx5_rvI_vp sh p d : readable_share sh -> rx_pfield sh p d |-- valid_pointer p.
Proof.
  intros Hr. unfold rx_pfield. apply field_at_valid_ptr0.
  - apply readable_nonidentity; auto.
  - reflexivity.
  - reflexivity.
Qed.
End NoiseCS.

(* the model *)
Lemma hrx5_rvI_pk_find PS pub a P : pk_find PS pub = Some (a, P) -> In a (saddrs PS).
Proof.
  induction PS as [|[[x shx] Q] PS IH]; simpl; intros H; [discriminate|].
  destruct (bytes_eqb _ _); [inv H; auto | auto].
Qed.

Lemma hrx5_rvI_cin_in x25519 aead_dec D PS M S a P1 :
  cin_res x25519 aead_dec D PS M S = Some (a, P1) -> In a (saddrs PS).
Proof.
  unfold cin_res, consume_initiation_model. intros H.
  destruct (negb _); [discriminate|].
  destruct (consume_init_stage1 _ _ _ _) as [[[[s0 x] ck1] h1]|]; [|discriminate].
  destruct (pk_find PS s0) as [[a0 P]|] eqn:HF; [|discriminate].
  destruct (peer_get P); [|discriminate].
  destruct (consume_init_stage2 _ _ _ _ _) as [[[t ck2] h2]|]; [|discriminate].
  destruct (_ || _)%bool; [discriminate|]. inv H. eapply hrx5_rvI_pk_find; eauto.
Qed.

Section Assoc.
Context {A: Type}.
Lemma hrx5_rvI_sfind_supd (l: list (val * share * A)) a sh v0 v :
  sfind l a = Some (sh, v0) -> sfind (supd l a v) a = Some (sh, v).
Proof.
  induction l as [|[[x shx] w] l IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); simpl.
  - inv H. destruct (EqDec_val a a); [reflexivity | congruence].
  - destruct (EqDec_val x a); [congruence | auto].
Qed.
Lemma hrx5_rvI_supd_supd (l: list (val * share * A)) a v w : supd (supd l a v) a w = supd l a w.
Proof.
  induction l as [|[[x shx] u] l IH]; simpl; [reflexivity|].
  destruct (EqDec_val x a); simpl.
  - destruct (EqDec_val x a); [reflexivity | congruence].
  - destruct (EqDec_val x a); [congruence | rewrite IH; reflexivity].
Qed.
End Assoc.

Lemma hrx5_rvI_wf PS a sh P : peers_wf PS -> sfind PS a = Some (sh, P) -> writable_share sh.
Proof.
  intros Hwf Hf. apply prot_rep3_sfind_In in Hf. unfold peers_wf in Hwf.
  rewrite Forall_forall in Hwf. exact (Hwf _ Hf).
Qed.

Section Model.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_rvI_model W q sp s msg d :
  Int.eq (hrx5_tw msg) Int.one = true -> hrx5_rv_cons W q s msg (rd_r d) = true ->
  rx_packet x25519 aead_dec xaead_enc xaead_dec W q sp s msg d =
  match cin_res x25519 aead_dec (rw_D (hrx5_rv_W1 W q s msg (rd_r d))) (rw_PS W) (im_of msg)
          (rw_S (hrx5_rv_W1 W q s msg (rd_r d))) with
  | None => hrx5_rv_W1 W q s msg (rd_r d)
  | Some (a, P1) => rx_init_accepted W (rw_D (hrx5_rv_W1 W q s msg (rd_r d)))
                      (rw_S (hrx5_rv_W1 W q s msg (rd_r d))) (rw_lul (hrx5_rv_W1 W q s msg (rd_r d))) a P1 sp (sk_len s)
  end.
Proof.
  intros T C. apply Int.same_if_eq in T.
  unfold hrx5_rv_cons, hrx5_rv_vm, hrx5_rv_ul in C.
  unfold rx_packet, hrx5_rv_W1, hrx5_rv_vm, hrx5_rv_ul, hrx5_rv_lul. cbv zeta. rewrite T.
  change (Int.eq Int.one (Int.repr 3)) with false. change (Int.eq Int.one Int.one) with true. cbv iota.
  rewrite C. cbn [rw_D rw_S rw_lul]. reflexivity.
Qed.

Lemma hrx5_rvI_tail W D1 S1 lul a P1 sp len sh P :
  sfind (rw_PS W) a = Some (sh, P) ->
  rx_init_accepted W D1 S1 lul a P1 sp len =
  hrx5_rv_tailw (mkRW D1 (rw_T W) (supd (rw_PS W) a P1) (rw_KS W) S1 (rw_w W) (rw_kc W) lul
                   (rx_send_response (rx_set_endpoint (rw_rx W) a sp) a)) a len.
Proof.
  intros Hf. unfold hrx5_rv_tailw. cbn [rw_PS rw_D rw_T rw_KS rw_S rw_w rw_kc rw_lul rw_rx].
  rewrite (hrx5_rvI_sfind_supd _ _ _ _ P1 Hf). rewrite hrx5_rvI_supd_supd. reflexivity.
Qed.
End Model.

Lemma hrx5_rvI_peer_set X a sp : rx_peer X = nullval -> rx_peer (rx_set_endpoint X a sp) = a.
Proof.
  intros Hx. unfold rx_set_endpoint, rx_note. cbn [rx_peer]. rewrite Hx.
  destruct (eq_dec nullval nullval); [reflexivity | congruence].
Qed.

Lemma hrx5_rvI_tail_ok W D1 S1 lul a P1 sp sh P :
  a <> nullval -> rx_peer (rw_rx W) = nullval -> sfind (rw_PS W) a = Some (sh, P) -> writable_share sh ->
  hrx5_rv_tail_ok (mkRW D1 (rw_T W) (supd (rw_PS W) a P1) (rw_KS W) S1 (rw_w W) (rw_kc W) lul
                     (rx_send_response (rx_set_endpoint (rw_rx W) a sp) a)) a.
Proof.
  intros Ha Hx Hf Hw. unfold hrx5_rv_tail_ok. cbn [rw_PS rw_rx]. split; [exact Ha|]. split.
  - unfold rx_send_response, rx_set_endpoint, rx_note. cbn [rx_peer]. rewrite Hx.
    destruct (eq_dec nullval nullval); [|congruence]. cbn [rx_peer].
    destruct (eq_dec a nullval); [congruence|]. destruct (eq_dec a a); [reflexivity|congruence].
  - exists sh, P1. split; [eapply hrx5_rvI_sfind_supd; eauto | exact Hw].
Qed.
