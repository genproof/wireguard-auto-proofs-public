(* law handshake_receive, body recv:
   helpers of segment T (hrx5_recv_T.v).
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_recv_lem.
Local Open Scope logic.

Section NoiseCS.
#[local] Existing Instance Noise.CS.

(* peer_rep = its device field * its reference count * the rest *)
Definition hrx5_rvT_prest (sh: share) (p: val) (P: peer) : mpred :=
  !! field_compatible t_peer [] p &&
  (field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   field_at sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   field_at sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   field_at sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Lemma hrx5_rvT_peer_split sh p P :
  peer_rep sh p P = rx_pfield sh p (p_device P) * peer_refs_rep sh p (p_refs P) * hrx5_rvT_prest sh p P.
Proof.
  unfold peer_rep, hrx5_rvT_prest, rx_pfield, peer_refs_rep.
  apply pred_ext; Intros; entailer!.
Qed.

Lemma hrx5_rvT_prest_refs sh p P r : hrx5_rvT_prest sh p (p_set_refs P r) = hrx5_rvT_prest sh p P.
Proof. reflexivity. Qed.

Lemma hrx5_rvT_vp sh p d : readable_share sh -> rx_pfield sh p d |-- valid_pointer p.
Proof.
  intros Hr. unfold rx_pfield. apply field_at_valid_ptr0.
  - apply readable_nonidentity; auto.
  - reflexivity.
  - reflexivity.
Qed.
End NoiseCS.

Section Assoc.
Context {A: Type}.
Lemma hrx5_rvT_sfind_supd (l: list (val * share * A)) a sh v0 v :
  sfind l a = Some (sh, v0) -> sfind (supd l a v) a = Some (sh, v).
Proof.
  induction l as [|[[x shx] w] l IH]; simpl; intros H; [discriminate|].
  destruct (EqDec_val x a); simpl.
  - inv H. destruct (EqDec_val a a); [reflexivity | congruence].
  - destruct (EqDec_val x a); [congruence | auto].
Qed.
Lemma hrx5_rvT_sdel_supd (l: list (val * share * A)) a v : sdel (supd l a v) a = sdel l a.
Proof.
  induction l as [|[[x shx] u] l IH]; simpl; [reflexivity|].
  destruct (EqDec_val x a); simpl.
  - destruct (EqDec_val x a); [reflexivity | congruence].
  - destruct (EqDec_val x a); [congruence | rewrite IH; reflexivity].
Qed.
End Assoc.

(* the log: the peer stays a *)
Lemma hrx5_rvT_note X p : rx_peer X = p -> rx_peer (rx_note X p) = p.
Proof.
  intros H. unfold rx_note. destruct (eq_dec (rx_peer X) nullval); [reflexivity|].
  destruct (eq_dec (rx_peer X) p); [exact H | congruence].
Qed.
Lemma hrx5_rvT_stats X p len : rx_peer X = p -> rx_peer (rx_update_stats X p len) = p.
Proof. intros H. unfold rx_update_stats. apply hrx5_rvT_note. exact H. Qed.
Lemma hrx5_rvT_recv X p : rx_peer X = p -> rx_peer (rx_auth_received X p) = p.
Proof. intros H. unfold rx_auth_received. apply hrx5_rvT_note. exact H. Qed.
