(* law handshake, phase P6: pure lemma (begin_session / keypairs_clear models).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.handshake.hhs3_spec.
Require Import WgNoise.proof.harness.handshake.hhs3_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_conv.
Require Import WgNoise.proof.harness.handshake.hhs3_p6_defs.
Require WgNoise.harness.x_handshake.code.

Local Open Scope Z_scope.

Ltac hhs3_p6_m :=
  repeat (first [rewrite if_true by (reflexivity || (left; reflexivity) || assumption)
                | rewrite if_false by (congruence || assumption)]; cbn beta iota).

(* a one-entry table holding p's hashed handshake entry *)
Lemma hhs3_p6_model_TA1 L I :
  hhs3_TA1 L I = mkT [(hs_addr (l_pb L), Tsh, mkEntry (l_pb L) IDX_HANDSHAKE (i_idx I))] [hs_addr (l_pb L)].
Proof.
  unfold hhs3_TA1, hhs3_TA0, hhs3_EB, t_insert, t_set_index, t_entry, t_upd; simpl. hhs3_p6_m. reflexivity.
Qed.

Lemma hhs3_p6_model_TB1 L Q :
  hhs3_TB1 L Q = mkT [(hs_addr (l_pa L), Tsh, mkEntry (l_pa L) IDX_HANDSHAKE (s_idx Q))] [hs_addr (l_pa L)].
Proof.
  unfold hhs3_TB1, hhs3_TB0, hhs3_EA, t_insert, t_set_index, t_entry, t_upd; simpl. hhs3_p6_m. reflexivity.
Qed.

(* begin_session with a failed allocation *)
Lemma hhs3_p6_model_bs_null P p kc KS T S :
  orb (Int.eq (hs_state (p_hs P)) HS_CREATED_RESPONSE) (Int.eq (hs_state (p_hs P)) HS_CONSUMED_RESPONSE) = true ->
  bs_res P p nullval kc KS T S = (false, P, mkKW KS T (shim_alloc_fail S), kc).
Proof.
  intros H. unfold bs_res, begin_session_model. rewrite H. simpl. hhs3_p6_m. reflexivity.
Qed.

(* begin_session with a fresh keypair k, no keypairs, NULL slots, alive, the handshake entry hashed alone *)
Lemma hhs3_p6_model_bs_ok P p k kc S sh E :
  orb (Int.eq (hs_state (p_hs P)) HS_CREATED_RESPONSE) (Int.eq (hs_state (p_hs P)) HS_CONSUMED_RESPONSE) = true ->
  p_dead P = false -> p_cur P = nullval -> p_prev P = nullval -> p_next P = nullval ->
  k <> nullval -> k <> hs_addr p ->
  bs_res P p k kc [] (mkT [(hs_addr p, sh, E)] [hs_addr p]) S =
  (true,
   p_set_slots (p_set_hs P (hs_zero (p_hs P)))
     (if Int.eq (hs_state (p_hs P)) HS_CONSUMED_RESPONSE then k else nullval) nullval
     (if Int.eq (hs_state (p_hs P)) HS_CONSUMED_RESPONSE then nullval else k),
   mkKW [(k, kp_new (p_hs P) (Int64.add kc Int64.one) (s_boot S))]
        (mkT [(k, Ews, mkEntry (e_peer E) IDX_KEYPAIR (e_index E)); (hs_addr p, sh, E)] [k]) (shim_alloc_ok S),
   Int64.add kc Int64.one).
Proof.
  intros H Hd Hc Hp Hn Hk Hkh. unfold bs_res, begin_session_model. rewrite H. cbn beta iota.
  hhs3_p6_m. rewrite Hd.
  unfold e_peer_of_hs, t_entry; simpl. hhs3_p6_m.
  unfold add_new_keypair_model. simpl kp_init.
  destruct (Int.eq (hs_state (p_hs P)) HS_CONSUMED_RESPONSE) eqn:Ei.
  - simpl. rewrite Hn, Hp, Hc. unfold kp_put. hhs3_p6_m.
    unfold t_replace, vin, t_set_index, t_upd, t_add; simpl. hhs3_p6_m. unfold t_entry; simpl. hhs3_p6_m. reflexivity.
  - simpl. rewrite Hn, Hp, Hc. unfold kp_put. hhs3_p6_m.
    unfold t_replace, vin, t_set_index, t_upd, t_add; simpl. hhs3_p6_m. unfold t_entry; simpl. hhs3_p6_m. reflexivity.
Qed.

(* keypairs_clear with one live keypair (one reference) in the current or the next slot *)
Lemma hhs3_p6_model_clear P k K Ek hs sh E S :
  kp_refs K = Int.one -> k <> nullval -> p_prev P = nullval ->
  ((p_cur P = k /\ p_next P = nullval) \/ (p_cur P = nullval /\ p_next P = k)) ->
  keypairs_clear_model P (mkKW [(k, K)] (mkT [(k, Ews, Ek); (hs, sh, E)] [k]) S) =
  (p_set_slots P nullval nullval nullval, mkKW [] (mkT [(hs, sh, E)] []) (shim_free S)).
Proof.
  intros Hr Hk Hp [[Hc Hn] | [Hc Hn]]; unfold keypairs_clear_model, kp_put; rewrite Hp, Hc, Hn; simpl;
    hhs3_p6_m; rewrite Hr; change (rc_sub1 Int.one) with Int.zero; rewrite Int.eq_true; unfold t_free, t_remove; simpl; hhs3_p6_m; reflexivity.
Qed.

Lemma hhs3_p6_model_ok x25519 aead_enc aead_dec : hhs3_p6_model_stmt x25519 aead_enc aead_dec.
Proof.
  intros Hx Ha L V HC HA HB.
  destruct (HA Hx Ha L V HC) as (HPB & _ & _ & _ & _).
  destruct (HB Hx Ha L V HC) as (Hst & _ & _ & _ & Hdead & Hcur & Hprev & Hnext & _).
  destruct HC as (_ & _ & _ & _ & _ & _ & Hboot).
  assert (FA: hs_state (p_hs (hhs3_p6_PBa V)) = HS_CONSUMED_RESPONSE /\ p_dead (hhs3_p6_PBa V) = false /\
              p_cur (hhs3_p6_PBa V) = nullval /\ p_prev (hhs3_p6_PBa V) = nullval /\
              p_next (hhs3_p6_PBa V) = nullval).
  { unfold hhs3_p6_PBa. rewrite HPB. unfold hhs3_p6_PB2n. destruct (w_ST2 V). repeat split; reflexivity. }
  destruct FA as (FA1 & FA2 & FA3 & FA4 & FA5).
  assert (FB: hs_state (p_hs (hhs3_p6_PAa x25519 V)) = HS_CREATED_RESPONSE /\
              p_dead (hhs3_p6_PAa x25519 V) = false /\
              p_cur (hhs3_p6_PAa x25519 V) = nullval /\ p_prev (hhs3_p6_PAa x25519 V) = nullval /\
              p_next (hhs3_p6_PAa x25519 V) = nullval /\ p_hs (hhs3_p6_PAa x25519 V) = w_H2 V).
  { unfold hhs3_p6_PAa, hhs3_PA3, hhs3_PA2. cbn [p_hs p_dead p_cur p_prev p_next p_set_cookie p_set_hs p_set_refs].
    repeat split; assumption || reflexivity. }
  destruct FB as (FB1 & FB2 & FB3 & FB4 & FB5 & FB6).
  split; [| split; [| split; [| split; [| split]]]].
  - unfold hhs3_p6_BA. apply hhs3_p6_model_bs_null. rewrite FA1. reflexivity.
  - intros ka Hk Hnin. unfold hhs3_p6_BA. rewrite hhs3_p6_model_TA1 in *.
    rewrite hhs3_p6_model_bs_ok by (first [assumption | rewrite FA1; reflexivity | intro Hh; apply Hnin; left; congruence]).
    rewrite FA1, Int.eq_true, Int64.add_zero_l, Hboot. reflexivity.
  - unfold hhs3_p6_BB. apply hhs3_p6_model_bs_null. rewrite FB1. reflexivity.
  - intros kb Hk Hnin. unfold hhs3_p6_BB. rewrite hhs3_p6_model_TB1 in *.
    rewrite hhs3_p6_model_bs_ok by (first [assumption | rewrite FB1; reflexivity | intro Hh; apply Hnin; left; congruence]).
    rewrite FB1, FB6. simpl s_boot. rewrite Hboot. reflexivity.
  - intros ka S Hk. unfold hhs3_p6_PB3, hhs3_p6_TA2, hhs3_p6_TA3.
    apply hhs3_p6_model_clear; [reflexivity | assumption | reflexivity | left; split; reflexivity].
  - intros kb S Hk. unfold hhs3_p6_PA4, hhs3_p6_TB2, hhs3_p6_TB3.
    apply hhs3_p6_model_clear; [reflexivity | assumption | reflexivity | right; split; reflexivity].
Qed.
