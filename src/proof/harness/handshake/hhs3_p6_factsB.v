(* law handshake, phase P6: pure lemma (B side after P4).
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

(* consume_initiation on a one-peer list: the accepted peer is that peer with one more reference and a new
   handshake keeping the static identity, with the message's sender index as remote index *)
Lemma hhs3_p6_factsB_cin x25519 aead_dec ID a sh P0 M now a' P' :
  consume_initiation_model x25519 aead_dec ID [(a, sh, P0)] M now = Some (a', P') ->
  exists H', P' = p_set_hs (p_set_refs P0 (rc_add1 (p_refs P0))) H' /\
             hs_sid H' = hs_sid (p_hs P0) /\ hs_rindex H' = im_sender M.
Proof.
  intros H. unfold consume_initiation_model in H. cbv zeta in H. simpl pk_find in H. unfold peer_get in H.
  repeat match goal with
         | Hh: context [match ?e with _ => _ end] |- _ => destruct e eqn:?; try discriminate
         end;
  repeat match goal with
         | Hh: Some _ = Some _ |- _ => inversion Hh; clear Hh; subst
         end;
  eexists; (split; [reflexivity | split; reflexivity]).
Qed.

(* create_response succeeded: state CREATED_RESPONSE, remote index and identity kept, sender = idx *)
Lemma hhs3_p6_factsB_cr x25519 aead_enc H M r idx M' H' :
  create_response_model x25519 aead_enc H M r idx = (true, M', H') ->
  hs_state H' = HS_CREATED_RESPONSE /\ hs_rindex H' = hs_rindex H /\ hs_sid H' = hs_sid H /\ rm_sender M' = idx.
Proof.
  intros E. unfold create_response_model in E. cbv zeta in E.
  repeat match type of E with
         | context [if ?c then _ else _] => destruct c eqn:?; try discriminate
         end.
  inversion E; subst. repeat split; reflexivity.
Qed.

Lemma hhs3_p6_factsB_ok x25519 aead_enc aead_dec : hhs3_p6_factsB_stmt x25519 aead_enc aead_dec.
Proof.
  intros Hx Ha L V HC.
  destruct HC as (_ & _ & _ & (Hcin & _) & (Hcr & _) & _ & _).
  unfold hhs3_cr in Hcr. apply hhs3_p6_factsB_cr in Hcr. destruct Hcr as (Hst & Hri & Hsid & Hsnd).
  unfold hhs3_cin in Hcin. apply hhs3_p6_factsB_cin in Hcin. destruct Hcin as (H' & HPA & Hsid' & Hri').
  unfold hhs3_PA2 in Hri, Hsid. cbn [p_hs p_set_refs] in Hri, Hsid.
  rewrite HPA in Hri, Hsid |- *. cbn [p_hs p_set_hs p_set_refs p_dead p_cur p_prev p_next p_device] in *.
  rewrite Hri, Hsid, Hsid', Hri'.
  repeat split; try assumption; reflexivity.
Qed.
