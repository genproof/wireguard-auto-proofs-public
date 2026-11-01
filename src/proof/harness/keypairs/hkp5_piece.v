(* law keypairs: main's parts discharged by the proven segment lemmas, and the law's
   own piece (the 9 functions of the harness unit, hkp5_G) from their bodies, each lifted from its small context
   into hkp5_imports W_keypairs ++ hkp5_G = hkp5_Gmain. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.harness.common.hc3_lift.
Require Import WgNoise.proof.harness.keypairs.hkp5_stmts.
Require Import WgNoise.proof.harness.keypairs.hkp5_lem_a.
Require Import WgNoise.proof.harness.keypairs.hkp5_lem_put.
Require Import WgNoise.proof.harness.keypairs.hkp5_mput.
Require Import WgNoise.proof.harness.keypairs.hkp5_pick.
Require Import WgNoise.proof.harness.keypairs.hkp5_rest_body.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_defs.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body.
Require Import WgNoise.proof.harness.keypairs.hkp5_segL0.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp1a.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp1b.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp2.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp3.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp7.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp45.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp6.
Require Import WgNoise.proof.harness.keypairs.hkp5_segLC.
Require Import WgNoise.proof.harness.keypairs.hkp5_segA.
Require Import WgNoise.proof.harness.keypairs.hkp5_segF.
Require Import WgNoise.proof.harness.keypairs.hkp5_bridge.
Require Import WgNoise.proof.harness.keypairs.hkp5_glob.
Require Import WgNoise.proof.harness.keypairs.hkp5_main.

#[local] Existing Instance W_keypairs.

Lemma hkp5_model_facts_ok : hkp5_model_facts.
Proof.
  destruct hkp5_lem_a as (A1 & A2 & A3 & A4). destruct hkp5_lem_put as (B1 & B2).
  exact (conj A1 (conj A2 (conj A3 (conj B1 (conj B2 A4))))).
Qed.

Lemma hkp5_parts_ok : hkp5_parts.
Proof.
  unfold hkp5_parts, hkp5_S_L0, hkp5_S_op, hkp5_S_Op1a, hkp5_S_Op45, hkp5_S_LC, hkp5_S_A, hkp5_S_F, hkp5_S_bridge,
    hkp5_S_glob.
  split; [exact hkp5_model_facts_ok |].
  split; [intros; apply hkp5_segL0_ok |].
  split; [intros; apply hkp5_segOp0_ok; assumption |].
  split; [intros; apply hkp5_segOp1b_ok; assumption |].
  split; [intros; apply hkp5_segOp1a_ok; assumption |].
  split; [intros; apply hkp5_segOp2_ok; assumption |].
  split; [intros; apply hkp5_segOp3_ok; assumption |].
  split; [intros; apply hkp5_segOp7_ok; assumption |].
  split; [intros; apply hkp5_segOp45_ok; assumption |].
  split; [intros; apply hkp5_segOp6_ok; assumption |].
  split; [intros; apply hkp5_segLC_ok; assumption |].
  split; [intros; apply hkp5_segA_ok; assumption |].
  split; [intros; apply hkp5_segF_ok; assumption |].
  split; [intros; apply hkp5_bridge_ok |].
  intros gv Hg. apply hkp5_init_globals; exact Hg.
Qed.

(* a body proved in a small context G0 (each of its entries literally in main's context) *)
Lemma hkp5_pc_lift x25519 aead_enc aead_dec xaead_enc xaead_dec G0 f ip :
  @semax_body hkp5_V G0 W_keypairs f ip ->
  find_internal KC.prog (fst ip) = Some f ->
  hc3_Gsub G0 (hkp5_Gmain x25519 aead_enc aead_dec xaead_enc xaead_dec) ->
  verified_in u_hkp5 (hkp5_imports x25519 aead_enc aead_dec xaead_enc xaead_dec (u_cs u_hkp5) ++ hkp5_G x25519) ip.
Proof.
  intros B F HG. exists f; split; [exact F |].
  eapply semax_body_subsumption; [exact B |].
  apply hc3_tycontext_sub; [exact HG | apply hkp5_br_vsub].
Qed.

Ltac hkp5_pc_G :=
  unfold hc3_Gsub; repeat (apply Forall_cons; [cbv beta; eexists; split; [reflexivity | apply funspec_sub_refl] |]);
  apply Forall_nil.

Theorem hkp5_piece : hkp5_piece_stmt.
Proof.
  intros x25519 aead_enc aead_dec xaead_enc xaead_dec HX HA HXA. split.
  - unfold hkp5_G; simpl. repeat constructor; simpl; intuition discriminate.
  - destruct hkp5_mput_bodies as (Bu & Bg & Bp). destruct hkp5_pick_bodies as (Bl & Bh & Bw).
    unfold hkp5_G.
    repeat apply Forall_cons; try apply Forall_nil; exists u_hkp5; (split; [left; reflexivity |]).
    + refine (hkp5_pc_lift x25519 aead_enc aead_dec xaead_enc xaead_dec [] _ _ Bu _ _); [reflexivity | hkp5_pc_G].
    + refine (hkp5_pc_lift x25519 aead_enc aead_dec xaead_enc xaead_dec [] _ _ Bg _ _); [reflexivity | hkp5_pc_G].
    + refine (hkp5_pc_lift x25519 aead_enc aead_dec xaead_enc xaead_dec hk5_Gm_put _ _ Bp _ _); [reflexivity | hkp5_pc_G].
    + refine (hkp5_pc_lift x25519 aead_enc aead_dec xaead_enc xaead_dec hk5_G_rest_same _ _ hkp5_rest_body _ _); [reflexivity | hkp5_pc_G].
    + refine (hkp5_pc_lift x25519 aead_enc aead_dec xaead_enc xaead_dec [] _ _ Bw _ _); [reflexivity | hkp5_pc_G].
    + refine (hkp5_pc_lift x25519 aead_enc aead_dec xaead_enc xaead_dec hkc5_G _ _ (hkp5_check_body x25519) _ _); [reflexivity | hkp5_pc_G].
    + refine (hkp5_pc_lift x25519 aead_enc aead_dec xaead_enc xaead_dec hk5_Gpick _ _ Bl _ _); [reflexivity | hkp5_pc_G].
    + refine (hkp5_pc_lift x25519 aead_enc aead_dec xaead_enc xaead_dec hk5_Gpick _ _ Bh _ _); [reflexivity | hkp5_pc_G].
    + exists KC.f_main. split; [reflexivity |].
      exact (hkp5_main_body_from x25519 aead_enc aead_dec xaead_enc xaead_dec hkp5_parts_ok HX).
Qed.
