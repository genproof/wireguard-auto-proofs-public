(* law keypairs: the prologue A (statements 0..28 of main): from main's start to the loop's entry. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.keypairs.hkp5_op1.
Require Import WgNoise.proof.harness.keypairs.hkp5_spec.
Require Import WgNoise.proof.harness.keypairs.hkp5_segA_defs.
Require Import WgNoise.proof.harness.keypairs.hkp5_segA_1.
Require Import WgNoise.proof.harness.keypairs.hkp5_segA_2a.
Require Import WgNoise.proof.harness.keypairs.hkp5_segA_2b.
Require Import WgNoise.proof.harness.keypairs.hkp5_segA_3a.
Require Import WgNoise.proof.harness.keypairs.hkp5_segA_3b.
Require Import WgNoise.proof.harness.keypairs.hkp5_segA_4.
Require Import WgNoise.proof.harness.keypairs.hkp5_segA_pure.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

(* the end of the prologue: hkp5A_S4 is the loop's entry *)
Lemma hkp5A_close x25519 (F: hkp5_fix) (FR: mpred) Delta :
  ENTAIL Delta, hkp5A_S4 x25519 F FR |-- hkp5_PA x25519 F FR.
Proof.
  unfold hkp5A_S4. Intros R P S w NS PS KE T head steps.
  assert_PROP (itable_wf T) as HwfT.
  { go_lowerx. unfold prot_repr3.itable. normalize. }
  destruct (hkp5A_pure_ok F R S w P NS PS KE T head H H0 HwfT H1) as (Hfix & Hinv & Hoth).
  unfold hkp5_PA.
  Exists (hkp5A_V F R S w P T head) (hkp5A_Y F R S w P T) steps (hkp5A_O NS PS KE T).
  unfold hkp5_temps, hkp5_SEP, hkp5_world, hkp5_hglobs, hkp5_globs, hkp5_othR, hkp5_oth_rep,
    hkp5A_world, hkp5A_snaps, hkp5A_oth, hkp5A_kes, hkp5A_globs, hkp5A_temps.
  cbn [app fold_right_sepcon y_S y_w y_kc y_P y_KS y_T y_H y_now y_next_id y_id_known y_hsn
       v_RAW v_PUB v_sec v_boot v_allocs0 v_frees0 v_w0 v_OD v_OH v_head v_prefs
       o_hd o_NS o_PS o_kd o_KE o_T0 hkp5A_V hkp5A_Y hkp5A_O].
  change (keypairs_rep W_keypairs []) with (@emp mpred _ _).
  change (hkp5_D x25519 F (hkp5A_V F R S w P T head)) with (hkp5A_D x25519 F R).
  unfold hk5_items; cbn [app]. go_lowerx. entailer!.
Qed.

Lemma hkp5_segA_ok {Espec: OracleKind} x25519 (F: hkp5_fix) (FR: mpred) R :
  x25519_props x25519 ->
  semax (hkp5_Delta (hkp5_G_A x25519)) (hkp5_P0 F FR) hkp5_segA (overridePost (hkp5_PA x25519 F FR) R).
Proof.
  intros HX.
  destruct hkp5A_s_eq as (E1 & E2a & E2b & E3a & E3b & E4).
  rewrite hkp5_segA_eq, hkp5A_cut_eq.
  apply hkp5_seql_app with (Q := hkp5A_S2 x25519 F FR); [discriminate | discriminate | rewrite <- E1; apply hkp5A_1_ok; exact HX |].
  apply hkp5_seql_app with (Q := hkp5A_S2 x25519 F FR); [discriminate | discriminate | rewrite <- E2a; apply hkp5A_2a_ok; exact HX |].
  apply hkp5_seql_app with (Q := hkp5A_S2 x25519 F FR); [discriminate | discriminate | rewrite <- E2b; apply hkp5A_2b_ok; exact HX |].
  apply hkp5_seql_app with (Q := hkp5A_SK x25519 F FR); [discriminate | discriminate | rewrite <- E3a; apply hkp5A_3a_ok; exact HX |].
  apply hkp5_seql_app with (Q := hkp5A_S3 x25519 F FR); [discriminate | discriminate | rewrite <- E3b; apply hkp5A_3b_ok; exact HX |].
  rewrite <- E4.
  eapply semax_post; [| | | | apply (hkp5A_4_ok x25519 F FR R HX)];
    destruct R; unfold overridePost; simpl; intros; try (apply andp_left2; apply derives_refl).
  exact (hkp5A_close x25519 F FR _ x).
Qed.
