(* law replay: main's body from its segments: the prologue (initial globals,
   stack frame, mem_mgr), segments A and B, the loop (invariant hrp3_Inv, body L1; L2a; L2b; L3, i++) and
   segment F. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.protocol.prot_prog3.
Require Import WgNoise.proof.harness.common.hc_prog3.
Require Import WgNoise.proof.harness.replay.hrp3_spec.
Require Import WgNoise.proof.harness.replay.hrp3_model.
Require Import WgNoise.proof.harness.replay.hrp3_defs.
Require Import WgNoise.proof.harness.replay.hrp3_init.
Require Import WgNoise.proof.harness.replay.hrp3_close.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.harness.replay.hrp3_segA.
Require Import WgNoise.proof.harness.replay.hrp3_segB.
Require Import WgNoise.proof.harness.replay.hrp3_segF.
Require Import WgNoise.proof.harness.replay.hrp3_segL1.
Require Import WgNoise.proof.harness.replay.hrp3_segL2a.
Require Import WgNoise.proof.harness.replay.hrp3_segL2b.
Require Import WgNoise.proof.harness.replay.hrp3_segL3.
Require WgNoise.contracts.x_replay.
Require WgNoise.harness.x_replay.code.

#[local] Existing Instance W_replay.
Local Open Scope Z_scope.

Lemma hrp3_facts_ok : hrp3_facts.
Proof.
  split; [exact hrp3_model_lemmas |]. split; [exact prot_rep_lemmas3 |]. apply hrp3_close. exact prot_rep_lemmas3.
Qed.

Lemma hrp3_l1w {Espec: OracleKind} {cs: compspecs} Delta P c (Q: Z -> environ -> mpred) (i: Z) R :
  semax Delta P c (loop1_ret_assert (Q i) R) -> semax Delta P c (loop1_ret_assert (EX j: Z, Q j) R).
Proof.
  intros H. eapply semax_post; [| | | | exact H]; destruct R; simpl; intros; try intro rho; apply andp_left2;
    try apply derives_refl; cbv beta; apply (exp_right i); apply derives_refl.
Qed.

Ltac hrp3_unf := unfold hrp3_St, hrp3_temps, hrp3_lvars, hrp3_world, hrp3_globs; simpl app.

Lemma hrp3_main_body x25519 aead_enc aead_dec :
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  @semax_body hrp3_V0 (hrp3_G0 x25519 aead_enc aead_dec) W_replay RC.f_main hrp3_main_spec.
Proof.
  intros Hx Ha. pose proof hrp3_facts_ok as HF.
  unfold hrp3_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply (main_pre_InitGpred (shim_state gv hrp3_S0 * noise_globals_raw gv zeros32 zeros32 Int64.zero *
                              wg_consts gv * hrp3_consts gv * TT)%logic);
    [apply hrp3_init_globals | reflexivity
    | apply Forall_forall; intros x Hx'; vm_compute in Hx'; repeat destruct Hx' as [Hx'|Hx']; try contradiction;
      subst x; vm_compute; exact I | ].
  process_stackframe_of.
  set (FR0 := (TT * has_ext tt)%logic).
  set (F := mkRFix gv v_wa v_wb v_ita v_itb v_pta v_ptb v_pa v_pb v_ia v_ib v_raw_a v_raw_b v_psk v_ss_b
                   v_latest v_ci v_snap).
  eapply semax_pre with (P' := hrp3_P0 F FR0).
  { unfold hrp3_P0, hrp3_lvars. sep_apply (create_mem_mgr gv). unfold FR0. entailer!. unfold F; simpl. cancel. }
  rewrite hrp3_body_eq.
  destruct hrp3_segs_eq as (EA & EB & EF & EL1 & EL2a & EL2b & EL3).
  eapply semax_seq with (Q := FF); [| apply semax_ff].
  eapply hrp3_semax_cut with (Q := hrp3_PA x25519 F FR0);
    [discriminate | rewrite hrp3_overridePost2, <- EA; apply hrp3_segA_ok; auto |].
  eapply hrp3_semax_cut with (Q := hrp3_PB x25519 aead_dec F FR0);
    [discriminate | rewrite hrp3_overridePost2, <- EB; apply hrp3_segB_ok; auto |].
  unfold hrp3_PB at 1. Intros V Y sp ap mp steps.
  eapply hrp3_semax_cut with (Q := hrp3_Inv x25519 aead_dec F V sp ap mp steps FR0);
    [discriminate | rewrite hrp3_overridePost2 | rewrite <- EF; apply hrp3_segF_ok; auto].
  rewrite hrp3_loop_eq, hrp3_loop_shape.
  abbreviate_semax.
  forward.
  forward_loop (hrp3_Inv x25519 aead_dec F V sp ap mp steps FR0)
    continue: (EX i: Z, hrp3_Icont x25519 aead_dec F V sp ap mp steps FR0 i)%argsassert
    break: (hrp3_Inv x25519 aead_dec F V sp ap mp steps FR0).
  - (* entry *)
    unfold hrp3_Inv. Exists 0 Y. hrp3_unf. entailer!.
  - (* body *)
    unfold hrp3_Inv at 1. Intros i Y0. hrp3_unf. Intros.
    forward_if (EX Y: hrp3_dyn, hrp3_St x25519 aead_dec F V sp ap mp steps FR0 (0 <= i < steps) i Y).
    + forward. Exists Y0. hrp3_unf. entailer!.
    + forward. Exists i Y0. hrp3_unf. entailer!.
    + apply (hrp3_l1w _ _ _ (hrp3_Icont x25519 aead_dec F V sp ap mp steps FR0) i).
      eapply hrp3_semax_cut with (Q := hrp3_PL1 x25519 aead_dec F V sp ap mp steps FR0 i);
        [discriminate | rewrite <- EL1; apply hrp3_segL1_ok; auto |].
      eapply hrp3_semax_cut with (Q := hrp3_PL2a x25519 aead_dec F V sp ap mp steps FR0 i);
        [discriminate | rewrite <- EL2a; apply hrp3_segL2a_ok; auto |].
      eapply hrp3_semax_cut with (Q := hrp3_PL2b x25519 aead_dec F V sp ap mp steps FR0 i);
        [discriminate | rewrite <- EL2b; apply hrp3_segL2b_ok; auto |].
      rewrite <- EL3; apply hrp3_segL3_ok; auto.
  - (* i++ *)
    Intros i. unfold hrp3_Icont. Intros Y0. hrp3_unf. Intros.
    forward.
    unfold hrp3_Inv. Exists (i + 1) Y0. hrp3_unf. entailer!.
  - unfold POSTCONDITION, abbreviate. simpl RA_normal. apply ENTAIL_refl.
Qed.
