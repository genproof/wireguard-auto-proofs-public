(* law create_any: main's body, from the prologue (initial globals, stack frame) and
   the phases A .. I. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.create_any.hca3_model.
Require Import WgNoise.proof.harness.create_any.hca5_spec.
Require Import WgNoise.proof.harness.create_any.hca5_defs.
Require Import WgNoise.proof.harness.create_any.hca5_conv.
Require Import WgNoise.proof.harness.create_any.hca5_globals.
Require Import WgNoise.proof.harness.create_any.hca5_PA.
Require Import WgNoise.proof.harness.create_any.hca5_PB.
Require Import WgNoise.proof.harness.create_any.hca5_PC.
Require Import WgNoise.proof.harness.create_any.hca5_PD.
Require Import WgNoise.proof.harness.create_any.hca5_PE.
Require Import WgNoise.proof.harness.create_any.hca5_F.
Require Import WgNoise.proof.harness.create_any.hca5_PG.
Require Import WgNoise.proof.harness.create_any.hca5_PH.
Require Import WgNoise.proof.harness.create_any.hca5_PI.
Require WgNoise.contracts.x_create_any.
Require WgNoise.harness.x_create_any.code.

#[local] Existing Instance W_create_any.
Local Open Scope Z_scope.

(* main's precondition (VSU's main_pre over the whole program): keep gvars and main_pre's globals; their
   predicate is opened by H1 (hca5_init_globals).  As VST's main_pre_InitGpred, without its requirement that
   every global of the whole program be in main's Delta (the harness unit's varspecs list only 8). *)
Lemma hca5_main_pre {Espec: OracleKind} {cs: compspecs} Delta (prog: QP.program function) (gv: globals) Gl R c Post:
  (globals_ok gv -> globvars2pred gv (QPprog_vars prog) |-- Gl) ->
  semax Delta (PROP () LOCAL (gvars gv) SEP (Gl; has_ext tt) * R)%logic c Post ->
  semax Delta (close_precondition nil (@main_pre unit prog tt gv) * R)%logic c Post.
Proof.
  intros H1 H2. eapply semax_pre; [| apply H2]; clear H2.
  unfold main_pre, PROPx, LOCALx, SEPx, local, lift1.
  intro rho. unfold close_precondition. simpl. unfold_lift. normalize.
  rewrite prop_true_andp by (split; auto; hnf; reflexivity).
  apply sepcon_derives; [| apply derives_refl].
  apply sepcon_derives; [| apply derives_refl].
  apply H1. intro i. unfold initialize.genviron2globals.
  destruct (Map.get (ge_of rho) i); auto. left; eexists; reflexivity.
Qed.

Section Main.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hca5_main_body :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax_body hca5_V (hca5_Gprog x25519 aead_enc aead_dec xaead_enc xaead_dec) HC.f_main hca3_main_spec.
Proof.
  intros HH.
  unfold hca3_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply (hca5_main_pre _ _ _ (EX S: shim, EX w: list int64, shim_state4 gv S w *
                                 noise_globals_raw gv zeros32 zeros32 Int64.zero *
                                 wg_consts gv * hca5_consts gv * TT)%logic);
    [apply hca5_init_globals |].
  process_stackframe_of.
  set (FR0 := (TT * has_ext tt)%logic).
  set (L := mkLoc5 v_wa v_ita v_pta v_p v_ia v_s v_x v_st v_ps v_ds v_ss v_raw v_pub v_psk v_key v_dh v_eph v_E
              v_ts v_nothing v_before v_exp v_img v_before__1 v_exp__1 v_img__1).
  Intros S w.
  eapply semax_pre with (P' := hca5_S0 gv L FR0 w).
  { unfold hca5_S0, hca5_lvars, hca5_scr, hca5_scr0, hca5_snap0. subst L.
    cbn [app l_wa l_ita l_pta l_p l_ia l_s l_x l_st l_ps l_ds l_ss l_raw l_pub l_psk l_key l_dh l_eph l_E l_ts
         l_nothing l_before l_exp l_img l_before1 l_exp1 l_img1].
    rewrite !hca5_conv_dev, !hca5_conv_itab, !hca5_conv_ptab, !hca5_conv_peer, !hca5_conv_mident,
      !hca5_conv_hsnap, !hca5_conv_mstate, !hca5_conv_prsnap, !hca5_conv_devsnap, !hca5_conv_shimsnap,
      !hca5_conv_bytes.
    Exists S.
    sep_apply (create_mem_mgr gv). unfold FR0. entailer!. }
  rewrite hca5_body_eq.
  destruct hca5_phases_eq as (EA & EB & EC & ED & EE & EF & EG & EH & EI).
  eapply semax_seq with (Q := FF); [| apply semax_ff].
  eapply hca5_semax_cut with (Q := hca5_SA x25519 gv L FR0 w);
    [discriminate | rewrite hca5_overridePost2, <- EA; apply hca5_PA_ok; exact HH |].
  eapply hca5_semax_cut with (Q := hca5_SB x25519 gv L FR0 w);
    [discriminate | rewrite hca5_overridePost2, <- EB; apply hca5_PB_ok; exact HH |].
  eapply hca5_semax_cut with (Q := hca5_SB x25519 gv L FR0 w);
    [discriminate | rewrite hca5_overridePost2, <- EC; apply hca5_PC_ok; exact HH |].
  eapply hca5_semax_cut with (Q := hca5_SK x25519 gv L FR0 w);
    [discriminate | rewrite hca5_overridePost2, <- ED; apply hca5_PD_ok; exact HH |].
  eapply hca5_semax_cut with (Q := hca5_SE x25519 gv L FR0 w);
    [discriminate | rewrite hca5_overridePost2, <- EE; apply hca5_PE_ok; exact HH |].
  eapply hca5_semax_cut with (Q := hca5_SF x25519 gv L FR0 w);
    [discriminate | rewrite hca5_overridePost2, <- EF; apply hca5_PF_ok; exact HH |].
  eapply hca5_semax_cut with (Q := hca5_SG x25519 gv L FR0 w);
    [discriminate | rewrite hca5_overridePost2, <- EG; apply hca5_PG_ok; exact HH |].
  eapply hca5_semax_cut with (Q := hca5_SG x25519 gv L FR0 w);
    [discriminate | rewrite hca5_overridePost2, <- EH; apply hca5_PH_ok; exact HH |].
  rewrite <- EI. apply hca5_PI_ok; exact HH.
Qed.

End Main.
