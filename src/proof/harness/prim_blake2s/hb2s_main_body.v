(* body of main of law prim_blake2s (harness/prim_blake2s.c). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.harness.prim_blake2s.hb2s_spec.
Require Import WgNoise.proof.harness.prim_blake2s.hb2s_main_defs.
Require Import WgNoise.proof.harness.prim_blake2s.hb2s_main_segA.
Require Import WgNoise.proof.harness.prim_blake2s.hb2s_main_segB.
Require Import WgNoise.proof.harness.prim_blake2s.hb2s_main_segC.
Require Import WgNoise.proof.harness.prim_blake2s.hb2s_main_segD.
Require Import WgNoise.proof.harness.prim_blake2s.hb2s_main_segE.
Require Import WgNoise.proof.harness.prim_blake2s.hb2s_main_segF.
Require WgNoise.harness.x_prim_blake2s.code.

#[local] Existing Instance W_prim_blake2s.
Local Open Scope Z_scope.

Lemma hb2s_main_body :
  semax_body hb2s_V hb2s_Gprog WgNoise.harness.x_prim_blake2s.code.f_main hb2s_main_spec.
Proof.
  unfold hb2s_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply (main_pre_InitGpred (hb2s_globals gv * blake2s_globals gv * TT)%logic);
    [apply hb2s_init_globals | reflexivity
    | apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; subst x; vm_compute; exact I | ].
  process_stackframe_of.
  set (FR0 := (TT * has_ext tt)%logic).
  eapply semax_pre with (P' := hb2s_P0 gv v_ctx v_key v_key_copy FR0).
  { unfold hb2s_P0, hb2s_lv, t_hctx. sep_apply (create_mem_mgr gv). unfold FR0. entailer!. }
  rewrite hb2s_body_eq.
  destruct hb2s_segs_eq as (EA & EB & EC & ED & EE & EF).
  eapply semax_seq with (Q := FF); [| apply semax_ff].
  eapply hb2s_semax_cut with (Q := hb2s_PA gv v_ctx v_key v_key_copy FR0);
    [discriminate | rewrite hb2s_overridePost2, <- EA; apply hb2s_segA_ok |].
  eapply hb2s_semax_cut with (Q := hb2s_PB gv v_ctx v_key v_key_copy FR0);
    [discriminate | rewrite hb2s_overridePost2, <- EB; apply hb2s_segB_ok |].
  unfold hb2s_PB. Intros outlen keylen n kb mb msg copy out ref out2.
  eapply hb2s_semax_cut with (Q := hb2s_PC gv v_ctx v_key v_key_copy FR0 outlen keylen n kb mb msg copy out ref out2 n);
    [discriminate | rewrite hb2s_overridePost2, <- EC; apply hb2s_segC_ok |].
  eapply hb2s_semax_cut with (Q := hb2s_PD gv v_ctx v_key v_key_copy FR0);
    [discriminate | rewrite hb2s_overridePost2, <- ED; apply hb2s_segD_ok |].
  eapply hb2s_semax_cut with (Q := hb2s_PE gv v_ctx v_key v_key_copy FR0);
    [discriminate | rewrite hb2s_overridePost2, <- EE; apply hb2s_segE_ok |].
  rewrite <- EF. apply hb2s_segF_ok.
Qed.
