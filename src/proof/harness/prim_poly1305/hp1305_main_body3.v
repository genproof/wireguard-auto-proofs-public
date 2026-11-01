(* body of main of law prim_poly1305. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.harness.prim_poly1305.hp1305_spec3.
Require Import WgNoise.proof.harness.prim_poly1305.hp1305_main_defs3.
Require Import WgNoise.proof.harness.prim_poly1305.hp1305_main_segA3.
Require Import WgNoise.proof.harness.prim_poly1305.hp1305_main_segB3.
Require Import WgNoise.proof.harness.prim_poly1305.hp1305_main_segC3.
Require Import WgNoise.proof.harness.prim_poly1305.hp1305_main_segD3.
Require Import WgNoise.proof.harness.prim_poly1305.hp1305_main_segE3.
Require Import WgNoise.proof.harness.prim_poly1305.hp1305_main_segF3.
Require WgNoise.harness.x_prim_poly1305.code.

#[local] Existing Instance W_prim_poly1305.
Local Open Scope Z_scope.

Module C := WgNoise.harness.x_prim_poly1305.code.

(* main assembled from the segments A-F *)
Lemma hp1305_main_body :
  semax_body hp1305_V hp1305_Gprog C.f_main hp1305_main_spec.
Proof.
  unfold hp1305_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply (main_pre_InitGpred (hp1305_globals gv * TT)%logic);
    [apply hp1305m_init_globals | reflexivity
    | apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; subst x; vm_compute; exact I | ].
  process_stackframe_of.
  set (FR0 := (TT * has_ext tt)%logic).
  eapply semax_pre with (P' := hp1305m_P0 gv v_d v_key v_key0 v_ref FR0).
  { unfold hp1305m_P0, hp1305m_lv, t_hpctx. sep_apply (create_mem_mgr gv). unfold FR0. entailer!. }
  rewrite hp1305m_body_eq.
  destruct hp1305m_segs_eq as (EA & EB & EC & ED & EE & EF).
  eapply semax_seq with (Q := FF); [| apply semax_ff].
  eapply hp1305m_semax_cut with (Q := hp1305m_PA gv v_d v_key v_key0 v_ref FR0);
    [discriminate | rewrite hp1305m_overridePost2, <- EA; apply hp1305m_segA_ok |].
  eapply hp1305m_semax_cut with (Q := hp1305m_PB gv v_d v_key v_key0 v_ref FR0);
    [discriminate | rewrite hp1305m_overridePost2, <- EB; apply hp1305m_segB_ok |].
  unfold hp1305m_PB. Intros n kb mb msg copy tag.
  eapply hp1305m_semax_cut with (Q := hp1305m_PC gv v_d v_key v_key0 v_ref FR0 n kb mb msg copy tag n);
    [discriminate | rewrite hp1305m_overridePost2, <- EC; apply hp1305m_segC_ok |].
  eapply hp1305m_semax_cut with (Q := hp1305m_PD gv v_d v_key v_key0 v_ref FR0);
    [discriminate | rewrite hp1305m_overridePost2, <- ED; apply hp1305m_segD_ok |].
  eapply hp1305m_semax_cut with (Q := hp1305m_PE gv v_d v_key v_key0 v_ref FR0);
    [discriminate | rewrite hp1305m_overridePost2, <- EE; apply hp1305m_segE_ok |].
  rewrite <- EF. apply hp1305m_segF_ok.
Qed.
