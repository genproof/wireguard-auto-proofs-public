(* law prim_aead: main of prim_aead.h. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.harness.prim_aead.haead_spec3.
Require Import WgNoise.proof.harness.prim_aead.haead_lemmas3.
Require Import WgNoise.proof.harness.prim_aead.haead_main_body3_defs.
Require Import WgNoise.proof.harness.prim_aead.haead_main_body3_A.
Require Import WgNoise.proof.harness.prim_aead.haead_main_body3_B.
Require Import WgNoise.proof.harness.prim_aead.haead_main_body3_C.
Require Import WgNoise.proof.harness.prim_aead.haead_main_body3_D.
Require Import WgNoise.proof.harness.prim_aead.haead_main_body3_E.
Require Import WgNoise.proof.harness.prim_aead.haead_main_body3_F.
Require WgNoise.harness.x_prim_aead.code.

#[local] Existing Instance W_prim_aead.
Local Open Scope Z_scope.

Lemma haead_main_body3 : haead_hyps ->
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_main haead_main_spec.
Proof.
  intros HH.
  unfold haead_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply (main_pre_InitGpred (zero_page gv * haead_globals gv * TT)%logic);
    [apply hm3_init_globals | reflexivity
    | apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; subst x; vm_compute; exact I | ].
  process_stackframe_of.
  set (FR0 := (TT * has_ext tt)%logic).
  eapply semax_pre with (P' := hm3_P0 gv v_key v_xnonce FR0).
  { unfold hm3_P0, hm3_lv. sep_apply (create_mem_mgr gv). unfold FR0. entailer!. }
  rewrite hm3_body_eq.
  destruct hm3_segs_eq as (EA & EB & EC & ED & EE & EF).
  eapply semax_seq with (Q := FF); [| apply semax_ff].
  eapply hm3_semax_cut with (Q := hm3_PA gv v_key v_xnonce FR0);
    [discriminate | rewrite hm3_overridePost2, <- EA; apply hm3_segA_ok |].
  eapply hm3_semax_cut with (Q := hm3_PB gv v_key v_xnonce FR0);
    [discriminate | rewrite hm3_overridePost2, <- EB; apply hm3_segB_ok |].
  eapply hm3_semax_cut with (Q := hm3_PC gv v_key v_xnonce FR0);
    [discriminate | rewrite hm3_overridePost2, <- EC; apply hm3_segC_ok |].
  eapply hm3_semax_cut with (Q := hm3_PD gv v_key v_xnonce FR0);
    [discriminate | rewrite hm3_overridePost2, <- ED; apply hm3_segD_ok; exact HH |].
  eapply hm3_semax_cut with (Q := hm3_PE gv v_key v_xnonce FR0);
    [discriminate | rewrite hm3_overridePost2, <- EE; apply hm3_segE_ok; exact HH |].
  rewrite <- EF. apply hm3_segF_ok; exact HH.
Qed.
