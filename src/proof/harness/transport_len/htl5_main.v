(* main of harness/transport_len.c from its six segments. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.units.DataHeader.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.harness.common4t.ht4_worlds.
Require Import WgNoise.proof.harness.common4t.ht4c_spec.
Require Import WgNoise.proof.harness.transport_len.htl5_defs.
Require Import WgNoise.proof.harness.transport_len.htl5_segA WgNoise.proof.harness.transport_len.htl5_segB
        WgNoise.proof.harness.transport_len.htl5_segC WgNoise.proof.harness.transport_len.htl5_segD
        WgNoise.proof.harness.transport_len.htl5_segE WgNoise.proof.harness.transport_len.htl5_segF.
Require WgNoise.harness.x_transport_len.code.

#[local] Existing Instance W_transport_len.
Local Open Scope Z_scope.

Lemma htl5_main_body :
  semax_body htl5_V htl5_Gprog WgNoise.harness.x_transport_len.code.f_main htl5_main_spec.
Proof.
  unfold htl5_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply (main_pre_InitGpred (zero_page gv * htl5_minusp gv * TT)%logic);
    [apply htl5_init_globals | reflexivity
    | apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; subst x; vm_compute; exact I | ].
  process_stackframe_of.
  set (FR0 := (TT * has_ext tt)%logic).
  eapply semax_pre with (P' := htl5_P0 gv v_key FR0).
  { unfold htl5_P0, htl5_lv. sep_apply (create_mem_mgr gv). unfold FR0. entailer!. }
  rewrite htl5_body_eq.
  destruct htl5_segs_eq as (EA & EB & EC & ED & EE & EF).
  eapply semax_seq with (Q := FF); [| apply semax_ff].
  eapply htl5_semax_cut with (Q := htl5_PA gv v_key FR0);
    [discriminate | rewrite htl5_overridePost2, <- EA; apply htl5_segA_ok |].
  eapply htl5_semax_cut with (Q := htl5_PB gv v_key FR0);
    [discriminate | rewrite htl5_overridePost2, <- EB; apply htl5_segB_ok |].
  eapply htl5_semax_cut with (Q := htl5_PC gv v_key FR0);
    [discriminate | rewrite htl5_overridePost2, <- EC; apply htl5_segC_ok |].
  eapply htl5_semax_cut with (Q := htl5_PD gv v_key FR0);
    [discriminate | rewrite htl5_overridePost2, <- ED; apply htl5_segD_ok |].
  eapply htl5_semax_cut with (Q := htl5_PE gv v_key FR0);
    [discriminate | rewrite htl5_overridePost2, <- EE; apply htl5_segE_ok |].
  rewrite <- EF. apply htl5_segF_ok.
Qed.
