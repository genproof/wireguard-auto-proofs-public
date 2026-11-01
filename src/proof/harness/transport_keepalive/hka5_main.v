(* main's body proof from the
   segments A-E of its loop body (hka5_segA.v .. hka5_segE.v, states in hka5_defs.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.counter.counter_spec.
Require WgNoise.proof.harness.counter.hcnt_defs3.
Require Import WgNoise.proof.harness.transport_keepalive.hka5_defs.
Require Import WgNoise.proof.harness.transport_keepalive.hka5_segA.
Require Import WgNoise.proof.harness.transport_keepalive.hka5_segB.
Require Import WgNoise.proof.harness.transport_keepalive.hka5_segC.
Require Import WgNoise.proof.harness.transport_keepalive.hka5_segD.
Require Import WgNoise.proof.harness.transport_keepalive.hka5_segE.

#[local] Existing Instance W_transport_keepalive.
Local Open Scope Z_scope.

Lemma hka5_key_bytes (kb: list Z) : Forall (fun b => 0 <= b <= Byte.max_unsigned) kb ->
  map (fun b => Vint (Int.repr b)) kb = map Vubyte (map Byte.repr kb).
Proof.
  intros H. induction H as [|b kb Hb H IH]; [reflexivity |]. simpl. rewrite IH. f_equal.
  unfold Vubyte. rewrite Byte.unsigned_repr by (unfold Byte.max_unsigned in Hb; simpl in Hb; rep_lia). reflexivity.
Qed.

(* main's post (TT) weakened to the canonical form forward needs for a return *)
Lemma hka5_post_canon {Espec: OracleKind} {cs: compspecs} Delta P c gv F :
  semax Delta P c (frame_ret_assert (function_body_ret_assert tint (PROP () LOCAL () SEP (TT))) F) ->
  semax Delta P c (frame_ret_assert (function_body_ret_assert tint (hka5_post gv)) F).
Proof.
  intros H. eapply semax_post; [| | | | apply H]; intros; simpl; intros rho; apply andp_left2;
    try apply derives_refl.
  apply sepcon_derives; [| apply derives_refl]. revert rho. apply bind_ret_derives. intros rho. apply TT_right.
Qed.

Lemma hka5_main_body : semax_body hka5_V hka5_Gprog KA.f_main hka5_main_spec.
Proof.
  unfold hka5_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply (main_pre_InitGpred (zero_page gv * ht4_minusp hka5_mp gv * TT)%logic);
    [apply hka5_init_globals | reflexivity
    | apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; subst x; vm_compute; exact I | ].
  process_stackframe_of.
  set (FR := (TT * has_ext tt)%logic).
  simpl fn_body; simpl fn_return.
  sep_apply (create_mem_mgr gv).
  forward. forward.
  forward_call (Tsh, v_rc).
  forward_call (Tsh, v_wm).
  forward_call (v_key, 32, Tsh).
  Intros kb.
  forward_call tt. Intros steps.
  forward.
  rewrite (hka5_key_bytes kb) by assumption.
  forward_loop (hka5_Inv gv v_rc v_wm v_snap v_key (map Byte.repr kb) steps FR)
    continue: (hka5_Cont gv v_rc v_wm v_snap v_key (map Byte.repr kb) steps FR)
    break: (hka5_Brk gv v_rc v_wm v_snap v_key (map Byte.repr kb) FR).
  - (* entry *)
    unfold hka5_Inv. Exists 0 0 (@nil Z) (Zrepeat 0 128) 0 0.
    unfold hka5_facts, hka5_tl, hka5_lv, hka5_cw, hka5_fr. simpl app.
    entailer!.
    all: first [apply derives_refl | apply hcnt_defs3.cnt_inv_init
               | split; [rewrite Zlength_map; auto | apply hcnt_defs3.cnt_inv_init]].
  - (* the body *)
    unfold hka5_Inv. Intros i top S bm ha ln.
    unfold hka5_tl, hka5_lv, hka5_cw, hka5_fr. simpl app.
    forward_if.
    2: { forward. unfold hka5_Brk, hka5_lv, hka5_fr. Exists top S. entailer!. }
    assert (Hi: i < steps).
    { destruct H2 as (Hi & Hs & _). unfold Int64.ltu in H3.
      rewrite !Int64.unsigned_repr in H3 by rep_lia. destruct (zlt i steps); [lia | discriminate]. }
    clear H3.
    unfold MORE_COMMANDS, abbreviate.
    match goal with |- semax _ _ ?b _ => change b with hka5_body end.
    rewrite hka5_body_eq.
    destruct hka5_segs_eq as (EA & EB & EC & ED & EE).
    eapply semax_pre with (P' := hka5_PA gv v_rc v_wm v_snap v_key (map Byte.repr kb) steps FR i top S bm ha ln).
    { unfold hka5_PA, hka5_tl, hka5_lv, hka5_cw, hka5_fr. simpl app. entailer!. }
    eapply hka5_semax_cut with (Q := hka5_QA gv v_rc v_wm v_snap v_key (map Byte.repr kb) steps FR i top S bm ha ln);
      [discriminate | rewrite <- EA; apply hka5_segA_ok |].
    unfold hka5_QA. Intros kind enc pkt po rp.
    eapply hka5_semax_cut with (Q := hka5_QB gv v_rc v_wm v_snap v_key (map Byte.repr kb) steps FR i top S bm ha ln pkt po rp);
      [discriminate | rewrite <- EB; apply hka5_segB_ok |].
    unfold hka5_QB. Intros nonce hdr c.
    eapply hka5_semax_cut with (Q := hka5_QC gv v_rc v_wm v_snap v_key (map Byte.repr kb) steps FR i top S bm ha ln nonce hdr c pkt po rp);
      [discriminate | rewrite <- EC; apply hka5_segC_ok |].
    unfold hka5_QC.
    eapply hka5_semax_cut with (Q := hka5_QD gv v_rc v_wm v_snap v_key (map Byte.repr kb) steps FR i hdr c pkt po rp);
      [discriminate | rewrite <- ED; apply hka5_segD_ok |].
    unfold hka5_QD. Intros top' S' bm' ha' ln'.
    rewrite <- EE. apply hka5_segE_ok.
  - (* the increment *)
    unfold hka5_Cont. Intros i top S bm ha ln.
    unfold hka5_tl, hka5_lv, hka5_cw, hka5_fr. simpl app.
    forward.
    unfold hka5_Inv. Exists (i + 1) top S bm ha ln.
    unfold hka5_facts, hka5_tl, hka5_lv, hka5_cw, hka5_fr in *. simpl app.
    destruct H2 as (Hi & Hs & Hk & Hc & Hha & Hln).
    entailer!.
  - (* after the loop *)
    unfold hka5_Brk. Intros top S.
    unfold hka5_lv, hka5_fr.
    forward_call (Tsh, v_wm, top, S, gv).
    unfold POSTCONDITION, abbreviate. apply hka5_post_canon.
    forward.
    entailer!.
Qed.
