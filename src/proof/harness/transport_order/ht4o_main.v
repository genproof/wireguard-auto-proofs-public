(* law transport_order: main's body from its segments: the prologue (initial globals, stack frame, mem_mgr; rc_init, wm_init, the key,
   steps), the loop (invariant ht4o_Inv, body L1; L2; L3; L4, i++, break state ht4o_Brk) and the epilogue
   (wm_free, return 0). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.counter.counter_spec.
Require Import WgNoise.proof.harness.common4t.ht4_worlds.
Require Import WgNoise.proof.harness.common4t.ht4c_spec.
Require Import WgNoise.proof.harness.common4t.ht4r_spec.
Require Import WgNoise.proof.harness.common4t.ht4a_aead.
Require Import WgNoise.proof.harness.transport_order.ht4o_main_defs.
Require Import WgNoise.proof.harness.transport_order.ht4o_init.
Require Import WgNoise.proof.harness.transport_order.ht4o_segL1.
Require Import WgNoise.proof.harness.transport_order.ht4o_segL2.
Require Import WgNoise.proof.harness.transport_order.ht4o_segL3.
Require Import WgNoise.proof.harness.transport_order.ht4o_segL4.
Require WgNoise.proof.harness.counter.hcnt_defs3.

#[local] Existing Instance W_transport_order.
Local Open Scope Z_scope.

Lemma ht4o_l1w {Espec: OracleKind} {cs: compspecs} Delta P c (Q: Z -> environ -> mpred) (i: Z) R :
  semax Delta P c (loop1_ret_assert (Q i) R) -> semax Delta P c (loop1_ret_assert (EX j: Z, Q j) R).
Proof.
  intros H. eapply semax_post; [| | | | exact H]; destruct R; simpl; intros; try intro rho; apply andp_left2;
    try apply derives_refl; cbv beta; apply (exp_right i); apply derives_refl.
Qed.

Lemma ht4o_bytes_Vubyte (bs: list Z) : Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  map (fun b => Vint (Int.repr b)) bs = map Vubyte (map Byte.repr bs).
Proof.
  induction 1; [reflexivity |]. simpl. rewrite IHForall. unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia.
  reflexivity.
Qed.

Lemma ht4o_main_body : semax_body ht4o_V ht4o_G0 TO.f_main ht4o_main_spec.
Proof.
  unfold ht4o_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply (main_pre_InitGpred (zero_page gv * ht4_minusp ht4o_mp gv * TT)%logic);
    [apply ht4o_init_globals | reflexivity
    | apply Forall_forall; intros x Hx'; vm_compute in Hx'; repeat destruct Hx' as [Hx'|Hx']; try contradiction;
      subst x; vm_compute; exact I | ].
  process_stackframe_of.
  set (FR0 := (TT * has_ext tt)%logic).
  sep_apply (create_mem_mgr gv).
  rewrite ht4o_body_eq.
  eapply semax_seq with (Q := FF); [| apply semax_ff].
  (* the prologue *)
  eapply ht4o_semax_cut with (Q := (EX K: list byte, EX steps: Z,
    PROP (Zlength K = 32; 0 <= steps <= Int64.max_unsigned)
    LOCAL (temp TO._steps (Vlong (Int64.repr steps)); temp TO._last_nonce (Vlong (Int64.repr 0));
           temp TO._have_auth (Vint Int.zero);
           lvar TO._rc ht4o_trc v_rc; lvar TO._wm ht4o_twm v_wm; lvar TO._snap ht4o_tsnap v_snap;
           lvar TO._key (tarray tuchar 32) v_key; gvars gv)
    SEP (data_at_ Tsh ht4o_tsnap v_snap;
         data_at Tsh ht4o_trc (ht4o_rc 0 (Zrepeat 0 128)) v_rc; ht4o_wm Tsh 0 [] v_wm;
         data_at Tsh (tarray tuchar 32) (map Vubyte K) v_key;
         zero_page gv; ht4_minusp ht4o_mp gv; mem_mgr gv; FR0))%assert); [discriminate | |].
  { rewrite ht4o_overridePost2. abbreviate_semax.
    cbv [ht4o_l ht4o_seql firstn skipn ht4o_stmts].
    forward. forward.
    forward_call (Tsh, v_rc). forward_call (Tsh, v_wm).
    forward_call (v_key, 32, Tsh). Intros bs.
    forward_call. Intros steps.
    forward.
    Exists (map Byte.repr bs) steps.
    rewrite (ht4o_bytes_Vubyte bs) by auto. unfold FR0.
    entailer!. rewrite !Zlength_map. auto. }
  Intros K steps.
  set (F := mkTFix gv v_rc v_wm v_snap v_key K steps).
  (* the loop, then the epilogue *)
  eapply ht4o_semax_cut with (Q := ht4o_Brk F FR0); [discriminate | rewrite ht4o_overridePost2 | ].
  2:{ cbv [ht4o_l ht4o_seql firstn skipn ht4o_stmts]. unfold ht4o_Brk. Intros top S.
      unfold ht4o_lvars. simpl f_gv; simpl f_rc; simpl f_wm; simpl f_snap; simpl f_key; simpl f_K.
      apply ht4o_post_canon. abbreviate_semax.
      forward_call (Tsh, v_wm, top, S, gv).
      forward.
      unfold FR0. entailer!. }
  rewrite ht4o_loop_eq, ht4o_loop_shape.
  abbreviate_semax.
  forward.
  forward_loop (ht4o_Inv F FR0)
    continue: (EX i: Z, ht4o_Icont F FR0 i)%argsassert
    break: (ht4o_Brk F FR0).
  - (* entry *)
    unfold ht4o_Inv. Exists 0 (mkTDyn 0 [] (Zrepeat 0 128) false 0).
    unfold ht4o_St, ht4o_temps, ht4o_lvars, ht4o_world, ht4o_fix_ok, ht4o_inv. simpl app. unfold F.
    cbn [y_top y_S y_bm y_have y_ln f_gv f_rc f_wm f_snap f_key f_K f_steps].
    entailer!. apply hcnt_defs3.cnt_inv_init.
  - (* the body *)
    unfold ht4o_Inv at 1. Intros i Y0. unfold ht4o_St, ht4o_temps, ht4o_lvars, ht4o_world. simpl app. Intros.
    forward_if (EX Y: ht4o_dyn, ht4o_St F FR0 (0 <= i < f_steps F) i Y).
    + forward. Exists Y0. unfold ht4o_St, ht4o_temps, ht4o_lvars, ht4o_world. simpl app. entailer!.
      unfold Int64.ltu in H4. simpl f_steps in *. rewrite !Int64.unsigned_repr in H4 by lia.
      destruct (zlt i steps); [lia | discriminate].
    + forward. unfold ht4o_Brk. Exists (y_top Y0) (y_S Y0). unfold ht4o_lvars. simpl app. entailer!.
    + unfold POSTCONDITION, abbreviate.
      apply (ht4o_l1w _ _ _ (ht4o_Icont F FR0) i).
      destruct ht4o_segs_eq as (EL1 & EL2 & EL3 & EL4).
      eapply ht4o_semax_cut with (Q := ht4o_PL1 F FR0 i);
        [discriminate | rewrite <- EL1; apply ht4o_segL1_ok |].
      eapply ht4o_semax_cut with (Q := ht4o_PL2 F FR0 i);
        [discriminate | rewrite <- EL2; apply ht4o_segL2_ok |].
      eapply ht4o_semax_cut with (Q := ht4o_PL3 F FR0 i);
        [discriminate | rewrite <- EL3; apply ht4o_segL3_ok |].
      rewrite <- EL4; apply ht4o_segL4_ok.
  - (* i++ *)
    Intros i. unfold ht4o_Icont. Intros Y0. unfold ht4o_St, ht4o_temps, ht4o_lvars, ht4o_world. simpl app. Intros.
    forward.
    unfold ht4o_Inv. Exists (i + 1) Y0. unfold ht4o_St, ht4o_temps, ht4o_lvars, ht4o_world. simpl app.
    entailer!.
  - unfold POSTCONDITION, abbreviate. simpl RA_normal. apply ENTAIL_refl.
Qed.
