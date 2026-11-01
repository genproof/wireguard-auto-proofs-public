(* law handshake_clear: main's phase P1, statements 0..3: peers = NULL, wg_shim_boottime_ns = draw_boottime(), nondet_bytes(raw, 32), setup_device(&w, &it, &pt, raw) (setup_device4: the shim's warnings w from prot_repr4's shim_state_ex4).
   (states: hcl5_defs.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_world.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_cut.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_globals.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_spec.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_defs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_conv.
Require WgNoise.harness.x_handshake_clear.code.

#[local] Existing Instance W_handshake_clear.
Local Open Scope Z_scope.

#[local] Instance hcl5_p1_cceN : change_composite_env Noise.CS W_handshake_clear.
Proof. make_cs_preserve Noise.CS W_handshake_clear. Defined.

Lemma hcl5_p1_tulong_cs sh v p :
  @data_at Noise.CS sh tulong v p = @data_at W_handshake_clear sh tulong v p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W_handshake_clear _ sh tulong v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

Definition hcl5_p1_rest (gv: globals) (S: shim) : mpred :=
  (@data_at Noise.CS Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
   @data_at Noise.CS Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
   @data_at Noise.CS Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
   @data_at Noise.CS Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   @data_at Noise.CS Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
   @data_at Noise.CS Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   @data_at Noise.CS Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow))%logic.

Lemma hcl5_p1_core_open gv S :
  shim_core gv S = (!! shim_ok S &&
    (@data_at W_handshake_clear Ews tulong (Vlong (s_boot S)) (gv HC._wg_shim_boottime_ns) *
     hcl5_p1_rest gv S))%logic.
Proof.
  unfold shim_core, hcl5_p1_rest. rewrite <- hcl5_p1_tulong_cs. rewrite !sepcon_assoc. reflexivity.
Qed.

(* the shim after the boot clock store *)
Definition hcl5_p1_S1 (v: int64) : shim :=
  mkShim v Int64.zero Int64.zero zeros32 zeros32 Int.zero Int64.zero Int64.zero Int64.zero false
         Int64.zero false.

#[local] Instance hcl5_p1_cceH : change_composite_env HCS W_handshake_clear.
Proof. make_cs_preserve HCS W_handshake_clear. Defined.

(* nondet_bytes's result as hbytes *)
Lemma hcl5_p1_nd sh n bs p : Zlength bs = n -> Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  @data_at W_handshake_clear sh (tarray tuchar n) (map (fun b => Vint (Int.repr b)) bs) p =
  hbytes sh (map Byte.repr bs) p.
Proof.
  intros Hn Hb. subst n. unfold hbytes, bytes. rewrite Zlength_map.
  rewrite (@data_at_change_composite HCS W_handshake_clear _ sh (tarray tuchar (Zlength bs))
             (map Vubyte (map Byte.repr bs)) (map Vubyte (map Byte.repr bs)) (JMeq_refl _))
    by prove_cs_preserve_type.
  f_equal. rewrite map_map. induction Hb; simpl; [reflexivity |]. f_equal; [| assumption].
  unfold Vubyte. rewrite Byte.unsigned_repr by (unfold Byte.max_unsigned in *; simpl in *; lia). reflexivity.
Qed.

Section P1.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcl5_P1_ok {Espec: OracleKind} gv L FR :
  hcl5_hyps x25519 ->
  semax (hcl5_Delta x25519) (hcl5_S0 gv L FR) hcl5_P1
    (overridePost (hcl5_SA x25519 gv L FR) (hcl5_R gv)).
Proof.
  intros HH. unfold hcl5_S0, hcl5_Delta, hcl5_R, hcl5_P1. simplify_func_tycontext.
  abbreviate_semax.
  unfold hcl5_lvars, hcl5_snaps0, hcl5_scr; cbn [app].
  rewrite shim_state_ex4. Intros w.
  forward. forward_call tt.
  Intros v. unfold shim_state4. rewrite (hcl5_p1_core_open gv hcl5_shim0). Intros.
  forward. gather_SEP 6 7 8. replace_SEP 0 (shim_state4 gv (hcl5_p1_S1 v) w).
  1: unfold shim_state4; rewrite hcl5_p1_core_open; entailer!; apply derives_refl.
  rewrite !hcl5_conv_bytes.
  forward_call (l_raw L, 32, Tsh). Intros bs.
  rewrite (hcl5_p1_nd Tsh 32 bs) by tauto.
  rewrite <- !hcl5_conv_bytes.
  forward_call (gv, hcl5_p1_S1 v, w, Tsh, l_w L, l_it L, l_pt L, Tsh, l_raw L, map Byte.repr bs).
  { rewrite Zlength_map; tauto. }
  Intros sec.
  set (R := mkRun5 (map Byte.repr bs) sec v).
  change (setup_dev x25519 (l_w L) (l_it L) (l_pt L) (map Byte.repr bs) sec (s_boot (hcl5_p1_S1 v)))
    with (hcl5_D x25519 R L).
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
  unfold hcl5_SA.
  Exists R (shim_draw (hcl5_p1_S1 v) sec) w (@nil hnode4) (@nil (val * share * peer)) (mkT [] []) nullval.
  unfold hcl5_world, hcl5_globs, hcl5_lvars, hcl5_scr, hcl5_snaps0; cbn [app map hcl5_head].
  entailer!.
  { unfold hcl5_run_ok, hcl5_inv, hcl5_T_ok, hcl5_slots_ok; simpl. rewrite Zlength_map.
    repeat split; auto; try lia; constructor. }
  { unfold hnodes_rep4; simpl; entailer!. }
Qed.

End P1.
