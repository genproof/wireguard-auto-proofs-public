(* law handshake, phase P6, segment D = blk 17..19: hs_take(pa), f0, rb = begin_session(pa).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.handshake.hhs3_spec.
Require Import WgNoise.proof.harness.handshake.hhs3_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_conv.
Require Import WgNoise.proof.harness.handshake.hhs3_p6_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.

(* ---------------------------------------------------------------------- *)
(* Helpers (as segment A's)                                                *)
(* ---------------------------------------------------------------------- *)
Local Open Scope logic.

(* the shim's globals other than the allocation failure counter *)
Definition hhs3_p6_D_rest (gv: globals) (S: shim) : mpred :=
  !! shim_ok S &&
  (@data_at Noise.CS Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
   @data_at Noise.CS Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
   @data_at Noise.CS Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
   @data_at Noise.CS Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
   @data_at Noise.CS Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   @data_at Noise.CS Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   @data_at Noise.CS Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow) * refwarn gv).

#[local] Instance hhs3_p6_D_cceN : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.

Lemma hhs3_p6_D_ulong sh (v: val) p : @data_at Noise.CS sh tulong v p = @data_at W_handshake sh tulong v p.
Proof. apply equal_f, (@data_at_change_composite Noise.CS W_handshake _ sh tulong v v); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

Lemma hhs3_p6_D_shim gv S : shim_state gv S =
  @data_at W_handshake Ews tulong (Vlong (s_fails S)) (gv HC._wg_shim_alloc_failures) * hhs3_p6_D_rest gv S.
Proof.
  unfold shim_state, hhs3_p6_D_rest.
  rewrite <- !hhs3_p6_D_ulong.
  apply pred_ext; Intros; entailer!.
Qed.

(* B's table at S5: only pa's handshake entry, index s_idx Q *)
Lemma hhs3_p6_D_TB1 L Q :
  t_D (hhs3_TB1 L Q) = [(hs_addr (l_pa L), Tsh, mkEntry (l_pa L) IDX_HANDSHAKE (s_idx Q))].
Proof.
  unfold hhs3_TB1, t_insert, t_set_index, t_entry, hhs3_TB0, hhs3_EA; cbn [t_D sfind].
  rewrite if_true by auto. unfold t_upd; cbn [t_D supd]. rewrite if_true by auto. reflexivity.
Qed.

Local Open Scope Z_scope.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p6_D_ok {Espec: OracleKind} gv L FR V :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hhs3_p6_pure x25519 aead_enc aead_dec -> hhs3_p6_free_stmt x25519 ->
  hhs3_p6_ctx x25519 aead_enc aead_dec L V ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p6_SC x25519 gv L FR V) hhs3_p6_D
    (overridePost (hhs3_p6_SD x25519 gv L FR V) (hhs3_R gv)).
Proof.
  intros HH HP HF HC. unfold hhs3_p6_SC, hhs3_Delta, hhs3_R, hhs3_p6_D. simplify_func_tycontext. abbreviate_semax.
  destruct HH as [Hx [Ha HHr]]. destruct HP as [HfA [HfB [Hck Hmod]]].
  destruct (HfB Hx Ha L V HC) as [HS2 [HRI [HSID [HMS [HPdead [HPc [HPp [HPn HPd]]]]]]]].
  pose proof HC as HC'. destruct HC' as [HR [Hcnt [HAI [HAC [HAR [HACR HBOOT]]]]]].
  Intros ka.
  unfold hhs3_p6_sep, hhs3_globs, hhs3_p6_locals, hhs3_lvars, hhs3_cnt_temps, hhs3_setup_sep; cbn [app].
  (* hs_take(&snap, &pa.handshake) *)
  assert (HE: t_entry (hhs3_TB1 L (w_Q V)) (hs_addr (l_pa L)) = Some (hhs3_p6_EA1 L V)).
  { unfold t_entry. rewrite hhs3_p6_D_TB1. cbn [sfind]. rewrite if_true by auto. reflexivity. }
  assert_PROP (isptr (l_pa L) /\ isptr (l_wb L)) as HPtr by entailer!.
  destruct HPtr as [HPa HPw].
  forward_call (Tsh, l_snap L, Tsh, l_pa L, hhs3_p6_PAa x25519 V, Tsh, l_itb L, hhs3_TB1 L (w_Q V), hhs3_p6_EA1 L V).
  { (* hs_take's round-4 side conditions *)
    assert (Hs: hs_sid (p_hs (hhs3_p6_PAa x25519 V)) = id_addr (l_wb L)) by exact HSID.
    split; [unfold hhs3_p6_EA1; cbn; destruct (l_pa L); try contradiction; discriminate
           | rewrite Hs; unfold id_addr; destruct (l_wb L); try contradiction; discriminate]. }
  (* f0 = wg_shim_alloc_failures *)
  rewrite hhs3_p6_D_shim. Intros. forward.
  gather_SEP (data_at _ tulong _ (gv HC._wg_shim_alloc_failures)) (hhs3_p6_D_rest gv (hhs3_p6_S1 V)).
  rewrite <- hhs3_p6_D_shim.
  (* rb = wg_noise_handshake_begin_session(&pa.handshake, &pa.keypairs) *)
  assert (HPA: p_device (hhs3_p6_PAa x25519 V) = l_wb L /\ p_cur (hhs3_p6_PAa x25519 V) = nullval /\
               p_prev (hhs3_p6_PAa x25519 V) = nullval /\ p_next (hhs3_p6_PAa x25519 V) = nullval).
  { unfold hhs3_p6_PAa, hhs3_PA3, hhs3_PA2, p_set_hs, p_set_refs, p_set_cookie. cbn. auto. }
  destruct HPA as [HQd [HQc [HQp HQn]]].
  assert_PROP (@field_compatible Noise.CS t_peer [] (l_pa L)) as FCpa.
  { unfold peer_rep at 1. entailer!. }
  forward_call (gv, hhs3_p6_S1 V, Int64.one, @nil (val * keypair), hhs3_TB1 L (w_Q V), Tsh, l_pa L,
    hhs3_p6_PAa x25519 V, Tsh, l_wb L, hhs3_DB x25519 (w_R V) L, Tsh).
  { split; [| split].
    - exists (hhs3_p6_EA1 L V). split; [exact HE | reflexivity].
    - split; constructor.
    - unfold slots_ok. rewrite HQc, HQp, HQn. cbn [filter].
      destruct (eq_dec nullval nullval); [| congruence].
      split; [repeat constructor; auto | constructor]. }
  Intros kb.
  forward.
  (* the post: SD *)
  unfold hhs3_p6_SD, hhs3_p6_sep, hhs3_p6_locals, hhs3_p6_snapB, hhs3_p6_BB,
    hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps, hhs3_lvars. cbn [app].
  Exists ka kb.
  destruct Hcnt as [_ [_ Hl]].
  change (s_fails (hhs3_p6_S1 V)) with (s_fails (w_S V)). rewrite Hl.
  change (d_itab (hhs3_DB x25519 (w_R V) L)) with (l_itb L).
  change (hhs3_p6_S1 V) with (shim_alloc_ok (w_S V)).
  assert (Hra: forall b, force_val (sem_cast tbool tbool (Val.of_bool b)) = Val.of_bool b)
    by (destruct b; reflexivity).
  rewrite Hra.
  entailer!.
  match goal with Hk: kb <> nullval, Hi: In kb _ |- _ => exact (proj1 (H2 Hk) Hi) end.
Qed.

End Seg.
