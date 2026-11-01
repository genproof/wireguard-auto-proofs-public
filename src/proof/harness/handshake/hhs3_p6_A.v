(* law handshake, phase P6, segment A = blk 0..3: m_transport, hs_take(pb), f0, ra = begin_session(pb).
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
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Helpers                                                                 *)
(* ---------------------------------------------------------------------- *)
Local Open Scope logic.

(* st2 = (ck, h) as two byte buffers *)
Lemma hhs3_p6_A_st2_open sh p (ST: list byte * list byte) :
  @field_compatible HCS t_mstate [] p -> Zlength (fst ST) = 32 -> Zlength (snd ST) = 32 ->
  (let '(ck, h) := ST in @data_at HCS sh t_mstate (mstate_val ck h) p) =
  hbytes sh (fst ST) p * hbytes sh (snd ST) (offset_val 32 p).
Proof.
  destruct ST as [ck h]. cbn [fst snd]. intros FC L1 L2.
  unfold mstate_val, hbytes. rewrite L1, L2.
  unfold_data_at (@data_at HCS sh t_mstate _ p).
  rewrite (@field_at_data_at HCS sh t_mstate (DOT HC._ck)), (@field_at_data_at HCS sh t_mstate (DOT HC._h)).
  rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  assert (isptr p) by (destruct FC; auto).
  rewrite !(isptr_offset_val_zero p) by auto.
  reflexivity.
Qed.

(* the read-only globals: blake2s's sigma and the rest *)
Definition hhs3_p6_A_wgrest (gv: globals) : mpred :=
  @curve25519_globals Noise.CS gv * @zero_page Noise.CS gv * cookie_globals gv.
Lemma hhs3_p6_A_wgc gv : wg_consts gv = WgNoise.proof.blake2s.spec.blake2s_globals gv * hhs3_p6_A_wgrest gv.
Proof. unfold wg_consts, hhs3_p6_A_wgrest. rewrite !sepcon_assoc. reflexivity. Qed.

(* the shim's globals other than the allocation failure counter *)
Definition hhs3_p6_A_rest (gv: globals) (S: shim) : mpred :=
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

#[local] Instance hhs3_p6_A_cceN : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.

Lemma hhs3_p6_A_ulong sh (v: val) p : @data_at Noise.CS sh tulong v p = @data_at W_handshake sh tulong v p.
Proof. apply equal_f, (@data_at_change_composite Noise.CS W_handshake _ sh tulong v v); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

Lemma hhs3_p6_A_shim gv S : shim_state gv S =
  @data_at W_handshake Ews tulong (Vlong (s_fails S)) (gv HC._wg_shim_alloc_failures) * hhs3_p6_A_rest gv S.
Proof.
  unfold shim_state, hhs3_p6_A_rest.
  rewrite <- !hhs3_p6_A_ulong.
  apply pred_ext; Intros; entailer!.
Qed.

(* A's table at S5: only pb's handshake entry, index idx1 *)
Lemma hhs3_p6_A_TA1 L I :
  t_D (hhs3_TA1 L I) = [(hs_addr (l_pb L), Tsh, mkEntry (l_pb L) IDX_HANDSHAKE (i_idx I))].
Proof.
  unfold hhs3_TA1, t_insert, t_set_index, t_entry, hhs3_TA0, hhs3_EB; cbn [t_D sfind].
  rewrite if_true by auto. unfold t_upd; cbn [t_D supd]. rewrite if_true by auto. reflexivity.
Qed.

Local Open Scope Z_scope.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p6_A_ok {Espec: OracleKind} gv L FR V :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hhs3_p6_pure x25519 aead_enc aead_dec -> hhs3_p6_free_stmt x25519 ->
  hhs3_p6_ctx x25519 aead_enc aead_dec L V ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p6_S5 x25519 gv L FR V) hhs3_p6_A
    (overridePost (hhs3_p6_SA x25519 gv L FR V) (hhs3_R gv)).
Proof.
  intros HH HP HF HC. unfold hhs3_p6_S5, hhs3_Delta, hhs3_R, hhs3_p6_A. simplify_func_tycontext. abbreviate_semax.
  destruct HH as [Hx [Ha HHr]]. destruct HP as [HfA [HfB [Hck Hmod]]].
  destruct (HfA Hx Ha L V HC) as [EPB [LCK [LH [EM1 ESID]]]].
  pose proof HC as HC'. destruct HC' as [HR [Hcnt [HAI [HAC [HAR [HACR HBOOT]]]]]].
  unfold hhs3_scr_tmp, hhs3_globs, hhs3_p6_locals, hhs3_lvars, hhs3_cnt_temps, hhs3_setup_sep; cbn [app].
  (* m_transport(first, second, st2.ck) *)
  assert_PROP (@field_compatible HCS t_mstate [] (l_st2 L)) as FCst.
  { destruct (w_ST2 V) as [ck h]. entailer!. }
  rewrite (hhs3_p6_A_st2_open Tsh (l_st2 L) (w_ST2 V) FCst LCK LH).
  rewrite hhs3_p6_A_wgc. Intros.
  change (fst (w_ST2 V)) with (hhs3_p6_ck V).
  forward_call (gv, Tsh, l_first L, Tsh, l_second L, Tsh, l_st2 L, hhs3_p6_ck V).
  (* hs_take(&snap, &pb.handshake) *)
  assert (HE: t_entry (hhs3_TA1 L (w_I V)) (hs_addr (l_pb L)) = Some (hhs3_p6_EB1 L V)).
  { unfold t_entry. rewrite hhs3_p6_A_TA1. cbn [sfind]. rewrite if_true by auto. reflexivity. }
  assert_PROP (isptr (l_pb L) /\ isptr (l_wa L)) as HPtr by entailer!.
  destruct HPtr as [HPb HPw].
  forward_call (Tsh, l_snap L, Tsh, l_pb L, hhs3_p6_PBa V, Tsh, l_ita L, hhs3_TA1 L (w_I V), hhs3_p6_EB1 L V).
  { (* hs_take's round-4 side conditions *)
    assert (Hs: hs_sid (p_hs (hhs3_p6_PBa V)) = id_addr (l_wa L))
      by (unfold hhs3_p6_PBa; rewrite EPB; unfold hhs3_p6_PB2n; destruct (w_ST2 V); exact ESID).
    split; [unfold hhs3_p6_EB1; cbn; destruct (l_pb L); try contradiction; discriminate
           | rewrite Hs; unfold id_addr; destruct (l_wa L); try contradiction; discriminate]. }
  (* f0 = wg_shim_alloc_failures *)
  rewrite hhs3_p6_A_shim. Intros. forward.
  gather_SEP (data_at _ tulong _ (gv HC._wg_shim_alloc_failures)) (hhs3_p6_A_rest gv (w_S V)).
  rewrite <- hhs3_p6_A_shim.
  (* ra = wg_noise_handshake_begin_session(&pb.handshake, &pb.keypairs) *)
  assert (HPB: p_device (hhs3_p6_PBa V) = l_wa L /\ p_cur (hhs3_p6_PBa V) = nullval /\
               p_prev (hhs3_p6_PBa V) = nullval /\ p_next (hhs3_p6_PBa V) = nullval).
  { unfold hhs3_p6_PBa. rewrite EPB. unfold hhs3_p6_PB2n. destruct (w_ST2 V).
    unfold hhs3_PB1, hhs3_PB0, setup_peer_val, p_set_hs, p_set_refs, p_set_cookie. cbn. auto. }
  destruct HPB as [HPd [HPc [HPp HPn]]].
  assert_PROP (@field_compatible Noise.CS t_peer [] (l_pb L)) as FCpb.
  { unfold peer_rep at 1. entailer!. }
  gather_SEP (spec.blake2s_globals gv) (hhs3_p6_A_wgrest gv). rewrite <- hhs3_p6_A_wgc.
  forward_call (gv, w_S V, Int64.zero, @nil (val * keypair), hhs3_TA1 L (w_I V), Tsh, l_pb L, hhs3_p6_PBa V,
    Tsh, l_wa L, hhs3_DA x25519 (w_R V) L, Tsh).
  { change (keypairs_rep W_handshake []) with (@emp mpred _ _). rewrite emp_sepcon. cancel. }
  { split; [| split].
    - exists (hhs3_p6_EB1 L V). split; [exact HE | reflexivity].
    - split; constructor.
    - unfold slots_ok. rewrite HPc, HPp, HPn. cbn [filter].
      destruct (eq_dec nullval nullval); [| congruence].
      split; [repeat constructor; auto | constructor]. }
  Intros ka.
  forward.
  (* the post: SA *)
  unfold hhs3_p6_SA, hhs3_p6_sep, hhs3_p6_locals, hhs3_p6_snapA, hhs3_p6_first, hhs3_p6_second, hhs3_p6_BA,
    hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps, hhs3_lvars. cbn [app].
  Exists ka.
  rewrite (hhs3_p6_A_st2_open Tsh (l_st2 L) (w_ST2 V) FCst LCK LH).
  change (fst (w_ST2 V)) with (hhs3_p6_ck V).
  destruct Hcnt as [_ [_ Hl]]. rewrite Hl.
  change (d_itab (hhs3_DA x25519 (w_R V) L)) with (l_ita L).
  assert (Hra: forall b, force_val (sem_cast tbool tbool (Val.of_bool b)) = Val.of_bool b)
    by (destruct b; reflexivity).
  rewrite Hra.
  entailer!.
  match goal with Hk: ka <> nullval, Hi: In ka _ |- _ => exact (proj1 (H0 Hk) Hi) end.
Qed.

End Seg.
