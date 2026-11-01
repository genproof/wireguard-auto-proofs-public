(* law handshake, phase P3, segment A.
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
Require Import WgNoise.proof.harness.handshake.hhs3_p3_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Local Open Scope logic.
(* the shim's globals other than the boot clock *)
Definition hhs3_p3_A_rest (gv: globals) (S: shim) : mpred :=
  !! shim_ok S &&
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
   @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow) * refwarn gv).

#[local] Instance hhs3_p3_A_cceN : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.

Lemma hhs3_p3_A_ulong sh (v: val) p : @data_at Noise.CS sh tulong v p = @data_at W_handshake sh tulong v p.
Proof. apply equal_f, (@data_at_change_composite Noise.CS W_handshake _ sh tulong v v); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

Lemma hhs3_p3_A_shim gv S now : shim_state gv (shim_set_boot S now) =
  @data_at W_handshake Ews tulong (Vlong now) (gv HC._wg_shim_boottime_ns) * hhs3_p3_A_rest gv S.
Proof.
  unfold shim_state, hhs3_p3_A_rest. cbn [shim_set_boot s_boot s_rsec s_rnsec s_log s_logprev s_u32 s_allocs
    s_fails s_frees s_failnext s_released s_rlallow].
  rewrite <- !hhs3_p3_A_ulong.
  assert (E: shim_ok (shim_set_boot S now) = shim_ok S) by reflexivity. rewrite E.
  apply pred_ext; Intros; entailer!.
Qed.

Lemma hhs3_p3_A_boot S : shim_set_boot S (s_boot S) = S.
Proof. destruct S; reflexivity. Qed.
Local Open Scope Z_scope.

Section P3A.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p3_A_addr ID a sh P0 M now :
  match consume_initiation_model x25519 aead_dec ID [(a, sh, P0)] M now with
  | Some (a', _) => a' = a | None => True end.
Proof.
  unfold consume_initiation_model.
  destruct (negb (id_has ID)); [exact I |].
  destruct (consume_init_stage1 x25519 aead_dec ID M) as [[[[s k] ck1] h1] |]; [| exact I].
  cbn [pk_find]. destruct (bytes_eqb (hs_rstatic (p_hs P0)) s); [| exact I].
  destruct (peer_get P0); [| exact I].
  destruct (consume_init_stage2 _ _ _ _ _) as [[[t ck2] h2] |]; [| exact I].
  destruct (orb _ _); [exact I | reflexivity].
Qed.

Lemma hhs3_p3_A_peers R L M1 nowb :
  peers_rep (peers_after [(l_pa L, Tsh, hhs3_PA0 x25519 R L)] (hhs3_cin x25519 aead_dec R L M1 nowb)) =
  peer_rep Tsh (l_pa L) (hhs3_p3_pa x25519 R L (hhs3_cin x25519 aead_dec R L M1 nowb)).
Proof.
  pose proof (hhs3_p3_A_addr (d_id (hhs3_DB x25519 R L)) (l_pa L) Tsh (hhs3_PA0 x25519 R L)
    (hhs3_M1m x25519 R M1) nowb) as HA.
  unfold hhs3_cin in *.
  destruct (consume_initiation_model _ _ _ _ _ _) as [[a P] |]; unfold peers_after, hhs3_p3_pa, peers_rep;
    simpl supd; simpl iter_sepcon.iter_sepcon; unfold peer_item_rep.
  - subst a. rewrite if_true by auto. simpl. apply sepcon_emp.
  - apply sepcon_emp.
Qed.

Lemma hhs3_p3_A_ok {Espec: OracleKind} gv L FR :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_S2 x25519 aead_enc gv L FR) hhs3_p3_A
    (overridePost (hhs3_p3_SA x25519 aead_enc aead_dec gv L FR) (hhs3_R gv)).
Proof.
  intros HH. unfold hhs3_S2, hhs3_Delta, hhs3_R, hhs3_p3_A. simplify_func_tycontext. abbreviate_semax.
  Intros R S m1 m2 a0 f0 l0 I M1 H1 MI.
  unfold hhs3_lvars, hhs3_scr_tmp, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
  rewrite <- (hhs3_p3_A_boot S), hhs3_p3_A_shim. Intros.
  forward_call tt. Intros nowb.
  forward.
  forward.
  gather_SEP (data_at _ tulong _ (gv HC._wg_shim_boottime_ns)) (hhs3_p3_A_rest gv S).
  rewrite <- hhs3_p3_A_shim.
  assert (HE: t_entry (hhs3_TB0 L) (hs_addr (l_pa L)) = Some (hhs3_EA L)).
  { unfold t_entry, hhs3_TB0; cbn [t_D sfind]. rewrite if_true by auto. reflexivity. }
  assert_PROP (isptr (l_pa L) /\ isptr (l_wb L)) as HPtr by entailer!.
  destruct HPtr as [HPa HPw].
  forward_call (Tsh, l_snap L, Tsh, l_pa L, hhs3_PA0 x25519 R L, Tsh, l_itb L, hhs3_TB0 L, hhs3_EA L).
  { (* hs_take's round-4 side conditions *)
    split; [unfold hhs3_EA; cbn; destruct (l_pa L); try contradiction; discriminate
           | cbn; unfold id_addr; destruct (l_wb L); try contradiction; discriminate]. }
  change (ptable Tsh (l_ptb L) (l_pa L)) with (ptable Tsh (d_ptab (hhs3_DB x25519 R L)) (l_pa L)).
  replace (peer_rep Tsh (l_pa L) (hhs3_PA0 x25519 R L)) with (peers_rep [(l_pa L, Tsh, hhs3_PA0 x25519 R L)])
    by (unfold peers_rep; simpl; apply sepcon_emp).
  forward_call (gv, shim_set_boot S nowb, Int64.zero, Ews, m1, hhs3_M1m x25519 R M1, Tsh, l_wb L,
    hhs3_DB x25519 R L, Tsh, l_pa L, [(l_pa L, Tsh, hhs3_PA0 x25519 R L)]).
  { split; [| split; [| split]].
    - constructor; [apply writable_share_top | constructor].
    - split; reflexivity.
    - constructor; [| constructor]. unfold hhs3_PA0, setup_peer_val, hs_initial; cbn [p_hs hs_lic].
      rewrite Int64.signed_zero. rep_lia.
    - (* the peer holds one reference (peers_refs_ok) *)
      constructor; [| constructor]. unfold hhs3_PA0, setup_peer_val; cbn [p_refs].
      rewrite Int.unsigned_one. lia. }
  forward.
  change (cin_res x25519 aead_dec (hhs3_DB x25519 R L) [(l_pa L, Tsh, hhs3_PA0 x25519 R L)]
            (hhs3_M1m x25519 R M1) (shim_set_boot S nowb)) with (hhs3_cin x25519 aead_dec R L M1 nowb).
  rewrite hhs3_p3_A_peers.
  change (d_ptab (hhs3_DB x25519 R L)) with (l_ptb L).
  assert (Hcnt: hhs3_cnt (shim_set_boot S nowb) a0 f0 l0) by exact H0.
  unfold hhs3_p3_SA, hhs3_p3_sep, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps, hhs3_lvars.
  Exists R (shim_set_boot S nowb) m1 m2 a0 f0 l0 I M1 H1 MI nowb (hhs3_cin x25519 aead_dec R L M1 nowb).
  cbn [app]. unfold hhs3_p3_snap.
  entailer!.
Qed.

End P3A.
