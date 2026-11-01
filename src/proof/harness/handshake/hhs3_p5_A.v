(* law handshake, phase P5, segment A.
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
Require Import WgNoise.proof.harness.handshake.hhs3_p5_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Local Open Scope logic.
(* the shim's globals other than the boot clock *)
Definition hhs3_p5_A_rest (gv: globals) (S: shim) : mpred :=
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

#[local] Instance hhs3_p5_A_cceN : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.

Lemma hhs3_p5_A_ulong sh (v: val) p : @data_at Noise.CS sh tulong v p = @data_at W_handshake sh tulong v p.
Proof. apply equal_f, (@data_at_change_composite Noise.CS W_handshake _ sh tulong v v); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

Lemma hhs3_p5_A_shim gv S now : shim_state gv (shim_set_boot S now) =
  @data_at W_handshake Ews tulong (Vlong now) (gv HC._wg_shim_boottime_ns) * hhs3_p5_A_rest gv S.
Proof.
  unfold shim_state, hhs3_p5_A_rest. cbn [shim_set_boot s_boot s_rsec s_rnsec s_log s_logprev s_u32 s_allocs
    s_fails s_frees s_failnext s_released s_rlallow].
  rewrite <- !hhs3_p5_A_ulong.
  assert (E: shim_ok (shim_set_boot S now) = shim_ok S) by reflexivity. rewrite E.
  apply pred_ext; Intros; entailer!.
Qed.

Lemma hhs3_p5_A_boot S : shim_set_boot S (s_boot S) = S.
Proof. destruct S; reflexivity. Qed.
Local Open Scope Z_scope.

Section P5A.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p5_A_sfind1 {A: Type} a sh (v: A) : sfind [(a, sh, v)] a = Some (sh, v).
Proof. simpl. rewrite if_true by auto. reflexivity. Qed.

Lemma hhs3_p5_A_entry L I : t_entry (hhs3_TA1 L I) (hs_addr (l_pb L)) = Some (hhs3_p5_EB1 L I).
Proof.
  unfold hhs3_TA1, t_insert, t_set_index, t_upd, hhs3_TA0. unfold t_entry at 2. cbn [t_D].
  rewrite hhs3_p5_A_sfind1. unfold t_entry. cbn [t_D supd]. rewrite if_true by auto.
  rewrite hhs3_p5_A_sfind1. reflexivity.
Qed.

Lemma hhs3_p5_A_peers R L I M1 H1 MI M2 :
  hhs3_p5_acc_stmt x25519 aead_enc aead_dec -> x25519_props x25519 -> aead_props aead_enc aead_dec ->
  hhs3_run_ok R -> hhs3_after_init x25519 aead_enc R L I M1 H1 MI ->
  peers_rep (peers_after [(l_pb L, Tsh, hhs3_PB1 x25519 R L M1 H1)] (hhs3_cre x25519 aead_dec R L I M1 H1 M2)) =
  peer_rep Tsh (l_pb L) (hhs3_p5_pb x25519 R L M1 H1 (hhs3_cre x25519 aead_dec R L I M1 H1 M2)).
Proof.
  intros HACC Hx Ha HR HI.
  destruct (HACC Hx Ha R L I M1 H1 MI M2 HR HI) as [_ [_ HA]].
  destruct (hhs3_cre x25519 aead_dec R L I M1 H1 M2) as [[a P] |] eqn:EC;
    unfold peers_after, hhs3_p5_pb, peers_rep; simpl supd; simpl iter_sepcon.iter_sepcon; unfold peer_item_rep.
  - rewrite (HA a P eq_refl). rewrite if_true by auto. simpl. apply sepcon_emp.
  - apply sepcon_emp.
Qed.

(* hs_take's round-4 PROP fact for pb: create_initiation keeps the handshake's static identity *)
Lemma hhs3_p5_A_cisid ID H M r ts idx b M' H' :
  create_initiation_model x25519 aead_enc ID H M r ts idx = (b, M', H') -> hs_sid H' = hs_sid H.
Proof.
  unfold create_initiation_model.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end;
  intros E; inversion E; subst; reflexivity.
Qed.

Lemma hhs3_p5_A_sid R L I M1 H1 MI : hhs3_after_init x25519 aead_enc R L I M1 H1 MI -> isptr (l_wa L) ->
  hs_sid (p_hs (hhs3_PB1 x25519 R L M1 H1)) <> Vundef.
Proof.
  intros (_ & Hci & _) Hp. unfold hhs3_PB1, p_set_cookie, p_set_hs; cbn [p_hs].
  unfold hhs3_ci in Hci. rewrite (hhs3_p5_A_cisid _ _ _ _ _ _ _ _ _ Hci).
  unfold hhs3_PB0, setup_peer_val, hs_initial; cbn [p_hs hs_sid].
  unfold id_addr. destruct (l_wa L); try contradiction; discriminate.
Qed.

Lemma hhs3_p5_A_ok {Espec: OracleKind} gv L FR :
  hhs3_p5_acc_stmt x25519 aead_enc aead_dec ->
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_S4 x25519 aead_enc aead_dec gv L FR) hhs3_p5_A
    (overridePost (hhs3_p5_SA x25519 aead_enc aead_dec gv L FR) (hhs3_R gv)).
Proof.
  intros HACC HH. unfold hhs3_S4, hhs3_Delta, hhs3_R, hhs3_p5_A. simplify_func_tycontext. abbreviate_semax.
  Intros R S m1 m2 a0 f0 l0 I M1 H1 MI.
  Intros nowb PA1 CI1 CI2 Q M2 H2 MR.
  unfold hhs3_lvars, hhs3_scr_tmp, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
  rewrite <- (hhs3_p5_A_boot S), hhs3_p5_A_shim. Intros.
  forward_call tt. Intros nowa.
  forward.
  forward.
  gather_SEP (data_at _ tulong _ (gv HC._wg_shim_boottime_ns)) (hhs3_p5_A_rest gv S).
  rewrite <- hhs3_p5_A_shim.
  pose proof (hhs3_p5_A_entry L I) as HE.
  assert_PROP (isptr (l_pb L) /\ isptr (l_wa L)) as HPtr by entailer!.
  destruct HPtr as [HPb HPw].
  forward_call (Tsh, l_snap L, Tsh, l_pb L, hhs3_PB1 x25519 R L M1 H1, Tsh, l_ita L, hhs3_TA1 L I, hhs3_p5_EB1 L I).
  { (* hs_take's round-4 side conditions *)
    split; [unfold hhs3_p5_EB1; cbn; destruct (l_pb L); try contradiction; discriminate
           | exact (hhs3_p5_A_sid _ _ _ _ _ _ H3 HPw)]. }
  change (itable Tsh (l_ita L) (hhs3_TA1 L I)) with (itable Tsh (d_itab (hhs3_DA x25519 R L)) (hhs3_TA1 L I)).
  replace (peer_rep Tsh (l_pb L) (hhs3_PB1 x25519 R L M1 H1)) with (peers_rep [(l_pb L, Tsh, hhs3_PB1 x25519 R L M1 H1)])
    by (unfold peers_rep; simpl; apply sepcon_emp).
  forward_call (gv, shim_set_boot S nowa, Ews, m2, hhs3_M2m x25519 R M2, Tsh, l_wa L,
    hhs3_DA x25519 R L, Tsh, hhs3_TA1 L I, [(l_pb L, Tsh, hhs3_PB1 x25519 R L M1 H1)]).
  { split; [| split].
    - unfold pool_peers_ok, hhs3_TA1, t_insert, t_set_index, t_upd, hhs3_TA0. unfold t_entry at 1. cbn [t_D].
      rewrite hhs3_p5_A_sfind1. cbn [t_D supd]. rewrite if_true by auto.
      constructor; [| constructor]. cbn [hhs3_EB e_peer e_type]. split.
      + exists Tsh, (hhs3_PB1 x25519 R L M1 H1). split; [apply hhs3_p5_A_sfind1 |].
        unfold hhs3_PB1, hhs3_PB0, setup_peer_val. cbn. discriminate.
      + left. split; reflexivity.
    - constructor; [apply writable_share_top | constructor].
    - (* the peer holds one reference (peers_refs_ok) *)
      constructor; [| constructor]. unfold hhs3_PB1, hhs3_PB0, setup_peer_val. cbn.
      rewrite Int.unsigned_one. lia. }
  forward.
  change (cre_res x25519 aead_dec (hhs3_DA x25519 R L) (hhs3_TA1 L I) [(l_pb L, Tsh, hhs3_PB1 x25519 R L M1 H1)]
            (hhs3_M2m x25519 R M2)) with (hhs3_cre x25519 aead_dec R L I M1 H1 M2).
  destruct HH as [Hx [Ha _]].
  rewrite (hhs3_p5_A_peers R L I M1 H1 MI M2 HACC Hx Ha H H3).
  change (d_itab (hhs3_DA x25519 R L)) with (l_ita L).
  assert (Hcnt: hhs3_cnt (shim_set_boot S nowa) a0 f0 l0) by exact H0.
  unfold hhs3_p5_SA, hhs3_p5_sep, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps, hhs3_lvars.
  Exists R (shim_set_boot S nowa) m1 m2 a0 f0 l0 I M1 H1 MI.
  Exists nowb PA1 CI1 CI2 Q M2 H2 MR nowa (hhs3_cre x25519 aead_dec R L I M1 H1 M2).
  cbn [app]. unfold hhs3_p5_snap.
  entailer!.
Qed.

End P5A.
