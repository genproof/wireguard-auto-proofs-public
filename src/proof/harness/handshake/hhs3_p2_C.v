(* law handshake: main's phase P2, segment C (statements 46..50): hhs3_p2_SB x25519 aead_enc gv L FR -> hhs3_p2_SC x25519 aead_enc gv L FR.
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
Require Import WgNoise.proof.harness.handshake.hhs3_p2_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Local Open Scope logic.

#[local] Instance hhs3_p2_C_cceN : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.

(* the shim's globals but wg_shim_random_u32 *)
Definition hhs3_p2_C_rest (gv: globals) (S: shim) : mpred :=
  !! shim_ok S &&
  (@data_at Noise.CS Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
   @data_at Noise.CS Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
   @data_at Noise.CS Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
   @data_at Noise.CS Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   @data_at Noise.CS Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
   @data_at Noise.CS Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   @data_at Noise.CS Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow) * refwarn gv).

Lemma hhs3_p2_C_uint sh (v: val) p : @data_at Noise.CS sh tuint v p = @data_at W_handshake sh tuint v p.
Proof. apply equal_f, (@data_at_change_composite Noise.CS W_handshake _ sh tuint v v); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

Lemma hhs3_p2_C_shim gv S : shim_state gv S =
  @data_at W_handshake Ews tuint (Vint (s_u32 S)) (gv HC._wg_shim_random_u32) * hhs3_p2_C_rest gv S.
Proof.
  unfold shim_state, hhs3_p2_C_rest. rewrite <- hhs3_p2_C_uint.
  apply pred_ext; Intros; entailer!.
Qed.

(* the message at the world *)
Lemma hhs3_p2_C_init sh m M : init_rep sh m M =
  !! im_ok M && @data_at W_handshake sh t_init
     (Vint (im_type M), (Vint (im_sender M), (bytes (im_eph M), (bytes (im_encs M), (bytes (im_enct M),
      (bytes (im_mac1 M), bytes (im_mac2 M))))))) m.
Proof.
  unfold init_rep, init_val. f_equal.
  apply equal_f, (@data_at_change_composite Noise.CS W_handshake _ sh t_init); [apply JMeq_refl | prove_cs_preserve_type].
Qed.

(* the table after create_initiation *)
Lemma hhs3_p2_C_TA1 L I : hhs3_TA1 L I =
  mkT [(hs_addr (l_pb L), Tsh, mkEntry (l_pb L) IDX_HANDSHAKE (i_idx I))] [hs_addr (l_pb L)].
Proof.
  unfold hhs3_TA1, t_insert, t_set_index, t_entry, t_upd, hhs3_TA0, hhs3_EB; cbn [t_D t_L sfind supd vremove].
  rewrite !if_true by auto. reflexivity.
Qed.

(* the table opened at its only entry: the entry as a field of the peer, at the world *)
Lemma hhs3_p2_C_open tab pb E : @field_compatible Noise.CS t_peer [] pb ->
  itable Tsh tab (mkT [(hs_addr pb, Tsh, E)] [hs_addr pb]) =
  @data_at Noise.CS Tsh t_itab (hs_addr pb) tab *
  @field_at W_handshake Tsh t_peer (DOT HC._handshake DOT HC._entry)
    (e_peer E, (nullval, (Vtrue, (Vint (e_type E), Vint (e_index E))))) pb.
Proof.
  intros FC0. assert (FC: @field_compatible W_handshake t_peer [] pb).
  { apply (@field_compatible_change_composite Noise.CS W_handshake _); [prove_cs_preserve_type | exact FC0]. }
  unfold itable, pool_item_rep, entry_at, entry_val, vin. cbn [t_L t_D hd VST.msl.iter_sepcon.iter_sepcon succ_in].
  rewrite if_true by auto. destruct (in_dec eq_dec (hs_addr pb) [hs_addr pb]) as [_|N]; [|exfalso; apply N; left; auto].
  rewrite field_at_data_at. rewrite field_address_offset by auto with field_compatible.
  erewrite <- (@data_at_change_composite Noise.CS W_handshake _ Tsh t_entry_s); [| apply JMeq_refl | prove_cs_preserve_type].
  rewrite prop_true_andp.
  2:{ unfold itable_wf; cbn [t_L t_D saddrs map]. split; [constructor; [intros []|constructor]|].
      split; [intros x Hx; exact Hx|]. split; [constructor; [intros []|constructor]|].
      constructor; [apply writable_share_top | constructor]. }
  rewrite sepcon_emp. reflexivity.
Qed.
Lemma hhs3_p2_C_open1 L I : @field_compatible Noise.CS t_peer [] (l_pb L) ->
  itable Tsh (l_ita L) (hhs3_TA1 L I) =
  @data_at Noise.CS Tsh t_itab (hs_addr (l_pb L)) (l_ita L) *
  @field_at W_handshake Tsh t_peer (DOT HC._handshake DOT HC._entry)
    (l_pb L, (nullval, (Vtrue, (Vint IDX_HANDSHAKE, Vint (i_idx I))))) (l_pb L).
Proof. intros FC. rewrite hhs3_p2_C_TA1. apply (hhs3_p2_C_open _ _ (mkEntry (l_pb L) IDX_HANDSHAKE (i_idx I)) FC). Qed.

Lemma hhs3_p2_C_facts L I :
  In (hs_addr (l_pb L)) (saddrs (t_D (hhs3_TA1 L I))) /\ vin (hs_addr (l_pb L)) (t_L (hhs3_TA1 L I)) = true /\
  count_index (hhs3_TA1 L I) (i_idx I) = 1 /\ Zlength (t_L (hhs3_TA1 L I)) = 1.
Proof.
  rewrite hhs3_p2_C_TA1. cbn [t_D t_L saddrs map]. split; [left; auto|]. split.
  { unfold vin. destruct (in_dec eq_dec (hs_addr (l_pb L)) [hs_addr (l_pb L)]) as [_|N]; [auto | exfalso; apply N; left; auto]. }
  split; [|reflexivity].
  unfold count_index, t_indices, t_entry. cbn [t_D t_L map sfind]. rewrite if_true by auto.
  cbn [e_index filter]. rewrite Int.eq_true. reflexivity.
Qed.

Lemma hhs3_p2_C_vp sh p P : sepalg.nonidentity sh -> peer_rep sh p P |-- valid_pointer p.
Proof.
  intros N. unfold peer_rep. apply andp_left2. repeat apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; auto; reflexivity.
Qed.
Local Open Scope Z_scope.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p2_C_ok {Espec: OracleKind} gv L FR :
  hhs3_p2_agree_stmt x25519 aead_enc ->
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p2_SB x25519 aead_enc gv L FR) hhs3_p2_C
    (overridePost (hhs3_p2_SC x25519 aead_enc gv L FR) (hhs3_R gv)).
Proof.
  intros HA HH. unfold hhs3_p2_SB, hhs3_Delta, hhs3_R, hhs3_p2_C. simplify_func_tycontext. abbreviate_semax.
  Intros R S m1 m2 a0 f0 l0 I M1 H1 MI.
  unfold hhs3_p2_sepB, hhs3_lvars, hhs3_p2_scr, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
  forward_call (Tsh, l_img L, Ews, m1, M1).
  destruct HH as (HX & _ & _ & _ & Hrep).
  assert (HM: im_type M1 = Int.repr 1 /\ im_sender M1 = i_idx I).
  { destruct H2 as (Hok & Hci & Hmi & _ & _ & Hr & _).
    specialize (HA HX R L I H Hr Hok). rewrite Hmi in HA. destruct MI as [[[[[E encs] enct] ep] ck] h].
    rewrite Hci in HA. injection HA as HM1 _. rewrite HM1. split; reflexivity. }
  destruct HM as [Ety Esnd].
  rewrite hhs3_p2_C_init. Intros.
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  - apply ENTAIL_refl.
  - forward. forward_if.
    + rewrite Ety in *. discriminate.
    + forward. entailer!.
  - forward. apply ENTAIL_refl.
  - assert_PROP (@field_compatible Noise.CS t_peer [] (l_pb L)) as FCpb by (unfold peer_rep; entailer!).
    rewrite hhs3_p2_C_shim, (hhs3_p2_C_open1 L I FCpb). Intros.
    destruct (hhs3_p2_C_facts L I) as (Fin & Fvin & Fcnt & Flen).
    match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
    + apply ENTAIL_refl.
    + forward. forward.
      forward_if (temp HC._t'30 (Vint Int.one)).
      { forward. forward. forward. entailer!. rewrite Esnd, Int.eq_true. reflexivity. }
      { match goal with Hn: im_sender M1 <> s_u32 S |- _ => exfalso; apply Hn; rewrite Esnd, H3; reflexivity end. }
      forward_if.
      { discriminate. }
      forward. entailer!.
    + forward. apply ENTAIL_refl.
    + sep_apply (derives_refl' _ _ (eq_sym (hhs3_p2_C_open1 L I FCpb))).
      match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
      * apply ENTAIL_refl.
      * forward_call (Tsh, l_ita L, hhs3_TA1 L I, hs_addr (l_pb L)).
        rewrite Fvin.
        assert (Fcnt': count_index (hhs3_TA1 L I) (im_sender M1) = 1) by (rewrite Esnd; exact Fcnt).
        forward_if (temp HC._t'32 (Vint Int.one)).
        { forward. forward_call (Tsh, l_ita L, hhs3_TA1 L I, im_sender M1).
          rewrite Fcnt', if_true by auto. forward. entailer!. }
        { discriminate. }
        forward_if (temp HC._t'34 (Vint Int.one)).
        { forward_call (Tsh, l_ita L, hhs3_TA1 L I). rewrite Flen. forward. entailer!. }
        { discriminate. }
        forward_if.
        { discriminate. }
        forward. entailer!.
      * forward. apply ENTAIL_refl.
      * rewrite (hhs3_p2_C_open1 L I FCpb). Intros.
        match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
        { apply ENTAIL_refl. }
        { forward. forward_if (temp HC._t'36 (Vint Int.one)).
          { forward. forward.
            2: { entailer!. rewrite if_true by auto. reflexivity. }
            entailer!.
            apply denote_tc_test_eq_split;
              (pull_left (peer_rep Tsh (l_pb L) (p_set_hs (hhs3_PB0 x25519 R L) H1));
               repeat apply sepcon_valid_pointer1; apply hhs3_p2_C_vp; auto). }
          { match goal with Hn: IDX_HANDSHAKE <> _ |- _ => exfalso; apply Hn; reflexivity end. }
          forward_if.
          { discriminate. }
          forward. entailer!. }
        { forward. apply ENTAIL_refl. }
        unfold POSTCONDITION, abbreviate. rewrite overridePost_normal'. unfold hhs3_p2_SC.
        Exists R S m1 m2 a0 f0 l0 I M1 H1 MI.
        unfold hhs3_p2_sepB, hhs3_lvars, hhs3_p2_scr, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
        rewrite hhs3_p2_C_shim, (hhs3_p2_C_open1 L I FCpb), hhs3_p2_C_init.
        entailer!.
Qed.

End Seg.
