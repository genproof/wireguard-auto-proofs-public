(* law handshake, phase P4, segment E1.
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
Require Import WgNoise.proof.harness.handshake.hhs3_p4_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Local Open Scope logic.

#[local] Instance hhs3_p4_E1_cceN : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.

(* the shim's globals but wg_shim_random_u32 *)
Definition hhs3_p4_E1_rest (gv: globals) (S: shim) : mpred :=
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

Lemma hhs3_p4_E1_uint sh (v: val) p : @data_at Noise.CS sh tuint v p = @data_at W_handshake sh tuint v p.
Proof. apply equal_f, (@data_at_change_composite Noise.CS W_handshake _ sh tuint v v); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

Lemma hhs3_p4_E1_shim gv S : shim_state gv S =
  @data_at W_handshake Ews tuint (Vint (s_u32 S)) (gv HC._wg_shim_random_u32) * hhs3_p4_E1_rest gv S.
Proof.
  unfold shim_state, hhs3_p4_E1_rest. rewrite <- hhs3_p4_E1_uint.
  apply pred_ext; Intros; entailer!.
Qed.

(* the messages at the world *)
Lemma hhs3_p4_E1_init sh m M : init_rep sh m M =
  !! im_ok M && @data_at W_handshake sh t_init
     (Vint (im_type M), (Vint (im_sender M), (bytes (im_eph M), (bytes (im_encs M), (bytes (im_enct M),
      (bytes (im_mac1 M), bytes (im_mac2 M))))))) m.
Proof.
  unfold init_rep, init_val. f_equal.
  apply equal_f, (@data_at_change_composite Noise.CS W_handshake _ sh t_init); [apply JMeq_refl | prove_cs_preserve_type].
Qed.

Lemma hhs3_p4_E1_resp sh m M : resp_rep sh m M =
  !! rm_ok M && @data_at W_handshake sh t_resp
     (Vint (rm_type M), (Vint (rm_sender M), (Vint (rm_receiver M), (bytes (rm_eph M), (bytes (rm_encn M),
      (bytes (rm_mac1 M), bytes (rm_mac2 M))))))) m.
Proof.
  unfold resp_rep, resp_val. f_equal.
  apply equal_f, (@data_at_change_composite Noise.CS W_handshake _ sh t_resp); [apply JMeq_refl | prove_cs_preserve_type].
Qed.

(* the table after create_response *)
Lemma hhs3_p4_E1_TB1 L Q : hhs3_TB1 L Q =
  mkT [(hs_addr (l_pa L), Tsh, mkEntry (l_pa L) IDX_HANDSHAKE (s_idx Q))] [hs_addr (l_pa L)].
Proof.
  unfold hhs3_TB1, t_insert, t_set_index, t_entry, t_upd, hhs3_TB0, hhs3_EA; cbn [t_D t_L sfind supd vremove].
  rewrite !if_true by auto. reflexivity.
Qed.

(* the table opened at its only entry: the entry as a field of the peer, at the world *)
Lemma hhs3_p4_E1_open tab pb E : @field_compatible Noise.CS t_peer [] pb ->
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
Lemma hhs3_p4_E1_open1 L Q : @field_compatible Noise.CS t_peer [] (l_pa L) ->
  itable Tsh (l_itb L) (hhs3_TB1 L Q) =
  @data_at Noise.CS Tsh t_itab (hs_addr (l_pa L)) (l_itb L) *
  @field_at W_handshake Tsh t_peer (DOT HC._handshake DOT HC._entry)
    (l_pa L, (nullval, (Vtrue, (Vint IDX_HANDSHAKE, Vint (s_idx Q))))) (l_pa L).
Proof. intros FC. rewrite hhs3_p4_E1_TB1. apply (hhs3_p4_E1_open _ _ (mkEntry (l_pa L) IDX_HANDSHAKE (s_idx Q)) FC). Qed.

Lemma hhs3_p4_E1_facts L Q :
  In (hs_addr (l_pa L)) (saddrs (t_D (hhs3_TB1 L Q))) /\ vin (hs_addr (l_pa L)) (t_L (hhs3_TB1 L Q)) = true /\
  count_index (hhs3_TB1 L Q) (s_idx Q) = 1 /\ Zlength (t_L (hhs3_TB1 L Q)) = 1.
Proof.
  rewrite hhs3_p4_E1_TB1. cbn [t_D t_L saddrs map]. split; [left; auto|]. split.
  { unfold vin. destruct (in_dec eq_dec (hs_addr (l_pa L)) [hs_addr (l_pa L)]) as [_|N]; [auto | exfalso; apply N; left; auto]. }
  split; [|reflexivity].
  unfold count_index, t_indices, t_entry. cbn [t_D t_L map sfind]. rewrite if_true by auto.
  cbn [e_index filter]. rewrite Int.eq_true. reflexivity.
Qed.
Local Open Scope Z_scope.

Section P4E1.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p4_E1_m2 R L I M1 H1 MI nowb PA1 CI1 CI2 Q M2 H2 MR :
  hhs3_p4_pa1_stmt x25519 aead_dec -> hhs3_p4_agree_stmt x25519 aead_enc -> x25519_props x25519 ->
  hhs3_run_ok R -> hhs3_after_init x25519 aead_enc R L I M1 H1 MI ->
  hhs3_after_cin x25519 aead_dec R L M1 nowb PA1 CI1 CI2 ->
  hhs3_after_resp x25519 aead_enc R L M1 PA1 CI2 Q M2 H2 MR ->
  rm_type M2 = Int.repr 2 /\ rm_sender M2 = s_idx Q /\ rm_receiver M2 = im_sender M1.
Proof.
  intros HP HA HX Hr Hi Hc (Hcr & Hmr & _ & _ & Hlen).
  specialize (HP _ _ _ _ _ _ _ Hr Hc). subst PA1.
  destruct (HA HX R L I M1 H1 MI nowb CI2 Q Hr Hi Hlen) as (_ & HA2 & _).
  destruct MR as [[[[E encn] ep] ck] h].
  destruct (HA2 _ _ _ _ _ Hmr) as (Hcr' & _ & _).
  rewrite Hcr' in Hcr. injection Hcr as <- _. split; [|split]; reflexivity.
Qed.

Lemma hhs3_p4_E1_ok {Espec: OracleKind} gv L FR :
  hhs3_p4_pa1_stmt x25519 aead_dec ->
  hhs3_p4_agree_stmt x25519 aead_enc ->
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p4_SD x25519 aead_enc aead_dec gv L FR) hhs3_p4_E1
    (overridePost (hhs3_p4_SE x25519 aead_enc aead_dec gv L FR) (hhs3_R gv)).
Proof.
  intros HP HA HH. unfold hhs3_p4_SD, hhs3_p4_SDE, hhs3_Delta, hhs3_R, hhs3_p4_E1. simplify_func_tycontext. abbreviate_semax.
  Intros R S m1 m2 a0 f0 l0 I M1 H1.
  Intros MI nowb PA1 CI1 CI2 Q M2 H2 MR.
  unfold hhs3_p4_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
  destruct (hhs3_p4_E1_m2 R L I M1 H1 MI nowb PA1 CI1 CI2 Q M2 H2 MR HP HA (proj1 HH) H H3 H4 H5)
    as (Ety & Esnd & Ercv).
  destruct CI1 as [[[s1 x1] ck1] y1]. destruct CI2 as [[t2 ck2] h2]. cbv beta iota.
  (* hide the BLAKE2s term of ci (forward_call diverges on it) *)
  remember (kdf2 ck1 (hhs3_ssb x25519 R)) as K2.
  forward_call (Tsh, l_rimg L, Ews, m2, M2).
  rewrite hhs3_p4_E1_resp, hhs3_p4_E1_init. Intros.
  (* CHECK type *)
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  - apply ENTAIL_refl.
  - forward. forward_if.
    + rewrite Ety in *. discriminate.
    + forward. entailer!.
  - forward. apply ENTAIL_refl.
  - (* CHECK receiver_index *)
    match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
    + apply ENTAIL_refl.
    + forward. forward. forward_if.
      * match goal with Hn: Int.repr (Z.b2z (Int.eq _ _)) = Int.zero |- _ => rewrite Ercv, Int.eq_true in Hn; discriminate Hn end.
      * forward. entailer!.
    + forward. apply ENTAIL_refl.
    + assert_PROP (@field_compatible Noise.CS t_peer [] (l_pa L)) as FCpa by (unfold peer_rep; entailer!).
      rewrite hhs3_p4_E1_shim, (hhs3_p4_E1_open1 L Q FCpa). Intros.
      destruct (hhs3_p4_E1_facts L Q) as (Fin & Fvin & Fcnt & Flen).
      match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
      * apply ENTAIL_refl.
      * forward. forward.
        forward_if (temp HC._t'112 (Vint Int.one)).
        { forward. forward. forward. entailer!. rewrite Esnd, Int.eq_true. reflexivity. }
        { match goal with Hn: rm_sender M2 <> s_u32 S |- _ => exfalso; apply Hn; rewrite Esnd, H6; reflexivity end. }
        forward_if.
        { discriminate. }
        forward. entailer!.
      * forward. apply ENTAIL_refl.
      * sep_apply (derives_refl' _ _ (eq_sym (hhs3_p4_E1_open1 L Q FCpa))).
        match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
        { apply ENTAIL_refl. }
        { forward_call (Tsh, l_itb L, hhs3_TB1 L Q, hs_addr (l_pa L)).
          rewrite Fvin.
          assert (Fcnt': count_index (hhs3_TB1 L Q) (rm_sender M2) = 1) by (rewrite Esnd; exact Fcnt).
          forward_if (temp HC._t'114 (Vint Int.one)).
          { forward. forward_call (Tsh, l_itb L, hhs3_TB1 L Q, rm_sender M2).
            rewrite Fcnt', if_true by auto. forward. entailer!. }
          { discriminate. }
          forward_if (temp HC._t'116 (Vint Int.one)).
          { forward_call (Tsh, l_itb L, hhs3_TB1 L Q). rewrite Flen. forward. entailer!. }
          { discriminate. }
          forward_if.
          { discriminate. }
          forward. entailer!. }
        { forward. apply ENTAIL_refl. }
        unfold POSTCONDITION, abbreviate. rewrite overridePost_normal'. unfold hhs3_p4_SE, hhs3_p4_SDE.
        Exists R S m1 m2 a0 f0 l0 I M1 H1.
        Exists MI nowb PA1 (s1, x1, ck1, y1) (t2, ck2, h2) Q M2 H2 MR.
        unfold hhs3_p4_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app]. cbv beta iota.
        rewrite <- HeqK2.
        rewrite hhs3_p4_E1_shim, hhs3_p4_E1_resp, hhs3_p4_E1_init.
        entailer!.
Qed.

End P4E1.
