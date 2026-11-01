(* law handshake: main's phase P2, segment B (statements 43..45): hhs3_p2_SA x25519 aead_enc gv L FR -> hhs3_p2_SB x25519 aead_enc gv L FR.
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

#[local] Instance hhs3_p2_B_cceN : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.
#[local] Instance hhs3_p2_B_cceH : change_composite_env HCS W_handshake.
Proof. make_cs_preserve HCS W_handshake. Defined.

Lemma hhs3_p2_B_mident_W sh I p :
  @data_at HCS sh t_mident (mident_val I) p = @data_at W_handshake sh t_mident (mident_val I) p.
Proof.
  exact (f_equal (fun f => f p) (@data_at_change_composite HCS W_handshake hhs3_p2_B_cceH sh t_mident (mident_val I)
    (mident_val I) (@JMeq_refl _ (mident_val I)) ltac:(vm_compute; reflexivity))).
Qed.

Lemma hhs3_p2_B_bytes_eqb_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

Lemma hhs3_p2_B_snap_refl s : snap_eqb s s = true.
Proof.
  destruct s as [[ep et ei] n hd [st lic sid eph rs re ss psk h ck ts ri]].
  unfold snap_eqb, entry_eqb, hs_eqb; simpl.
  rewrite !Int.eq_true, !Int64.eq_true, !hhs3_p2_B_bytes_eqb_refl, !Bool.eqb_reflx.
  destruct (EqDec_val ep ep); [|congruence]. destruct (EqDec_val n n); [|congruence].
  destruct (EqDec_val sid sid); [|congruence]. reflexivity.
Qed.

Lemma hhs3_p2_B_ilen M : im_ok M -> Zlength (init_bytes M) = 148.
Proof.
  intros (A & B & C & D & E). unfold init_bytes. rewrite !Zlength_app, A, B, C, D, E. reflexivity.
Qed.

Lemma hhs3_p2_B_init_free sh m M : init_rep sh m M |-- @data_at_ W_handshake sh t_init m.
Proof. unfold init_rep. Intros. rewrite <- hhs3_conv_init. apply data_at_data_at_. Qed.

Lemma hhs3_p2_B_tslen I : Zlength (hhs3_ts I) = 12.
Proof. unfold hhs3_ts, tai64n. rewrite Zlength_app. reflexivity. Qed.

Lemma hhs3_p2_B_hout sh bs p n : Zlength bs = n -> hbytes sh bs p |-- hout sh n p.
Proof. intros <-. unfold hbytes, hout. apply data_at_data_at_. Qed.

Lemma hhs3_p2_B_snap_out sh v p : @data_at HCS sh t_hsnap v p |-- @data_at_ HCS sh t_hsnap p.
Proof. apply data_at_data_at_. Qed.

(* ---------------------------------------------------------------------- *)
(* Opening the five input buffers of m_create_initiation at one share Ews *)
(* ---------------------------------------------------------------------- *)
Local Open Scope logic.

Lemma hhs3_p2_B_tuchar_cs {cs1 cs2: compspecs} sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible, size_compatible, align_compatible. destruct p; simpl; try tauto.
  assert (A: forall ce, align_compatible_rec ce (tarray tuchar n) (Ptrofs.unsigned i)).
  { intros ce. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  pose proof (A (@cenv_cs cs1)). pose proof (A (@cenv_cs cs2)). tauto.
Qed.

Lemma hhs3_p2_B_tsplit bs p : hbytes Tsh bs p = hbytes Ews bs p * hbytes (Share.comp Ews) bs p.
Proof. unfold hbytes. symmetry. apply data_at_share_join. apply join_comp_Tsh. Qed.

Lemma hhs3_p2_B_wand (P Q C: mpred) : P |-- Q * C -> C * Q |-- P -> P |-- Q * (Q -* P).
Proof.
  intros A B. eapply derives_trans; [apply A|]. apply sepcon_derives; [apply derives_refl|].
  apply wand_sepcon_adjoint. exact B.
Qed.

Section DevOpen.
#[local] Existing Instance Noise.CS.

Lemma hhs3_p2_B_sid_split a pub priv (lk: val) b :
  data_at Tsh t_sid (bytes pub, (bytes priv, (lk, b))) a =
  !! field_compatible t_sid [] a &&
  (data_at Tsh (tarray tuchar 32) (bytes pub) a * field_at Tsh t_sid (DOT I._static_private) (bytes priv) a *
   field_at Tsh t_sid (DOT I._lock) lk a * field_at Tsh t_sid (DOT I._has_identity) b a * spacer Tsh 69 72 a).
Proof.
  apply pred_ext.
  - assert_PROP (field_compatible t_sid [] a) by entailer!.
    unfold_data_at (data_at _ _ _ a).
    rewrite (field_at_data_at Tsh t_sid (DOT I._static_public)).
    rewrite field_address_offset by auto with field_compatible. simpl.
    rewrite isptr_offset_val_zero by auto with field_compatible. entailer!.
  - Intros. unfold_data_at (data_at _ t_sid _ a).
    rewrite (field_at_data_at Tsh t_sid (DOT I._static_public)).
    rewrite field_address_offset by auto with field_compatible. simpl.
    rewrite isptr_offset_val_zero by auto with field_compatible. entailer!.
Qed.

Lemma hhs3_p2_B_dev_open wg D :
  device_rep Tsh wg D |--
  !! id_ok (d_id D) &&
  (hbytes Ews (id_pub (d_id D)) (id_addr wg) * (hbytes Ews (id_pub (d_id D)) (id_addr wg) -* device_rep Tsh wg D)).
Proof.
  assert_PROP (id_ok (d_id D)) as Hid by (unfold device_rep, identity_rep; Intros lk; apply prop_right; assumption).
  pose proof Hid as [Lp Lq].
  apply andp_right; [apply prop_right; exact Hid |].
  assert (Eq: data_at Tsh (tarray tuchar 32) (bytes (id_pub (d_id D))) (id_addr wg) =
              hbytes Ews (id_pub (d_id D)) (id_addr wg) * hbytes (Share.comp Ews) (id_pub (d_id D)) (id_addr wg)).
  { rewrite <- hhs3_p2_B_tsplit. unfold hbytes. rewrite Lp. apply hhs3_p2_B_tuchar_cs. }
  apply hhs3_p2_B_wand with
    (C := EX lk: val, hbytes (Share.comp Ews) (id_pub (d_id D)) (id_addr wg) *
          (!! (@field_compatible Noise.CS t_dev [] wg /\ @field_compatible Noise.CS t_sid [] (id_addr wg)) &&
          (@field_at Noise.CS Tsh t_dev [StructField I._dev] (d_dev D) wg *
           checker_rep Tsh (cc_addr wg) (d_cc D) *
           @field_at Noise.CS Tsh t_dev [StructField I._peer_hashtable] (d_ptab D) wg *
           @field_at Noise.CS Tsh t_dev [StructField I._index_hashtable] (d_itab D) wg *
           @field_at Noise.CS Tsh t_sid (DOT I._static_private) (bytes (id_priv (d_id D))) (id_addr wg) *
           @field_at Noise.CS Tsh t_sid (DOT I._lock) lk (id_addr wg) *
           @field_at Noise.CS Tsh t_sid (DOT I._has_identity) (Val.of_bool (id_has (d_id D))) (id_addr wg) *
           spacer Tsh 69 72 (id_addr wg)))).
  - unfold device_rep, identity_rep. Intros lk. Exists lk. rewrite hhs3_p2_B_sid_split. Intros.
    rewrite Eq. entailer!.
  - Intros lk. unfold device_rep, identity_rep. Exists lk. rewrite hhs3_p2_B_sid_split. rewrite Eq. entailer!.
Qed.

Lemma hhs3_p2_B_shim_open gv S :
  shim_state gv S |--
  !! (Zlength (s_log S) = 32) &&
  (hbytes Ews (s_log S) (gv _wg_shim_random_log) * (hbytes Ews (s_log S) (gv _wg_shim_random_log) -* shim_state gv S)).
Proof.
  assert_PROP (shim_ok S) as Hok by (unfold shim_state; entailer!).
  pose proof Hok as [Ll Lp].
  apply andp_right; [apply prop_right; exact Ll |].
  assert (Eq: hbytes Ews (s_log S) (gv _wg_shim_random_log) =
              @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log)).
  { unfold hbytes. rewrite Ll. apply hhs3_p2_B_tuchar_cs. }
  apply hhs3_p2_B_wand with
    (C := @data_at Noise.CS Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
   @data_at Noise.CS Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
   @data_at Noise.CS Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
   @data_at Noise.CS Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
   @data_at Noise.CS Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   @data_at Noise.CS Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
   @data_at Noise.CS Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   @data_at Noise.CS Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow) * refwarn gv).
  - rewrite Eq. unfold shim_state. Intros. cancel.
  - rewrite Eq. unfold shim_state. entailer!.
Qed.
End DevOpen.

Lemma hhs3_p2_B_ib_open I p : Zlength (mi_pub I) = 32 ->
  @data_at HCS Tsh t_mident (mident_val I) p |--
  hbytes Ews (mi_pub I) (offset_val 32 p) * (hbytes Ews (mi_pub I) (offset_val 32 p) -* @data_at HCS Tsh t_mident (mident_val I) p).
Proof.
  intros Hl.
  apply hhs3_p2_B_wand with
    (C := hbytes (Share.comp Ews) (mi_pub I) (offset_val 32 p) *
          (!! @field_compatible HCS t_mident [] p &&
           (@field_at HCS Tsh t_mident (DOT HH._priv) (bytes (mi_priv I)) p *
            @field_at HCS Tsh t_mident (DOT HH._ok) (Vint (if mi_ok I then Int.one else Int.zero)) p))).
  - assert_PROP (@field_compatible HCS t_mident [] p) as FC by entailer!.
    rewrite <- sepcon_assoc, <- hhs3_p2_B_tsplit. unfold hbytes. rewrite Hl.
    unfold_data_at (@data_at HCS _ t_mident _ p).
    rewrite (@field_at_data_at HCS Tsh t_mident (DOT HH._pub)).
    rewrite field_address_offset by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset. entailer!.
  - Intros. rewrite (sepcon_comm _ (hbytes Ews _ _)), <- sepcon_assoc, <- hhs3_p2_B_tsplit.
    unfold hbytes. rewrite Hl.
    unfold_data_at (@data_at HCS _ t_mident _ p).
    rewrite (@field_at_data_at HCS Tsh t_mident (DOT HH._pub)).
    rewrite field_address_offset by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset. entailer!.
Qed.

Local Open Scope Z_scope.

Ltac hhs3_p2_B_absurd :=
  first [ discriminate
        | exfalso; match goal with Hx: _ <> _ |- _ => apply Hx; reflexivity end
        | exfalso; match goal with Hx: Int.repr ?a = Int.zero |- _ =>
            apply (f_equal Int.unsigned) in Hx; rewrite Int.unsigned_repr in Hx by rep_lia; discriminate end
        | exfalso; match goal with Hx: @eq int _ _ |- _ =>
            apply (f_equal Int.unsigned) in Hx; vm_compute in Hx; discriminate end ].

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p2_B_ok {Espec: OracleKind} gv L FR :
  hhs3_p2_agree_stmt x25519 aead_enc -> hhs3_p2_free_stmt x25519 ->
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p2_SA x25519 aead_enc gv L FR) hhs3_p2_B
    (overridePost (hhs3_p2_SB x25519 aead_enc gv L FR) (hhs3_R gv)).
Proof.
  intros HA HF HH. unfold hhs3_p2_SA, hhs3_Delta, hhs3_R, hhs3_p2_B. apply hhs3_post_canon.
  simplify_func_tycontext. abbreviate_semax.
  Intros R S m1 m2 a0 f0 l0 I ok1 M H.
  unfold hhs3_setup_sep, hhs3_globs, hhs3_p2_scr, hhs3_lvars, hhs3_cnt_temps. cbn [app].
  rewrite (hhs3_p2_B_mident_W Tsh (hhs3_IA x25519 R) (l_ia L)).
  forward.
  assert (HidA: id_has (d_id (hhs3_DA x25519 R L)) = mi_ok (hhs3_IA x25519 R)) by reflexivity.
  unfold mident_val at 1. cbv beta iota.
  destruct (mi_ok (hhs3_IA x25519 R)) eqn:EA.
  2: {
    assert (Eci: ok1 = false /\ M = i_M0 I /\ H = p_hs (hhs3_PB0 x25519 R L)).
    { unfold hhs3_ci, create_initiation_model in H5. rewrite HidA in H5. simpl in H5. inversion H5; auto. }
    destruct Eci as (-> & -> & ->).
    set (PB0 := hhs3_PB0 x25519 R L).
    set (SN := snap_of (hhs3_TA0 L) (hs_addr (l_pb L)) (hhs3_EB L) (p_hs PB0)).
    apply semax_if_seq. forward_if.
    2: { exfalso. apply H. reflexivity. }
    match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
    { apply ENTAIL_refl. }
    { forward_if (temp HC._t'23 (Vint Int.one)).
      { forward_call (Tsh, l_snap L, SN, Tsh, l_pb L, p_set_hs PB0 (p_hs PB0), Tsh, l_ita L, hhs3_TA0 L,
                      hhs3_EB L, Tsh, l_wa L, hhs3_DA x25519 R L).
        { unfold hs_cmp_pre, SN, snap_of, t_entry, hhs3_TA0, hhs3_EB; simpl sfind.
          rewrite if_true by reflexivity. repeat split; auto. }
        replace (snap_eqb SN _) with true by (symmetry; apply (hhs3_p2_B_snap_refl SN)).
        forward. entailer!. }
      { exfalso. auto. }
      forward_if. { discriminate. } forward. entailer!. }
    { forward. apply ENTAIL_refl. }
    forward_call (Tsh, l_img L, Ews, m1, i_M0 I).
    assert (LI: Zlength (init_bytes (i_M0 I)) = 148) by (apply hhs3_p2_B_ilen; auto).
    match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
    { apply ENTAIL_refl. }
    { forward_call (Tsh, l_img L, init_bytes (i_M0 I), Tsh, l_imgb L, init_bytes (i_M0 I)).
      { rewrite LI. entailer!. }
      rewrite hhs3_p2_B_bytes_eqb_refl.
      forward_if. { discriminate. } forward. entailer!. }
    { forward. apply ENTAIL_refl. }
    forward. unfold mident_val at 1. cbv beta iota. rewrite EA.
    apply semax_if_seq. forward_if. { hhs3_p2_B_absurd. }
    forward_if. 2: { hhs3_p2_B_absurd. }
    sep_apply (hhs3_p2_B_init_free Ews m1 (i_M0 I)).
    rewrite hhs3_conv_resp. unfold hhs3_tok.
    assert_PROP (isptr m1 /\ isptr m2) as Pm12 by entailer!. destruct Pm12 as [Pm1 Pm2].
    forward_call (t_init, m1, gv).
    { rewrite if_false by (intro; subst; contradiction). cancel. }
    forward_call (t_resp, m2, gv).
    { rewrite if_false by (intro; subst; contradiction). cancel. }
    forward.
    rewrite <- hhs3_p2_B_mident_W.
    sep_apply (hhs3_p2_B_hout Tsh (init_bytes (i_M0 I)) (l_img L) 148 LI).
    sep_apply (hhs3_p2_B_hout Tsh (init_bytes (i_M0 I)) (l_imgb L) 148 LI).
    sep_apply (hhs3_p2_B_hout Tsh (hhs3_ts I) (l_ts L) 12 (hhs3_p2_B_tslen I)).
    sep_apply (hhs3_p2_B_snap_out Tsh (hsnap_val SN) (l_snap L)).
    eapply derives_trans; [| eapply derives_trans;
      [apply (HF (proj1 HH) gv L FR R S (hhs3_TA0 L) (hhs3_TB0 L) (hhs3_EB L) (hhs3_EA L)
                 (p_set_hs PB0 (p_hs PB0)) (hhs3_PA0 x25519 R L) H0 eq_refl eq_refl) | ]].
    { unfold hhs3_setup_sep, hhs3_globs, hhs3_scr_tmp. simpl fold_right_sepcon. cancel. apply derives_refl. }
    { unfold hhs3_p2_frame. simpl fold_right_sepcon. cancel. }
    }
  (* A has an identity: m_create_initiation *)
  pose proof (proj1 HH) as Hx.
  apply semax_if_seq. forward_if. { hhs3_p2_B_absurd. }
  forward. unfold mident_val at 1. cbv beta iota. rewrite EA.
  apply semax_if_seq. forward_if. 2: { hhs3_p2_B_absurd. }
  assert (LpubB: Zlength (mi_pub (hhs3_IB x25519 R)) = 32) by apply Hx.
  assert (Lss: Zlength (hhs3_ssa x25519 R) = 32).
  { unfold hhs3_ssa, m_precomputed_model. match goal with |- context [if ?b then _ else _] => destruct b end; [apply Hx | reflexivity]. }
  specialize (H7 eq_refl).
  sep_apply (hhs3_p2_B_dev_open (l_wa L) (hhs3_DA x25519 R L)). Intros. rename H9 into HidDA.
  sep_apply (hhs3_p2_B_shim_open gv S). Intros. rewrite H7.
  sep_apply (hhs3_p2_B_ib_open (hhs3_IB x25519 R) (l_ib L) LpubB).
  rewrite (hhs3_p2_B_tsplit (hhs3_ssa x25519 R)), (hhs3_p2_B_tsplit (hhs3_ts I)).
  unfold hhs3_consts, wg_consts. Intros.
  forward_call (gv, Tsh, l_mi L, Ews, id_addr (l_wa L), id_pub (d_id (hhs3_DA x25519 R L)), offset_val 32 (l_ib L),
                mi_pub (hhs3_IB x25519 R), l_ssa L, hhs3_ssa x25519 R, gv _wg_shim_random_log, i_r I, l_ts L, hhs3_ts I).
  { match goal with Hq: id_ok _ |- _ => apply Hq end. }
  sep_apply (modus_ponens_wand (hbytes Ews (mi_pub (hhs3_IB x25519 R)) (offset_val 32 (l_ib L)))).
  sep_apply (modus_ponens_wand (hbytes Ews (i_r I) (gv _wg_shim_random_log))).
  sep_apply (modus_ponens_wand (hbytes Ews (id_pub (d_id (hhs3_DA x25519 R L))) (id_addr (l_wa L)))).
  sep_apply (derives_refl' _ _ (eq_sym (hhs3_p2_B_tsplit (hhs3_ssa x25519 R) (l_ssa L)))).
  sep_apply (derives_refl' _ _ (eq_sym (hhs3_p2_B_tsplit (hhs3_ts I) (l_ts L)))).
  change (m_create_initiation_model x25519 aead_enc (id_pub (d_id (hhs3_DA x25519 R L))) (mi_pub (hhs3_IB x25519 R))
            (hhs3_ssa x25519 R) (i_r I) (hhs3_ts I)) with (hhs3_mi x25519 aead_enc R L I).
  pose proof (HA Hx R L I H0 H3 EA) as HAg.
  assert (Eok1: hhs3_ok1 x25519 R = mi_ok (hhs3_IB x25519 R)) by (unfold hhs3_ok1; rewrite EA; reflexivity).
  rewrite Eok1.
  destruct (hhs3_mi x25519 aead_enc R L I) as [MI|] eqn:EMI.
  - (* the model succeeds: so does the kernel *)
    destruct MI as [[[[[E encs] enct] ep] ck] h].
    assert (Eok: ok1 = true) by (rewrite HAg in H5; inversion H5; auto). subst ok1.
    specialize (H6 eq_refl). specialize (H8 eq_refl).
    match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
    { apply ENTAIL_refl. }
    { forward_if. { hhs3_p2_B_absurd. } forward. entailer!. }
    { forward. apply ENTAIL_refl. }
    assert (Eok2: hhs3_ok2 x25519 R I = andb (mi_ok (hhs3_IB x25519 R)) (negb (is_zero (hhs3_ts I)))) by reflexivity.
    remember (mi_ok (hhs3_IB x25519 R)) as bB eqn:EB.
    forward_if (temp HC._t'27 (Vint (if bB then Int.one else Int.zero))).
    { forward. destruct bB; [entailer! | hhs3_p2_B_absurd]. }
    { forward. destruct bB; [hhs3_p2_B_absurd | entailer!]. }
    forward_if (temp HC._t'28 (Vint (if andb bB (negb (is_zero (hhs3_ts I))) then Int.one else Int.zero))).
    { forward_call (Tsh, l_ts L, hhs3_ts I).
      { rewrite hhs3_p2_B_tslen. rep_lia. }
      forward. destruct bB; [| hhs3_p2_B_absurd].
      destruct (is_zero (hhs3_ts I)); entailer!. }
    { forward. destruct bB; [hhs3_p2_B_absurd | entailer!]. }
    forward.
    forward_if. { hhs3_p2_B_absurd. }
    assert (HAI: hhs3_after_init x25519 aead_enc R L I M H (E, encs, enct, ep, ck, h))
      by exact (conj EA (conj H5 (conj EMI (conj H6 (conj H2 (conj H3 H4)))))).
    forward.
    unfold hhs3_p2_SB. Exists R S m1 m2 a0 f0 l0 I M H (E, encs, enct, ep, ck, h).
    unfold hhs3_p2_sepB, hhs3_setup_sep, hhs3_globs, hhs3_p2_scr, hhs3_lvars, hhs3_cnt_temps, hhs3_consts, wg_consts.
    cbn [app].
    rewrite <- hhs3_p2_B_mident_W. rewrite Eok2.
    entailer!.
  - (* the model fails: so does the kernel *)
    assert (Eok: ok1 = false) by (rewrite H5 in HAg; exact HAg). subst ok1.
    match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
    { apply ENTAIL_refl. }
    { forward_if. { hhs3_p2_B_absurd. } forward. entailer!. }
    { forward. apply ENTAIL_refl. }
    forward_if (temp HC._t'27 (Vint Int.zero)).
    { forward. entailer!. }
    { forward. entailer!. }
    forward_if (temp HC._t'28 (Vint Int.zero)).
    { hhs3_p2_B_absurd. }
    { forward. entailer!. }
    forward.
    forward_if. 2: { hhs3_p2_B_absurd. }
    sep_apply (hhs3_p2_B_init_free Ews m1 M).
    rewrite hhs3_conv_resp. unfold hhs3_tok.
    assert_PROP (isptr m1 /\ isptr m2) as Pm12 by entailer!. destruct Pm12 as [Pm1 Pm2].
    forward_call (t_init, m1, gv).
    { rewrite if_false by (intro; subst; contradiction). cancel. }
    forward_call (t_resp, m2, gv).
    { rewrite if_false by (intro; subst; contradiction). cancel. }
    forward.
    rewrite <- hhs3_p2_B_mident_W.
    sep_apply (hhs3_p2_B_hout Tsh (init_bytes (i_M0 I)) (l_imgb L) 148 (hhs3_p2_B_ilen _ H2)).
    sep_apply (hhs3_p2_B_hout Tsh (hhs3_ts I) (l_ts L) 12 (hhs3_p2_B_tslen I)).
    sep_apply (hhs3_p2_B_snap_out Tsh (hsnap_val (snap_of (hhs3_TA0 L) (hs_addr (l_pb L)) (hhs3_EB L)
                 (p_hs (hhs3_PB0 x25519 R L)))) (l_snap L)).
    eapply derives_trans; [| eapply derives_trans;
      [apply (HF Hx gv L FR R S (hhs3_TA0 L) (hhs3_TB0 L) (hhs3_EB L) (hhs3_EA L)
                 (p_set_hs (hhs3_PB0 x25519 R L) H) (hhs3_PA0 x25519 R L) H0 eq_refl eq_refl) | ]].
    { unfold hhs3_setup_sep, hhs3_globs, hhs3_scr_tmp, hhs3_consts, wg_consts. simpl fold_right_sepcon. cancel. }
    { unfold hhs3_p2_frame. simpl fold_right_sepcon. cancel. }
Qed.

End Seg.
