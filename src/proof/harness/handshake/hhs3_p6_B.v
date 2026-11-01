(* law handshake, phase P6, segment B = blk 4: the allocation-failure branch of A (return).
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
Local Open Scope logic.

#[local] Instance hhs3_p6_B_cceN : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.

(* the shim's globals: wg_shim_alloc_failures at the world, the rest *)
Definition hhs3_p6_B_srest (gv: globals) (S: shim) : mpred :=
  @data_at Noise.CS Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
  @data_at Noise.CS Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
  @data_at Noise.CS Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
  @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
  @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
  @data_at Noise.CS Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
  @data_at Noise.CS Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
  @data_at Noise.CS Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
  @data_at Noise.CS Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
  @data_at Noise.CS Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
  @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow) * refwarn gv.

Lemma hhs3_p6_B_ulong sh (v: val) p : @data_at Noise.CS sh tulong v p = @data_at W_handshake sh tulong v p.
Proof. apply equal_f, (@data_at_change_composite Noise.CS W_handshake _ sh tulong v v); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

Lemma hhs3_p6_B_shim gv S : shim_state gv S =
  !! shim_ok S &&
  (@data_at W_handshake Ews tulong (Vlong (s_fails S)) (gv HC._wg_shim_alloc_failures) * hhs3_p6_B_srest gv S).
Proof.
  unfold shim_state, hhs3_p6_B_srest. f_equal.
  rewrite <- !hhs3_p6_B_ulong.
  apply pred_ext; cancel.
Qed.

Lemma hhs3_p6_B_shim_fold gv S : shim_ok S ->
  @data_at W_handshake Ews tulong (Vlong (s_fails S)) (gv HC._wg_shim_alloc_failures) * hhs3_p6_B_srest gv S
  |-- shim_state gv S.
Proof. intros. rewrite hhs3_p6_B_shim. entailer!. Qed.

Lemma hhs3_p6_B_kps_nil : keypairs_rep W_handshake [] = emp.
Proof. reflexivity. Qed.

(* the peer: its keypairs struct at the world, the rest *)
Section NoiseKps.
#[local] Existing Instance Noise.CS.

Definition hhs3_p6_B_prest (sh: share) (p: val) (P: peer) : mpred :=
  field_at sh t_peer [StructField I._device] (p_device P) p *
  field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
  hs_rep sh (hs_addr p) (p_hs P) *
  field_at sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
  cookie_rep sh (cookie_addr p) (p_cookie P) *
  field_at sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
  field_at sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
  field_at sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
  spacer sh 9 16 p * spacer sh 476 480 p.

Lemma hhs3_p6_B_peer_openN sh p P :
  peer_rep sh p P =
  !! field_compatible t_peer [] p &&
  ((EX lk: val, field_at sh t_peer [StructField I._keypairs] (p_cur P, (p_prev P, (p_next P, lk))) p) *
   hhs3_p6_B_prest sh p P).
Proof.
  unfold peer_rep, hhs3_p6_B_prest, kps_rep. apply pred_ext.
  - Intros lk. assert_PROP (field_compatible t_peer [] p) as FC by entailer!.
    Exists lk.
    rewrite (field_at_data_at sh t_peer [StructField I._keypairs]).
    rewrite field_address_offset by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset.
    unfold kps_addr, OFS_PEER_KEYPAIRS. entailer!.
  - Intros lk. rename H into FC.
    rewrite (field_at_data_at sh t_peer [StructField I._keypairs]).
    rewrite field_address_offset by auto with field_compatible.
    simpl nested_field_type. simpl nested_field_offset.
    Exists lk. unfold kps_addr, OFS_PEER_KEYPAIRS. entailer!.
Qed.
End NoiseKps.

Lemma hhs3_p6_B_kps_W sh v p :
  @field_at Noise.CS sh t_peer [StructField I._keypairs] v p =
  @field_at W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._keypairs] v p.
Proof.
  apply equal_f, (@field_at_change_composite Noise.CS W_handshake _ sh t_peer _ v v);
    [apply JMeq_refl | vm_compute; reflexivity].
Qed.

Lemma hhs3_p6_B_peer_open sh p P :
  peer_rep sh p P =
  !! @field_compatible Noise.CS t_peer [] p &&
  ((EX lk: val, @field_at W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._keypairs]
                  (p_cur P, (p_prev P, (p_next P, lk))) p) *
   hhs3_p6_B_prest sh p P).
Proof.
  rewrite hhs3_p6_B_peer_openN. f_equal. f_equal. apply pred_ext; Intros lk; Exists lk;
    rewrite hhs3_p6_B_kps_W; apply derives_refl.
Qed.

Lemma hhs3_p6_B_bytes_eqb_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

Lemma hhs3_p6_B_snap_refl s : snap_eqb s s = true.
Proof.
  destruct s as [[ep et ei] n hd [st lic sid eph rs re ss psk h ck ts ri]].
  unfold snap_eqb, entry_eqb, hs_eqb; simpl.
  rewrite !Int.eq_true, !Int64.eq_true, !hhs3_p6_B_bytes_eqb_refl, !Bool.eqb_reflx.
  destruct (EqDec_val ep ep); [|congruence]. destruct (EqDec_val n n); [|congruence].
  destruct (EqDec_val sid sid); [|congruence]. reflexivity.
Qed.

Lemma hhs3_p6_B_init_free sh m M : init_rep sh m M |-- @data_at_ W_handshake sh t_init m.
Proof. unfold init_rep. Intros. rewrite <- hhs3_conv_init. apply data_at_data_at_. Qed.

Lemma hhs3_p6_B_resp_free sh m M : resp_rep sh m M |-- @data_at_ W_handshake sh t_resp m.
Proof. unfold resp_rep. Intros. rewrite <- hhs3_conv_resp. apply data_at_data_at_. Qed.

Lemma hhs3_p6_B_hout sh bs p n : Zlength bs = n -> hbytes sh bs p |-- hout sh n p.
Proof. intros <-. unfold hbytes, hout. apply data_at_data_at_. Qed.

Lemma hhs3_p6_B_snap_out sh v p : @data_at HCS sh t_hsnap v p |-- @data_at_ HCS sh t_hsnap p.
Proof. apply data_at_data_at_. Qed.

Lemma hhs3_p6_B_hmac_len key m : Zlength (hmac key m) = 32.
Proof. unfold hmac, HASH, model.blake2s, model.b2s_digest_stream, model.b2s_out. rewrite Zlength_map. reflexivity. Qed.

Lemma hhs3_p6_B_TA1 L I :
  t_D (hhs3_TA1 L I) = [(hs_addr (l_pb L), Tsh, mkEntry (l_pb L) IDX_HANDSHAKE (i_idx I))] /\
  t_L (hhs3_TA1 L I) = [hs_addr (l_pb L)].
Proof.
  unfold hhs3_TA1, t_insert, t_set_index, hhs3_TA0, t_upd, t_entry, hhs3_EB. simpl.
  destruct (EqDec_val (hs_addr (l_pb L)) (hs_addr (l_pb L))); [| congruence]. simpl.
  destruct (EqDec_val (hs_addr (l_pb L)) (hs_addr (l_pb L))); [| congruence]. auto.
Qed.

Lemma hhs3_p6_B_add1 x : Int64.add x Int64.one <> x.
Proof.
  intros E. apply (f_equal (fun y => Int64.sub y x)) in E.
  rewrite Int64.sub_add_l, Int64.sub_idem, Int64.add_zero_l in E. apply Int64.one_not_zero; exact E.
Qed.

Lemma hhs3_p6_B_TB1 L Q : exists Eb, t_D (hhs3_TB1 L Q) = [(hs_addr (l_pa L), Tsh, Eb)].
Proof.
  unfold hhs3_TB1, t_insert, t_set_index, hhs3_TB0, t_upd, t_entry. simpl.
  destruct (EqDec_val (hs_addr (l_pa L)) (hs_addr (l_pa L))); [| congruence]. simpl. eauto.
Qed.

Ltac hhs3_p6_B_absurd :=
  first [ discriminate | exfalso; apply Int.one_not_zero; assumption
        | exfalso; apply Int.one_not_zero; symmetry; assumption | exfalso; auto | contradiction ].

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p6_B_ok {Espec: OracleKind} gv L FR V :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hhs3_p6_pure x25519 aead_enc aead_dec -> hhs3_p6_free_stmt x25519 ->
  hhs3_p6_ctx x25519 aead_enc aead_dec L V ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p6_SA x25519 gv L FR V) hhs3_p6_B
    (overridePost (hhs3_p6_SB x25519 gv L FR V) (hhs3_R gv)).
Proof.
  intros HH HP HF HC. unfold hhs3_p6_SA, hhs3_p6_SB, hhs3_p6_SBC, hhs3_Delta, hhs3_R, hhs3_p6_B.
  apply hhs3_post_canon.
  simplify_func_tycontext. abbreviate_semax.
  Intros ka.
  unfold hhs3_p6_sep, hhs3_setup_sep, hhs3_globs, hhs3_p6_locals, hhs3_lvars, hhs3_cnt_temps. cbn [app].
  destruct HP as (FA & FB & CKs & MS).
  pose proof (MS (proj1 HH) (proj1 (proj2 HH)) L V HC FA FB) as (MA0 & MA1 & _).
  pose proof (FA (proj1 HH) (proj1 (proj2 HH)) L V HC) as (EPB2 & _ & _ & _ & Hsid).
  pose proof HC as (Hrun & (_ & _ & Hfl) & _).
  destruct (eq_dec ka nullval) as [-> | Hka].
  - rewrite MA0. cbn [fst snd kw_T kw_S kw_KS].
    assert (Hcur: p_cur (hhs3_p6_PBa V) = nullval).
    { unfold hhs3_p6_PBa. rewrite EPB2. unfold hhs3_p6_PB2n. destruct (w_ST2 V). reflexivity. }
    assert (Hsid2: hs_sid (p_hs (hhs3_p6_PBa V)) = id_addr (l_wa L)).
    { unfold hhs3_p6_PBa. rewrite EPB2. unfold hhs3_p6_PB2n. destruct (w_ST2 V). exact Hsid. }
    destruct (hhs3_p6_B_TA1 L (w_I V)) as [TD TL].
    rewrite hhs3_p6_B_shim. Intros.
    forward.
    forward_if.
    2: { exfalso. rewrite Hfl in *. apply Int64.same_if_eq in H1. apply (hhs3_p6_B_add1 (w_l0 V)); exact H1. }
    set (SN := snap_of (hhs3_TA1 L (w_I V)) (hs_addr (l_pb L)) (hhs3_p6_EB1 L V) (p_hs (hhs3_p6_PBa V))).
    match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
    { apply ENTAIL_refl. }
    { forward_if (temp HC._t'158 (Vint Int.one)).
      { unfold hhs3_p6_snapA. fold SN.
        forward_call (Tsh, l_snap L, SN, Tsh, l_pb L, hhs3_p6_PBa V, Tsh, l_ita L, hhs3_TA1 L (w_I V),
                      hhs3_p6_EB1 L V, Tsh, l_wa L, hhs3_DA x25519 (w_R V) L).
        { unfold hs_cmp_pre, SN, snap_of, t_entry. rewrite TD, TL. simpl.
          destruct (EqDec_val (hs_addr (l_pb L)) (hs_addr (l_pb L))); [|congruence].
          simpl. unfold hhs3_p6_EB1. simpl. repeat split; auto. }
        replace (snap_eqb SN _) with true by (symmetry; apply (hhs3_p6_B_snap_refl SN)).
        forward. entailer!. }
      { exfalso. auto. }
      forward_if (temp HC._t'160 (Vint Int.one)).
      { rewrite hhs3_p6_B_peer_open. Intros lk. rewrite Hcur.
        forward. forward.
        entailer!. rewrite hhs3_p6_B_peer_open, Hcur.
        apply andp_right; [apply prop_right; assumption |]. Exists lk. cancel. }
      { hhs3_p6_B_absurd. }
      forward_if. { hhs3_p6_B_absurd. } forward. entailer!. }
    { forward. apply ENTAIL_refl. }
    sep_apply (hhs3_p6_B_shim_fold gv _ H0).
    sep_apply (hhs3_p6_B_init_free Ews (w_m1 V) (hhs3_M1m x25519 (w_R V) (w_M1 V))).
    sep_apply (hhs3_p6_B_resp_free Ews (w_m2 V) (hhs3_M2m x25519 (w_R V) (w_M2 V))).
    unfold hhs3_tok.
    assert_PROP (isptr (w_m1 V) /\ isptr (w_m2 V)) as Pm12 by entailer!. destruct Pm12 as [Pm1 Pm2].
    forward_call (t_init, w_m1 V, gv).
    { rewrite if_false by (intro E; rewrite E in Pm1; contradiction). cancel. }
    forward_call (t_resp, w_m2 V, gv).
    { rewrite if_false by (intro E; rewrite E in Pm2; contradiction). cancel. }
    forward.
    unfold hhs3_p6_snapA, hhs3_p6_first, hhs3_p6_second.
    sep_apply (hhs3_p6_B_snap_out Tsh (hsnap_val SN) (l_snap L)).
    sep_apply (hhs3_p6_B_hout Tsh (kdf1 (hhs3_p6_ck V) []) (l_first L) 32 (hhs3_p6_B_hmac_len _ _)).
    sep_apply (hhs3_p6_B_hout Tsh (kdf2 (hhs3_p6_ck V) []) (l_second L) 32 (hhs3_p6_B_hmac_len _ _)).
    destruct (w_MI V) as [[[[[E encs] enct] ep] ck] h].
    sep_apply (@data_at_data_at_ HCS Tsh t_minit (minit_val E encs enct ep ck h) (l_mi L)).
    destruct (w_MR V) as [[[[E2 encn] ep2] ck2] h2].
    sep_apply (@data_at_data_at_ HCS Tsh t_mresp (mresp_val E2 encn ep2 ck2 h2) (l_mr L)).
    destruct (w_ST2 V) as [ck3 h3].
    sep_apply (@data_at_data_at_ HCS Tsh t_mstate (mstate_val ck3 h3) (l_st2 L)).
    destruct (hhs3_p6_B_TB1 L (w_Q V)) as [Eb HEb].
    eapply derives_trans; [| eapply derives_trans;
      [apply (HF (proj1 HH) gv L FR (w_R V) (shim_alloc_fail (w_S V)) Int64.zero (hhs3_TA1 L (w_I V))
                 (hhs3_TB1 L (w_Q V)) _ Eb (hhs3_p6_PBa V) (hhs3_p6_PAa x25519 V) Hrun TD HEb) | ]].
    { unfold hhs3_setup_sep, hhs3_globs, hhs3_scr_tmp. simpl fold_right_sepcon. cancel. }
    { unfold hhs3_p6_frame. simpl fold_right_sepcon. cancel. }
  - rewrite (MA1 ka Hka (H Hka)). cbn [fst snd kw_T kw_S kw_KS].
    rewrite hhs3_p6_B_shim. Intros.
    forward.
    forward_if.
    { exfalso. match goal with Hx: s_fails _ <> _ |- _ => apply Hx end.
      unfold hhs3_p6_S1, shim_alloc_ok. cbn [s_fails]. exact Hfl. }
    forward.
    sep_apply (hhs3_p6_B_shim_fold gv _ H0).
    Exists ka.
    unfold hhs3_p6_sep, hhs3_setup_sep, hhs3_globs, hhs3_p6_locals, hhs3_lvars, hhs3_cnt_temps. cbn [app].
    entailer!.
Qed.

End Seg.
