(* law handshake, phase P6, segment H = statements 114..120: the final CHECKs, free(m1), free(m2), return 0.
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
Require Import WgNoise.proof.harness.handshake.hhs3_p6_B.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.
Local Open Scope logic.

#[local] Instance hhs3_p6_H_cceN : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.

(* pa.refcount / pb.refcount at the world *)
Lemma hhs3_p6_H_ref_W sh v p :
  @field_at Noise.CS sh t_peer [StructField I._refcount] v p =
  @field_at W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._refcount] v p.
Proof.
  apply equal_f, (@field_at_change_composite Noise.CS W_handshake _ sh t_peer _ v v);
    [apply JMeq_refl | vm_compute; reflexivity].
Qed.

(* an index table's head at the world *)
Lemma hhs3_p6_H_itab_W sh v p :
  @data_at Noise.CS sh t_itab v p = @data_at W_handshake sh (Tstruct HC._index_hashtable noattr) v p.
Proof.
  apply equal_f, (@data_at_change_composite Noise.CS W_handshake _ sh t_itab v v);
    [apply JMeq_refl | vm_compute; reflexivity].
Qed.

Lemma hhs3_p6_H_itable sht tab T :
  itable sht tab T =
  !! itable_wf T &&
  (@data_at W_handshake sht (Tstruct HC._index_hashtable noattr) (hd nullval (t_L T)) tab *
   VST.msl.iter_sepcon.iter_sepcon (pool_item_rep (t_L T)) (t_D T)).
Proof. unfold itable. rewrite hhs3_p6_H_itab_W. reflexivity. Qed.

(* the shim's globals: the three counters at the world, the rest *)
Definition hhs3_p6_H_srest (gv: globals) (S: shim) : mpred :=
  @data_at Noise.CS Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
  @data_at Noise.CS Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
  @data_at Noise.CS Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
  @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
  @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
  @data_at Noise.CS Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
  @data_at Noise.CS Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
  @data_at Noise.CS Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
  @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow) * refwarn gv.

Lemma hhs3_p6_H_shim gv S : shim_state gv S =
  !! shim_ok S &&
  (@data_at W_handshake Ews tulong (Vlong (s_allocs S)) (gv HC._wg_shim_allocs) *
   @data_at W_handshake Ews tulong (Vlong (s_frees S)) (gv HC._wg_shim_frees) *
   @data_at W_handshake Ews tulong (Vlong (s_fails S)) (gv HC._wg_shim_alloc_failures) *
   hhs3_p6_H_srest gv S).
Proof.
  unfold shim_state, hhs3_p6_H_srest. f_equal.
  rewrite <- !hhs3_p6_B_ulong.
  apply pred_ext; cancel.
Qed.

Lemma hhs3_p6_H_shim_fold gv S : shim_ok S ->
  @data_at W_handshake Ews tulong (Vlong (s_allocs S)) (gv HC._wg_shim_allocs) *
  @data_at W_handshake Ews tulong (Vlong (s_frees S)) (gv HC._wg_shim_frees) *
  @data_at W_handshake Ews tulong (Vlong (s_fails S)) (gv HC._wg_shim_alloc_failures) *
  hhs3_p6_H_srest gv S |-- shim_state gv S.
Proof. intros. rewrite hhs3_p6_H_shim. entailer!. Qed.

Lemma hhs3_p6_H_two x : Int64.sub (Int64.add (Int64.add x Int64.one) Int64.one) x = Int64.repr 2.
Proof.
  rewrite !Int64.sub_add_l, Int64.sub_idem, Int64.add_zero_l. reflexivity.
Qed.

(* folding back *)
Lemma hhs3_p6_H_fold sh p P lk :
  p_cur P = nullval -> p_prev P = nullval -> p_next P = nullval -> @field_compatible Noise.CS t_peer [] p ->
  @field_at W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._keypairs] (nullval, (nullval, (nullval, lk))) p *
  hhs3_p6_B_prest sh p P |-- peer_rep sh p P.
Proof.
  intros Hc Hp Hn FC. rewrite hhs3_p6_B_peer_open, Hc, Hp, Hn.
  apply andp_right; [apply prop_right; exact FC |]. Exists lk. cancel.
Qed.

Lemma hhs3_p6_H_itable_fold sht tab T :
  itable_wf T -> hd nullval (t_L T) = nullval ->
  @data_at W_handshake sht (Tstruct HC._index_hashtable noattr) nullval tab *
  VST.msl.iter_sepcon.iter_sepcon (pool_item_rep (t_L T)) (t_D T) |-- itable sht tab T.
Proof.
  intros W Hh. rewrite hhs3_p6_H_itable, Hh. apply andp_right; [apply prop_right; exact W | cancel].
Qed.

(* the refcount field of a peer at the world, the rest *)
Section NoiseRef.
#[local] Existing Instance Noise.CS.
Definition hhs3_p6_H_rrest (sh: share) (p: val) (P: peer) : mpred :=
  field_at sh t_peer [StructField I._device] (p_device P) p *
  field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
  kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
  hs_rep sh (hs_addr p) (p_hs P) *
  field_at sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
  cookie_rep sh (cookie_addr p) (p_cookie P) *
  field_at sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
  field_at sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
  spacer sh 9 16 p * spacer sh 476 480 p.
End NoiseRef.

Lemma hhs3_p6_H_peer_ref sh p P :
  peer_rep sh p P =
  !! @field_compatible Noise.CS t_peer [] p &&
  (@field_at W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._refcount] (Vint (p_refs P)) p *
   hhs3_p6_H_rrest sh p P).
Proof.
  unfold peer_rep, hhs3_p6_H_rrest. rewrite hhs3_p6_H_ref_W. f_equal. apply pred_ext; cancel.
Qed.

Lemma hhs3_p6_H_ref_fold sh p P r :
  p_refs P = r -> @field_compatible Noise.CS t_peer [] p ->
  @field_at W_handshake sh (Tstruct HC._wg_peer noattr) [StructField HC._refcount] (Vint r) p *
  hhs3_p6_H_rrest sh p P |-- peer_rep sh p P.
Proof. intros <- FC. rewrite hhs3_p6_H_peer_ref. apply andp_right; [apply prop_right; exact FC | cancel]. Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p6_H_ok {Espec: OracleKind} gv L FR V :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hhs3_p6_pure x25519 aead_enc aead_dec -> hhs3_p6_free_stmt x25519 ->
  hhs3_p6_ctx x25519 aead_enc aead_dec L V ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p6_SG x25519 gv L FR V) hhs3_p6_H
    (overridePost FF (hhs3_R gv)).
Proof.
  intros HH HP HF HC. unfold hhs3_p6_SG, hhs3_Delta, hhs3_R, hhs3_p6_H.
  apply hhs3_post_canon.
  simplify_func_tycontext. abbreviate_semax.
  Intros ka kb.
  unfold hhs3_p6_sep, hhs3_setup_sep, hhs3_globs, hhs3_p6_locals, hhs3_lvars, hhs3_cnt_temps. cbn [app].
  pose proof HC as (Hrun & (Ha0 & Hf0 & Hl0) & _).
  set (PB4 := p_set_slots (hhs3_p6_PB3 V ka) nullval nullval nullval).
  set (PA5 := p_set_slots (hhs3_p6_PA4 x25519 V kb) nullval nullval nullval).
  assert_PROP (@field_compatible Noise.CS t_peer [] (l_pb L) /\ @field_compatible Noise.CS t_peer [] (l_pa L))
    as FCba by (unfold peer_rep; entailer!).
  destruct FCba as [FCb FCa].
  assert_PROP (itable_wf (hhs3_p6_TA3 L V) /\ itable_wf (hhs3_p6_TB3 L V)) as WAB
    by (unfold itable; entailer!).
  destruct WAB as [WA WB].
  (* CHECK(pb.keypairs.current_keypair == NULL && pa.keypairs.next_keypair == NULL) *)
  rewrite (hhs3_p6_B_peer_open Tsh (l_pb L)), (hhs3_p6_B_peer_open Tsh (l_pa L)). Intros lka lkb.
  change (p_cur PB4) with nullval. change (p_prev PB4) with nullval. change (p_next PB4) with nullval.
  change (p_cur PA5) with nullval. change (p_prev PA5) with nullval. change (p_next PA5) with nullval.
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward.
    forward_if (temp HC._t'201 (Vint Int.one)).
    { forward. forward. entailer!. }
    { hhs3_p6_B_absurd. }
    forward_if. { hhs3_p6_B_absurd. } forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  sep_apply (hhs3_p6_H_fold Tsh (l_pb L) PB4 lka eq_refl eq_refl eq_refl FCb).
  sep_apply (hhs3_p6_H_fold Tsh (l_pa L) PA5 lkb eq_refl eq_refl eq_refl FCa).
  (* CHECK(ita.head == NULL && itb.head == NULL) *)
  rewrite (hhs3_p6_H_itable Tsh (l_ita L)), (hhs3_p6_H_itable Tsh (l_itb L)). Intros.
  change (hd nullval (t_L (hhs3_p6_TA3 L V))) with nullval.
  change (hd nullval (t_L (hhs3_p6_TB3 L V))) with nullval.
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward.
    forward_if (temp HC._t'202 (Vint Int.one)).
    { forward. forward. entailer!. }
    { hhs3_p6_B_absurd. }
    forward_if. { hhs3_p6_B_absurd. } forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  sep_apply (hhs3_p6_H_itable_fold Tsh (l_ita L) (hhs3_p6_TA3 L V) WA eq_refl).
  sep_apply (hhs3_p6_H_itable_fold Tsh (l_itb L) (hhs3_p6_TB3 L V) WB eq_refl).
  (* CHECK(allocs - allocs0 == 2 && frees - frees0 == 2 && failures == fails0) *)
  assert (HS4: s_allocs (hhs3_p6_S4 V) = Int64.add (Int64.add (w_a0 V) Int64.one) Int64.one /\
               s_frees (hhs3_p6_S4 V) = Int64.add (Int64.add (w_f0 V) Int64.one) Int64.one /\
               s_fails (hhs3_p6_S4 V) = w_l0 V).
  { unfold hhs3_p6_S4, hhs3_p6_S2, shim_free, shim_alloc_ok. cbn [s_allocs s_frees s_fails].
    rewrite Ha0, Hf0, Hl0. auto. }
  destruct HS4 as (HA4 & HF4 & HL4).
  rewrite hhs3_p6_H_shim. Intros. rewrite HA4, HF4, HL4.
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward.
    forward_if (temp HC._t'203 (Vint Int.one)).
    { forward. forward. entailer!. rewrite hhs3_p6_H_two. reflexivity. }
    { exfalso. rewrite hhs3_p6_H_two in *. auto. }
    forward_if (temp HC._t'204 (Vint Int.one)).
    { forward. forward. entailer!. rewrite Int64.eq_true. reflexivity. }
    { hhs3_p6_B_absurd. }
    forward_if. { hhs3_p6_B_absurd. } forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  rewrite <- HA4, <- HF4, <- HL4.
  match goal with Hok: shim_ok _ |- _ => sep_apply (hhs3_p6_H_shim_fold gv _ Hok) end.
  (* CHECK(pa.refcount.refcount == 1 && pb.refcount.refcount == 1) *)
  rewrite (hhs3_p6_H_peer_ref Tsh (l_pa L)), (hhs3_p6_H_peer_ref Tsh (l_pb L)). Intros.
  assert (RA: p_refs PA5 = Int.one) by reflexivity. assert (RB: p_refs PB4 = Int.one) by reflexivity.
  rewrite RA, RB.
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward.
    forward_if (temp HC._t'205 (Vint Int.one)).
    { forward. forward. entailer!. }
    { hhs3_p6_B_absurd. }
    forward_if. { hhs3_p6_B_absurd. } forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  sep_apply (hhs3_p6_H_ref_fold Tsh (l_pa L) PA5 Int.one RA FCa).
  sep_apply (hhs3_p6_H_ref_fold Tsh (l_pb L) PB4 Int.one RB FCb).
  (* free(m1); free(m2); return 0 *)
  sep_apply (hhs3_p6_B_init_free Ews (w_m1 V) (hhs3_M1m x25519 (w_R V) (w_M1 V))).
  sep_apply (hhs3_p6_B_resp_free Ews (w_m2 V) (hhs3_M2m x25519 (w_R V) (w_M2 V))).
  unfold hhs3_tok.
  assert_PROP (isptr (w_m1 V) /\ isptr (w_m2 V)) as Pm12 by entailer!. destruct Pm12 as [Pm1 Pm2].
  forward_call (t_init, w_m1 V, gv).
  { rewrite if_false by (intro E; rewrite E in Pm1; contradiction). cancel. }
  forward_call (t_resp, w_m2 V, gv).
  { rewrite if_false by (intro E; rewrite E in Pm2; contradiction). cancel. }
  forward.
  destruct (w_MI V) as [[[[[E encs] enct] ep] ck] h].
  sep_apply (@data_at_data_at_ HCS Tsh t_minit (minit_val E encs enct ep ck h) (l_mi L)).
  destruct (w_MR V) as [[[[E2 encn] ep2] ck2] h2].
  sep_apply (@data_at_data_at_ HCS Tsh t_mresp (mresp_val E2 encn ep2 ck2 h2) (l_mr L)).
  destruct (w_ST2 V) as [ck3 h3].
  sep_apply (@data_at_data_at_ HCS Tsh t_mstate (mstate_val ck3 h3) (l_st2 L)).
  eapply derives_trans; [| eapply derives_trans;
    [apply (HF (proj1 HH) gv L FR (w_R V) (hhs3_p6_S4 V) (Int64.repr 2) (hhs3_p6_TA3 L V) (hhs3_p6_TB3 L V)
               (hhs3_p6_EB1 L V) (hhs3_p6_EA1 L V) PB4 PA5 Hrun eq_refl eq_refl) | ]].
  { unfold hhs3_setup_sep, hhs3_globs, hhs3_scr_tmp. simpl fold_right_sepcon. cancel. }
  { unfold hhs3_p6_frame. simpl fold_right_sepcon. cancel. }
Qed.

End Seg.
