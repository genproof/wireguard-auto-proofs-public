(* law cookie_mac, phase P7, segment A2_tail: A2_tail: the mac2 test and the ratelimit branches (v1 hck3_p7_A2_tail.v.old).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_mac.hck5_cut.
Require Import WgNoise.proof.harness.cookie_mac.hck5_spec.
Require Import WgNoise.proof.harness.cookie_mac.hck5_defs.
Require Import WgNoise.proof.harness.cookie_mac.hck5_conv.
Require Import WgNoise.proof.harness.cookie_mac.hck5_p7_defs.
Require Import WgNoise.proof.harness.cookie_mac.hck5_p7_A2_defs.
Require WgNoise.harness.x_cookie_mac.code.

#[local] Existing Instance W_cookie_mac.
Local Open Scope Z_scope.

(* validate never changes the mac1 key *)
Lemma hck5_p7_A2_tail_mkey CC s msg chk now rl r :
  cc_mkey (snd (validate_model CC s msg chk now rl r)) = cc_mkey CC.
Proof.
  unfold validate_model, checker_rotate. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

(* the mac1 test passed and check_cookie: the three verdicts, and the rotated checker *)
Lemma hck5_p7_A2_tail_vm CC s msg now rl r :
  bytes_eqb (mac1_of (cc_mkey CC) msg) (sublist (Zlength msg - 32) (Zlength msg - 16) msg) = true ->
  validate_model CC s msg true now rl r =
  (if bytes_eqb (mac2_of (cookie_of (cc_secret (checker_rotate CC now r)) s) msg)
                (sublist (Zlength msg - 16) (Zlength msg) msg)
   then (if rl then VALID_MAC_WITH_COOKIE else VALID_MAC_WITH_COOKIE_BUT_RATELIMITED)
   else VALID_MAC_BUT_NO_COOKIE,
   checker_rotate CC now r).
Proof.
  intros E. unfold validate_model. cbv zeta. rewrite E. cbn [negb]. clear E.
  destruct (bytes_eqb (mac2_of _ _) _); destruct rl; reflexivity.
Qed.

Lemma hck5_p7_A2_tail_hbytes_out sh bs p : hbytes sh bs p |-- hout sh (Zlength bs) p.
Proof. unfold hbytes, hout. apply data_at_data_at_. Qed.

(* the copy buffer: the bytes [k, j) at offset k, and the rest (opaque) *)
Definition hck5_p7_A2_tail_rest (sh: share) (bs: list byte) (p: val) (k j: Z) : mpred :=
  (@data_at HCS sh (tarray tuchar k) (sublist 0 k (bytes bs)) p *
   @data_at HCS sh (tarray tuchar (Zlength bs - j)) (sublist j (Zlength bs) (bytes bs))
     (@field_address0 HCS (tarray tuchar (Zlength bs)) [ArraySubsc j] p))%logic.

Lemma hck5_p7_A2_tail_split sh bs p k j : 0 <= k <= j -> j <= Zlength bs ->
  @field_compatible HCS (tarray tuchar (Zlength bs)) [] p ->
  hbytes sh bs p = (hbytes sh (sublist k j bs) (offset_val k p) * hck5_p7_A2_tail_rest sh bs p k j)%logic.
Proof.
  intros Hk Hj FC. unfold hbytes, hck5_p7_A2_tail_rest.
  rewrite (@split3_data_at_Tarray_tuchar HCS sh (Zlength bs) k j) by (unfold bytes; rewrite ?Zlength_map; lia).
  rewrite Zlength_sublist by lia.
  rewrite field_address0_offset by (apply arr_field_compatible0; [exact FC | lia]).
  replace (@nested_field_offset HCS (Tarray tuchar (Zlength bs) noattr) (SUB k)) with k by (simpl; lia).
  unfold bytes. rewrite <- (sublist_map Vubyte k j bs).
  apply pred_ext; cancel.
Qed.

Lemma hck5_p7_A2_tail_ptr i n k : 0 <= k <= Int.max_signed ->
  Ptrofs.sub (Ptrofs.add i (Ptrofs.repr n)) (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr k))) =
  Ptrofs.add i (Ptrofs.repr (n - k)).
Proof.
  intros Hk. rewrite Ptrofs.mul_commut, Ptrofs.mul_one, Ptrofs.sub_add_opp, Ptrofs.add_assoc. f_equal.
  unfold Ptrofs.of_ints. rewrite Int.signed_repr by rep_lia. rewrite Ptrofs.neg_repr, ptrofs_add_repr.
  f_equal; lia.
Qed.

Section Shim.
#[local] Existing Instance Noise.CS.
(* the shim's globals but the rate limiter's answer *)
Definition hck5_p7_A2_tail_shrest (gv: globals) (S: shim) : mpred :=
  (data_at Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
   data_at Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
   data_at Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
   data_at Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
   data_at Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
   data_at Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
   data_at Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   data_at Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
   data_at Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   data_at Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   data_at Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released))%logic.
End Shim.

#[local] Instance hck5_p7_A2_tail_cce_N : change_composite_env Noise.CS W_cookie_mac.
Proof. make_cs_preserve Noise.CS W_cookie_mac. Defined.

Lemma hck5_p7_A2_tail_tbool_cs sh (v: val) p :
  @data_at Noise.CS sh tbool v p = @data_at W_cookie_mac sh tbool v p.
Proof. exact (f_equal (fun f => f p) (@data_at_change_composite Noise.CS W_cookie_mac _ sh tbool v v (JMeq_refl v) eq_refl)). Qed.

Lemma hck5_p7_A2_tail_shim_open gv S w :
  shim_state4 gv S w =
  (!! shim_ok S && (@data_at W_cookie_mac Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow) *
                    (hck5_p7_A2_tail_shrest gv S * refwarn4 gv w)))%logic.
Proof.
  unfold shim_state4, shim_core, hck5_p7_A2_tail_shrest. rewrite sepcon_andp_prop'. rewrite <- hck5_p7_A2_tail_tbool_cs. apply pred_ext.
  - Intros. apply andp_right; [apply prop_right; assumption |]. cancel.
  - Intros. apply andp_right; [apply prop_right; assumption |]. cancel.
Qed.

Section P7A2_tail.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hck5_p7_A2_tail_ok {Espec: OracleKind} gv L FR :
  hck5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hck5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hck5_p7_A2_U3 x25519 gv L FR) hck5_p7_A2_tail
    (overridePost (hck5_T2 x25519 gv L FR) (hck5_R gv)).
Proof.
  intros HH. unfold hck5_p7_A2_U3, hck5_Delta, hck5_R, hck5_p7_A2_tail. simplify_func_tycontext. abbreviate_semax.
  Intros R S A m c Q cmode C ck. Intros MSG1 C1 MSG2 corrupted chk rl r VR. Intros M1 CK M2.
  unfold hck5_lvars, hck5_scr2, hck5_globs, hck5_bside, hck5_bufs, hck5_snaps. simpl app.
  subst chk. pose proof H6 as (AV1 & AV2 & AV3 & AV4 & AV5 & AV6 & AV7).
  pose proof H1 as (Hn1 & Hn2 & _).
  set (CC2 := hck5_CC2 x25519 R L (q_now Q) cmode) in *.
  assert (Emk: cc_mkey (snd VR) = cc_mkey CC2) by (unfold hck5_is in AV4; rewrite AV4; apply hck5_p7_A2_tail_mkey).
  assert (VRE := hck5_p7_A2_tail_vm CC2 (hck5_skb Q m) MSG2 (q_now Q) rl r).
  unfold hck5_is in AV4, H7, H11, H13. rewrite <- AV4, AV2, <- Emk, <- H7 in VRE. specialize (VRE H9).
  assert (SV: snd VR = checker_rotate CC2 (q_now Q) r) by (rewrite VRE; reflexivity).
  assert (FV: fst VR = if bytes_eqb M2 (sublist (q_n Q - 16) (q_n Q) MSG2) then (if rl then 3 else 2) else 1).
  { rewrite VRE. cbn [fst]. rewrite H13, H11, SV. reflexivity. }
  clear VRE.
  assert_PROP (@field_compatible HCS (tarray tuchar (Zlength MSG2)) [] c) as FCc.
  { unfold hbytes. entailer!. }
  pose proof (hck5_p7_A2_tail_split Ews MSG2 c (q_n Q - 16) (q_n Q) ltac:(lia) ltac:(lia) FCc) as SPL.
  rewrite SPL. flatten_sepcon_in_SEP.
  set (s2 := sublist (q_n Q - 16) (q_n Q) MSG2) in *.
  assert (Ls2: Zlength s2 = 16) by (unfold s2; rewrite Zlength_sublist; lia).
  assert (Pc: isptr c) by (destruct FCc; auto).
  forward_call (Tsh, l_mac2 L, M2, Ews, offset_val (q_n Q - 16) c, s2).
  { entailer!. rewrite H14. destruct c; try contradiction. simpl. rewrite hck5_p7_A2_tail_ptr by rep_lia. reflexivity. }
  sep_apply (derives_refl' _ _ (eq_sym SPL)).
  sep_apply (hck5_p7_A2_tail_hbytes_out Tsh M1 (l_mac1 L)).
  sep_apply (hck5_p7_A2_tail_hbytes_out Tsh M2 (l_mac2 L)).
  sep_apply (hck5_p7_A2_tail_hbytes_out Tsh CK (l_cookie L)).
  rewrite H8, H12, H14.
  destruct (bytes_eqb M2 s2) eqn:EQ.
  - forward_if.
    { exfalso. exact (Int.one_not_zero H10). }
    rewrite hck5_p7_A2_tail_shim_open. Intros.
    forward.
    { entailer!. destruct (s_rlallow S); simpl; auto. }
    forward_if.
    + forward.
      unfold hck5_T2. Exists R S A m c. Exists Q cmode C ck. Exists MSG1 C1 MSG2 corrupted. Exists true rl r VR.
      unfold hck5_lvars, hck5_globs, hck5_bside, hck5_bufs, hck5_snaps. simpl app.
      rewrite hck5_p7_A2_tail_shim_open.
      entailer!.
      rewrite FV. destruct (s_rlallow S); [| reflexivity].
      match goal with Ht: typed_true _ _ |- _ => unfold typed_true in Ht; simpl in Ht; discriminate end.
    + forward.
      unfold hck5_T2. Exists R S A m c. Exists Q cmode C ck. Exists MSG1 C1 MSG2 corrupted. Exists true rl r VR.
      unfold hck5_lvars, hck5_globs, hck5_bside, hck5_bufs, hck5_snaps. simpl app.
      rewrite hck5_p7_A2_tail_shim_open.
      entailer!.
      rewrite FV. destruct (s_rlallow S); [reflexivity |].
      match goal with Ht: typed_false _ _ |- _ => unfold typed_false in Ht; simpl in Ht; discriminate end.
  - forward_if.
    2: { exfalso. apply H10. reflexivity. }
    forward.
    unfold hck5_T2. Exists R S A m c. Exists Q cmode C ck. Exists MSG1 C1 MSG2 corrupted. Exists true rl r VR.
    unfold hck5_lvars, hck5_globs, hck5_bside, hck5_bufs, hck5_snaps. simpl app.
    entailer!.
Qed.

End P7A2_tail.
