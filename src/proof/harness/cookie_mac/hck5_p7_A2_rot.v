(* law cookie_mac, phase P7, segment A2_rot: A2_rot: the secret's rotation from wg_shim_random_log (v1 hck3_p7_A2_rot.v.old).
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
Require Import WgNoise.proof.libc.libc_bytes.
Require WgNoise.harness.x_cookie_mac.code.

#[local] Existing Instance W_cookie_mac.
Local Open Scope Z_scope.

(* validate never changes the mac1 key *)
Lemma hck5_p7_A2_rot_mkey CC s msg chk now rl r :
  cc_mkey (snd (validate_model CC s msg chk now rl r)) = cc_mkey CC.
Proof.
  unfold validate_model, checker_rotate. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

(* the mac1 test passed and check_cookie: validate's checker is the rotated one *)
Lemma hck5_p7_A2_rot_vm CC s msg now rl r :
  bytes_eqb (mac1_of (cc_mkey (snd (validate_model CC s msg true now rl r))) msg)
            (sublist (Zlength msg - 32) (Zlength msg - 16) msg) = true ->
  snd (validate_model CC s msg true now rl r) = checker_rotate CC now r /\
  validate_rotates CC msg true now = checker_rotates CC now.
Proof.
  rewrite hck5_p7_A2_rot_mkey. intros E.
  unfold validate_model, validate_rotates. cbv zeta. rewrite E. cbn [negb andb].
  destruct (negb (bytes_eqb (mac2_of _ _) _)); destruct rl; split; reflexivity.
Qed.

Lemma hck5_p7_A2_rot_cc2_secret x R L now cmode : cc_secret (hck5_CC2 x R L now cmode) = r_secret R.
Proof. unfold hck5_CC2, hck5_CC1. destruct (andb _ _); reflexivity. Qed.

Lemma hck5_p7_A2_rot_hbytes_out sh bs p : hbytes sh bs p |-- hout sh (Zlength bs) p.
Proof. unfold hbytes, hout. apply data_at_data_at_. Qed.

Section Shim.
#[local] Existing Instance Noise.CS.
(* the shim's globals but the random log *)
Definition hck5_p7_A2_rot_shrest (gv: globals) (S: shim) : mpred :=
  (data_at Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
   data_at Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
   data_at Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
   data_at Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
   data_at Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
   data_at Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   data_at Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
   data_at Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   data_at Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   data_at Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
   data_at Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow))%logic.
End Shim.

Lemma hck5_p7_A2_rot_shim_open gv S w :
  shim_state4 gv S w =
  (!! shim_ok S && (hbytes Ews (s_log S) (gv _wg_shim_random_log) * hck5_p7_A2_rot_shrest gv S * refwarn4 gv w))%logic.
Proof.
  unfold shim_state4, shim_core, hck5_p7_A2_rot_shrest. apply pred_ext.
  - Intros. pose proof H as [H1 _]. apply andp_right; [apply prop_right; exact H |].
    unfold hbytes. rewrite H1. rewrite (@data_at_tarray_tuchar_cs HCS Noise.CS). cancel.
  - Intros. pose proof H as [H1 _]. apply andp_right; [apply prop_right; exact H |].
    unfold hbytes. rewrite H1. rewrite (@data_at_tarray_tuchar_cs HCS Noise.CS). cancel.
Qed.

Section P7A2_rot.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hck5_p7_A2_rot_ok {Espec: OracleKind} gv L FR :
  hck5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hck5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hck5_p7_A2_U x25519 gv L FR) hck5_p7_A2_rot
    (overridePost (hck5_p7_A2_U2 x25519 gv L FR) (hck5_R gv)).
Proof.
  intros HH. unfold hck5_p7_A2_U, hck5_Delta, hck5_R, hck5_p7_A2_rot. simplify_func_tycontext. abbreviate_semax.
  Intros R S A m c Q cmode C ck. Intros MSG1 C1 MSG2 corrupted chk rl r VR. Intros M1.
  unfold hck5_lvars, hck5_scr2, hck5_globs, hck5_bside, hck5_bufs, hck5_snaps. simpl app.
  rename H6 into HAV, H7 into HM1, H9 into HEQ.
  subst chk. pose proof HAV as (AV1 & AV2 & AV3 & AV4 & AV5 & AV6 & AV7).
  assert (VRE: snd VR = checker_rotate (hck5_CC2 x25519 R L (q_now Q) cmode) (q_now Q) r /\
    validate_rotates (hck5_CC2 x25519 R L (q_now Q) cmode) MSG2 true (q_now Q) =
    checker_rotates (hck5_CC2 x25519 R L (q_now Q) cmode) (q_now Q)).
  { unfold hck5_is in AV4, HM1. subst VR. apply hck5_p7_A2_rot_vm. rewrite AV2, <- HM1. exact HEQ. }
  forward_call (cc_birth (hck5_CC2 x25519 R L (q_now Q) cmode), Int64.repr 120, q_now Q).
  destruct (birthdate_expired (cc_birth (hck5_CC2 x25519 R L (q_now Q) cmode)) (Int64.repr 120) (q_now Q)) eqn:EXP.
  - assert (SL: s_log S = r) by (apply AV7; rewrite (proj2 VRE); unfold checker_rotates; exact EXP).
    forward_if.
    + rewrite hck5_p7_A2_rot_shim_open. Intros.
      rewrite hck5_p7_A2_rot_cc2_secret.
      sep_apply (hck5_p7_A2_rot_hbytes_out Tsh (r_secret R) (l_secret L)).
      replace (Zlength (r_secret R)) with (Zlength (s_log S)) by (destruct H as (?&?&?&?&?&?); rewrite SL; lia).
      forward_call (Tsh, l_secret L, Ews, gv _wg_shim_random_log, s_log S).
      { entailer!. rewrite AV3. reflexivity. }
      { rewrite SL, AV3. rep_lia. }
      forward.
      unfold hck5_p7_A2_U2. Exists R S A m c. Exists Q cmode C ck. Exists MSG1 C1 MSG2 corrupted. Exists true rl r VR. Exists M1.
      unfold hck5_lvars, hck5_globs, hck5_bside, hck5_bufs, hck5_snaps. simpl app.
      replace (cc_birth (snd VR)) with (q_now Q) by (rewrite (proj1 VRE); unfold checker_rotate; rewrite EXP; reflexivity).
      replace (cc_secret (snd VR)) with (s_log S) by (rewrite (proj1 VRE); unfold checker_rotate; rewrite EXP; simpl; auto).
      rewrite hck5_p7_A2_rot_shim_open.
      entailer!.
    + exfalso. match goal with Hc: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hc) end.
  - forward_if.
    + exfalso. match goal with Hc: ?a <> ?a |- _ => apply Hc; reflexivity end.
    + forward.
      unfold hck5_p7_A2_U2. Exists R S A m c. Exists Q cmode C ck. Exists MSG1 C1 MSG2 corrupted. Exists true rl r VR. Exists M1.
      unfold hck5_lvars, hck5_globs, hck5_bside, hck5_bufs, hck5_snaps. simpl app.
      replace (cc_birth (snd VR)) with (cc_birth (hck5_CC2 x25519 R L (q_now Q) cmode))
        by (rewrite (proj1 VRE); unfold checker_rotate; rewrite EXP; reflexivity).
      replace (cc_secret (snd VR)) with (cc_secret (hck5_CC2 x25519 R L (q_now Q) cmode))
        by (rewrite (proj1 VRE); unfold checker_rotate; rewrite EXP; reflexivity).
      entailer!.
Qed.

End P7A2_rot.
