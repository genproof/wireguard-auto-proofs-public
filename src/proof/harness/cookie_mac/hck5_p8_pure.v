(* law cookie_mac, phase P8 (port of v1's hck3_p8_pure.v): the pure facts of the round trips. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.model.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.cookie_mac.hck5_cut.
Require Import WgNoise.proof.harness.cookie_mac.hck5_spec.
Require Import WgNoise.proof.harness.cookie_mac.hck5_defs.

Local Open Scope Z_scope.

Lemma hck5_p8_mac_len k m : Zlength (MAC k m) = 16.
Proof. unfold MAC, blake2s, b2s_digest_stream, b2s_out. rewrite Zlength_map. reflexivity. Qed.

Lemma hck5_p8_eqb_refl a : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); congruence. Qed.

(* a fresh birthdate (below 2^62) is not expired after 115 or 120 s *)
Lemma hck5_p8_not_expired (now: int64) s :
  0 <= Int64.unsigned now < 2 ^ 62 -> 0 < s < 1000 ->
  birthdate_expired now (Int64.repr s) now = false.
Proof.
  intros Hn Hs. unfold birthdate_expired, s64_le, NSEC_PER_SEC.
  assert (Hsn: Int64.signed now = Int64.unsigned now).
  { rewrite Int64.signed_eq_unsigned; auto. unfold Int64.max_signed, Int64.half_modulus, Int64.modulus,
      Int64.wordsize, Wordsize_64.wordsize. simpl. lia. }
  assert (Hs1: Int64.signed (Int64.repr s) = s) by (apply Int64.signed_repr; rep_lia).
  assert (Hs2: Int64.signed (Int64.repr 1000000000) = 1000000000) by reflexivity.
  assert (Hs3: Int64.signed (Int64.repr (s * 1000000000)) = s * 1000000000) by (apply Int64.signed_repr; rep_lia).
  assert (Hs4: Int64.signed (Int64.repr (Int64.unsigned now + s * 1000000000)) = Int64.unsigned now + s * 1000000000)
    by (apply Int64.signed_repr; rep_lia).
  unfold Int64.lt. rewrite Int64.add_signed, Int64.mul_signed, Hs1, Hs2, Hs3, Hsn, Hs4.
  destruct (zlt (Int64.unsigned now) (Int64.unsigned now + s * 1000000000)); [reflexivity | lia].
Qed.

Lemma hck5_p8_vrange CC s msg chk now rl r : 0 <= fst (validate_model CC s msg chk now rl r) <= 3.
Proof.
  unfold validate_model, INVALID_MAC, VALID_MAC_BUT_NO_COOKIE, VALID_MAC_WITH_COOKIE_BUT_RATELIMITED,
    VALID_MAC_WITH_COOKIE.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; simpl; lia.
Qed.

Section P8pure.
Variable x25519: list byte -> list byte -> list byte.

(* the round trips: a message with B's peer's macs passes mac1 at B; with B's fresh cookie also mac2 *)
Lemma hck5_p8_round R L Q m cmode C ck MSG1 C1 MSG2 chk rl r VR S :
  hck5_run_ok x25519 R -> hck5_pkt_ok Q ->
  hck5_is ck (cookie_of (r_secret R) (hck5_skb Q m)) -> hck5_ck_ok R Q cmode C ck ->
  hck5_is (MSG1, C1) (add_mac_model C (q_msg Q) (q_now Q)) -> Zlength MSG1 = q_n Q ->
  hck5_after_val x25519 R L Q m cmode MSG1 MSG2 false chk rl r VR S ->
  r_honest R = true -> mi_ok (mident_of x25519 (r_rawb R)) = true ->
  fst VR <> INVALID_MAC /\
  (cmode = true -> chk = true -> fst VR = if rl then VALID_MAC_WITH_COOKIE else VALID_MAC_WITH_COOKIE_BUT_RATELIMITED).
Proof.
  intros Hrun HQ Hck Hckok HM HL1 Hav Hhon Hok.
  destruct Hav as (HM2 & _ & _ & HVR & _). specialize (HM2 eq_refl). subst MSG2.
  unfold hck5_is in *. subst VR.
  destruct Hrun as (_&_&_&_&_&_&_&_&Hpub). specialize (Hpub Hhon).
  destruct HQ as (Hn & Hlm & _ & _ & _ & _ & Hnow).
  destruct Hckok as (_ & _ & Hmk & Hcm).
  (* the mac1 keys agree *)
  assert (Hkey: cc_mkey (hck5_CC2 x25519 R L (q_now Q) cmode) = ck_mkey C).
  { rewrite Hmk.
    replace (cc_mkey (hck5_CC2 x25519 R L (q_now Q) cmode)) with (cc_mkey (hck5_CC1 x25519 R L))
      by (unfold hck5_CC2; destruct (andb _ _); reflexivity).
    unfold hck5_CC1, hck5_DB, setup_dev, hck5_C0. simpl.
    rewrite Hpub. unfold hck5_IDB, setup_identity, identity_of, checker_keys. simpl.
    unfold mident_of in Hok. simpl in Hok. rewrite Hok.
    apply andb_prop in Hok. destruct Hok as [Hok _]. rewrite Hok. reflexivity. }
  set (n := Zlength (q_msg Q)) in *.
  set (msg := q_msg Q) in *.
  set (m1 := mac1_of (ck_mkey C) msg).
  assert (L1: Zlength m1 = 16) by (unfold m1, mac1_of; apply hck5_p8_mac_len).
  set (msg1 := sublist 0 (n - 32) msg ++ m1 ++ sublist (n - 16) n msg).
  assert (Lmsg1: Zlength msg1 = n).
  { unfold msg1. rewrite !Zlength_app, !Zlength_sublist by lia. lia. }
  set (m2 := if andb (ck_valid C) (negb (birthdate_expired (ck_birth C) (Int64.repr 115) (q_now Q)))
            then mac2_of (ck_cookie C) msg1 else zeros 16).
  assert (L2: Zlength m2 = 16).
  { unfold m2. destruct (andb _ _); [unfold mac2_of; apply hck5_p8_mac_len | reflexivity]. }
  assert (EM1: MSG1 = sublist 0 (n - 16) msg1 ++ m2).
  { unfold add_mac_model in HM. injection HM as HM _. rewrite HM. reflexivity. }
  assert (Hpre: sublist 0 (n - 16) MSG1 = sublist 0 (n - 16) msg1).
  { rewrite EM1. rewrite sublist_app1 by (rewrite ?Zlength_sublist; lia). rewrite sublist_sublist00 by lia.
    reflexivity. }
  assert (HLM: Zlength MSG1 = n) by lia.
  assert (Hmac1: mac1_of (cc_mkey (hck5_CC2 x25519 R L (q_now Q) cmode)) MSG1 = sublist (n - 32) (n - 16) MSG1).
  { rewrite Hkey. unfold mac1_of. rewrite HLM.
    replace (sublist 0 (n - 32) MSG1) with (sublist 0 (n - 32) msg).
    2:{ rewrite <- (sublist_sublist00 (n - 32) (n - 16) MSG1) by lia. rewrite Hpre.
        rewrite sublist_sublist00 by lia. unfold msg1.
        rewrite sublist_app1 by (rewrite ?Zlength_sublist; lia). rewrite sublist_sublist00 by lia.
        reflexivity. }
    replace (sublist (n - 32) (n - 16) MSG1) with (sublist (n - 32) (n - 16) msg1).
    2:{ rewrite EM1. rewrite sublist_app1 by (rewrite ?Zlength_sublist; lia).
        rewrite sublist_sublist by lia. f_equal; lia. }
    unfold msg1. rewrite sublist_app2 by (rewrite ?Zlength_sublist; lia).
    rewrite Zlength_sublist by lia.
    rewrite sublist_app1 by lia.
    replace (n - 32 - (n - 32 - 0)) with 0 by lia. replace (n - 16 - (n - 32 - 0)) with 16 by lia.
    rewrite (sublist_same 0 16 m1) by lia. reflexivity. }
  unfold validate_model. rewrite HLM, Hmac1, hck5_p8_eqb_refl. simpl negb. cbv iota.
  split.
  { destruct chk; [| discriminate]. simpl negb; cbv iota.
    destruct (negb (bytes_eqb _ _)); [discriminate |]. destruct rl; discriminate. }
  intros Hcm' Hchk. subst chk. specialize (Hcm Hcm'). destruct Hcm as (Hval & Hbirth & Hcook). subst cmode.
  simpl negb; cbv iota.
  (* no rotation *)
  assert (Hrot: checker_rotate (hck5_CC2 x25519 R L (q_now Q) true) (q_now Q) r = hck5_CC2 x25519 R L (q_now Q) true).
  { unfold checker_rotate, hck5_CC2. simpl andb. change (cc_birth (hck5_CC1 x25519 R L)) with (r_birth R).
    destruct (birthdate_expired (r_birth R) (Int64.repr 120) (q_now Q)) eqn:E.
    - simpl cc_birth. rewrite hck5_p8_not_expired by lia. reflexivity.
    - change (cc_birth (hck5_CC1 x25519 R L)) with (r_birth R). rewrite E. reflexivity. }
  rewrite Hrot.
  assert (Hsec: cc_secret (hck5_CC2 x25519 R L (q_now Q) true) = r_secret R).
  { unfold hck5_CC2. simpl andb. change (cc_birth (hck5_CC1 x25519 R L)) with (r_birth R).
    destruct (birthdate_expired (r_birth R) (Int64.repr 120) (q_now Q)); reflexivity. }
  rewrite Hsec, <- Hck.
  assert (Em2: m2 = mac2_of ck msg1).
  { unfold m2. rewrite Hval, Hbirth, hck5_p8_not_expired by lia. simpl. rewrite Hcook. reflexivity. }
  assert (Hmac2: mac2_of ck MSG1 = sublist (n - 16) n MSG1).
  { unfold mac2_of. rewrite HLM, Hpre.
    rewrite EM1. rewrite sublist_app2 by (rewrite ?Zlength_sublist; lia).
    rewrite Zlength_sublist by lia. replace (n - 16 - (n - 16 - 0)) with 0 by lia.
    replace (n - (n - 16 - 0)) with 16 by lia. rewrite (sublist_same 0 16 m2) by lia.
    rewrite Em2. unfold mac2_of. rewrite Lmsg1. reflexivity. }
  rewrite Hmac2, hck5_p8_eqb_refl. simpl negb; cbv iota.
  destruct rl; reflexivity.
Qed.

End P8pure.
