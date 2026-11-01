(* law cookie_mac, phase P7, segment A2_outer: s83 outer: the mac1 test and the first two verdict branches, the inner block as a hypothesis (v1 hck3_p7_A2_outer.v.old).
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

(* the copy buffer: the 16 bytes [k, j) at offset k, and the rest (opaque) *)
Definition hck5_p7_A2_outer_rest (sh: share) (bs: list byte) (p: val) (k j: Z) : mpred :=
  (@data_at HCS sh (tarray tuchar k) (sublist 0 k (bytes bs)) p *
   @data_at HCS sh (tarray tuchar (Zlength bs - j)) (sublist j (Zlength bs) (bytes bs))
     (@field_address0 HCS (tarray tuchar (Zlength bs)) [ArraySubsc j] p))%logic.

Lemma hck5_p7_A2_outer_split sh bs p k j : 0 <= k <= j -> j <= Zlength bs ->
  @field_compatible HCS (tarray tuchar (Zlength bs)) [] p ->
  hbytes sh bs p = (hbytes sh (sublist k j bs) (offset_val k p) * hck5_p7_A2_outer_rest sh bs p k j)%logic.
Proof.
  intros Hk Hj FC. unfold hbytes, hck5_p7_A2_outer_rest.
  rewrite (@split3_data_at_Tarray_tuchar HCS sh (Zlength bs) k j) by (unfold bytes; rewrite ?Zlength_map; lia).
  rewrite Zlength_sublist by lia.
  rewrite field_address0_offset by (apply arr_field_compatible0; [exact FC | lia]).
  replace (@nested_field_offset HCS (Tarray tuchar (Zlength bs) noattr) (SUB k)) with k by (simpl; lia).
  unfold bytes. rewrite <- (sublist_map Vubyte k j bs).
  apply pred_ext; cancel.
Qed.

Lemma hck5_p7_A2_outer_ptr i n k : 0 <= k <= Int.max_signed ->
  Ptrofs.sub (Ptrofs.add i (Ptrofs.repr n)) (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr k))) =
  Ptrofs.add i (Ptrofs.repr (n - k)).
Proof.
  intros Hk. rewrite Ptrofs.mul_commut, Ptrofs.mul_one, Ptrofs.sub_add_opp, Ptrofs.add_assoc. f_equal.
  unfold Ptrofs.of_ints. rewrite Int.signed_repr by rep_lia. rewrite Ptrofs.neg_repr, ptrofs_add_repr.
  f_equal; lia.
Qed.

Lemma hck5_p7_A2_outer_hbytes_out sh bs p : hbytes sh bs p |-- hout sh (Zlength bs) p.
Proof. unfold hbytes, hout. apply data_at_data_at_. Qed.

(* validate keeps the mac1 key; its first two verdicts *)
Lemma hck5_p7_A2_outer_mkey CC s msg chk now rl r :
  cc_mkey (snd (validate_model CC s msg chk now rl r)) = cc_mkey CC.
Proof.
  unfold validate_model, checker_rotate.
  destruct (negb _); [reflexivity |]. destruct (negb chk); [reflexivity |].
  destruct (birthdate_expired _ _ _); destruct (negb _); try reflexivity; destruct (negb rl); reflexivity.
Qed.

Lemma hck5_p7_A2_outer_inv CC s msg chk now rl r :
  bytes_eqb (mac1_of (cc_mkey CC) msg) (sublist (Zlength msg - 32) (Zlength msg - 16) msg) = false ->
  validate_model CC s msg chk now rl r = (INVALID_MAC, CC).
Proof. intros E. unfold validate_model. rewrite E. reflexivity. Qed.

Lemma hck5_p7_A2_outer_nochk CC s msg now rl r :
  bytes_eqb (mac1_of (cc_mkey CC) msg) (sublist (Zlength msg - 32) (Zlength msg - 16) msg) = true ->
  validate_model CC s msg false now rl r = (VALID_MAC_BUT_NO_COOKIE, CC).
Proof. intros E. unfold validate_model. rewrite E. reflexivity. Qed.

(* s61 with its inner block folded: VST's force_sequential does not see through the constant hck5_p7_A2_inner,
   so the postcondition stays overridePost T2 R (the form of the hypothesis INNER) *)
Definition hck5_p7_A2_outer_if := ltac:(let x := eval cbv delta [hck5_p7_s83] in hck5_p7_s83 in
  match x with Ssequence _ (Sifthenelse ?e ?a (Sifthenelse ?e2 ?b _)) =>
    exact (Sifthenelse e a (Sifthenelse e2 b hck5_p7_A2_inner)) end).

Lemma hck5_p7_A2_outer_eq : hck5_p7_s83 = Ssequence hck5_p7_A2_call hck5_p7_A2_outer_if.
Proof. reflexivity. Qed.

Section P7A2_outer.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hck5_p7_A2_outer_ok {Espec: OracleKind} gv L FR :
  hck5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hck5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hck5_p7_A2_U x25519 gv L FR) hck5_p7_A2_inner
    (overridePost (hck5_T2 x25519 gv L FR) (hck5_R gv)) ->
  semax (hck5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hck5_T1 x25519 gv L FR) hck5_p7_s83
    (overridePost (hck5_T2 x25519 gv L FR) (hck5_R gv)).
Proof.
  intros HH INNER. rewrite hck5_p7_A2_outer_eq. unfold hck5_p7_A2_outer_if, hck5_p7_A2_call.
  unfold hck5_T1, hck5_Delta. simplify_func_tycontext. abbreviate_semax.
  Intros R S A m c Q cmode C ck. Intros MSG1 C1 MSG2 corrupted chk rl r VR M1.
  unfold hck5_lvars, hck5_scr2, hck5_globs, hck5_bside, hck5_bufs. simpl app.
  pose proof H6 as (HM2 & HL2 & Hr & HVR & HB & HRL & HROT).
  pose proof H1 as (Hn1 & Hn2 & _).
  assert_PROP (@field_compatible HCS (tarray tuchar (Zlength MSG2)) [] c) as FCc.
  { unfold hbytes. entailer!. }
  pose proof (hck5_p7_A2_outer_split Ews MSG2 c (q_n Q - 32) (q_n Q - 16) ltac:(lia) ltac:(lia) FCc) as SPL.
  rewrite SPL. flatten_sepcon_in_SEP.
  set (s1 := sublist (q_n Q - 32) (q_n Q - 16) MSG2) in *.
  assert (Ls1: Zlength s1 = 16) by (unfold s1; rewrite Zlength_sublist; lia).
  assert (Pc: isptr c) by (destruct FCc; auto).
  (* t' = bytes_eq(mac1, copy + len - 32, 16) *)
  forward_call (Tsh, l_mac1 L, M1, Ews, offset_val (q_n Q - 32) c, s1).
  { entailer!. rewrite H8. destruct c; try contradiction. simpl. rewrite hck5_p7_A2_outer_ptr by rep_lia. reflexivity. }
  sep_apply (derives_refl' _ _ (eq_sym SPL)).
  set (CC2 := hck5_CC2 x25519 R L (q_now Q) cmode) in *.
  assert (Emk: cc_mkey (snd VR) = cc_mkey CC2) by (unfold hck5_is in HVR; rewrite HVR; apply hck5_p7_A2_outer_mkey).
  assert (EB: bytes_eqb M1 s1 =
              bytes_eqb (mac1_of (cc_mkey CC2) MSG2) (sublist (Zlength MSG2 - 32) (Zlength MSG2 - 16) MSG2))
    by (unfold hck5_is in H7; rewrite H7, Emk, HL2; reflexivity).
  unfold hck5_is in HVR.
  destruct (bytes_eqb M1 s1) eqn:EQ.
  2: {
    (* mac1 wrong: verdict = INVALID_MAC *)
    assert (VR0: VR = (INVALID_MAC, CC2)) by (rewrite HVR; apply hck5_p7_A2_outer_inv; symmetry; exact EB).
    forward_if.
    2: { exfalso. apply H9. reflexivity. }
    forward.
    clear HVR. subst VR.
    unfold hck5_T2. Exists R S A m c. Exists Q cmode C ck. Exists MSG1 C1 MSG2 corrupted. Exists chk rl r (INVALID_MAC, CC2).
    unfold hck5_lvars, hck5_scr2, hck5_globs, hck5_bside, hck5_bufs, hck5_snaps. simpl app.
    sep_apply (hck5_p7_A2_outer_hbytes_out Tsh M1 (l_mac1 L)). rewrite H8.
    entailer!. all: apply derives_refl. }
  forward_if.
  { exfalso. revert H9. simpl. discriminate. }
  destruct chk.
  2: {
    (* no check_cookie: verdict = VALID_MAC_BUT_NO_COOKIE *)
    assert (VR1: VR = (VALID_MAC_BUT_NO_COOKIE, CC2)) by (rewrite HVR; apply hck5_p7_A2_outer_nochk; symmetry; exact EB).
    forward_if.
    2: { exfalso. apply H10. reflexivity. }
    forward.
    clear HVR. subst VR.
    unfold hck5_T2. Exists R S A m c. Exists Q cmode C ck. Exists MSG1 C1 MSG2 corrupted. Exists false rl r (VALID_MAC_BUT_NO_COOKIE, CC2).
    unfold hck5_lvars, hck5_scr2, hck5_globs, hck5_bside, hck5_bufs, hck5_snaps. simpl app.
    sep_apply (hck5_p7_A2_outer_hbytes_out Tsh M1 (l_mac1 L)). rewrite H8.
    entailer!. all: apply derives_refl. }
  forward_if.
  { exfalso. revert H10. simpl. discriminate. }
  (* mac1 ok and check_cookie: the inner block (hypothesis INNER) from U *)
  eapply semax_pre; [| exact INNER].
  unfold hck5_p7_A2_U. Exists R S A m c. Exists Q cmode C ck. Exists MSG1 C1 MSG2 corrupted. Exists true rl r VR. Exists M1.
  unfold hck5_lvars, hck5_globs, hck5_bside, hck5_bufs, hck5_snaps. simpl app.
  entailer!. all: apply derives_refl.
Qed.

End P7A2_outer.
