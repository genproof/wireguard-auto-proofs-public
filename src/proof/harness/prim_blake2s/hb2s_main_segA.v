(* main of law prim_blake2s, segment A (statements 0..11 of the body): draw outlen, keylen, the key,
   copy it, draw n (return if n > PTRDIFF_MAX), the five mallocs, the NULL test. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.harness.prim_blake2s.hb2s_spec.
Require Import WgNoise.proof.harness.prim_blake2s.hb2s_main_defs.
Require WgNoise.harness.x_prim_blake2s.code.

#[local] Existing Instance W_prim_blake2s.
Local Open Scope Z_scope.

Lemma hb2s_mods b m : 0 <= b <= Byte.max_unsigned -> 0 < m <= Byte.max_unsigned ->
  Int.signed (Int.mods (Int.repr b) (Int.repr m)) = b mod m.
Proof.
  intros Hb Hm. unfold Int.mods. rewrite (Int.signed_repr b), (Int.signed_repr m) by rep_lia.
  rewrite Z.rem_mod_nonneg by rep_lia. apply Int.signed_repr.
  pose proof (Z.mod_pos_bound b m ltac:(lia)). rep_lia.
Qed.

Lemma hb2s_outlen b : 0 <= b <= Byte.max_unsigned ->
  Int.signed (Int.add (Int.repr 1) (Int.mods (Int.repr b) (Int.repr 32))) = 1 + b mod 32.
Proof.
  intros Hb. rewrite Int.add_signed, hb2s_mods by rep_lia.
  pose proof (Z.mod_pos_bound b 32 ltac:(lia)).
  rewrite (Int.signed_repr 1) by rep_lia. apply Int.signed_repr. rep_lia.
Qed.

Lemma hb2s_kb kz : Forall (fun b => 0 <= b <= Byte.max_unsigned) kz ->
  map (fun b => Vint (Int.repr b)) kz = map Vubyte (map Byte.repr kz).
Proof.
  induction 1; simpl; f_equal; auto.
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma hb2s_post_canon {Espec: OracleKind} {cs: compspecs} Delta P c Q gv F :
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (PROP () LOCAL () SEP (TT))) F)) ->
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (hb2s_post gv)) F)).
Proof.
  intros H. eapply semax_post; [| | | | apply H]; intros; simpl; intros rho; apply andp_left2;
    try apply derives_refl.
  apply sepcon_derives; [| apply derives_refl]. revert rho. apply bind_ret_derives. intros rho. apply TT_right.
Qed.

Definition hb2s_nul (p: val) : bool := if eq_dec p nullval then true else false.

Lemma hb2s_mres_valid n p :
  (if eq_dec p nullval then emp else malloc_token Ews (tarray tuchar n) p * data_at_ Ews (tarray tuchar n) p)
  |-- valid_pointer p.
Proof.
  destruct (eq_dec p nullval).
  - subst. apply valid_pointer_null.
  - destruct (zlt 0 n).
    + apply sepcon_valid_pointer2. apply data_at__valid_ptr; [auto | simpl sizeof; lia].
    + apply sepcon_valid_pointer1. apply malloc_token_valid_pointer. simpl sizeof. lia.
Qed.

#[local] Hint Resolve hb2s_mres_valid : valid_pointer.

Lemma hb2s_mres_local n p :
  (if eq_dec p nullval then emp else malloc_token Ews (tarray tuchar n) p * data_at_ Ews (tarray tuchar n) p)
  |-- !! is_pointer_or_null p.
Proof.
  destruct (eq_dec p nullval).
  - subst. apply prop_right. simpl. auto.
  - entailer!; destruct p; try contradiction; simpl; auto.
Qed.

#[local] Hint Resolve hb2s_mres_local : saturate_local.

Lemma hb2s_nul_null : hb2s_nul nullval = true.
Proof. unfold hb2s_nul. rewrite if_true; auto. Qed.

Lemma hb2s_nul_nn p : p <> nullval -> hb2s_nul p = false.
Proof. intros. unfold hb2s_nul. rewrite if_false; auto. Qed.

Lemma hb2s_test_eq p : is_pointer_or_null p ->
  force_val (sem_cast_i2bool (force_val (sem_cmp_pp Ceq p (Vlong (Int64.repr 0))))) =
  Vint (if hb2s_nul p then Int.one else Int.zero).
Proof.
  intros H. destruct p; simpl in H; try contradiction.
  - subst. reflexivity.
  - rewrite hb2s_nul_nn by discriminate. reflexivity.
Qed.

Lemma hb2s_if_true (b: bool) : (if b then Int.one else Int.repr 0) <> Int.zero -> b = true.
Proof. destruct b; intros H; [reflexivity | contradiction H; reflexivity]. Qed.

Lemma hb2s_if_false (b: bool) : (if b then Int.one else Int.repr 0) = Int.zero -> b = false.
Proof. destruct b; intros H; [discriminate H | reflexivity]. Qed.

Ltac hb2s_or_then :=
  forward;
  match goal with H: (if ?b then Int.one else Int.repr 0) <> Int.zero |- _ => apply hb2s_if_true in H; rewrite H end;
  simpl orb; apply ENTAIL_refl.

Ltac hb2s_or_else :=
  forward;
  match goal with H: (if ?b then Int.one else Int.repr 0) = Int.zero |- _ => apply hb2s_if_false in H; rewrite H end;
  simpl orb; entailer!; rewrite hb2s_test_eq by auto; reflexivity.

Lemma hb2s_segA_ok {Espec: OracleKind} gv vctx vkey vkc FR :
  semax hb2s_Delta (hb2s_P0 gv vctx vkey vkc FR) hb2s_segA
    (overridePost (hb2s_PA gv vctx vkey vkc FR) (hb2s_R gv)).
Proof.
  unfold hb2s_P0, hb2s_Delta, hb2s_segA, hb2s_R.
  apply hb2s_post_canon.
  simplify_func_tycontext. abbreviate_semax.
  unfold hb2s_lv.
  forward_call. Intros b1. forward.
  { entailer!. rewrite hb2s_mods by rep_lia. pose proof (Z.mod_pos_bound b1 32 ltac:(lia)). split; [rep_lia|].
    intros [_ E]. discriminate. }
  rewrite hb2s_outlen by auto.
  forward_call. Intros b2. forward.
  { entailer!. match goal with H: _ /\ Int.repr 33 = Int.mone |- _ => destruct H as [_ E]; discriminate end. }
  rewrite hb2s_mods by rep_lia.
  forward_call (vkey, 32, Tsh). Intros kz.
  rewrite hb2s_kb by auto.
  set (kb := map Byte.repr kz).
  assert (HZ: Zlength kb = 32) by (unfold kb; rewrite Zlength_map; auto).
  replace (data_at_ Tsh (tarray tuchar 32) vkc) with (data_at_ Tsh (tarray tuchar (Zlength kb)) vkc)
    by (rewrite HZ; reflexivity).
  replace (data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey)
    with (data_at Tsh (tarray tuchar (Zlength kb)) (map Vubyte kb) vkey) by (rewrite HZ; reflexivity).
  forward_call (Tsh, vkc, Tsh, vkey, kb).
  { entailer!. rewrite HZ. reflexivity. }
  rewrite HZ.
  forward_call. Intros n.
  forward_if.
  { forward. sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (map Vubyte kb) vkc).
    sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (map Vubyte kb) vkey). unfold t_hctx. cancel. }
  set (outlen := 1 + b1 mod 32).
  assert (Hol: 1 <= outlen <= 32) by (pose proof (Z.mod_pos_bound b1 32 ltac:(lia)); unfold outlen; lia).
  set (keylen := b2 mod 33).
  assert (Hkl: 0 <= keylen <= 32) by (pose proof (Z.mod_pos_bound b2 33 ltac:(lia)); unfold keylen; lia).
  clearbody outlen keylen.
  forward_call (tarray tuchar n, gv). { simpl sizeof. rewrite Z.max_r by lia. rep_lia. } Intros msg.
  forward_call (tarray tuchar n, gv). { simpl sizeof. rewrite Z.max_r by lia. rep_lia. } Intros copy.
  forward_call (tarray tuchar outlen, gv). { simpl sizeof. rewrite Z.max_r by lia. rep_lia. } Intros out.
  forward_call (tarray tuchar outlen, gv). { simpl sizeof. rewrite Z.max_r by lia. rep_lia. } Intros ref.
  forward_call (tarray tuchar outlen, gv). { simpl sizeof. rewrite Z.max_r by lia. rep_lia. } Intros out2.
  forward_if (temp HC._t'9 (Vint (if orb (hb2s_nul msg) (hb2s_nul copy) then Int.one else Int.zero))).
  { forward. match goal with H: msg = nullval |- _ => rewrite H, hb2s_nul_null end. simpl orb. apply ENTAIL_refl. }
  { forward. entailer!. rewrite hb2s_test_eq by auto. rewrite (hb2s_nul_nn msg) by auto. reflexivity. }
  forward_if (temp HC._t'10 (Vint (if orb (orb (hb2s_nul msg) (hb2s_nul copy)) (hb2s_nul out) then Int.one else Int.zero))).
  { hb2s_or_then. }
  { hb2s_or_else. }
  forward_if (temp HC._t'11 (Vint (if orb (orb (orb (hb2s_nul msg) (hb2s_nul copy)) (hb2s_nul out)) (hb2s_nul ref)
    then Int.one else Int.zero))).
  { hb2s_or_then. }
  { hb2s_or_else. }
  forward_if (temp HC._t'12 (Vint (if orb (orb (orb (orb (hb2s_nul msg) (hb2s_nul copy)) (hb2s_nul out)) (hb2s_nul ref))
    (hb2s_nul out2) then Int.one else Int.zero))).
  { hb2s_or_then. }
  { hb2s_or_else. }
  forward_if (orb (orb (orb (orb (hb2s_nul msg) (hb2s_nul copy)) (hb2s_nul out)) (hb2s_nul ref))
    (hb2s_nul out2) = false).
  { forward_call (tarray tuchar n, msg, gv).
    forward_call (tarray tuchar n, copy, gv).
    forward_call (tarray tuchar outlen, out, gv).
    forward_call (tarray tuchar outlen, ref, gv).
    forward_call (tarray tuchar outlen, out2, gv).
    forward. sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (map Vubyte kb) vkc).
    sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (map Vubyte kb) vkey). unfold t_hctx. cancel. }
  { forward. match goal with H: (if ?b then Int.one else Int.repr 0) = Int.zero |- _ => apply hb2s_if_false in H end.
    entailer!. }
  Intros.
  match goal with H: orb _ _ = false |- _ => rename H into Hnn end.
  rewrite !orb_false_iff in Hnn. destruct Hnn as [[[[Hm Hc] Ho] Hr] Ho2].
  unfold hb2s_nul in Hm, Hc, Ho, Hr, Ho2.
  destruct (eq_dec msg nullval); [discriminate |].
  destruct (eq_dec copy nullval); [discriminate |].
  destruct (eq_dec out nullval); [discriminate |].
  destruct (eq_dec ref nullval); [discriminate |].
  destruct (eq_dec out2 nullval); [discriminate |].
  unfold hb2s_PA. Exists outlen keylen n kb msg copy out ref out2.
  unfold hb2s_ranges, hb2s_buf, hb2s_tv, hb2s_lv. simpl app.
  entailer!.
Qed.
