(* main of law prim_poly1305, segment A (statements 0..7): nondet key, key0 copy, draw n, return if
   n > PTRDIFF_MAX, three mallocs, the NULL test. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.harness.prim_poly1305.hp1305_spec3.
Require Import WgNoise.proof.harness.prim_poly1305.hp1305_main_defs3.
Require Import WgNoise.proof.libc.libc_bytes.
Require WgNoise.harness.x_prim_poly1305.code.

#[local] Existing Instance W_prim_poly1305.
Local Open Scope Z_scope.

Lemma hp1305m_kb kz : Forall (fun b => 0 <= b <= Byte.max_unsigned) kz ->
  map (fun b => Vint (Int.repr b)) kz = map Vubyte (map Byte.repr kz).
Proof.
  induction 1; simpl; f_equal; auto.
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

Definition hp1305m_nul (p: val) : bool := if eq_dec p nullval then true else false.

Lemma hp1305m_mres_valid n p :
  (if eq_dec p nullval then emp else malloc_token Ews (tarray tuchar n) p * data_at_ Ews (tarray tuchar n) p)
  |-- valid_pointer p.
Proof.
  destruct (eq_dec p nullval).
  - subst. apply valid_pointer_null.
  - destruct (zlt 0 n).
    + apply sepcon_valid_pointer2. apply data_at__valid_ptr; [auto | simpl sizeof; lia].
    + apply sepcon_valid_pointer1. apply malloc_token_valid_pointer. simpl sizeof. lia.
Qed.

#[local] Hint Resolve hp1305m_mres_valid : valid_pointer.

Lemma hp1305m_mres_local n p :
  (if eq_dec p nullval then emp else malloc_token Ews (tarray tuchar n) p * data_at_ Ews (tarray tuchar n) p)
  |-- !! is_pointer_or_null p.
Proof.
  destruct (eq_dec p nullval).
  - subst. apply prop_right. simpl. auto.
  - entailer!; destruct p; try contradiction; simpl; auto.
Qed.

#[local] Hint Resolve hp1305m_mres_local : saturate_local.

Lemma hp1305m_nul_null : hp1305m_nul nullval = true.
Proof. unfold hp1305m_nul. rewrite if_true; auto. Qed.

Lemma hp1305m_nul_nn p : p <> nullval -> hp1305m_nul p = false.
Proof. intros. unfold hp1305m_nul. rewrite if_false; auto. Qed.

Lemma hp1305m_test_eq p : is_pointer_or_null p ->
  force_val (sem_cast_i2bool (force_val (sem_cmp_pp Ceq p (Vlong (Int64.repr 0))))) =
  Vint (if hp1305m_nul p then Int.one else Int.zero).
Proof.
  intros H. destruct p; simpl in H; try contradiction.
  - subst. reflexivity.
  - rewrite hp1305m_nul_nn by discriminate. reflexivity.
Qed.

Lemma hp1305m_if_true (b: bool) : (if b then Int.one else Int.repr 0) <> Int.zero -> b = true.
Proof. destruct b; intros H; [reflexivity | contradiction H; reflexivity]. Qed.

Lemma hp1305m_if_false (b: bool) : (if b then Int.one else Int.repr 0) = Int.zero -> b = false.
Proof. destruct b; intros H; [discriminate H | reflexivity]. Qed.

Ltac hp1305m_or_then :=
  forward;
  match goal with H: (if ?b then Int.one else Int.repr 0) <> Int.zero |- _ => apply hp1305m_if_true in H; rewrite H end;
  simpl orb; apply ENTAIL_refl.

Ltac hp1305m_or_else :=
  forward;
  match goal with H: (if ?b then Int.one else Int.repr 0) = Int.zero |- _ => apply hp1305m_if_false in H; rewrite H end;
  simpl orb; entailer!; rewrite hp1305m_test_eq by auto; reflexivity.

Lemma hp1305m_segA_ok {Espec: OracleKind} gv vd vkey vkey0 vref FR :
  semax hp1305m_Delta (hp1305m_P0 gv vd vkey vkey0 vref FR) hp1305m_segA
    (overridePost (hp1305m_PA gv vd vkey vkey0 vref FR) (hp1305m_R gv)).
Proof.
  unfold hp1305m_P0, hp1305m_Delta, hp1305m_segA, hp1305m_R.
  apply hp1305m_post_canon.
  simplify_func_tycontext. abbreviate_semax.
  unfold hp1305m_lv.
  forward_call (vkey, 32, Tsh). Intros kz.
  rewrite hp1305m_kb by auto.
  set (kb := map Byte.repr kz).
  assert (HZ: Zlength kb = 32) by (unfold kb; rewrite Zlength_map; auto).
  replace (data_at_ Tsh (tarray tuchar 32) vkey0) with (data_at_ Tsh (tarray tuchar (Zlength kb)) vkey0)
    by (rewrite HZ; reflexivity).
  replace (data_at Tsh (tarray tuchar 32) (map Vubyte kb) vkey)
    with (data_at Tsh (tarray tuchar (Zlength kb)) (map Vubyte kb) vkey) by (rewrite HZ; reflexivity).
  forward_call (Tsh, vkey0, Tsh, vkey, kb).
  { entailer!. rewrite HZ. reflexivity. }
  rewrite HZ.
  forward_call. Intros n.
  forward_if.
  { forward. sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (map Vubyte kb) vkey0).
    sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (map Vubyte kb) vkey). unfold t_hpctx. cancel. }
  forward_call (tarray tuchar n, gv). { simpl sizeof. rewrite Z.max_r by lia. rep_lia. } Intros msg.
  forward_call (tarray tuchar n, gv). { simpl sizeof. rewrite Z.max_r by lia. rep_lia. } Intros copy.
  forward_call (tarray tuchar 16, gv). { simpl sizeof. rep_lia. } Intros tag.
  forward_if (temp HPC._t'5 (Vint (if orb (hp1305m_nul msg) (hp1305m_nul copy) then Int.one else Int.zero))).
  { forward. match goal with H: msg = nullval |- _ => rewrite H, hp1305m_nul_null end. simpl orb. apply ENTAIL_refl. }
  { forward. entailer!. rewrite hp1305m_test_eq by auto. rewrite (hp1305m_nul_nn msg) by auto. reflexivity. }
  forward_if (temp HPC._t'6 (Vint (if orb (orb (hp1305m_nul msg) (hp1305m_nul copy)) (hp1305m_nul tag) then Int.one else Int.zero))).
  { hp1305m_or_then. }
  { hp1305m_or_else. }
  forward_if (orb (orb (hp1305m_nul msg) (hp1305m_nul copy)) (hp1305m_nul tag) = false).
  { forward_call (tarray tuchar n, msg, gv).
    forward_call (tarray tuchar n, copy, gv).
    forward_call (tarray tuchar 16, tag, gv).
    forward. sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (map Vubyte kb) vkey0).
    sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (map Vubyte kb) vkey). unfold t_hpctx. cancel. }
  { forward. match goal with H: (if ?b then Int.one else Int.repr 0) = Int.zero |- _ => apply hp1305m_if_false in H end.
    entailer!. }
  Intros.
  match goal with H: orb _ _ = false |- _ => rename H into Hnn end.
  rewrite !orb_false_iff in Hnn. destruct Hnn as [[Hm Hc] Ht].
  unfold hp1305m_nul in Hm, Hc, Ht.
  destruct (eq_dec msg nullval); [discriminate |].
  destruct (eq_dec copy nullval); [discriminate |].
  destruct (eq_dec tag nullval); [discriminate |].
  unfold hp1305m_PA. Exists n kb msg copy tag.
  unfold hp1305m_ranges, hp1305m_buf, hp1305m_tv, hp1305m_lv. simpl app.
  entailer!.
Qed.
