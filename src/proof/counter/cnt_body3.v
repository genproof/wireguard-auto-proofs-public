(* the bodies of patch/counter_validate.c against counter_spec.v; the
   arithmetic of the window is in cnt_math3.v, cnt_old3.v, cnt_new3.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.counter.counter_spec.
Require Import WgNoise.proof.counter.cnt_math3.
Require Import WgNoise.proof.counter.cnt_old3.
Require Import WgNoise.proof.counter.cnt_new3.
Require Import WgNoise.counter.code.

#[local] Existing Instance WgNoise.units.Counter.CS.
Local Open Scope Z_scope.

Definition cnt3_V : varspecs := QPvarspecs Counter.qp.
Definition cnt3_Gprog : funspecs := cnt_imports Counter.CS ++ cnt_G.

Lemma cnt3_log2_lt64 : forall n, 0 <= n <= Int64.max_unsigned -> 0 <= Z.log2 n < 64.
Proof.
  intros. split; [apply Z.log2_nonneg|].
  destruct (Z.eq_dec n 0) as [->|?]; [simpl; lia|].
  apply Z.log2_lt_pow2; [lia|]. rep_lia.
Qed.

Lemma cnt3_log2_div2 : forall m, 1 < m -> Z.log2 (m / 2) = Z.log2 m - 1.
Proof.
  intros. replace (m / 2) with (Z.shiftr m 1) by (rewrite Z.shiftr_div_pow2; reflexivity || lia).
  rewrite Z.log2_shiftr by lia.
  assert (1 <= Z.log2 m) by (change 1 with (Z.log2 2); apply Z.log2_le_mono; lia). lia.
Qed.

Lemma body_quickproof_ilog2 :
  semax_body cnt3_V cnt3_Gprog WgNoise.counter.code.f_quickproof_ilog2 quickproof_ilog2_spec.
Proof.
  start_function.
  forward.
  forward_while (EX r: Z, EX m: Z,
    PROP ((0 <= r)%Z; (0 <= m <= n)%Z; (r + Z.log2 m = Z.log2 n)%Z)
    LOCAL (temp _r (Vint (Int.repr r)); temp _n (Vlong (Int64.repr m)))
    SEP ()).
  - Exists 0 n. entailer!.
  - entailer!.
  - pose proof (cnt3_log2_lt64 n H). pose proof (Z.log2_nonneg m).
    forward. forward. Exists (r + 1, m / 2). unfold fst, snd. entailer!.
    + split; [split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]|].
      rewrite cnt3_log2_div2 by lia. lia.
  - forward. entailer!.
    assert (Z.log2 m = 0) by (destruct (Z.eq_dec m 0) as [->|?]; [reflexivity|]; replace m with 1 by lia; reflexivity).
    f_equal. f_equal. lia.
Qed.

Lemma cnt3_land_bit : forall w nr, 0 <= nr ->
  Z.land w (2 ^ nr) = if Z.testbit w nr then 2 ^ nr else 0.
Proof.
  intros. apply Z.bits_inj'; intros k Hk. rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec nr k) as [<-|Hne]; destruct (Z.testbit w nr) eqn:E;
    rewrite ?Z.pow2_bits_eqb, ?Z.bits_0 by lia; simpl; rewrite ?andb_false_r; auto.
  - rewrite Z.eqb_refl. reflexivity.
  - apply Z.eqb_neq in Hne. rewrite Hne. reflexivity.
Qed.

Lemma body_test_and_set_bit :
  semax_body cnt3_V cnt3_Gprog WgNoise.counter.code.f_test_and_set_bit test_and_set_bit_spec.
Proof.
  start_function.
  assert (Hm: Int64.modu (Int64.repr nr) (Int64.repr (Int.signed (Int.repr 64))) = Int64.repr nr).
  { unfold Int64.modu. rewrite (Int64.unsigned_repr nr) by rep_lia. rewrite Int.signed_repr by rep_lia.
    rewrite Int64.unsigned_repr by rep_lia. rewrite Z.mod_small by lia. reflexivity. }
  assert (Hd: Int64.divu (Int64.repr nr) (Int64.repr (Int.signed (Int.repr 64))) = Int64.repr 0).
  { unfold Int64.divu. rewrite (Int64.unsigned_repr nr) by rep_lia. rewrite Int.signed_repr by rep_lia.
    rewrite Int64.unsigned_repr by rep_lia. rewrite Z.div_small by lia. reflexivity. }
  assert (Hpow: 0 < 2 ^ nr <= 2 ^ 63) by (split; [apply Z.pow_pos_nonneg | apply Z.pow_le_mono_r]; lia).
  assert (Hs: Int64.shl (Int64.repr 1) (Int64.repr nr) = Int64.repr (2 ^ nr)).
  { unfold Int64.shl. rewrite !Int64.unsigned_repr by rep_lia. rewrite Z.shiftl_1_l. reflexivity. }
  forward.
  { entailer!. rewrite !Int64.Z_mod_modulus_eq, (Z.mod_small nr) by rep_lia.
    rewrite Z.mod_small; pose proof (Z.mod_pos_bound nr 64); rep_lia. }
  rewrite Hm. assert_PROP (isptr p) by entailer!. forward.
  destruct p; try contradiction. simpl eval_binop. rewrite Hd. simpl force_val.
  rewrite Ptrofs.mul_zero, Ptrofs.add_zero.
  forward. forward. forward. rewrite Hs. entailer!.
  - rewrite cnt3_land_bit by lia.
    destruct (Z.testbit w nr); simpl.
    + rewrite Int64.eq_false; [reflexivity|]. intro Heq. apply (f_equal Int64.unsigned) in Heq.
      rewrite !Int64.unsigned_repr in Heq by rep_lia. lia.
    + reflexivity.
  - rewrite Z.shiftl_1_l. apply derives_refl.
Qed.

Lemma cnt3_and_ones : forall x k, 0 <= x <= Int64.max_unsigned -> 0 <= k < 64 ->
  Int64.and (Int64.repr x) (Int64.repr (Z.ones k)) = Int64.repr (x mod 2 ^ k).
Proof.
  intros. unfold Int64.and.
  assert (0 <= Z.ones k <= Int64.max_unsigned).
  { rewrite Z.ones_equiv. assert (2 ^ k <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    pose proof (Z.pow_pos_nonneg 2 k). rep_lia. }
  rewrite !Int64.unsigned_repr by lia. rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma cnt3_add : forall x y, 0 <= x -> 0 <= y -> x + y <= Int64.max_unsigned ->
  Int64.add (Int64.repr x) (Int64.repr y) = Int64.repr (x + y).
Proof. intros. unfold Int64.add. rewrite !Int64.unsigned_repr by lia. reflexivity. Qed.

Lemma cnt3_shru6 : forall x, 0 <= x <= Int64.max_unsigned ->
  Int64.shru (Int64.repr x) (Int64.repr (Int.unsigned (Int.repr (Z.log2 64)))) = Int64.repr (x / 64).
Proof.
  intros. unfold Int64.shru. change (Int.unsigned (Int.repr (Z.log2 64))) with 6.
  rewrite !Int64.unsigned_repr by rep_lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Ltac cnt3_fold :=
  repeat match goal with
  | |- context [let (q, _) := Z.div_eucl ?a 64 in q] =>
      change (let (q, _) := Z.div_eucl a 64 in q) with (a / 64)
  | H: context [let (q, _) := Z.div_eucl ?a 64 in q] |- _ =>
      change (let (q, _) := Z.div_eucl a 64 in q) with (a / 64) in H
  end.

Lemma body_counter_validate :
  semax_body cnt3_V cnt3_Gprog WgNoise.counter.code.f_counter_validate counter_validate_spec.
Proof.
  start_function.
  pose proof H0 as Hinv. destruct H0 as [Hlen Hwords Htop HL Hwin Habove].
  forward.
  forward_loop (PROP () LOCAL (temp _ret (Val.of_bool false); temp _counter c;
                   temp _their_counter (Vlong (Int64.repr n)))
                SEP (data_at sh (Tstruct _noise_replay_counter noattr) (cnt_val top lk bm) c))
    continue: (EX bm': list Z,
      PROP (cnt_inv (cnt_top' top L n) (cnt_L' top L n) bm')
      LOCAL (temp _ret (Val.of_bool (cnt_ok top L n)))
      SEP (data_at sh (Tstruct _noise_replay_counter noattr) (cnt_val (cnt_top' top L n) lk bm') c))
    break: (EX bm': list Z,
      PROP (cnt_inv (cnt_top' top L n) (cnt_L' top L n) bm')
      LOCAL (temp _ret (Val.of_bool (cnt_ok top L n)))
      SEP (data_at sh (Tstruct _noise_replay_counter noattr) (cnt_val (cnt_top' top L n) lk bm') c)).
  { entailer!. }
  2: { Intros bm'. forward. Exists bm'. entailer!. }
  2: { Intros bm'. forward. Exists bm'. entailer!. destruct (cnt_ok top L n); reflexivity. }
  unfold cnt_val. forward.
  assert (HR1: Int64.unsigned (Int64.repr (-8130 + 1)) = CNT_R + 1) by reflexivity.
  assert (HR: Int64.unsigned (Int64.repr (-8130)) = CNT_R) by reflexivity.
  assert (HRm: CNT_R + 8130 = Int64.max_unsigned + 1) by reflexivity.
  assert (Htopr: 0 <= top <= Int64.max_unsigned) by lia.
  forward_if (temp _t'1 (Vint (if (CNT_R <=? n) then Int.one else Int.zero))).
  { forward. entailer!. rewrite HR1, Int64.unsigned_repr in H0 by lia. lia. }
  { forward. entailer!.
    unfold Int64.cmpu, Int64.ltu. rewrite HR, Int64.unsigned_repr by lia.
    destruct (zlt n CNT_R); destruct (Z.leb_spec CNT_R n); try lia; reflexivity. }
  forward_if.
  { destruct (cnt_math_reject top L n) as (Hok & Ht & HL').
    { destruct (Z.leb_spec CNT_R n); try contradiction; lia. }
    forward. Exists bm. rewrite Hok, Ht, HL'. entailer!. }
  assert (Hn: n < CNT_R) by (destruct (Z.leb_spec CNT_R n); try discriminate; lia).
  forward.
  assert (Ht1: Int64.add (Int64.repr n) (Int64.repr (Int.signed (Int.repr 1))) = Int64.repr (n + 1)).
  { rewrite Int.signed_repr by rep_lia. unfold Int64.add.
    rewrite !Int64.unsigned_repr by lia. reflexivity. }
  rewrite Ht1. forward.
  forward_if.
  { destruct (cnt_math_reject top L n) as (Hok & Ht & HL').
    { right; right. rewrite cnt3_add, !Int64.unsigned_repr in H1 by (unfold CNT_W in *; lia).
      unfold CNT_W; lia. }
    forward. Exists bm. rewrite Hok, Ht, HL'. entailer!. }
  assert (Hw: top <= n + 1 + CNT_W).
  { rewrite cnt3_add, !Int64.unsigned_repr in H1 by (unfold CNT_W in *; lia).
    unfold CNT_W; lia. }
  forward_call 64.
  forward.
  rewrite cnt3_shru6 by lia.
  forward.
  forward_if (PROP () LOCAL (temp _index (Vlong (Int64.repr ((n + 1) / 64)));
      temp _their_counter (Vlong (Int64.repr (n + 1))); temp _ret (Val.of_bool false); temp _counter c)
    SEP (data_at sh (Tstruct _noise_replay_counter noattr)
       (Vlong (Int64.repr (Z.max top (n + 1))),
        (lk, map (fun w : Z => Vlong (Int64.repr w))
          (if top <? n + 1 then cnt_clear bm (top / 64) (Z.min ((n + 1) / 64 - top / 64) 128) else bm))) c)).
  2: { forward. rewrite Z.max_l by lia. replace (top <? n + 1) with false by (symmetry; apply Z.ltb_ge; lia).
       entailer!. }
  forward_call 64. forward. forward. rewrite cnt3_shru6 by lia.
  assert (Hic: top / 64 <= (n + 1) / 64) by (apply Z.div_le_mono; lia).
  assert (Hic0: 0 <= top / 64) by (apply Z.div_pos; lia).
  assert (Hidx: (n + 1) / 64 < 2 ^ 58) by (apply Z.div_lt_upper_bound; rep_lia).
  assert (Hsub: Int64.sub (Int64.repr ((n + 1) / 64)) (Int64.repr (top / 64)) =
                Int64.repr ((n + 1) / 64 - top / 64)).
  { unfold Int64.sub. rewrite !Int64.unsigned_repr by rep_lia. reflexivity. }
  assert (H128: Int64.unsigned (Int64.repr (Int.signed (Int.divs (Int.repr 8192) (Int.repr 64)))) = 128)
    by reflexivity.
  forward_if (temp _t'4 (Vlong (Int64.repr (Z.min ((n + 1) / 64 - top / 64) 128)))).
  { change (let (q, _) := Z.div_eucl (n + 1) 64 in q) with ((n + 1) / 64) in H3.
    change (let (q, _) := Z.div_eucl top 64 in q) with (top / 64) in H3.
    rewrite Hsub in H3. unfold Int64.ltu in H3. rewrite H128, Int64.unsigned_repr in H3 by rep_lia.
    destruct (zlt _ _) in H3; [|discriminate].
    forward. entailer!. rewrite Z.min_l by lia. reflexivity. }
  { change (let (q, _) := Z.div_eucl (n + 1) 64 in q) with ((n + 1) / 64) in H3.
    change (let (q, _) := Z.div_eucl top 64 in q) with (top / 64) in H3.
    rewrite Hsub in H3. unfold Int64.ltu in H3. rewrite H128, Int64.unsigned_repr in H3 by rep_lia.
    destruct (zlt _ _) in H3; [discriminate|].
    forward. entailer!. rewrite Z.min_r by lia. reflexivity. }
  forward.
  assert (Hk: 0 <= Z.min ((n + 1) / 64 - top / 64) 128 <= 128) by lia.
  assert (H127: Int.signed (Int.sub (Int.divs (Int.repr 8192) (Int.repr 64)) (Int.repr 1)) = Z.ones 7)
    by reflexivity.
  forward_loop (EX i: Z,
      PROP (1 <= i <= Z.min ((n + 1) / 64 - top / 64) 128 + 1)
      LOCAL (temp _i (Vlong (Int64.repr i));
        temp _top (Vlong (Int64.repr (Z.min ((n + 1) / 64 - top / 64) 128)));
        temp _index_current (Vlong (Int64.repr (top / 64)));
        temp _index (Vlong (Int64.repr ((n + 1) / 64)));
        temp _their_counter (Vlong (Int64.repr (n + 1))); temp _ret (Val.of_bool false); temp _counter c)
      SEP (data_at sh (Tstruct _noise_replay_counter noattr)
         (Vlong (Int64.repr top),
          (lk, map (fun w : Z => Vlong (Int64.repr w)) (cnt_clear bm (top / 64) (i - 1)))) c))%assert
    continue: (EX i: Z,
      PROP (1 <= i <= Z.min ((n + 1) / 64 - top / 64) 128)
      LOCAL (temp _i (Vlong (Int64.repr i));
        temp _top (Vlong (Int64.repr (Z.min ((n + 1) / 64 - top / 64) 128)));
        temp _index_current (Vlong (Int64.repr (top / 64)));
        temp _index (Vlong (Int64.repr ((n + 1) / 64)));
        temp _their_counter (Vlong (Int64.repr (n + 1))); temp _ret (Val.of_bool false); temp _counter c)
      SEP (data_at sh (Tstruct _noise_replay_counter noattr)
         (Vlong (Int64.repr top),
          (lk, map (fun w : Z => Vlong (Int64.repr w)) (cnt_clear bm (top / 64) i))) c))%assert
    break: (PROP ()
      LOCAL (temp _index (Vlong (Int64.repr ((n + 1) / 64)));
        temp _their_counter (Vlong (Int64.repr (n + 1))); temp _ret (Val.of_bool false); temp _counter c)
      SEP (data_at sh (Tstruct _noise_replay_counter noattr)
         (Vlong (Int64.repr top),
          (lk, map (fun w : Z => Vlong (Int64.repr w))
                 (cnt_clear bm (top / 64) (Z.min ((n + 1) / 64 - top / 64) 128)))) c)).
  { forward. Exists 1. entailer!. }
  { Intros i. forward_if.
    - cnt3_fold. unfold Int64.ltu in H4. rewrite !Int64.unsigned_repr in H4 by rep_lia.
      destruct (zlt _ _) in H4; [discriminate|].
      assert (Hl: Zlength (cnt_clear bm (top / 64) (i - 1)) = 128) by (rewrite cnt_clear_len; auto).
      assert (Hmod: 0 <= (i + top / 64) mod 128 < 128) by (apply Z.mod_pos_bound; lia).
      forward.
      { entailer!. cnt3_fold. rewrite H127, Z.land_ones by lia. change (2 ^ 7) with 128. lia. }
      Exists i. entailer!. cnt3_fold. rewrite H127, Z.land_ones by lia. change (2 ^ 7) with 128.
      rewrite (cnt_clear_step bm (top / 64) i) by lia.
      rewrite <- (upd_Znth_map (fun w : Z => Vlong (Int64.repr w)) _ _ 0). apply derives_refl.
    - cnt3_fold. unfold Int64.ltu in H4. rewrite !Int64.unsigned_repr in H4 by rep_lia.
      destruct (zlt _ _) in H4; [|discriminate].
      forward. replace (i - 1) with (Z.min ((n + 1) / 64 - top / 64) 128) by lia. entailer!. }
  { Intros i. forward. Exists (i + 1). replace (i + 1 - 1) with i by lia. entailer!. }
  forward.
  rewrite Z.max_r by lia. replace (top <? n + 1) with true by (symmetry; apply Z.ltb_lt; lia).
  entailer!.
  remember (if top <? n + 1 then cnt_clear bm (top / 64) (Z.min ((n + 1) / 64 - top / 64) 128) else bm)
    as bm1 eqn:Ebm1.
  assert (Hfin: cnt_ok top L n = negb (cnt_bit bm1 (n + 1)) /\ cnt_top' top L n = Z.max top (n + 1) /\
                cnt_inv (cnt_top' top L n) (cnt_L' top L n) (cnt_set bm1 (n + 1))).
  { subst bm1. destruct (Z.ltb_spec top (n + 1)).
    - pose proof (cnt_math_new top L bm n Hinv ltac:(lia) H2) as Hm. cbv zeta in Hm.
      destruct Hm as (Hb & Hok & Ht & HL' & Hi'). rewrite Hb, Hok, Ht, HL', Z.max_r by lia. auto.
    - destruct (cnt_math_old top L bm n Hinv ltac:(lia) Hw ltac:(lia)) as (Hok & Ht & Hi').
      rewrite Ht, Z.max_l by lia. auto. }
  assert (Hl1: Zlength bm1 = 128) by (subst bm1; destruct (top <? n + 1); rewrite ?cnt_clear_len; auto).
  assert (Hw1: Forall (fun w => 0 <= w <= Int64.max_unsigned) bm1)
    by (subst bm1; destruct (top <? n + 1); auto; apply cnt_clear_words; auto).
  assert (Hidx: 0 <= (n + 1) / 64 <= n + 1) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  forward.
  assert (H127: Int.signed (Int.sub (Int.divs (Int.repr 8192) (Int.repr 64)) (Int.repr 1)) = Z.ones 7)
    by reflexivity.
  assert (H63: Int.signed (Int.sub (Int.repr 64) (Int.repr 1)) = Z.ones 6) by reflexivity.
  rewrite H127, cnt3_and_ones by (try split; lia). change (2 ^ 7) with 128.
  assert (Hi: 0 <= ((n + 1) / 64) mod 128 < 128) by (apply Z.mod_pos_bound; lia).
  assert_PROP (field_compatible (Tstruct _noise_replay_counter noattr) [] c) by entailer!.
  unfold_data_at (data_at _ _ _ c).
  rewrite (field_at_data_at sh _ (DOT _backtrack)).
  sep_apply (SingletonHole.array_with_hole_intro sh tulong (((n + 1) / 64) mod 128) 128
    (map (fun w : Z => Vlong (Int64.repr w)) bm1)
    (field_address (Tstruct _noise_replay_counter noattr) (DOT _backtrack) c)).
  Intros. rewrite Znth_map by lia.
  assert (Hwi: 0 <= Znth (((n + 1) / 64) mod 128) bm1 <= Int64.max_unsigned)
    by (apply Forall_Znth; auto; lia).
  forward_call (sh, field_address (tarray tulong 128) [ArraySubsc (((n + 1) / 64) mod 128)]
      (field_address (Tstruct _noise_replay_counter noattr) (DOT _backtrack) c),
    (n + 1) mod 64, Znth (((n + 1) / 64) mod 128) bm1).
  { entailer!. simpl. cnt3_fold. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. f_equal. f_equal.
    unfold field_address in *.
    destruct (field_compatible_dec _ (DOT _backtrack) c) as [Hf|Hf];
      [|exfalso; apply Hf; auto with field_compatible].
    destruct (field_compatible_dec (tarray tulong 128) _ _) as [Hg|Hg]; [|destruct H4 as [Hp _]; contradiction].
    rewrite offset_offset_val. f_equal. }
  { apply Z.mod_pos_bound; lia. }
  forward.
  sep_apply (SingletonHole.array_with_hole_elim sh tulong (((n + 1) / 64) mod 128) 128
    (Vlong (Int64.repr (Z.lor (Znth (((n + 1) / 64) mod 128) bm1) (Z.shiftl 1 ((n + 1) mod 64)))))
    (map (fun w : Z => Vlong (Int64.repr w)) bm1)
    (field_address (Tstruct _noise_replay_counter noattr) (DOT _backtrack) c)).
  rewrite (upd_Znth_map (fun w : Z => Vlong (Int64.repr w))).
  destruct Hfin as (Hok & Ht & Hinv').
  Exists (cnt_set bm1 (n + 1)).
  unfold cnt_val. rewrite Ht. unfold_data_at (data_at _ _ _ c).
  rewrite (field_at_data_at sh _ (DOT _backtrack)).
  entailer!.
  rewrite Hok. unfold cnt_bit. destruct (Z.testbit _ _); reflexivity.
Qed.

Lemma body_wg_counter_validate :
  semax_body cnt3_V cnt3_Gprog WgNoise.counter.code.f_wg_counter_validate wg_counter_validate_spec.
Proof.
  start_function.
  forward_call (sh, c, top, L, bm, lk, n). Intros bm'.
  forward. Exists bm'. entailer!. destruct (cnt_ok top L n); reflexivity.
Qed.
