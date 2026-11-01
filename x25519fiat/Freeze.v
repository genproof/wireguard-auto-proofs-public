(* fe_freeze_m: for tight limbs, the canonical limbs of (value mod p).  VST-side file: no fiat-crypto here. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.x25519.x25519_model.
Require Import X25519.Limbs.

Local Open Scope Z_scope.

(* the canonical limbs of v (0 <= v < 2^255) *)
Definition canon (v: Z) : list int :=
  map Int.repr [v mod 2^26; (v / 2^26) mod 2^25; (v / 2^51) mod 2^26; (v / 2^77) mod 2^25;
                (v / 2^102) mod 2^26; (v / 2^128) mod 2^25; (v / 2^153) mod 2^26; (v / 2^179) mod 2^25;
                (v / 2^204) mod 2^26; (v / 2^230) mod 2^25].

Lemma digit V (L o H w b : Z) : V = L + 2 ^ w * (o + 2 ^ b * H) ->
  0 <= w -> 0 <= b -> 0 <= L < 2 ^ w -> 0 <= o < 2 ^ b -> (V / 2 ^ w) mod 2 ^ b = o.
Proof.
  intros -> Hw Hb HL Ho.
  rewrite (Z.mul_comm (2 ^ w)), Z.div_add by lia. rewrite (Z.div_small L) by lia. rewrite Z.add_0_l.
  rewrite (Z.mul_comm (2 ^ b)), Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma digit0 V (o H b : Z) : V = o + 2 ^ b * H -> 0 <= b -> 0 <= o < 2 ^ b -> V mod 2 ^ b = o.
Proof.
  intros -> Hb Ho. rewrite (Z.mul_comm (2 ^ b)), Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma canon_limbs o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 :
  0 <= o0 < 2^26 -> 0 <= o1 < 2^25 -> 0 <= o2 < 2^26 -> 0 <= o3 < 2^25 -> 0 <= o4 < 2^26 ->
  0 <= o5 < 2^25 -> 0 <= o6 < 2^26 -> 0 <= o7 < 2^25 -> 0 <= o8 < 2^26 -> 0 <= o9 < 2^25 ->
  canon (fevalZ [o0; o1; o2; o3; o4; o5; o6; o7; o8; o9]) =
  map Int.repr [o0; o1; o2; o3; o4; o5; o6; o7; o8; o9].
Proof.
  intros. unfold canon, fevalZ. cbn [map].
  set (V := o0 + 2 ^ 26 * o1 + 2 ^ 51 * o2 + 2 ^ 77 * o3 + 2 ^ 102 * o4 + 2 ^ 128 * o5 +
            2 ^ 153 * o6 + 2 ^ 179 * o7 + 2 ^ 204 * o8 + 2 ^ 230 * o9).
  rewrite (digit0 V o0 (o1 + 2^25 * o2 + 2^51 * o3 + 2^76 * o4 + 2^102 * o5 + 2^127 * o6 + 2^153 * o7
                        + 2^178 * o8 + 2^204 * o9) 26) by (unfold V; first [ring | lia]).
  rewrite (digit V (o0) o1 (o2 + 2^26 * o3 + 2^51 * o4 + 2^77 * o5 + 2^102 * o6 + 2^128 * o7 + 2^153 * o8
                            + 2^179 * o9) 26 25) by (unfold V; first [ring | lia]).
  rewrite (digit V (o0 + 2^26 * o1) o2 (o3 + 2^25 * o4 + 2^51 * o5 + 2^76 * o6 + 2^102 * o7 + 2^127 * o8
                            + 2^153 * o9) 51 26) by (unfold V; first [ring | lia]).
  rewrite (digit V (o0 + 2^26 * o1 + 2^51 * o2) o3 (o4 + 2^26 * o5 + 2^51 * o6 + 2^77 * o7 + 2^102 * o8
                            + 2^128 * o9) 77 25) by (unfold V; first [ring | lia]).
  rewrite (digit V (o0 + 2^26 * o1 + 2^51 * o2 + 2^77 * o3) o4 (o5 + 2^25 * o6 + 2^51 * o7 + 2^76 * o8
                            + 2^102 * o9) 102 26) by (unfold V; first [ring | lia]).
  rewrite (digit V (o0 + 2^26 * o1 + 2^51 * o2 + 2^77 * o3 + 2^102 * o4) o5 (o6 + 2^26 * o7 + 2^51 * o8
                            + 2^77 * o9) 128 25) by (unfold V; first [ring | lia]).
  rewrite (digit V (o0 + 2^26 * o1 + 2^51 * o2 + 2^77 * o3 + 2^102 * o4 + 2^128 * o5) o6
                   (o7 + 2^25 * o8 + 2^51 * o9) 153 26) by (unfold V; first [ring | lia]).
  rewrite (digit V (o0 + 2^26 * o1 + 2^51 * o2 + 2^77 * o3 + 2^102 * o4 + 2^128 * o5 + 2^153 * o6) o7
                   (o8 + 2^26 * o9) 179 25) by (unfold V; first [ring | lia]).
  rewrite (digit V (o0 + 2^26 * o1 + 2^51 * o2 + 2^77 * o3 + 2^102 * o4 + 2^128 * o5 + 2^153 * o6
                    + 2^179 * o7) o8 o9 204 26) by (unfold V; first [ring | lia]).
  rewrite (digit V (o0 + 2^26 * o1 + 2^51 * o2 + 2^77 * o3 + 2^102 * o4 + 2^128 * o5 + 2^153 * o6
                    + 2^179 * o7 + 2^204 * o8) o9 0 230 25) by (unfold V; first [ring | lia]).
  reflexivity.
Qed.

Lemma canon_limbs_lit o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 :
  0 <= o0 < 2^26 -> 0 <= o1 < 2^25 -> 0 <= o2 < 2^26 -> 0 <= o3 < 2^25 -> 0 <= o4 < 2^26 ->
  0 <= o5 < 2^25 -> 0 <= o6 < 2^26 -> 0 <= o7 < 2^25 -> 0 <= o8 < 2^26 -> 0 <= o9 < 2^25 ->
  canon (fevalZ [o0; o1; o2; o3; o4; o5; o6; o7; o8; o9]) =
  [Int.repr o0; Int.repr o1; Int.repr o2; Int.repr o3; Int.repr o4; Int.repr o5; Int.repr o6;
   Int.repr o7; Int.repr o8; Int.repr o9].
Proof. intros. rewrite canon_limbs by assumption. reflexivity. Qed.

Lemma fevalZ_canon_range v : 0 <= v < 2 ^ 255 ->
  map Int.unsigned (canon v) = [v mod 2^26; (v / 2^26) mod 2^25; (v / 2^51) mod 2^26; (v / 2^77) mod 2^25;
                (v / 2^102) mod 2^26; (v / 2^128) mod 2^25; (v / 2^153) mod 2^26; (v / 2^179) mod 2^25;
                (v / 2^204) mod 2^26; (v / 2^230) mod 2^25].
Proof.
  intros. unfold canon. cbn [map].
  repeat f_equal; apply Int.unsigned_repr;
    match goal with |- 0 <= ?x mod 2 ^ ?k <= _ =>
      pose proof (Z.mod_pos_bound x (2 ^ k) ltac:(lia)); rep_lia end.
Qed.

(* ------------------------------------------------------------------ *)
(* the borrow and carry steps                                          *)
(* ------------------------------------------------------------------ *)

Lemma land_ones_mod' a k : 0 <= k -> Z.land a (2 ^ k - 1) = a mod 2 ^ k.
Proof. intros. rewrite <- Z.land_ones by lia. f_equal. rewrite Z.ones_equiv. lia. Qed.

Lemma mod32_mod_pow D bits : 0 <= bits <= 32 -> (D mod 2 ^ 32) mod 2 ^ bits = D mod 2 ^ bits.
Proof.
  intros. symmetry. apply Znumtheory.Zmod_div_mod; try lia.
  exists (2 ^ (32 - bits)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma subborrow_spec bits (c a b: int) :
  0 < bits <= 26 ->
  - 2 ^ bits <= Int.unsigned a - Int.unsigned b - Int.unsigned c < 2 ^ bits ->
  Int.unsigned a - Int.unsigned b - Int.unsigned c =
    Int.unsigned (fst (subborrow_m bits c a b)) - 2 ^ bits * Int.unsigned (snd (subborrow_m bits c a b)) /\
  0 <= Int.unsigned (fst (subborrow_m bits c a b)) < 2 ^ bits /\
  0 <= Int.unsigned (snd (subborrow_m bits c a b)) <= 1.
Proof.
  intros Hb Hd. unfold subborrow_m. cbn [fst snd].
  set (D := Int.unsigned a - Int.unsigned b - Int.unsigned c) in *.
  assert (P: 2 ^ bits <= 2 ^ 26) by (apply Z.pow_le_mono_r; lia).
  assert (X: Int.unsigned (Int.sub (Int.sub a b) c) = D mod 2 ^ 32).
  { unfold Int.sub. rewrite (Int.unsigned_repr_eq (Int.unsigned a - Int.unsigned b)).
    rewrite Int.unsigned_repr_eq. change Int.modulus with (2 ^ 32).
    rewrite Zminus_mod_idemp_l. reflexivity. }
  assert (F: Int.unsigned (Int.and (Int.sub (Int.sub a b) c) (Int.repr (2 ^ bits - 1))) = D mod 2 ^ bits).
  { unfold Int.and. rewrite X, (Int.unsigned_repr (2 ^ bits - 1)) by rep_lia.
    rewrite land_ones_mod' by lia. rewrite mod32_mod_pow by lia.
    apply Int.unsigned_repr. pose proof (Z.mod_pos_bound D (2 ^ bits) ltac:(lia)). rep_lia. }
  assert (S: Int.unsigned (Int.shru (Int.sub (Int.sub a b) c) (Int.repr 31)) = D mod 2 ^ 32 / 2 ^ 31).
  { unfold Int.shru. rewrite X, (Int.unsigned_repr 31) by rep_lia. rewrite Z.shiftr_div_pow2 by lia.
    pose proof (Z.mod_pos_bound D (2 ^ 32) ltac:(lia)).
    apply Int.unsigned_repr. split; [apply Z.div_pos; lia|].
    assert (D mod 2 ^ 32 / 2 ^ 31 < 2) by (apply Z.div_lt_upper_bound; lia). rep_lia. }
  rewrite F, S.
  destruct (Z_lt_le_dec D 0) as [N|N].
  - assert (E1: D mod 2 ^ 32 = D + 2 ^ 32) by (rewrite <- (Z_mod_plus_full D 1), ?Z.mul_1_l; apply Z.mod_small; lia).
    assert (E2: D mod 2 ^ bits = D + 2 ^ bits) by (rewrite <- (Z_mod_plus_full D 1), ?Z.mul_1_l; apply Z.mod_small; lia).
    assert (E3: (D + 2 ^ 32) / 2 ^ 31 = 1) by (symmetry; apply Z.div_unique with (D + 2 ^ 31); lia).
    rewrite E1, E2, E3. lia.
  - assert (E1: D mod 2 ^ 32 = D) by (apply Z.mod_small; lia).
    assert (E2: D mod 2 ^ bits = D) by (apply Z.mod_small; lia).
    assert (E3: D / 2 ^ 31 = 0) by (apply Z.div_small; lia).
    rewrite E1, E2, E3. lia.
Qed.

Lemma addcarry_spec bits (c a b: int) :
  0 < bits <= 26 ->
  Int.unsigned a + Int.unsigned b + Int.unsigned c < 2 ^ (bits + 1) ->
  Int.unsigned a + Int.unsigned b + Int.unsigned c =
    Int.unsigned (fst (addcarryx_m bits c a b)) + 2 ^ bits * Int.unsigned (snd (addcarryx_m bits c a b)) /\
  0 <= Int.unsigned (fst (addcarryx_m bits c a b)) < 2 ^ bits /\
  0 <= Int.unsigned (snd (addcarryx_m bits c a b)) <= 1.
Proof.
  intros Hb Hs. unfold addcarryx_m. cbn [fst snd].
  set (S := Int.unsigned a + Int.unsigned b + Int.unsigned c) in *.
  assert (P: 2 ^ (bits + 1) <= 2 ^ 27) by (apply Z.pow_le_mono_r; lia).
  assert (P2: 2 ^ (bits + 1) = 2 * 2 ^ bits) by (rewrite Z.pow_add_r by lia; lia).
  assert (S0: 0 <= S) by (unfold S; rep_lia).
  assert (X: Int.unsigned (Int.add (Int.add a b) c) = S).
  { unfold Int.add. rewrite (Int.unsigned_repr (Int.unsigned a + Int.unsigned b)) by rep_lia.
    apply Int.unsigned_repr. rep_lia. }
  assert (F: Int.unsigned (Int.and (Int.add (Int.add a b) c) (Int.repr (2 ^ bits - 1))) = S mod 2 ^ bits).
  { unfold Int.and. rewrite X, (Int.unsigned_repr (2 ^ bits - 1)) by rep_lia.
    rewrite land_ones_mod' by lia.
    apply Int.unsigned_repr. pose proof (Z.mod_pos_bound S (2 ^ bits) ltac:(lia)). rep_lia. }
  assert (Q: 0 <= S / 2 ^ bits <= 1).
  { split; [apply Z.div_pos; lia|]. assert (S / 2 ^ bits < 2) by (apply Z.div_lt_upper_bound; lia). lia. }
  assert (C: Int.unsigned (Int.and (Int.shru (Int.add (Int.add a b) c) (Int.repr bits)) Int.one) = S / 2 ^ bits).
  { unfold Int.and, Int.shru. rewrite X, (Int.unsigned_repr bits) by rep_lia.
    rewrite Z.shiftr_div_pow2 by lia. rewrite (Int.unsigned_repr (S / 2 ^ bits)) by rep_lia.
    change (Int.unsigned Int.one) with (2 ^ 1 - 1). rewrite land_ones_mod' by lia.
    rewrite Z.mod_small by lia. apply Int.unsigned_repr. rep_lia. }
  rewrite F, C. pose proof (Z.div_mod S (2 ^ bits) ltac:(lia)).
  pose proof (Z.mod_pos_bound S (2 ^ bits) ltac:(lia)). lia.
Qed.

Lemma cmov_spec (t z nz: int) : Int.unsigned t <= 1 ->
  cmovznz32_m t z nz = if zeq (Int.unsigned t) 0 then z else nz.
Proof.
  intros Ht. pose proof (Int.unsigned_range t) as R.
  rewrite <- (Int.repr_unsigned t). unfold cmovznz32_m.
  destruct (zeq (Int.unsigned t) 0) as [E|E].
  - rewrite E. change (Int.eq (Int.repr 0) Int.zero) with true. cbv iota.
    change (Int.neg Int.zero) with Int.zero.
    rewrite Int.and_zero_l, Int.not_zero, Int.and_mone_l, Int.or_zero_l. reflexivity.
  - replace (Int.unsigned t) with 1 by lia.
    change (Int.eq (Int.repr 1) Int.zero) with false. cbv iota.
    change (Int.neg Int.one) with Int.mone.
    rewrite Int.and_mone_l, Int.not_mone, Int.and_zero_l, Int.or_zero. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* fe_freeze                                                           *)
(* ------------------------------------------------------------------ *)

Ltac side := rewrite ?Int.unsigned_zero, ?Int.unsigned_repr by rep_lia; rep_lia.

Ltac sb_step :=
  match goal with |- context [subborrow_m ?bits ?c ?a ?b] =>
    let Sp := fresh "Sb" in
    pose proof (subborrow_spec bits c a b ltac:(lia)) as Sp;
    let p := fresh "r" in let q := fresh "c" in
    destruct (subborrow_m bits c a b) as [p q]; cbn [fst snd] in Sp;
    specialize (Sp ltac:(side));
    rewrite ?Int.unsigned_zero, ?Int.unsigned_repr in Sp by rep_lia
  end.

Ltac ac_step :=
  match goal with |- context [addcarryx_m ?bits ?c ?a ?b] =>
    let Sp := fresh "Ac" in
    pose proof (addcarry_spec bits c a b ltac:(lia)) as Sp;
    let p := fresh "o" in let q := fresh "k" in
    destruct (addcarryx_m bits c a b) as [p q]; cbn [fst snd] in Sp;
    specialize (Sp ltac:(side));
    rewrite ?Int.unsigned_zero, ?Int.unsigned_repr in Sp by rep_lia
  end.

Lemma fe_freeze_ok f : bounded tight f -> fe_freeze_m f = canon (feval f mod P25519).
Proof.
  intros Hf. destruct10 f. bnd_limbs Hf.
  unfold fe_freeze_m. znth10.
  do 10 sb_step.
  match goal with |- context [cmovznz32_m ?t] => rewrite (cmov_spec t) by lia end.
  match goal with |- context [if zeq (Int.unsigned ?t) 0 then _ else _] =>
    destruct (zeq (Int.unsigned t) 0) as [Z0|Z0] end.
  - rewrite !Int.and_zero_l. do 10 ac_step.
    rewrite <- (Int.repr_unsigned o), <- (Int.repr_unsigned o0), <- (Int.repr_unsigned o1),
      <- (Int.repr_unsigned o2), <- (Int.repr_unsigned o3), <- (Int.repr_unsigned o4),
      <- (Int.repr_unsigned o5), <- (Int.repr_unsigned o6), <- (Int.repr_unsigned o7),
      <- (Int.repr_unsigned o8).
    rewrite <- canon_limbs_lit by lia. f_equal.
    unfold feval, P25519. cbn [map fevalZ].
    apply Z.mod_unique with (q := 1); [left|]; rep_lia.
  - replace (Int.repr 4294967295) with Int.mone by (apply Int.mkint_eq; reflexivity).
    rewrite !Int.and_mone_l. do 10 ac_step.
    rewrite <- (Int.repr_unsigned o), <- (Int.repr_unsigned o0), <- (Int.repr_unsigned o1),
      <- (Int.repr_unsigned o2), <- (Int.repr_unsigned o3), <- (Int.repr_unsigned o4),
      <- (Int.repr_unsigned o5), <- (Int.repr_unsigned o6), <- (Int.repr_unsigned o7),
      <- (Int.repr_unsigned o8).
    rewrite <- canon_limbs_lit by lia. f_equal.
    unfold feval, P25519. cbn [map fevalZ].
    apply Z.mod_unique with (q := 0); [left|]; rep_lia.
Qed.
