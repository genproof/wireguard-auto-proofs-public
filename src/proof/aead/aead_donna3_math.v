(* the arithmetic of one block of poly1305_core_blocks (lib/crypto/poly1305-donna32.c), plain Coq.
   adb3_c is the loop body of poly1305_core_blocks on CompCert integers, written exactly as VST's symbolic
   execution computes it (casts u32 -> u64 = Int64.repr (Int.unsigned _), u64 -> u32 = Int.repr
   (Int64.unsigned _)).  adb3_c_ok: no overflow matters, the limbs stay in bounds and the value is
   (h + m + hibit 2^128) * r mod 2^130 - 5, m the message limbs. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.aead.aead_model.
Require Import WgNoise.proof.aead.aead_spec.

Local Open Scope Z_scope.

Definition adb3_L (x: int) : int64 := Int64.repr (Int.unsigned x).

(* inputs: h0..h4 (state), r0..r4 (key), s1..s4 (5 r1 .. 5 r4), w0..w4 (le32 at offsets 0, 3, 6, 9, 12 of
   the block), hb (hibit << 24); output: the new h0..h4 *)
Definition adb3_c (h0 h1 h2 h3 h4 r0 r1 r2 r3 r4 s1 s2 s3 s4 w0 w1 w2 w3 w4 hb: int) : list int :=
  let h0 := Int.add h0 (Int.and w0 (Int.repr 67108863)) in
  let h1 := Int.add h1 (Int.and (Int.shru w1 (Int.repr 2)) (Int.repr 67108863)) in
  let h2 := Int.add h2 (Int.and (Int.shru w2 (Int.repr 4)) (Int.repr 67108863)) in
  let h3 := Int.add h3 (Int.and (Int.shru w3 (Int.repr 6)) (Int.repr 67108863)) in
  let h4 := Int.add h4 (Int.or (Int.shru w4 (Int.repr 8)) hb) in
  let d0 := Int64.add (Int64.add (Int64.add (Int64.add
              (Int64.mul (adb3_L h0) (adb3_L r0)) (Int64.mul (adb3_L h1) (adb3_L s4)))
              (Int64.mul (adb3_L h2) (adb3_L s3))) (Int64.mul (adb3_L h3) (adb3_L s2)))
              (Int64.mul (adb3_L h4) (adb3_L s1)) in
  let d1 := Int64.add (Int64.add (Int64.add (Int64.add
              (Int64.mul (adb3_L h0) (adb3_L r1)) (Int64.mul (adb3_L h1) (adb3_L r0)))
              (Int64.mul (adb3_L h2) (adb3_L s4))) (Int64.mul (adb3_L h3) (adb3_L s3)))
              (Int64.mul (adb3_L h4) (adb3_L s2)) in
  let d2 := Int64.add (Int64.add (Int64.add (Int64.add
              (Int64.mul (adb3_L h0) (adb3_L r2)) (Int64.mul (adb3_L h1) (adb3_L r1)))
              (Int64.mul (adb3_L h2) (adb3_L r0))) (Int64.mul (adb3_L h3) (adb3_L s4)))
              (Int64.mul (adb3_L h4) (adb3_L s3)) in
  let d3 := Int64.add (Int64.add (Int64.add (Int64.add
              (Int64.mul (adb3_L h0) (adb3_L r3)) (Int64.mul (adb3_L h1) (adb3_L r2)))
              (Int64.mul (adb3_L h2) (adb3_L r1))) (Int64.mul (adb3_L h3) (adb3_L r0)))
              (Int64.mul (adb3_L h4) (adb3_L s4)) in
  let d4 := Int64.add (Int64.add (Int64.add (Int64.add
              (Int64.mul (adb3_L h0) (adb3_L r4)) (Int64.mul (adb3_L h1) (adb3_L r3)))
              (Int64.mul (adb3_L h2) (adb3_L r2))) (Int64.mul (adb3_L h3) (adb3_L r1)))
              (Int64.mul (adb3_L h4) (adb3_L r0)) in
  let c := Int.repr (Int64.unsigned (Int64.shru d0 (Int64.repr (Int.unsigned (Int.repr 26))))) in
  let h0 := Int.and (Int.repr (Int64.unsigned d0)) (Int.repr 67108863) in
  let d1 := Int64.add d1 (adb3_L c) in
  let c := Int.repr (Int64.unsigned (Int64.shru d1 (Int64.repr (Int.unsigned (Int.repr 26))))) in
  let h1 := Int.and (Int.repr (Int64.unsigned d1)) (Int.repr 67108863) in
  let d2 := Int64.add d2 (adb3_L c) in
  let c := Int.repr (Int64.unsigned (Int64.shru d2 (Int64.repr (Int.unsigned (Int.repr 26))))) in
  let h2 := Int.and (Int.repr (Int64.unsigned d2)) (Int.repr 67108863) in
  let d3 := Int64.add d3 (adb3_L c) in
  let c := Int.repr (Int64.unsigned (Int64.shru d3 (Int64.repr (Int.unsigned (Int.repr 26))))) in
  let h3 := Int.and (Int.repr (Int64.unsigned d3)) (Int.repr 67108863) in
  let d4 := Int64.add d4 (adb3_L c) in
  let c := Int.repr (Int64.unsigned (Int64.shru d4 (Int64.repr (Int.unsigned (Int.repr 26))))) in
  let h4 := Int.and (Int.repr (Int64.unsigned d4)) (Int.repr 67108863) in
  let h0 := Int.add h0 (Int.mul c (Int.repr 5)) in
  let c := Int.shru h0 (Int.repr 26) in
  let h0 := Int.and h0 (Int.repr 67108863) in
  let h1 := Int.add h1 c in
  [h0; h1; h2; h3; h4].

(* the message limbs the loop body adds (m4 without hibit) *)
Definition adb3_m (w0 w1 w2 w3 w4: int) : Z :=
  Int.unsigned (Int.and w0 (Int.repr 67108863)) +
  Int.unsigned (Int.and (Int.shru w1 (Int.repr 2)) (Int.repr 67108863)) * 2 ^ 26 +
  Int.unsigned (Int.and (Int.shru w2 (Int.repr 4)) (Int.repr 67108863)) * 2 ^ 52 +
  Int.unsigned (Int.and (Int.shru w3 (Int.repr 6)) (Int.repr 67108863)) * 2 ^ 78 +
  Int.unsigned (Int.shru w4 (Int.repr 8)) * 2 ^ 104.

(* helpers for adb3_c_ok: the computation split into the products, the carry chain and the final fold *)
Definition adb3_d (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4: int) : int64 :=
  Int64.add (Int64.add (Int64.add (Int64.add
    (Int64.mul (adb3_L a0) (adb3_L b0)) (Int64.mul (adb3_L a1) (adb3_L b1)))
    (Int64.mul (adb3_L a2) (adb3_L b2))) (Int64.mul (adb3_L a3) (adb3_L b3)))
    (Int64.mul (adb3_L a4) (adb3_L b4)).

Definition adb3_cy (d: int64) : int :=
  Int.repr (Int64.unsigned (Int64.shru d (Int64.repr (Int.unsigned (Int.repr 26))))).

Definition adb3_lo (d: int64) : int := Int.and (Int.repr (Int64.unsigned d)) (Int.repr 67108863).

Definition adb3_chain (d0 d1 d2 d3 d4: int64) : list int :=
  let c := adb3_cy d0 in
  let h0 := adb3_lo d0 in
  let d1 := Int64.add d1 (adb3_L c) in
  let c := adb3_cy d1 in
  let h1 := adb3_lo d1 in
  let d2 := Int64.add d2 (adb3_L c) in
  let c := adb3_cy d2 in
  let h2 := adb3_lo d2 in
  let d3 := Int64.add d3 (adb3_L c) in
  let c := adb3_cy d3 in
  let h3 := adb3_lo d3 in
  let d4 := Int64.add d4 (adb3_L c) in
  let c := adb3_cy d4 in
  let h4 := adb3_lo d4 in
  let h0 := Int.add h0 (Int.mul c (Int.repr 5)) in
  let c := Int.shru h0 (Int.repr 26) in
  let h0 := Int.and h0 (Int.repr 67108863) in
  let h1 := Int.add h1 c in
  [h0; h1; h2; h3; h4].

Definition adb3_tail (h0 h1 h2 h3 h4 r0 r1 r2 r3 r4 s1 s2 s3 s4: int) : list int :=
  adb3_chain (adb3_d h0 h1 h2 h3 h4 r0 s4 s3 s2 s1) (adb3_d h0 h1 h2 h3 h4 r1 r0 s4 s3 s2)
             (adb3_d h0 h1 h2 h3 h4 r2 r1 r0 s4 s3) (adb3_d h0 h1 h2 h3 h4 r3 r2 r1 r0 s4)
             (adb3_d h0 h1 h2 h3 h4 r4 r3 r2 r1 r0).

Lemma adb3_c_eq h0 h1 h2 h3 h4 r0 r1 r2 r3 r4 s1 s2 s3 s4 w0 w1 w2 w3 w4 hb :
  adb3_c h0 h1 h2 h3 h4 r0 r1 r2 r3 r4 s1 s2 s3 s4 w0 w1 w2 w3 w4 hb =
  adb3_tail (Int.add h0 (Int.and w0 (Int.repr 67108863)))
            (Int.add h1 (Int.and (Int.shru w1 (Int.repr 2)) (Int.repr 67108863)))
            (Int.add h2 (Int.and (Int.shru w2 (Int.repr 4)) (Int.repr 67108863)))
            (Int.add h3 (Int.and (Int.shru w3 (Int.repr 6)) (Int.repr 67108863)))
            (Int.add h4 (Int.or (Int.shru w4 (Int.repr 8)) hb))
            r0 r1 r2 r3 r4 s1 s2 s3 s4.
Proof. reflexivity. Qed.

Lemma adb3_uL (x: int) : Int64.unsigned (adb3_L x) = Int.unsigned x.
Proof.
  unfold adb3_L. apply Int64.unsigned_repr. pose proof (Int.unsigned_range_2 x). rep_lia.
Qed.

Lemma adb3_umul (a b: int) :
  Int.unsigned a * Int.unsigned b <= Int64.max_unsigned ->
  Int64.unsigned (Int64.mul (adb3_L a) (adb3_L b)) = Int.unsigned a * Int.unsigned b.
Proof.
  intros. unfold Int64.mul. rewrite !adb3_uL. apply Int64.unsigned_repr. split; [|assumption].
  apply Z.mul_nonneg_nonneg; apply Int.unsigned_range.
Qed.

Lemma adb3_uadd_mul (x: int64) (a b: int) (v: Z) :
  Int64.unsigned x = v -> 0 <= v -> v + Int.unsigned a * Int.unsigned b <= Int64.max_unsigned ->
  Int64.unsigned (Int64.add x (Int64.mul (adb3_L a) (adb3_L b))) = v + Int.unsigned a * Int.unsigned b.
Proof.
  intros Hx Hv Hs. assert (0 <= Int.unsigned a * Int.unsigned b)
    by (apply Z.mul_nonneg_nonneg; apply Int.unsigned_range).
  unfold Int64.add. rewrite adb3_umul by lia. rewrite Hx. apply Int64.unsigned_repr. lia.
Qed.

Lemma adb3_ud (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4: int) :
  Int.unsigned a0 * Int.unsigned b0 < 2 ^ 58 -> Int.unsigned a1 * Int.unsigned b1 < 2 ^ 58 ->
  Int.unsigned a2 * Int.unsigned b2 < 2 ^ 58 -> Int.unsigned a3 * Int.unsigned b3 < 2 ^ 58 ->
  Int.unsigned a4 * Int.unsigned b4 < 2 ^ 58 ->
  Int64.unsigned (adb3_d a0 a1 a2 a3 a4 b0 b1 b2 b3 b4) =
  Int.unsigned a0 * Int.unsigned b0 + Int.unsigned a1 * Int.unsigned b1 +
  Int.unsigned a2 * Int.unsigned b2 + Int.unsigned a3 * Int.unsigned b3 +
  Int.unsigned a4 * Int.unsigned b4.
Proof.
  intros P0 P1 P2 P3 P4.
  assert (N: forall a b: int, 0 <= Int.unsigned a * Int.unsigned b)
    by (intros; apply Z.mul_nonneg_nonneg; apply Int.unsigned_range).
  pose proof (N a0 b0). pose proof (N a1 b1). pose proof (N a2 b2). pose proof (N a3 b3).
  pose proof (N a4 b4).
  unfold adb3_d.
  apply adb3_uadd_mul; [apply adb3_uadd_mul; [apply adb3_uadd_mul; [apply adb3_uadd_mul;
    [apply adb3_umul|..]|..]|..]|..]; rep_lia.
Qed.

Lemma adb3_ucy (d: int64) : Int64.unsigned d < 2 ^ 58 -> Int.unsigned (adb3_cy d) = Int64.unsigned d / 2 ^ 26.
Proof.
  intros. unfold adb3_cy. rewrite Int64.shru_div_two_p.
  change (Int64.unsigned (Int64.repr (Int.unsigned (Int.repr 26)))) with 26.
  change (two_p 26) with (2 ^ 26).
  assert (0 <= Int64.unsigned d / 2 ^ 26 < 2 ^ 32).
  { split. apply Z.div_pos; rep_lia. apply Z.div_lt_upper_bound; rep_lia. }
  rewrite Int64.unsigned_repr by rep_lia. apply Int.unsigned_repr. rep_lia.
Qed.

Lemma adb3_uand (x: int) : Int.unsigned (Int.and x (Int.repr 67108863)) = Int.unsigned x mod 2 ^ 26.
Proof.
  change (Int.repr 67108863) with (Int.repr (two_p 26 - 1)).
  rewrite <- Int.zero_ext_and by lia. rewrite Int.zero_ext_mod by rep_lia. reflexivity.
Qed.

Lemma adb3_ulo (d: int64) : Int.unsigned (adb3_lo d) = Int64.unsigned d mod 2 ^ 26.
Proof.
  unfold adb3_lo. rewrite adb3_uand, Int.unsigned_repr_eq.
  symmetry. apply Zmod_div_mod; [lia | rep_lia | exists (2 ^ 6); reflexivity].
Qed.

Lemma adb3_ushru (x: int) (k: Z) : 0 <= k < 32 -> Int.unsigned (Int.shru x (Int.repr k)) = Int.unsigned x / 2 ^ k.
Proof.
  intros. rewrite Int.shru_div_two_p. rewrite (Int.unsigned_repr k) by rep_lia.
  rewrite two_p_equiv. pose proof (Int.unsigned_range_2 x).
  assert (0 <= Int.unsigned x / 2 ^ k <= Int.unsigned x).
  { split. apply Z.div_pos; lia. apply Z.div_le_upper_bound. lia.
    assert (1 <= 2 ^ k) by (apply Z.pow_le_mono_r with (a := 2) (b := 0) (c := k); lia). nia. }
  apply Int.unsigned_repr. lia.
Qed.

Lemma adb3_uadd32 (x y: int) :
  Int.unsigned x + Int.unsigned y <= Int.max_unsigned -> Int.unsigned (Int.add x y) = Int.unsigned x + Int.unsigned y.
Proof.
  intros. unfold Int.add. apply Int.unsigned_repr. pose proof (Int.unsigned_range x).
  pose proof (Int.unsigned_range y). lia.
Qed.

Lemma adb3_umul5 (c: int) :
  Int.unsigned c * 5 <= Int.max_unsigned -> Int.unsigned (Int.mul c (Int.repr 5)) = Int.unsigned c * 5.
Proof.
  intros. unfold Int.mul. change (Int.unsigned (Int.repr 5)) with 5. apply Int.unsigned_repr.
  pose proof (Int.unsigned_range c). lia.
Qed.

Lemma adb3_uaddL (d: int64) (c: int) :
  Int64.unsigned d + Int.unsigned c <= Int64.max_unsigned ->
  Int64.unsigned (Int64.add d (adb3_L c)) = Int64.unsigned d + Int.unsigned c.
Proof.
  intros. unfold Int64.add. rewrite adb3_uL. apply Int64.unsigned_repr.
  pose proof (Int.unsigned_range c). pose proof (Int64.unsigned_range d). lia.
Qed.

Lemma adb3_uor (w: int) (hibit: Z) : hibit = 0 \/ hibit = 1 ->
  Int.unsigned (Int.or (Int.shru w (Int.repr 8)) (Int.repr (hibit * 2 ^ 24))) =
  Int.unsigned (Int.shru w (Int.repr 8)) + hibit * 2 ^ 24.
Proof.
  intros [-> | ->].
  - change (Int.repr (0 * 2 ^ 24)) with Int.zero. rewrite Int.or_zero. lia.
  - rewrite <- Int.add_is_or.
    + rewrite adb3_uadd32; rewrite adb3_ushru by lia; change (Int.unsigned (Int.repr (1 * 2 ^ 24))) with (2 ^ 24).
      * lia.
      * assert (Int.unsigned w / 2 ^ 8 < 2 ^ 24) by (apply Z.div_lt_upper_bound; rep_lia). rep_lia.
    + apply Int.same_bits_eq. intros i Hi. rewrite Int.bits_and, Int.bits_zero by assumption.
      rewrite Int.testbit_repr by assumption. replace (1 * 2 ^ 24) with (2 ^ 24) by lia.
      rewrite Z.pow2_bits_eqb by lia.
      destruct (Z.eq_dec i 24) as [-> | Hne].
      * rewrite Int.bits_shru by assumption. reflexivity.
      * rewrite (proj2 (Z.eqb_neq 24 i)) by lia. apply andb_false_r.
Qed.

Lemma adb3_z0 (a b c e f: Z) : Znth 0 [a; b; c; e; f] = a. Proof. reflexivity. Qed.
Lemma adb3_z1 (a b c e f: Z) : Znth 1 [a; b; c; e; f] = b. Proof. reflexivity. Qed.
Lemma adb3_z2 (a b c e f: Z) : Znth 2 [a; b; c; e; f] = c. Proof. reflexivity. Qed.
Lemma adb3_z3 (a b c e f: Z) : Znth 3 [a; b; c; e; f] = e. Proof. reflexivity. Qed.
Lemma adb3_z4 (a b c e f: Z) : Znth 4 [a; b; c; e; f] = f. Proof. reflexivity. Qed.
Lemma adb3_zl (a b c e f: Z) : Zlength [a; b; c; e; f] = 5. Proof. reflexivity. Qed.

Lemma adb3_dm (x q l: Z) : q = x / 2 ^ 26 -> l = x mod 2 ^ 26 -> x = 2 ^ 26 * q + l /\ 0 <= l < 2 ^ 26.
Proof. intros -> ->. split. apply Z.div_mod; lia. apply Z.mod_pos_bound; lia. Qed.

(* the carry chain: limbs in bounds, value = sum d_i 2^(26 i) mod p *)
Lemma adb3_chain_ok (d0 d1 d2 d3 d4: int64) (v: Z) :
  Int64.unsigned d0 < 2 ^ 57 -> Int64.unsigned d1 < 2 ^ 57 -> Int64.unsigned d2 < 2 ^ 57 ->
  Int64.unsigned d3 < 2 ^ 57 -> Int64.unsigned d4 < 2 ^ 55 ->
  (Int64.unsigned d0 + Int64.unsigned d1 * 2 ^ 26 + Int64.unsigned d2 * 2 ^ 52 +
   Int64.unsigned d3 * 2 ^ 78 + Int64.unsigned d4 * 2 ^ 104) mod p1305_p = v mod p1305_p ->
  p1305_limbs_ok (map Int.unsigned (adb3_chain d0 d1 d2 d3 d4)) /\
  p1305_limbs_val (map Int.unsigned (adb3_chain d0 d1 d2 d3 d4)) mod p1305_p = v mod p1305_p.
Proof.
  intros B0 B1 B2 B3 B4 Hv. unfold adb3_chain. cbv zeta.
  set (c0 := adb3_cy d0). set (l0 := adb3_lo d0).
  set (e1 := Int64.add d1 (adb3_L c0)). set (c1 := adb3_cy e1). set (l1 := adb3_lo e1).
  set (e2 := Int64.add d2 (adb3_L c1)). set (c2 := adb3_cy e2). set (l2 := adb3_lo e2).
  set (e3 := Int64.add d3 (adb3_L c2)). set (c3 := adb3_cy e3). set (l3 := adb3_lo e3).
  set (e4 := Int64.add d4 (adb3_L c3)). set (c4 := adb3_cy e4). set (l4 := adb3_lo e4).
  set (g0 := Int.add l0 (Int.mul c4 (Int.repr 5))).
  pose proof (Int.unsigned_range_2 c0). pose proof (Int.unsigned_range_2 c1).
  pose proof (Int.unsigned_range_2 c2). pose proof (Int.unsigned_range_2 c3).
  assert (Ec0: Int.unsigned c0 = Int64.unsigned d0 / 2 ^ 26) by (apply adb3_ucy; lia).
  assert (El0: Int.unsigned l0 = Int64.unsigned d0 mod 2 ^ 26) by apply adb3_ulo.
  assert (Ee1: Int64.unsigned e1 = Int64.unsigned d1 + Int.unsigned c0) by (apply adb3_uaddL; rep_lia).
  assert (Ec1: Int.unsigned c1 = Int64.unsigned e1 / 2 ^ 26) by (apply adb3_ucy; rep_lia).
  assert (El1: Int.unsigned l1 = Int64.unsigned e1 mod 2 ^ 26) by apply adb3_ulo.
  assert (Ee2: Int64.unsigned e2 = Int64.unsigned d2 + Int.unsigned c1) by (apply adb3_uaddL; rep_lia).
  assert (Ec2: Int.unsigned c2 = Int64.unsigned e2 / 2 ^ 26) by (apply adb3_ucy; rep_lia).
  assert (El2: Int.unsigned l2 = Int64.unsigned e2 mod 2 ^ 26) by apply adb3_ulo.
  assert (Ee3: Int64.unsigned e3 = Int64.unsigned d3 + Int.unsigned c2) by (apply adb3_uaddL; rep_lia).
  assert (Ec3: Int.unsigned c3 = Int64.unsigned e3 / 2 ^ 26) by (apply adb3_ucy; rep_lia).
  assert (El3: Int.unsigned l3 = Int64.unsigned e3 mod 2 ^ 26) by apply adb3_ulo.
  assert (Ee4: Int64.unsigned e4 = Int64.unsigned d4 + Int.unsigned c3) by (apply adb3_uaddL; rep_lia).
  assert (Ec4: Int.unsigned c4 = Int64.unsigned e4 / 2 ^ 26) by (apply adb3_ucy; rep_lia).
  assert (El4: Int.unsigned l4 = Int64.unsigned e4 mod 2 ^ 26) by apply adb3_ulo.
  destruct (adb3_dm _ _ _ Ec0 El0) as [D0 R0]. destruct (adb3_dm _ _ _ Ec1 El1) as [D1 R1].
  destruct (adb3_dm _ _ _ Ec2 El2) as [D2 R2]. destruct (adb3_dm _ _ _ Ec3 El3) as [D3 R3].
  destruct (adb3_dm _ _ _ Ec4 El4) as [D4 R4].
  assert (Bc4: Int.unsigned c4 < 2 ^ 29 + 2 ^ 7) by lia.
  assert (M5: Int.unsigned (Int.mul c4 (Int.repr 5)) = Int.unsigned c4 * 5) by (apply adb3_umul5; rep_lia).
  assert (Eg0: Int.unsigned g0 = Int.unsigned l0 + Int.unsigned c4 * 5).
  { unfold g0. rewrite adb3_uadd32; rewrite M5; rep_lia. }
  assert (Es: Int.unsigned (Int.shru g0 (Int.repr 26)) = Int.unsigned g0 / 2 ^ 26) by (apply adb3_ushru; lia).
  destruct (adb3_dm (Int.unsigned g0) _ _ eq_refl eq_refl) as [DG RG].
  pose proof (Int.unsigned_range_2 c4). pose proof (Int.unsigned_range_2 g0).
  assert (Bq: 0 <= Int.unsigned g0 / 2 ^ 26 < 2 ^ 6) by lia.
  assert (Eh0: Int.unsigned (Int.and g0 (Int.repr 67108863)) = Int.unsigned g0 mod 2 ^ 26) by apply adb3_uand.
  assert (Eh1: Int.unsigned (Int.add l1 (Int.shru g0 (Int.repr 26))) = Int.unsigned l1 + Int.unsigned g0 / 2 ^ 26).
  { rewrite adb3_uadd32; rewrite Es; rep_lia. }
  cbn [map]. rewrite Eh0, Eh1. unfold p1305_limbs_ok, p1305_limbs_val.
  rewrite adb3_z0, adb3_z1, adb3_z2, adb3_z3, adb3_z4, adb3_zl.
  split. lia.
  rewrite <- Hv.
  replace (Int.unsigned g0 mod 2 ^ 26 + (Int.unsigned l1 + Int.unsigned g0 / 2 ^ 26) * 2 ^ 26 +
     Int.unsigned l2 * 2 ^ 52 + Int.unsigned l3 * 2 ^ 78 + Int.unsigned l4 * 2 ^ 104)
    with ((Int64.unsigned d0 + Int64.unsigned d1 * 2 ^ 26 + Int64.unsigned d2 * 2 ^ 52 +
           Int64.unsigned d3 * 2 ^ 78 + Int64.unsigned d4 * 2 ^ 104) + (- Int.unsigned c4) * p1305_p)
    by (unfold p1305_p; lia).
  apply Z_mod_plus_full.
Qed.

Lemma adb3_mb (a b A B: Z) : 0 <= a <= A -> 0 <= b <= B -> 0 <= a * b <= A * B.
Proof. intros. split. apply Z.mul_nonneg_nonneg; lia. apply Z.mul_le_mono_nonneg; lia. Qed.

Lemma adb3_mb' (a b A B: Z) : 0 <= a <= A -> 0 <= b <= B -> a * b <= A * B.
Proof. intros. apply Z.mul_le_mono_nonneg; lia. Qed.

Lemma adb3_s5 (x0 x1 x2 x3 x4 X0 X1 X2 X3 X4 C: Z) :
  x0 <= X0 -> x1 <= X1 -> x2 <= X2 -> x3 <= X3 -> x4 <= X4 -> X0 + X1 + X2 + X3 + X4 < C ->
  x0 + x1 + x2 + x3 + x4 < C.
Proof. lia. Qed.

(* the products: bounds and the value h * r mod p *)
Lemma adb3_tail_ok (h0 h1 h2 h3 h4 r0 r1 r2 r3 r4 s1 s2 s3 s4: int) (v: Z) :
  Int.unsigned h0 <= 2 ^ 27 -> Int.unsigned h1 <= 2 ^ 27 + 2 ^ 6 -> Int.unsigned h2 <= 2 ^ 27 ->
  Int.unsigned h3 <= 2 ^ 27 -> Int.unsigned h4 <= 2 ^ 26 + 2 ^ 25 ->
  Int.unsigned r0 <= 2 ^ 26 -> Int.unsigned r1 <= 2 ^ 26 -> Int.unsigned r2 <= 2 ^ 26 ->
  Int.unsigned r3 <= 2 ^ 26 -> Int.unsigned r4 <= 2 ^ 20 ->
  Int.unsigned s1 = 5 * Int.unsigned r1 -> Int.unsigned s2 = 5 * Int.unsigned r2 ->
  Int.unsigned s3 = 5 * Int.unsigned r3 -> Int.unsigned s4 = 5 * Int.unsigned r4 ->
  (Int.unsigned h0 + Int.unsigned h1 * 2 ^ 26 + Int.unsigned h2 * 2 ^ 52 + Int.unsigned h3 * 2 ^ 78 +
   Int.unsigned h4 * 2 ^ 104) *
  (Int.unsigned r0 + Int.unsigned r1 * 2 ^ 26 + Int.unsigned r2 * 2 ^ 52 + Int.unsigned r3 * 2 ^ 78 +
   Int.unsigned r4 * 2 ^ 104) = v ->
  p1305_limbs_ok (map Int.unsigned (adb3_tail h0 h1 h2 h3 h4 r0 r1 r2 r3 r4 s1 s2 s3 s4)) /\
  p1305_limbs_val (map Int.unsigned (adb3_tail h0 h1 h2 h3 h4 r0 r1 r2 r3 r4 s1 s2 s3 s4)) mod p1305_p =
  v mod p1305_p.
Proof.
  intros A0 A1 A2 A3 A4 B0 B1 B2 B3 B4 S1 S2 S3 S4 Hv. subst v. unfold adb3_tail.
  pose proof (Int.unsigned_range_2 h0) as N0. pose proof (Int.unsigned_range_2 h1) as N1.
  pose proof (Int.unsigned_range_2 h2) as N2. pose proof (Int.unsigned_range_2 h3) as N3.
  pose proof (Int.unsigned_range_2 h4) as N4. pose proof (Int.unsigned_range_2 r0) as M0.
  pose proof (Int.unsigned_range_2 r1) as M1. pose proof (Int.unsigned_range_2 r2) as M2.
  pose proof (Int.unsigned_range_2 r3) as M3. pose proof (Int.unsigned_range_2 r4) as M4.
  set (a0 := Int.unsigned h0) in *. set (a1 := Int.unsigned h1) in *. set (a2 := Int.unsigned h2) in *.
  set (a3 := Int.unsigned h3) in *. set (a4 := Int.unsigned h4) in *.
  set (b0 := Int.unsigned r0) in *. set (b1 := Int.unsigned r1) in *. set (b2 := Int.unsigned r2) in *.
  set (b3 := Int.unsigned r3) in *. set (b4 := Int.unsigned r4) in *.
  assert (A0': 0 <= a0 <= 2 ^ 27) by lia. assert (A1': 0 <= a1 <= 2 ^ 27 + 2 ^ 6) by lia.
  assert (A2': 0 <= a2 <= 2 ^ 27) by lia. assert (A3': 0 <= a3 <= 2 ^ 27) by lia.
  assert (A4': 0 <= a4 <= 2 ^ 26 + 2 ^ 25) by lia.
  assert (B0': 0 <= b0 <= 2 ^ 26) by lia. assert (B1': 0 <= b1 <= 2 ^ 26) by lia.
  assert (B2': 0 <= b2 <= 2 ^ 26) by lia. assert (B3': 0 <= b3 <= 2 ^ 26) by lia.
  assert (B4': 0 <= b4 <= 2 ^ 20) by lia.
  assert (C1: 0 <= 5 * b1 <= 5 * 2 ^ 26) by lia. assert (C2: 0 <= 5 * b2 <= 5 * 2 ^ 26) by lia.
  assert (C3: 0 <= 5 * b3 <= 5 * 2 ^ 26) by lia. assert (C4: 0 <= 5 * b4 <= 5 * 2 ^ 20) by lia.
  clear A0 A1 A2 A3 A4 B0 B1 B2 B3 B4 N0 N1 N2 N3 N4 M0 M1 M2 M3 M4.
  apply adb3_chain_ok; rewrite ?adb3_ud; fold a0 a1 a2 a3 a4 b0 b1 b2 b3 b4; rewrite ?S1, ?S2, ?S3, ?S4;
    try solve [eapply adb3_s5; [eapply adb3_mb'; eassumption ..| vm_compute; reflexivity]
              | eapply Z.le_lt_trans; [eapply adb3_mb'; eassumption | vm_compute; reflexivity]].
  replace ((a0 + a1 * 2 ^ 26 + a2 * 2 ^ 52 + a3 * 2 ^ 78 + a4 * 2 ^ 104) *
           (b0 + b1 * 2 ^ 26 + b2 * 2 ^ 52 + b3 * 2 ^ 78 + b4 * 2 ^ 104))
    with ((a0 * b0 + a1 * (5 * b4) + a2 * (5 * b3) + a3 * (5 * b2) + a4 * (5 * b1)) +
          (a0 * b1 + a1 * b0 + a2 * (5 * b4) + a3 * (5 * b3) + a4 * (5 * b2)) * 2 ^ 26 +
          (a0 * b2 + a1 * b1 + a2 * b0 + a3 * (5 * b4) + a4 * (5 * b3)) * 2 ^ 52 +
          (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0 + a4 * (5 * b4)) * 2 ^ 78 +
          (a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0) * 2 ^ 104 +
          (a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1 + (a2 * b4 + a3 * b3 + a4 * b2) * 2 ^ 26 +
           (a3 * b4 + a4 * b3) * 2 ^ 52 + a4 * b4 * 2 ^ 78) * p1305_p)
    by (unfold p1305_p; ring).
  rewrite Z_mod_plus_full. reflexivity.
Qed.

(* the clamped key: r < 2^124 and r is the sum of its limbs *)
Lemma adb3_r_lt (r: Z) : p1305_r_ok r -> 0 <= r < 2 ^ 124.
Proof.
  intros [Hl Hn]. rewrite <- Hl.
  assert (Hm: 21267647620597763993911028882763415551 =
              Z.land 21267647620597763993911028882763415551 (Z.ones 124)) by reflexivity.
  rewrite Hm, Z.land_assoc, Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.

Lemma adb3_r_sum (r: Z) : 0 <= r ->
  r mod 2 ^ 26 + (r / 2 ^ 26) mod 2 ^ 26 * 2 ^ 26 + (r / 2 ^ 52) mod 2 ^ 26 * 2 ^ 52 +
  (r / 2 ^ 78) mod 2 ^ 26 * 2 ^ 78 + r / 2 ^ 104 * 2 ^ 104 = r.
Proof.
  intros Hr.
  assert (E1: r / 2 ^ 52 = r / 2 ^ 26 / 2 ^ 26) by (rewrite Z.div_div by lia; reflexivity).
  assert (E2: r / 2 ^ 78 = r / 2 ^ 52 / 2 ^ 26) by (rewrite Z.div_div by lia; reflexivity).
  assert (E3: r / 2 ^ 104 = r / 2 ^ 78 / 2 ^ 26) by (rewrite Z.div_div by lia; reflexivity).
  pose proof (Z.div_mod r (2 ^ 26) ltac:(lia)) as D0.
  pose proof (Z.div_mod (r / 2 ^ 26) (2 ^ 26) ltac:(lia)) as D1.
  pose proof (Z.div_mod (r / 2 ^ 52) (2 ^ 26) ltac:(lia)) as D2.
  pose proof (Z.div_mod (r / 2 ^ 78) (2 ^ 26) ltac:(lia)) as D3.
  rewrite <- E1 in D1. rewrite <- E2 in D2. rewrite <- E3 in D3.
  set (q1 := r / 2 ^ 26) in *. set (q2 := r / 2 ^ 52) in *. set (q3 := r / 2 ^ 78) in *.
  set (q4 := r / 2 ^ 104) in *. set (m0 := r mod 2 ^ 26) in *. set (m1 := q1 mod 2 ^ 26) in *.
  set (m2 := q2 mod 2 ^ 26) in *. set (m3 := q3 mod 2 ^ 26) in *.
  clearbody q1 q2 q3 q4 m0 m1 m2 m3. lia.
Qed.

(* one block: the C computation from h (limbs ok), the clamped key r (its limbs and 5 r1 .. 5 r4, as
   poly1305_core_setkey stores them) and ANY five words *)
Lemma adb3_c_ok (hk: list Z) (r hibit: Z) (w0 w1 w2 w3 w4: int) :
  p1305_limbs_ok hk -> p1305_r_ok r -> (hibit = 0 \/ hibit = 1) ->
  let rl := p1305_r_limbs r in
  let L := map Int.unsigned
    (adb3_c (Int.repr (Znth 0 hk)) (Int.repr (Znth 1 hk)) (Int.repr (Znth 2 hk)) (Int.repr (Znth 3 hk))
            (Int.repr (Znth 4 hk))
            (Int.repr (Znth 0 rl)) (Int.repr (Znth 1 rl)) (Int.repr (Znth 2 rl)) (Int.repr (Znth 3 rl))
            (Int.repr (Znth 4 rl))
            (Int.repr (5 * Znth 1 rl)) (Int.repr (5 * Znth 2 rl)) (Int.repr (5 * Znth 3 rl))
            (Int.repr (5 * Znth 4 rl))
            w0 w1 w2 w3 w4 (Int.repr (hibit * 2 ^ 24))) in
  p1305_limbs_ok L /\
  p1305_limbs_val L mod p1305_p =
    (p1305_limbs_val hk + adb3_m w0 w1 w2 w3 w4 + hibit * 2 ^ 128) * r mod p1305_p.
Proof.
  intros Hh Hr Hhb. cbv zeta. rewrite adb3_c_eq.
  destruct Hh as (_ & K0 & K1 & K2 & K3 & K4).
  pose proof (adb3_r_lt r Hr) as Rr.
  unfold p1305_r_limbs. rewrite adb3_z0, adb3_z1, adb3_z2, adb3_z3, adb3_z4.
  assert (R0: 0 <= r mod 2 ^ 26 < 2 ^ 26) by (apply Z.mod_pos_bound; lia).
  assert (R1: 0 <= (r / 2 ^ 26) mod 2 ^ 26 < 2 ^ 26) by (apply Z.mod_pos_bound; lia).
  assert (R2: 0 <= (r / 2 ^ 52) mod 2 ^ 26 < 2 ^ 26) by (apply Z.mod_pos_bound; lia).
  assert (R3: 0 <= (r / 2 ^ 78) mod 2 ^ 26 < 2 ^ 26) by (apply Z.mod_pos_bound; lia).
  assert (R4: 0 <= r / 2 ^ 104 < 2 ^ 20)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (W0: 0 <= Int.unsigned (Int.and w0 (Int.repr 67108863)) < 2 ^ 26)
    by (rewrite adb3_uand; apply Z.mod_pos_bound; lia).
  assert (W1: 0 <= Int.unsigned (Int.and (Int.shru w1 (Int.repr 2)) (Int.repr 67108863)) < 2 ^ 26)
    by (rewrite adb3_uand; apply Z.mod_pos_bound; lia).
  assert (W2: 0 <= Int.unsigned (Int.and (Int.shru w2 (Int.repr 4)) (Int.repr 67108863)) < 2 ^ 26)
    by (rewrite adb3_uand; apply Z.mod_pos_bound; lia).
  assert (W3: 0 <= Int.unsigned (Int.and (Int.shru w3 (Int.repr 6)) (Int.repr 67108863)) < 2 ^ 26)
    by (rewrite adb3_uand; apply Z.mod_pos_bound; lia).
  assert (W4: 0 <= Int.unsigned (Int.shru w4 (Int.repr 8)) < 2 ^ 24).
  { rewrite adb3_ushru by lia. split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; rep_lia. }
  assert (O4: Int.unsigned (Int.or (Int.shru w4 (Int.repr 8)) (Int.repr (hibit * 2 ^ 24))) =
              Int.unsigned (Int.shru w4 (Int.repr 8)) + hibit * 2 ^ 24) by (apply adb3_uor; assumption).
  assert (EH0: Int.unsigned (Int.add (Int.repr (Znth 0 hk)) (Int.and w0 (Int.repr 67108863))) =
               Znth 0 hk + Int.unsigned (Int.and w0 (Int.repr 67108863)))
    by (rewrite adb3_uadd32; rewrite ?Int.unsigned_repr; rep_lia).
  assert (EH1: Int.unsigned (Int.add (Int.repr (Znth 1 hk))
                 (Int.and (Int.shru w1 (Int.repr 2)) (Int.repr 67108863))) =
               Znth 1 hk + Int.unsigned (Int.and (Int.shru w1 (Int.repr 2)) (Int.repr 67108863)))
    by (rewrite adb3_uadd32; rewrite ?Int.unsigned_repr; rep_lia).
  assert (EH2: Int.unsigned (Int.add (Int.repr (Znth 2 hk))
                 (Int.and (Int.shru w2 (Int.repr 4)) (Int.repr 67108863))) =
               Znth 2 hk + Int.unsigned (Int.and (Int.shru w2 (Int.repr 4)) (Int.repr 67108863)))
    by (rewrite adb3_uadd32; rewrite ?Int.unsigned_repr; rep_lia).
  assert (EH3: Int.unsigned (Int.add (Int.repr (Znth 3 hk))
                 (Int.and (Int.shru w3 (Int.repr 6)) (Int.repr 67108863))) =
               Znth 3 hk + Int.unsigned (Int.and (Int.shru w3 (Int.repr 6)) (Int.repr 67108863)))
    by (rewrite adb3_uadd32; rewrite ?Int.unsigned_repr; rep_lia).
  assert (EH4: Int.unsigned (Int.add (Int.repr (Znth 4 hk))
                 (Int.or (Int.shru w4 (Int.repr 8)) (Int.repr (hibit * 2 ^ 24)))) =
               Znth 4 hk + (Int.unsigned (Int.shru w4 (Int.repr 8)) + hibit * 2 ^ 24))
    by (rewrite adb3_uadd32; rewrite O4, ?Int.unsigned_repr; rep_lia).
  assert (ER0: Int.unsigned (Int.repr (r mod 2 ^ 26)) = r mod 2 ^ 26) by (apply Int.unsigned_repr; rep_lia).
  assert (ER1: Int.unsigned (Int.repr ((r / 2 ^ 26) mod 2 ^ 26)) = (r / 2 ^ 26) mod 2 ^ 26)
    by (apply Int.unsigned_repr; rep_lia).
  assert (ER2: Int.unsigned (Int.repr ((r / 2 ^ 52) mod 2 ^ 26)) = (r / 2 ^ 52) mod 2 ^ 26)
    by (apply Int.unsigned_repr; rep_lia).
  assert (ER3: Int.unsigned (Int.repr ((r / 2 ^ 78) mod 2 ^ 26)) = (r / 2 ^ 78) mod 2 ^ 26)
    by (apply Int.unsigned_repr; rep_lia).
  assert (ER4: Int.unsigned (Int.repr (r / 2 ^ 104)) = r / 2 ^ 104) by (apply Int.unsigned_repr; rep_lia).
  assert (ES1: Int.unsigned (Int.repr (5 * ((r / 2 ^ 26) mod 2 ^ 26))) = 5 * ((r / 2 ^ 26) mod 2 ^ 26))
    by (apply Int.unsigned_repr; rep_lia).
  assert (ES2: Int.unsigned (Int.repr (5 * ((r / 2 ^ 52) mod 2 ^ 26))) = 5 * ((r / 2 ^ 52) mod 2 ^ 26))
    by (apply Int.unsigned_repr; rep_lia).
  assert (ES3: Int.unsigned (Int.repr (5 * ((r / 2 ^ 78) mod 2 ^ 26))) = 5 * ((r / 2 ^ 78) mod 2 ^ 26))
    by (apply Int.unsigned_repr; rep_lia).
  assert (ES4: Int.unsigned (Int.repr (5 * (r / 2 ^ 104))) = 5 * (r / 2 ^ 104))
    by (apply Int.unsigned_repr; rep_lia).
  apply adb3_tail_ok; rewrite ?EH0, ?EH1, ?EH2, ?EH3, ?EH4, ?ER0, ?ER1, ?ER2, ?ER3, ?ER4, ?ES1, ?ES2, ?ES3, ?ES4;
    [clear - K0 K1 K2 K3 K4 R0 R1 R2 R3 R4 W0 W1 W2 W3 W4 Hhb; lia .. |].
  rewrite (adb3_r_sum r) by lia. apply (f_equal (fun x => x * r)).
  unfold p1305_limbs_val, adb3_m. ring.
Qed.
