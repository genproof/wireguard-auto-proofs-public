(* fe_tobytes_m / fe_frombytes_m: the bytes of the canonical limbs are the little-endian bytes of the value,
   and fe_frombytes_m reads them back.  Bit-level proofs.  VST-side file: no fiat-crypto here. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.x25519.x25519_model.
Require Import X25519.Limbs X25519.Freeze.

Local Open Scope Z_scope.

(* the 32 little-endian bytes of v *)
Definition le_bytes (v: Z) : list byte := map (fun j => Byte.repr ((v / 2 ^ (8 * j)) mod 2 ^ 8)) (upto 32).

Definition limbs_to_bytes (h: list int) : list byte :=
  let h0 := Znth 0 h in let h1 := Znth 1 h in let h2 := Znth 2 h in let h3 := Znth 3 h in
  let h4 := Znth 4 h in let h5 := Znth 5 h in let h6 := Znth 6 h in let h7 := Znth 7 h in
  let h8 := Znth 8 h in let h9 := Znth 9 h in
  [u8_of (Int.shru h0 (Int.repr 0));
   u8_of (Int.shru h0 (Int.repr 8));
   u8_of (Int.shru h0 (Int.repr 16));
   u8_of (Int.or (Int.shru h0 (Int.repr 24)) (Int.shl h1 (Int.repr 2)));
   u8_of (Int.shru h1 (Int.repr 6));
   u8_of (Int.shru h1 (Int.repr 14));
   u8_of (Int.or (Int.shru h1 (Int.repr 22)) (Int.shl h2 (Int.repr 3)));
   u8_of (Int.shru h2 (Int.repr 5));
   u8_of (Int.shru h2 (Int.repr 13));
   u8_of (Int.or (Int.shru h2 (Int.repr 21)) (Int.shl h3 (Int.repr 5)));
   u8_of (Int.shru h3 (Int.repr 3));
   u8_of (Int.shru h3 (Int.repr 11));
   u8_of (Int.or (Int.shru h3 (Int.repr 19)) (Int.shl h4 (Int.repr 6)));
   u8_of (Int.shru h4 (Int.repr 2));
   u8_of (Int.shru h4 (Int.repr 10));
   u8_of (Int.shru h4 (Int.repr 18));
   u8_of (Int.shru h5 (Int.repr 0));
   u8_of (Int.shru h5 (Int.repr 8));
   u8_of (Int.shru h5 (Int.repr 16));
   u8_of (Int.or (Int.shru h5 (Int.repr 24)) (Int.shl h6 (Int.repr 1)));
   u8_of (Int.shru h6 (Int.repr 7));
   u8_of (Int.shru h6 (Int.repr 15));
   u8_of (Int.or (Int.shru h6 (Int.repr 23)) (Int.shl h7 (Int.repr 3)));
   u8_of (Int.shru h7 (Int.repr 5));
   u8_of (Int.shru h7 (Int.repr 13));
   u8_of (Int.or (Int.shru h7 (Int.repr 21)) (Int.shl h8 (Int.repr 4)));
   u8_of (Int.shru h8 (Int.repr 4));
   u8_of (Int.shru h8 (Int.repr 12));
   u8_of (Int.or (Int.shru h8 (Int.repr 20)) (Int.shl h9 (Int.repr 6)));
   u8_of (Int.shru h9 (Int.repr 2));
   u8_of (Int.shru h9 (Int.repr 10));
   u8_of (Int.shru h9 (Int.repr 18))].

Lemma fe_tobytes_m_limbs f : fe_tobytes_m f = limbs_to_bytes (fe_freeze_m f).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* bit lemmas                                                          *)
(* ------------------------------------------------------------------ *)

Lemma tb_u8 (x: int) i : 0 <= i < 8 -> Byte.testbit (u8_of x) i = Int.testbit x i.
Proof.
  intros. unfold u8_of. rewrite Byte.testbit_repr by (change Byte.zwordsize with 8; lia). reflexivity.
Qed.

Lemma tb_int_byte (b: byte) i : 0 <= i < 32 ->
  Int.testbit (Int.repr (Byte.unsigned b)) i = if zlt i 8 then Byte.testbit b i else false.
Proof.
  intros. rewrite Int.testbit_repr by (change Int.zwordsize with 32; lia).
  destruct (zlt i 8); [reflexivity|].
  apply Byte.bits_above. change Byte.zwordsize with 8. lia.
Qed.

Lemma tb_divmod (v w b i: Z) : 0 <= w -> 0 <= b -> 0 <= i ->
  Z.testbit ((v / 2 ^ w) mod 2 ^ b) i = if zlt i b then Z.testbit v (i + w) else false.
Proof.
  intros. destruct (zlt i b).
  - rewrite Z.mod_pow2_bits_low by lia. rewrite Z.div_pow2_bits by lia. reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma tb_mod (v b i: Z) : 0 <= b -> 0 <= i ->
  Z.testbit (v mod 2 ^ b) i = if zlt i b then Z.testbit v i else false.
Proof.
  intros. destruct (zlt i b).
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma tb_int_repr z i : 0 <= i < 32 -> Int.testbit (Int.repr z) i = Z.testbit z i.
Proof. intros. apply Int.testbit_repr. change Int.zwordsize with 32. lia. Qed.

Lemma tb_byte_repr z i : 0 <= i < 8 -> Byte.testbit (Byte.repr z) i = Z.testbit z i.
Proof. intros. apply Byte.testbit_repr. change Byte.zwordsize with 8. lia. Qed.

Lemma tb_int_or x y i : 0 <= i < 32 -> Int.testbit (Int.or x y) i = orb (Int.testbit x i) (Int.testbit y i).
Proof. intros. apply Int.bits_or. change Int.zwordsize with 32. lia. Qed.

Lemma tb_int_and x y i : 0 <= i < 32 -> Int.testbit (Int.and x y) i = andb (Int.testbit x i) (Int.testbit y i).
Proof. intros. apply Int.bits_and. change Int.zwordsize with 32. lia. Qed.

Lemma tb_int_shru x k i : 0 <= i < 32 -> 0 <= k < 32 ->
  Int.testbit (Int.shru x (Int.repr k)) i = if zlt (i + k) 32 then Int.testbit x (i + k) else false.
Proof.
  intros. rewrite Int.bits_shru by (change Int.zwordsize with 32; lia).
  rewrite Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma tb_int_shl x k i : 0 <= i < 32 -> 0 <= k < 32 ->
  Int.testbit (Int.shl x (Int.repr k)) i = if zlt i k then false else Int.testbit x (i - k).
Proof.
  intros. rewrite Int.bits_shl by (change Int.zwordsize with 32; lia).
  rewrite Int.unsigned_repr by rep_lia. reflexivity.
Qed.

(* one rewriting / case step; every side condition is closed arithmetic *)
Ltac bstep :=
  first
  [ match goal with |- context [zlt ?a ?b] => destruct (zlt a b); try lia end
  | rewrite tb_u8 by lia
  | rewrite tb_int_or by lia
  | rewrite tb_int_and by lia
  | rewrite tb_int_shru by lia
  | rewrite tb_int_shl by lia
  | rewrite tb_int_byte by lia
  | rewrite tb_byte_repr by lia
  | rewrite tb_int_repr by lia
  | rewrite tb_divmod by lia
  | rewrite tb_mod by lia
  | rewrite Z.div_pow2_bits by lia
  | match goal with |- context [Z.testbit ?z ?k] =>
      (* only closed literals: vm_compute of a symbolic argument would be costly *)
      lazymatch z with Zpos _ => idtac | Z0 => idtac
                     | Byte.unsigned (Byte.repr (Zpos _)) => idtac | Int.unsigned (Int.repr (Zpos _)) => idtac end;
      let b := eval vm_compute in (Z.testbit z k) in
      match b with true => change (Z.testbit z k) with true | false => change (Z.testbit z k) with false end
    end ].

Ltac case_bits n i :=
  let H := fresh in
  match n with
  | 8 => assert (H: i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia
  | 32 => assert (H: i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/
                     i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16 \/ i = 17 \/
                     i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/ i = 24 \/ i = 25 \/
                     i = 26 \/ i = 27 \/ i = 28 \/ i = 29 \/ i = 30 \/ i = 31) by lia
  end;
  repeat destruct H as [H|H]; subst i.

Ltac bfinish Hhi :=
  repeat bstep;
  cbn [andb orb];
  rewrite ?Bool.orb_false_r, ?Bool.orb_false_l, ?Bool.andb_true_r, ?Bool.andb_false_r;
  repeat match goal with |- context [Z.testbit ?v ?k] =>
    let k' := eval vm_compute in k in
    progress change k with k' end;
  try reflexivity;
  try (rewrite Hhi by lia; reflexivity).

(* ------------------------------------------------------------------ *)
(* the bytes of the canonical limbs                                    *)
(* ------------------------------------------------------------------ *)

Lemma limbs_to_bytes_canon v : 0 <= v < 2 ^ 255 -> limbs_to_bytes (canon v) = le_bytes v.
Proof.
  intros Hv.
  assert (Hhi: forall k, 255 <= k -> Z.testbit v k = false).
  { intros k Hk. apply Z.bits_above_log2; [lia|].
    destruct (Z.eq_dec v 0) as [->|N]; [simpl; lia|].
    apply Z.log2_lt_pow2; [lia|]. apply Z.lt_le_trans with (2 ^ 255); [lia|].
    apply Z.pow_le_mono_r; lia. }
  unfold limbs_to_bytes, canon, le_bytes. cbn [map]. znth10. simpl upto. cbn [map].
  repeat f_equal; apply Byte.same_bits_eq; change Byte.zwordsize with 8; intros i Hi;
    case_bits 8 i; bfinish Hhi.
Qed.

(* ------------------------------------------------------------------ *)
(* fe_frombytes_m reads the little-endian bytes back                   *)
(* ------------------------------------------------------------------ *)

Lemma le_bytes_Znth v i : 0 <= i < 32 -> Znth i (le_bytes v) = Byte.repr ((v / 2 ^ (8 * i)) mod 2 ^ 8).
Proof.
  intros. unfold le_bytes. rewrite Znth_map by (rewrite Zlength_upto; simpl; lia).
  rewrite Znth_upto by (simpl; lia). reflexivity.
Qed.

Lemma frombytes_le_bytes v : 0 <= v -> fe_frombytes_m (le_bytes v) = canon v.
Proof.
  intros Hv. unfold fe_frombytes_m, le32_at, le32_of, canon.
  rewrite !le_bytes_Znth by lia.
  cbn [map].
  repeat (apply (f_equal2 (@cons int));
    [apply Int.same_bits_eq; change Int.zwordsize with 32; intros i Hi; case_bits 32 i; bfinish Hv |]).
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* the value of the canonical limbs; fe_frombytes_m is tight           *)
(* ------------------------------------------------------------------ *)

Lemma feval_canon v : 0 <= v < 2 ^ 255 -> feval (canon v) = v.
Proof.
  intros Hv. unfold feval. rewrite fevalZ_canon_range by assumption. cbn [fevalZ].
  assert (D: forall w b c, 0 <= w -> 0 <= b -> c = w + b ->
             v / 2 ^ w = (v / 2 ^ w) mod 2 ^ b + 2 ^ b * (v / 2 ^ c)).
  { intros w b c Hw Hb ->. rewrite Z.pow_add_r, <- Z.div_div by lia. rewrite Z.add_comm. apply Z.div_mod. lia. }
  pose proof (D 0 26 26 ltac:(lia) ltac:(lia) eq_refl) as D0.
  pose proof (D 26 25 51 ltac:(lia) ltac:(lia) eq_refl) as D1.
  pose proof (D 51 26 77 ltac:(lia) ltac:(lia) eq_refl) as D2.
  pose proof (D 77 25 102 ltac:(lia) ltac:(lia) eq_refl) as D3.
  pose proof (D 102 26 128 ltac:(lia) ltac:(lia) eq_refl) as D4.
  pose proof (D 128 25 153 ltac:(lia) ltac:(lia) eq_refl) as D5.
  pose proof (D 153 26 179 ltac:(lia) ltac:(lia) eq_refl) as D6.
  pose proof (D 179 25 204 ltac:(lia) ltac:(lia) eq_refl) as D7.
  pose proof (D 204 26 230 ltac:(lia) ltac:(lia) eq_refl) as D8.
  pose proof (D 230 25 255 ltac:(lia) ltac:(lia) eq_refl) as D9.
  rewrite (Z.div_small v (2 ^ 255)) in D9 by lia.
  rewrite Z.pow_0_r, Z.div_1_r in D0.
  lia.
Qed.

Lemma bits_bound (x: int) k : 0 <= k < 32 ->
  (forall i, k <= i < 32 -> Int.testbit x i = false) -> Int.unsigned x < 2 ^ k.
Proof.
  intros Hk H.
  assert (E: x = Int.zero_ext k x).
  { apply Int.same_bits_eq. intros i Hi. rewrite Int.bits_zero_ext by lia.
    destruct (zlt i k); [reflexivity|]. apply H. change Int.zwordsize with 32 in Hi. lia. }
  rewrite E. pose proof (Int.zero_ext_range k x ltac:(change Int.zwordsize with 32; lia)) as R.
  rewrite two_p_equiv in R. lia.
Qed.

Lemma frombytes_tight s : bounded tight (fe_frombytes_m s).
Proof.
  unfold fe_frombytes_m, le32_at, le32_of, bounded, tight.
  repeat (apply Forall2_cons;
    [ match goal with |- Int.unsigned ?x <= ?t =>
        first [ assert (Int.unsigned x < 2 ^ 25) as B by
                  (apply bits_bound; [lia|]; intros i Hi; case_bits 32 i; try lia; bfinish Hi)
              | assert (Int.unsigned x < 2 ^ 26) as B by
                  (apply bits_bound; [lia|]; intros i Hi; case_bits 32 i; try lia; bfinish Hi) ];
        lia
      end |]).
  constructor.
Qed.
