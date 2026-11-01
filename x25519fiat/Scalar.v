(* The scalar bits read by the ladder: ladder_bit e pos is bit pos of the little-endian integer of e.
   VST-side file: no fiat-crypto here. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.x25519.x25519_model.

Local Open Scope Z_scope.

Fixpoint le_val_n (n: nat) (e: list byte) : Z :=
  match n with
  | O => 0
  | S n' => Z.lor (le_val_n n' e) (Z.shiftl (Byte.unsigned (Znth (Z.of_nat n') e)) (8 * Z.of_nat n'))
  end.

(* the little-endian integer of the 32 bytes of e *)
Definition scalar_of (e: list byte) : Z := le_val_n 32 e.

Lemma byte_bits_high (b: byte) k : 8 <= k -> Z.testbit (Byte.unsigned b) k = false.
Proof. intros. apply Byte.bits_above. change Byte.zwordsize with 8. lia. Qed.

Lemma testbit_le_val_n n e pos : 0 <= pos ->
  Z.testbit (le_val_n n e) pos =
    if zlt pos (8 * Z.of_nat n) then Z.testbit (Byte.unsigned (Znth (pos / 8) e)) (pos mod 8) else false.
Proof.
  intros Hp. induction n as [|n IH].
  - simpl. destruct (zlt pos 0); [lia|]. apply Z.testbit_0_l.
  - cbn [le_val_n]. rewrite Z.lor_spec, IH. rewrite Z.shiftl_spec by lia. rewrite Nat2Z.inj_succ.
    destruct (zlt pos (8 * Z.of_nat n)) as [L|L].
    + destruct (zlt pos (8 * Z.succ (Z.of_nat n))); [|lia].
      rewrite (Z.testbit_neg_r _ (pos - 8 * Z.of_nat n)) by lia. apply Bool.orb_false_r.
    + cbn [orb].
      destruct (zlt pos (8 * Z.succ (Z.of_nat n))) as [L2|L2].
      * assert (E: pos / 8 = Z.of_nat n) by (symmetry; apply Z.div_unique with (pos - 8 * Z.of_nat n); lia).
        rewrite E. f_equal. rewrite Z.mod_eq by lia. rewrite E. lia.
      * apply byte_bits_high. lia.
Qed.

Lemma testbit_scalar_of e pos : 0 <= pos < 256 ->
  Z.testbit (scalar_of e) pos = Z.testbit (Byte.unsigned (Znth (pos / 8) e)) (pos mod 8).
Proof.
  intros. unfold scalar_of. rewrite testbit_le_val_n by lia.
  destruct (zlt pos (8 * Z.of_nat 32)); [reflexivity | simpl in *; lia].
Qed.

Lemma ladder_bit_spec e pos : 0 <= pos < 256 ->
  ladder_bit e pos = if Z.testbit (scalar_of e) pos then Int.one else Int.zero.
Proof.
  intros Hp. rewrite testbit_scalar_of by assumption. unfold ladder_bit.
  set (b := Byte.unsigned (Znth (pos / 8) e)).
  assert (Hb: 0 <= b < 256) by (pose proof (Byte.unsigned_range (Znth (pos / 8) e)); unfold b; rep_lia).
  assert (K: Int.and (Int.repr pos) (Int.repr 7) = Int.repr (pos mod 8)).
  { unfold Int.and. rewrite !Int.unsigned_repr by rep_lia.
    change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. }
  rewrite K.
  assert (M: 0 <= pos mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  apply Int.same_bits_eq. intros i Hi. change Int.zwordsize with 32 in Hi.
  rewrite Int.bits_and by (change Int.zwordsize with 32; lia).
  rewrite Int.bits_one.
  destruct (zeq i 0) as [->|N].
  - cbn [andb]. rewrite Int.bits_shr by (change Int.zwordsize with 32; lia).
    rewrite (Int.unsigned_repr (pos mod 8)) by rep_lia.
    destruct (zlt (0 + pos mod 8) Int.zwordsize) as [_|C]; [|change Int.zwordsize with 32 in C; lia].
    rewrite Int.testbit_repr by (change Int.zwordsize with 32; lia). rewrite Z.add_0_l.
    destruct (Z.testbit b (pos mod 8)); reflexivity.
  - cbn [andb]. destruct (Z.testbit b (pos mod 8)).
    + rewrite Int.bits_one. destruct (zeq i 0); [lia | reflexivity].
    + rewrite Int.bits_zero. reflexivity.
Qed.
