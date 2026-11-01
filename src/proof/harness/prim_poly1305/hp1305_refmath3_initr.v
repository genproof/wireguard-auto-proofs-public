(* proven copy of hrp1305_math3.v's hrp_init_r_ok.
   hrp_init_r key = the 16 bytes of key[0..16) as u32 limbs, clamped by hrp_mask at limbs 3,7,11,15 (& 15)
   and 4,8,12 (& 252), limb 16 = 0; its value sum limb_j 256^j is aead_model's p1305_r key, the Z.land of
   le_Z key[0..16) with 0x0ffffffc0ffffffc0ffffffc0fffffff. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.aead.aead_model.
Require Import WgNoise.proof.harness.hrp1305_math3.

Local Open Scope Z_scope.

Lemma hpf_land_split a y M : 0 <= a < 256 ->
  Z.land (a + 256 * y) M = Z.land a (M mod 256) + 256 * Z.land y (M / 256).
Proof.
  intros Ha.
  rewrite (Z_div_mod_eq_full (Z.land (a + 256 * y) M) 256).
  assert (Hd : (a + 256 * y) / 256 = y).
  { rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
  assert (Hm : (a + 256 * y) mod 256 = a).
  { rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small; lia. }
  change 256 with (2 ^ 8) in *.
  rewrite <- !Z.shiftr_div_pow2 in * by lia.
  rewrite Z.shiftr_land, Hd.
  rewrite <- !Z.land_ones in * by lia.
  replace (Z.land (Z.land (a + 2 ^ 8 * y) M) (Z.ones 8)) with
    (Z.land (Z.land (a + 2 ^ 8 * y) (Z.ones 8)) (Z.land M (Z.ones 8))).
  - rewrite Hm. lia.
  - apply Z.bits_inj'; intros n Hn. rewrite !Z.land_spec.
    destruct (Z.testbit (a + 2 ^ 8 * y) n), (Z.testbit M n), (Z.testbit (Z.ones 8) n); reflexivity.
Qed.

Lemma hpf_land_range a m : 0 <= a < 256 -> 0 <= m -> 0 <= Z.land a m < 256.
Proof.
  intros Ha Hm.
  replace a with (Z.land a (Z.ones 8)) by (rewrite Z.land_ones by lia; apply Z.mod_small; simpl; lia).
  rewrite <- Z.land_assoc, (Z.land_comm (Z.ones 8)), Z.land_assoc, Z.land_ones by lia.
  apply Z.mod_pos_bound. simpl; lia.
Qed.

Lemma hpf_u8_unsigned b : Int.unsigned (hrp_u8 b) = Byte.unsigned b.
Proof.
  unfold hrp_u8. pose proof (Byte.unsigned_range_2 b).
  rewrite Int.unsigned_repr; auto. rep_lia.
Qed.

Lemma hpf_and_unsigned b m : 0 <= m <= 255 ->
  Int.unsigned (Int.and (hrp_u8 b) (Int.repr m)) = Z.land (Byte.unsigned b) m.
Proof.
  intros Hm. unfold Int.and. rewrite hpf_u8_unsigned, (Int.unsigned_repr m) by rep_lia.
  pose proof (Byte.unsigned_range_2 b).
  pose proof (hpf_land_range (Byte.unsigned b) m ltac:(rep_lia) ltac:(lia)).
  rewrite Int.unsigned_repr; rep_lia.
Qed.

Lemma hpf_mask_unf j m r : hrp_mask j m r = upd_Znth j r (Int.and (Znth j r) (Int.repr m)).
Proof. reflexivity. Qed.

Lemma hpf_land255 b : Z.land (Byte.unsigned b) 255 = Byte.unsigned b.
Proof.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  apply Z.mod_small. pose proof (Byte.unsigned_range_2 b). simpl; rep_lia.
Qed.

Lemma hpf_init_r_ok key : 16 <= Zlength key ->
  Zlength (hrp_init_r key) = 17 /\ Forall (fun w => Int.unsigned w <= 255) (hrp_init_r key) /\
  hrp_val (hrp_init_r key) = p1305_r key.
Proof.
  intros Hk. unfold hrp_init_r, p1305_r.
  assert (Hl : Zlength (sublist 0 16 key) = 16) by list_solve.
  generalize dependent (sublist 0 16 key). intros k Hl.
  do 16 (destruct k as [|? k]; [rewrite ?Zlength_cons, ?Zlength_nil in Hl; lia |]).
  destruct k; [| rewrite !Zlength_cons in Hl; pose proof (Zlength_nonneg k); lia].
  cbn [map app].
  repeat (match goal with |- context [hrp_mask ?j ?m ?r] =>
            lazymatch r with context [hrp_mask] => fail | _ => rewrite (hpf_mask_unf j m r) end end;
          repeat (first [ rewrite upd_Znth0 | rewrite Znth_0_cons | rewrite upd_Znth_cons by lia
                        | rewrite Znth_pos_cons by lia ];
                  cbn [Z.sub Z.add Z.opp Z.pos_sub Pos.pred_double Z.double Z.pred_double Z.succ_double])).
  split; [reflexivity |]. split.
  - repeat constructor; rewrite ?hpf_u8_unsigned, ?hpf_and_unsigned by lia;
      try match goal with |- context [Byte.unsigned ?b] => pose proof (Byte.unsigned_range_2 b) end;
      try match goal with |- Z.land (Byte.unsigned ?b) ?m <= _ =>
        pose proof (hpf_land_range (Byte.unsigned b) m ltac:(rep_lia) ltac:(lia)) end;
      try rewrite Int.unsigned_zero; rep_lia.
  - cbn [hrp_val le_Z].
    repeat (rewrite hpf_land_split by rep_lia;
      repeat match goal with
      | |- context [?M mod 256] => let v := eval vm_compute in (M mod 256) in change (M mod 256) with v
      | |- context [?M / 256] => let v := eval vm_compute in (M / 256) in change (M / 256) with v
      end).
    rewrite !hpf_u8_unsigned, !hpf_and_unsigned, Int.unsigned_zero, !hpf_land255, Z.land_0_l by lia.
    lia.
Qed.
