(* ref_poly1305 (harness/common.h) computes aead_model.v's poly1305_tag, over the TweetNaCl model
   hrp1305_math3.v.  The three steps of ref_poly1305's proof:
   - the loop over the full blocks: invariant hrp_inv h /\ hrp_val h mod p = p1305_acc r 0 msg[0..pos)
     (pos a multiple of 16), initially h = hrp_zero17, pos = 0;
   - the last partial block (1..15 bytes): c = the bytes, then 1, then zeros (hp_last_c);
   - rp_final. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.aead.aead_model.
Require Import WgNoise.proof.harness.hrp1305_math3.
Require Import WgNoise.proof.harness.prim_poly1305.hp1305_refmath3_pf.

Local Open Scope Z_scope.

(* ref_poly1305's c for the last 1..15 bytes rest: c[j] = rest[j], c[|rest|] = 1, zeros up to c[16] *)
Definition hp_last_c (rest: list byte) : list int :=
  map hrp_u8 rest ++ [Int.one] ++ Zrepeat Int.zero (16 - Zlength rest).

(* ---------------------------------------------------------------------- *)
(* helpers                                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma hp_sublist_short {A} (l: list A) : Zlength l <= 16 -> sublist 0 16 l = l.
Proof.
  intros H. rewrite sublist_firstn. apply firstn_all2. rewrite Zlength_correct in H. lia.
Qed.

(* the blocks of a ++ b, |a| a multiple of 16, b one block of 1..16 bytes *)
Lemma hp_blocks_app (a b: list byte) :
  Zlength a mod 16 = 0 -> 0 < Zlength b <= 16 ->
  p1305_blocks (a ++ b) = p1305_blocks a ++ [b].
Proof.
  intros Ha Hb. unfold p1305_blocks. rewrite Zlength_app.
  set (n := Zlength a / 16).
  assert (Hn : Zlength a = 16 * n) by (pose proof (Z.div_mod (Zlength a) 16); lia).
  assert (Hn0 : 0 <= n) by (pose proof (Zlength_nonneg a); lia).
  replace ((Zlength a + Zlength b + 15) / 16) with (n + 1)
    by (rewrite Hn; replace (16 * n + Zlength b + 15) with ((Zlength b + 15) + n * 16) by lia;
        rewrite Z.div_add by lia; assert ((Zlength b + 15) / 16 = 1) by (symmetry; apply Z.div_unique with (Zlength b - 1); lia); lia).
  replace ((Zlength a + 15) / 16) with n
    by (rewrite Hn; replace (16 * n + 15) with (15 + n * 16) by lia; rewrite Z.div_add by lia; reflexivity).
  rewrite Z2Nat.inj_add by lia. rewrite seq_app, !map_app. simpl.
  rewrite Z2Nat.id by lia. f_equal.
  - apply map_ext_in. intros i Hi. apply in_map_iff in Hi. destruct Hi as [k [Hk Hin]]. subst i.
    apply in_seq in Hin. rewrite sublist_app1; auto; rep_lia.
  - f_equal. rewrite sublist_app2 by lia. rewrite Hn.
    replace (16 * n - 16 * n) with 0 by lia. replace (16 * n + 16 - 16 * n) with 16 by lia.
    apply hp_sublist_short; lia.
Qed.

Lemma hp_acc_app r a b :
  Zlength a mod 16 = 0 -> 0 < Zlength b <= 16 ->
  p1305_acc r 0 (a ++ b) = p1305_step r (p1305_acc r 0 a) b.
Proof.
  intros Ha Hb. unfold p1305_acc. rewrite hp_blocks_app by auto. rewrite fold_left_app. reflexivity.
Qed.

(* one step of the reference model from the TweetNaCl invariant *)
Lemma hp_step key h c blk :
  16 <= Zlength key -> hrp_inv h -> hrp_cblock c ->
  hrp_val c = le_Z blk + 2 ^ (8 * Zlength blk) ->
  hrp_inv (hrp_mul (hrp_init_r key) h c) /\
  hrp_val (hrp_mul (hrp_init_r key) h c) mod p1305_p = p1305_step (p1305_r key) (hrp_val h mod p1305_p) blk.
Proof.
  intros Hk Hh Hc Hv. destruct (hpf_mul_ok key h c Hk Hh Hc) as [H1 H2]. split; auto.
  rewrite H2, Hv. unfold p1305_step.
  assert (Hm : forall x y z, (x mod p1305_p + y) * z mod p1305_p = (x + y) * z mod p1305_p).
  { intros x y z. rewrite <- (Z.mul_mod_idemp_l (x mod p1305_p + y)) by (unfold p1305_p; lia).
    rewrite Z.add_mod_idemp_l by (unfold p1305_p; lia).
    rewrite Z.mul_mod_idemp_l by (unfold p1305_p; lia). reflexivity. }
  rewrite <- Z.add_assoc, Hm. reflexivity.
Qed.

Lemma hp_val_app a b : hrp_val (a ++ b) = hrp_val a + 256 ^ Zlength a * hrp_val b.
Proof.
  induction a as [|w t IH]; simpl.
  - lia.
  - rewrite Zlength_cons, IH, Z.pow_succ_r by (apply Zlength_nonneg). lia.
Qed.

Lemma hp_val_u8 l : hrp_val (map hrp_u8 l) = le_Z l.
Proof.
  induction l as [|b t IH]; simpl; auto. rewrite IH. unfold hrp_u8.
  rewrite Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma hp_val_zeros n : hrp_val (Zrepeat Int.zero n) = 0.
Proof.
  unfold Zrepeat. induction (Z.to_nat n); simpl; auto. rewrite IHn0. reflexivity.
Qed.

Lemma hp_last_c_ok rest : 0 < Zlength rest < 16 ->
  hrp_cblock (hp_last_c rest) /\ hrp_val (hp_last_c rest) = le_Z rest + 2 ^ (8 * Zlength rest).
Proof.
  intros Hr. unfold hp_last_c. split.
  - assert (HF : Forall (fun w => Int.unsigned w <= 255)
                   (map hrp_u8 rest ++ [Int.one] ++ Zrepeat Int.zero (16 - Zlength rest))).
    { apply Forall_app. split; [|apply Forall_app; split].
      - apply Forall_map. apply Forall_forall. intros b _. unfold hrp_u8. cbv beta. simpl.
        rewrite Int.unsigned_repr by rep_lia. rep_lia.
      - repeat constructor. rewrite Int.unsigned_one. lia.
      - apply Forall_forall. intros x Hx. unfold Zrepeat in Hx. apply repeat_spec in Hx. subst x. rewrite Int.unsigned_zero. lia. }
    assert (HL : Zlength (map hrp_u8 rest ++ [Int.one] ++ Zrepeat Int.zero (16 - Zlength rest)) = 17).
    { rewrite !Zlength_app, Zlength_map, Zlength_Zrepeat by lia. simpl. rewrite Zlength_cons, Zlength_nil. lia. }
    split; [auto | split].
    + intros j Hj. rewrite Forall_Znth in HF. apply HF. lia.
    + rewrite app_assoc. rewrite Znth_app2 by (rewrite Zlength_app, Zlength_map; simpl; rewrite Zlength_cons, Zlength_nil; lia).
      rewrite Zlength_app, Zlength_map, Zlength_cons, Zlength_nil.
      rewrite Znth_Zrepeat by lia. rewrite Int.unsigned_zero. lia.
  - rewrite hp_val_app, hp_val_u8, Zlength_map. simpl. rewrite hp_val_zeros, Int.unsigned_one.
    rewrite Z.pow_mul_r by lia. change (2 ^ 8) with 256. lia.
Qed.

(* one full block at pos *)
Lemma hp_acc_block key msg pos h :
  Zlength key = 32 -> 0 <= pos -> pos mod 16 = 0 -> pos + 16 <= Zlength msg ->
  hrp_inv h -> hrp_val h mod p1305_p = p1305_acc (p1305_r key) 0 (sublist 0 pos msg) ->
  hrp_inv (hrp_block (hrp_init_r key) h (sublist pos (pos + 16) msg)) /\
  hrp_val (hrp_block (hrp_init_r key) h (sublist pos (pos + 16) msg)) mod p1305_p =
    p1305_acc (p1305_r key) 0 (sublist 0 (pos + 16) msg).
Proof.
  intros Hk Hp Hm Hl Hh Hv.
  assert (Hs : sublist 0 (pos + 16) msg = sublist 0 pos msg ++ sublist pos (pos + 16) msg)
    by (rewrite <- sublist_split; auto; lia).
  assert (Hb : Zlength (sublist pos (pos + 16) msg) = 16) by (rewrite Zlength_sublist; lia).
  destruct (hpf_block_c_ok _ Hb) as [Hc Hcv].
  unfold hrp_block. rewrite Hs, hp_acc_app, <- Hv.
  - apply hp_step; auto; try lia. rewrite Hcv, Hb. reflexivity.
  - rewrite Zlength_sublist by lia. rewrite Z.sub_0_r. auto.
  - lia.
Qed.

(* the last partial block *)
Lemma hp_acc_last key msg pos h :
  Zlength key = 32 -> 0 <= pos -> pos mod 16 = 0 -> pos < Zlength msg < pos + 16 ->
  hrp_inv h -> hrp_val h mod p1305_p = p1305_acc (p1305_r key) 0 (sublist 0 pos msg) ->
  hrp_inv (hrp_mul (hrp_init_r key) h (hp_last_c (sublist pos (Zlength msg) msg))) /\
  hrp_val (hrp_mul (hrp_init_r key) h (hp_last_c (sublist pos (Zlength msg) msg))) mod p1305_p =
    p1305_acc (p1305_r key) 0 msg.
Proof.
  intros Hk Hp Hm Hl Hh Hv.
  assert (Hs : msg = sublist 0 pos msg ++ sublist pos (Zlength msg) msg)
    by (rewrite <- sublist_split, sublist_same; auto; lia).
  assert (Hb : Zlength (sublist pos (Zlength msg) msg) = Zlength msg - pos) by (rewrite Zlength_sublist; lia).
  destruct (hp_last_c_ok (sublist pos (Zlength msg) msg)) as [Hc Hcv]; [lia|].
  replace (p1305_acc (p1305_r key) 0 msg)
    with (p1305_acc (p1305_r key) 0 (sublist 0 pos msg ++ sublist pos (Zlength msg) msg))
    by (rewrite <- Hs; reflexivity).
  rewrite hp_acc_app, <- Hv.
  - apply hp_step; auto; lia.
  - rewrite Zlength_sublist by lia. rewrite Z.sub_0_r. auto.
  - lia.
Qed.

(* rp_final gives the tag *)
Lemma hp_tag key msg h :
  Zlength key = 32 -> hrp_inv h -> hrp_val h mod p1305_p = p1305_acc (p1305_r key) 0 msg ->
  hrp_final_out h (hrp_init_s key) = poly1305_tag key msg.
Proof.
  intros Hk Hh Hv. unfold hrp_init_s. rewrite hpf_final_ok; auto.
  - rewrite Hv. reflexivity.
  - rewrite Zlength_sublist; lia.
Qed.
