(* the math of ref_poly1305's body, proven (no unproved dependency):
   - hpr_final_ok: a proven copy of hrp1305_math3.v's hrp_final_ok (rp_final: h mod p + s mod 2^128);
   - hpr_acc_block, hpr_acc_last, hpr_tag: proven copies of hp1305_refmath3.v's hp_acc_block, hp_acc_last,
     hp_tag, over the proven hpf_ lemmas of hp1305_ref_pf3.v. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.aead.aead_model.
Require Import WgNoise.proof.harness.hrp1305_math3.
Require Import WgNoise.proof.harness.prim_poly1305.hp1305_refmath3.
Require Import WgNoise.proof.harness.prim_poly1305.hp1305_ref_pf3.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* rp_final                                                                *)
(* ---------------------------------------------------------------------- *)

Lemma hpr_le_bytes_val l : (forall j, 0 <= j < Zlength l -> Int.unsigned (Znth j l) <= 255) ->
  map (fun w => Byte.repr (Int.unsigned w)) l = le_bytes (length l) (hrp_val l).
Proof.
  induction l as [|w t IH]; intros H; cbn [map length le_bytes hrp_val]; auto.
  assert (Hw: Int.unsigned w <= 255).
  { specialize (H 0). rewrite Znth_0_cons in H. apply H. rewrite Zlength_cons. pose proof (Zlength_nonneg t). lia. }
  assert (Ht: forall j, 0 <= j < Zlength t -> Int.unsigned (Znth j t) <= 255).
  { intros j Hj. specialize (H (j + 1)). rewrite Znth_pos_cons in H by lia.
    replace (j + 1 - 1) with j in H by lia. apply H. rewrite Zlength_cons. lia. }
  f_equal.
  - apply Byte.eqm_samerepr. exists (- hrp_val t). change Byte.modulus with 256. lia.
  - rewrite IH by auto. f_equal. pose proof (Int.unsigned_range w).
    rewrite Z.mul_comm, Z.div_add, Z.div_small by lia. lia.
Qed.

Lemma hpr_select_zero g h1 n : 0 <= n -> hrp_loop (hrp_select_step Int.zero g) n h1 = h1.
Proof.
  intros Hn. pattern n. apply natlike_ind; [reflexivity | | exact Hn].
  intros k Hk IH. rewrite <- Z.add_1_r, hrp_loop_succ, IH by lia. unfold hrp_select_step.
  rewrite Int.and_zero_l, Int.xor_zero.
  destruct (zlt k (Zlength h1)); [| rewrite upd_Znth_out_of_range by lia; reflexivity].
  destruct (zlt k 0); [lia |]. apply upd_Znth_triv; auto; lia.
Qed.

Lemma hpr_select_mone g h1 n : Zlength g = 17 -> Zlength h1 = 17 -> 0 <= n <= 17 ->
  hrp_loop (hrp_select_step Int.mone g) n h1 = sublist 0 n g ++ sublist n 17 h1.
Proof.
  intros Hg Hh [Hn Hn']. revert Hn'. pattern n. apply natlike_ind; [| | exact Hn].
  - intros _. rewrite hrp_loop_0. rewrite sublist_nil, sublist_same by lia. reflexivity.
  - intros k Hk IH Hk'. rewrite <- Z.add_1_r, hrp_loop_succ, IH by lia. unfold hrp_select_step.
    rewrite Int.and_mone_l.
    assert (E: forall a b, Int.xor a (Int.xor b a) = b).
    { intros a b. rewrite (Int.xor_commut b a), <- Int.xor_assoc, Int.xor_idem, Int.xor_zero_l. reflexivity. }
    rewrite Znth_app2 by (rewrite Zlength_sublist; lia). rewrite Zlength_sublist by lia.
    replace (k - (k - 0)) with 0 by lia. rewrite Znth_sublist by lia. replace (0 + k) with k by lia.
    rewrite E. list_solve.
Qed.

Lemma hpr_minusp_ok :
  Zlength hrp_minusp = 17 /\ (forall j, 0 <= j < 17 -> Int.unsigned (Znth j hrp_minusp) <= 255) /\
  hrp_val hrp_minusp = 5 + 252 * 2 ^ 128.
Proof.
  split; [reflexivity | split; [| vm_compute; reflexivity]].
  assert (HF: Forall (fun w => Int.unsigned w <= 255) hrp_minusp) by (vm_compute; repeat constructor; discriminate).
  intros j Hj. rewrite Forall_Znth in HF. apply HF. change (Zlength hrp_minusp) with 17. lia.
Qed.

Lemma hpr_int_of_unsigned x z : Int.unsigned x = z -> x = Int.repr z.
Proof. intros H. rewrite <- H, Int.repr_unsigned. reflexivity. Qed.

Lemma hpr_final_ok h sk : hrp_inv h -> Zlength sk = 16 ->
  hrp_final_out h sk = le_bytes 16 ((hrp_val h mod p1305_p + le_Z sk) mod 2 ^ 128).
Proof.
  intros [Hh [Bh B16]] Hsk.
  assert (Bh17: forall j, 0 <= j < 17 -> Int.unsigned (Znth j h) <= 255).
  { intros j Hj. destruct (zlt j 16); [apply Bh; lia | replace j with 16 by lia; lia]. }
  set (V := hrp_val h).
  assert (HV: 0 <= V <= 5 * 2 ^ 128 - 1).
  { unfold V. rewrite hpf_val_split by auto. pose proof (hpf_val_low h Hh Bh).
    pose proof (Int.unsigned_range (Znth 16 h)). lia. }
  assert (Pp: p1305_p = 2 ^ 130 - 5) by reflexivity.
  destruct hpr_minusp_ok as (Lm & Bm & Vm).
  destruct (hpf_add_ok h hrp_minusp Hh Lm Bh17 Bm) as (L1 & B1 & u & Hu & V1).
  set (h1 := hrp_add h hrp_minusp) in *.
  assert (R1: 0 <= hrp_val h1 <= 2 ^ 136 - 1).
  { pose proof (hpf_val_range h1) as R. rewrite L1 in R. apply R. intros j Hj. apply B1. lia. }
  assert (S1: hrp_val h1 = hrp_val (sublist 0 16 h1) + 2 ^ 128 * Int.unsigned (Znth 16 h1))
    by (apply hpf_val_split; auto).
  assert (Lo1: 0 <= hrp_val (sublist 0 16 h1) <= 2 ^ 128 - 1) by (apply hpf_val_low; auto; intros; apply B1; lia).
  assert (B116: Int.unsigned (Znth 16 h1) <= 255) by (apply B1; lia).
  (* the select: h if V < p, else h1 = h - p *)
  assert (Hsel: exists h2, hrp_loop (hrp_select_step (Int.neg (Int.shru (Znth 16 h1) (Int.repr 7))) h) 17 h1 = h2 /\
            Zlength h2 = 17 /\ (forall j, 0 <= j < 17 -> Int.unsigned (Znth j h2) <= 255) /\
            hrp_val h2 = V mod p1305_p).
  { destruct (zlt V p1305_p) as [Hlt | Hge].
    - assert (u = 0) by (rewrite Vm in V1; fold V in V1; rewrite Pp in Hlt; nia). subst u.
      assert (E16: Int.unsigned (Znth 16 h1) / 2 ^ 7 = 1).
      { rewrite Vm in V1; fold V in V1. change (2 ^ 7) with 128.
        enough (252 <= Int.unsigned (Znth 16 h1))
          by (symmetry; apply Z.div_unique with (r := Int.unsigned (Znth 16 h1) - 128); lia).
        rewrite Pp in Hlt. nia. }
      replace (Int.shru (Znth 16 h1) (Int.repr 7)) with Int.one
        by (symmetry; apply hpr_int_of_unsigned; rewrite hpf_shru by lia; exact E16).
      change (Int.neg Int.one) with Int.mone.
      exists h. split; [| split; [auto | split; [auto |]]].
      + rewrite hpr_select_mone by (auto; lia). rewrite sublist_same by auto. rewrite sublist_nil, app_nil_r. reflexivity.
      + rewrite Z.mod_small; lia.
    - assert (u = 1) by (rewrite Vm in V1; fold V in V1; rewrite Pp in Hge; nia). subst u.
      assert (E16: Int.unsigned (Znth 16 h1) / 2 ^ 7 = 0).
      { rewrite Vm in V1; fold V in V1. apply Z.div_small. split; [apply Int.unsigned_range |].
        rewrite Pp in Hge. nia. }
      replace (Int.shru (Znth 16 h1) (Int.repr 7)) with Int.zero
        by (symmetry; apply hpr_int_of_unsigned; rewrite hpf_shru by lia; exact E16).
      change (Int.neg Int.zero) with Int.zero.
      exists h1. split; [apply hpr_select_zero; lia | split; [auto | split; [auto |]]].
      rewrite Vm in V1; fold V in V1.
      rewrite <- (Z.mod_unique V p1305_p 1 (V - p1305_p)); rewrite ?Pp in *; lia. }
  destruct Hsel as (h2 & E2 & L2 & B2 & V2).
  (* adding s *)
  set (c := map hrp_u8 sk ++ [Int.zero]).
  assert (Lc: Zlength c = 17) by (unfold c; rewrite Zlength_app, Zlength_map, Hsk; reflexivity).
  assert (Bc: forall j, 0 <= j < 17 -> Int.unsigned (Znth j c) <= 255).
  { intros j Hj. unfold c. destruct (zlt j 16).
    - rewrite Znth_app1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia. unfold hrp_u8.
      rewrite Int.unsigned_repr by rep_lia. rep_lia.
    - rewrite Znth_app2 by (rewrite Zlength_map; lia). rewrite Zlength_map, Hsk.
      replace (j - 16) with 0 by lia. rewrite Znth_0_cons, Int.unsigned_zero. lia. }
  assert (Vc: hrp_val c = le_Z sk).
  { unfold c. rewrite hpf_val_app, hpf_val_u8. simpl. lia. }
  destruct (hpf_add_ok h2 c L2 Lc B2 Bc) as (L3 & B3 & u3 & Hu3 & V3).
  unfold hrp_final_out, hrp_final_h. cbv zeta. fold h1. rewrite E2. fold c.
  set (res := hrp_add h2 c) in *.
  rewrite hpr_le_bytes_val.
  2: { intros j Hj. rewrite Zlength_sublist in Hj by lia. rewrite Znth_sublist by lia. apply B3. lia. }
  replace (length (sublist 0 16 res)) with 16%nat
    by (rewrite <- ZtoNat_Zlength, Zlength_sublist by lia; reflexivity).
  f_equal.
  assert (S3: hrp_val res = hrp_val (sublist 0 16 res) + 2 ^ 128 * Int.unsigned (Znth 16 res))
    by (apply hpf_val_split; auto).
  assert (Lo3: 0 <= hrp_val (sublist 0 16 res) <= 2 ^ 128 - 1) by (apply hpf_val_low; auto; intros; apply B3; lia).
  rewrite <- V2, <- Vc, <- V3, S3.
  apply Z.mod_unique with (Int.unsigned (Znth 16 res) + 256 * u3); [lia |].
  generalize (hrp_val (sublist 0 16 res)) (Int.unsigned (Znth 16 res)) u3. intros A B C. clear.
  assert (E: 2 ^ 136 = 2 ^ 128 * 256) by reflexivity. rewrite E. generalize (2 ^ 128). intros P. ring.
Qed.

(* ---------------------------------------------------------------------- *)
(* ref_poly1305 = poly1305_tag *)
(* ---------------------------------------------------------------------- *)

Lemma hpr_sublist_short {A} (l: list A) : Zlength l <= 16 -> sublist 0 16 l = l.
Proof.
  intros H. rewrite sublist_firstn. apply firstn_all2. rewrite Zlength_correct in H. lia.
Qed.

Lemma hpr_blocks_app (a b: list byte) :
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
    apply hpr_sublist_short; lia.
Qed.

Lemma hpr_acc_app r a b :
  Zlength a mod 16 = 0 -> 0 < Zlength b <= 16 ->
  p1305_acc r 0 (a ++ b) = p1305_step r (p1305_acc r 0 a) b.
Proof.
  intros Ha Hb. unfold p1305_acc. rewrite hpr_blocks_app by auto. rewrite fold_left_app. reflexivity.
Qed.

Lemma hpr_step key h c blk :
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

Lemma hpr_val_zeros n : hrp_val (Zrepeat Int.zero n) = 0.
Proof.
  unfold Zrepeat. induction (Z.to_nat n); simpl; auto. rewrite IHn0. reflexivity.
Qed.

Lemma hpr_last_c_ok rest : 0 < Zlength rest < 16 ->
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
  - rewrite hpf_val_app, hpf_val_u8, Zlength_map. simpl. rewrite hpr_val_zeros, Int.unsigned_one.
    rewrite Z.pow_mul_r by lia. change (2 ^ 8) with 256. lia.
Qed.

(* one full block at pos *)
Lemma hpr_acc_block key msg pos h :
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
  unfold hrp_block. rewrite Hs, hpr_acc_app, <- Hv.
  - apply hpr_step; auto; try lia. rewrite Hcv, Hb. reflexivity.
  - rewrite Zlength_sublist by lia. rewrite Z.sub_0_r. auto.
  - lia.
Qed.

(* the last partial block *)
Lemma hpr_acc_last key msg pos h :
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
  destruct (hpr_last_c_ok (sublist pos (Zlength msg) msg)) as [Hc Hcv]; [lia|].
  replace (p1305_acc (p1305_r key) 0 msg)
    with (p1305_acc (p1305_r key) 0 (sublist 0 pos msg ++ sublist pos (Zlength msg) msg))
    by (rewrite <- Hs; reflexivity).
  rewrite hpr_acc_app, <- Hv.
  - apply hpr_step; auto; lia.
  - rewrite Zlength_sublist by lia. rewrite Z.sub_0_r. auto.
  - lia.
Qed.

(* rp_final gives the tag *)
Lemma hpr_tag key msg h :
  Zlength key = 32 -> hrp_inv h -> hrp_val h mod p1305_p = p1305_acc (p1305_r key) 0 msg ->
  hrp_final_out h (hrp_init_s key) = poly1305_tag key msg.
Proof.
  intros Hk Hh Hv. unfold hrp_init_s. rewrite hpr_final_ok; auto.
  - rewrite Hv. reflexivity.
  - rewrite Zlength_sublist; lia.
Qed.
