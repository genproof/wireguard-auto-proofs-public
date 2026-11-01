(* law prim_aead: the model facts the harness piece needs: the references of
   common.h compute aead_model.v's functions.
   The facts of hrp1305_math3.v are used through the hypothesis haead_hrp_facts
   (haead_defs3.v), never through the lemmas of hrp1305_math3.v themselves. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Export WgNoise.proof.harness.prim_aead.haead_lemmas3.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* the block counter                                                       *)
(* ---------------------------------------------------------------------- *)

(* helpers *)
Lemma hm3_byte_bit y j : 0 <= j < 32 ->
  Int.testbit (Int.repr (Byte.unsigned (Byte.repr y))) j = if zlt j 8 then Z.testbit y j else false.
Proof.
  intros Hj. rewrite Int.testbit_repr by (unfold Int.zwordsize; simpl; lia).
  rewrite Byte.unsigned_repr_eq. change Byte.modulus with (2 ^ 8).
  destruct (zlt j 8); [rewrite Z.mod_pow2_bits_low by lia | rewrite Z.mod_pow2_bits_high by lia]; auto.
Qed.

Lemma hm3_le32_of x :
  le32_of (Byte.repr x) (Byte.repr (Z.shiftr x 8)) (Byte.repr (Z.shiftr x 16)) (Byte.repr (Z.shiftr x 24)) =
  Int.repr x.
Proof.
  apply Int.same_bits_eq. intros i Hi. unfold Int.zwordsize in Hi; simpl in Hi.
  unfold le32_of. rewrite !Int.bits_or by (unfold Int.zwordsize; simpl; lia).
  rewrite !Int.bits_shl by (unfold Int.zwordsize; simpl; lia).
  change (Int.unsigned (Int.repr 8)) with 8. change (Int.unsigned (Int.repr 16)) with 16.
  change (Int.unsigned (Int.repr 24)) with 24.
  rewrite (hm3_byte_bit x i) by lia. rewrite (Int.testbit_repr x i) by (unfold Int.zwordsize; simpl; lia).
  destruct (zlt i 8); destruct (zlt i 16); destruct (zlt i 24); try lia;
  rewrite ?hm3_byte_bit by lia; rewrite ?Z.shiftr_spec by lia;
  repeat (destruct (zlt _ _)); simpl; rewrite ?orb_false_r, ?orb_false_l; try lia;
  f_equal; lia.
Qed.

Lemma hm3_le32_of_div x :
  le32_of (Byte.repr x) (Byte.repr (x / 256)) (Byte.repr (x / 256 / 256)) (Byte.repr (x / 256 / 256 / 256)) =
  Int.repr x.
Proof.
  rewrite <- hm3_le32_of. rewrite !Z.shiftr_div_pow2 by lia. rewrite !Z.div_div by lia. reflexivity.
Qed.

Lemma hm3_le32_words_length n bs : Zlength (le32_words n bs) = Z.of_nat n.
Proof. unfold le32_words. rewrite !Zlength_map, Zlength_correct, seq_length. reflexivity. Qed.

Lemma hm3_iv_words n :
  le32_at (aead_iv n) 0 = Int.zero /\ le32_at (aead_iv n) 4 = Int.zero /\
  le32_at (aead_iv n) 8 = Int.repr n /\ le32_at (aead_iv n) 12 = Int.repr (Z.shiftr n 32).
Proof.
  split; [reflexivity |]. split; [reflexivity |]. split.
  - rewrite <- hm3_le32_of_div. reflexivity.
  - replace (Z.shiftr n 32) with (n / 256 / 256 / 256 / 256)
      by (rewrite Z.shiftr_div_pow2 by lia; rewrite !Z.div_div by lia; reflexivity).
    rewrite <- hm3_le32_of_div. reflexivity.
Qed.

(* ref_chacha20_block's state: rc_setup(s, key, ctr, 0, (u32)n, (u32)(n >> 32)) *)
Lemma haead_setup_st key n ctr : Zlength key = 32 -> 0 <= n <= Int64.max_unsigned ->
  chacha_consts ++ le32_words 8 key ++ [ctr; Int.zero; Int.repr n; Int.repr (Z.shiftr n 32)] =
  chacha_advance (aead_st key n) (Int.unsigned ctr).
Proof.
  intros Hk Hn. unfold chacha_advance, aead_st, chacha_init_st.
  pose proof (hm3_le32_words_length 8 key) as HK. set (K := le32_words 8 key) in *.
  rewrite !app_assoc.
  assert (H12: Zlength (chacha_consts ++ K) = 12) by (rewrite Zlength_app, HK; reflexivity).
  rewrite Znth_app2 by lia. rewrite H12, Z.sub_diag.
  rewrite upd_Znth_app2 by (rewrite H12; simpl; lia). rewrite H12, Z.sub_diag.
  destruct (hm3_iv_words n) as (E0 & E4 & E8 & E12). rewrite E0, E4, E8, E12.
  rewrite Znth_0_cons, upd_Znth0, Int.add_zero_l, Int.repr_unsigned. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* the keystream                                                           *)
(* ---------------------------------------------------------------------- *)

Lemma hm3_upd_len {A} i (l: list A) x : Zlength (upd_Znth i l x) = Zlength l.
Proof.
  unfold upd_Znth. destruct (Sumbool.sumbool_and _ _ _ _ _ _) as [[H1 H2] | H]; auto.
  rewrite Zlength_app, Zlength_cons, !Zlength_sublist by lia. lia.
Qed.

Lemma hm3_qround_length x a b c d : Zlength (chacha_qround x a b c d) = Zlength x.
Proof. unfold chacha_qround. do 8 rewrite hm3_upd_len. reflexivity. Qed.

Lemma hm3_dround_length x : Zlength (chacha_dround x) = Zlength x.
Proof. unfold chacha_dround. do 8 rewrite hm3_qround_length. reflexivity. Qed.

Lemma hm3_rounds_length n x : Zlength (chacha_rounds n x) = Zlength x.
Proof.
  (* never let the kernel compare chacha_rounds (S n) x with chacha_rounds n (chacha_dround x) *)
  revert x; induction n as [| n IH]; intros x; [reflexivity |].
  change (Zlength ((fix rounds (n : nat) (x : list int) {struct n} : list int :=
                      match n with O => x | S k => rounds k (chacha_dround x) end) n (chacha_dround x))
          = Zlength x).
  transitivity (Zlength (chacha_dround x)).
  - exact (IH (chacha_dround x)).
  - apply hm3_dround_length.
Qed.

Lemma hm3_words_bytes_cons w ws : words_bytes (w :: ws) = le32_bytes w ++ words_bytes ws.
Proof. reflexivity. Qed.

Lemma hm3_words_bytes_length ws : Zlength (words_bytes ws) = 4 * Zlength ws.
Proof.
  induction ws as [| w ws IH]; [reflexivity |]. rewrite hm3_words_bytes_cons, Zlength_app, IH, Zlength_cons.
  change (Zlength (le32_bytes w)) with 4. lia.
Qed.

Lemma hm3_block_length n st : Zlength st = 16 -> Zlength (chacha_block_bytes n st) = 64.
Proof.
  intros H. unfold chacha_block_bytes, chacha_block_words, add_words.
  rewrite hm3_words_bytes_length, Zlength_map, Zlength_combine, hm3_rounds_length, H. reflexivity.
Qed.

Lemma hm3_stream_length n st k : Zlength st = 16 -> Zlength (chacha_stream n st k) = 64 * Z.of_nat k.
Proof.
  revert st; induction k as [| k IH]; intros st H; [reflexivity |].
  cbn [chacha_stream]. rewrite Zlength_app, hm3_block_length, IH by (auto; apply haead_advance_length; auto). lia.
Qed.

Lemma hm3_stream_Znth n st k b i : Zlength st = 16 -> 0 <= b < Z.of_nat k -> 0 <= i < 64 ->
  Znth (64 * b + i) (chacha_stream n st k) = Znth i (chacha_block_bytes n (chacha_advance st b)).
Proof.
  revert st b; induction k as [| k IH]; intros st b Hst Hb Hi; [lia |].
  cbn [chacha_stream]. destruct (Z.eq_dec b 0).
  - subst b. rewrite haead_advance_0 by auto. rewrite Znth_app1 by (rewrite hm3_block_length by auto; lia). f_equal; lia.
  - rewrite Znth_app2 by (rewrite hm3_block_length by auto; lia). rewrite hm3_block_length by auto.
    replace (64 * b + i - 64) with (64 * (b - 1) + i) by lia.
    rewrite IH by (try apply haead_advance_length; auto; lia).
    rewrite haead_advance_add by auto. f_equal. f_equal. f_equal. lia.
Qed.

Lemma hm3_Znth_combine {A B} {da: Inhabitant A} {db: Inhabitant B} (a: list A) (b: list B) i :
  0 <= i < Z.min (Zlength a) (Zlength b) -> Znth i (combine a b) = (Znth i a, Znth i b).
Proof.
  revert b i; induction a as [| x a IH]; intros [| y b] i Hi; rewrite ?Zlength_nil, ?Zlength_cons in Hi; try lia.
  simpl combine. destruct (Z.eq_dec i 0).
  - subst. rewrite !Znth_0_cons. reflexivity.
  - rewrite !Znth_pos_cons by lia. apply IH. lia.
Qed.

Lemma hm3_xor_length a b : Zlength (xor_bytes a b) = Z.min (Zlength a) (Zlength b).
Proof. unfold xor_bytes. rewrite Zlength_map, Zlength_combine. reflexivity. Qed.

Lemma hm3_xor_Znth a b i : 0 <= i < Z.min (Zlength a) (Zlength b) ->
  Znth i (xor_bytes a b) = Byte.xor (Znth i a) (Znth i b).
Proof.
  intros H. unfold xor_bytes. rewrite Znth_map by (rewrite Zlength_combine; lia).
  rewrite hm3_Znth_combine by lia. reflexivity.
Qed.

Lemma hm3_nblocks_ge L : 0 <= L -> L <= 64 * chacha_nblocks L /\ 0 <= chacha_nblocks L.
Proof.
  intros H. unfold chacha_nblocks. pose proof (Z.div_mod (L + 63) 64 ltac:(lia)).
  pose proof (Z.mod_pos_bound (L + 63) 64 ltac:(lia)). split; [lia |]. apply Z.div_pos; lia.
Qed.

Lemma hm3_xor_length16 st m : Zlength st = 16 -> Zlength (chacha_xor 10 st m) = Zlength m.
Proof.
  intros H. unfold chacha_xor. rewrite hm3_xor_length, hm3_stream_length by auto.
  pose proof (hm3_nblocks_ge (Zlength m) (Zlength_nonneg m)). rewrite Z2Nat.id by lia. lia.
Qed.

(* block b of the XOR (ref_chacha20_xor's outer loop; the last block may be partial) *)
Lemma haead_xor_length st m : Zlength st = 16 -> Zlength (chacha_xor 10 st m) = Zlength m.
Proof. intros; apply hm3_xor_length16; auto. Qed.

Lemma haead_xor_block st m b : Zlength st = 16 -> 0 <= b -> 64 * b < Zlength m ->
  sublist (64 * b) (Z.min (64 * b + 64) (Zlength m)) (chacha_xor 10 st m) =
  xor_bytes (sublist (64 * b) (Z.min (64 * b + 64) (Zlength m)) m) (chacha_block_bytes 10 (chacha_advance st b)).
Proof.
  intros Hst Hb Hm. pose proof (hm3_xor_length16 st m Hst) as HX.
  pose proof (hm3_nblocks_ge (Zlength m) (Zlength_nonneg m)) as [HN1 HN2].
  apply Znth_eq_ext.
  - rewrite hm3_xor_length, !Zlength_sublist, hm3_block_length by (try apply haead_advance_length; auto; lia). lia.
  - intros i Hi. rewrite Zlength_sublist in Hi by lia.
    rewrite hm3_xor_Znth by (rewrite Zlength_sublist, hm3_block_length by (try apply haead_advance_length; auto; lia); lia).
    rewrite !Znth_sublist by lia. unfold chacha_xor at 1.
    rewrite hm3_xor_Znth.
    2: { rewrite hm3_stream_length, Z2Nat.id by (auto; lia). lia. }
    f_equal. replace (i + 64 * b) with (64 * b + i) by lia.
    apply hm3_stream_Znth; auto; [| lia]. rewrite Z2Nat.id by lia. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* the tag                                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma hm3_fold_len {A} (f: list int -> A -> list int) (l: list A) a :
  (forall h x, Zlength h = 17 -> Zlength (f h x) = 17) -> Zlength a = 17 -> Zlength (fold_left f l a) = 17.
Proof. intros Hf; revert a; induction l as [| x l IH]; intros a Ha; simpl; auto. Qed.

Lemma haead_padded_length (HF: haead_hrp_facts) r h buf : Zlength h = 17 -> Zlength (haead_padded r h buf) = 17.
Proof.
  intros Hh. destruct HF as (_ & _ & Hmul & _).
  assert (Hb: forall h m, Zlength h = 17 -> Zlength (hrp_block r h m) = 17) by (intros; apply Hmul; auto).
  unfold haead_padded. unfold hrp_loop.
  destruct (Z.eq_dec _ 0); [| apply Hb]; apply hm3_fold_len; auto.
Qed.

(* helpers of haead_mac_ok: the invariant `hrp_inv h /\ hrp_val h mod p1305_p = acc` *)
Lemma hm3_loop_succ {A: Type} (f: A -> Z -> A) (n: Z) (a: A) :
  0 <= n -> hrp_loop f (n + 1) a = f (hrp_loop f n a) n.
Proof.
  intros Hn. unfold hrp_loop. rewrite Z2Nat.inj_add by lia. change (Z.to_nat 1) with 1%nat.
  rewrite seq_app, map_app, fold_left_app. simpl. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma hm3_mod_l a b c : (a mod p1305_p + b) * c mod p1305_p = (a + b) * c mod p1305_p.
Proof.
  rewrite <- Z.mul_mod_idemp_l by (unfold p1305_p; lia).
  rewrite Z.add_mod_idemp_l by (unfold p1305_p; lia).
  rewrite Z.mul_mod_idemp_l by (unfold p1305_p; lia). reflexivity.
Qed.

Lemma hm3_step (HF: haead_hrp_facts) blk h m A : 16 <= Zlength blk -> Zlength m = 16 ->
  hrp_inv h -> hrp_val h mod p1305_p = A ->
  hrp_inv (hrp_block (hrp_init_r blk) h m) /\
  hrp_val (hrp_block (hrp_init_r blk) h m) mod p1305_p = p1305_step (p1305_r blk) A m.
Proof.
  destruct HF as (_&_&_&_&_&_&_&Hc&Hm&_).
  intros Hb Hl Hi Hv. destruct (Hc m Hl) as [Hcb Hcv]. unfold hrp_block.
  destruct (Hm blk h (hrp_block_c m) Hb Hi Hcb) as [Hi' Hv'].
  split; [exact Hi' |]. rewrite Hv', Hcv. unfold p1305_step. rewrite Hl. subst A.
  change (8 * 16) with 128. rewrite <- Z.add_assoc, hm3_mod_l. reflexivity.
Qed.

Lemma hm3_map_seq_shift {B: Type} m : forall (f: Z -> B) k,
  map f (map Z.of_nat (seq k m)) = map (fun i => f (i + Z.of_nat k)) (map Z.of_nat (seq 0 m)).
Proof.
  induction m as [| m IH]; intros f k; [reflexivity |].
  cbn [seq map]. rewrite IH. rewrite (IH (fun i => f (i + Z.of_nat k)) 1%nat).
  f_equal. apply map_ext. intros i. f_equal. lia.
Qed.

Lemma hm3_blocks_app x y : Zlength x mod 16 = 0 ->
  p1305_blocks (x ++ y) = p1305_blocks x ++ p1305_blocks y.
Proof.
  intros Hx. unfold p1305_blocks.
  assert (Hk: Zlength x = 16 * (Zlength x / 16)) by (pose proof (Z.div_mod (Zlength x) 16); lia).
  set (k := Zlength x / 16) in *. assert (0 <= k) by (pose proof (Zlength_nonneg x); lia).
  pose proof (Zlength_nonneg y).
  rewrite Zlength_app.
  replace ((Zlength x + Zlength y + 15) / 16) with (k + (Zlength y + 15) / 16)
    by (rewrite Hk, <- Z.add_assoc, (Z.mul_comm 16 k), Z.div_add_l by lia; reflexivity).
  replace ((Zlength x + 15) / 16) with k
    by (rewrite Hk, (Z.mul_comm 16 k), Z.div_add_l, (Z.div_small 15 16) by lia; lia).
  rewrite Z2Nat.inj_add by (try apply Z.div_pos; lia).
  rewrite seq_app, !map_app. f_equal.
  - apply map_ext_in. intros i Hi. apply in_map_iff in Hi. destruct Hi as (n & <- & Hn).
    apply in_seq in Hn. apply sublist_app1; lia.
  - rewrite hm3_map_seq_shift. simpl Nat.add. rewrite Z2Nat.id by lia.
    apply map_ext_in. intros i Hi. apply in_map_iff in Hi. destruct Hi as (n & <- & _).
    rewrite sublist_app2 by lia. f_equal; lia.
Qed.

Lemma hm3_acc_app R A x y : Zlength x mod 16 = 0 ->
  p1305_acc R A (x ++ y) = p1305_acc R (p1305_acc R A x) y.
Proof. intros Hx. unfold p1305_acc. rewrite hm3_blocks_app by exact Hx. apply fold_left_app. Qed.

Lemma hm3_acc_one R A b : Zlength b = 16 -> p1305_acc R A b = p1305_step R A b.
Proof.
  intros Hb. unfold p1305_acc, p1305_blocks. rewrite Hb. simpl. rewrite sublist_same by lia. reflexivity.
Qed.

Lemma hm3_acc_nil R A : p1305_acc R A [] = A.
Proof. reflexivity. Qed.

Lemma hm3_loop (HF: haead_hrp_facts) blk buf h A n : 16 <= Zlength blk -> 0 <= n -> 16 * n <= Zlength buf ->
  hrp_inv h -> hrp_val h mod p1305_p = A ->
  let h1 := hrp_loop (fun h k => hrp_block (hrp_init_r blk) h (sublist (16 * k) (16 * k + 16) buf)) n h in
  hrp_inv h1 /\ hrp_val h1 mod p1305_p = p1305_acc (p1305_r blk) A (sublist 0 (16 * n) buf).
Proof.
  intros Hb Hn. pattern n. apply natlike_ind; [| | exact Hn]; clear n Hn.
  - intros _ Hi Hv. cbv zeta. rewrite hrp_loop_0. split; [exact Hi |]. rewrite Hv. reflexivity.
  - intros n Hn IH Hl Hi Hv. cbv zeta. unfold Z.succ. rewrite hm3_loop_succ by exact Hn.
    destruct IH as [Hi1 Hv1]; [lia | exact Hi | exact Hv |].
    rewrite (sublist_split 0 (16 * n) (16 * (n + 1))) by lia.
    rewrite hm3_acc_app by (rewrite Zlength_sublist by lia; rewrite Z.sub_0_r, Z.mul_comm, Z_mod_mult; reflexivity).
    rewrite hm3_acc_one by (rewrite Zlength_sublist by lia; lia).
    replace (16 * (n + 1)) with (16 * n + 16) by lia.
    apply hm3_step; auto. rewrite Zlength_sublist by lia. lia.
Qed.

Lemma hm3_padded (HF: haead_hrp_facts) blk buf h A : 16 <= Zlength blk -> hrp_inv h -> hrp_val h mod p1305_p = A ->
  hrp_inv (haead_padded (hrp_init_r blk) h buf) /\
  hrp_val (haead_padded (hrp_init_r blk) h buf) mod p1305_p = p1305_acc (p1305_r blk) A (buf ++ pad16 buf).
Proof.
  intros Hb Hi Hv. unfold haead_padded.
  pose proof (Zlength_nonneg buf). pose proof (Z.div_mod (Zlength buf) 16).
  pose proof (Z.mod_pos_bound (Zlength buf) 16).
  set (nb := Zlength buf / 16) in *. assert (0 <= nb) by (apply Z.div_pos; lia).
  destruct (hm3_loop HF blk buf h A nb Hb) as [Hi1 Hv1]; auto; try lia.
  set (h1 := hrp_loop _ nb h) in *.
  unfold pad16. destruct (Z.eq_dec (Zlength buf - 16 * nb) 0) as [E | E].
  - split; [exact Hi1 |]. rewrite Hv1.
    replace (Zlength buf mod 16) with 0 by lia. change ((16 - 0) mod 16) with 0. cbn [Zrepeat repeat Z.to_nat].
    rewrite app_nil_r. f_equal. rewrite sublist_same by lia. reflexivity.
  - replace ((16 - Zlength buf mod 16) mod 16) with (16 - (Zlength buf - 16 * nb)) by (rewrite Z.mod_small; lia).
    replace (buf ++ _) with (sublist 0 (16 * nb) buf ++ (sublist (16 * nb) (Zlength buf) buf ++
      Zrepeat Byte.zero (16 - (Zlength buf - 16 * nb))))
      by (rewrite app_assoc, <- sublist_split, sublist_same by lia; reflexivity).
    rewrite hm3_acc_app by (rewrite Zlength_sublist by lia; rewrite Z.sub_0_r, Z.mul_comm, Z_mod_mult; reflexivity).
    assert (HL: Zlength (sublist (16 * nb) (Zlength buf) buf ++ Zrepeat Byte.zero (16 - (Zlength buf - 16 * nb))) = 16)
      by (rewrite Zlength_app, Zlength_sublist, Zlength_Zrepeat by lia; lia).
    rewrite hm3_acc_one by exact HL.
    apply hm3_step; auto.
Qed.

Lemma hm3_pad16_mod l : Zlength (l ++ pad16 l) mod 16 = 0.
Proof.
  unfold pad16. pose proof (Z.mod_pos_bound (16 - Zlength l mod 16) 16).
  rewrite Zlength_app, Zlength_Zrepeat by lia.
  rewrite Z.add_mod_idemp_r by lia. rewrite <- Z.add_mod_idemp_l by lia.
  replace (Zlength l mod 16 + (16 - Zlength l mod 16)) with (1 * 16) by lia. apply Z_mod_mult.
Qed.

Lemma hm3_le_bytes_length n z : Zlength (le_bytes n z) = Z.of_nat n.
Proof.
  revert z. induction n as [| n IH]; intros z; [reflexivity |].
  cbn [le_bytes]. rewrite Zlength_cons, IH. lia.
Qed.

(* ref_aead_tag: rp_init(blk), rp_padded(ad), rp_padded(ct), rp_block(lens), rp_final = Poly1305 of the
   AEAD's MAC data under blk[0..32) *)
Lemma haead_mac_ok (HF: haead_hrp_facts) blk ad ct : 32 <= Zlength blk ->
  hrp_final_out (haead_tag_h blk ad ct) (hrp_init_s blk) = poly1305_tag (sublist 0 32 blk) (aead_mac_data ad ct).
Proof.
  intros Hb. assert (Hb16: 16 <= Zlength blk) by lia.
  pose proof HF as HF'. destruct HF' as (_&_&_&_&_&[Hz0 Hz1]&_&_&_&Hf).
  destruct (hm3_padded HF blk ad hrp_zero17 0 Hb16 Hz0) as [Hi1 Hv1]; [rewrite Hz1; reflexivity |].
  destruct (hm3_padded HF blk ct _ _ Hb16 Hi1 Hv1) as [Hi2 Hv2].
  assert (HL: Zlength (le64_bytes (Zlength ad) ++ le64_bytes (Zlength ct)) = 16)
    by (unfold le64_bytes; rewrite Zlength_app, !hm3_le_bytes_length; reflexivity).
  destruct (hm3_step HF blk _ _ _ Hb16 HL Hi2 Hv2) as [Hi3 Hv3].
  unfold haead_tag_h. rewrite Hf by (auto; unfold hrp_init_s; rewrite Zlength_sublist by lia; lia).
  rewrite Hv3. unfold poly1305_tag, aead_mac_data, p1305_s, hrp_init_s.
  rewrite (app_assoc ad), (hm3_acc_app _ _ (ad ++ pad16 ad)) by apply hm3_pad16_mod.
  rewrite (app_assoc ct), (hm3_acc_app _ _ (ct ++ pad16 ct)) by apply hm3_pad16_mod.
  rewrite (hm3_acc_one _ _ (le64_bytes (Zlength ad) ++ le64_bytes (Zlength ct))) by exact HL.
  replace (p1305_r (sublist 0 32 blk)) with (p1305_r blk)
    by (unfold p1305_r; rewrite sublist_sublist00 by lia; reflexivity).
  rewrite (sublist_sublist 32 32 16 0) by lia. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* XChaCha20-Poly1305                                                      *)
(* ---------------------------------------------------------------------- *)

Lemma hm3_le_Z_range bs : 0 <= le_Z bs < 2 ^ (8 * Zlength bs).
Proof.
  induction bs as [| x bs IH]; [simpl; lia |]. cbn [le_Z]. rewrite Zlength_cons.
  replace (8 * Z.succ (Zlength bs)) with (8 * Zlength bs + 8) by lia. rewrite Z.pow_add_r by (pose proof (Zlength_nonneg bs); lia).
  change (2 ^ 8) with 256. pose proof (Byte.unsigned_range x) as Hx. change Byte.modulus with 256 in Hx. set (P := 2 ^ (8 * Zlength bs)) in *. lia.
Qed.

Lemma haead_le64_range bs : Zlength bs = 8 -> 0 <= le_Z bs <= Int64.max_unsigned.
Proof.
  intros H. pose proof (hm3_le_Z_range bs) as R. rewrite H in R.
  change Int64.max_unsigned with (2 ^ (8 * 8) - 1). lia.
Qed.

Lemma hm3_le32_at_words ws j : 0 <= j < Zlength ws -> le32_at (words_bytes ws) (4 * j) = Znth j ws.
Proof.
  revert j; induction ws as [| w ws IH]; intros j Hj; [rewrite Zlength_nil in Hj; lia |].
  rewrite Zlength_cons in Hj. rewrite hm3_words_bytes_cons. destruct (Z.eq_dec j 0).
  - subst j. rewrite Znth_0_cons.
    transitivity (le32_of (Byte.repr (Int.unsigned w)) (Byte.repr (Z.shiftr (Int.unsigned w) 8))
      (Byte.repr (Z.shiftr (Int.unsigned w) 16)) (Byte.repr (Z.shiftr (Int.unsigned w) 24))); [reflexivity |].
    rewrite hm3_le32_of, Int.repr_unsigned. reflexivity.
  - rewrite Znth_pos_cons by lia. rewrite <- IH by lia. unfold le32_at.
    assert (L4: Zlength (le32_bytes w) = 4) by reflexivity.
    rewrite !Znth_app2 by lia. rewrite L4. f_equal; f_equal; lia.
Qed.

Lemma hm3_le32_words_Znth n bs i : 0 <= i < Z.of_nat n -> Znth i (le32_words n bs) = le32_at bs (4 * i).
Proof.
  intros Hi. unfold le32_words.
  rewrite Znth_map by (rewrite Zlength_map, Zlength_correct, seq_length; lia).
  rewrite Znth_map by (rewrite Zlength_correct, seq_length; lia).
  f_equal. f_equal. unfold Znth. destruct (Z_lt_dec i 0); [lia |].
  rewrite seq_nth by lia. lia.
Qed.

Lemma hm3_le32_words_bytes ws : Zlength ws = 8 -> le32_words 8 (words_bytes ws) = ws.
Proof.
  intros H. apply Znth_eq_ext; [rewrite hm3_le32_words_length; lia |].
  intros i Hi. rewrite hm3_le32_words_length in Hi.
  rewrite hm3_le32_words_Znth by lia. apply hm3_le32_at_words. lia.
Qed.

Lemma hm3_hchacha_length n st : Zlength st = 16 -> Zlength (hchacha_words n st) = 8.
Proof.
  intros H. unfold hchacha_words. pose proof (hm3_rounds_length n st).
  rewrite Zlength_app, !Zlength_sublist by lia. lia.
Qed.

Lemma hm3_le_bytes_le_Z b : le_bytes (length b) (le_Z b) = b.
Proof.
  induction b as [| x b IH]; [reflexivity |]. cbn [length le_bytes le_Z]. f_equal.
  - rewrite <- (Byte.repr_unsigned x) at 2. apply Byte.eqm_samerepr. exists (le_Z b).
    change Byte.modulus with 256. lia.
  - replace ((Byte.unsigned x + 256 * le_Z b) / 256) with (le_Z b); [exact IH |].
    pose proof (Byte.unsigned_range x) as Hx. change Byte.modulus with 256 in Hx.
    rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

(* ref_xaead_*: the subkey as bytes (ref_hchacha20) and the nonce's last 8 bytes as a u64 (le64_load) *)
Lemma haead_xaead_st key nonce : Zlength key = 32 -> Zlength nonce = 24 ->
  aead_st (words_bytes (hchacha_words 10 (chacha_init_st (le32_words 8 key) (sublist 0 16 nonce))))
    (le_Z (sublist 16 24 nonce)) = xaead_st key nonce.
Proof.
  intros Hk Hn. unfold xaead_st, aead_st, xaead_subkey, aead_iv.
  rewrite hm3_le32_words_bytes by (apply hm3_hchacha_length; unfold chacha_init_st;
    rewrite !Zlength_app, hm3_le32_words_length; reflexivity).
  f_equal. f_equal. unfold le64_bytes.
  assert (L: length (sublist 16 24 nonce) = 8%nat).
  { pose proof (Zlength_sublist 16 24 nonce ltac:(lia) ltac:(lia)). rewrite Zlength_correct in H. lia. }
  rewrite <- L at 1. apply hm3_le_bytes_le_Z.
Qed.

(* the target: every fact above *)
Theorem haead_model3_all : haead_hrp_facts -> haead_facts.
Proof.
  intros HF. split; [exact haead_setup_st |]. split; [exact haead_xor_length |].
  split; [exact haead_xor_block |]. split; [exact (haead_padded_length HF) |].
  split; [exact (haead_mac_ok HF) |]. split; [exact haead_le64_range | exact haead_xaead_st].
Qed.
