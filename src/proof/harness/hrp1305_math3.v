(* the TweetNaCl Poly1305 of harness/common.h (struct rpoly: rp_add, rp_init, rp_mul, rp_block,
   rp_final; 17 limbs of 8 bits in u32 words) as plain Coq, and its correctness against aead_model.v's
   Poly1305.  SHARED by the laws prim_aead and prim_poly1305: copy this file verbatim, never change a statement.

   - The models mirror the C statement by statement, with CompCert's u32 arithmetic (Int.add, Int.mul,
     Int.and, Int.shru, Int.neg, Int.xor): a body proof is a transliteration, the loops by prefix
     (`hrp_loop f n a` is `for (j = 0; j < n; j++) a = f a j`, `hrp_loop_succ`).
   - The correctness lemmas (hrp_mul_ok, hrp_final_ok) hold for ANY 17-limb block c with c[0..15] <= 255 and
     c[16] <= 1 (full blocks: c[16] = 1; ref_poly1305's last partial block: c[len] = 1, c[16] = 0), under the
     invariant hrp_inv (h[0..15] <= 255, h[16] <= 4), which every rp_mul re-establishes. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.aead.aead_model.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* loops                                                                   *)
(* ---------------------------------------------------------------------- *)

(* for (j = 0; j < n; j++) a = f a j *)
Definition hrp_loop {A: Type} (f: A -> Z -> A) (n: Z) (a: A) : A :=
  fold_left f (map Z.of_nat (seq 0 (Z.to_nat n))) a.

Lemma hrp_loop_0 {A: Type} (f: A -> Z -> A) (a: A) : hrp_loop f 0 a = a.
Proof. reflexivity. Qed.

Lemma hrp_loop_succ {A: Type} (f: A -> Z -> A) (n: Z) (a: A) :
  0 <= n -> hrp_loop f (n + 1) a = f (hrp_loop f n a) n.
Proof.
  intros Hn. unfold hrp_loop. rewrite Z2Nat.inj_add by lia. change (Z.to_nat 1) with 1%nat.
  rewrite seq_app, map_app, fold_left_app. simpl. rewrite Z2Nat.id by lia. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* the C functions                                                         *)
(* ---------------------------------------------------------------------- *)

(* a byte as a u32 limb *)
Definition hrp_u8 (b: byte) : int := Int.repr (Byte.unsigned b).

(* rp_add(h, c): u32 u = 0; for (j = 0; j < 17; j++) { u += h[j] + c[j]; h[j] = u & 255; u >>= 8; } *)
Definition hrp_add_step (c: list int) (s: list int * int) (j: Z) : list int * int :=
  let u := Int.add (snd s) (Int.add (Znth j (fst s)) (Znth j c)) in
  (upd_Znth j (fst s) (Int.and u (Int.repr 255)), Int.shru u (Int.repr 8)).

Definition hrp_add (h c: list int) : list int := fst (hrp_loop (hrp_add_step c) 17 (h, Int.zero)).

(* rp_init(p, key): r = key[0..16) clamped (r[3] &= 15; r[4] &= 252; r[7] &= 15; r[8] &= 252; r[11] &= 15;
   r[12] &= 252; r[15] &= 15), r[16] = 0; h = 0; s = key[16..32) *)
Definition hrp_zero17 : list int := Zrepeat Int.zero 17.

Definition hrp_mask (j m: Z) (r: list int) : list int := upd_Znth j r (Int.and (Znth j r) (Int.repr m)).

Definition hrp_init_r (key: list byte) : list int :=
  hrp_mask 15 15 (hrp_mask 12 252 (hrp_mask 11 15 (hrp_mask 8 252 (hrp_mask 7 15 (hrp_mask 4 252
    (hrp_mask 3 15 (map hrp_u8 (sublist 0 16 key) ++ [Int.zero]))))))).

Definition hrp_init_s (key: list byte) : list byte := sublist 16 32 key.

(* rp_mul(p, c):
     rp_add(p->h, c);
     for (i = 0; i < 17; i++) { x[i] = 0;
       for (j = 0; j < 17; j++) x[i] += p->h[j] * ((j <= i) ? p->r[i - j] : 320 * p->r[i + 17 - j]); }
     for (i = 0; i < 17; i++) p->h[i] = x[i];
     u = 0; for (j = 0; j < 16; j++) { u += p->h[j]; p->h[j] = u & 255; u >>= 8; }
     u += p->h[16]; p->h[16] = u & 3; u = 5 * (u >> 2);
     for (j = 0; j < 16; j++) { u += p->h[j]; p->h[j] = u & 255; u >>= 8; }
     u += p->h[16]; p->h[16] = u; *)
Definition hrp_coef (r: list int) (i j: Z) : int :=
  if Z_le_dec j i then Znth (i - j) r else Int.mul (Int.repr 320) (Znth (i + 17 - j) r).

Definition hrp_prod_step (h r: list int) (i: Z) (x: int) (j: Z) : int :=
  Int.add x (Int.mul (Znth j h) (hrp_coef r i j)).

(* x[i] *)
Definition hrp_prod (h r: list int) (i: Z) : int := hrp_loop (hrp_prod_step h r i) 17 Int.zero.

(* x *)
Definition hrp_prods (h r: list int) : list int := map (hrp_prod h r) (map Z.of_nat (seq 0 17)).

(* u += h[j]; h[j] = u & 255; u >>= 8 *)
Definition hrp_carry_step (s: list int * int) (j: Z) : list int * int :=
  let u := Int.add (snd s) (Znth j (fst s)) in
  (upd_Znth j (fst s) (Int.and u (Int.repr 255)), Int.shru u (Int.repr 8)).

(* the two carry passes on h = x *)
Definition hrp_reduce (x: list int) : list int :=
  let s1 := hrp_loop hrp_carry_step 16 (x, Int.zero) in
  let u2 := Int.add (snd s1) (Znth 16 (fst s1)) in
  let h2 := upd_Znth 16 (fst s1) (Int.and u2 (Int.repr 3)) in
  let u3 := Int.mul (Int.repr 5) (Int.shru u2 (Int.repr 2)) in
  let s3 := hrp_loop hrp_carry_step 16 (h2, u3) in
  upd_Znth 16 (fst s3) (Int.add (snd s3) (Znth 16 (fst s3))).

(* p->h after rp_mul(p, c), with r = p->r and h = p->h before *)
Definition hrp_mul (r h c: list int) : list int := hrp_reduce (hrp_prods (hrp_add h c) r).

(* rp_block(p, m): c[j] = m[j] (j < 16), c[16] = 1; rp_mul(p, c) *)
Definition hrp_block_c (m: list byte) : list int := map hrp_u8 m ++ [Int.one].

Definition hrp_block (r h: list int) (m: list byte) : list int := hrp_mul r h (hrp_block_c m).

(* rp_final(p, out):
     for (j = 0; j < 17; j++) g[j] = p->h[j];
     rp_add(p->h, minusp);  s = -(p->h[16] >> 7);
     for (j = 0; j < 17; j++) p->h[j] ^= s & (g[j] ^ p->h[j]);
     for (j = 0; j < 16; j++) c[j] = p->s[j];  c[16] = 0;  rp_add(p->h, c);
     for (j = 0; j < 16; j++) out[j] = (u8)p->h[j]; *)
Definition hrp_minusp : list int := [Int.repr 5] ++ Zrepeat Int.zero 15 ++ [Int.repr 252].

Definition hrp_select_step (s: int) (g: list int) (h: list int) (j: Z) : list int :=
  upd_Znth j h (Int.xor (Znth j h) (Int.and s (Int.xor (Znth j g) (Znth j h)))).

(* p->h after rp_final, with sk = p->s *)
Definition hrp_final_h (h: list int) (sk: list byte) : list int :=
  let h1 := hrp_add h hrp_minusp in
  let s := Int.neg (Int.shru (Znth 16 h1) (Int.repr 7)) in
  let h2 := hrp_loop (hrp_select_step s h) 17 h1 in
  hrp_add h2 (map hrp_u8 sk ++ [Int.zero]).

(* out after rp_final *)
Definition hrp_final_out (h: list int) (sk: list byte) : list byte :=
  map (fun w => Byte.repr (Int.unsigned w)) (sublist 0 16 (hrp_final_h h sk)).

(* ---------------------------------------------------------------------- *)
(* values and the invariant                                                *)
(* ---------------------------------------------------------------------- *)

(* the number sum_j limb_j * 256^j *)
Fixpoint hrp_val (l: list int) : Z :=
  match l with [] => 0 | w :: t => Int.unsigned w + 256 * hrp_val t end.

(* the accumulator between two blocks (TweetNaCl): limbs 0..15 bytes, limb 16 at most 4 *)
Definition hrp_inv (h: list int) : Prop :=
  Zlength h = 17 /\ (forall j, 0 <= j < 16 -> Int.unsigned (Znth j h) <= 255) /\ Int.unsigned (Znth 16 h) <= 4.

(* a block: 16 byte limbs and a top limb 0 or 1 *)
Definition hrp_cblock (c: list int) : Prop :=
  Zlength c = 17 /\ (forall j, 0 <= j < 16 -> Int.unsigned (Znth j c) <= 255) /\ Int.unsigned (Znth 16 c) <= 1.

(* ---------------------------------------------------------------------- *)
(* helpers                                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma hrp_loop_ext {A: Type} (f g: A -> Z -> A) (n: Z) (a: A) :
  (forall b j, 0 <= j < n -> f b j = g b j) -> hrp_loop f n a = hrp_loop g n a.
Proof.
  intros H. unfold hrp_loop.
  assert (Hl: forall j, In j (map Z.of_nat (seq 0 (Z.to_nat n))) -> 0 <= j < n).
  { intros j Hj. apply in_map_iff in Hj. destruct Hj as [k [<- Hk]]. apply in_seq in Hk.
    destruct (Z_lt_le_dec n 0).
    - assert (Z.to_nat n = 0%nat) by (destruct n; simpl; auto; lia). lia.
    - rewrite <- (Z2Nat.id n) by lia. lia. }
  revert a Hl. generalize (map Z.of_nat (seq 0 (Z.to_nat n))).
  induction l as [|j l IH]; intros a Hl; simpl; [reflexivity | ].
  rewrite H by (apply Hl; left; auto). apply IH. intros; apply Hl; right; auto.
Qed.

Lemma hrp_loop_ind {A: Type} (f: A -> Z -> A) (P: Z -> A -> Prop) (n: Z) (a: A) :
  0 <= n -> P 0 a -> (forall k b, 0 <= k < n -> P k b -> P (k + 1) (f b k)) -> P n (hrp_loop f n a).
Proof.
  intros Hn H0 HS.
  assert (forall m, (m <= Z.to_nat n)%nat -> P (Z.of_nat m) (hrp_loop f (Z.of_nat m) a)).
  { induction m as [|m IH]; intros Hm; [exact H0 | ].
    rewrite Nat2Z.inj_succ, <- Z.add_1_r, hrp_loop_succ by lia. apply HS; [lia | apply IH; lia]. }
  specialize (H (Z.to_nat n) (le_n _)). rewrite Z2Nat.id in H by lia. exact H.
Qed.

Lemma hrp_and255 (x: int) : Int.unsigned (Int.and x (Int.repr 255)) = Int.unsigned x mod 256.
Proof.
  unfold Int.and. change (Int.unsigned (Int.repr 255)) with (Z.ones 8).
  rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
  apply Int.unsigned_repr. pose proof (Z.mod_pos_bound (Int.unsigned x) 256). rep_lia.
Qed.

Lemma hrp_and3 (x: int) : Int.unsigned (Int.and x (Int.repr 3)) = Int.unsigned x mod 4.
Proof.
  unfold Int.and. change (Int.unsigned (Int.repr 3)) with (Z.ones 2).
  rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
  apply Int.unsigned_repr. pose proof (Z.mod_pos_bound (Int.unsigned x) 4). rep_lia.
Qed.

Lemma hrp_shru (x: int) (k: Z) : 0 <= k < 32 ->
  Int.unsigned (Int.shru x (Int.repr k)) = Int.unsigned x / 2 ^ k.
Proof.
  intros Hk. unfold Int.shru. rewrite (Int.unsigned_repr k) by rep_lia.
  rewrite Z.shiftr_div_pow2 by lia. apply Int.unsigned_repr.
  pose proof (Int.unsigned_range x). assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia | ]. assert (Int.unsigned x / 2 ^ k <= Int.unsigned x).
  { apply Z.div_le_upper_bound; [lia | ]. nia. } rep_lia.
Qed.

Lemma hrp_uadd (x y: int) : Int.unsigned x + Int.unsigned y < Int.modulus ->
  Int.unsigned (Int.add x y) = Int.unsigned x + Int.unsigned y.
Proof. intros H. rewrite Int.add_unsigned. apply Int.unsigned_repr. rep_lia. Qed.

Lemma hrp_umul (x y: int) : Int.unsigned x * Int.unsigned y < Int.modulus ->
  Int.unsigned (Int.mul x y) = Int.unsigned x * Int.unsigned y.
Proof.
  intros H. unfold Int.mul. apply Int.unsigned_repr.
  pose proof (Int.unsigned_range x). pose proof (Int.unsigned_range y).
  assert (0 <= Int.unsigned x * Int.unsigned y) by nia. rep_lia.
Qed.

Lemma hrp_val_app l1 l2 : hrp_val (l1 ++ l2) = hrp_val l1 + 256 ^ Zlength l1 * hrp_val l2.
Proof.
  induction l1 as [|w t IH]; cbn [hrp_val app]; [rewrite Zlength_nil; lia | ].
  rewrite IH, Zlength_cons, Z.pow_succ_r by (pose proof (Zlength_nonneg t); lia). ring.
Qed.

Lemma hrp_val_nonneg l : 0 <= hrp_val l.
Proof. induction l as [|w t IH]; simpl; [lia | ]. pose proof (Int.unsigned_range w). lia. Qed.

Lemma hrp_val_lt l : (forall j, 0 <= j < Zlength l -> Int.unsigned (Znth j l) < 256) ->
  hrp_val l < 256 ^ Zlength l.
Proof.
  induction l as [|w t IH]; intros H; cbn [hrp_val]; [rewrite Zlength_nil; lia | ].
  rewrite Zlength_cons, Z.pow_succ_r by (pose proof (Zlength_nonneg t); lia).
  assert (hrp_val t < 256 ^ Zlength t).
  { apply IH. intros j Hj. specialize (H (j + 1)). rewrite Znth_pos_cons, Z.add_simpl_r in H by lia.
    apply H. rewrite Zlength_cons. lia. }
  specialize (H 0). rewrite Znth_0_cons in H. pose proof (Zlength_nonneg t). rewrite Zlength_cons in H.
  assert (Int.unsigned w < 256) by (apply H; lia). pose proof (Int.unsigned_range w). lia.
Qed.

(* the value of a prefix grows by one limb *)
Lemma hrp_val_sublist_succ l k : 0 <= k < Zlength l ->
  hrp_val (sublist 0 (k + 1) l) = hrp_val (sublist 0 k l) + 256 ^ k * Int.unsigned (Znth k l).
Proof.
  intros Hk. rewrite (sublist_split 0 k (k + 1)) by lia. rewrite hrp_val_app, sublist_len_1 by lia.
  rewrite Zlength_sublist, Z.sub_0_r by lia. cbn [hrp_val]. ring.
Qed.

Lemma hrp_val_split16 l : Zlength l = 17 ->
  hrp_val l = hrp_val (sublist 0 16 l) + 2 ^ 128 * Int.unsigned (Znth 16 l).
Proof.
  intros Hl. rewrite <- (sublist_same 0 17 l) at 1 by lia.
  change 17 with (16 + 1). rewrite (hrp_val_sublist_succ l 16) by lia. reflexivity.
Qed.

(* the carry loop of rp_add (and, with c = 0, of the carry passes of rp_mul) *)
Lemma hrp_add_loop (c h: list int) (u: int) (n: Z) :
  0 <= n <= Zlength h -> n <= Zlength c ->
  (forall j, 0 <= j < n -> Int.unsigned (Znth j h) + Int.unsigned (Znth j c) < 2 ^ 31) ->
  Int.unsigned u < 2 ^ 28 ->
  let s := hrp_loop (hrp_add_step c) n (h, u) in
  Zlength (fst s) = Zlength h /\
  (forall j, 0 <= j < n -> Int.unsigned (Znth j (fst s)) < 256) /\
  (forall j, n <= j < Zlength h -> Znth j (fst s) = Znth j h) /\
  Int.unsigned (snd s) < 2 ^ 28 /\ (0 < n -> Int.unsigned (snd s) < 2 ^ 24) /\
  hrp_val (sublist 0 n (fst s)) + 256 ^ n * Int.unsigned (snd s) =
    hrp_val (sublist 0 n h) + hrp_val (sublist 0 n c) + Int.unsigned u.
Proof.
  intros Hn Hc Hb Hu s. subst s.
  apply (hrp_loop_ind (hrp_add_step c) (fun k s =>
    Zlength (fst s) = Zlength h /\
    (forall j, 0 <= j < k -> Int.unsigned (Znth j (fst s)) < 256) /\
    (forall j, k <= j < Zlength h -> Znth j (fst s) = Znth j h) /\
    Int.unsigned (snd s) < 2 ^ 28 /\ (0 < k -> Int.unsigned (snd s) < 2 ^ 24) /\
    hrp_val (sublist 0 k (fst s)) + 256 ^ k * Int.unsigned (snd s) =
      hrp_val (sublist 0 k h) + hrp_val (sublist 0 k c) + Int.unsigned u)); [lia | | ].
  - simpl. split; [reflexivity | ]. split; [intros; lia | ]. split; [reflexivity | ].
    split; [lia | ]. split; [lia | ]. rewrite ?sublist_nil. simpl. lia.
  - intros k [h' u'] Hk (Hl & Hlo & Hhi & Hu1 & Hu2 & Hv). simpl in *.
    unfold hrp_add_step; simpl.
    rewrite Hhi by lia.
    pose proof (Hb k ltac:(lia)) as Hbk.
    pose proof (Int.unsigned_range (Znth k h)). pose proof (Int.unsigned_range (Znth k c)).
    pose proof (Int.unsigned_range u').
    set (v := Int.add u' (Int.add (Znth k h) (Znth k c))).
    assert (Hv': Int.unsigned v = Int.unsigned u' + Int.unsigned (Znth k h) + Int.unsigned (Znth k c)).
    { assert (Hin: Int.unsigned (Int.add (Znth k h) (Znth k c)) = Int.unsigned (Znth k h) + Int.unsigned (Znth k c))
        by (apply hrp_uadd; rep_lia).
      unfold v. rewrite hrp_uadd; rewrite Hin; rep_lia. }
    split; [rewrite upd_Znth_Zlength; lia | ].
    split.
    { intros j Hj. destruct (Z.eq_dec j k) as [->|].
      - rewrite upd_Znth_same by lia. rewrite hrp_and255. apply Z.mod_pos_bound; lia.
      - rewrite upd_Znth_diff by lia. apply Hlo; lia. }
    split; [intros j Hj; rewrite upd_Znth_diff by lia; apply Hhi; lia | ].
    rewrite (hrp_shru v 8) by lia. change (2 ^ 8) with 256.
    assert (Hd: Int.unsigned v / 256 < 2 ^ 24).
    { apply Z.div_lt_upper_bound; [lia | ]. rewrite Hv'. lia. }
    split; [lia | ]. split; [intros; lia | ].
    rewrite hrp_val_sublist_succ by (rewrite upd_Znth_Zlength; lia).
    rewrite (hrp_val_sublist_succ h) by lia. rewrite (hrp_val_sublist_succ c) by lia.
    rewrite upd_Znth_same by lia. rewrite hrp_and255.
    rewrite sublist_upd_Znth_l by lia.
    rewrite Z.pow_add_r by lia. change (256 ^ 1) with 256.
    assert (Hdm: Int.unsigned v = 256 * (Int.unsigned v / 256) + Int.unsigned v mod 256)
      by (apply Z.div_mod; lia).
    assert (Hp: 256 ^ k * Int.unsigned v = 256 ^ k * Int.unsigned u' +
       256 ^ k * Int.unsigned (Znth k h) + 256 ^ k * Int.unsigned (Znth k c)) by (rewrite Hv'; ring).
    assert (Hp2: 256 ^ k * (Int.unsigned v mod 256) + 256 ^ k * 256 * (Int.unsigned v / 256) =
       256 ^ k * Int.unsigned v) by (rewrite Hdm at 3; ring).
    lia.
Qed.

Lemma hrp_add_loop_length c h u n : 0 <= n <= Zlength h ->
  Zlength (fst (hrp_loop (hrp_add_step c) n (h, u))) = Zlength h.
Proof.
  intros Hn. apply (hrp_loop_ind _ (fun k s => Zlength (fst s) = Zlength h)); [lia | reflexivity | ].
  intros k [h' u'] Hk Hl. simpl in *. unfold hrp_add_step; simpl. rewrite upd_Znth_Zlength; lia.
Qed.

Lemma hrp_carry_add n s : hrp_loop hrp_carry_step n s = hrp_loop (hrp_add_step hrp_zero17) n s.
Proof.
  apply hrp_loop_ext. intros [h u] j Hj. unfold hrp_carry_step, hrp_add_step; simpl.
  assert (E: Znth j hrp_zero17 = Int.zero).
  { unfold hrp_zero17. destruct (Z_lt_le_dec j 17).
    - apply Znth_Zrepeat; lia.
    - apply Znth_overflow. rewrite Zlength_Zrepeat; lia. }
  rewrite E, Int.add_zero. reflexivity.
Qed.

Lemma hrp_pow16 : 256 ^ 16 = 2 ^ 128.
Proof. reflexivity. Qed.

Lemma hrp_pow17 : 256 ^ 17 = 2 ^ 136.
Proof. reflexivity. Qed.

(* rp_add on 17 limbs without overflow *)
Lemma hrp_add_spec h c : Zlength h = 17 -> Zlength c = 17 ->
  (forall j, 0 <= j < 17 -> Int.unsigned (Znth j h) + Int.unsigned (Znth j c) < 2 ^ 31) ->
  Zlength (hrp_add h c) = 17 /\ (forall j, 0 <= j < 17 -> Int.unsigned (Znth j (hrp_add h c)) < 256) /\
  exists t, 0 <= t /\ hrp_val (hrp_add h c) + 2 ^ 136 * t = hrp_val h + hrp_val c.
Proof.
  intros Hh Hc Hb. unfold hrp_add.
  pose proof (hrp_add_loop c h Int.zero 17 ltac:(lia) ltac:(lia) Hb ltac:(rewrite Int.unsigned_zero; lia))
    as H. cbv zeta in H.
  destruct (hrp_loop (hrp_add_step c) 17 (h, Int.zero)) as [h' u'] eqn:E. cbn [fst snd] in *.
  destruct H as (Hl & Hlo & _ & _ & _ & Hv).
  rewrite !sublist_same in Hv by lia. rewrite Int.unsigned_zero, hrp_pow17 in Hv.
  split; [lia | ]. split; [exact Hlo | ]. exists (Int.unsigned u').
  split; [apply Int.unsigned_range | lia].
Qed.

(* the two carry passes of rp_mul *)
Lemma hrp_reduce_ok x : Zlength x = 17 ->
  (forall j, 0 <= j < 17 -> Int.unsigned (Znth j x) < 2 ^ 31) -> Int.unsigned (Znth 16 x) < 2 ^ 24 ->
  hrp_inv (hrp_reduce x) /\ hrp_val (hrp_reduce x) mod p1305_p = hrp_val x mod p1305_p.
Proof.
  intros Hx Hb H16. unfold hrp_reduce. rewrite !hrp_carry_add.
  assert (Hz: forall j, Int.unsigned (Znth j hrp_zero17) = 0).
  { intros j. unfold hrp_zero17. destruct (Z_lt_le_dec j 0).
    - rewrite Znth_underflow by lia. reflexivity.
    - destruct (Z_lt_le_dec j 17).
      + rewrite Znth_Zrepeat by lia. reflexivity.
      + rewrite Znth_overflow by (rewrite Zlength_Zrepeat; lia). reflexivity. }
  assert (Hz16: hrp_val (sublist 0 16 hrp_zero17) = 0) by reflexivity.
  pose proof (hrp_add_loop hrp_zero17 x Int.zero 16 ltac:(lia) ltac:(unfold hrp_zero17; rewrite Zlength_Zrepeat; lia)
    ltac:(intros j Hj; rewrite Hz; specialize (Hb j ltac:(lia)); lia)
    ltac:(rewrite Int.unsigned_zero; lia)) as H1. cbv zeta in H1.
  destruct (hrp_loop (hrp_add_step hrp_zero17) 16 (x, Int.zero)) as [h1 u1] eqn:E1. cbn [fst snd] in *.
  destruct H1 as (L1 & Lo1 & Hi1 & _ & U1 & V1).
  specialize (U1 ltac:(lia)). rewrite Hz16, Int.unsigned_zero, hrp_pow16 in V1.
  rewrite (Hi1 16) by lia.
  pose proof (Int.unsigned_range u1). pose proof (Int.unsigned_range (Znth 16 x)).
  set (u2 := Int.add u1 (Znth 16 x)).
  assert (Hu2: Int.unsigned u2 = Int.unsigned u1 + Int.unsigned (Znth 16 x)) by (apply hrp_uadd; rep_lia).
  set (h2 := upd_Znth 16 h1 (Int.and u2 (Int.repr 3))).
  assert (Hq: 0 <= Int.unsigned u2 / 4 < 2 ^ 23).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  set (u3 := Int.mul (Int.repr 5) (Int.shru u2 (Int.repr 2))).
  assert (Hu3: Int.unsigned u3 = 5 * (Int.unsigned u2 / 4)).
  { unfold u3. rewrite hrp_umul; rewrite (hrp_shru u2 2) by lia; change (2 ^ 2) with 4;
      rewrite Int.unsigned_repr by rep_lia; rep_lia. }
  assert (L2: Zlength h2 = 17) by (unfold h2; rewrite upd_Znth_Zlength; lia).
  assert (Lo2: forall j, 0 <= j < 16 -> Znth j h2 = Znth j h1).
  { intros j Hj. unfold h2. rewrite upd_Znth_diff by lia. reflexivity. }
  pose proof (hrp_add_loop hrp_zero17 h2 u3 16 ltac:(lia) ltac:(unfold hrp_zero17; rewrite Zlength_Zrepeat; lia)
    ltac:(intros j Hj; rewrite Hz, Lo2 by lia; specialize (Lo1 j Hj); lia)
    ltac:(lia)) as H3. cbv zeta in H3.
  destruct (hrp_loop (hrp_add_step hrp_zero17) 16 (h2, u3)) as [h3 uf] eqn:E3. cbn [fst snd] in *.
  destruct H3 as (L3 & Lo3 & Hi3 & _ & Uf & V3).
  specialize (Uf ltac:(lia)). rewrite Hz16, hrp_pow16 in V3.
  rewrite (Hi3 16) by lia.
  assert (Hh216: Int.unsigned (Znth 16 h2) = Int.unsigned u2 mod 4).
  { unfold h2. rewrite upd_Znth_same by lia. apply hrp_and3. }
  assert (Hs2: sublist 0 16 h2 = sublist 0 16 h1) by (unfold h2; rewrite sublist_upd_Znth_l by lia; reflexivity).
  rewrite Hs2 in V3.
  assert (B1: hrp_val (sublist 0 16 h1) < 2 ^ 128).
  { rewrite <- hrp_pow16. replace 16 with (Zlength (sublist 0 16 h1)) at 2 by (rewrite Zlength_sublist; lia).
    apply hrp_val_lt. rewrite Zlength_sublist by lia. intros j Hj. rewrite Znth_sublist by lia.
    apply Lo1; lia. }
  pose proof (hrp_val_nonneg (sublist 0 16 h3)).
  pose proof (Int.unsigned_range uf).
  assert (Huf: Int.unsigned uf <= 1).
  { assert (2 ^ 128 * Int.unsigned uf < 2 ^ 128 * 2) by lia. nia. }
  pose proof (Z.mod_pos_bound (Int.unsigned u2) 4 ltac:(lia)).
  set (hf := upd_Znth 16 h3 (Int.add uf (Znth 16 h2))).
  assert (Lf: Zlength hf = 17) by (unfold hf; rewrite upd_Znth_Zlength; lia).
  assert (Hf16: Int.unsigned (Znth 16 hf) = Int.unsigned uf + Int.unsigned u2 mod 4).
  { unfold hf. rewrite upd_Znth_same by lia. rewrite hrp_uadd; rewrite Hh216; rep_lia. }
  assert (Hfs: sublist 0 16 hf = sublist 0 16 h3) by (unfold hf; rewrite sublist_upd_Znth_l by lia; reflexivity).
  split.
  - split; [exact Lf | ]. split; [ | lia].
    intros j Hj. unfold hf. rewrite upd_Znth_diff by lia. specialize (Lo3 j Hj). lia.
  - rewrite (hrp_val_split16 hf Lf), (hrp_val_split16 x Hx), Hfs, Hf16.
    assert (Hdm: Int.unsigned u2 = 4 * (Int.unsigned u2 / 4) + Int.unsigned u2 mod 4) by (apply Z.div_mod; lia).
    replace (hrp_val (sublist 0 16 h3) + 2 ^ 128 * (Int.unsigned uf + Int.unsigned u2 mod 4))
      with (hrp_val (sublist 0 16 x) + 2 ^ 128 * Int.unsigned (Znth 16 x) + (- (Int.unsigned u2 / 4)) * p1305_p).
    + apply Z_mod_plus_full.
    + unfold p1305_p. rewrite Hu3 in V3. lia.
Qed.

(* the products x[i] as integers *)
Definition hrp_zcoef (r: list int) (i j: Z) : Z :=
  if Z_le_dec j i then Int.unsigned (Znth (i - j) r) else 320 * Int.unsigned (Znth (i + 17 - j) r).

Definition hrp_zprod_step (h r: list int) (i: Z) (x: Z) (j: Z) : Z :=
  x + Int.unsigned (Znth j h) * hrp_zcoef r i j.

Definition hrp_zprod (h r: list int) (i: Z) : Z := hrp_loop (hrp_zprod_step h r i) 17 0.

Lemma hrp_prod_val h r i : (forall j, 0 <= j < 17 -> Int.unsigned (Znth j h) <= 255) ->
  (forall j, 0 <= j < 17 -> Int.unsigned (Znth j r) <= 255) -> 0 <= i < 17 ->
  Int.unsigned (hrp_prod h r i) = hrp_zprod h r i /\ hrp_zprod h r i < 2 ^ 31 /\
  (i = 16 -> hrp_zprod h r i < 2 ^ 24).
Proof.
  intros Hh Hr Hi. unfold hrp_prod, hrp_zprod.
  assert (H: forall n, 0 <= n <= 17 ->
    Int.unsigned (hrp_loop (hrp_prod_step h r i) n Int.zero) = hrp_loop (hrp_zprod_step h r i) n 0 /\
    0 <= hrp_loop (hrp_zprod_step h r i) n 0 <= n * (255 * 81600) /\
    (i = 16 -> hrp_loop (hrp_zprod_step h r i) n 0 <= n * (255 * 255))).
  { intros n Hn.
    apply (hrp_loop_ind _ (fun k x => Int.unsigned x = hrp_loop (hrp_zprod_step h r i) k 0 /\
      0 <= hrp_loop (hrp_zprod_step h r i) k 0 <= k * (255 * 81600) /\
      (i = 16 -> hrp_loop (hrp_zprod_step h r i) k 0 <= k * (255 * 255)))); [lia | | ].
    - rewrite hrp_loop_0, Int.unsigned_zero. lia.
    - intros k x Hk (Hx & Hb & Hb16). rewrite hrp_loop_succ by lia.
      set (L := hrp_loop (hrp_zprod_step h r i) k 0) in *.
      unfold hrp_prod_step, hrp_zprod_step.
      assert (Hc: Int.unsigned (hrp_coef r i k) = hrp_zcoef r i k /\ 0 <= hrp_zcoef r i k <= 81600 /\
                  (i = 16 -> hrp_zcoef r i k <= 255)).
      { unfold hrp_coef, hrp_zcoef. destruct (Z_le_dec k i).
        - pose proof (Int.unsigned_range (Znth (i - k) r)). specialize (Hr (i - k) ltac:(lia)). lia.
        - pose proof (Int.unsigned_range (Znth (i + 17 - k) r)). specialize (Hr (i + 17 - k) ltac:(lia)).
          rewrite hrp_umul; rewrite Int.unsigned_repr by rep_lia; [lia | rep_lia]. }
      destruct Hc as (Hc & Hc1 & Hc16).
      pose proof (Int.unsigned_range (Znth k h)). specialize (Hh k ltac:(lia)).
      assert (Hm: 0 <= Int.unsigned (Znth k h) * hrp_zcoef r i k <= 255 * 81600) by nia.
      assert (Hm16: i = 16 -> Int.unsigned (Znth k h) * hrp_zcoef r i k <= 255 * 255).
      { intros E. specialize (Hc16 E). nia. }
      rewrite hrp_uadd; rewrite hrp_umul; rewrite ?Hc; rep_lia. }
  destruct (H 17 ltac:(lia)) as (H1 & H2 & H3). split; [exact H1 | ]. split; [lia | ].
  intros E. specialize (H3 E). lia.
Qed.

Fixpoint hrp_zval (l: list Z) : Z :=
  match l with [] => 0 | z :: t => z + 256 * hrp_zval t end.

Lemma hrp_val_map {A: Type} (f: A -> int) (l: list A) :
  hrp_val (map f l) = hrp_zval (map (fun a => Int.unsigned (f a)) l).
Proof. induction l as [|a l IH]; simpl; [reflexivity | ]. rewrite IH. reflexivity. Qed.

Lemma hrp_val_zval l : hrp_val l = hrp_zval (map Int.unsigned l).
Proof. induction l as [|a l IH]; simpl; [reflexivity | ]. rewrite IH. reflexivity. Qed.

(* the product as a polynomial identity over the limb values (nat indices, computed by cbv) *)
Definition hrp_nc (r: list Z) (i j: nat) : Z :=
  if Nat.leb j i then nth (i - j) r 0 else 320 * nth (i + 17 - j) r 0.

Definition hrp_nprod (h r: list Z) (i: nat) : Z :=
  fold_left (fun x j => x + nth j h 0 * hrp_nc r i j) (seq 0 17) 0.

Definition hrp_nQ (h r: list Z) (i: nat) : Z :=
  fold_left (fun x j => x + if Nat.leb j i then 0 else nth j h 0 * nth (i + 17 - j) r 0) (seq 0 17) 0.

Lemma hrp_ring17 h r : length h = 17%nat -> length r = 17%nat ->
  hrp_zval (map (hrp_nprod h r) (seq 0 17)) =
  hrp_zval h * hrp_zval r + (-64 * hrp_zval (map (hrp_nQ h r) (seq 0 17))) * p1305_p.
Proof.
  intros Hh Hr.
  do 17 (destruct h as [|? h]; [simpl in Hh; discriminate | ]). destruct h; [ | simpl in Hh; discriminate].
  do 17 (destruct r as [|? r]; [simpl in Hr; discriminate | ]). destruct r; [ | simpl in Hr; discriminate].
  unfold p1305_p. cbv [hrp_zval hrp_nc hrp_nprod hrp_nQ map seq fold_left nth Nat.leb Nat.sub Nat.add].
  ring.
Qed.

Lemma hrp_fold_ext {A B: Type} (f g: A -> B -> A) (l: list B) (a: A) :
  (forall x y, In y l -> f x y = g x y) -> fold_left f l a = fold_left g l a.
Proof.
  revert a. induction l as [|y l IH]; intros a H; simpl; [reflexivity | ].
  rewrite H by (left; auto). apply IH. intros; apply H; right; auto.
Qed.

Lemma hrp_znth_nth (l: list int) (j: nat) : Int.unsigned (Znth (Z.of_nat j) l) = nth j (map Int.unsigned l) 0.
Proof.
  unfold Znth. destruct (Z_lt_dec (Z.of_nat j) 0); [lia | ]. rewrite Nat2Z.id.
  change 0 with (Int.unsigned Int.zero). rewrite map_nth. reflexivity.
Qed.

Lemma hrp_zprod_nat h r (i: nat) : (i < 17)%nat ->
  hrp_zprod h r (Z.of_nat i) = hrp_nprod (map Int.unsigned h) (map Int.unsigned r) i.
Proof.
  intros Hi. unfold hrp_zprod, hrp_loop, hrp_nprod. change (Z.to_nat 17) with 17%nat.
  assert (Hs: forall j, In j (seq 0 17) -> (j < 17)%nat) by (intros j Hj; apply in_seq in Hj; lia).
  assert (Hstep: forall x j, (j < 17)%nat -> hrp_zprod_step h r (Z.of_nat i) x (Z.of_nat j) =
     x + nth j (map Int.unsigned h) 0 * hrp_nc (map Int.unsigned r) i j).
  { intros x j Hj. unfold hrp_zprod_step, hrp_zcoef, hrp_nc. rewrite hrp_znth_nth. f_equal. f_equal.
    destruct (Z_le_dec (Z.of_nat j) (Z.of_nat i)); destruct (Nat.leb_spec j i); try lia.
    - replace (Z.of_nat i - Z.of_nat j) with (Z.of_nat (i - j)) by lia. apply hrp_znth_nth.
    - replace (Z.of_nat i + 17 - Z.of_nat j) with (Z.of_nat (i + 17 - j)) by lia.
      rewrite hrp_znth_nth. reflexivity. }
  revert Hs. generalize (seq 0 17). intros l Hs.
  enough (E: forall a, fold_left (hrp_zprod_step h r (Z.of_nat i)) (map Z.of_nat l) a =
    fold_left (fun x j => x + nth j (map Int.unsigned h) 0 * hrp_nc (map Int.unsigned r) i j) l a)
    by apply E.
  induction l as [|j l IH]; intros a; simpl; [reflexivity | ].
  rewrite Hstep by (apply Hs; left; auto). apply IH. intros; apply Hs; right; auto.
Qed.

Lemma hrp_prods_ok h r : Zlength h = 17 -> Zlength r = 17 ->
  (forall j, 0 <= j < 17 -> Int.unsigned (Znth j h) <= 255) ->
  (forall j, 0 <= j < 17 -> Int.unsigned (Znth j r) <= 255) ->
  Zlength (hrp_prods h r) = 17 /\
  (forall i, 0 <= i < 17 -> Int.unsigned (Znth i (hrp_prods h r)) < 2 ^ 31) /\
  Int.unsigned (Znth 16 (hrp_prods h r)) < 2 ^ 24 /\
  hrp_val (hrp_prods h r) mod p1305_p = hrp_val h * hrp_val r mod p1305_p.
Proof.
  intros Lh Lr Bh Br.
  assert (Hz: forall i, 0 <= i < 17 -> Znth i (hrp_prods h r) = hrp_prod h r i).
  { intros i Hi. unfold hrp_prods. rewrite Znth_map by (rewrite Zlength_map, Zlength_correct, seq_length; lia).
    rewrite Znth_map by (rewrite Zlength_correct, seq_length; lia). f_equal.
    unfold Znth. destruct (Z_lt_dec i 0); [lia | ]. rewrite seq_nth by lia. lia. }
  split; [unfold hrp_prods; rewrite !Zlength_map, Zlength_correct, seq_length; reflexivity | ].
  split; [intros i Hi; rewrite Hz by lia; pose proof (hrp_prod_val h r i Bh Br Hi); lia | ].
  split; [rewrite Hz by lia; pose proof (hrp_prod_val h r 16 Bh Br ltac:(lia)); lia | ].
  unfold hrp_prods. rewrite hrp_val_map, map_map.
  rewrite (map_ext_in _ (hrp_nprod (map Int.unsigned h) (map Int.unsigned r))).
  2: { intros i Hi. apply in_seq in Hi. rewrite (proj1 (hrp_prod_val h r (Z.of_nat i) Bh Br ltac:(lia))).
       apply hrp_zprod_nat. lia. }
  rewrite hrp_ring17 by (rewrite map_length; rewrite <- ZtoNat_Zlength; rewrite ?Lh, ?Lr; reflexivity).
  rewrite <- !hrp_val_zval. apply Z_mod_plus_full.
Qed.

Lemma hrp_reduce_length x : Zlength x = 17 -> Zlength (hrp_reduce x) = 17.
Proof.
  intros Hx. unfold hrp_reduce. cbv zeta. rewrite !hrp_carry_add.
  repeat (first [rewrite upd_Znth_Zlength | rewrite hrp_add_loop_length]); lia.
Qed.

Lemma hrp_byte_range b : 0 <= Byte.unsigned b < 256.
Proof. pose proof (Byte.unsigned_range b). exact H. Qed.

Lemma hrp_u8_val b : Int.unsigned (hrp_u8 b) = Byte.unsigned b.
Proof. unfold hrp_u8. pose proof (hrp_byte_range b). apply Int.unsigned_repr. rep_lia. Qed.

Lemma hrp_land_byte a m : 0 <= m < 256 -> 0 <= Z.land a m < 256.
Proof.
  intros Hm. assert (Hm': Z.land m (Z.ones 8) = m) by (rewrite Z.land_ones by lia; apply Z.mod_small; lia).
  rewrite <- Hm', Z.land_assoc, Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.

Lemma hrp_and_u8 b m : 0 <= m < 256 ->
  Int.unsigned (Int.and (hrp_u8 b) (Int.repr m)) = Z.land (Byte.unsigned b) m /\
  0 <= Z.land (Byte.unsigned b) m < 256.
Proof.
  intros Hm. pose proof (hrp_byte_range b).
  pose proof (hrp_land_byte (Byte.unsigned b) m Hm) as H1. split; [ | exact H1].
  unfold Int.and. rewrite hrp_u8_val, (Int.unsigned_repr m) by rep_lia. apply Int.unsigned_repr. rep_lia.
Qed.

Lemma hrp_land_split b t m n : 0 <= b < 256 -> 0 <= m < 256 ->
  Z.land (b + 256 * t) (m + 256 * n) = Z.land b m + 256 * Z.land t n.
Proof.
  intros Hb Hm. set (X := Z.land (b + 256 * t) (m + 256 * n)).
  assert (Hmod: forall y z, 0 <= y < 256 -> (y + 256 * z) mod 256 = y).
  { intros y z Hy. rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_small. lia. }
  assert (Hdiv: forall y z, 0 <= y < 256 -> (y + 256 * z) / 256 = z).
  { intros y z Hy. rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  assert (E1: X mod 256 = Z.land b m).
  { change 256 with (2 ^ 8). rewrite <- Z.land_ones by lia. unfold X.
    assert (Hl: forall A B O, Z.land (Z.land A B) O = Z.land (Z.land A O) (Z.land B O)).
    { intros A B O. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
      destruct (Z.testbit A i), (Z.testbit B i), (Z.testbit O i); reflexivity. }
    rewrite Hl, !Z.land_ones by lia. change (2 ^ 8) with 256. rewrite !Hmod by lia. reflexivity. }
  assert (E2: X / 256 = Z.land t n).
  { change 256 with (2 ^ 8). rewrite <- Z.shiftr_div_pow2 by lia. unfold X.
    rewrite Z.shiftr_land, !Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. rewrite !Hdiv by lia.
    reflexivity. }
  rewrite (Z.div_mod X 256) by lia. rewrite E1, E2. ring.
Qed.

Lemma hrp_le_Z_nonneg bs : 0 <= le_Z bs.
Proof. induction bs as [|b t IH]; simpl; [lia | ]. pose proof (hrp_byte_range b). lia. Qed.

Lemma hrp_val_u8 bs : hrp_val (map hrp_u8 bs) = le_Z bs.
Proof. induction bs as [|b t IH]; simpl; [reflexivity | ]. rewrite IH, hrp_u8_val. reflexivity. Qed.

(* the limbs as little-endian bytes *)
Lemma hrp_bytes_le (n: nat) (l: list int) :
  Zlength l = Z.of_nat n -> (forall j, 0 <= j < Zlength l -> Int.unsigned (Znth j l) < 256) ->
  map (fun w => Byte.repr (Int.unsigned w)) l = le_bytes n (hrp_val l).
Proof.
  revert l. induction n as [|n IH]; intros l Hl Hb.
  - destruct l; [reflexivity | ]. rewrite Zlength_cons in Hl. pose proof (Zlength_nonneg l). lia.
  - destruct l as [|w t]; [rewrite Zlength_nil in Hl; lia | ].
    rewrite Zlength_cons in Hl. cbn [map le_bytes hrp_val].
    assert (Hw: Int.unsigned w < 256) by (specialize (Hb 0); rewrite Znth_0_cons, Zlength_cons in Hb;
      apply Hb; pose proof (Zlength_nonneg t); lia).
    pose proof (Int.unsigned_range w).
    f_equal.
    + apply Byte.eqm_samerepr. exists (- hrp_val t). change Byte.modulus with 256. lia.
    + rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l.
      apply IH; [lia | ]. intros j Hj. specialize (Hb (j + 1)). rewrite Znth_pos_cons, Z.add_simpl_r in Hb by lia.
      apply Hb. rewrite Zlength_cons. lia.
Qed.

(* the select loop of rp_final *)
Lemma hrp_select_length s g h n : 0 <= n <= Zlength h ->
  Zlength (hrp_loop (hrp_select_step s g) n h) = Zlength h.
Proof.
  intros Hn. apply (hrp_loop_ind _ (fun k l => Zlength l = Zlength h)); [lia | reflexivity | ].
  intros k l Hk Hl. unfold hrp_select_step. rewrite upd_Znth_Zlength; lia.
Qed.

Lemma hrp_select_zero g h : Zlength h = 17 -> hrp_loop (hrp_select_step Int.zero g) 17 h = h.
Proof.
  intros Hh. apply (hrp_loop_ind _ (fun k l => l = h)); [lia | reflexivity | ].
  intros k l Hk ->. unfold hrp_select_step. rewrite Int.and_zero_l, Int.xor_zero.
  apply upd_Znth_triv; [lia | reflexivity].
Qed.

Lemma hrp_select_mone g h : Zlength h = 17 -> Zlength g = 17 -> hrp_loop (hrp_select_step Int.mone g) 17 h = g.
Proof.
  intros Hh Hg.
  assert (H: Zlength (hrp_loop (hrp_select_step Int.mone g) 17 h) = 17 /\
    forall j, 0 <= j < 17 -> Znth j (hrp_loop (hrp_select_step Int.mone g) 17 h) = Znth j g).
  { apply (hrp_loop_ind _ (fun k l => Zlength l = 17 /\ forall j, 0 <= j < k -> Znth j l = Znth j g));
      [lia | split; [exact Hh | intros; lia] | ].
    intros k l Hk [Hl Hj]. unfold hrp_select_step. split; [rewrite upd_Znth_Zlength; lia | ].
    intros j Hj'. destruct (Z.eq_dec j k) as [->|].
    - rewrite upd_Znth_same by lia. rewrite Int.and_mone_l, (Int.xor_commut (Znth k g)), <- Int.xor_assoc,
        Int.xor_idem, Int.xor_zero_l. reflexivity.
    - rewrite upd_Znth_diff by lia. apply Hj. lia. }
  destruct H as [Hl Hj]. apply Znth_eq_ext; [lia | ]. intros j Hj'. apply Hj. lia.
Qed.

Lemma hrp_val_sub16_lt l : Zlength l = 17 -> (forall j, 0 <= j < 16 -> Int.unsigned (Znth j l) < 256) ->
  0 <= hrp_val (sublist 0 16 l) < 2 ^ 128.
Proof.
  intros Hl Hb. split; [apply hrp_val_nonneg | ].
  rewrite <- hrp_pow16. replace 16 with (Zlength (sublist 0 16 l)) at 2 by (rewrite Zlength_sublist; lia).
  apply hrp_val_lt. rewrite Zlength_sublist by lia. intros j Hj. rewrite Znth_sublist by lia.
  apply Hb; lia.
Qed.

Lemma hrp_init_r_explicit b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 :
  hrp_mask 15 15 (hrp_mask 12 252 (hrp_mask 11 15 (hrp_mask 8 252 (hrp_mask 7 15 (hrp_mask 4 252
    (hrp_mask 3 15 (map hrp_u8 [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15] ++ [Int.zero]))))))) =
  [hrp_u8 b0; hrp_u8 b1; hrp_u8 b2; Int.and (hrp_u8 b3) (Int.repr 15); Int.and (hrp_u8 b4) (Int.repr 252);
   hrp_u8 b5; hrp_u8 b6; Int.and (hrp_u8 b7) (Int.repr 15); Int.and (hrp_u8 b8) (Int.repr 252);
   hrp_u8 b9; hrp_u8 b10; Int.and (hrp_u8 b11) (Int.repr 15); Int.and (hrp_u8 b12) (Int.repr 252);
   hrp_u8 b13; hrp_u8 b14; Int.and (hrp_u8 b15) (Int.repr 15); Int.zero].
Proof. reflexivity. Qed.

Lemma hrp_land255 b : Z.land (Byte.unsigned b) 255 = Byte.unsigned b.
Proof.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. apply hrp_byte_range.
Qed.

(* ---------------------------------------------------------------------- *)
(* lengths                                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma hrp_add_length h c : Zlength h = 17 -> Zlength (hrp_add h c) = 17.
Proof.
  intros Hh. unfold hrp_add. rewrite hrp_add_loop_length; lia.
Qed.

Lemma hrp_init_r_length key : Zlength key >= 16 -> Zlength (hrp_init_r key) = 17.
Proof.
  intros Hk. unfold hrp_init_r, hrp_mask.
  assert (L0: Zlength (map hrp_u8 (sublist 0 16 key) ++ [Int.zero]) = 17)
    by (rewrite Zlength_app, Zlength_map, Zlength_sublist by lia; reflexivity).
  repeat rewrite upd_Znth_Zlength; rewrite ?L0; lia.
Qed.

Lemma hrp_mul_length r h c : Zlength h = 17 -> Zlength (hrp_mul r h c) = 17.
Proof.
  intros Hh. unfold hrp_mul. apply hrp_reduce_length.
  unfold hrp_prods. rewrite !Zlength_map, Zlength_correct, seq_length. reflexivity.
Qed.

Lemma hrp_final_h_length h sk : Zlength h = 17 -> Zlength (hrp_final_h h sk) = 17.
Proof.
  intros Hh. unfold hrp_final_h. cbv zeta.
  assert (L1: Zlength (hrp_add h hrp_minusp) = 17) by (apply hrp_add_length; auto).
  apply hrp_add_length. rewrite hrp_select_length; lia.
Qed.

Lemma hrp_final_out_length h sk : Zlength h = 17 -> Zlength (hrp_final_out h sk) = 16.
Proof.
  intros Hh. unfold hrp_final_out.
  rewrite Zlength_map, Zlength_sublist by (try rewrite hrp_final_h_length by auto; lia). reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* correctness                                                             *)
(* ---------------------------------------------------------------------- *)

Lemma hrp_inv_zero : hrp_inv hrp_zero17 /\ hrp_val hrp_zero17 = 0.
Proof.
  split; [ | reflexivity]. split; [reflexivity | ]. unfold hrp_zero17.
  split; [intros j Hj | ]; rewrite Znth_Zrepeat by lia; rewrite Int.unsigned_zero; lia.
Qed.

Lemma hrp_init_r_ok key : 16 <= Zlength key ->
  Zlength (hrp_init_r key) = 17 /\ Forall (fun w => Int.unsigned w <= 255) (hrp_init_r key) /\
  hrp_val (hrp_init_r key) = p1305_r key.
Proof.
  intros Hk.
  assert (Lb: Zlength (sublist 0 16 key) = 16) by (rewrite Zlength_sublist; lia).
  unfold hrp_init_r, p1305_r. remember (sublist 0 16 key) as bs eqn:Ebs. clear Ebs.
  rewrite Zlength_correct in Lb.
  do 16 (destruct bs as [|? bs]; [simpl in Lb; discriminate | ]). destruct bs; [ | simpl in Lb; lia].
  rewrite hrp_init_r_explicit.
  split; [reflexivity | ]. split.
  - repeat (apply Forall_cons; [ | ]); [ .. | apply Forall_nil];
      match goal with
      | |- Int.unsigned (hrp_u8 ?b) <= 255 => rewrite hrp_u8_val; pose proof (hrp_byte_range b); lia
      | |- Int.unsigned (Int.and (hrp_u8 ?b) (Int.repr ?m)) <= 255 =>
          destruct (hrp_and_u8 b m ltac:(lia)) as [E1 E2]; rewrite E1; lia
      | |- Int.unsigned Int.zero <= 255 => rewrite Int.unsigned_zero; lia
      end.
  - cbn [hrp_val le_Z].
    repeat match goal with |- context [Int.unsigned (Int.and (hrp_u8 ?b) (Int.repr ?m))] =>
      rewrite (proj1 (hrp_and_u8 b m ltac:(lia))) end.
    rewrite !hrp_u8_val, Int.unsigned_zero.
    change 21267647620597763993911028882763415551 with
      (255 + 256 * (255 + 256 * (255 + 256 * (15 + 256 * (252 + 256 * (255 + 256 * (255 + 256 * (15 +
       256 * (252 + 256 * (255 + 256 * (255 + 256 * (15 + 256 * (252 + 256 * (255 + 256 * (255 + 256 *
       (15 + 256 * 0)))))))))))))))).
    rewrite !hrp_land_split by (first [apply hrp_byte_range | lia]).
    rewrite !hrp_land255, Z.land_0_l. ring.
Qed.

Lemma hrp_block_c_ok m : Zlength m = 16 ->
  hrp_cblock (hrp_block_c m) /\ hrp_val (hrp_block_c m) = le_Z m + 2 ^ 128.
Proof.
  intros Hm. unfold hrp_block_c. split.
  - split; [rewrite Zlength_app, Zlength_map, Hm; reflexivity | ]. split.
    + intros j Hj. rewrite Znth_app1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia.
      rewrite hrp_u8_val. pose proof (hrp_byte_range (Znth j m)). lia.
    + rewrite Znth_app2 by (rewrite Zlength_map; lia). rewrite Zlength_map, Hm, Z.sub_diag, Znth_0_cons.
      rewrite Int.unsigned_one. lia.
  - rewrite hrp_val_app, hrp_val_u8, Zlength_map, Hm, hrp_pow16. cbn [hrp_val]. rewrite Int.unsigned_one. ring.
Qed.

(* one block: h := (h + c) * r mod 2^130 - 5, and the invariant again *)
Lemma hrp_mul_ok key h c : 16 <= Zlength key -> hrp_inv h -> hrp_cblock c ->
  hrp_inv (hrp_mul (hrp_init_r key) h c) /\
  hrp_val (hrp_mul (hrp_init_r key) h c) mod p1305_p = (hrp_val h + hrp_val c) * p1305_r key mod p1305_p.
Proof.
  intros Hk Hh Hc.
  destruct (hrp_init_r_ok key Hk) as (Lr & Fr & Vr). rewrite Forall_forall in Fr.
  destruct Hh as (Lh & Bh & Bh16). destruct Hc as (Lc & Bc & Bc16).
  assert (Bhc: forall j, 0 <= j < 17 -> Int.unsigned (Znth j h) + Int.unsigned (Znth j c) < 2 ^ 31).
  { intros j Hj. destruct (Z.eq_dec j 16) as [->|]; [lia | ].
    specialize (Bh j ltac:(lia)). specialize (Bc j ltac:(lia)). lia. }
  destruct (hrp_add_spec h c Lh Lc Bhc) as (La & Ba & t & Ht & Va).
  unfold hrp_mul. set (a := hrp_add h c) in *.
  assert (Vh: hrp_val h < 5 * 2 ^ 128).
  { rewrite (hrp_val_split16 h Lh). pose proof (hrp_val_sub16_lt h Lh ltac:(intros j Hj; specialize (Bh j Hj); lia)). lia. }
  assert (Vc: hrp_val c < 2 * 2 ^ 128).
  { rewrite (hrp_val_split16 c Lc). pose proof (hrp_val_sub16_lt c Lc ltac:(intros j Hj; specialize (Bc j Hj); lia)). lia. }
  pose proof (hrp_val_nonneg a).
  assert (Vah: hrp_val a = hrp_val h + hrp_val c) by lia.
  destruct (hrp_prods_ok a (hrp_init_r key) La Lr ltac:(intros j Hj; specialize (Ba j Hj); lia)
    ltac:(intros j Hj; apply Fr; apply Znth_In; lia)) as (Lx & Bx & Bx16 & Vx).
  destruct (hrp_reduce_ok _ Lx Bx Bx16) as (Inv & Vred).
  split; [exact Inv | ]. rewrite Vred, Vx, Vah, Vr. reflexivity.
Qed.

(* the tag: (h mod 2^130 - 5 + s) mod 2^128 *)
Lemma hrp_final_ok h sk : hrp_inv h -> Zlength sk = 16 ->
  hrp_final_out h sk = le_bytes 16 ((hrp_val h mod p1305_p + le_Z sk) mod 2 ^ 128).
Proof.
  intros (Lh & Bh & Bh16) Hsk.
  assert (Vh: 0 <= hrp_val h < 5 * 2 ^ 128).
  { rewrite (hrp_val_split16 h Lh). pose proof (hrp_val_sub16_lt h Lh ltac:(intros j Hj; specialize (Bh j Hj); lia)).
    pose proof (Int.unsigned_range (Znth 16 h)). lia. }
  assert (Fm: Forall (fun w => Int.unsigned w <= 252) hrp_minusp).
  { unfold hrp_minusp. simpl. repeat (apply Forall_cons; [compute; discriminate | ]). apply Forall_nil. }
  rewrite Forall_forall in Fm.
  assert (Lm: Zlength hrp_minusp = 17) by reflexivity.
  assert (Vm: hrp_val hrp_minusp = 5 + 252 * 2 ^ 128) by reflexivity.
  assert (Bhm: forall j, 0 <= j < 17 -> Int.unsigned (Znth j h) + Int.unsigned (Znth j hrp_minusp) < 2 ^ 31).
  { intros j Hj. assert (Int.unsigned (Znth j hrp_minusp) <= 252) by (apply Fm; apply Znth_In; lia).
    destruct (Z.eq_dec j 16) as [->|]; [lia | ]. specialize (Bh j ltac:(lia)). lia. }
  destruct (hrp_add_spec h hrp_minusp Lh Lm Bhm) as (L1 & B1 & t & Ht & V1).
  unfold hrp_final_out, hrp_final_h. cbv zeta.
  set (h1 := hrp_add h hrp_minusp) in *.
  rewrite Vm in V1.
  assert (V1lt: hrp_val h1 < 2 ^ 136) by (rewrite <- hrp_pow17, <- L1; apply hrp_val_lt; rewrite L1; exact B1).
  pose proof (hrp_val_nonneg h1).
  pose proof (hrp_val_sub16_lt h1 L1 ltac:(intros j Hj; apply B1; lia)) as S1.
  pose proof (hrp_val_split16 h1 L1) as Sp1.
  pose proof (B1 16 ltac:(lia)) as B116. pose proof (Int.unsigned_range (Znth 16 h1)).
  assert (Hsh: Int.unsigned (Int.shru (Znth 16 h1) (Int.repr 7)) = Int.unsigned (Znth 16 h1) / 128)
    by (rewrite hrp_shru by lia; reflexivity).
  set (s := Int.neg (Int.shru (Znth 16 h1) (Int.repr 7))).
  assert (H2: exists h2, hrp_loop (hrp_select_step s h) 17 h1 = h2 /\ Zlength h2 = 17 /\
    (forall j, 0 <= j < 17 -> Int.unsigned (Znth j h2) < 256) /\ hrp_val h2 = hrp_val h mod p1305_p).
  { destruct (Z_lt_le_dec (hrp_val h) p1305_p) as [Hlt | Hge]; unfold p1305_p in *.
    - assert (t = 0) by lia. subst t.
      assert (E: Int.unsigned (Znth 16 h1) / 128 = 1) by (symmetry; apply Z.div_unique with (Int.unsigned (Znth 16 h1) - 128); lia).
      assert (Es: s = Int.mone).
      { unfold s. rewrite <- (Int.repr_unsigned (Int.shru _ _)), Hsh, E. reflexivity. }
      exists h. rewrite Es, hrp_select_mone by auto. split; [reflexivity | ]. split; [exact Lh | ]. split.
      + intros j Hj. destruct (Z.eq_dec j 16) as [->|]; [lia | ]. specialize (Bh j ltac:(lia)). lia.
      + symmetry. apply Z.mod_small. lia.
    - assert (t = 1) by lia. subst t.
      assert (E: Int.unsigned (Znth 16 h1) / 128 = 0) by (apply Z.div_small; lia).
      assert (Es: s = Int.zero).
      { unfold s. rewrite <- (Int.repr_unsigned (Int.shru _ _)), Hsh, E. reflexivity. }
      exists h1. rewrite Es, hrp_select_zero by auto. split; [reflexivity | ]. split; [exact L1 | ]. split; [exact B1 | ].
      replace (hrp_val h) with (hrp_val h - (2 ^ 130 - 5) + 1 * (2 ^ 130 - 5)) by ring.
      rewrite Z_mod_plus_full, Z.mod_small by lia. lia. }
  destruct H2 as (h2 & -> & L2 & B2 & V2).
  set (c := map hrp_u8 sk ++ [Int.zero]).
  assert (Lc: Zlength c = 17) by (unfold c; rewrite Zlength_app, Zlength_map, Hsk; reflexivity).
  assert (Bc: forall j, 0 <= j < 17 -> Int.unsigned (Znth j c) <= 255).
  { intros j Hj. unfold c. destruct (Z_lt_le_dec j 16).
    - rewrite Znth_app1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia. rewrite hrp_u8_val.
      pose proof (hrp_byte_range (Znth j sk)). lia.
    - rewrite Znth_app2 by (rewrite Zlength_map; lia). rewrite Zlength_map, Hsk.
      replace (j - 16) with 0 by lia. rewrite Znth_0_cons, Int.unsigned_zero. lia. }
  assert (Vc: hrp_val c = le_Z sk).
  { unfold c. rewrite hrp_val_app, hrp_val_u8. cbn [hrp_val]. rewrite Int.unsigned_zero. lia. }
  destruct (hrp_add_spec h2 c L2 Lc ltac:(intros j Hj; specialize (B2 j Hj); specialize (Bc j Hj); lia))
    as (L3 & B3 & t3 & Ht3 & V3).
  set (h3 := hrp_add h2 c) in *.
  rewrite (hrp_bytes_le 16 (sublist 0 16 h3)).
  2: { rewrite Zlength_sublist by lia. reflexivity. }
  2: { rewrite Zlength_sublist by lia. intros j Hj. rewrite Znth_sublist by lia. apply B3. lia. }
  f_equal. rewrite <- V2, <- Vc, <- V3, (hrp_val_split16 h3 L3).
  pose proof (hrp_val_sub16_lt h3 L3 ltac:(intros j Hj; apply B3; lia)).
  replace (hrp_val (sublist 0 16 h3) + 2 ^ 128 * Int.unsigned (Znth 16 h3) + 2 ^ 136 * t3)
    with (hrp_val (sublist 0 16 h3) + (Int.unsigned (Znth 16 h3) + 256 * t3) * 2 ^ 128) by lia.
  rewrite Z_mod_plus_full, Z.mod_small by lia. reflexivity.
Qed.

(* every lemma above *)
Theorem hrp1305_math3_all : True.
Proof.
  pose proof hrp_add_length. pose proof hrp_init_r_length. pose proof hrp_mul_length.
  pose proof hrp_final_h_length. pose proof hrp_final_out_length. pose proof hrp_inv_zero.
  pose proof hrp_init_r_ok. pose proof hrp_block_c_ok. pose proof hrp_mul_ok. pose proof hrp_final_ok.
  exact I.
Qed.
