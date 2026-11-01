(* a copy of hp1305_refmath3_pf.v, with
   hpf_init_r_ok taken from hp1305_ref_initr3.v (hpr_init_r_ok), and one slow `replace ... by ring` in
   hpf_prods_ok (> 300 s here) replaced by rewrites; the unused hpf_mul_length, hpf_final_h_length and
   hpf_final_out_length dropped (the first exhausted memory), one step of hpf_block_c_ok fixed; everything
   else unchanged. *)
(* proven copies (prefix hpf_) of hrp1305_math3.v's then unproved lemmas.  Same statements, only the definitions of
   hrp1305_math3.v are used.  Plan:
   - a generic carry loop (hpf_cstep: u += f(h[j]); h[j] = u & 255; u >>= 8) covering rp_add and the carry
     passes: value identity hrp_val h' + u' 256^n = hrp_val h + u + sum_{j<n} (f(h_j) - h_j) 256^j, no wrap;
   - the products x_i = sum_j h_j coef(i,j) without wrap (all limbs <= 255, 17 * 255 * 320 * 255 < 2^32), and
     the polynomial identity hrp_val x = hrp_val h * hrp_val r - 64 p Q (2^136 = 320 + 64 p), by ring;
   - hrp_reduce keeps the value mod p (2^130 = 5 mod p) and ends with limbs <= 255, limb 16 <= 4;
   - rp_final: h + (2^136 - p) has bit 7 of limb 16 set iff h < p; the select picks h or h - p. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.aead.aead_model.
Require Import WgNoise.proof.harness.hrp1305_math3.
Require Import WgNoise.proof.harness.prim_poly1305.hp1305_ref_initr3.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Int facts                                                               *)
(* ---------------------------------------------------------------------- *)

Lemma hpf_and255 x : Int.unsigned (Int.and x (Int.repr 255)) = Int.unsigned x mod 256.
Proof.
  replace (Int.repr 255) with (Int.sub (Int.repr 256) Int.one) by reflexivity.
  rewrite <- (Int.modu_and x (Int.repr 256) (Int.repr 8)) by reflexivity.
  unfold Int.modu. rewrite (Int.unsigned_repr 256) by rep_lia.
  apply Int.unsigned_repr. pose proof (Z.mod_pos_bound (Int.unsigned x) 256). rep_lia.
Qed.

Lemma hpf_and3 x : Int.unsigned (Int.and x (Int.repr 3)) = Int.unsigned x mod 4.
Proof.
  replace (Int.repr 3) with (Int.sub (Int.repr 4) Int.one) by reflexivity.
  rewrite <- (Int.modu_and x (Int.repr 4) (Int.repr 2)) by reflexivity.
  unfold Int.modu. rewrite (Int.unsigned_repr 4) by rep_lia.
  apply Int.unsigned_repr. pose proof (Z.mod_pos_bound (Int.unsigned x) 4). rep_lia.
Qed.

Lemma hpf_shru x k : 0 <= k < 32 -> Int.unsigned (Int.shru x (Int.repr k)) = Int.unsigned x / 2 ^ k.
Proof.
  intros Hk. rewrite Int.shru_div_two_p, (Int.unsigned_repr k) by rep_lia. rewrite two_p_correct.
  apply Int.unsigned_repr. pose proof (Int.unsigned_range x).
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia|]. apply Z.le_trans with (Int.unsigned x); [|rep_lia].
  apply Z.div_le_upper_bound; nia.
Qed.

Lemma hpf_add x y : Int.unsigned x + Int.unsigned y <= Int.max_unsigned ->
  Int.unsigned (Int.add x y) = Int.unsigned x + Int.unsigned y.
Proof.
  intros H. rewrite Int.add_unsigned. apply Int.unsigned_repr. rep_lia.
Qed.

Lemma hpf_mul x y : Int.unsigned x * Int.unsigned y <= Int.max_unsigned ->
  Int.unsigned (Int.mul x y) = Int.unsigned x * Int.unsigned y.
Proof.
  intros H. unfold Int.mul. apply Int.unsigned_repr. pose proof (Int.unsigned_range x).
  pose proof (Int.unsigned_range y). nia.
Qed.

(* ---------------------------------------------------------------------- *)
(* values                                                                  *)
(* ---------------------------------------------------------------------- *)

Lemma hpf_val_app a b : hrp_val (a ++ b) = hrp_val a + 256 ^ Zlength a * hrp_val b.
Proof.
  induction a as [|w t IH]; simpl.
  - lia.
  - rewrite Zlength_cons, IH, Z.pow_succ_r by (apply Zlength_nonneg). lia.
Qed.

Lemma hpf_val_upd l j x : 0 <= j < Zlength l ->
  hrp_val (upd_Znth j l x) = hrp_val l + (Int.unsigned x - Int.unsigned (Znth j l)) * 256 ^ j.
Proof.
  intros Hj. rewrite upd_Znth_unfold by auto.
  assert (E : l = sublist 0 j l ++ [Znth j l] ++ sublist (j + 1) (Zlength l) l) by list_solve.
  remember (sublist 0 j l) as A. remember (sublist (j + 1) (Zlength l) l) as C.
  assert (HA : Zlength A = j) by (subst A; rewrite Zlength_sublist; lia).
  replace (hrp_val l) with (hrp_val (A ++ [Znth j l] ++ C)) by (rewrite <- E; reflexivity).
  rewrite !hpf_val_app, HA. simpl. ring.
Qed.

Definition hpf_b255 (l: list int) : Prop := forall j, 0 <= j < Zlength l -> Int.unsigned (Znth j l) <= 255.

Lemma hpf_val_range l : hpf_b255 l -> 0 <= hrp_val l <= 256 ^ Zlength l - 1.
Proof.
  induction l as [|w t IH]; intros H; simpl.
  - simpl. lia.
  - rewrite Zlength_cons, Z.pow_succ_r by (apply Zlength_nonneg).
    assert (Hw : Int.unsigned w <= 255) by (specialize (H 0); rewrite Znth_0_cons in H; apply H;
      rewrite Zlength_cons; pose proof (Zlength_nonneg t); lia).
    assert (Ht : hpf_b255 t).
    { intros j Hj. specialize (H (j + 1)). rewrite Znth_pos_cons in H by lia.
      replace (j + 1 - 1) with j in H by lia. apply H. rewrite Zlength_cons. lia. }
    specialize (IH Ht). pose proof (Int.unsigned_range w). lia.
Qed.

Lemma hpf_val_nonneg l : 0 <= hrp_val l.
Proof. induction l; simpl; [lia|]. pose proof (Int.unsigned_range a). lia. Qed.

(* a 17-limb list: the low 16 limbs and limb 16 *)
Lemma hpf_val_split l : Zlength l = 17 ->
  hrp_val l = hrp_val (sublist 0 16 l) + 2 ^ 128 * Int.unsigned (Znth 16 l).
Proof.
  intros Hl. rewrite <- (sublist_same 0 17 l) at 1 by auto.
  rewrite (sublist_split 0 16 17) by lia. rewrite sublist_len_1 by lia.
  rewrite hpf_val_app, Zlength_sublist by lia. simpl. lia.
Qed.

Lemma hpf_val_low l : Zlength l = 17 -> (forall j, 0 <= j < 16 -> Int.unsigned (Znth j l) <= 255) ->
  0 <= hrp_val (sublist 0 16 l) <= 2 ^ 128 - 1.
Proof.
  intros Hl H. pose proof (hpf_val_range (sublist 0 16 l)) as R.
  rewrite Zlength_sublist in R by lia. apply R.
  intros j Hj. rewrite Zlength_sublist in Hj by lia. rewrite Znth_sublist by lia. apply H. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* sums and loops                                                          *)
(* ---------------------------------------------------------------------- *)

Lemma hpf_loop_ext {A: Type} (f g: A -> Z -> A) n a :
  (forall s j, f s j = g s j) -> hrp_loop f n a = hrp_loop g n a.
Proof.
  intros H. unfold hrp_loop. generalize (map Z.of_nat (seq 0 (Z.to_nat n))) a.
  induction l as [|x t IH]; intros b; simpl; auto. rewrite H. apply IH.
Qed.

(* sum_{j<n} d j 256^j *)
Definition hpf_psum (d: Z -> Z) (n: Z) : Z := hrp_loop (fun acc j => acc + d j * 256 ^ j) n 0.

Lemma hpf_psum_succ d n : 0 <= n -> hpf_psum d (n + 1) = hpf_psum d n + d n * 256 ^ n.
Proof. intros Hn. unfold hpf_psum. rewrite hrp_loop_succ by auto. reflexivity. Qed.

Lemma hpf_psum_ext d1 d2 n : 0 <= n -> (forall j, 0 <= j < n -> d1 j = d2 j) -> hpf_psum d1 n = hpf_psum d2 n.
Proof.
  intros Hn. pattern n. apply natlike_ind; [| |exact Hn]; clear n Hn.
  - intros _. reflexivity.
  - intros n Hn IH H. rewrite <- Z.add_1_r, !hpf_psum_succ by lia.
    rewrite IH, H by (try intros; try apply H; lia). reflexivity.
Qed.

Lemma hpf_psum_zero n : 0 <= n -> hpf_psum (fun _ => 0) n = 0.
Proof.
  intros Hn. pattern n. apply natlike_ind; [| |exact Hn]; clear n Hn.
  - reflexivity.
  - intros n Hn IH. rewrite <- Z.add_1_r, hpf_psum_succ, IH by lia. lia.
Qed.

Lemma hpf_psum_val l n : 0 <= n <= Zlength l ->
  hpf_psum (fun j => Int.unsigned (Znth j l)) n = hrp_val (sublist 0 n l).
Proof.
  intros Hn. destruct Hn as [Hn Hn']. revert Hn'. pattern n. apply natlike_ind; [| |exact Hn]; clear n Hn.
  - intros _. reflexivity.
  - intros n Hn IH Hn'. rewrite <- Z.add_1_r, hpf_psum_succ, IH by lia.
    rewrite (sublist_split 0 n (n + 1)) by lia. rewrite sublist_len_1 by lia.
    rewrite hpf_val_app, Zlength_sublist by lia. simpl. rewrite Z.sub_0_r. ring.
Qed.

(* the generic carry loop: u += f(h[j], j); h[j] = u & 255; u >>= 8 *)
Definition hpf_cstep (f: int -> Z -> int) (s: list int * int) (j: Z) : list int * int :=
  let u := Int.add (snd s) (f (Znth j (fst s)) j) in
  (upd_Znth j (fst s) (Int.and u (Int.repr 255)), Int.shru u (Int.repr 8)).

Lemma hpf_cloop f l0 u0 M n : Zlength l0 = 17 -> 0 <= n <= 17 -> 0 <= M < 2 ^ 31 ->
  Int.unsigned u0 <= M -> (forall j, 0 <= j < n -> Int.unsigned (f (Znth j l0) j) <= M) ->
  let s := hrp_loop (hpf_cstep f) n (l0, u0) in
  Zlength (fst s) = 17 /\
  (forall j, n <= j < 17 -> Znth j (fst s) = Znth j l0) /\
  (forall j, 0 <= j < n -> Int.unsigned (Znth j (fst s)) <= 255) /\
  Int.unsigned (snd s) <= M /\
  hrp_val (fst s) + Int.unsigned (snd s) * 256 ^ n =
    hrp_val l0 + Int.unsigned u0 + hpf_psum (fun j => Int.unsigned (f (Znth j l0) j) - Int.unsigned (Znth j l0)) n.
Proof.
  intros Hl Hn HM Hu. change (2 ^ 31) with 2147483648 in HM. destruct Hn as [Hn Hn17]. revert Hn17.
  pattern n. apply natlike_ind; [| |exact Hn]; clear n Hn.
  - intros _ _. simpl. unfold hpf_psum. rewrite !hrp_loop_0. repeat split; auto; intros; lia.
  - intros n Hn IH Hn17 Hf.
    destruct IH as (IH1 & IH2 & IH3 & IH4 & IH5); [lia | intros; apply Hf; lia |].
    rewrite <- Z.add_1_r, hrp_loop_succ by lia.
    set (s := hrp_loop (hpf_cstep f) n (l0, u0)) in *.
    unfold hpf_cstep. cbv beta zeta. cbn [fst snd].
    rewrite (IH2 n) by lia.
    set (a := f (Znth n l0) n). set (u := snd s) in *. set (l := fst s) in *.
    assert (Ha : Int.unsigned a <= M) by (apply Hf; lia).
    pose proof (Int.unsigned_range a). pose proof (Int.unsigned_range u).
    assert (HU : Int.unsigned (Int.add u a) = Int.unsigned u + Int.unsigned a) by (apply hpf_add; rep_lia).
    set (U := Int.add u a) in *.
    assert (HS : Int.unsigned (Int.shru U (Int.repr 8)) = Int.unsigned U / 256) by (apply hpf_shru; lia).
    pose proof (Z.div_mod (Int.unsigned U) 256). pose proof (Z.mod_pos_bound (Int.unsigned U) 256).
    split; [|split; [|split; [|split]]].
    + rewrite Zlength_upd_Znth. auto.
    + intros j Hj. rewrite upd_Znth_diff by lia. apply IH2. lia.
    + intros j Hj. destruct (Z.eq_dec j n) as [->|Hjn].
      * rewrite upd_Znth_same by lia. rewrite hpf_and255. lia.
      * rewrite upd_Znth_diff by lia. apply IH3. lia.
    + rewrite HS. apply Z.div_le_upper_bound; lia.
    + rewrite hpf_val_upd by lia. rewrite hpf_and255, HS, hpf_psum_succ by lia.
      rewrite (IH2 n) by lia. rewrite Z.pow_add_r by lia. change (256 ^ 1) with 256.
      set (ps := hpf_psum _ n) in *. set (P := 256 ^ n) in *.
      assert (E : Int.unsigned U mod 256 = Int.unsigned U - 256 * (Int.unsigned U / 256)) by lia.
      rewrite E. set (q := Int.unsigned U / 256). rewrite HU.
      assert (Eps : ps = hrp_val l + Int.unsigned u * P - hrp_val l0 - Int.unsigned u0) by lia.
      rewrite Eps. fold a. ring.
Qed.

Lemma hpf_b17_psum (d: Z -> Z) : (forall j, d j = 0) -> hpf_psum d 17 = 0.
Proof.
  intros H. rewrite (hpf_psum_ext d (fun _ => 0)) by (auto; lia). apply hpf_psum_zero. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* rp_add                                                                  *)
(* ---------------------------------------------------------------------- *)

Lemma hpf_add_ok h c : Zlength h = 17 -> Zlength c = 17 ->
  (forall j, 0 <= j < 17 -> Int.unsigned (Znth j h) <= 255) ->
  (forall j, 0 <= j < 17 -> Int.unsigned (Znth j c) <= 255) ->
  Zlength (hrp_add h c) = 17 /\ (forall j, 0 <= j < 17 -> Int.unsigned (Znth j (hrp_add h c)) <= 255) /\
  exists u, 0 <= u /\ hrp_val (hrp_add h c) + u * 2 ^ 136 = hrp_val h + hrp_val c.
Proof.
  intros Hh Hc Bh Bc. unfold hrp_add.
  rewrite (hpf_loop_ext _ (hpf_cstep (fun x j => Int.add x (Znth j c)))) by reflexivity.
  assert (Hj : forall j, 0 <= j < 17 -> Int.unsigned (Int.add (Znth j h) (Znth j c)) =
                                       Int.unsigned (Znth j h) + Int.unsigned (Znth j c)).
  { intros j Hj. apply hpf_add. specialize (Bh j Hj). specialize (Bc j Hj). rep_lia. }
  destruct (hpf_cloop (fun x j => Int.add x (Znth j c)) h Int.zero 511 17) as (L1 & L2 & L3 & L4 & L5);
    try lia; try (rewrite Int.unsigned_zero; lia).
  { intros j Hj'. rewrite Hj by lia. specialize (Bh j Hj'). specialize (Bc j Hj'). lia. }
  split; [auto | split; [intros j Hj'; apply L3; lia |]].
  exists (Int.unsigned (snd (hrp_loop (hpf_cstep (fun x j => Int.add x (Znth j c))) 17 (h, Int.zero)))).
  split; [apply Int.unsigned_range|].
  assert (Vc : hrp_val c = hpf_psum (fun j => Int.unsigned (Znth j c)) 17)
    by (rewrite hpf_psum_val, sublist_same; auto; lia).
  change (2 ^ 136) with (256 ^ 17). rewrite L5, Int.unsigned_zero, Vc.
  rewrite Z.add_0_r. f_equal. apply hpf_psum_ext; [lia|]. intros j Hj'. rewrite Hj by lia. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* the carry passes                                                        *)
(* ---------------------------------------------------------------------- *)

Lemma hpf_psum_zero' d n : 0 <= n -> (forall j, 0 <= j < n -> d j = 0) -> hpf_psum d n = 0.
Proof. intros Hn H. rewrite (hpf_psum_ext d (fun _ => 0)) by auto. apply hpf_psum_zero. auto. Qed.

Lemma hpf_reduce_ok x : Zlength x = 17 -> (forall j, 0 <= j < 17 -> Int.unsigned (Znth j x) <= 2 ^ 29) ->
  hrp_inv (hrp_reduce x) /\ hrp_val (hrp_reduce x) mod p1305_p = hrp_val x mod p1305_p.
Proof.
  intros Hx Bx. unfold hrp_reduce. cbv zeta.
  rewrite (hpf_loop_ext hrp_carry_step (hpf_cstep (fun w _ => w)) 16 (x, Int.zero)) by reflexivity.
  rewrite (hpf_loop_ext hrp_carry_step (hpf_cstep (fun w _ => w))) by reflexivity.
  assert (P128 : 2 ^ 128 = 340282366920938463463374607431768211456) by reflexivity.
  assert (P16 : 256 ^ 16 = 2 ^ 128) by reflexivity.
  (* pass 1 *)
  destruct (hpf_cloop (fun w _ => w) x Int.zero (2 ^ 29) 16) as (L1 & L2 & L3 & L4 & L5);
    try lia; try (rewrite Int.unsigned_zero; lia).
  { intros j Hj. apply Bx. lia. }
  set (s1 := hrp_loop (hpf_cstep (fun w _ => w)) 16 (x, Int.zero)) in *.
  rewrite hpf_psum_zero' in L5 by (auto; lia). rewrite Int.unsigned_zero in L5.
  set (l1 := fst s1) in *. set (u1 := snd s1) in *.
  assert (X16 : Znth 16 l1 = Znth 16 x) by (apply L2; lia).
  rewrite X16.
  pose proof (Bx 16 ltac:(lia)) as B16. pose proof (Int.unsigned_range u1). pose proof (Int.unsigned_range (Znth 16 x)).
  change (2 ^ 29) with 536870912 in *.
  assert (HU2 : Int.unsigned (Int.add u1 (Znth 16 x)) = Int.unsigned u1 + Int.unsigned (Znth 16 x))
    by (apply hpf_add; rep_lia).
  set (U2 := Int.add u1 (Znth 16 x)) in *.
  assert (HU2s : Int.unsigned (Int.shru U2 (Int.repr 2)) = Int.unsigned U2 / 4) by (apply (hpf_shru U2 2); lia).
  assert (HU3 : Int.unsigned (Int.mul (Int.repr 5) (Int.shru U2 (Int.repr 2))) = 5 * (Int.unsigned U2 / 4)).
  { rewrite hpf_mul; rewrite HU2s, Int.unsigned_repr by rep_lia; [lia|].
    pose proof (Z.div_le_upper_bound (Int.unsigned U2) 4 (2 ^ 28)). rep_lia. }
  set (U3 := Int.mul (Int.repr 5) (Int.shru U2 (Int.repr 2))) in *.
  set (h2 := upd_Znth 16 l1 (Int.and U2 (Int.repr 3))).
  assert (H2len : Zlength h2 = 17) by (unfold h2; rewrite Zlength_upd_Znth; auto).
  assert (H2lo : forall j, 0 <= j < 16 -> Znth j h2 = Znth j l1) by (intros; unfold h2; rewrite upd_Znth_diff; auto; lia).
  assert (H216 : Int.unsigned (Znth 16 h2) = Int.unsigned U2 mod 4)
    by (unfold h2; rewrite upd_Znth_same by lia; apply hpf_and3).
  (* pass 2 *)
  destruct (hpf_cloop (fun w _ => w) h2 U3 (2 ^ 31 - 1) 16) as (M1 & M2 & M3 & M4 & M5); try lia.
  { rewrite HU3. pose proof (Z.div_le_upper_bound (Int.unsigned U2) 4 (2 ^ 28)). lia. }
  { intros j Hj. rewrite H2lo by lia. pose proof (L3 j Hj). lia. }
  set (s3 := hrp_loop (hpf_cstep (fun w _ => w)) 16 (h2, U3)) in *.
  rewrite hpf_psum_zero' in M5 by (auto; lia).
  set (l3 := fst s3) in *. set (uf := snd s3) in *.
  assert (L316 : Znth 16 l3 = Znth 16 h2) by (apply M2; lia).
  (* the carry out of pass 2 is at most 1 *)
  assert (Huf : Int.unsigned uf <= 1).
  { rewrite (hpf_val_split l3), (hpf_val_split h2), L316, P16 in M5 by auto.
    pose proof (hpf_val_low l3 M1 M3).
    pose proof (hpf_val_low h2 H2len ltac:(intros j Hj; rewrite H2lo by lia; apply L3; lia)).
    rewrite P128 in *. rewrite HU3 in M5. pose proof (Int.unsigned_range uf).
    assert (Int.unsigned U2 / 4 <= 2 ^ 28) by (apply Z.div_le_upper_bound; lia). lia. }
  assert (HF : Int.unsigned (Int.add uf (Znth 16 l3)) = Int.unsigned uf + Int.unsigned U2 mod 4).
  { rewrite hpf_add; rewrite L316, H216; [lia|]. pose proof (Z.mod_pos_bound (Int.unsigned U2) 4). rep_lia. }
  split.
  - split; [rewrite Zlength_upd_Znth; auto | split].
    + intros j Hj. rewrite upd_Znth_diff by lia. apply M3. lia.
    + rewrite upd_Znth_same by lia. rewrite HF. pose proof (Z.mod_pos_bound (Int.unsigned U2) 4). lia.
  - rewrite hpf_val_upd by lia. rewrite HF, L316, H216.
    replace (hrp_val l3) with (hrp_val h2 + Int.unsigned U3 - Int.unsigned uf * 256 ^ 16) by lia.
    unfold h2. rewrite hpf_val_upd by lia. rewrite hpf_and3, X16, HU3.
    replace (hrp_val l1) with (hrp_val x - Int.unsigned u1 * 256 ^ 16) by lia.
    pose proof (Z.div_mod (Int.unsigned U2) 4 ltac:(lia)).
    replace (hrp_val x - Int.unsigned u1 * 256 ^ 16 +
       (Int.unsigned U2 mod 4 - Int.unsigned (Znth 16 x)) * 256 ^ 16 + 5 * (Int.unsigned U2 / 4) -
       Int.unsigned uf * 256 ^ 16 + (Int.unsigned uf + Int.unsigned U2 mod 4 - Int.unsigned U2 mod 4) * 256 ^ 16)
      with (hrp_val x + (- (Int.unsigned U2 / 4)) * p1305_p)
      by (unfold p1305_p; rewrite P16; change (2 ^ 130) with (4 * 2 ^ 128); nia).
    apply Z_mod_plus_full.
Qed.

(* ---------------------------------------------------------------------- *)
(* the products                                                            *)
(* ---------------------------------------------------------------------- *)

Definition hpf_zc (r: list int) (i j: Z) : Z :=
  if Z_le_dec j i then Int.unsigned (Znth (i - j) r) else 320 * Int.unsigned (Znth (i + 17 - j) r).

Lemma hpf_coef_ok r i j : (forall k, 0 <= k < 17 -> Int.unsigned (Znth k r) <= 255) ->
  0 <= i < 17 -> 0 <= j < 17 ->
  Int.unsigned (hrp_coef r i j) = hpf_zc r i j /\ 0 <= hpf_zc r i j <= 81600.
Proof.
  intros Br Hi Hj. unfold hrp_coef, hpf_zc. destruct (Z_le_dec j i).
  - pose proof (Br (i - j) ltac:(lia)). pose proof (Int.unsigned_range (Znth (i - j) r)). split; auto; lia.
  - pose proof (Br (i + 17 - j) ltac:(lia)). pose proof (Int.unsigned_range (Znth (i + 17 - j) r)).
    rewrite hpf_mul; rewrite Int.unsigned_repr by rep_lia; [split; [auto | lia]|]. rep_lia.
Qed.

(* x[i] as a number *)
Definition hpf_X (h r: list int) (i: Z) : Z :=
  hrp_loop (fun acc j => acc + Int.unsigned (Znth j h) * hpf_zc r i j) 17 0.

Lemma hpf_prod_ok h r i : (forall k, 0 <= k < 17 -> Int.unsigned (Znth k h) <= 255) ->
  (forall k, 0 <= k < 17 -> Int.unsigned (Znth k r) <= 255) -> 0 <= i < 17 ->
  Int.unsigned (hrp_prod h r i) = hpf_X h r i /\ 0 <= hpf_X h r i <= 17 * 20808000.
Proof.
  intros Bh Br Hi. unfold hrp_prod, hpf_X.
  assert (G : forall n, 0 <= n -> n <= 17 ->
    Int.unsigned (hrp_loop (hrp_prod_step h r i) n Int.zero) =
      hrp_loop (fun acc j => acc + Int.unsigned (Znth j h) * hpf_zc r i j) n 0 /\
    0 <= hrp_loop (fun acc j => acc + Int.unsigned (Znth j h) * hpf_zc r i j) n 0 <= n * 20808000).
  { intros n Hn. pattern n. apply natlike_ind; [| |exact Hn]; clear n Hn.
    - intros _. rewrite !hrp_loop_0, Int.unsigned_zero. lia.
    - intros n Hn IH Hn17. destruct IH as [IH1 IH2]; [lia|].
      rewrite <- Z.add_1_r, !hrp_loop_succ by lia.
      change (hrp_prod_step h r i (hrp_loop (hrp_prod_step h r i) n Int.zero) n) with
        (Int.add (hrp_loop (hrp_prod_step h r i) n Int.zero) (Int.mul (Znth n h) (hrp_coef r i n))).
      destruct (hpf_coef_ok r i n Br Hi ltac:(lia)) as [C1 C2].
      pose proof (Bh n ltac:(lia)). pose proof (Int.unsigned_range (Znth n h)).
      assert (Hb : 0 <= Int.unsigned (Znth n h) * hpf_zc r i n <= 255 * 81600)
        by (split; [apply Z.mul_nonneg_nonneg | apply Z.mul_le_mono_nonneg]; lia).
      assert (Hm : Int.unsigned (Int.mul (Znth n h) (hrp_coef r i n)) = Int.unsigned (Znth n h) * hpf_zc r i n)
        by (rewrite hpf_mul; rewrite C1; [lia | rep_lia]).
      rewrite hpf_add; rewrite Hm, IH1; [lia | rep_lia]. }
  apply G; lia.
Qed.

Lemma hpf_val_map17 (g: Z -> int) :
  hrp_val (map g (map Z.of_nat (seq 0 17))) = hpf_psum (fun i => Int.unsigned (g i)) 17.
Proof. unfold hpf_psum, hrp_loop. simpl. rewrite ?Z.pow_pos_fold. ring. Qed.

(* the polynomial identity over limb functions: x = h * r - 64 p Q, where Q collects the products
   h_j r_k with j + k >= 17 (folded onto limb j + k - 17 with 320 = 2^136 - 64 p) *)
Lemma hpf_gpoly (hz rz: Z -> Z) :
  hpf_psum (fun i => hrp_loop (fun acc j => acc + hz j *
      (if Z_le_dec j i then rz (i - j) else 320 * rz (i + 17 - j))) 17 0) 17 +
  64 * p1305_p * hpf_psum (fun i => hrp_loop (fun acc j => acc +
      (if Z_le_dec j i then 0 else hz j * rz (i + 17 - j))) 17 0) 17 =
  hpf_psum hz 17 * hpf_psum rz 17.
Proof. unfold hpf_psum, hrp_loop, p1305_p. cbn -[Z.mul Z.pow]. ring. Qed.

Definition hpf_Q (h r: list int) : Z :=
  hpf_psum (fun i => hrp_loop (fun acc j => acc +
    (if Z_le_dec j i then 0 else Int.unsigned (Znth j h) * Int.unsigned (Znth (i + 17 - j) r))) 17 0) 17.

Lemma hpf_poly h r : Zlength h = 17 -> Zlength r = 17 ->
  hpf_psum (hpf_X h r) 17 + 64 * p1305_p * hpf_Q h r = hrp_val h * hrp_val r.
Proof.
  intros Hh Hr.
  assert (Vh : hrp_val h = hpf_psum (fun j => Int.unsigned (Znth j h)) 17)
    by (rewrite hpf_psum_val, sublist_same; auto; lia).
  assert (Vr : hrp_val r = hpf_psum (fun j => Int.unsigned (Znth j r)) 17)
    by (rewrite hpf_psum_val, sublist_same; auto; lia).
  rewrite Vh, Vr.
  exact (hpf_gpoly (fun j => Int.unsigned (Znth j h)) (fun k => Int.unsigned (Znth k r))).
Qed.

(* ---------------------------------------------------------------------- *)
(* rp_mul                                                                  *)
(* ---------------------------------------------------------------------- *)

Lemma hpf_prods_ok h r : Zlength h = 17 -> Zlength r = 17 ->
  (forall k, 0 <= k < 17 -> Int.unsigned (Znth k h) <= 255) ->
  (forall k, 0 <= k < 17 -> Int.unsigned (Znth k r) <= 255) ->
  Zlength (hrp_prods h r) = 17 /\
  (forall i, 0 <= i < 17 -> Int.unsigned (Znth i (hrp_prods h r)) <= 2 ^ 29) /\
  hrp_val (hrp_prods h r) mod p1305_p = hrp_val h * hrp_val r mod p1305_p.
Proof.
  intros Hh Hr Bh Br. split; [reflexivity | split].
  - intros i Hi. unfold hrp_prods.
    assert (L17 : Zlength (map Z.of_nat (seq 0 17)) = 17) by reflexivity.
    rewrite Znth_map by (rewrite L17; lia).
    replace (Znth i (map Z.of_nat (seq 0 17))) with i
      by (unfold Znth; destruct (Z_lt_dec i 0); [lia|];
          rewrite (map_nth Z.of_nat (seq 0 17) 0%nat), seq_nth by lia; rewrite Nat.add_0_l, Z2Nat.id; lia).
    destruct (hpf_prod_ok h r i Bh Br Hi) as [-> B]. change (2 ^ 29) with 536870912. lia.
  - unfold hrp_prods. rewrite hpf_val_map17.
    rewrite (hpf_psum_ext _ (hpf_X h r)) by (try lia; intros i Hi; apply hpf_prod_ok; auto).
    rewrite <- (hpf_poly h r Hh Hr).
    rewrite <- (Z.mul_assoc 64 p1305_p), (Z.mul_comm p1305_p), Z.mul_assoc.
    rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma hpf_mul_ok key h c : 16 <= Zlength key -> hrp_inv h -> hrp_cblock c ->
  hrp_inv (hrp_mul (hrp_init_r key) h c) /\
  hrp_val (hrp_mul (hrp_init_r key) h c) mod p1305_p = (hrp_val h + hrp_val c) * p1305_r key mod p1305_p.
Proof.
  intros Hk (Hh & Bh & Bh16) (Hc & Bc & Bc16).
  destruct (hpr_init_r_ok key Hk) as (Hr & Br & Vr).
  assert (Bh' : forall j, 0 <= j < 17 -> Int.unsigned (Znth j h) <= 255)
    by (intros j Hj; destruct (Z.eq_dec j 16); [subst; lia | apply Bh; lia]).
  assert (Bc' : forall j, 0 <= j < 17 -> Int.unsigned (Znth j c) <= 255)
    by (intros j Hj; destruct (Z.eq_dec j 16); [subst; lia | apply Bc; lia]).
  assert (Br' : forall j, 0 <= j < 17 -> Int.unsigned (Znth j (hrp_init_r key)) <= 255)
    by (intros j Hj; rewrite Forall_Znth in Br; apply Br; lia).
  destruct (hpf_add_ok h c Hh Hc Bh' Bc') as (A1 & A2 & u & Hu & A3).
  (* no carry out: h + c < 2^136 *)
  assert (Vh : hrp_val h <= 5 * 2 ^ 128 - 1).
  { rewrite (hpf_val_split h Hh). pose proof (hpf_val_low h Hh Bh). lia. }
  assert (Vc : hrp_val c <= 2 * 2 ^ 128 - 1).
  { rewrite (hpf_val_split c Hc). pose proof (hpf_val_low c Hc Bc). lia. }
  assert (Hu0 : u = 0).
  { pose proof (hpf_val_nonneg (hrp_add h c)). change (2 ^ 136) with (256 * 2 ^ 128) in A3.
    assert (u * (256 * 2 ^ 128) < 256 * 2 ^ 128) by lia. nia. }
  subst u. rewrite Z.mul_0_l, Z.add_0_r in A3.
  unfold hrp_mul.
  destruct (hpf_prods_ok (hrp_add h c) (hrp_init_r key) A1 Hr A2 Br') as (P1 & P2 & P3).
  destruct (hpf_reduce_ok _ P1 P2) as [R1 R2].
  split; auto. rewrite R2, P3, A3, Vr. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* small facts                                                             *)
(* ---------------------------------------------------------------------- *)

Lemma hpf_loop_len (f: list int * int -> Z -> list int * int) n s :
  (forall s j, Zlength (fst (f s j)) = Zlength (fst s)) -> Zlength (fst (hrp_loop f n s)) = Zlength (fst s).
Proof.
  intros H. unfold hrp_loop. generalize (map Z.of_nat (seq 0 (Z.to_nat n))) s.
  induction l as [|x t IH]; intros a; simpl; auto. rewrite IH, H. reflexivity.
Qed.

Lemma hpf_loop_len1 (f: list int -> Z -> list int) n l :
  (forall l j, Zlength (f l j) = Zlength l) -> Zlength (hrp_loop f n l) = Zlength l.
Proof.
  intros H. unfold hrp_loop. generalize (map Z.of_nat (seq 0 (Z.to_nat n))) l.
  induction l0 as [|x t IH]; intros a; simpl; auto. rewrite IH, H. reflexivity.
Qed.

Lemma hpf_add_length h c : Zlength h = 17 -> Zlength (hrp_add h c) = 17.
Proof.
  intros Hh. unfold hrp_add. rewrite hpf_loop_len; auto.
  intros s j. unfold hrp_add_step. simpl. apply Zlength_upd_Znth.
Qed.

Lemma hpf_init_r_length key : Zlength key >= 16 -> Zlength (hrp_init_r key) = 17.
Proof. intros Hk. apply hpr_init_r_ok. lia. Qed.

Lemma hpf_inv_zero : hrp_inv hrp_zero17 /\ hrp_val hrp_zero17 = 0.
Proof.
  split; [|reflexivity]. unfold hrp_inv, hrp_zero17. split; [reflexivity | split].
  - intros j Hj. rewrite Znth_Zrepeat by lia. rewrite Int.unsigned_zero. lia.
  - rewrite Znth_Zrepeat by lia. rewrite Int.unsigned_zero. lia.
Qed.

Lemma hpf_val_u8 l : hrp_val (map hrp_u8 l) = le_Z l.
Proof.
  induction l as [|b t IH]; simpl; auto. rewrite IH. unfold hrp_u8.
  rewrite Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma hpf_u8_le m : Forall (fun w => Int.unsigned w <= 255) (map hrp_u8 m).
Proof.
  apply Forall_map. apply Forall_forall. intros b _. unfold hrp_u8, Basics.compose.
  rewrite Int.unsigned_repr by rep_lia. rep_lia.
Qed.

Lemma hpf_block_c_ok m : Zlength m = 16 ->
  hrp_cblock (hrp_block_c m) /\ hrp_val (hrp_block_c m) = le_Z m + 2 ^ 128.
Proof.
  intros Hm. unfold hrp_block_c.
  assert (HF : Forall (fun w => Int.unsigned w <= 255) (map hrp_u8 m ++ [Int.one])).
  { apply Forall_app. split; [apply hpf_u8_le|]. repeat constructor. rewrite Int.unsigned_one. lia. }
  assert (HL : Zlength (map hrp_u8 m ++ [Int.one]) = 17)
    by (rewrite Zlength_app, Zlength_map, Hm; reflexivity).
  split; [split; [auto | split] |].
  - intros j Hj. rewrite Forall_Znth in HF. apply HF. lia.
  - rewrite Znth_app2 by (rewrite Zlength_map; lia). rewrite Zlength_map, Hm.
    replace (16 - 16) with 0 by lia. rewrite Znth_0_cons, Int.unsigned_one. lia.
  - rewrite hpf_val_app, hpf_val_u8, Zlength_map, Hm. simpl. reflexivity.
Qed.
