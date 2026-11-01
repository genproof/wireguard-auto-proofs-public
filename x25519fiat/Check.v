(* A small reflective interval checker for the straight-line limb code of curve25519-fiat32.c.

   expr t: a tree of the u32 / u64 operations used by fe_mul_m / fe_sqr_m (x25519_model.v).
   eD: its value over CompCert machine integers, written with the SAME functions as the model
       (Int.add, Int64.mul, u64, lo, ...), so that the model's definitions are convertible to eD of a tree;
   eZ: its value over Z, without wrap-around (masks are mod 2^k, shifts are * / div by 2^k);
   bnd: an upper bound computed by interval arithmetic, None when an operation may wrap.

   Soundness (bnd_sound): if every input limb is below its bound and bnd e = Some h, then
   0 <= eZ e <= h and the unsigned value of eD e is eZ e: the machine computation never wraps. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.x25519.x25519_model.

Local Open Scope Z_scope.

Inductive ty := T32 | T64.
Definition tD (t: ty) : Type := match t with T32 => int | T64 => int64 end.
Definition uD (t: ty) : tD t -> Z := match t with T32 => Int.unsigned | T64 => Int64.unsigned end.

Inductive expr : ty -> Type :=
| EV (b: bool) (i: Z) : expr T32              (* Znth i f (b = false) or Znth i g (b = true) *)
| EC32 (z: Z) : expr T32
| EC64 (z: Z) : expr T64
| EAdd32 (a b: expr T32) : expr T32
| EMul32 (a b: expr T32) : expr T32
| EMask32 (a: expr T32) (k: Z) : expr T32     (* a & (2^k - 1) *)
| EShru32 (a: expr T32) (k: Z) : expr T32
| ELo (a: expr T64) : expr T32                (* (u32)a, checked not to truncate *)
| EMaskLo (a: expr T64) (k: Z) : expr T32     (* (u32)a & (2^k - 1): truncation allowed *)
| EU64 (a: expr T32) : expr T64               (* (u64)a *)
| EAdd64 (a b: expr T64) : expr T64
| EMul64 (a b: expr T64) : expr T64
| EShl64 (a: expr T64) (k: Z) : expr T64
| EShru64 (a: expr T64) (k: Z) : expr T64.

Section Sem.
Variables f g : list int.

Fixpoint eD {t} (e: expr t) : tD t :=
  match e in expr t return tD t with
  | EV b i => Znth i (if b then g else f)
  | EC32 z => Int.repr z
  | EC64 z => Int64.repr z
  | EAdd32 a b => Int.add (eD a) (eD b)
  | EMul32 a b => Int.mul (eD a) (eD b)
  | EMask32 a k => Int.and (eD a) (Int.repr (2 ^ k - 1))
  | EShru32 a k => Int.shru (eD a) (Int.repr k)
  | ELo a => lo (eD a)
  | EMaskLo a k => Int.and (lo (eD a)) (Int.repr (2 ^ k - 1))
  | EU64 a => u64 (eD a)
  | EAdd64 a b => Int64.add (eD a) (eD b)
  | EMul64 a b => Int64.mul (eD a) (eD b)
  | EShl64 a k => Int64.shl (eD a) (Int64.repr k)
  | EShru64 a k => Int64.shru (eD a) (Int64.repr k)
  end.

Fixpoint eZ {t} (e: expr t) : Z :=
  match e with
  | EV b i => Int.unsigned (Znth i (if b then g else f))
  | EC32 z => z
  | EC64 z => z
  | EAdd32 a b => eZ a + eZ b
  | EMul32 a b => eZ a * eZ b
  | EMask32 a k => eZ a mod 2 ^ k
  | EShru32 a k => eZ a / 2 ^ k
  | ELo a => eZ a
  | EMaskLo a k => eZ a mod 2 ^ k
  | EU64 a => eZ a
  | EAdd64 a b => eZ a + eZ b
  | EMul64 a b => eZ a * eZ b
  | EShl64 a k => eZ a * 2 ^ k
  | EShru64 a k => eZ a / 2 ^ k
  end.
End Sem.

Section Bnd.
Variables bf bg : list Z.   (* upper bounds of the input limbs *)

Definition ob2 (x y: option Z) (op: Z -> Z -> Z) (lim: Z) : option Z :=
  match x, y with
  | Some a, Some b => if op a b <? lim then Some (op a b) else None
  | _, _ => None
  end.

Fixpoint bnd {t} (e: expr t) : option Z :=
  match e with
  | EV b i => if andb (0 <=? i) (i <? 10) then Some (Znth i (if b then bg else bf)) else None
  | EC32 z => if andb (0 <=? z) (z <? 2 ^ 32) then Some z else None
  | EC64 z => if andb (0 <=? z) (z <? 2 ^ 64) then Some z else None
  | EAdd32 a b => ob2 (bnd a) (bnd b) Z.add (2 ^ 32)
  | EMul32 a b => ob2 (bnd a) (bnd b) Z.mul (2 ^ 32)
  | EMask32 a k => if andb (0 <=? k) (k <? 32) then
                     match bnd a with Some x => Some (Z.min x (2 ^ k - 1)) | None => None end else None
  | EShru32 a k => if andb (0 <=? k) (k <? 32) then
                     match bnd a with Some x => Some (x / 2 ^ k) | None => None end else None
  | ELo a => match bnd a with Some x => if x <? 2 ^ 32 then Some x else None | None => None end
  | EMaskLo a k => if andb (0 <=? k) (k <=? 32) then
                     match bnd a with Some x => Some (Z.min x (2 ^ k - 1)) | None => None end else None
  | EU64 a => bnd a
  | EAdd64 a b => ob2 (bnd a) (bnd b) Z.add (2 ^ 64)
  | EMul64 a b => ob2 (bnd a) (bnd b) Z.mul (2 ^ 64)
  | EShl64 a k => if andb (0 <=? k) (k <? 64) then
                    match bnd a with Some x => if x * 2 ^ k <? 2 ^ 64 then Some (x * 2 ^ k) else None
                                | None => None end else None
  | EShru64 a k => if andb (0 <=? k) (k <? 64) then
                     match bnd a with Some x => Some (x / 2 ^ k) | None => None end else None
  end.

(* every tree of the list has a bound, and that bound is below the target *)
Fixpoint check_out (es: list (expr T32)) (target: list Z) : bool :=
  match es, target with
  | e :: es', t :: ts' => match bnd e with Some h => andb (h <=? t) (check_out es' ts') | None => false end
  | [], [] => true
  | _, _ => false
  end.
End Bnd.

(* ------------------------------------------------------------------ *)
(* soundness                                                           *)
(* ------------------------------------------------------------------ *)

Lemma ob2_some x y op lim h :
  ob2 x y op lim = Some h -> exists a b, x = Some a /\ y = Some b /\ h = op a b /\ op a b < lim.
Proof.
  unfold ob2. destruct x as [a|], y as [b|]; try discriminate.
  destruct (op a b <? lim) eqn:E; [|discriminate]. intros H; inv H.
  apply Z.ltb_lt in E. eauto 10.
Qed.

Lemma unsigned_repr32 z : 0 <= z < 2 ^ 32 -> Int.unsigned (Int.repr z) = z.
Proof. intros. apply Int.unsigned_repr. unfold Int.max_unsigned. simpl. lia. Qed.

Lemma unsigned_repr64 z : 0 <= z < 2 ^ 64 -> Int64.unsigned (Int64.repr z) = z.
Proof. intros. apply Int64.unsigned_repr. unfold Int64.max_unsigned. simpl. lia. Qed.

Lemma div_le_self a c : 0 <= a -> 0 < c -> a / c <= a.
Proof. intros. apply Z.div_le_upper_bound; [lia|]. nia. Qed.

Lemma land_ones_mod a k : 0 <= k -> Z.land a (2 ^ k - 1) = a mod 2 ^ k.
Proof. intros. rewrite <- Z.land_ones by lia. f_equal. rewrite Z.ones_equiv. lia. Qed.

Ltac dif H E :=
  match type of H with context [if ?c then _ else _] => destruct c eqn:E; [|discriminate] end.

Section Sound.
Variables (f g : list int) (bf bg : list Z).
Hypothesis Hf : forall i, 0 <= i < 10 -> Int.unsigned (Znth i f) <= Znth i bf.
Hypothesis Hg : forall i, 0 <= i < 10 -> Int.unsigned (Znth i g) <= Znth i bg.

Lemma bnd_sound : forall t (e: expr t) h, bnd bf bg e = Some h ->
  0 <= eZ f g e <= h /\ uD t (eD f g e) = eZ f g e.
Proof.
  induction e; intros h H; simpl in H; cbn [eZ eD uD].
  - (* EV *)
    dif H E. inv H.
    apply andb_prop in E. destruct E as [K1 K2]. apply Z.leb_le in K1. apply Z.ltb_lt in K2.
    split; [|reflexivity]. split; [apply Int.unsigned_range|].
    destruct b; [apply Hg | apply Hf]; lia.
  - (* EC32 *)
    dif H E. inv H.
    apply andb_prop in E. destruct E as [K1 K2]. apply Z.leb_le in K1. apply Z.ltb_lt in K2.
    split; [lia|]. apply unsigned_repr32; lia.
  - (* EC64 *)
    dif H E. inv H.
    apply andb_prop in E. destruct E as [K1 K2]. apply Z.leb_le in K1. apply Z.ltb_lt in K2.
    split; [lia|]. apply unsigned_repr64; lia.
  - (* EAdd32 *)
    apply ob2_some in H. destruct H as (x & y & Hx & Hy & -> & L).
    destruct (IHe1 _ Hx) as [B1 E1]; destruct (IHe2 _ Hy) as [B2 E2]. simpl in E1, E2.
    split; [lia|]. unfold Int.add. rewrite E1, E2. apply unsigned_repr32. lia.
  - (* EMul32 *)
    apply ob2_some in H. destruct H as (x & y & Hx & Hy & -> & L).
    destruct (IHe1 _ Hx) as [B1 E1]; destruct (IHe2 _ Hy) as [B2 E2]. simpl in E1, E2.
    split; [split; [nia | apply Z.mul_le_mono_nonneg; lia]|].
    unfold Int.mul. rewrite E1, E2. apply unsigned_repr32. split; [nia|].
    eapply Z.le_lt_trans; [apply Z.mul_le_mono_nonneg; try apply B1; try apply B2; lia | lia].
  - (* EMask32 *)
    dif H E.
    apply andb_prop in E. destruct E as [K1 K2]. apply Z.leb_le in K1. apply Z.ltb_lt in K2.
    destruct (bnd bf bg e) as [x|] eqn:Hx; [|discriminate]. inv H.
    destruct (IHe _ eq_refl) as [B1 E1]. simpl in E1.
    assert (P: 0 < 2 ^ k) by lia.
    assert (M1: 0 <= eZ f g e mod 2 ^ k < 2 ^ k) by (apply Z.mod_pos_bound; lia).
    assert (M2: eZ f g e mod 2 ^ k <= eZ f g e) by (apply Z.mod_le; lia).
    split; [split; [lia|] |].
    + apply Z.min_glb; lia.
    + unfold Int.and. rewrite E1.
      assert (2 ^ k <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
      rewrite (unsigned_repr32 (2 ^ k - 1)) by lia.
      rewrite land_ones_mod by lia. apply unsigned_repr32. lia.
  - (* EShru32 *)
    dif H E.
    apply andb_prop in E. destruct E as [K1 K2]. apply Z.leb_le in K1. apply Z.ltb_lt in K2.
    destruct (bnd bf bg e) as [x|] eqn:Hx; [|discriminate]. inv H.
    destruct (IHe _ eq_refl) as [B1 E1]. simpl in E1.
    assert (P: 0 < 2 ^ k) by lia.
    split; [split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia]|].
    unfold Int.shru. rewrite E1. rewrite unsigned_repr32 with (z := k) by lia.
    rewrite Z.shiftr_div_pow2 by lia.
    pose proof (Int.unsigned_range (eD f g e)) as R. rewrite E1 in R.
    apply unsigned_repr32. split; [apply Z.div_pos; lia|].
    apply Z.le_lt_trans with (eZ f g e); [apply div_le_self; lia | change Int.modulus with (2^32) in R; lia].
  - (* ELo *)
    destruct (bnd bf bg e) as [x|] eqn:Hx; [|discriminate].
    dif H L. inv H. apply Z.ltb_lt in L.
    destruct (IHe _ eq_refl) as [B1 E1]. simpl in E1.
    split; [lia|]. unfold lo. rewrite E1. apply unsigned_repr32. lia.
  - (* EMaskLo *)
    dif H E.
    apply andb_prop in E. destruct E as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
    destruct (bnd bf bg e) as [x|] eqn:Hx; [|discriminate]. inv H.
    destruct (IHe _ eq_refl) as [B1 E1]. simpl in E1.
    assert (P: 0 < 2 ^ k) by lia.
    assert (P32: 2 ^ k <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
    assert (M1: 0 <= eZ f g e mod 2 ^ k < 2 ^ k) by (apply Z.mod_pos_bound; lia).
    assert (M2: eZ f g e mod 2 ^ k <= eZ f g e) by (apply Z.mod_le; lia).
    split; [split; [lia|] |].
    + apply Z.min_glb; lia.
    + unfold Int.and, lo. rewrite (unsigned_repr32 (2 ^ k - 1)) by lia.
      rewrite E1, (Int.unsigned_repr_eq (eZ f g e)).
      rewrite land_ones_mod by lia.
      change Int.modulus with (2 ^ 32).
      rewrite <- Znumtheory.Zmod_div_mod; [| lia | lia |].
      * apply unsigned_repr32. lia.
      * exists (2 ^ (32 - k)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
  - (* EU64 *)
    destruct (IHe _ H) as [B1 E1]. simpl in E1.
    split; [lia|]. unfold u64. simpl. rewrite E1. apply unsigned_repr64.
    pose proof (Int.unsigned_range (eD f g e)) as R. rewrite E1 in R. change Int.modulus with (2^32) in R. lia.
  - (* EAdd64 *)
    apply ob2_some in H. destruct H as (x & y & Hx & Hy & -> & L).
    destruct (IHe1 _ Hx) as [B1 E1]; destruct (IHe2 _ Hy) as [B2 E2]. simpl in E1, E2.
    split; [lia|]. simpl. unfold Int64.add. rewrite E1, E2. apply unsigned_repr64. lia.
  - (* EMul64 *)
    apply ob2_some in H. destruct H as (x & y & Hx & Hy & -> & L).
    destruct (IHe1 _ Hx) as [B1 E1]; destruct (IHe2 _ Hy) as [B2 E2]. simpl in E1, E2.
    split; [split; [nia | apply Z.mul_le_mono_nonneg; lia]|].
    simpl. unfold Int64.mul. rewrite E1, E2. apply unsigned_repr64. split; [nia|].
    eapply Z.le_lt_trans; [apply Z.mul_le_mono_nonneg; try apply B1; try apply B2; lia | lia].
  - (* EShl64 *)
    dif H E.
    apply andb_prop in E. destruct E as [K1 K2]. apply Z.leb_le in K1. apply Z.ltb_lt in K2.
    destruct (bnd bf bg e) as [x|] eqn:Hx; [|discriminate].
    dif H L. inv H. apply Z.ltb_lt in L.
    destruct (IHe _ eq_refl) as [B1 E1]. simpl in E1.
    assert (P: 0 < 2 ^ k) by lia.
    split; [split; [nia | apply Z.mul_le_mono_nonneg_r; lia]|].
    cbn [uD eD]. unfold Int64.shl. rewrite E1. rewrite unsigned_repr64 with (z := k) by lia.
    rewrite Z.shiftl_mul_pow2 by lia. apply unsigned_repr64.
    split; [nia|]. eapply Z.le_lt_trans; [apply Z.mul_le_mono_nonneg_r; [lia | apply B1] | lia].
  - (* EShru64 *)
    dif H E.
    apply andb_prop in E. destruct E as [K1 K2]. apply Z.leb_le in K1. apply Z.ltb_lt in K2.
    destruct (bnd bf bg e) as [x|] eqn:Hx; [|discriminate]. inv H.
    destruct (IHe _ eq_refl) as [B1 E1]. simpl in E1.
    assert (P: 0 < 2 ^ k) by lia.
    split; [split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia]|].
    cbn [uD eD]. unfold Int64.shru. rewrite E1. rewrite unsigned_repr64 with (z := k) by lia.
    rewrite Z.shiftr_div_pow2 by lia.
    pose proof (Int64.unsigned_range (eD f g e)) as R. rewrite E1 in R.
    apply unsigned_repr64. split; [apply Z.div_pos; lia|].
    apply Z.le_lt_trans with (eZ f g e); [apply div_le_self; lia | change Int64.modulus with (2^64) in R; lia].
Qed.

Lemma check_out_sound : forall es ts, check_out bf bg es ts = true ->
  Forall2 (fun (e: expr T32) (t: Z) => 0 <= eZ f g e <= t /\ Int.unsigned (eD f g e) = eZ f g e) es ts.
Proof.
  induction es as [|e es IH]; intros [|t ts] H; simpl in H; try discriminate; constructor.
  - destruct (bnd bf bg e) as [h|] eqn:B; [|discriminate].
    apply andb_prop in H. destruct H as [H _]. apply Z.leb_le in H.
    destruct (bnd_sound _ e h B) as [[L U] E]. split; [lia | exact E].
  - destruct (bnd bf bg e) as [h|]; [|discriminate]. apply andb_prop in H. apply IH, H.
Qed.
End Sound.
