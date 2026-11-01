(* The model's Montgomery ladder (ladder_steps of x25519_model.v) computes fiat-crypto's M.montladder over
   F p, step by step: the kernel's ladder step is fiat's xzladderstep (with a24 = 121665; the C multiplies
   by 121666 = a24 + 1 in BoringSSL's arrangement), the conditional swaps are fiat's cswap. *)
From Coq Require Import NArith.
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.prims.prim_api WgNoise.proof.x25519.x25519_model.
Require Import X25519.Limbs X25519.MulSqr X25519.Freeze X25519.Bytes X25519.Scalar X25519.FeF.
Require Import Crypto.Spec.ModularArithmetic Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.LetIn Crypto.Util.Loops.
Require Crypto.Spec.Curve25519 Crypto.Curves.Montgomery.XZ.

Local Open Scope Z_scope.

Lemma a24_val : Curve25519.M.a24 = F.of_Z pP 121665.
Proof. apply F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

Definition xzstep (x1: Fp) (Q Q': Fp * Fp) : (Fp * Fp) * (Fp * Fp) :=
  @XZ.M.xzladderstep Fp F.add F.sub F.mul Curve25519.M.a24 x1 Q Q'.

(* the field-arithmetic part of the model's ladder step (after the conditional swaps) *)
Definition limb_step (x1 x2 z2 x3 z3: list int) : list int * list int * list int * list int :=
  let tmp0l := fe_sub_m x3 z3 in
  let tmp1l := fe_sub_m x2 z2 in
  let x2l := fe_add_m x2 z2 in
  let z2l := fe_add_m x3 z3 in
  let z3 := fe_mul_m tmp0l x2l in
  let z2 := fe_mul_m z2l tmp1l in
  let tmp0 := fe_sqr_m tmp1l in
  let tmp1 := fe_sqr_m x2l in
  let x3l := fe_add_m z3 z2 in
  let z2l := fe_sub_m z3 z2 in
  let x2 := fe_mul_m tmp1 tmp0 in
  let tmp1l := fe_sub_m tmp1 tmp0 in
  let z2 := fe_sqr_m z2l in
  let z3 := fe_mul121666_m tmp1l in
  let x3 := fe_sqr_m x3l in
  let tmp0l := fe_add_m tmp0 z3 in
  let z3 := fe_mul_m x1 z2 in
  let z2 := fe_mul_m tmp1l tmp0l in
  (x2, z2, x3, z3).

Lemma ladder_step_split e x1 pos st :
  ladder_step e x1 pos st =
  let b := ladder_bit e pos in
  let swap := Int.xor (ls_swap st) b in
  let xs := fe_cswap_m (ls_x2 st) (ls_x3 st) swap in
  let zs := fe_cswap_m (ls_z2 st) (ls_z3 st) swap in
  match limb_step x1 (fst xs) (fst zs) (snd xs) (snd zs) with
  | (x2, z2, x3, z3) => mk_ls x2 z2 x3 z3 b
  end.
Proof. reflexivity. Qed.

(* one step of the forward evaluation of a limb expression *)
Lemma st_add a b A B : bounded tight a /\ fe a = A -> bounded tight b /\ fe b = B ->
  bounded loose (fe_add_m a b) /\ fe (fe_add_m a b) = F.add A B.
Proof. intros [Ha <-] [Hb <-]. apply fe_add; assumption. Qed.
Lemma st_sub a b A B : bounded tight a /\ fe a = A -> bounded tight b /\ fe b = B ->
  bounded loose (fe_sub_m a b) /\ fe (fe_sub_m a b) = F.sub A B.
Proof. intros [Ha <-] [Hb <-]. apply fe_sub; assumption. Qed.
Lemma st_mul a b A B : bounded loose a /\ fe a = A -> bounded loose b /\ fe b = B ->
  bounded tight (fe_mul_m a b) /\ fe (fe_mul_m a b) = F.mul A B.
Proof. intros [Ha <-] [Hb <-]. apply fe_mul; assumption. Qed.
Lemma st_sqr a A : bounded loose a /\ fe a = A ->
  bounded tight (fe_sqr_m a) /\ fe (fe_sqr_m a) = F.mul A A.
Proof. intros [Ha <-]. apply fe_sqr; assumption. Qed.
Lemma st_121666 a A : bounded loose a /\ fe a = A ->
  bounded tight (fe_mul121666_m a) /\ fe (fe_mul121666_m a) = F.mul A (F.of_Z pP 121666).
Proof. intros [Ha <-]. apply fe_mul121666; assumption. Qed.
Lemma st_loose a A : bounded tight a /\ fe a = A -> bounded loose a /\ fe a = A.
Proof. intros [Ha E]. split; [apply tight_loose, Ha | exact E]. Qed.

Ltac fevT t :=
  lazymatch t with
  | fe_mul_m ?a ?b => let Ha := fevL a in let Hb := fevL b in constr:(st_mul _ _ _ _ Ha Hb)
  | fe_sqr_m ?a => let Ha := fevL a in constr:(st_sqr _ _ Ha)
  | fe_mul121666_m ?a => let Ha := fevL a in constr:(st_121666 _ _ Ha)
  | _ => match goal with H: bounded tight t |- _ => constr:(conj H (eq_refl (fe t))) end
  end
with fevL t :=
  lazymatch t with
  | fe_add_m ?a ?b => let Ha := fevT a in let Hb := fevT b in constr:(st_add _ _ _ _ Ha Hb)
  | fe_sub_m ?a ?b => let Ha := fevT a in let Hb := fevT b in constr:(st_sub _ _ _ _ Ha Hb)
  | _ => let H := fevT t in constr:(st_loose _ _ H)
  end.

Lemma limb_step_ok x1 x2 z2 x3 z3 :
  bounded tight x1 -> bounded tight x2 -> bounded tight z2 -> bounded tight x3 -> bounded tight z3 ->
  match limb_step x1 x2 z2 x3 z3 with
  | (a, b, c, d) =>
    bounded tight a /\ bounded tight b /\ bounded tight c /\ bounded tight d /\
    xzstep (fe x1) (fe x2, fe z2) (fe x3, fe z3) = ((fe a, fe b), (fe c, fe d))
  end.
Proof.
  intros H1 H2 H3 H4 H5. unfold limb_step. cbv zeta.
  match goal with |- bounded tight ?a /\ bounded tight ?b /\ bounded tight ?c /\ bounded tight ?d /\ _ =>
    let Ha := fevT a in let Hb := fevT b in let Hc := fevT c in let Hd := fevT d in
    destruct Ha as [Ba ->]; destruct Hb as [Bb ->]; destruct Hc as [Bc ->]; destruct Hd as [Bd ->];
    split; [exact Ba|]; split; [exact Bb|]; split; [exact Bc|]; split; [exact Bd|]
  end.
  unfold xzstep, XZ.M.xzladderstep, Let_In. rewrite a24_val.
  f_equal; f_equal; ring.
Qed.

(* ------------------------------------------------------------------ *)
(* the loop                                                            *)
(* ------------------------------------------------------------------ *)

Definition fstate : Type := (Fp * Fp * Fp * Fp * bool * Z)%type.

Definition ftest (s: fstate) : bool := let '(_, i) := s in i >=? 0.

Definition fbody (tb: Z -> bool) (x1: Fp) (s: fstate) : fstate :=
  let '(x2, z2, x3, z3, swap, i) := s in
  @Let_In bool (fun _ => fstate) (tb i) (fun b =>
  @Let_In bool (fun _ => fstate) (xorb swap b) (fun swap0 =>
  let (x4, x5) := XZ.M.cswap swap0 x2 x3 in
  let (z4, z5) := XZ.M.cswap swap0 z2 z3 in
  @Let_In bool (fun _ => fstate) b (fun swap1 =>
  let '(x6, z6, (x7, z7)) := xzstep x1 (x4, z4) (x5, z5) return fstate in
  let i0 := Z.pred i in (x6, z6, x7, z7, swap1, i0)))).

Lemma montladder_unfold tb (x1: Fp) :
  @XZ.M.montladder Fp F.zero F.one F.add F.sub F.mul F.inv Curve25519.M.a24 255 tb x1 =
  let '(x2, z2, x3, z3, swap, _) := while ftest (fbody tb x1) 255 (F.one, F.zero, x1, F.one, false, 254) in
  let (x4, _) := XZ.M.cswap swap x2 x3 in
  let (z4, _) := XZ.M.cswap swap z2 z3 in F.mul x4 (F.inv z4).
Proof. reflexivity. Qed.

Definition R (st: ladder_state) (s: fstate) : Prop :=
  let '(x2, z2, x3, z3, swap, _) := s in
  bounded tight (ls_x2 st) /\ bounded tight (ls_z2 st) /\ bounded tight (ls_x3 st) /\
  bounded tight (ls_z3 st) /\
  fe (ls_x2 st) = x2 /\ fe (ls_z2 st) = z2 /\ fe (ls_x3 st) = x3 /\ fe (ls_z3 st) = z3 /\
  ls_swap st = (if swap then Int.one else Int.zero).

Lemma xor_bits (a b: bool) :
  Int.xor (if a then Int.one else Int.zero) (if b then Int.one else Int.zero) =
  if xorb a b then Int.one else Int.zero.
Proof. destruct a, b; reflexivity. Qed.

Lemma step_rel e x1 st (x2 z2 x3 z3: Fp) (swap: bool) (i: Z) :
  bounded tight x1 -> 0 <= i < 255 ->
  R st (x2, z2, x3, z3, swap, i) ->
  R (ladder_step e x1 i st) (fbody (Z.testbit (scalar_of e)) (fe x1) (x2, z2, x3, z3, swap, i)) /\
  snd (fbody (Z.testbit (scalar_of e)) (fe x1) (x2, z2, x3, z3, swap, i)) = i - 1.
Proof.
  intros Hx1 Hi (B2 & B3 & B4 & B5 & <- & <- & <- & <- & Hs).
  rewrite ladder_step_split. cbv zeta. rewrite ladder_bit_spec by lia. rewrite Hs, xor_bits.
  unfold fbody, Let_In. cbv zeta.
  pose proof (bounded_length _ _ B2) as L2. pose proof (bounded_length _ _ B3) as L3.
  pose proof (bounded_length _ _ B4) as L4. pose proof (bounded_length _ _ B5) as L5.
  rewrite (fe_cswap_ok (ls_x2 st) (ls_x3 st)) by assumption.
  rewrite (fe_cswap_ok (ls_z2 st) (ls_z3 st)) by assumption.
  destruct (xorb swap (Z.testbit (scalar_of e) i)); cbn [fst snd XZ.M.cswap].
  - pose proof (limb_step_ok x1 (ls_x3 st) (ls_z3 st) (ls_x2 st) (ls_z2 st) Hx1 B4 B5 B2 B3) as H.
    destruct (limb_step x1 (ls_x3 st) (ls_z3 st) (ls_x2 st) (ls_z2 st)) as [[[a b] c] d].
    destruct H as (Ba & Bb & Bc & Bd & E). rewrite E. cbn.
    split; [|lia]. repeat split; try assumption.
  - pose proof (limb_step_ok x1 (ls_x2 st) (ls_z2 st) (ls_x3 st) (ls_z3 st) Hx1 B2 B3 B4 B5) as H.
    destruct (limb_step x1 (ls_x2 st) (ls_z2 st) (ls_x3 st) (ls_z3 st)) as [[[a b] c] d].
    destruct H as (Ba & Bb & Bc & Bd & E). rewrite E. cbn.
    split; [|lia]. repeat split; try assumption.
Qed.

Lemma fe1_tight : bounded tight fe1_m.
Proof. unfold bounded, tight, fe1_m. simpl. repeat constructor; cbv; discriminate. Qed.
Lemma fe0_tight : bounded tight fe0_m.
Proof. unfold bounded, tight, fe0_m. simpl. repeat constructor; cbv; discriminate. Qed.
Lemma fe_fe1 : fe fe1_m = F.one.
Proof. reflexivity. Qed.
Lemma fe_fe0 : fe fe0_m = F.zero.
Proof. reflexivity. Qed.

Lemma while_step {St} (test: St -> bool) (body: St -> St) n s :
  test s = true -> while test body (S n) s = while test body n (body s).
Proof. intros H. cbn [while.while]. rewrite H. reflexivity. Qed.

Lemma while_stop {St} (test: St -> bool) (body: St -> St) n s :
  test s = false -> while test body n s = s.
Proof. intros H. destruct n; cbn [while.while]; rewrite H; reflexivity. Qed.

Lemma loop_rel e x1 : bounded tight x1 ->
  forall k, (k <= 255)%nat -> exists s : fstate,
    R (ladder_steps e x1 k (ladder_init x1)) s /\ snd s = 254 - Z.of_nat k /\
    while ftest (fbody (Z.testbit (scalar_of e)) (fe x1)) 255 (F.one, F.zero, fe x1, F.one, false, 254) =
    while ftest (fbody (Z.testbit (scalar_of e)) (fe x1)) (255 - k) s.
Proof.
  intros Hx1 k. induction k as [|k IH]; intros Hk.
  - exists (F.one, F.zero, fe x1, F.one, false, 254). split; [|split; reflexivity].
    unfold R, ladder_init. cbn [ls_x2 ls_z2 ls_x3 ls_z3 ls_swap].
    repeat split; auto using fe1_tight, fe0_tight.
  - destruct (IH ltac:(lia)) as [s (Hr & Hi & Hw)].
    destruct s as [[[[[x2 z2] x3] z3] swap] i]. cbn [snd] in Hi.
    destruct (step_rel e x1 _ x2 z2 x3 z3 swap i Hx1 ltac:(lia) Hr) as [Hr' Hi'].
    exists (fbody (Z.testbit (scalar_of e)) (fe x1) (x2, z2, x3, z3, swap, i)).
    split; [|split].
    + cbn [ladder_steps]. replace (254 - Z.of_nat k) with i by lia. exact Hr'.
    + rewrite Hi'. lia.
    + rewrite Hw. replace (255 - k)%nat with (S (255 - S k)) by lia.
      apply while_step. cbn. apply Z.geb_le. lia.
Qed.

Lemma ladder_refines e x1 : bounded tight x1 ->
  let st := ladder_steps e x1 255 (ladder_init x1) in
  let x2 := fst (fe_cswap_m (ls_x2 st) (ls_x3 st) (ls_swap st)) in
  let z2 := fst (fe_cswap_m (ls_z2 st) (ls_z3 st) (ls_swap st)) in
  bounded tight (fe_mul_m x2 (fe_invert_m z2)) /\
  fe (fe_mul_m x2 (fe_invert_m z2)) =
    @XZ.M.montladder Fp F.zero F.one F.add F.sub F.mul F.inv Curve25519.M.a24 255
      (Z.testbit (scalar_of e)) (fe x1).
Proof.
  intros Hx1. cbv zeta. rewrite montladder_unfold.
  destruct (loop_rel e x1 Hx1 255 ltac:(lia)) as [s (Hr & Hi & Hw)]. rewrite Hw.
  destruct s as [[[[[x2 z2] x3] z3] swap] i]. cbn [snd] in Hi.
  rewrite while_stop by (cbn; rewrite Z.geb_leb; apply Z.leb_gt; lia).
  destruct Hr as (B2 & B3 & B4 & B5 & <- & <- & <- & <- & Hs). rewrite Hs.
  pose proof (bounded_length _ _ B2) as L2. pose proof (bounded_length _ _ B3) as L3.
  pose proof (bounded_length _ _ B4) as L4. pose proof (bounded_length _ _ B5) as L5.
  rewrite (fe_cswap_ok (ls_x2 _) (ls_x3 _)) by assumption.
  rewrite (fe_cswap_ok (ls_z2 _) (ls_z3 _)) by assumption.
  destruct swap; cbn [fst XZ.M.cswap].
  - destruct (fe_invert _ B5) as [Bi Ei].
    destruct (fe_mul _ _ (tight_loose _ B4) (tight_loose _ Bi)) as [Bm Em].
    split; [exact Bm|]. rewrite Em, Ei. reflexivity.
  - destruct (fe_invert _ B3) as [Bi Ei].
    destruct (fe_mul _ _ (tight_loose _ B2) (tight_loose _ Bi)) as [Bm Em].
    split; [exact Bm|]. rewrite Em, Ei. reflexivity.
Qed.
