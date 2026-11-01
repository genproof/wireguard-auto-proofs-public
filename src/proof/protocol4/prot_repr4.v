(* the shim's refcount_t warnings EXACTLY.

   The any-state laws claim that a call raises no refcount_t warning (common.h shim_same compares
   wg_shim_refcount_warn[5]), and law keypairs claims the warnings are exactly the model's.  The shared layer v3
   (prot_repr3.v) keeps them existentially (`refwarn gv`, the last conjunct of `shim_state gv S`), so no v3
   specification can give that.  The v4 layer keeps the v3 model and representation (prot_model3 / prot_repr3:
   every object predicate is shared) and replaces only the shim's state: `shim_state4 gv S w` = the globals (`shim_core gv S`, prot_repr3.v) and the warnings w (5 counters, by enum refcount_saturation_type)
   exactly.  This file: the predicate, the warning model of wg_shim.c's refcount_t functions, and the bridge to
   the v3 predicate. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require WgNoise.shim.code.
Local Open Scope logic.

#[local] Existing Instance Noise.CS.

(* enum refcount_saturation_type (include/linux/refcount.h) *)
Definition REFCOUNT_ADD_NOT_ZERO_OVF : Z := 0.
Definition REFCOUNT_ADD_OVF : Z := 1.
Definition REFCOUNT_ADD_UAF : Z := 2.
Definition REFCOUNT_SUB_UAF : Z := 3.
Definition REFCOUNT_DEC_LEAK : Z := 4.

(* wg_shim_refcount_warn[t]++ (unsigned long: wraps) *)
Definition warn_bump (w: list int64) (t: Z) : list int64 :=
  upd_Znth t w (Int64.add (Znth t w) Int64.one).

(* the warnings after wg_shim_refcount_inc_not_zero / _inc / _dec_and_test on a count v (wg_shim.c) *)
Definition rc_inz_warn (v: int) (w: list int64) : list int64 :=
  if Int.eq v Int.zero then w
  else if orb (rc_neg v) (rc_neg (Int.add v Int.one)) then warn_bump w REFCOUNT_ADD_NOT_ZERO_OVF else w.
Definition rc_inc_warn (v: int) (w: list int64) : list int64 :=
  if Int.eq v Int.zero then warn_bump w REFCOUNT_ADD_UAF
  else if orb (rc_neg v) (rc_neg (Int.add v Int.one)) then warn_bump w REFCOUNT_ADD_OVF else w.
Definition rc_dec_warn (v: int) (w: list int64) : list int64 :=
  if andb (negb (rc_neg v)) (Int.eq v Int.one) then w
  else if orb (Int.eq v Int.zero) (rc_neg v) then warn_bump w REFCOUNT_SUB_UAF else w.

(* the warnings, exactly *)
Definition refwarn4 (gv: globals) (w: list int64) : mpred :=
  !! (Zlength w = 5) && data_at Ews (tarray tulong 5) (map Vlong w) (gv _wg_shim_refcount_warn).

(* the shim's state with the warnings exact *)
Definition shim_state4 (gv: globals) (S: shim) (w: list int64) : mpred :=
  shim_core gv S * refwarn4 gv w.

Lemma refwarn_ex4 gv : refwarn gv = EX w: list int64, refwarn4 gv w.
Proof.
  unfold refwarn, refwarn4. reflexivity.
Qed.

(* v3's shim_state is v4's with the warnings forgotten *)
Lemma shim_state_ex4 gv S : shim_state gv S = EX w: list int64, shim_state4 gv S w.
Proof.
  rewrite shim_state_split, refwarn_ex4. unfold shim_state4.
  apply pred_ext; Intros w; Exists w; cancel.
Qed.

Lemma shim_state4_forget gv S w : shim_state4 gv S w |-- shim_state gv S.
Proof. rewrite shim_state_ex4. Exists w. cancel. Qed.

Lemma refwarn4_length gv w : refwarn4 gv w |-- !! (Zlength w = 5).
Proof. unfold refwarn4. entailer!. Qed.

(* below saturation (1 <= v < INT_MAX for an increment, 1 <= v <= INT_MAX for a decrement) no warning *)
Lemma rc_inz_warn_small v w : 0 < Int.unsigned v < 2147483647 -> rc_inz_warn v w = w.
Proof.
  intros H. unfold rc_inz_warn.
  pose proof (Int.eq_spec v Int.zero) as E; destruct (Int.eq v Int.zero); [reflexivity |].
  unfold rc_neg, Int.ltu.
  rewrite (Int.unsigned_repr 2147483648) by rep_lia.
  rewrite Int.add_unsigned, Int.unsigned_one, Int.unsigned_repr by rep_lia.
  repeat (destruct zlt; try lia). reflexivity.
Qed.

Lemma rc_dec_warn_small v w : 0 < Int.unsigned v < 2147483648 -> rc_dec_warn v w = w.
Proof.
  intros H. unfold rc_dec_warn, rc_neg, Int.ltu.
  rewrite (Int.unsigned_repr 2147483648) by rep_lia.
  destruct zlt; [| lia]. simpl.
  destruct (Int.eq v Int.one); [reflexivity |].
  pose proof (Int.eq_spec v Int.zero) as E; destruct (Int.eq v Int.zero).
  - subst. rewrite Int.unsigned_zero in H. lia.
  - reflexivity.
Qed.
