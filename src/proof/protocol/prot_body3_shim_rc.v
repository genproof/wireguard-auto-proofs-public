(* Body proofs of the protocol piece, group shim_rc: the kernel's refcount_t in the
   shim, wg_shim_refcount_warn_saturate / _neg / _inc_not_zero / _inc / _dec_and_test of patch/wg_shim.c,
   against their specifications in prot_specs3.v (counts exact: rc_add1 / rc_sub1 of prot_model3.v; the warning
   counters wg_shim_refcount_warn kept existentially, refwarn of prot_repr3.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_prog3.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

(* -1073741824 and 3221225472 (REFCOUNT_SATURATED) are the same 32 bits *)
Lemma prot3_shim_rc_sat_repr : Int.repr (-1073741824) = REFCOUNT_SATURATED.
Proof. unfold REFCOUNT_SATURATED. apply Int.eqm_samerepr. exists (-1). reflexivity. Qed.

Lemma prot3_shim_rc_neg_repr : Int.repr (-2147483648) = Int.repr 2147483648.
Proof. apply Int.eqm_samerepr. exists (-1). reflexivity. Qed.

(* rc_neg as the shim computes it: v >= 0x80000000u *)
Lemma prot3_shim_rc_neg_cmpu v : Int.cmpu Cge v (Int.repr (-2147483648)) = rc_neg v.
Proof. unfold rc_neg. rewrite prot3_shim_rc_neg_repr. reflexivity. Qed.

Section Bodies.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Shim.CS.
Local Open Scope logic.

Definition Gsh_rc := Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS.

(* refwarn in the shim's compspecs *)
Definition refwarn_S (gv: globals) : mpred :=
  EX w: list int64, !! (Zlength w = 5) &&
    @data_at Shim.CS Ews (tarray tulong 5) (map Vlong w) (gv _wg_shim_refcount_warn).

Lemma refwarn_S_eq gv : refwarn gv = refwarn_S gv.
Proof.
  unfold refwarn, refwarn_S. f_equal. extensionality w. f_equal.
  apply data_at_cs_eq; first [apply JMeq_refl | reflexivity].
Qed.

Lemma prot3_shim_rc_uint_N2S sh v r : @data_at Noise.CS sh tuint v r = @data_at Shim.CS sh tuint v r.
Proof. apply data_at_cs_eq; first [apply JMeq_refl | reflexivity]. Qed.

Lemma prot3_shim_rc_body_warn_saturate :
  @semax_body (QPvarspecs Shim.qp) Gsh_rc Shim.CS
    WgNoise.shim.code.f_wg_shim_refcount_warn_saturate wg_shim_refcount_warn_saturate_spec.
Proof.
  start_function.
  rewrite refwarn_S_eq, prot3_shim_rc_uint_N2S. unfold refwarn_S. Intros w.
  forward.
  forward.
  forward.
  rewrite refwarn_S_eq, prot3_shim_rc_uint_N2S. unfold refwarn_S.
  Exists (upd_Znth t w (Int64.add (Znth t w) (Int64.repr 1))).
  rewrite prot3_shim_rc_sat_repr.
  entailer!.
  - rewrite upd_Znth_Zlength by lia. auto.
  - first [rewrite upd_Znth_map | rewrite <- upd_Znth_map]; cancel.
Qed.

Lemma prot3_shim_rc_body_neg :
  @semax_body (QPvarspecs Shim.qp) Gsh_rc Shim.CS
    WgNoise.shim.code.f_wg_shim_refcount_neg wg_shim_refcount_neg_spec.
Proof.
  start_function.
  forward.
  entailer!.
  unfold rc_neg. rewrite prot3_shim_rc_neg_repr.
  destruct (Int.ltu v (Int.repr 2147483648)); reflexivity.
Qed.

Lemma prot3_shim_rc_body_inc_not_zero :
  @semax_body (QPvarspecs Shim.qp) Gsh_rc Shim.CS
    WgNoise.shim.code.f_wg_shim_refcount_inc_not_zero wg_shim_refcount_inc_not_zero_spec.
Proof.
  start_function.
  rewrite prot3_shim_rc_uint_N2S.
  forward.
  forward_if.
  { forward. rewrite prot3_shim_rc_uint_N2S. entailer!. }
  forward.
  forward_call v.
  forward_if (PROP () LOCAL (temp WgNoise.shim.code._t'2
                                (Vint (if orb (rc_neg v) (rc_neg (Int.add v Int.one)) then Int.one else Int.zero));
                             temp WgNoise.shim.code._r r; temp WgNoise.shim.code._old (Vint v); gvars gv)
              SEP (@data_at Shim.CS sh tuint (Vint (Int.add v Int.one)) r; refwarn gv)).
  { forward. destruct (rc_neg v) eqn:E; [| unfold typed_true in *; simpl in *; discriminate].
    simpl orb. entailer!. }
  { forward_call (Int.add v Int.one). forward.
    destruct (rc_neg v) eqn:E; [unfold typed_false in *; simpl in *; discriminate |].
    simpl orb. entailer!. destruct (rc_neg (Int.add v Int.one)); reflexivity. }
  forward_if (PROP () LOCAL (temp WgNoise.shim.code._r r; temp WgNoise.shim.code._old (Vint v); gvars gv)
              SEP (@data_at Noise.CS sh tuint (Vint (rc_add1 v)) r; refwarn gv)).
  { rewrite <- prot3_shim_rc_uint_N2S. forward_call (gv, sh, r, Int.add v Int.one, 0).
    unfold rc_add1. destruct (orb (rc_neg v) (rc_neg (Int.add v Int.one))); [entailer! | contradiction]. }
  { forward. rewrite <- prot3_shim_rc_uint_N2S.
    unfold rc_add1. destruct (orb (rc_neg v) (rc_neg (Int.add v Int.one))); [discriminate | entailer!]. }
  forward.
  rewrite (Int.eq_false v Int.zero H). entailer!.
Qed.

Lemma prot3_shim_rc_body_inc :
  @semax_body (QPvarspecs Shim.qp) Gsh_rc Shim.CS
    WgNoise.shim.code.f_wg_shim_refcount_inc wg_shim_refcount_inc_spec.
Proof.
  start_function.
  rewrite prot3_shim_rc_uint_N2S.
  forward.
  forward.
  forward_if (PROP () LOCAL ()
              SEP (@data_at Noise.CS sh tuint
                     (Vint (if Int.eq v Int.zero then REFCOUNT_SATURATED else rc_add1 v)) r; refwarn gv)).
  { rewrite <- prot3_shim_rc_uint_N2S. forward_call (gv, sh, r, Int.add v Int.one, 2).
    subst v. entailer!. }
  { forward_call v.
    forward_if (PROP () LOCAL (temp WgNoise.shim.code._t'2
                                (Vint (if orb (rc_neg v) (rc_neg (Int.add v Int.one)) then Int.one else Int.zero));
                             temp WgNoise.shim.code._r r; temp WgNoise.shim.code._old (Vint v); gvars gv)
              SEP (@data_at Shim.CS sh tuint (Vint (Int.add v Int.one)) r; refwarn gv)).
    { forward. destruct (rc_neg v) eqn:E; [| unfold typed_true in *; simpl in *; discriminate].
      simpl orb. entailer!. }
    { forward_call (Int.add v Int.one). forward.
      destruct (rc_neg v) eqn:E; [unfold typed_false in *; simpl in *; discriminate |].
      simpl orb. entailer!. destruct (rc_neg (Int.add v Int.one)); reflexivity. }
    forward_if.
    { rewrite <- prot3_shim_rc_uint_N2S. forward_call (gv, sh, r, Int.add v Int.one, 1).
      rewrite (Int.eq_false v Int.zero H).
      unfold rc_add1. destruct (orb (rc_neg v) (rc_neg (Int.add v Int.one))); [entailer! | contradiction]. }
    { forward. rewrite <- prot3_shim_rc_uint_N2S. rewrite (Int.eq_false v Int.zero H).
      unfold rc_add1. destruct (orb (rc_neg v) (rc_neg (Int.add v Int.one))); [discriminate | entailer!]. } }
Qed.

Lemma prot3_shim_rc_sub_one v : v <> Int.one -> Int.eq (Int.sub v Int.one) Int.zero = false.
Proof.
  intros N. apply Int.eq_false. intros E. apply N.
  assert (v = Int.add (Int.sub v Int.one) Int.one) as ->.
  { rewrite Int.sub_add_opp, Int.add_assoc, (Int.add_commut (Int.neg Int.one)), Int.add_neg_zero, Int.add_zero.
    reflexivity. }
  rewrite E. reflexivity.
Qed.

Lemma prot3_shim_rc_body_dec_and_test :
  @semax_body (QPvarspecs Shim.qp) Gsh_rc Shim.CS
    WgNoise.shim.code.f_wg_shim_refcount_dec_and_test wg_shim_refcount_dec_and_test_spec.
Proof.
  start_function.
  rewrite prot3_shim_rc_uint_N2S.
  forward.
  forward.
  forward_call v.
  forward_if (PROP () LOCAL (temp WgNoise.shim.code._t'2
                                (Vint (if andb (negb (rc_neg v)) (Int.eq v Int.one) then Int.one else Int.zero));
                             temp WgNoise.shim.code._r r; temp WgNoise.shim.code._old (Vint v); gvars gv)
              SEP (@data_at Shim.CS sh tuint (Vint (Int.sub v Int.one)) r; refwarn gv)).
  { forward. destruct (rc_neg v) eqn:E; [unfold typed_true in *; simpl in *; discriminate |].
    cbn [andb negb]. entailer!. change (Int.repr 1) with Int.one. destruct (Int.eq v Int.one); reflexivity. }
  { forward. destruct (rc_neg v) eqn:E; [| unfold typed_false in *; simpl in *; discriminate].
    cbn [andb negb]. entailer!. }
  forward_if.
  { forward.
    destruct (andb (negb (rc_neg v)) (Int.eq v Int.one)) eqn:E; [| contradiction].
    apply andb_prop in E. destruct E as [_ E]. apply Int.same_if_eq in E. subst v.
    rewrite <- prot3_shim_rc_uint_N2S. unfold rc_sub1. rewrite Int.eq_true. simpl. entailer!. }
  assert (EA: andb (negb (rc_neg v)) (Int.eq v Int.one) = false).
  { destruct (andb (negb (rc_neg v)) (Int.eq v Int.one)); [discriminate | reflexivity]. }
  clear H.
  forward_if (PROP () LOCAL (temp WgNoise.shim.code._t'3
                                (Vint (if orb (Int.eq v Int.zero) (rc_neg v) then Int.one else Int.zero));
                             temp WgNoise.shim.code._r r; temp WgNoise.shim.code._old (Vint v); gvars gv)
              SEP (@data_at Shim.CS sh tuint (Vint (Int.sub v Int.one)) r; refwarn gv)).
  { forward. subst v. entailer!. }
  { forward_call v. forward. rewrite (Int.eq_false v Int.zero H). cbn [orb]. entailer!.
    destruct (rc_neg v); reflexivity. }
  forward_if (PROP () LOCAL ()
              SEP (@data_at Noise.CS sh tuint (Vint (rc_sub1 v)) r; refwarn gv)).
  { rewrite <- prot3_shim_rc_uint_N2S. forward_call (gv, sh, r, Int.sub v Int.one, 3).
    unfold rc_sub1. rewrite EA. change (Int.repr 0) with Int.zero in H.
    destruct (orb (Int.eq v Int.zero) (rc_neg v)); [entailer! | contradiction]. }
  { forward. rewrite <- prot3_shim_rc_uint_N2S.
    unfold rc_sub1. rewrite EA. change (Int.repr 0) with Int.zero in H.
    destruct (orb (Int.eq v Int.zero) (rc_neg v));
      [exfalso; apply Int.one_not_zero; exact H | entailer!]. }
  forward.
  apply prop_right.
  assert (Int.eq (rc_sub1 v) Int.zero = false) as ->; [| reflexivity].
  unfold rc_sub1. rewrite EA.
  destruct (Int.eq v Int.zero) eqn:E0; [vm_compute; reflexivity |].
  destruct (rc_neg v) eqn:EN; [vm_compute; reflexivity |].
  simpl. apply prot3_shim_rc_sub_one. intros ->. rewrite Int.eq_true in EA. discriminate.
Qed.

End Bodies.

Theorem prot_bodies3_shim_rc :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body (QPvarspecs Shim.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_shim_refcount_warn_saturate wg_shim_refcount_warn_saturate_spec) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_shim_refcount_neg wg_shim_refcount_neg_spec) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_shim_refcount_inc_not_zero wg_shim_refcount_inc_not_zero_spec) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_shim_refcount_inc wg_shim_refcount_inc_spec) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_shim_refcount_dec_and_test wg_shim_refcount_dec_and_test_spec).
Proof.
  intros.
  split; [apply prot3_shim_rc_body_warn_saturate |].
  split; [apply prot3_shim_rc_body_neg |].
  split; [apply prot3_shim_rc_body_inc_not_zero |].
  split; [apply prot3_shim_rc_body_inc |].
  apply prot3_shim_rc_body_dec_and_test.
Qed.
