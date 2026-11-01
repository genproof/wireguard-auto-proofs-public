(* nb port of the hc4b_ke_k1_seg.v. [segments of kent_same_but_next, split out of hc4nb2_ke_k1.v for the Qed budget], (common4 group kents): the body of kent_same_but_next. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4a_nb_cs.
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require Import WgNoise.proof.harness.common4.hc4a_nb_ctx.
Require Import WgNoise.proof.harness.common4.hc4nb2_ke_hf.
Require Import WgNoise.proof.harness.common4.hc4nb2_ke_hf2.
Require Import WgNoise.proof.harness.common4.hc4nb2_ke_k1_vp.
Require Import WgNoise.proof.harness.common4.hc4nb2_ke_k1_lem.
Require WgNoise.harness.x_cookie_mac.code.
Local Open Scope logic.

Module FC := WgNoise.harness.x_cookie_mac.code.

(* the Clight of kent_same_but_next's || chain, cut in three (verbatim from src/harness/cookie_mac/code.v) *)
Definition hc4nb2_ke_k1_X3 : statement := (Ssequence (Ssequence (Ssequence (Sset FC._t'44 (Efield (Efield (Ederef (Etempvar FC._kp (tptr (Tstruct FC._noise_keypair noattr))) (Tstruct FC._noise_keypair noattr)) FC._entry (Tstruct FC._index_hashtable_entry noattr)) FC._peer (tptr (Tstruct FC._wg_peer noattr)))) (Ssequence (Sset FC._t'45 (Efield (Ederef (Etempvar FC._l (tptr (Tstruct FC._kent noattr))) (Tstruct FC._kent noattr)) FC._peer0 (tptr (Tstruct FC._wg_peer noattr)))) (Sifthenelse (Ebinop Cop.One (Etempvar FC._t'44 (tptr (Tstruct FC._wg_peer noattr))) (Etempvar FC._t'45 (tptr (Tstruct FC._wg_peer noattr))) tint) (Sset FC._t'1 (Econst_int (Int.repr 1) tint)) (Ssequence (Sset FC._t'46 (Efield (Efield (Ederef (Etempvar FC._kp (tptr (Tstruct FC._noise_keypair noattr))) (Tstruct FC._noise_keypair noattr)) FC._entry (Tstruct FC._index_hashtable_entry noattr)) FC._type tint)) (Ssequence (Sset FC._t'47 (Efield (Ederef (Etempvar FC._l (tptr (Tstruct FC._kent noattr))) (Tstruct FC._kent noattr)) FC._type0 tint)) (Sset FC._t'1 (Ecast (Ebinop Cop.One (Etempvar FC._t'46 tint) (Etempvar FC._t'47 tint) tint) tbool))))))) (Sifthenelse (Etempvar FC._t'1 tint) (Sset FC._t'2 (Econst_int (Int.repr 1) tint)) (Ssequence (Sset FC._t'42 (Efield (Efield (Ederef (Etempvar FC._kp (tptr (Tstruct FC._noise_keypair noattr))) (Tstruct FC._noise_keypair noattr)) FC._entry (Tstruct FC._index_hashtable_entry noattr)) FC._index tuint)) (Ssequence (Sset FC._t'43 (Efield (Ederef (Etempvar FC._l (tptr (Tstruct FC._kent noattr))) (Tstruct FC._kent noattr)) FC._index0 tuint)) (Sset FC._t'2 (Ecast (Ebinop Cop.One (Etempvar FC._t'42 tuint) (Etempvar FC._t'43 tuint) tint) tbool)))))) (Sifthenelse (Etempvar FC._t'2 tint) (Sset FC._t'3 (Econst_int (Int.repr 1) tint)) (Ssequence (Sset FC._t'40 (Efield (Efield (Ederef (Etempvar FC._kp (tptr (Tstruct FC._noise_keypair noattr))) (Tstruct FC._noise_keypair noattr)) FC._entry (Tstruct FC._index_hashtable_entry noattr)) FC._hashed tbool)) (Ssequence (Sset FC._t'41 (Efield (Ederef (Etempvar FC._l (tptr (Tstruct FC._kent noattr))) (Tstruct FC._kent noattr)) FC._hashed0 tbool)) (Sset FC._t'3 (Ecast (Ebinop Cop.One (Etempvar FC._t'40 tbool) (Etempvar FC._t'41 tbool) tint) tbool)))))).
Definition hc4nb2_ke_k1_s4 : statement := (Sifthenelse (Etempvar FC._t'3 tint) (Sset FC._t'4 (Econst_int (Int.repr 1) tint)) (Ssequence (Scall (Some FC._t'5) (Evar FC._bytes_eq (Tfunction ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil) tint cc_default)) ((Efield (Efield (Ederef (Etempvar FC._kp (tptr (Tstruct FC._noise_keypair noattr))) (Tstruct FC._noise_keypair noattr)) FC._sending (Tstruct FC._noise_symmetric_key noattr)) FC._key (tarray tuchar 32)) :: (Efield (Ederef (Etempvar FC._l (tptr (Tstruct FC._kent noattr))) (Tstruct FC._kent noattr)) FC._skey0 (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) :: nil)) (Sset FC._t'4 (Ecast (Eunop Onotbool (Etempvar FC._t'5 tint) tint) tbool)))).
Definition hc4nb2_ke_k1_s6 : statement := (Sifthenelse (Etempvar FC._t'4 tint) (Sset FC._t'6 (Econst_int (Int.repr 1) tint)) (Ssequence (Scall (Some FC._t'7) (Evar FC._bytes_eq (Tfunction ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil) tint cc_default)) ((Efield (Efield (Ederef (Etempvar FC._kp (tptr (Tstruct FC._noise_keypair noattr))) (Tstruct FC._noise_keypair noattr)) FC._receiving (Tstruct FC._noise_symmetric_key noattr)) FC._key (tarray tuchar 32)) :: (Efield (Ederef (Etempvar FC._l (tptr (Tstruct FC._kent noattr))) (Tstruct FC._kent noattr)) FC._rkey0 (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) :: nil)) (Sset FC._t'6 (Ecast (Eunop Onotbool (Etempvar FC._t'7 tint) tint) tbool)))).
Definition hc4nb2_ke_k1_s8 : statement := (Sifthenelse (Etempvar FC._t'6 tint) (Sset FC._t'8 (Econst_int (Int.repr 1) tint)) (Ssequence (Sset FC._t'38 (Efield (Efield (Ederef (Etempvar FC._kp (tptr (Tstruct FC._noise_keypair noattr))) (Tstruct FC._noise_keypair noattr)) FC._sending (Tstruct FC._noise_symmetric_key noattr)) FC._birthdate tulong)) (Ssequence (Sset FC._t'39 (Efield (Ederef (Etempvar FC._l (tptr (Tstruct FC._kent noattr))) (Tstruct FC._kent noattr)) FC._sbirth0 tulong)) (Sset FC._t'8 (Ecast (Ebinop Cop.One (Etempvar FC._t'38 tulong) (Etempvar FC._t'39 tulong) tint) tbool))))).
Definition hc4nb2_ke_k1_s9 : statement := (Sifthenelse (Etempvar FC._t'8 tint) (Sset FC._t'9 (Econst_int (Int.repr 1) tint)) (Ssequence (Sset FC._t'36 (Efield (Efield (Ederef (Etempvar FC._kp (tptr (Tstruct FC._noise_keypair noattr))) (Tstruct FC._noise_keypair noattr)) FC._receiving (Tstruct FC._noise_symmetric_key noattr)) FC._birthdate tulong)) (Ssequence (Sset FC._t'37 (Efield (Ederef (Etempvar FC._l (tptr (Tstruct FC._kent noattr))) (Tstruct FC._kent noattr)) FC._rbirth0 tulong)) (Sset FC._t'9 (Ecast (Ebinop Cop.One (Etempvar FC._t'36 tulong) (Etempvar FC._t'37 tulong) tint) tbool))))).
Definition hc4nb2_ke_k1_X9 : statement := Ssequence (Ssequence (Ssequence (Ssequence hc4nb2_ke_k1_X3 hc4nb2_ke_k1_s4) hc4nb2_ke_k1_s6) hc4nb2_ke_k1_s8) hc4nb2_ke_k1_s9.
Definition hc4nb2_ke_k1_s10 : statement := (Sifthenelse (Etempvar FC._t'9 tint) (Sset FC._t'10 (Econst_int (Int.repr 1) tint)) (Ssequence (Sset FC._t'34 (Efield (Efield (Ederef (Etempvar FC._kp (tptr (Tstruct FC._noise_keypair noattr))) (Tstruct FC._noise_keypair noattr)) FC._sending (Tstruct FC._noise_symmetric_key noattr)) FC._is_valid tbool)) (Ssequence (Sset FC._t'35 (Efield (Ederef (Etempvar FC._l (tptr (Tstruct FC._kent noattr))) (Tstruct FC._kent noattr)) FC._svalid0 tbool)) (Sset FC._t'10 (Ecast (Ebinop Cop.One (Etempvar FC._t'34 tbool) (Etempvar FC._t'35 tbool) tint) tbool))))).
Definition hc4nb2_ke_k1_s11 : statement := (Sifthenelse (Etempvar FC._t'10 tint) (Sset FC._t'11 (Econst_int (Int.repr 1) tint)) (Ssequence (Sset FC._t'32 (Efield (Efield (Ederef (Etempvar FC._kp (tptr (Tstruct FC._noise_keypair noattr))) (Tstruct FC._noise_keypair noattr)) FC._receiving (Tstruct FC._noise_symmetric_key noattr)) FC._is_valid tbool)) (Ssequence (Sset FC._t'33 (Efield (Ederef (Etempvar FC._l (tptr (Tstruct FC._kent noattr))) (Tstruct FC._kent noattr)) FC._rvalid0 tbool)) (Sset FC._t'11 (Ecast (Ebinop Cop.One (Etempvar FC._t'32 tbool) (Etempvar FC._t'33 tbool) tint) tbool))))).
Definition hc4nb2_ke_k1_s12 : statement := (Sifthenelse (Etempvar FC._t'11 tint) (Sset FC._t'12 (Econst_int (Int.repr 1) tint)) (Ssequence (Sset FC._t'30 (Efield (Efield (Ederef (Etempvar FC._kp (tptr (Tstruct FC._noise_keypair noattr))) (Tstruct FC._noise_keypair noattr)) FC._sending_counter (Tstruct FC.___gp_atomic64_t noattr)) FC._counter tlong)) (Ssequence (Sset FC._t'31 (Efield (Ederef (Etempvar FC._l (tptr (Tstruct FC._kent noattr))) (Tstruct FC._kent noattr)) FC._scnt0 tlong)) (Sset FC._t'12 (Ecast (Ebinop Cop.One (Etempvar FC._t'30 tlong) (Etempvar FC._t'31 tlong) tint) tbool))))).
Definition hc4nb2_ke_k1_s13 : statement := (Sifthenelse (Etempvar FC._t'12 tint) (Sset FC._t'13 (Econst_int (Int.repr 1) tint)) (Ssequence (Sset FC._t'28 (Efield (Efield (Ederef (Etempvar FC._kp (tptr (Tstruct FC._noise_keypair noattr))) (Tstruct FC._noise_keypair noattr)) FC._receiving_counter (Tstruct FC._noise_replay_counter noattr)) FC._counter tulong)) (Ssequence (Sset FC._t'29 (Efield (Ederef (Etempvar FC._l (tptr (Tstruct FC._kent noattr))) (Tstruct FC._kent noattr)) FC._rcnt0 tulong)) (Sset FC._t'13 (Ecast (Ebinop Cop.One (Etempvar FC._t'28 tulong) (Etempvar FC._t'29 tulong) tint) tbool))))).
Definition hc4nb2_ke_k1_s14 : statement := (Sifthenelse (Etempvar FC._t'13 tint) (Sset FC._t'14 (Econst_int (Int.repr 1) tint)) (Ssequence (Sset FC._t'26 (Efield (Ederef (Etempvar FC._kp (tptr (Tstruct FC._noise_keypair noattr))) (Tstruct FC._noise_keypair noattr)) FC._remote_index tuint)) (Ssequence (Sset FC._t'27 (Efield (Ederef (Etempvar FC._l (tptr (Tstruct FC._kent noattr))) (Tstruct FC._kent noattr)) FC._remote_index0 tuint)) (Sset FC._t'14 (Ecast (Ebinop Cop.One (Etempvar FC._t'26 tuint) (Etempvar FC._t'27 tuint) tint) tbool))))).
Definition hc4nb2_ke_k1_s15 : statement := (Sifthenelse (Etempvar FC._t'14 tint) (Sset FC._t'15 (Econst_int (Int.repr 1) tint)) (Ssequence (Sset FC._t'24 (Efield (Ederef (Etempvar FC._kp (tptr (Tstruct FC._noise_keypair noattr))) (Tstruct FC._noise_keypair noattr)) FC._i_am_the_initiator tbool)) (Ssequence (Sset FC._t'25 (Efield (Ederef (Etempvar FC._l (tptr (Tstruct FC._kent noattr))) (Tstruct FC._kent noattr)) FC._initiator0 tbool)) (Sset FC._t'15 (Ecast (Ebinop Cop.One (Etempvar FC._t'24 tbool) (Etempvar FC._t'25 tbool) tint) tbool))))).
Definition hc4nb2_ke_k1_s16 : statement := (Sifthenelse (Etempvar FC._t'15 tint) (Sset FC._t'16 (Econst_int (Int.repr 1) tint)) (Ssequence (Sset FC._t'22 (Efield (Efield (Ederef (Etempvar FC._kp (tptr (Tstruct FC._noise_keypair noattr))) (Tstruct FC._noise_keypair noattr)) FC._refcount (Tstruct FC._kref noattr)) FC._refcount tuint)) (Ssequence (Sset FC._t'23 (Efield (Ederef (Etempvar FC._l (tptr (Tstruct FC._kent noattr))) (Tstruct FC._kent noattr)) FC._refs0 tuint)) (Sset FC._t'16 (Ecast (Ebinop Cop.One (Etempvar FC._t'22 tuint) (Etempvar FC._t'23 tuint) tint) tbool))))).
Definition hc4nb2_ke_k1_s17 : statement := (Sifthenelse (Etempvar FC._t'16 tint) (Sset FC._t'17 (Econst_int (Int.repr 1) tint)) (Ssequence (Sset FC._t'20 (Efield (Ederef (Etempvar FC._kp (tptr (Tstruct FC._noise_keypair noattr))) (Tstruct FC._noise_keypair noattr)) FC._internal_id tulong)) (Ssequence (Sset FC._t'21 (Efield (Ederef (Etempvar FC._l (tptr (Tstruct FC._kent noattr))) (Tstruct FC._kent noattr)) FC._id0 tulong)) (Sset FC._t'17 (Ecast (Ebinop Cop.One (Etempvar FC._t'20 tulong) (Etempvar FC._t'21 tulong) tint) tbool))))).
Definition hc4nb2_ke_k1_X16 : statement := (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence hc4nb2_ke_k1_X9 hc4nb2_ke_k1_s10) hc4nb2_ke_k1_s11) hc4nb2_ke_k1_s12) hc4nb2_ke_k1_s13) hc4nb2_ke_k1_s14) hc4nb2_ke_k1_s15) hc4nb2_ke_k1_s16) hc4nb2_ke_k1_s17).

Lemma hc4nb2_ke_k1_vpn p : valid_pointer p |-- !! is_pointer_or_null p.
Proof. constructor. apply valid_pointer_is_pointer_or_null. Qed.

Definition hc4nb2_ke_k1_is (a b: bool) : Prop := a = b.

Lemma hc4nb2_ke_k1_tt (b: bool) : typed_true tint (Val.of_bool (negb b)) -> b = false.
Proof. destruct b; auto. intros X. inv X. Qed.
Lemma hc4nb2_ke_k1_tf (b: bool) : typed_false tint (Val.of_bool (negb b)) -> b = true.
Proof. destruct b; auto. intros X. inv X. Qed.

Lemma hc4nb2_ke_k1_drop2 (Delta: tycontext) P i (v v': val) x1 x2 Q R :
  v = v' ->
  ENTAIL Delta, PROPx P (LOCALx (temp i v :: x1 :: x2 :: Q) (SEPx R)) |-- PROPx P (LOCALx (temp i v' :: Q) (SEPx R)).
Proof.
  intros <-. apply andp_left2. apply andp_derives; [apply derives_refl|].
  unfold LOCALx. apply andp_derives; [|apply derives_refl].
  intro rho. unfold local, lift1. simpl. apply prop_derives. unfold_lift. tauto.
Qed.

Lemma hc4nb2_ke_k1_b2v b : bool2val b = Val.of_bool b.
Proof. destruct b; reflexivity. Qed.

(* one step of the || chain: t' = t'prev ? 1 : (cur != snap); the new prefix p = q && c *)
Ltac hc4nb2_ke_k1_cmpfin :=
  first [ apply hc4nb2_ke_k1_b2v | reflexivity
        | match goal with |- context [Bool.eqb ?x ?y] => destruct x, y; reflexivity end ].

Lemma hc4nb2_ke_k1_vf {cs: compspecs} (l: list byte) : value_fits (tarray tuchar 32) (bytes l) -> Zlength l = 32.
Proof.
  intros X. rewrite value_fits_eq in X. simpl in X. destruct X as [X _].
  change (Zlength (bytes l) = 32) in X. unfold bytes in X. rewrite Zlength_map in X. exact X.
Qed.

Lemma hc4nb2_ke_k1_tcb (Delta: tycontext) P b : ENTAIL Delta, P |-- local (liftx (tc_val tbool (Val.of_bool b))).
Proof. intro rho. unfold local, lift1; simpl. apply prop_right. destruct b; hnf; auto. Qed.

(* forward, with the tc side goal of a _Bool load *)
Ltac hc4nb2_ke_k1_fw :=
  forward;
  repeat match goal with |- context [let (_, y) := let (_, y) := symkey_val ?S in y in y] =>
    change (let (_, y) := let (_, y) := symkey_val S in y in y) with (Val.of_bool (sk_valid S)) end;
  try match goal with |- ENTAIL _, _ |-- local (liftx (tc_val tbool (Val.of_bool _))) =>
                 apply hc4nb2_ke_k1_tcb end.

Ltac hc4nb2_ke_k1_els Ceq Peq :=
  match goal with Hf: typed_false tint _ |- _ => apply hc4nb2_ke_k1_tf in Hf end;
  hc4nb2_ke_k1_fw; hc4nb2_ke_k1_fw; hc4nb2_ke_k1_fw;
  unfold hc4nb2_ke_k1_is in Peq; rewrite Peq;
  match goal with Hf: ?q = true |- context [andb ?q _] => rewrite Hf end; cbn [andb];
  apply hc4nb2_ke_k1_drop2; unfold hc4nb2_ke_k1_is in Ceq; rewrite Ceq; hc4nb2_ke_k1_cmpfin.

Ltac hc4nb2_ke_k1_step tnew cexp c q p Ceq Peq :=
  remember cexp as c eqn:Ceq; change (hc4nb2_ke_k1_is c cexp) in Ceq;
  remember (andb q c) as p eqn:Peq; change (hc4nb2_ke_k1_is p (andb q c)) in Peq;
  forward_if (temp tnew (Val.of_bool (negb p)));
  [ forward;
    match goal with Ht: typed_true tint _ |- _ => apply hc4nb2_ke_k1_tt in Ht; unfold hc4nb2_ke_k1_is in Peq; rewrite Peq, Ht end;
    apply ENTAIL_refl
  | | ].

Section K1.
Variable CSw: compspecs.
#[local] Existing Instance CS4nb.

#[local] Instance hc4nb2_ke_k1_cce3 : change_composite_env Noise.CS CS4nb.
Proof. make_cs_preserve Noise.CS CS4nb. Defined.

Ltac hc4nb2_ke_k1_cc2 :=
  repeat match goal with
  | |- context [@field_at Noise.CS ?sh ?t ?gfs ?v ?p] =>
      rewrite (f_equal (fun f => f p) (@field_at_change_composite Noise.CS CS4nb hc4nb2_ke_k1_cce3 sh t gfs v v (JMeq_refl v) eq_refl))
  end.

(* the keys of the keypair's symmetric keys (fields at Noise.CS), lent to bytes_eq *)
Lemma hc4nb2_ke_k1_key_sN sh k Ks :
  Zlength (sk_key Ks) = 32 -> @field_compatible CS4nb t_kp [] k ->
  @field_at Noise.CS sh t_kp (DOT I._sending) (symkey_val Ks) k |--
  hbytes sh (sk_key Ks) (field_address t_kp [StructField I._key; StructField I._sending] k) *
  (hbytes sh (sk_key Ks) (field_address t_kp [StructField I._key; StructField I._sending] k) -*
   @field_at Noise.CS sh t_kp (DOT I._sending) (symkey_val Ks) k).
Proof.
  intros L FC. hc4nb2_ke_k1_cc2. apply hc4nb2_ke_k1_key_s; auto. Qed.

Lemma hc4nb2_ke_k1_key_rN sh k Ks :
  Zlength (sk_key Ks) = 32 -> @field_compatible CS4nb t_kp [] k ->
  @field_at Noise.CS sh t_kp (DOT I._receiving) (symkey_val Ks) k |--
  hbytes sh (sk_key Ks) (field_address t_kp [StructField I._key; StructField I._receiving] k) *
  (hbytes sh (sk_key Ks) (field_address t_kp [StructField I._key; StructField I._receiving] k) -*
   @field_at Noise.CS sh t_kp (DOT I._receiving) (symkey_val Ks) k).
Proof.
  intros L FC. hc4nb2_ke_k1_cc2. apply hc4nb2_ke_k1_key_r; auto. Qed.

(* the model's comparison in the C order (current vs snapshot) *)
Lemma hc4nb2_ke_k1_eqd_sym (a b: val) :
  (if eq_dec a b then true else false) = (if eq_dec b a then true else false).
Proof. destruct (eq_dec a b), (eq_dec b a); congruence. Qed.

Lemma hc4nb2_ke_k1_beqb_sym (a b: bool) : Bool.eqb a b = Bool.eqb b a.
Proof. destruct a, b; reflexivity. Qed.

Lemma hc4nb2_ke_k1_bytes_sym (a b: list byte) : bytes_eqb a b = bytes_eqb b a.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a b), (list_eq_dec Byte.eq_dec b a); congruence. Qed.

Lemma hc4nb2_ke_k1_model s E h K :
  kent_eqb_nn s E h K = (
  (if eq_dec (e_peer E) (e_peer (ks_E s)) then true else false) && Int.eq (e_type E) (e_type (ks_E s)) &&
  Int.eq (e_index E) (e_index (ks_E s)) && Bool.eqb h (ks_hashed s) &&
  bytes_eqb (sk_key (kp_send K)) (sk_key (kp_send (ks_K s))) &&
  bytes_eqb (sk_key (kp_recv K)) (sk_key (kp_recv (ks_K s))) &&
  Int64.eq (sk_birth (kp_send K)) (sk_birth (kp_send (ks_K s))) &&
  Int64.eq (sk_birth (kp_recv K)) (sk_birth (kp_recv (ks_K s))) &&
  Bool.eqb (sk_valid (kp_send K)) (sk_valid (kp_send (ks_K s))) &&
  Bool.eqb (sk_valid (kp_recv K)) (sk_valid (kp_recv (ks_K s))) &&
  Int64.eq (kp_scounter K) (kp_scounter (ks_K s)) && Int64.eq (kp_rcounter K) (kp_rcounter (ks_K s)) &&
  Int.eq (kp_rindex K) (kp_rindex (ks_K s)) && Bool.eqb (kp_init K) (kp_init (ks_K s)) &&
  Int.eq (kp_refs K) (kp_refs (ks_K s)) && Int64.eq (kp_id K) (kp_id (ks_K s)) &&
  int64s_eqb (kp_backtrack (ks_K s)) (kp_backtrack K))%bool.
Proof.
  unfold kent_eqb_nn, entry_eqb, kp_eqb, symkey_eqb.
  rewrite (hc4nb2_ke_k1_eqd_sym (e_peer (ks_E s))), (Int.eq_sym (e_type (ks_E s))), (Int.eq_sym (e_index (ks_E s))),
    (hc4nb2_ke_k1_beqb_sym (ks_hashed s)), (hc4nb2_ke_k1_bytes_sym (sk_key (kp_send (ks_K s)))),
    (hc4nb2_ke_k1_bytes_sym (sk_key (kp_recv (ks_K s)))), (Int64.eq_sym (sk_birth (kp_send (ks_K s)))),
    (Int64.eq_sym (sk_birth (kp_recv (ks_K s)))), (hc4nb2_ke_k1_beqb_sym (sk_valid (kp_send (ks_K s)))),
    (hc4nb2_ke_k1_beqb_sym (sk_valid (kp_recv (ks_K s)))), (Int64.eq_sym (kp_scounter (ks_K s))),
    (Int64.eq_sym (kp_rcounter (ks_K s))), (Int.eq_sym (kp_rindex (ks_K s))), (hc4nb2_ke_k1_beqb_sym (kp_init (ks_K s))),
    (Int.eq_sym (kp_refs (ks_K s))), (Int64.eq_sym (kp_id (ks_K s))).
  apply eq_true_iff_eq. rewrite !andb_true_iff. tauto.
Qed.

Lemma hc4nb2_ke_k1_i64s (a b: list int64) : int64s_eqb a b = true <-> a = b.
Proof.
  revert b. induction a as [|x a IH]; destruct b as [|y b]; simpl; split; intros X; try discriminate; auto.
  - rewrite andb_true_iff in X. destruct X as [X1 X2]. apply Int64.same_if_eq in X1. apply IH in X2. congruence.
  - inv X. rewrite Int64.eq_true. simpl. apply IH. reflexivity.
Qed.

Lemma hc4nb2_ke_k1_vfl {cs: compspecs} (l: list int64) :
  value_fits (tarray tulong 128) (map Vlong l) -> Zlength l = 128.
Proof.
  intros X. rewrite value_fits_eq in X. simpl in X. destruct X as [X _].
  change (Zlength (map Vlong l) = 128) in X. rewrite Zlength_map in X. exact X.
Qed.

Lemma hc4nb2_ke_k1_sub (a b: list int64) i :
  0 <= i < Zlength a -> Zlength a = Zlength b -> sublist 0 i a = sublist 0 i b ->
  Int64.eq (Znth i a) (Znth i b) = true -> sublist 0 (i + 1) a = sublist 0 (i + 1) b.
Proof.
  intros R L S E. rewrite (sublist_split 0 i (i + 1) a), (sublist_split 0 i (i + 1) b) by lia.
  rewrite S. f_equal. rewrite !sublist_len_1 by lia. apply Int64.same_if_eq in E. congruence.
Qed.

(* the close of the opened kent, with the keypair's symmetric keys at CS4nb *)
Lemma hc4nb2_ke_k1_close4 sht tab T k K s nx sh E lk r :
  itable_wf T -> sfind (t_D T) k = Some (sh, E) ->
  @field_compatible CS4nb t_kp [] k -> @field_compatible Noise.CS t_kp [] k -> kp_ok K ->
  @field_compatible CKS t_kent [] k ->
  hc4nb2_ke_k1_ent sh T k E * hc4nb2_ke_hf2_irest sht tab T k *
  (@field_at CS4nb Ews t_kp (DOT I._sending) (symkey_val (kp_send K)) k *
   field_at Ews t_kp (DOT I._sending_counter) (Vlong (kp_scounter K)) k *
   @field_at CS4nb Ews t_kp (DOT I._receiving) (symkey_val (kp_recv K)) k *
   field_at Ews t_kp (DOT I._receiving_counter) (Vlong (kp_rcounter K), (lk, map Vlong (kp_backtrack K))) k *
   field_at Ews t_kp (DOT I._remote_index) (Vint (kp_rindex K)) k *
   field_at Ews t_kp (DOT I._i_am_the_initiator) (Val.of_bool (kp_init K)) k *
   field_at Ews t_kp (DOT I._refcount) (Vint (kp_refs K)) k *
   field_at Ews t_kp (DOT I._rcu) r k *
   field_at Ews t_kp (DOT I._internal_id) (Vlong (kp_id K)) k *
   spacer Ews 1181 1184 k) * hc4nb2_ke_k1_sn k s * hc4nb2_ke_k1_fr CSw k nx |--
  kent_cell CSw (mkKe k K (Some s)) nx * itable sht tab T.
Proof.
  intros W F FC4 FCn OK FCk.
  eapply derives_trans; [|apply (hc4nb2_ke_k1_close CSw sht tab T k K s nx sh E lk r W F FC4 FCn OK FCk)].
  unfold hc4nb2_ke_k1_kp. hc4nb2_ke_k1_cc2. apply derives_refl.
Qed.

Ltac hc4nb2_ke_k1_vpt CSw sht tab T k sh E VO x HVO VQ W F FC4 :=
  eapply derives_trans; [| apply (hc4nb2_ke_k1_vp CSw sht tab T k sh E VO x TT HVO VQ W F FC4)];
  unfold hc4nb2_ke_k1_ent; cancel.

(* the opened kent (hc4nb2_ke_k1_open, the keypair's symmetric keys at CS4nb) *)
Definition hc4nb2_ke_k1_St (sh: share) (T: tstate) (k: val) (E: entry) (K: keypair) (s: ksnap) (lk r nx: val)
    (sht: share) (tab: val) (VO: list vobj) : list mpred :=
  [@field_at CS4nb sh t_kp (DOT I._entry)
     (e_peer E, (succ_in (t_L T) k, (Val.of_bool (vin k (t_L T)), (Vint (e_type E), Vint (e_index E))))) k;
   hc4nb2_ke_hf2_irest sht tab T k;
   @field_at CS4nb Ews t_kp (DOT I._sending) (symkey_val (kp_send K)) k;
   @field_at CS4nb Ews t_kp (DOT I._sending_counter) (Vlong (kp_scounter K)) k;
   @field_at CS4nb Ews t_kp (DOT I._receiving) (symkey_val (kp_recv K)) k;
   @field_at CS4nb Ews t_kp (DOT I._receiving_counter) (Vlong (kp_rcounter K), (lk, map Vlong (kp_backtrack K))) k;
   @field_at CS4nb Ews t_kp (DOT I._remote_index) (Vint (kp_rindex K)) k;
   @field_at CS4nb Ews t_kp (DOT I._i_am_the_initiator) (Val.of_bool (kp_init K)) k;
   @field_at CS4nb Ews t_kp (DOT I._refcount) (Vint (kp_refs K)) k;
   @field_at CS4nb Ews t_kp (DOT I._rcu) r k;
   @field_at CS4nb Ews t_kp (DOT I._internal_id) (Vlong (kp_id K)) k;
   spacer Ews 1181 1184 k;
   @field_at CS4nb Ews t_kent (DOT HC._peer0) (e_peer (ks_E s)) k;
   @field_at CS4nb Ews t_kent (DOT HC._next0) (ks_next s) k;
   @field_at CS4nb Ews t_kent (DOT HC._type0) (Vint (e_type (ks_E s))) k;
   @field_at CS4nb Ews t_kent (DOT HC._index0) (Vint (e_index (ks_E s))) k;
   @field_at CS4nb Ews t_kent (DOT HC._hashed0) (Val.of_bool (ks_hashed s)) k;
   @field_at CS4nb Ews t_kent (DOT HC._skey0) (bytes (sk_key (kp_send (ks_K s)))) k;
   @field_at CS4nb Ews t_kent (DOT HC._rkey0) (bytes (sk_key (kp_recv (ks_K s)))) k;
   @field_at CS4nb Ews t_kent (DOT HC._sbirth0) (Vlong (sk_birth (kp_send (ks_K s)))) k;
   @field_at CS4nb Ews t_kent (DOT HC._rbirth0) (Vlong (sk_birth (kp_recv (ks_K s)))) k;
   @field_at CS4nb Ews t_kent (DOT HC._svalid0) (Val.of_bool (sk_valid (kp_send (ks_K s)))) k;
   @field_at CS4nb Ews t_kent (DOT HC._rvalid0) (Val.of_bool (sk_valid (kp_recv (ks_K s)))) k;
   @field_at CS4nb Ews t_kent (DOT HC._scnt0) (Vlong (kp_scounter (ks_K s))) k;
   @field_at CS4nb Ews t_kent (DOT HC._rcnt0) (Vlong (kp_rcounter (ks_K s))) k;
   @field_at CS4nb Ews t_kent (DOT HC._bt0) (map Vlong (kp_backtrack (ks_K s))) k;
   @field_at CS4nb Ews t_kent (DOT HC._remote_index0) (Vint (kp_rindex (ks_K s))) k;
   @field_at CS4nb Ews t_kent (DOT HC._initiator0) (Val.of_bool (kp_init (ks_K s))) k;
   @field_at CS4nb Ews t_kent (DOT HC._refs0) (Vint (kp_refs (ks_K s))) k;
   @field_at CS4nb Ews t_kent (DOT HC._id0) (Vlong (kp_id (ks_K s))) k;
   hc4nb2_ke_k1_fr CSw k nx; vobjs CSw VO].

(* the || chain's prefixes, in the C order *)
Definition hc4nb2_ke_k1_m3 (T: tstate) (k: val) (E: entry) (s: ksnap) : bool :=
  ((if eq_dec (e_peer E) (e_peer (ks_E s)) then true else false) && Int.eq (e_type E) (e_type (ks_E s)) &&
   Int.eq (e_index E) (e_index (ks_E s)) && Bool.eqb (vin k (t_L T)) (ks_hashed s))%bool.
Definition hc4nb2_ke_k1_m9 (T: tstate) (k: val) (E: entry) (K: keypair) (s: ksnap) : bool :=
  (hc4nb2_ke_k1_m3 T k E s && bytes_eqb (sk_key (kp_send K)) (sk_key (kp_send (ks_K s))) &&
   bytes_eqb (sk_key (kp_recv K)) (sk_key (kp_recv (ks_K s))) &&
   Int64.eq (sk_birth (kp_send K)) (sk_birth (kp_send (ks_K s))) &&
   Int64.eq (sk_birth (kp_recv K)) (sk_birth (kp_recv (ks_K s))))%bool.
Definition hc4nb2_ke_k1_m17 (T: tstate) (k: val) (E: entry) (K: keypair) (s: ksnap) : bool :=
  (hc4nb2_ke_k1_m9 T k E K s && Bool.eqb (sk_valid (kp_send K)) (sk_valid (kp_send (ks_K s))) &&
   Bool.eqb (sk_valid (kp_recv K)) (sk_valid (kp_recv (ks_K s))) &&
   Int64.eq (kp_scounter K) (kp_scounter (ks_K s)) && Int64.eq (kp_rcounter K) (kp_rcounter (ks_K s)) &&
   Int.eq (kp_rindex K) (kp_rindex (ks_K s)) && Bool.eqb (kp_init K) (kp_init (ks_K s)) &&
   Int.eq (kp_refs K) (kp_refs (ks_K s)) && Int64.eq (kp_id K) (kp_id (ks_K s)))%bool.

Definition hc4nb2_ke_k1_Delta : tycontext := func_tycontext FC.f_kent_same_but_next [] hc4_G_dev_same nil.

Lemma hc4nb2_ke_k1_LA {Espec: OracleKind} k K s nx sht tab T VO sh E lk r :
  Forall vobj_ok VO -> itable_wf T -> sfind (t_D T) k = Some (sh, E) -> @field_compatible CS4nb t_kp [] k ->
  (e_peer (ks_E s) = nullval \/ In (e_peer (ks_E s)) (saddrs (t_D T)) \/
   In (e_peer (ks_E s)) (hc4nb2_ke_k1_vobjs_vaddrs VO)) ->
  (e_peer E = nullval \/ In (e_peer E) (saddrs (t_D T)) \/ In (e_peer E) (hc4nb2_ke_k1_vobjs_vaddrs VO)) ->
  is_pointer_or_null (e_peer E) -> is_pointer_or_null (e_peer (ks_E s)) ->
  semax hc4nb2_ke_k1_Delta
    (PROPx [] (LOCALx [temp FC._kp k; temp FC._l k] (SEPx (hc4nb2_ke_k1_St sh T k E K s lk r nx sht tab VO))))
    hc4nb2_ke_k1_X3
    (normal_ret_assert (PROPx [] (LOCALx [temp FC._t'3 (Val.of_bool (negb (hc4nb2_ke_k1_m3 T k E s)));
      temp FC._kp k; temp FC._l k] (SEPx (hc4nb2_ke_k1_St sh T k E K s lk r nx sht tab VO))))).
Proof.
  intros H W F FC4 VQ1 VQ2 PN2 PN1.
  assert (RS: readable_share sh).
  { apply writable_readable_share. destruct W as (_ & _ & _ & HF). pose proof (hc4nb2_ke_hf2_sfind_In _ _ _ _ F) as F'.
    rewrite Forall_forall in HF. apply (HF _ F'). }
  unfold hc4nb2_ke_k1_St, hc4nb2_ke_k1_X3, hc4nb2_ke_k1_Delta, hc4nb2_ke_k1_m3. abbreviate_semax.
  forward. forward.
  remember (if eq_dec (e_peer E) (e_peer (ks_E s)) then true else false) as c1 eqn:C1.
  remember (Int.eq (e_type E) (e_type (ks_E s))) as c2 eqn:C2.
  remember (andb c1 c2) as p1 eqn:P1. change (hc4nb2_ke_k1_is p1 (andb c1 c2)) in P1.
  change (hc4nb2_ke_k1_is c1 (if eq_dec (e_peer E) (e_peer (ks_E s)) then true else false)) in C1.
  change (hc4nb2_ke_k1_is c2 (Int.eq (e_type E) (e_type (ks_E s)))) in C2.
  forward_if (temp FC._t'1 (Val.of_bool (negb p1))).
  { apply denote_tc_test_eq_split;
      [hc4nb2_ke_k1_vpt CSw sht tab T k sh E VO (e_peer E) H VQ2 W F FC4 |
       hc4nb2_ke_k1_vpt CSw sht tab T k sh E VO (e_peer (ks_E s)) H VQ1 W F FC4]. }
  { forward. entailer!. unfold hc4nb2_ke_k1_is in *. subst.
    destruct (eq_dec (e_peer E) (e_peer (ks_E s))); [contradiction | reflexivity]. }
  { forward. forward. forward. entailer!. unfold hc4nb2_ke_k1_is in *. subst.
    destruct (eq_dec (e_peer E) (e_peer (ks_E s))); [| contradiction]. cbn [andb].
    destruct (Int.eq (e_type E) (e_type (ks_E s))); reflexivity. }
  hc4nb2_ke_k1_step FC._t'2 (Int.eq (e_index E) (e_index (ks_E s))) c3 p1 p2 C3 P2.
  { hc4nb2_ke_k1_els C3 P2. }
  hc4nb2_ke_k1_step FC._t'3 (Bool.eqb (vin k (t_L T)) (ks_hashed s)) c4 p2 p3 C4 P3.
  { hc4nb2_ke_k1_els C4 P3. }
  entailer!.
Qed.

Lemma hc4nb2_ke_k1_LB {Espec: OracleKind} k K s nx sht tab T VO sh E lk r :
  Forall vobj_ok VO -> itable_wf T -> sfind (t_D T) k = Some (sh, E) -> @field_compatible CS4nb t_kp [] k ->
  (e_peer (ks_E s) = nullval \/ In (e_peer (ks_E s)) (saddrs (t_D T)) \/
   In (e_peer (ks_E s)) (hc4nb2_ke_k1_vobjs_vaddrs VO)) ->
  (e_peer E = nullval \/ In (e_peer E) (saddrs (t_D T)) \/ In (e_peer E) (hc4nb2_ke_k1_vobjs_vaddrs VO)) ->
  is_pointer_or_null (e_peer E) -> is_pointer_or_null (e_peer (ks_E s)) -> kp_ok K ->
  semax hc4nb2_ke_k1_Delta
    (PROPx [] (LOCALx [temp FC._kp k; temp FC._l k] (SEPx (hc4nb2_ke_k1_St sh T k E K s lk r nx sht tab VO))))
    hc4nb2_ke_k1_X9
    (normal_ret_assert (PROPx [] (LOCALx [temp FC._t'9 (Val.of_bool (negb (hc4nb2_ke_k1_m9 T k E K s)));
      temp FC._kp k; temp FC._l k] (SEPx (hc4nb2_ke_k1_St sh T k E K s lk r nx sht tab VO))))).
Proof.
  intros H W F FC4 VQ1 VQ2 PN2 PN1 OK.
  unfold hc4nb2_ke_k1_X9. rewrite <- !seq_assoc.
  eapply semax_seq'; [apply hc4nb2_ke_k1_LA; auto|].
  unfold hc4nb2_ke_k1_St, hc4nb2_ke_k1_s4, hc4nb2_ke_k1_s6, hc4nb2_ke_k1_s8, hc4nb2_ke_k1_s9, hc4nb2_ke_k1_m9, hc4nb2_ke_k1_Delta. abbreviate_semax.
  remember (hc4nb2_ke_k1_m3 T k E s) as p3 eqn:P3. change (hc4nb2_ke_k1_is p3 (hc4nb2_ke_k1_m3 T k E s)) in P3.
  assert_PROP (Zlength (sk_key (kp_send (ks_K s))) = 32 /\ Zlength (sk_key (kp_recv (ks_K s))) = 32) as LSR.
  { entailer!. split; match goal with X: value_fits _ (bytes ?l) |- Zlength ?l = 32 => exact (hc4nb2_ke_k1_vf _ X) end. }
  destruct LSR as [LS LR].
  hc4nb2_ke_k1_step FC._t'4 (bytes_eqb (sk_key (kp_send K)) (sk_key (kp_send (ks_K s)))) c5 p3 p4 C5 P4.
  { match goal with Hf: typed_false tint _ |- _ => apply hc4nb2_ke_k1_tf in Hf end.
    pose proof OK as (OK1 & OK2 & OK3).
    sep_apply (hc4nb2_ke_k1_key_s Ews k (kp_send K) OK1 FC4).
    assert_PROP (field_compatible t_kent (DOT HC._skey0) k) as FCx by entailer!.
    rewrite (hc4nb2_ke_k1_sn_skey0 Ews k _ LS).
    flatten_sepcon_in_SEP.
    forward_call (Ews, field_address t_kp [StructField I._key; StructField I._sending] k, sk_key (kp_send K),
                  Ews, field_address t_kent (DOT HC._skey0) k, sk_key (kp_send (ks_K s))).
    { rewrite OK1. entailer!. rewrite !field_address_offset by auto with field_compatible.
      pose proof FC4 as [Pk _]. destruct k; try contradiction. simpl. rewrite !Ptrofs.add_zero. reflexivity. }
    forward.
    sep_apply (modus_ponens_wand (hbytes Ews (sk_key (kp_send K)) (field_address t_kp [StructField I._key; StructField I._sending] k))).
    rewrite <- (hc4nb2_ke_k1_sn_skey0 Ews k _ LS).
    entailer!. unfold hc4nb2_ke_k1_is in *. subst. cbn [andb].
    destruct (bytes_eqb (sk_key (kp_send K)) (sk_key (kp_send (ks_K s)))); reflexivity. }
  hc4nb2_ke_k1_step FC._t'6 (bytes_eqb (sk_key (kp_recv K)) (sk_key (kp_recv (ks_K s)))) c6 p4 p5 C6 P5.
  { match goal with Hf: typed_false tint _ |- _ => apply hc4nb2_ke_k1_tf in Hf end.
    pose proof OK as (OK1 & OK2 & OK3).
    sep_apply (hc4nb2_ke_k1_key_r Ews k (kp_recv K) OK2 FC4).
    assert_PROP (field_compatible t_kent (DOT HC._rkey0) k) as FCx by entailer!.
    rewrite (hc4nb2_ke_k1_sn_rkey0 Ews k _ LR).
    flatten_sepcon_in_SEP.
    forward_call (Ews, field_address t_kp [StructField I._key; StructField I._receiving] k, sk_key (kp_recv K),
                  Ews, field_address t_kent (DOT HC._rkey0) k, sk_key (kp_recv (ks_K s))).
    { rewrite OK2. entailer!. rewrite !field_address_offset by auto with field_compatible.
      pose proof FC4 as [Pk _]. destruct k; try contradiction. simpl. rewrite !Ptrofs.add_zero. reflexivity. }
    forward.
    sep_apply (modus_ponens_wand (hbytes Ews (sk_key (kp_recv K)) (field_address t_kp [StructField I._key; StructField I._receiving] k))).
    rewrite <- (hc4nb2_ke_k1_sn_rkey0 Ews k _ LR).
    entailer!. unfold hc4nb2_ke_k1_is in *. subst. cbn [andb].
    destruct (bytes_eqb (sk_key (kp_recv K)) (sk_key (kp_recv (ks_K s)))); reflexivity. }
  hc4nb2_ke_k1_step FC._t'8 (Int64.eq (sk_birth (kp_send K)) (sk_birth (kp_send (ks_K s)))) c7 p5 p6 C7 P6.
  { hc4nb2_ke_k1_els C7 P6. }
  hc4nb2_ke_k1_step FC._t'9 (Int64.eq (sk_birth (kp_recv K)) (sk_birth (kp_recv (ks_K s)))) c8 p6 p7 C8 P7.
  { hc4nb2_ke_k1_els C8 P7. }
  entailer!.
Qed.

Lemma hc4nb2_ke_k1_LC {Espec: OracleKind} k K s nx sht tab T VO sh E lk r :
  Forall vobj_ok VO -> itable_wf T -> sfind (t_D T) k = Some (sh, E) -> @field_compatible CS4nb t_kp [] k ->
  (e_peer (ks_E s) = nullval \/ In (e_peer (ks_E s)) (saddrs (t_D T)) \/
   In (e_peer (ks_E s)) (hc4nb2_ke_k1_vobjs_vaddrs VO)) ->
  (e_peer E = nullval \/ In (e_peer E) (saddrs (t_D T)) \/ In (e_peer E) (hc4nb2_ke_k1_vobjs_vaddrs VO)) ->
  is_pointer_or_null (e_peer E) -> is_pointer_or_null (e_peer (ks_E s)) -> kp_ok K ->
  semax hc4nb2_ke_k1_Delta
    (PROPx [] (LOCALx [temp FC._kp k; temp FC._l k] (SEPx (hc4nb2_ke_k1_St sh T k E K s lk r nx sht tab VO))))
    hc4nb2_ke_k1_X16
    (normal_ret_assert (PROPx [] (LOCALx [temp FC._t'17 (Val.of_bool (negb (hc4nb2_ke_k1_m17 T k E K s)));
      temp FC._kp k; temp FC._l k] (SEPx (hc4nb2_ke_k1_St sh T k E K s lk r nx sht tab VO))))).
Proof.
  intros H W F FC4 VQ1 VQ2 PN2 PN1 OK.
  unfold hc4nb2_ke_k1_X16. rewrite <- !seq_assoc.
  eapply semax_seq'; [apply hc4nb2_ke_k1_LB; auto|].
  unfold hc4nb2_ke_k1_St, hc4nb2_ke_k1_s10, hc4nb2_ke_k1_s11, hc4nb2_ke_k1_s12, hc4nb2_ke_k1_s13, hc4nb2_ke_k1_s14, hc4nb2_ke_k1_s15, hc4nb2_ke_k1_s16, hc4nb2_ke_k1_s17, hc4nb2_ke_k1_m17, hc4nb2_ke_k1_Delta. abbreviate_semax.
  remember (hc4nb2_ke_k1_m9 T k E K s) as p7 eqn:P7. change (hc4nb2_ke_k1_is p7 (hc4nb2_ke_k1_m9 T k E K s)) in P7.
  unfold symkey_val.
  hc4nb2_ke_k1_step FC._t'10 (Bool.eqb (sk_valid (kp_send K)) (sk_valid (kp_send (ks_K s)))) c9 p7 p8 C9 P8.
  { hc4nb2_ke_k1_els C9 P8. }
  hc4nb2_ke_k1_step FC._t'11 (Bool.eqb (sk_valid (kp_recv K)) (sk_valid (kp_recv (ks_K s)))) c10 p8 p9 C10 P9.
  { hc4nb2_ke_k1_els C10 P9. }
  hc4nb2_ke_k1_step FC._t'12 (Int64.eq (kp_scounter K) (kp_scounter (ks_K s))) c11 p9 p10 C11 P10.
  { hc4nb2_ke_k1_els C11 P10. }
  hc4nb2_ke_k1_step FC._t'13 (Int64.eq (kp_rcounter K) (kp_rcounter (ks_K s))) c12 p10 p11 C12 P11.
  { hc4nb2_ke_k1_els C12 P11. }
  hc4nb2_ke_k1_step FC._t'14 (Int.eq (kp_rindex K) (kp_rindex (ks_K s))) c13 p11 p12 C13 P12.
  { hc4nb2_ke_k1_els C13 P12. }
  hc4nb2_ke_k1_step FC._t'15 (Bool.eqb (kp_init K) (kp_init (ks_K s))) c14 p12 p13 C14 P13.
  { hc4nb2_ke_k1_els C14 P13. }
  hc4nb2_ke_k1_step FC._t'16 (Int.eq (kp_refs K) (kp_refs (ks_K s))) c15 p13 p14 C15 P14.
  { hc4nb2_ke_k1_els C15 P14. }
  hc4nb2_ke_k1_step FC._t'17 (Int64.eq (kp_id K) (kp_id (ks_K s))) c16 p14 p15 C16 P15.
  { hc4nb2_ke_k1_els C16 P15. }
  entailer!.
Qed.

End K1.
