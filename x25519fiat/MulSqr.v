(* fe_mul_m, fe_sqr_m, fe_mul121666_m: no wrap-around for loose inputs, tight outputs, and the value is the
   product modulo p.  VST-side file: no fiat-crypto here.

   Method: the model's definitions are convertible to eD of expression trees (Check.v): the 19 column sums
   (Cols.v, generated) and the common carry chain carry_tree (written here, the C's lines x59..x120).  The
   interval checker (vm_compute) shows that nothing wraps and that the outputs are tight; then the value of
   the trees over Z (eZ) is related to the product by two ring identities (the carry chain telescopes, the
   column sums are the schoolbook product with 2^255 = 19 + p). *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.x25519.x25519_model.
Require Import X25519.Check X25519.Cols X25519.Limbs.

Local Open Scope Z_scope.

Definition fold3 (a b: expr T64) : expr T64 := EAdd64 (EAdd64 (EAdd64 a (EShl64 b 4)) (EShl64 b 1)) b.

Definition carry_tree (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 : expr T64)
    : list (expr T32) :=
  let x61 := fold3 c8 c18 in
  let x64 := fold3 c7 c17 in
  let x67 := fold3 c6 c16 in
  let x70 := fold3 c5 c15 in
  let x73 := fold3 c4 c14 in
  let x76 := fold3 c3 c13 in
  let x79 := fold3 c2 c12 in
  let x82 := fold3 c1 c11 in
  let x85 := fold3 c0 c10 in
  let x86 := EShru64 x85 26 in let x87 := EMaskLo x85 26 in
  let x88 := EAdd64 x86 x82 in let x89 := EShru64 x88 25 in let x90 := EMaskLo x88 25 in
  let x91 := EAdd64 x89 x79 in let x92 := EShru64 x91 26 in let x93 := EMaskLo x91 26 in
  let x94 := EAdd64 x92 x76 in let x95 := EShru64 x94 25 in let x96 := EMaskLo x94 25 in
  let x97 := EAdd64 x95 x73 in let x98 := EShru64 x97 26 in let x99 := EMaskLo x97 26 in
  let x100 := EAdd64 x98 x70 in let x101 := EShru64 x100 25 in let x102 := EMaskLo x100 25 in
  let x103 := EAdd64 x101 x67 in let x104 := EShru64 x103 26 in let x105 := EMaskLo x103 26 in
  let x106 := EAdd64 x104 x64 in let x107 := EShru64 x106 25 in let x108 := EMaskLo x106 25 in
  let x109 := EAdd64 x107 x61 in let x110 := EShru64 x109 26 in let x111 := EMaskLo x109 26 in
  let x112 := EAdd64 x110 c9 in let x113 := EShru64 x112 25 in let x114 := EMaskLo x112 25 in
  let x115 := EAdd64 (EU64 x87) (EMul64 (EC64 19) x113) in
  let x116 := ELo (EShru64 x115 26) in
  let x117 := EMaskLo x115 26 in
  let x118 := EAdd32 x116 x90 in
  let x119 := EShru32 x118 25 in
  let x120 := EMask32 x118 25 in
  [x117; x120; EAdd32 x119 x93; x96; x99; x102; x105; x108; x111; x114].

Definition mul_trees := carry_tree mul_c0 mul_c1 mul_c2 mul_c3 mul_c4 mul_c5 mul_c6 mul_c7 mul_c8 mul_c9
  mul_c10 mul_c11 mul_c12 mul_c13 mul_c14 mul_c15 mul_c16 mul_c17 mul_c18.
Definition sqr_trees := carry_tree sqr_c0 sqr_c1 sqr_c2 sqr_c3 sqr_c4 sqr_c5 sqr_c6 sqr_c7 sqr_c8 sqr_c9
  sqr_c10 sqr_c11 sqr_c12 sqr_c13 sqr_c14 sqr_c15 sqr_c16 sqr_c17 sqr_c18.

(* the model IS the trees (conversion) *)
Lemma fe_mul_m_tree f g : fe_mul_m f g = map (eD f g) mul_trees.
Proof. reflexivity. Qed.

Lemma fe_sqr_m_tree f : fe_sqr_m f = map (eD f f) sqr_trees.
Proof. reflexivity. Qed.

Definition c121666 : list int := map Int.repr [121666; 0; 0; 0; 0; 0; 0; 0; 0; 0].

Lemma fe_mul121666_m_mul f : fe_mul121666_m f = fe_mul_m f c121666.
Proof. reflexivity. Qed.

(* the interval checker *)
Lemma mul_check : check_out loose loose mul_trees tight = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sqr_check : check_out loose loose sqr_trees tight = true.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* the carry chain telescopes                                          *)
(* ------------------------------------------------------------------ *)

Definition carry_q (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 : Z) : Z :=
  let y := fun a b => a + b * 2 ^ 4 + b * 2 ^ 1 + b in
  let s0 := y a0 a10 in
  let s1 := s0 / 2 ^ 26 + y a1 a11 in
  let s2 := s1 / 2 ^ 25 + y a2 a12 in
  let s3 := s2 / 2 ^ 26 + y a3 a13 in
  let s4 := s3 / 2 ^ 25 + y a4 a14 in
  let s5 := s4 / 2 ^ 26 + y a5 a15 in
  let s6 := s5 / 2 ^ 25 + y a6 a16 in
  let s7 := s6 / 2 ^ 26 + y a7 a17 in
  let s8 := s7 / 2 ^ 25 + y a8 a18 in
  let s9 := s8 / 2 ^ 26 + a9 in
  s9 / 2 ^ 25.

Lemma carry_alg f g c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 :
  exists q,
  fevalZ (map (eZ f g) (carry_tree c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18)) =
    (eZ f g c0 + 19 * eZ f g c10) + 2^26 * (eZ f g c1 + 19 * eZ f g c11)
    + 2^51 * (eZ f g c2 + 19 * eZ f g c12) + 2^77 * (eZ f g c3 + 19 * eZ f g c13)
    + 2^102 * (eZ f g c4 + 19 * eZ f g c14) + 2^128 * (eZ f g c5 + 19 * eZ f g c15)
    + 2^153 * (eZ f g c6 + 19 * eZ f g c16) + 2^179 * (eZ f g c7 + 19 * eZ f g c17)
    + 2^204 * (eZ f g c8 + 19 * eZ f g c18) + 2^230 * eZ f g c9 - P25519 * q.
Proof.
  cbn [carry_tree fold3 map eZ fevalZ].
  generalize (eZ f g c0) (eZ f g c1) (eZ f g c2) (eZ f g c3) (eZ f g c4) (eZ f g c5) (eZ f g c6)
    (eZ f g c7) (eZ f g c8) (eZ f g c9) (eZ f g c10) (eZ f g c11) (eZ f g c12) (eZ f g c13) (eZ f g c14)
    (eZ f g c15) (eZ f g c16) (eZ f g c17) (eZ f g c18).
  intros a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18.
  exists (carry_q a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18).
  unfold carry_q. cbv beta zeta.
  rewrite !Zmod_eq_full by (apply Z.pow_nonzero; lia).
  (* name the quotients, innermost first, so that ring sees small atoms *)
  repeat match goal with |- context [?X / 2 ^ ?k] =>
    lazymatch X with context [_ / _] => fail | _ => idtac end;
    let q := fresh "q" in remember (X / 2 ^ k) as q
  end.
  unfold P25519. ring.
Qed.

(* ------------------------------------------------------------------ *)
(* from the checker to bounds and values                               *)
(* ------------------------------------------------------------------ *)

Lemma trees_sound f g bf bg es T :
  (forall i, 0 <= i < 10 -> Int.unsigned (Znth i f) <= Znth i bf) ->
  (forall i, 0 <= i < 10 -> Int.unsigned (Znth i g) <= Znth i bg) ->
  check_out bf bg es T = true ->
  bounded T (map (eD f g) es) /\ map Int.unsigned (map (eD f g) es) = map (eZ f g) es.
Proof.
  intros Hf Hg C. pose proof (check_out_sound f g bf bg Hf Hg es T C) as S. clear C.
  induction S as [|e t es ts [B E] S [IHB IHE]]; cbn [map].
  - split; [constructor | reflexivity].
  - split.
    + constructor; [lia | exact IHB].
    + rewrite E, IHE. reflexivity.
Qed.

Lemma mod_P_shift a b k : a = b + P25519 * k -> a mod P25519 = b mod P25519.
Proof. intros ->. rewrite (Z.mul_comm P25519 k), Z_mod_plus_full. reflexivity. Qed.

Lemma loose_Znth h : bounded loose h -> forall i, 0 <= i < 10 -> Int.unsigned (Znth i h) <= Znth i loose.
Proof. intros H i Hi. apply (bounded_Znth _ _ H). exact Hi. Qed.

Lemma fe_mul_ok f g : bounded loose f -> bounded loose g ->
  bounded tight (fe_mul_m f g) /\ feval (fe_mul_m f g) mod P25519 = (feval f * feval g) mod P25519.
Proof.
  intros Hf Hg.
  destruct (trees_sound f g loose loose mul_trees tight (loose_Znth f Hf) (loose_Znth g Hg) mul_check)
    as [B E].
  rewrite fe_mul_m_tree. split; [exact B|].
  unfold feval at 1. rewrite E.
  destruct (carry_alg f g mul_c0 mul_c1 mul_c2 mul_c3 mul_c4 mul_c5 mul_c6 mul_c7 mul_c8 mul_c9
              mul_c10 mul_c11 mul_c12 mul_c13 mul_c14 mul_c15 mul_c16 mul_c17 mul_c18) as [q Hq].
  unfold mul_trees. rewrite Hq. clear B E Hq.
  apply mod_P_shift with
    (k := - (eZ f g mul_c10 + 2^26 * eZ f g mul_c11 + 2^51 * eZ f g mul_c12 + 2^77 * eZ f g mul_c13
            + 2^102 * eZ f g mul_c14 + 2^128 * eZ f g mul_c15 + 2^153 * eZ f g mul_c16
            + 2^179 * eZ f g mul_c17 + 2^204 * eZ f g mul_c18) - q).
  destruct10 f. destruct10 g.
  cbn [eZ mul_c0 mul_c1 mul_c2 mul_c3 mul_c4 mul_c5 mul_c6 mul_c7 mul_c8 mul_c9
       mul_c10 mul_c11 mul_c12 mul_c13 mul_c14 mul_c15 mul_c16 mul_c17 mul_c18].
  znth10.
  unfold feval, P25519. cbn [map fevalZ]. ring.
Qed.

Lemma fe_sqr_ok f : bounded loose f ->
  bounded tight (fe_sqr_m f) /\ feval (fe_sqr_m f) mod P25519 = (feval f * feval f) mod P25519.
Proof.
  intros Hf.
  destruct (trees_sound f f loose loose sqr_trees tight (loose_Znth f Hf) (loose_Znth f Hf) sqr_check)
    as [B E].
  rewrite fe_sqr_m_tree. split; [exact B|].
  unfold feval at 1. rewrite E.
  destruct (carry_alg f f sqr_c0 sqr_c1 sqr_c2 sqr_c3 sqr_c4 sqr_c5 sqr_c6 sqr_c7 sqr_c8 sqr_c9
              sqr_c10 sqr_c11 sqr_c12 sqr_c13 sqr_c14 sqr_c15 sqr_c16 sqr_c17 sqr_c18) as [q Hq].
  unfold sqr_trees. rewrite Hq. clear B E Hq.
  apply mod_P_shift with
    (k := - (eZ f f sqr_c10 + 2^26 * eZ f f sqr_c11 + 2^51 * eZ f f sqr_c12 + 2^77 * eZ f f sqr_c13
            + 2^102 * eZ f f sqr_c14 + 2^128 * eZ f f sqr_c15 + 2^153 * eZ f f sqr_c16
            + 2^179 * eZ f f sqr_c17 + 2^204 * eZ f f sqr_c18) - q).
  destruct10 f.
  cbn [eZ sqr_c0 sqr_c1 sqr_c2 sqr_c3 sqr_c4 sqr_c5 sqr_c6 sqr_c7 sqr_c8 sqr_c9
       sqr_c10 sqr_c11 sqr_c12 sqr_c13 sqr_c14 sqr_c15 sqr_c16 sqr_c17 sqr_c18].
  znth10.
  unfold feval, P25519. cbn [map fevalZ]. ring.
Qed.

Lemma c121666_loose : bounded loose c121666.
Proof. unfold bounded, loose, c121666. simpl map. repeat constructor; rewrite Int.unsigned_repr by rep_lia; lia. Qed.

Lemma fe_mul121666_ok f : bounded loose f ->
  bounded tight (fe_mul121666_m f) /\
  feval (fe_mul121666_m f) mod P25519 = (feval f * 121666) mod P25519.
Proof.
  intros Hf. rewrite fe_mul121666_m_mul. apply (fe_mul_ok f c121666 Hf c121666_loose).
Qed.
