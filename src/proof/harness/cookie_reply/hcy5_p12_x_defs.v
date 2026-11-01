(* law cookie_reply, phase P12, segment X: the cut of s71 into its two branches
   (target == NULL: hcy5_p12_x_sN; else: hcy5_p12_x_sS).  Both go St -> St (normal_ret_assert). *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p12_defs.
Require WgNoise.harness.x_cookie_reply.code.

Definition hcy5_p12_x_sN :=
  ltac:(let x := eval cbv delta [hcy5_p12_s71] in hcy5_p12_s71 in
        match x with Sifthenelse _ ?a _ => exact a end).
Definition hcy5_p12_x_sS :=
  ltac:(let x := eval cbv delta [hcy5_p12_s71] in hcy5_p12_s71 in
        match x with Sifthenelse _ _ ?b => exact b end).
Definition hcy5_p12_x_cond :=
  ltac:(let x := eval cbv delta [hcy5_p12_s71] in hcy5_p12_s71 in
        match x with Sifthenelse ?c _ _ => exact c end).

Lemma hcy5_p12_x_s71_eq : hcy5_p12_s71 = Sifthenelse hcy5_p12_x_cond hcy5_p12_x_sN hcy5_p12_x_sS.
Proof. reflexivity. Qed.
