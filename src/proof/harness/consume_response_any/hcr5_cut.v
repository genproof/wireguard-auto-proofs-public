(* law consume_response_any: the cut of main's body
   into phases. *)
Require Import VST.floyd.proofauto.
Require WgNoise.harness.x_consume_response_any.code.

Module HR5 := WgNoise.harness.x_consume_response_any.code.

Fixpoint hcr5_seqs (l: list statement) (rest: statement) : statement :=
  match l with [] => rest | a :: l' => Ssequence a (hcr5_seqs l' rest) end.

Fixpoint hcr5_seql (l: list statement) : statement :=
  match l with [] => Sskip | [a] => a | a :: l' => Ssequence a (hcr5_seql l') end.

Fixpoint hcr5_flat (s: statement) : list statement :=
  match s with Ssequence a b => a :: hcr5_flat b | _ => [s] end.

Definition hcr5_stmts : list statement :=
  ltac:(let x := eval cbv beta iota delta [hcr5_flat HR5.f_main fn_body] in
        (match fn_body HR5.f_main with Ssequence s _ => hcr5_flat s | s => [s] end) in exact x).

(* the statement `if (msg != NULL) { ... }` and its then-branch *)
Definition hcr5_P14 := ltac:(let x := eval cbv beta iota delta [hcr5_stmts nth] in (nth 14 hcr5_stmts Sskip) in exact x).
Definition hcr5_tstmts : list statement :=
  ltac:(let x := eval cbv beta iota delta [hcr5_P14 hcr5_flat] in
        (match hcr5_P14 with Sifthenelse _ a _ => hcr5_flat a | _ => [] end) in exact x).
