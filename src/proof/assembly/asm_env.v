(* The external world as the body proofs use it.

   The theorems are stated in the framework's world QuickProof.Env (HonestEspec).  There,
   nondet_bytes(buf, n) also accepts buf = NULL when n = 0.  The harnesses of this project always
   pass a real buffer (an array or a block from malloc), and the body proofs call nondet_bytes with
   nondet_bytes_spec below, which has no NULL case: its precondition owns the n bytes at buf.
   env_specs lists the externals the programs of this project call, with these specifications.

   nondet_bytes_sub: the framework's specification is a subtype of this one (a buffer owned with
   data_at_ is a pointer, so not NULL, and for a pointer the two specifications agree).  The
   assembly (asm_lib.v) proves each external against the framework's specification and lifts the
   body proofs to it with this subtyping. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.

Section Environment.
Context {CS: compspecs}.

(* nondet_bytes(buf, n): buf must be writable for n bytes; afterwards it holds n arbitrary bytes.  Any
   share and any prior contents.  (QuickProof.Env.nondet_bytes_spec without its case buf = NULL.) *)
Definition nondet_bytes_spec :=
  DECLARE _nondet_bytes
  WITH buf: val, n: Z, sh: share
  PRE  [ tptr tuchar, tulong ]
       PROP (writable_share sh; 0 <= n <= Int64.max_unsigned)
       PARAMS (buf; Vlong (Int64.repr n))
       SEP (data_at_ sh (tarray tuchar n) buf)
  POST [ tvoid ] EX bs: list Z,
       PROP (Zlength bs = n; Forall (fun b => 0 <= b <= Byte.max_unsigned) bs)
       RETURN ()
       SEP (data_at sh (tarray tuchar n) (map (fun b => Vint (Int.repr b)) bs) buf).

(* The externals the programs of this project call. *)
Definition env_specs : funspecs :=
  [ (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
    nondet_u8_spec; nondet_u32_spec; nondet_size_spec; nondet_bytes_spec ].

Lemma nondet_bytes_sub :
  funspec_sub (snd QuickProof.Env.nondet_bytes_spec) (snd nondet_bytes_spec).
Proof.
  do_funspec_sub. destruct w as [[buf n] sh].
  rewrite sepcon_emp.
  assert_PROP (isptr buf) as Hp by (rewrite data_at__isptr; entailer!).
  assert (Hb: buf <> nullval) by (intros E; subst; inv Hp).
  Exists (buf, n, sh) emp. simpl.
  destruct (EqDec_val buf nullval) as [E|_]; [contradiction |].
  apply andp_right.
  - rewrite emp_sepcon, sepcon_emp. apply derives_refl.
  - apply prop_right. intros rho'. rewrite emp_sepcon. apply andp_left2, derives_refl.
Qed.


End Environment.
