(* The specifications of the helpers of harness/wg_laws.h, shared by the short laws.

   upto, any_u64, any_bytes and bytes_eq are static functions of wg_laws.h: every short-law harness that uses one
   has its own copy, with the same Clight (the identifiers are $"name", the same in every program).  Their bodies
   are proved once (wl_bodies.v) against the copies of harness/ae_roundtrip.c, under any compspecs (they touch
   byte arrays only), with a context of their callees only (the environment's functions, QuickProof.Env), and
   move into each law's program with asm_lib's asm_body_lift.

   - upto(max): any value from 0 to max.
   - any_u64(): any 64-bit value.
   - any_bytes(n): NULL (a failed malloc) or a new object of n arbitrary bytes, with its malloc token.
   - bytes_eq(a, b, n): 1 when the first n bytes of a and b are equal, 0 otherwise.  The buffers may be longer
     than n and hold anything (even undefined values) beyond their first n bytes (ae_split_blake2s compares the
     first outlen bytes of two 32-byte arrays). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.harness.ae_roundtrip.code.

Local Open Scope Z_scope.

Definition _upto : ident := WgNoise.harness.ae_roundtrip.code._upto.
Definition _any_u64 : ident := WgNoise.harness.ae_roundtrip.code._any_u64.
Definition _any_bytes : ident := WgNoise.harness.ae_roundtrip.code._any_bytes.
Definition _bytes_eq : ident := WgNoise.harness.ae_roundtrip.code._bytes_eq.

Section WgLawsSpecs.
Context {cs: compspecs}.

(* upto(max): any value from 0 to max *)
Definition upto_spec :=
  DECLARE _upto
  WITH max: Z
  PRE [ tulong ]
    PROP (0 <= max <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr max)) SEP ()
  POST [ tulong ] EX v: Z,
    PROP (0 <= v <= max) RETURN (Vlong (Int64.repr v)) SEP ().

(* any_u64(): any 64-bit value *)
Definition any_u64_spec :=
  DECLARE _any_u64
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tulong ] EX v: Z,
    PROP (0 <= v <= Int64.max_unsigned) RETURN (Vlong (Int64.repr v)) SEP ().

(* any_bytes(n): NULL, or a new object of n arbitrary bytes *)
Definition any_bytes_spec :=
  DECLARE _any_bytes
  WITH n: Z, gv: globals
  PRE [ tulong ]
    PROP (0 <= n <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr n)) GLOBALS (gv)
    SEP (mem_mgr gv)
  POST [ tptr tuchar ] EX p: val, EX bs: list byte,
    PROP (Zlength bs = n) RETURN (p)
    SEP (mem_mgr gv;
         if eq_dec p nullval then emp
         else malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) (map Vubyte bs) p).

(* bytes_eq(a, b, n): 1 iff the first n bytes of a and b (xa and xb) are equal *)
Definition bytes_eq_spec :=
  DECLARE _bytes_eq
  WITH sha: share, a: val, ca: list val, xa: list byte, shb: share, b: val, cb: list val, xb: list byte, n: Z
  PRE [ tptr tuchar, tptr tuchar, tulong ]
    PROP (readable_share sha; readable_share shb; 0 <= n <= Int64.max_unsigned;
          n <= Zlength ca; n <= Zlength cb; sublist 0 n ca = map Vubyte xa; sublist 0 n cb = map Vubyte xb)
    PARAMS (a; b; Vlong (Int64.repr n))
    SEP (data_at sha (tarray tuchar (Zlength ca)) ca a; data_at shb (tarray tuchar (Zlength cb)) cb b)
  POST [ tint ]
    PROP () RETURN (Vint (if list_eq_dec Byte.eq_dec xa xb then Int.one else Int.zero))
    SEP (data_at sha (tarray tuchar (Zlength ca)) ca a; data_at shb (tarray tuchar (Zlength cb)) cb b).

(* the context of the four bodies: the environment *)
Definition wl_imports : funspecs := @QuickProof.Env.env_specs cs.

End WgLawsSpecs.
