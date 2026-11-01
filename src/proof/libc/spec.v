(* Specifications of quickproof/libc/libc.c (the unit Libc of src/units.v).

   - Byte buffers are `list byte`, stored as `map Vubyte`.
   - The specifications are polymorphic in the compspecs: a caller instantiates them with its own
     unit's compspecs (the types involved are byte arrays, the same in every composite env).
   - memmove has no specification (no unit calls it): it gets a vacuous one in the assembly. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.libc.code.

Definition _memcpy : ident := WgNoise.libc.code._memcpy.
Definition _memset : ident := WgNoise.libc.code._memset.
Definition _memcmp : ident := WgNoise.libc.code._memcmp.
Definition _calloc : ident := WgNoise.libc.code._calloc.

(* memcmp's result: (int)a[i] - (int)b[i] at the first difference, 0 if none. *)
Fixpoint memcmp_Z (a b: list byte) : Z :=
  match a, b with
  | x :: a', y :: b' => if Byte.eq_dec x y then memcmp_Z a' b' else Byte.unsigned x - Byte.unsigned y
  | _, _ => 0
  end.

Section Specs.
Context {cs: compspecs}.

(* memcpy(dst, src, n): dst and src disjoint (separate SEP conjuncts), src holds n defined bytes. *)
Definition memcpy_spec :=
  DECLARE _memcpy
  WITH dsh: share, ssh: share, dst: val, src: val, n: Z, bs: list byte
  PRE [ tptr tvoid, tptr tvoid, tulong ]
    PROP (writable_share dsh; readable_share ssh; Zlength bs = n; n <= Int64.max_unsigned)
    PARAMS (dst; src; Vlong (Int64.repr n))
    SEP (data_at_ dsh (tarray tuchar n) dst; data_at ssh (tarray tuchar n) (map Vubyte bs) src)
  POST [ tptr tvoid ]
    PROP () RETURN (dst)
    SEP (data_at dsh (tarray tuchar n) (map Vubyte bs) dst; data_at ssh (tarray tuchar n) (map Vubyte bs) src).

(* memset(s, c, n): n bytes (unsigned char)c. *)
Definition memset_spec :=
  DECLARE _memset
  WITH sh: share, p: val, c: Z, n: Z
  PRE [ tptr tvoid, tint, tulong ]
    PROP (writable_share sh; Int.min_signed <= c <= Int.max_signed; 0 <= n <= Int64.max_unsigned)
    PARAMS (p; Vint (Int.repr c); Vlong (Int64.repr n))
    SEP (data_at_ sh (tarray tuchar n) p)
  POST [ tptr tvoid ]
    PROP () RETURN (p)
    SEP (data_at sh (tarray tuchar n) (Zrepeat (Vubyte (Byte.repr c)) n) p).

(* memcmp(s1, s2, n) *)
Definition memcmp_spec :=
  DECLARE _memcmp
  WITH sh1: share, sh2: share, p1: val, p2: val, n: Z, a: list byte, b: list byte
  PRE [ tptr tvoid, tptr tvoid, tulong ]
    PROP (readable_share sh1; readable_share sh2; Zlength a = n; Zlength b = n; n <= Int64.max_unsigned)
    PARAMS (p1; p2; Vlong (Int64.repr n))
    SEP (data_at sh1 (tarray tuchar n) (map Vubyte a) p1; data_at sh2 (tarray tuchar n) (map Vubyte b) p2)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (memcmp_Z a b)))
    SEP (data_at sh1 (tarray tuchar n) (map Vubyte a) p1; data_at sh2 (tarray tuchar n) (map Vubyte b) p2).

(* calloc(nmemb, size): NULL, or nmemb*size zero bytes owned with a malloc_token of the byte array
   (free it with free_spec' at t := tarray tuchar (nmemb * size)). *)
Definition calloc_spec :=
  DECLARE _calloc
  WITH nmemb: Z, size: Z, gv: globals
  PRE [ tulong, tulong ]
    PROP (0 <= nmemb <= Int64.max_unsigned; 0 <= size <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr nmemb); Vlong (Int64.repr size)) GLOBALS (gv)
    SEP (mem_mgr gv)
  POST [ tptr tvoid ] EX p: val,
    PROP (p = nullval \/ nmemb * size <= Int64.max_unsigned)
    RETURN (p)
    SEP (mem_mgr gv;
         if eq_dec p nullval then emp
         else (malloc_token Ews (tarray tuchar (nmemb * size)) p *
               data_at Ews (tarray tuchar (nmemb * size)) (Zrepeat (Vubyte Byte.zero) (nmemb * size)) p)).

End Specs.
