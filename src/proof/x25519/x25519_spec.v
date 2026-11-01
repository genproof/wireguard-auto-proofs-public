(* Specifications of the Curve25519 piece: every function of lib/crypto/curve25519.c
   and lib/crypto/curve25519-fiat32.c except the shared inlines memzero_explicit, get_unaligned_le32 (blake2s
   piece) and crypto_memneq (libc piece), against the functional model x25519_model.v.

   Conventions.
   - A field element (fe or fe_loose, a struct { u32 v[10]; }) is specified as the ARRAY of its 10 limbs at the
     struct's address: `data_at sh (tarray tuint 10) (map Vint f) p` (the wrappers pass h->v, which is
     offset_val 0 h).  curve25519_generic converts its struct locals (data_at_ Tsh (Tstruct _fe noattr)) to
     and from arrays / byte arrays through memory_block.
   - Outputs are data_at_ (any prior contents), inputs readable shares, outputs writable shares.
   - fe_mul_impl and its wrappers may be called in place (out = in1 or out = in2: fe_alias3), fe_sqr_impl and
     its wrappers too (out = in1: fe_alias2); fe_invert is only called in place (fe_invert(&z2, &z2)) and is
     specified in place; every other function has distinct buffers.
   - Fiat32 functions are stated at Curve25519Fiat32.CS, curve25519.c's at Curve25519.CS. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Export WgNoise.proof.libc.spec.
Require Export WgNoise.proof.blake2s.spec_shared.
Require Export WgNoise.proof.prims.prim_api.
Require Export WgNoise.proof.x25519.x25519_model.
Require WgNoise.curve25519_fiat32.code WgNoise.curve25519.code.

Module F := WgNoise.curve25519_fiat32.code.
Module C := WgNoise.curve25519.code.

Local Open Scope Z_scope.

Definition t_fe : type := Tstruct F._fe noattr.
Definition t_fel : type := Tstruct F._fe_loose noattr.
Definition t_limbs : type := tarray tuint 10.

(* in-place modes *)
Inductive fe_alias3 := FA_none | FA_out1 | FA_out2.   (* out distinct / out = in1 / out = in2 *)
Inductive fe_alias2 := FS_none | FS_out.              (* out distinct / out = in1 *)

Section Fiat32.
#[local] Existing Instance Curve25519Fiat32.CS.

Definition fe3_ok (m: fe_alias3) (out in1 in2: val) : Prop :=
  match m with FA_none => True | FA_out1 => out = in1 | FA_out2 => out = in2 end.

Definition fe3_pre (m: fe_alias3) (osh sh1 sh2: share) (out in1 in2: val) (f g: list int) : mpred :=
  match m with
  | FA_none => (data_at_ osh t_limbs out * data_at sh1 t_limbs (map Vint f) in1 *
               data_at sh2 t_limbs (map Vint g) in2)%logic
  | FA_out1 => (data_at osh t_limbs (map Vint f) out * data_at sh2 t_limbs (map Vint g) in2)%logic
  | FA_out2 => (data_at sh1 t_limbs (map Vint f) in1 * data_at osh t_limbs (map Vint g) out)%logic
  end.

Definition fe3_post (m: fe_alias3) (osh sh1 sh2: share) (out in1 in2: val) (f g h: list int) : mpred :=
  match m with
  | FA_none => (data_at osh t_limbs (map Vint h) out * data_at sh1 t_limbs (map Vint f) in1 *
               data_at sh2 t_limbs (map Vint g) in2)%logic
  | FA_out1 => (data_at osh t_limbs (map Vint h) out * data_at sh2 t_limbs (map Vint g) in2)%logic
  | FA_out2 => (data_at sh1 t_limbs (map Vint f) in1 * data_at osh t_limbs (map Vint h) out)%logic
  end.

Definition fe2_ok (m: fe_alias2) (out in1: val) : Prop :=
  match m with FS_none => True | FS_out => out = in1 end.

Definition fe2_pre (m: fe_alias2) (osh sh1: share) (out in1: val) (f: list int) : mpred :=
  match m with
  | FS_none => (data_at_ osh t_limbs out * data_at sh1 t_limbs (map Vint f) in1)%logic
  | FS_out => (data_at osh t_limbs (map Vint f) out)%logic
  end.

Definition fe2_post (m: fe_alias2) (osh sh1: share) (out in1: val) (f h: list int) : mpred :=
  match m with
  | FS_none => (data_at osh t_limbs (map Vint h) out * data_at sh1 t_limbs (map Vint f) in1)%logic
  | FS_out => (data_at osh t_limbs (map Vint h) out)%logic
  end.

(* ---------------------------------------------------------------------- *)
(* bytes <-> limbs                                                         *)
(* ---------------------------------------------------------------------- *)

Definition fe_frombytes_impl_spec :=
  DECLARE F._fe_frombytes_impl
  WITH osh: share, h: val, ssh: share, s: val, bs: list byte
  PRE [ tptr tuint, tptr tuchar ]
    PROP (writable_share osh; readable_share ssh; Zlength bs = 32)
    PARAMS (h; s)
    SEP (data_at_ osh t_limbs h; data_at ssh (tarray tuchar 32) (map Vubyte bs) s)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at osh t_limbs (map Vint (fe_frombytes_m bs)) h;
         data_at ssh (tarray tuchar 32) (map Vubyte bs) s).

Definition fe_frombytes_spec :=
  DECLARE F._fe_frombytes
  WITH osh: share, h: val, ssh: share, s: val, bs: list byte
  PRE [ tptr t_fe, tptr tuchar ]
    PROP (writable_share osh; readable_share ssh; Zlength bs = 32)
    PARAMS (h; s)
    SEP (data_at_ osh t_limbs h; data_at ssh (tarray tuchar 32) (map Vubyte bs) s)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at osh t_limbs (map Vint (fe_frombytes_m bs)) h;
         data_at ssh (tarray tuchar 32) (map Vubyte bs) s).

(* the carry / borrow helpers: *low := the low bits, return the carry (0 or 1) *)
Definition carry_spec (id: ident) (m: int -> int -> int -> int * int) :=
  DECLARE id
  WITH c: int, a: int, b: int, sh: share, low: val
  PRE [ tuchar, tuint, tuint, tptr tuint ]
    PROP (writable_share sh; Int.unsigned c <= Byte.max_unsigned)
    PARAMS (Vint c; Vint a; Vint b; low)
    SEP (data_at_ sh tuint low)
  POST [ tuchar ]
    PROP () RETURN (Vint (snd (m c a b)))
    SEP (data_at sh tuint (Vint (fst (m c a b))) low).

Definition addcarryx_u25_spec := carry_spec F._addcarryx_u25 (addcarryx_m 25).
Definition addcarryx_u26_spec := carry_spec F._addcarryx_u26 (addcarryx_m 26).
Definition subborrow_u25_spec := carry_spec F._subborrow_u25 (subborrow_m 25).
Definition subborrow_u26_spec := carry_spec F._subborrow_u26 (subborrow_m 26).

Definition cmovznz32_spec :=
  DECLARE F._cmovznz32
  WITH t: int, z: int, nz: int
  PRE [ tuint, tuint, tuint ]
    PROP () PARAMS (Vint t; Vint z; Vint nz) SEP ()
  POST [ tuint ]
    PROP () RETURN (Vint (cmovznz32_m t z nz)) SEP ().

Definition fe_freeze_spec :=
  DECLARE F._fe_freeze
  WITH osh: share, out: val, ish: share, inp: val, f: list int
  PRE [ tptr tuint, tptr tuint ]
    PROP (writable_share osh; readable_share ish; Zlength f = 10)
    PARAMS (out; inp)
    SEP (data_at_ osh t_limbs out; data_at ish t_limbs (map Vint f) inp)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at osh t_limbs (map Vint (fe_freeze_m f)) out; data_at ish t_limbs (map Vint f) inp).

Definition fe_tobytes_spec :=
  DECLARE F._fe_tobytes
  WITH osh: share, s: val, fsh: share, fp: val, f: list int
  PRE [ tptr tuchar, tptr t_fe ]
    PROP (writable_share osh; readable_share fsh; Zlength f = 10)
    PARAMS (s; fp)
    SEP (data_at_ osh (tarray tuchar 32) s; data_at fsh t_limbs (map Vint f) fp)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at osh (tarray tuchar 32) (map Vubyte (fe_tobytes_m f)) s;
         data_at fsh t_limbs (map Vint f) fp).

(* ---------------------------------------------------------------------- *)
(* copies and constants                                                    *)
(* ---------------------------------------------------------------------- *)

Definition fe_copy_spec_of (id: ident) (th: type) :=
  DECLARE id
  WITH osh: share, h: val, fsh: share, fp: val, f: list int
  PRE [ tptr th, tptr t_fe ]
    PROP (writable_share osh; readable_share fsh; Zlength f = 10)
    PARAMS (h; fp)
    SEP (data_at_ osh t_limbs h; data_at fsh t_limbs (map Vint f) fp)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at osh t_limbs (map Vint f) h; data_at fsh t_limbs (map Vint f) fp).

Definition fe_copy_spec := fe_copy_spec_of F._fe_copy t_fe.
Definition fe_copy_lt_spec := fe_copy_spec_of F._fe_copy_lt t_fel.

Definition fe_const_spec (id: ident) (c: list int) :=
  DECLARE id
  WITH osh: share, h: val
  PRE [ tptr t_fe ]
    PROP (writable_share osh) PARAMS (h) SEP (data_at_ osh t_limbs h)
  POST [ tvoid ]
    PROP () RETURN () SEP (data_at osh t_limbs (map Vint c) h).

Definition fe_0_spec := fe_const_spec F._fe_0 fe0_m.
Definition fe_1_spec := fe_const_spec F._fe_1 fe1_m.

(* ---------------------------------------------------------------------- *)
(* limb arithmetic                                                         *)
(* ---------------------------------------------------------------------- *)

(* out = op(in1, in2), three distinct buffers *)
Definition fe_binop_spec (id: ident) (to t1 t2: type) (op: list int -> list int -> list int) :=
  DECLARE id
  WITH osh: share, out: val, sh1: share, in1: val, f: list int, sh2: share, in2: val, g: list int
  PRE [ tptr to, tptr t1, tptr t2 ]
    PROP (writable_share osh; readable_share sh1; readable_share sh2; Zlength f = 10; Zlength g = 10)
    PARAMS (out; in1; in2)
    SEP (data_at_ osh t_limbs out; data_at sh1 t_limbs (map Vint f) in1; data_at sh2 t_limbs (map Vint g) in2)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at osh t_limbs (map Vint (op f g)) out; data_at sh1 t_limbs (map Vint f) in1;
         data_at sh2 t_limbs (map Vint g) in2).

Definition fe_add_impl_spec := fe_binop_spec F._fe_add_impl tuint tuint tuint fe_add_m.
Definition fe_add_spec := fe_binop_spec F._fe_add t_fel t_fe t_fe fe_add_m.
Definition fe_sub_impl_spec := fe_binop_spec F._fe_sub_impl tuint tuint tuint fe_sub_m.
Definition fe_sub_spec := fe_binop_spec F._fe_sub t_fel t_fe t_fe fe_sub_m.

(* out = f * g, possibly in place *)
Definition fe_mul_spec_of (id: ident) (to t1 t2: type) :=
  DECLARE id
  WITH m: fe_alias3, osh: share, out: val, sh1: share, in1: val, f: list int, sh2: share, in2: val,
       g: list int
  PRE [ tptr to, tptr t1, tptr t2 ]
    PROP (writable_share osh; readable_share sh1; readable_share sh2; Zlength f = 10; Zlength g = 10;
          fe3_ok m out in1 in2)
    PARAMS (out; in1; in2)
    SEP (fe3_pre m osh sh1 sh2 out in1 in2 f g)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (fe3_post m osh sh1 sh2 out in1 in2 f g (fe_mul_m f g)).

Definition fe_mul_impl_spec := fe_mul_spec_of F._fe_mul_impl tuint tuint tuint.
Definition fe_mul_ttt_spec := fe_mul_spec_of F._fe_mul_ttt t_fe t_fe t_fe.
Definition fe_mul_tlt_spec := fe_mul_spec_of F._fe_mul_tlt t_fe t_fel t_fe.
Definition fe_mul_tll_spec := fe_mul_spec_of F._fe_mul_tll t_fe t_fel t_fel.

(* out = f^2, possibly in place *)
Definition fe_sqr_spec_of (id: ident) (to t1: type) :=
  DECLARE id
  WITH m: fe_alias2, osh: share, out: val, sh1: share, in1: val, f: list int
  PRE [ tptr to, tptr t1 ]
    PROP (writable_share osh; readable_share sh1; Zlength f = 10; fe2_ok m out in1)
    PARAMS (out; in1)
    SEP (fe2_pre m osh sh1 out in1 f)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (fe2_post m osh sh1 out in1 f (fe_sqr_m f)).

Definition fe_sqr_impl_spec := fe_sqr_spec_of F._fe_sqr_impl tuint tuint.
Definition fe_sq_tl_spec := fe_sqr_spec_of F._fe_sq_tl t_fe t_fel.
Definition fe_sq_tt_spec := fe_sqr_spec_of F._fe_sq_tt t_fe t_fe.

(* out = op(in1), distinct buffers *)
Definition fe_unop_spec (id: ident) (to t1: type) (op: list int -> list int) :=
  DECLARE id
  WITH osh: share, out: val, sh1: share, in1: val, f: list int
  PRE [ tptr to, tptr t1 ]
    PROP (writable_share osh; readable_share sh1; Zlength f = 10)
    PARAMS (out; in1)
    SEP (data_at_ osh t_limbs out; data_at sh1 t_limbs (map Vint f) in1)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at osh t_limbs (map Vint (op f)) out; data_at sh1 t_limbs (map Vint f) in1).

Definition fe_mul_121666_impl_spec := fe_unop_spec F._fe_mul_121666_impl tuint tuint fe_mul121666_m.
Definition fe_mul121666_spec := fe_unop_spec F._fe_mul121666 t_fe t_fel fe_mul121666_m.
Definition fe_loose_invert_spec := fe_unop_spec F._fe_loose_invert t_fe t_fel fe_loose_invert_m.

(* fe_invert(p, p), in place *)
Definition fe_invert_spec :=
  DECLARE F._fe_invert
  WITH sh: share, p: val, f: list int
  PRE [ tptr t_fe, tptr t_fe ]
    PROP (writable_share sh; Zlength f = 10)
    PARAMS (p; p)
    SEP (data_at sh t_limbs (map Vint f) p)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh t_limbs (map Vint (fe_invert_m f)) p).

Definition fe_cswap_spec :=
  DECLARE F._fe_cswap
  WITH sh1: share, fp: val, f: list int, sh2: share, gp: val, g: list int, b: int
  PRE [ tptr t_fe, tptr t_fe, tuint ]
    PROP (writable_share sh1; writable_share sh2; Zlength f = 10; Zlength g = 10)
    PARAMS (fp; gp; Vint b)
    SEP (data_at sh1 t_limbs (map Vint f) fp; data_at sh2 t_limbs (map Vint g) gp)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh1 t_limbs (map Vint (fst (fe_cswap_m f g b))) fp;
         data_at sh2 t_limbs (map Vint (snd (fe_cswap_m f g b))) gp).

End Fiat32.

(* ---------------------------------------------------------------------- *)
(* curve25519.c (unit Curve25519)                                          *)
(* ---------------------------------------------------------------------- *)

Section Curve.
#[local] Existing Instance Curve25519.CS.

(* curve25519_arch: the same contract as curve25519_generic *)
Definition curve25519_arch_spec :=
  DECLARE C._curve25519_arch
  WITH osh: share, out: val, ssh: share, s: val, sc: list byte, psh: share, p: val, pt: list byte
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share osh; readable_share ssh; readable_share psh; Zlength sc = 32; Zlength pt = 32)
    PARAMS (out; s; p)
    SEP (data_at_ osh (tarray tuchar 32) out;
         data_at ssh (tarray tuchar 32) (map Vubyte sc) s; data_at psh (tarray tuchar 32) (map Vubyte pt) p)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at osh (tarray tuchar 32) (map Vubyte (x25519_m sc pt)) out;
         data_at ssh (tarray tuchar 32) (map Vubyte sc) s; data_at psh (tarray tuchar 32) (map Vubyte pt) p).

(* curve25519_base_arch(pub, secret): pub = x25519 secret 9 *)
Definition curve25519_base_arch_spec :=
  DECLARE C._curve25519_base_arch
  WITH osh: share, out: val, ssh: share, s: val, sc: list byte, gv: globals
  PRE [ tptr tuchar, tptr tuchar ]
    PROP (writable_share osh; readable_share ssh; Zlength sc = 32)
    PARAMS (out; s) GLOBALS (gv)
    SEP (data_at_ osh (tarray tuchar 32) out; data_at ssh (tarray tuchar 32) (map Vubyte sc) s;
         curve25519_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at osh (tarray tuchar 32) (map Vubyte (x25519_m sc basepoint9)) out;
         data_at ssh (tarray tuchar 32) (map Vubyte sc) s; curve25519_globals gv).

End Curve.

(* ---------------------------------------------------------------------- *)
(* the piece's specification list and the body-proof contexts              *)
(* ---------------------------------------------------------------------- *)

(* the same list as x25519_imports of x25519_piece.v *)
Definition x25_Imports (cs: compspecs) : funspecs :=
  [@memcpy_spec cs; @memset_spec cs; @memzero_explicit_spec cs; @get_unaligned_le32_spec cs;
   @crypto_memneq_spec cs].

Definition x25_G : funspecs :=
  [ (* curve25519-fiat32.c *)
    @curve25519_clamp_secret_spec Curve25519Fiat32.CS;
    fe_frombytes_impl_spec; fe_frombytes_spec;
    addcarryx_u25_spec; addcarryx_u26_spec; subborrow_u25_spec; subborrow_u26_spec; cmovznz32_spec;
    fe_freeze_spec; fe_tobytes_spec;
    fe_copy_spec; fe_copy_lt_spec; fe_0_spec; fe_1_spec;
    fe_add_impl_spec; fe_add_spec; fe_sub_impl_spec; fe_sub_spec;
    fe_mul_impl_spec; fe_mul_ttt_spec; fe_mul_tlt_spec; fe_mul_tll_spec;
    fe_sqr_impl_spec; fe_sq_tl_spec; fe_sq_tt_spec;
    fe_loose_invert_spec; fe_invert_spec; fe_cswap_spec;
    fe_mul_121666_impl_spec; fe_mul121666_spec;
    @curve25519_generic_spec_of Curve25519Fiat32.CS x25519_m;
    (* curve25519.c *)
    curve25519_arch_spec; curve25519_base_arch_spec;
    @curve25519_spec_of Curve25519.CS x25519_m;
    @curve25519_generate_public_spec_of Curve25519.CS x25519_m ].

(* the context of a body proof in the unit curve25519_fiat32 *)
Definition x25_Gprog : funspecs := x25_Imports Curve25519Fiat32.CS ++ x25_G.

(* the context of a body proof in the unit curve25519 *)
Definition x25_Gprog_c : funspecs := x25_Imports Curve25519.CS ++ x25_G.

(* the varspecs of the two units *)
Definition x25_V : varspecs := QPvarspecs Curve25519Fiat32.qp.
Definition x25_V_c : varspecs := QPvarspecs Curve25519.qp.
