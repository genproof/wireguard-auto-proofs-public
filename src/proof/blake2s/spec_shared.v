(* Specifications of small header functions compiled into SEVERAL units (identical Clight in each):
   - get_unaligned_le32 (blake2s, chacha20poly1305, curve25519_fiat32, poly1305, poly1305_donna32);
   - memzero_explicit (blake2s, chacha20poly1305, chacha_block, curve25519_fiat32, noise).
   One specification per function for the whole project: every unit uses these.
   Polymorphic in the compspecs (byte arrays only).  Owner: law prim_blake2s. *)
Require Import VST.floyd.proofauto.
Require WgNoise.blake2s.code.

Definition _get_unaligned_le32 : ident := WgNoise.blake2s.code._get_unaligned_le32.
Definition _memzero_explicit : ident := WgNoise.blake2s.code._memzero_explicit.

(* (u32)b0 | (u32)b1 << 8 | (u32)b2 << 16 | (u32)b3 << 24, as get_unaligned_le32 computes it *)
Definition le32_of (b0 b1 b2 b3: byte) : int :=
  Int.or (Int.or (Int.or (Int.repr (Byte.unsigned b0))
                         (Int.shl (Int.repr (Byte.unsigned b1)) (Int.repr 8)))
                 (Int.shl (Int.repr (Byte.unsigned b2)) (Int.repr 16)))
         (Int.shl (Int.repr (Byte.unsigned b3)) (Int.repr 24)).

(* the little-endian word at byte offset i of bs *)
Definition le32_at (bs: list byte) (i: Z) : int :=
  le32_of (Znth i bs) (Znth (i + 1) bs) (Znth (i + 2) bs) (Znth (i + 3) bs).

Section Specs.
Context {cs: compspecs}.

(* get_unaligned_le32(p + i), where p holds the byte buffer bs and i + 4 <= |bs| *)
Definition get_unaligned_le32_spec :=
  DECLARE _get_unaligned_le32
  WITH sh: share, p: val, i: Z, bs: list byte
  PRE [ tptr tvoid ]
    PROP (readable_share sh; 0 <= i; i + 4 <= Zlength bs)
    PARAMS (offset_val i p)
    SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) p)
  POST [ tuint ]
    PROP () RETURN (Vint (le32_at bs i))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) p).

(* memzero_explicit(p, n): n zero bytes (like memset(p, 0, n)) *)
Definition memzero_explicit_spec :=
  DECLARE _memzero_explicit
  WITH sh: share, p: val, n: Z
  PRE [ tptr tvoid, tulong ]
    PROP (writable_share sh; 0 <= n <= Int64.max_unsigned)
    PARAMS (p; Vlong (Int64.repr n))
    SEP (data_at_ sh (tarray tuchar n) p)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh (tarray tuchar n) (Zrepeat (Vubyte Byte.zero) n) p).

End Specs.
