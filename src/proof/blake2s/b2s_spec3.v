(* the BLAKE2s interface of the new contract.

   The specifications of src/proof/blake2s/spec.v, except blake2s_update and the one-shot blake2s: their
   chunk length is now bounded by PTRDIFF_MAX (Int64.max_signed) instead of 2^64 - 1.  Reason: for
   inlen >= 2^64 - 63, DIV_ROUND_UP(inlen, 64) in blake2s_update wraps (the old specification is false);
   no C object is larger than PTRDIFF_MAX, and the law prim_blake2s ends the run beyond it (DEVIATIONS.md L13).
   Every client (noise.c, cookie.c, the harnesses) passes chunks far below that bound.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.libc.spec.
Require Export WgNoise.proof.blake2s.spec.

#[local] Existing Instance WgNoise.units.Blake2s.CS.
Local Open Scope Z_scope.

(* blake2s_update(ctx, in, |data|): any chunk of at most PTRDIFF_MAX bytes, empty included (in may be NULL
   when empty) *)
Definition blake2s_update_spec3 :=
  DECLARE _blake2s_update
  WITH sh: share, ctx: val, key: list byte, outlen: Z, msg: list byte,
       dsh: share, d: val, data: list byte, gv: globals
  PRE [ tptr t_blake2s_ctx, tptr tuchar, tulong ]
    PROP (writable_share sh; readable_share dsh; Zlength data <= Int64.max_signed)
    PARAMS (ctx; d; Vlong (Int64.repr (Zlength data))) GLOBALS (gv)
    SEP (blake2s_state sh key outlen msg ctx; b2s_bytes dsh data d; blake2s_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (blake2s_state sh key outlen (msg ++ data) ctx; b2s_bytes dsh data d; blake2s_globals gv).

(* blake2s(key, |key|, in, |data|, out, outlen): one shot; key / in may be NULL when empty *)
Definition blake2s_spec3 :=
  DECLARE _blake2s
  WITH ksh: share, k: val, key: list byte, dsh: share, d: val, data: list byte,
       osh: share, out: val, outlen: Z, gv: globals
  PRE [ tptr tuchar, tulong, tptr tuchar, tulong, tptr tuchar, tulong ]
    PROP (readable_share ksh; readable_share dsh; writable_share osh;
          1 <= outlen <= 32; 0 <= Zlength key <= 32; Zlength data <= Int64.max_signed)
    PARAMS (k; Vlong (Int64.repr (Zlength key)); d; Vlong (Int64.repr (Zlength data));
            out; Vlong (Int64.repr outlen)) GLOBALS (gv)
    SEP (b2s_bytes ksh key k; b2s_bytes dsh data d; data_at_ osh (tarray tuchar outlen) out;
         blake2s_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (b2s_bytes ksh key k; b2s_bytes dsh data d;
         data_at osh (tarray tuchar outlen) (map Vubyte (blake2s key outlen data)) out;
         blake2s_globals gv).

(* the imports of the BLAKE2s piece (owned by the libc piece) *)
Definition blake2s_imports3 (cs: compspecs) : funspecs :=
  [@memcpy_spec cs; @memset_spec cs].

(* the specifications of the BLAKE2s piece: blake2s.c, the blake2s.h inlines (cookie.c's copy), and the
   shared inlines get_unaligned_le32 / memzero_explicit (blake2s.c's copies) *)
Definition blake2s_G3 : funspecs :=
  [ror32_spec; blake2s_increment_counter_spec; blake2s_compress_generic_spec; blake2s_set_lastblock_spec;
   blake2s_update_spec3; blake2s_final_spec;
   __blake2s_init_spec; blake2s_init_spec; blake2s_init_key_spec; blake2s_spec3;
   @get_unaligned_le32_spec Blake2s.CS; @memzero_explicit_spec Blake2s.CS].
