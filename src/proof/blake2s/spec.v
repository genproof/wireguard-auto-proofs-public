(* Specifications of the BLAKE2s layer: lib/crypto/blake2s.c (unit Blake2s) and the static inline
   functions of include/crypto/blake2s.h that noise.c, cookie.c and the harnesses compile into
   their own units (__blake2s_init, blake2s_init, blake2s_init_key, blake2s: byte-identical Clight
   in every unit, temporaries included).

   Owner: law prim_blake2s.  SHARED INTERFACE: one specification per
   function for every law.

   Conventions:
   - every specification is stated in the compspecs of the unit Blake2s (WgNoise.units.Blake2s.CS),
     also those of the header inlines (their body proofs use it too: struct blake2s_ctx is the same
     composite in every unit).  A caller of another unit converts the data_at of its own
     `struct blake2s_ctx` variable with change_compspecs;
   - the streaming state is the abstract predicate `blake2s_state sh key outlen msg ctx`: the
     context after init with (key, outlen) and update with msg (all chunks concatenated);
   - blake2s_final writes `blake2s key outlen msg` (model.v) and leaves the context all zero;
   - input buffers are `b2s_bytes sh bs p`: emp when bs = [] (p may then be anything, e.g. NULL),
     else the bytes at p;
   - blake2s_compress_generic reads the static const table blake2s_sigma: the functions that
     compress carry `blake2s_globals gv` (the table, readonly share Ers) in PRE and POST. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.blake2s.code.
Require WgNoise.cookie.code.
Require Import WgNoise.proof.libc.spec.
Require Export WgNoise.proof.blake2s.model.
Require Export WgNoise.proof.blake2s.spec_shared.

#[local] Existing Instance WgNoise.units.Blake2s.CS.
Local Open Scope Z_scope.

(* identifiers (clightgen's $"name": the same in every unit) *)
Definition _blake2s_ctx : ident := WgNoise.blake2s.code._blake2s_ctx.
Definition _blake2s_sigma : ident := WgNoise.blake2s.code._blake2s_sigma.
Definition _ror32 : ident := WgNoise.blake2s.code._ror32.
Definition _blake2s_increment_counter : ident := WgNoise.blake2s.code._blake2s_increment_counter.
Definition _blake2s_compress_generic : ident := WgNoise.blake2s.code._blake2s_compress_generic.
Definition _blake2s_set_lastblock : ident := WgNoise.blake2s.code._blake2s_set_lastblock.
Definition _blake2s_update : ident := WgNoise.blake2s.code._blake2s_update.
Definition _blake2s_final : ident := WgNoise.blake2s.code._blake2s_final.
Definition ___blake2s_init : ident := WgNoise.cookie.code.___blake2s_init.
Definition _blake2s_init : ident := WgNoise.cookie.code._blake2s_init.
Definition _blake2s_init_key : ident := WgNoise.cookie.code._blake2s_init_key.
Definition _blake2s : ident := WgNoise.cookie.code._blake2s.

Definition _h : ident := WgNoise.blake2s.code._h.
Definition _t : ident := WgNoise.blake2s.code._t.
Definition _f : ident := WgNoise.blake2s.code._f.
Definition _buf : ident := WgNoise.blake2s.code._buf.
Definition _buflen : ident := WgNoise.blake2s.code._buflen.
Definition _outlen : ident := WgNoise.blake2s.code._outlen.

Definition t_blake2s_ctx : type := Tstruct _blake2s_ctx noattr.

(* ---------------------------------------------------------------------- *)
(* Representation                                                          *)
(* ---------------------------------------------------------------------- *)

(* the global table blake2s_sigma (static const u8 [10][16]) *)
Definition blake2s_sigma_val : list (list val) :=
  map (map (fun z => Vint (Int.repr z))) b2s_sigma.

Definition blake2s_globals (gv: globals) : mpred :=
  data_at Ers (tarray (tarray tuchar 16) 10) blake2s_sigma_val (gv _blake2s_sigma).

(* the fields of a struct blake2s_ctx: h, counter t (Z, stored as t mod 2^64 in two words), f0 (f1 = 0),
   buf (64 values), buflen, outlen *)
Definition b2s_ctx_val (h: list int) (t: Z) (f0: int) (buf: list val) (buflen outlen: Z)
  : reptype t_blake2s_ctx :=
  (map Vint h,
   ([Vint (b2s_t0 t); Vint (b2s_t1 t)],
    ([Vint f0; Vint Int.zero],
     (buf, (Vint (Int.repr buflen), Vint (Int.repr outlen)))))).

(* the context after blake2s_final: all zero *)
Definition b2s_ctx_zero : reptype t_blake2s_ctx :=
  (Zrepeat (Vint Int.zero) 8,
   (Zrepeat (Vint Int.zero) 2,
    (Zrepeat (Vint Int.zero) 2,
     (Zrepeat (Vubyte Byte.zero) 64, (Vint Int.zero, Vint Int.zero))))).

(* The streaming state: initialised with key (0..32 bytes) and outlen (1..32), msg absorbed.
   With s = key block ++ msg and k = b2s_nfull s: h = the non-final blocks of s compressed, t = 64 k,
   f = 0, buf = the last block of s (0..64 bytes, then anything), buflen = its length. *)
Definition blake2s_state (sh: share) (key: list byte) (outlen: Z) (msg: list byte) (ctx: val)
  : mpred :=
  let s := b2s_stream key msg in
  let last := b2s_lastblock s in
  EX junk: list val,
    !! (1 <= outlen <= 32 /\ 0 <= Zlength key <= 32 /\ Zlength junk = 64 - Zlength last) &&
    data_at sh t_blake2s_ctx
      (b2s_ctx_val (b2s_h_nonfinal (Zlength key) outlen s) (64 * b2s_nfull s) Int.zero
         (map Vubyte last ++ junk) (Zlength last) outlen) ctx.

(* an input buffer: nothing when empty (the pointer may then be NULL) *)
Definition b2s_bytes (sh: share) (bs: list byte) (p: val) : mpred :=
  if Z.eq_dec (Zlength bs) 0 then emp
  else data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) p.

Lemma b2s_bytes_nil sh p : b2s_bytes sh [] p = emp.
Proof. reflexivity. Qed.

Lemma b2s_bytes_nonempty sh bs p :
  Zlength bs <> 0 ->
  b2s_bytes sh bs p = data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) p.
Proof. intros. unfold b2s_bytes. rewrite if_false by auto. reflexivity. Qed.

Lemma b2s_bytes_intro sh bs p :
  data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) p |--
  b2s_bytes sh bs p * (if Z.eq_dec (Zlength bs) 0
                       then data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) p else emp).
Proof. unfold b2s_bytes. if_tac; cancel. Qed.

(* ---------------------------------------------------------------------- *)
(* blake2s.c: internal functions                                           *)
(* ---------------------------------------------------------------------- *)

(* ror32(w, s) = w rotated right by s mod 32 *)
Definition ror32_spec :=
  DECLARE _ror32
  WITH w: int, s: int
  PRE [ tuint, tuint ]
    PROP () PARAMS (Vint w; Vint s) SEP ()
  POST [ tuint ]
    PROP () RETURN (Vint (Int.ror w s)) SEP ().

(* t += inc (64-bit counter in two words) *)
Definition blake2s_increment_counter_spec :=
  DECLARE _blake2s_increment_counter
  WITH sh: share, ctx: val, t: Z, inc: Z
  PRE [ tptr t_blake2s_ctx, tuint ]
    PROP (writable_share sh; 0 <= t; 0 <= inc <= Int.max_unsigned)
    PARAMS (ctx; Vint (Int.repr inc))
    SEP (field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 t); Vint (b2s_t1 t)] ctx)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 (t + inc)); Vint (b2s_t1 (t + inc))] ctx).

(* n blocks at data (possibly ctx->buf: the caller hands over that field as a byte array),
   counter advanced by inc before each *)
Definition blake2s_compress_generic_spec :=
  DECLARE _blake2s_compress_generic
  WITH sh: share, ctx: val, h: list int, t: Z, f0: int,
       dsh: share, data: val, n: Z, inc: Z, bs: list byte, gv: globals
  PRE [ tptr t_blake2s_ctx, tptr tuchar, tulong, tuint ]
    PROP (writable_share sh; readable_share dsh; Zlength h = 8; 0 <= t;
          0 <= inc <= Int.max_unsigned; 0 <= n; Zlength bs = (64 * n)%Z)
    PARAMS (ctx; data; Vlong (Int64.repr n); Vint (Int.repr inc)) GLOBALS (gv)
    SEP (field_at sh t_blake2s_ctx (DOT _h) (map Vint h) ctx;
         field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 t); Vint (b2s_t1 t)] ctx;
         field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
         data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data;
         blake2s_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (field_at sh t_blake2s_ctx (DOT _h) (map Vint (b2s_compress_n (Z.to_nat n) h t f0 inc bs)) ctx;
         field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 (t + n * inc)); Vint (b2s_t1 (t + n * inc))] ctx;
         field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
         data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data;
         blake2s_globals gv).

(* f[0] = -1 *)
Definition blake2s_set_lastblock_spec :=
  DECLARE _blake2s_set_lastblock
  WITH sh: share, ctx: val, f: list val
  PRE [ tptr t_blake2s_ctx ]
    PROP (writable_share sh; Zlength f = 2)
    PARAMS (ctx)
    SEP (field_at sh t_blake2s_ctx (DOT _f) f ctx)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (field_at sh t_blake2s_ctx (DOT _f) (upd_Znth 0 f (Vint Int.mone)) ctx).

(* ---------------------------------------------------------------------- *)
(* blake2s.c: the API                                                      *)
(* ---------------------------------------------------------------------- *)

(* blake2s_update(ctx, in, |data|): any chunk, empty included (in may be NULL when empty) *)
Definition blake2s_update_spec :=
  DECLARE _blake2s_update
  WITH sh: share, ctx: val, key: list byte, outlen: Z, msg: list byte,
       dsh: share, d: val, data: list byte, gv: globals
  PRE [ tptr t_blake2s_ctx, tptr tuchar, tulong ]
    PROP (writable_share sh; readable_share dsh; Zlength data <= Int64.max_unsigned)
    PARAMS (ctx; d; Vlong (Int64.repr (Zlength data))) GLOBALS (gv)
    SEP (blake2s_state sh key outlen msg ctx; b2s_bytes dsh data d; blake2s_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (blake2s_state sh key outlen (msg ++ data) ctx; b2s_bytes dsh data d; blake2s_globals gv).

(* blake2s_final(ctx, out): out[0..outlen) = BLAKE2s-outlen(key, msg); the context is zeroed *)
Definition blake2s_final_spec :=
  DECLARE _blake2s_final
  WITH sh: share, ctx: val, key: list byte, outlen: Z, msg: list byte,
       osh: share, out: val, gv: globals
  PRE [ tptr t_blake2s_ctx, tptr tuchar ]
    PROP (writable_share sh; writable_share osh)
    PARAMS (ctx; out) GLOBALS (gv)
    SEP (blake2s_state sh key outlen msg ctx; data_at_ osh (tarray tuchar outlen) out;
         blake2s_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh t_blake2s_ctx b2s_ctx_zero ctx;
         data_at osh (tarray tuchar outlen) (map Vubyte (blake2s key outlen msg)) out;
         blake2s_globals gv).

(* ---------------------------------------------------------------------- *)
(* include/crypto/blake2s.h: the static inline functions (one copy per unit) *)
(* ---------------------------------------------------------------------- *)

(* __blake2s_init(ctx, outlen, key, |key|): key may be NULL when empty *)
Definition __blake2s_init_spec :=
  DECLARE ___blake2s_init
  WITH sh: share, ctx: val, outlen: Z, ksh: share, k: val, key: list byte
  PRE [ tptr t_blake2s_ctx, tulong, tptr tvoid, tulong ]
    PROP (writable_share sh; readable_share ksh; 1 <= outlen <= 32; 0 <= Zlength key <= 32)
    PARAMS (ctx; Vlong (Int64.repr outlen); k; Vlong (Int64.repr (Zlength key)))
    SEP (data_at_ sh t_blake2s_ctx ctx; b2s_bytes ksh key k)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (blake2s_state sh key outlen [] ctx; b2s_bytes ksh key k).

Definition blake2s_init_spec :=
  DECLARE _blake2s_init
  WITH sh: share, ctx: val, outlen: Z
  PRE [ tptr t_blake2s_ctx, tulong ]
    PROP (writable_share sh; 1 <= outlen <= 32)
    PARAMS (ctx; Vlong (Int64.repr outlen))
    SEP (data_at_ sh t_blake2s_ctx ctx)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (blake2s_state sh [] outlen [] ctx).

(* the same as __blake2s_init (the documented key length is 1..32; 0 works too) *)
Definition blake2s_init_key_spec :=
  DECLARE _blake2s_init_key
  WITH sh: share, ctx: val, outlen: Z, ksh: share, k: val, key: list byte
  PRE [ tptr t_blake2s_ctx, tulong, tptr tvoid, tulong ]
    PROP (writable_share sh; readable_share ksh; 1 <= outlen <= 32; 0 <= Zlength key <= 32)
    PARAMS (ctx; Vlong (Int64.repr outlen); k; Vlong (Int64.repr (Zlength key)))
    SEP (data_at_ sh t_blake2s_ctx ctx; b2s_bytes ksh key k)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (blake2s_state sh key outlen [] ctx; b2s_bytes ksh key k).

(* blake2s(key, |key|, in, |data|, out, outlen): one shot; key / in may be NULL when empty *)
Definition blake2s_spec :=
  DECLARE _blake2s
  WITH ksh: share, k: val, key: list byte, dsh: share, d: val, data: list byte,
       osh: share, out: val, outlen: Z, gv: globals
  PRE [ tptr tuchar, tulong, tptr tuchar, tulong, tptr tuchar, tulong ]
    PROP (readable_share ksh; readable_share dsh; writable_share osh;
          1 <= outlen <= 32; 0 <= Zlength key <= 32; Zlength data <= Int64.max_unsigned)
    PARAMS (k; Vlong (Int64.repr (Zlength key)); d; Vlong (Int64.repr (Zlength data));
            out; Vlong (Int64.repr outlen)) GLOBALS (gv)
    SEP (b2s_bytes ksh key k; b2s_bytes dsh data d; data_at_ osh (tarray tuchar outlen) out;
         blake2s_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (b2s_bytes ksh key k; b2s_bytes dsh data d;
         data_at osh (tarray tuchar outlen) (map Vubyte (blake2s key outlen data)) out;
         blake2s_globals gv).

(* ---------------------------------------------------------------------- *)
(* Facts for clients                                                       *)
(* ---------------------------------------------------------------------- *)

Lemma blake2s_state_local_facts sh key outlen msg ctx :
  blake2s_state sh key outlen msg ctx |--
  !! (isptr ctx /\ 1 <= outlen <= 32 /\ 0 <= Zlength key <= 32).
Proof. unfold blake2s_state. Intros junk. entailer!. Qed.
#[export] Hint Resolve blake2s_state_local_facts : saturate_local.

Lemma blake2s_state_valid_pointer sh key outlen msg ctx :
  sepalg.nonidentity sh ->
  blake2s_state sh key outlen msg ctx |-- valid_pointer ctx.
Proof. intros. unfold blake2s_state. Intros junk. auto with valid_pointer. Qed.

(* give up a state without finalising it (e.g. to free the variable) *)
Lemma blake2s_state_data_at_ sh key outlen msg ctx :
  blake2s_state sh key outlen msg ctx |-- data_at_ sh t_blake2s_ctx ctx.
Proof. unfold blake2s_state. Intros junk. apply data_at_data_at_. Qed.
