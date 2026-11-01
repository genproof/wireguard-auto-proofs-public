(* Pieces: the currency of the whole proof.

   A PIECE is a list G of specifications (ident * funspec) of functions of the code, each proved against
   its body: `semax_body V (Imports ++ G) f (i, spec)` in the compspecs of the unit (translation unit)
   whose Clight contains f, with V = the unit's varspecs (QPvarspecs of its QP program).

   Every harness theorem is assembled at the end from pieces (one whole-program Component per harness,
   VST's WholeComponent_semax_prog): the specifications of the functions a harness reaches come from the
   pieces, every other function gets a vacuous specification.  One specification per function: a function
   belongs to exactly ONE piece (static inline functions compiled into several units - memzero_explicit,
   get_unaligned_le32, crypto_memneq, the blake2s.h inlines, curve25519_clamp_secret - have identical Clight
   in every unit; the owner proves the body of one copy).

   Imports are given as a function of the compspecs of the unit whose body is proved, so that the
   specifications polymorphic in the compspecs (byte buffers only: memcpy, memzero_explicit, ...) are seen
   by each body proof at its own unit's compspecs; the assembly relates the instances (for byte arrays
   they are equal).  Specifications that mention malloc_token / mem_mgr (quickproof_malloc/free, calloc,
   kzalloc, kfree, ...) are stated at the compspecs of the world CSw (the whole program's), a parameter of
   the pieces that use them. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.counter.code WgNoise.blake2s.code
        WgNoise.chacha.code WgNoise.chacha_block.code WgNoise.poly1305.code WgNoise.poly1305_donna32.code
        WgNoise.chacha20poly1305.code WgNoise.curve25519.code WgNoise.curve25519_fiat32.code
        WgNoise.shim.code WgNoise.libc.code WgNoise.malloc.code.

(* the internal function i of a Clight program *)
Definition find_internal (p: Clight.program) (i: ident) : option function :=
  match find (fun d => Pos.eqb (fst d) i) (prog_defs p) with
  | Some (_, Gfun (Internal f)) => Some f
  | _ => None
  end.

(* a translation unit: its compspecs, its varspecs and its Clight *)
Record unit_ctx := mk_unit { u_cs: compspecs; u_V: varspecs; u_prog: Clight.program }.

Definition u_noise := mk_unit Noise.CS (QPvarspecs Noise.qp) WgNoise.noise.code.prog.
Definition u_cookie := mk_unit Cookie.CS (QPvarspecs Cookie.qp) WgNoise.cookie.code.prog.
Definition u_counter := mk_unit Counter.CS (QPvarspecs Counter.qp) WgNoise.counter.code.prog.
Definition u_blake2s := mk_unit Blake2s.CS (QPvarspecs Blake2s.qp) WgNoise.blake2s.code.prog.
Definition u_chacha := mk_unit Chacha.CS (QPvarspecs Chacha.qp) WgNoise.chacha.code.prog.
Definition u_chacha_block := mk_unit ChachaBlock.CS (QPvarspecs ChachaBlock.qp) WgNoise.chacha_block.code.prog.
Definition u_poly1305 := mk_unit Poly1305.CS (QPvarspecs Poly1305.qp) WgNoise.poly1305.code.prog.
Definition u_poly1305_donna32 :=
  mk_unit Poly1305Donna32.CS (QPvarspecs Poly1305Donna32.qp) WgNoise.poly1305_donna32.code.prog.
Definition u_chacha20poly1305 :=
  mk_unit Chacha20poly1305.CS (QPvarspecs Chacha20poly1305.qp) WgNoise.chacha20poly1305.code.prog.
Definition u_curve25519 := mk_unit Curve25519.CS (QPvarspecs Curve25519.qp) WgNoise.curve25519.code.prog.
Definition u_curve25519_fiat32 :=
  mk_unit Curve25519Fiat32.CS (QPvarspecs Curve25519Fiat32.qp) WgNoise.curve25519_fiat32.code.prog.
Definition u_shim := mk_unit Shim.CS (QPvarspecs Shim.qp) WgNoise.shim.code.prog.
Definition u_libc := mk_unit Libc.CS (QPvarspecs Libc.qp) WgNoise.libc.code.prog.
Definition u_malloc := mk_unit Malloc.CS (QPvarspecs Malloc.qp) WgNoise.malloc.code.prog.

(* the specification ip is proved against the body of fst ip in unit u, with the specifications G *)
Definition verified_in (u: unit_ctx) (G: funspecs) (ip: ident * funspec) : Prop :=
  exists f, find_internal (u_prog u) (fst ip) = Some f /\ @semax_body (u_V u) G (u_cs u) f ip.

(* a piece: G's identifiers distinct, every entry proved in one of the units, with Imports ++ G *)
Definition piece_ok (units: list unit_ctx) (Imports: compspecs -> funspecs) (G: funspecs) : Prop :=
  list_norepet (map fst G) /\
  Forall (fun ip => exists u, In u units /\ verified_in u (Imports (u_cs u) ++ G) ip) G.
