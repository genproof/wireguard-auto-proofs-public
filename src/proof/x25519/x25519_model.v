(* The functional model of lib/crypto/curve25519-fiat32.c: a transliteration of the
   C code over CompCert's machine integers (u32 = int, u64 = int64, modular arithmetic exactly as Clight
   evaluates it; every operation of the code is on unsigned types, so there is no undefined behaviour to
   exclude).  A field element is a list of 10 limbs (list int).  NOT proved equal to RFC 7748's X25519:
   x25519_m is "what curve25519_generic computes".

   The limb functions fe_mul_m, fe_sqr_m, fe_mul121666_m were generated from the C source (one `let` per C
   variable, same names, same association of + as in the C expressions). *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.prims.prim_api.

Local Open Scope Z_scope.

(* (u64)a : zero extension; (u32)x : the low 32 bits *)
Definition u64 (a: int) : int64 := Int64.repr (Int.unsigned a).
Definition lo (x: int64) : int := Int.repr (Int64.unsigned x).
(* (u8)x : the low 8 bits *)
Definition u8_of (x: int) : byte := Byte.repr (Int.unsigned x).

(* ------------------------------------------------------------------ *)
(* bytes <-> limbs                                                     *)
(* ------------------------------------------------------------------ *)

(* fe_frombytes_impl: s = 32 bytes (the top bit is ignored) *)
Definition fe_frombytes_m (s: list byte) : list int :=
  let a0 := le32_at s 0 in
  let a1 := le32_at s 4 in
  let a2 := le32_at s 8 in
  let a3 := le32_at s 12 in
  let a4 := le32_at s 16 in
  let a5 := le32_at s 20 in
  let a6 := le32_at s 24 in
  let a7 := le32_at s 28 in
  [Int.and a0 (Int.repr 67108863);
   Int.or (Int.shru a0 (Int.repr 26)) (Int.shl (Int.and a1 (Int.repr 524287)) (Int.repr 6));
   Int.or (Int.shru a1 (Int.repr 19)) (Int.shl (Int.and a2 (Int.repr 8191)) (Int.repr 13));
   Int.or (Int.shru a2 (Int.repr 13)) (Int.shl (Int.and a3 (Int.repr 63)) (Int.repr 19));
   Int.shru a3 (Int.repr 6);
   Int.and a4 (Int.repr 33554431);
   Int.or (Int.shru a4 (Int.repr 25)) (Int.shl (Int.and a5 (Int.repr 524287)) (Int.repr 7));
   Int.or (Int.shru a5 (Int.repr 19)) (Int.shl (Int.and a6 (Int.repr 4095)) (Int.repr 13));
   Int.or (Int.shru a6 (Int.repr 12)) (Int.shl (Int.and a7 (Int.repr 63)) (Int.repr 20));
   Int.and (Int.shru a7 (Int.repr 6)) (Int.repr 33554431)].

(* addcarryx_u25 / _u26 (bits = 25 / 26): (low, carry) of a + b + c *)
Definition addcarryx_m (bits: Z) (c a b: int) : int * int :=
  let x := Int.add (Int.add a b) c in
  (Int.and x (Int.repr (2 ^ bits - 1)), Int.and (Int.shru x (Int.repr bits)) Int.one).

(* subborrow_u25 / _u26: (low, borrow) of a - b - c *)
Definition subborrow_m (bits: Z) (c a b: int) : int * int :=
  let x := Int.sub (Int.sub a b) c in
  (Int.and x (Int.repr (2 ^ bits - 1)), Int.shru x (Int.repr 31)).

(* cmovznz32(t, z, nz): nz if t <> 0, else z *)
Definition cmovznz32_m (t z nz: int) : int :=
  let m := Int.neg (if Int.eq t Int.zero then Int.zero else Int.one) in
  Int.or (Int.and m nz) (Int.and (Int.not m) z).

(* fe_freeze: the canonical representative (subtract p, add it back if negative) *)
Definition fe_freeze_m (f: list int) : list int :=
  let x17 := Znth 9 f in
  let x18 := Znth 8 f in
  let x16 := Znth 7 f in
  let x14 := Znth 6 f in
  let x12 := Znth 5 f in
  let x10 := Znth 4 f in
  let x8 := Znth 3 f in
  let x6 := Znth 2 f in
  let x4 := Znth 1 f in
  let x2 := Znth 0 f in
  let (x20, x21) := subborrow_m 26 Int.zero x2 (Int.repr 67108845) in
  let (x23, x24) := subborrow_m 25 x21 x4 (Int.repr 33554431) in
  let (x26, x27) := subborrow_m 26 x24 x6 (Int.repr 67108863) in
  let (x29, x30) := subborrow_m 25 x27 x8 (Int.repr 33554431) in
  let (x32, x33) := subborrow_m 26 x30 x10 (Int.repr 67108863) in
  let (x35, x36) := subborrow_m 25 x33 x12 (Int.repr 33554431) in
  let (x38, x39) := subborrow_m 26 x36 x14 (Int.repr 67108863) in
  let (x41, x42) := subborrow_m 25 x39 x16 (Int.repr 33554431) in
  let (x44, x45) := subborrow_m 26 x42 x18 (Int.repr 67108863) in
  let (x47, x48) := subborrow_m 25 x45 x17 (Int.repr 33554431) in
  let x49 := cmovznz32_m x48 Int.zero (Int.repr 4294967295) in
  let x50 := Int.and x49 (Int.repr 67108845) in
  let (x52, x53) := addcarryx_m 26 Int.zero x20 x50 in
  let x54 := Int.and x49 (Int.repr 33554431) in
  let (x56, x57) := addcarryx_m 25 x53 x23 x54 in
  let x58 := Int.and x49 (Int.repr 67108863) in
  let (x60, x61) := addcarryx_m 26 x57 x26 x58 in
  let x62 := Int.and x49 (Int.repr 33554431) in
  let (x64, x65) := addcarryx_m 25 x61 x29 x62 in
  let x66 := Int.and x49 (Int.repr 67108863) in
  let (x68, x69) := addcarryx_m 26 x65 x32 x66 in
  let x70 := Int.and x49 (Int.repr 33554431) in
  let (x72, x73) := addcarryx_m 25 x69 x35 x70 in
  let x74 := Int.and x49 (Int.repr 67108863) in
  let (x76, x77) := addcarryx_m 26 x73 x38 x74 in
  let x78 := Int.and x49 (Int.repr 33554431) in
  let (x80, x81) := addcarryx_m 25 x77 x41 x78 in
  let x82 := Int.and x49 (Int.repr 67108863) in
  let (x84, x85) := addcarryx_m 26 x81 x44 x82 in
  let x86 := Int.and x49 (Int.repr 33554431) in
  let (x88, _) := addcarryx_m 25 x85 x47 x86 in
  [x52; x56; x60; x64; x68; x72; x76; x80; x84; x88].

Definition fe_tobytes_m (f: list int) : list byte :=
  let h := fe_freeze_m f in
  let h0 := Znth 0 h in let h1 := Znth 1 h in let h2 := Znth 2 h in let h3 := Znth 3 h in
  let h4 := Znth 4 h in let h5 := Znth 5 h in let h6 := Znth 6 h in let h7 := Znth 7 h in
  let h8 := Znth 8 h in let h9 := Znth 9 h in
  [u8_of (Int.shru h0 (Int.repr 0));
   u8_of (Int.shru h0 (Int.repr 8));
   u8_of (Int.shru h0 (Int.repr 16));
   u8_of (Int.or (Int.shru h0 (Int.repr 24)) (Int.shl h1 (Int.repr 2)));
   u8_of (Int.shru h1 (Int.repr 6));
   u8_of (Int.shru h1 (Int.repr 14));
   u8_of (Int.or (Int.shru h1 (Int.repr 22)) (Int.shl h2 (Int.repr 3)));
   u8_of (Int.shru h2 (Int.repr 5));
   u8_of (Int.shru h2 (Int.repr 13));
   u8_of (Int.or (Int.shru h2 (Int.repr 21)) (Int.shl h3 (Int.repr 5)));
   u8_of (Int.shru h3 (Int.repr 3));
   u8_of (Int.shru h3 (Int.repr 11));
   u8_of (Int.or (Int.shru h3 (Int.repr 19)) (Int.shl h4 (Int.repr 6)));
   u8_of (Int.shru h4 (Int.repr 2));
   u8_of (Int.shru h4 (Int.repr 10));
   u8_of (Int.shru h4 (Int.repr 18));
   u8_of (Int.shru h5 (Int.repr 0));
   u8_of (Int.shru h5 (Int.repr 8));
   u8_of (Int.shru h5 (Int.repr 16));
   u8_of (Int.or (Int.shru h5 (Int.repr 24)) (Int.shl h6 (Int.repr 1)));
   u8_of (Int.shru h6 (Int.repr 7));
   u8_of (Int.shru h6 (Int.repr 15));
   u8_of (Int.or (Int.shru h6 (Int.repr 23)) (Int.shl h7 (Int.repr 3)));
   u8_of (Int.shru h7 (Int.repr 5));
   u8_of (Int.shru h7 (Int.repr 13));
   u8_of (Int.or (Int.shru h7 (Int.repr 21)) (Int.shl h8 (Int.repr 4)));
   u8_of (Int.shru h8 (Int.repr 4));
   u8_of (Int.shru h8 (Int.repr 12));
   u8_of (Int.or (Int.shru h8 (Int.repr 20)) (Int.shl h9 (Int.repr 6)));
   u8_of (Int.shru h9 (Int.repr 2));
   u8_of (Int.shru h9 (Int.repr 10));
   u8_of (Int.shru h9 (Int.repr 18))].

(* ------------------------------------------------------------------ *)
(* limb arithmetic                                                     *)
(* ------------------------------------------------------------------ *)

Definition fe0_m : list int := Zrepeat Int.zero 10.
Definition fe1_m : list int := Int.one :: Zrepeat Int.zero 9.

(* fe_add_impl *)
Definition fe_add_m (f g: list int) : list int :=
  map (fun i => Int.add (Znth i f) (Znth i g)) (upto 10).

(* fe_sub_impl: (2p + f) - g, limb-wise *)
Definition fe_sub_bias : list int :=
  map Int.repr [134217690; 67108862; 134217726; 67108862; 134217726; 67108862; 134217726; 67108862;
                134217726; 67108862].
Definition fe_sub_m (f g: list int) : list int :=
  map (fun i => Int.sub (Int.add (Znth i fe_sub_bias) (Znth i f)) (Znth i g)) (upto 10).

(* fe_mul_impl *)
Definition fe_mul_m (f g: list int) : list int :=
  let x20 := Znth 9 f in
  let x21 := Znth 8 f in
  let x19 := Znth 7 f in
  let x17 := Znth 6 f in
  let x15 := Znth 5 f in
  let x13 := Znth 4 f in
  let x11 := Znth 3 f in
  let x9 := Znth 2 f in
  let x7 := Znth 1 f in
  let x5 := Znth 0 f in
  let x38 := Znth 9 g in
  let x39 := Znth 8 g in
  let x37 := Znth 7 g in
  let x35 := Znth 6 g in
  let x33 := Znth 5 g in
  let x31 := Znth 4 g in
  let x29 := Znth 3 g in
  let x27 := Znth 2 g in
  let x25 := Znth 1 g in
  let x23 := Znth 0 g in
  let x40 := (Int64.mul (u64 x23) (u64 x5)) in
  let x41 := (Int64.add (Int64.mul (u64 x23) (u64 x7)) (Int64.mul (u64 x25) (u64 x5))) in
  let x42 := (Int64.add (Int64.add (Int64.mul (u64 (Int.mul (Int.repr 2) x25)) (u64 x7)) (Int64.mul (u64 x23) (u64 x9))) (Int64.mul (u64 x27) (u64 x5))) in
  let x43 := (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x25) (u64 x9)) (Int64.mul (u64 x27) (u64 x7))) (Int64.mul (u64 x23) (u64 x11))) (Int64.mul (u64 x29) (u64 x5))) in
  let x44 := (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x27) (u64 x9)) (Int64.mul (Int64.repr 2) (Int64.add (Int64.mul (u64 x25) (u64 x11)) (Int64.mul (u64 x29) (u64 x7))))) (Int64.mul (u64 x23) (u64 x13))) (Int64.mul (u64 x31) (u64 x5))) in
  let x45 := (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x27) (u64 x11)) (Int64.mul (u64 x29) (u64 x9))) (Int64.mul (u64 x25) (u64 x13))) (Int64.mul (u64 x31) (u64 x7))) (Int64.mul (u64 x23) (u64 x15))) (Int64.mul (u64 x33) (u64 x5))) in
  let x46 := (Int64.add (Int64.add (Int64.add (Int64.add (Int64.mul (Int64.repr 2) (Int64.add (Int64.add (Int64.mul (u64 x29) (u64 x11)) (Int64.mul (u64 x25) (u64 x15))) (Int64.mul (u64 x33) (u64 x7)))) (Int64.mul (u64 x27) (u64 x13))) (Int64.mul (u64 x31) (u64 x9))) (Int64.mul (u64 x23) (u64 x17))) (Int64.mul (u64 x35) (u64 x5))) in
  let x47 := (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x29) (u64 x13)) (Int64.mul (u64 x31) (u64 x11))) (Int64.mul (u64 x27) (u64 x15))) (Int64.mul (u64 x33) (u64 x9))) (Int64.mul (u64 x25) (u64 x17))) (Int64.mul (u64 x35) (u64 x7))) (Int64.mul (u64 x23) (u64 x19))) (Int64.mul (u64 x37) (u64 x5))) in
  let x48 := (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x31) (u64 x13)) (Int64.mul (Int64.repr 2) (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x29) (u64 x15)) (Int64.mul (u64 x33) (u64 x11))) (Int64.mul (u64 x25) (u64 x19))) (Int64.mul (u64 x37) (u64 x7))))) (Int64.mul (u64 x27) (u64 x17))) (Int64.mul (u64 x35) (u64 x9))) (Int64.mul (u64 x23) (u64 x21))) (Int64.mul (u64 x39) (u64 x5))) in
  let x49 := (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x31) (u64 x15)) (Int64.mul (u64 x33) (u64 x13))) (Int64.mul (u64 x29) (u64 x17))) (Int64.mul (u64 x35) (u64 x11))) (Int64.mul (u64 x27) (u64 x19))) (Int64.mul (u64 x37) (u64 x9))) (Int64.mul (u64 x25) (u64 x21))) (Int64.mul (u64 x39) (u64 x7))) (Int64.mul (u64 x23) (u64 x20))) (Int64.mul (u64 x38) (u64 x5))) in
  let x50 := (Int64.add (Int64.add (Int64.add (Int64.add (Int64.mul (Int64.repr 2) (Int64.add (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x33) (u64 x15)) (Int64.mul (u64 x29) (u64 x19))) (Int64.mul (u64 x37) (u64 x11))) (Int64.mul (u64 x25) (u64 x20))) (Int64.mul (u64 x38) (u64 x7)))) (Int64.mul (u64 x31) (u64 x17))) (Int64.mul (u64 x35) (u64 x13))) (Int64.mul (u64 x27) (u64 x21))) (Int64.mul (u64 x39) (u64 x9))) in
  let x51 := (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x33) (u64 x17)) (Int64.mul (u64 x35) (u64 x15))) (Int64.mul (u64 x31) (u64 x19))) (Int64.mul (u64 x37) (u64 x13))) (Int64.mul (u64 x29) (u64 x21))) (Int64.mul (u64 x39) (u64 x11))) (Int64.mul (u64 x27) (u64 x20))) (Int64.mul (u64 x38) (u64 x9))) in
  let x52 := (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x35) (u64 x17)) (Int64.mul (Int64.repr 2) (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x33) (u64 x19)) (Int64.mul (u64 x37) (u64 x15))) (Int64.mul (u64 x29) (u64 x20))) (Int64.mul (u64 x38) (u64 x11))))) (Int64.mul (u64 x31) (u64 x21))) (Int64.mul (u64 x39) (u64 x13))) in
  let x53 := (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x35) (u64 x19)) (Int64.mul (u64 x37) (u64 x17))) (Int64.mul (u64 x33) (u64 x21))) (Int64.mul (u64 x39) (u64 x15))) (Int64.mul (u64 x31) (u64 x20))) (Int64.mul (u64 x38) (u64 x13))) in
  let x54 := (Int64.add (Int64.add (Int64.mul (Int64.repr 2) (Int64.add (Int64.add (Int64.mul (u64 x37) (u64 x19)) (Int64.mul (u64 x33) (u64 x20))) (Int64.mul (u64 x38) (u64 x15)))) (Int64.mul (u64 x35) (u64 x21))) (Int64.mul (u64 x39) (u64 x17))) in
  let x55 := (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x37) (u64 x21)) (Int64.mul (u64 x39) (u64 x19))) (Int64.mul (u64 x35) (u64 x20))) (Int64.mul (u64 x38) (u64 x17))) in
  let x56 := (Int64.add (Int64.mul (u64 x39) (u64 x21)) (Int64.mul (Int64.repr 2) (Int64.add (Int64.mul (u64 x37) (u64 x20)) (Int64.mul (u64 x38) (u64 x19))))) in
  let x57 := (Int64.add (Int64.mul (u64 x39) (u64 x20)) (Int64.mul (u64 x38) (u64 x21))) in
  let x58 := (Int64.mul (u64 (Int.mul (Int.repr 2) x38)) (u64 x20)) in
  let x59 := (Int64.add x48 (Int64.shl x58 (Int64.repr 4))) in
  let x60 := (Int64.add x59 (Int64.shl x58 (Int64.repr 1))) in
  let x61 := (Int64.add x60 x58) in
  let x62 := (Int64.add x47 (Int64.shl x57 (Int64.repr 4))) in
  let x63 := (Int64.add x62 (Int64.shl x57 (Int64.repr 1))) in
  let x64 := (Int64.add x63 x57) in
  let x65 := (Int64.add x46 (Int64.shl x56 (Int64.repr 4))) in
  let x66 := (Int64.add x65 (Int64.shl x56 (Int64.repr 1))) in
  let x67 := (Int64.add x66 x56) in
  let x68 := (Int64.add x45 (Int64.shl x55 (Int64.repr 4))) in
  let x69 := (Int64.add x68 (Int64.shl x55 (Int64.repr 1))) in
  let x70 := (Int64.add x69 x55) in
  let x71 := (Int64.add x44 (Int64.shl x54 (Int64.repr 4))) in
  let x72 := (Int64.add x71 (Int64.shl x54 (Int64.repr 1))) in
  let x73 := (Int64.add x72 x54) in
  let x74 := (Int64.add x43 (Int64.shl x53 (Int64.repr 4))) in
  let x75 := (Int64.add x74 (Int64.shl x53 (Int64.repr 1))) in
  let x76 := (Int64.add x75 x53) in
  let x77 := (Int64.add x42 (Int64.shl x52 (Int64.repr 4))) in
  let x78 := (Int64.add x77 (Int64.shl x52 (Int64.repr 1))) in
  let x79 := (Int64.add x78 x52) in
  let x80 := (Int64.add x41 (Int64.shl x51 (Int64.repr 4))) in
  let x81 := (Int64.add x80 (Int64.shl x51 (Int64.repr 1))) in
  let x82 := (Int64.add x81 x51) in
  let x83 := (Int64.add x40 (Int64.shl x50 (Int64.repr 4))) in
  let x84 := (Int64.add x83 (Int64.shl x50 (Int64.repr 1))) in
  let x85 := (Int64.add x84 x50) in
  let x86 := (Int64.shru x85 (Int64.repr 26)) in
  let x87 := (Int.and (lo x85) (Int.repr 67108863)) in
  let x88 := (Int64.add x86 x82) in
  let x89 := (Int64.shru x88 (Int64.repr 25)) in
  let x90 := (Int.and (lo x88) (Int.repr 33554431)) in
  let x91 := (Int64.add x89 x79) in
  let x92 := (Int64.shru x91 (Int64.repr 26)) in
  let x93 := (Int.and (lo x91) (Int.repr 67108863)) in
  let x94 := (Int64.add x92 x76) in
  let x95 := (Int64.shru x94 (Int64.repr 25)) in
  let x96 := (Int.and (lo x94) (Int.repr 33554431)) in
  let x97 := (Int64.add x95 x73) in
  let x98 := (Int64.shru x97 (Int64.repr 26)) in
  let x99 := (Int.and (lo x97) (Int.repr 67108863)) in
  let x100 := (Int64.add x98 x70) in
  let x101 := (Int64.shru x100 (Int64.repr 25)) in
  let x102 := (Int.and (lo x100) (Int.repr 33554431)) in
  let x103 := (Int64.add x101 x67) in
  let x104 := (Int64.shru x103 (Int64.repr 26)) in
  let x105 := (Int.and (lo x103) (Int.repr 67108863)) in
  let x106 := (Int64.add x104 x64) in
  let x107 := (Int64.shru x106 (Int64.repr 25)) in
  let x108 := (Int.and (lo x106) (Int.repr 33554431)) in
  let x109 := (Int64.add x107 x61) in
  let x110 := (Int64.shru x109 (Int64.repr 26)) in
  let x111 := (Int.and (lo x109) (Int.repr 67108863)) in
  let x112 := (Int64.add x110 x49) in
  let x113 := (Int64.shru x112 (Int64.repr 25)) in
  let x114 := (Int.and (lo x112) (Int.repr 33554431)) in
  let x115 := (Int64.add (u64 x87) (Int64.mul (Int64.repr 19) x113)) in
  let x116 := (lo (Int64.shru x115 (Int64.repr 26))) in
  let x117 := (Int.and (lo x115) (Int.repr 67108863)) in
  let x118 := (Int.add x116 x90) in
  let x119 := (Int.shru x118 (Int.repr 25)) in
  let x120 := (Int.and x118 (Int.repr 33554431)) in
  [x117; x120; (Int.add x119 x93); x96; x99; x102; x105; x108; x111; x114].

(* fe_sqr_impl *)
Definition fe_sqr_m (f: list int) : list int :=
  let x17 := Znth 9 f in
  let x18 := Znth 8 f in
  let x16 := Znth 7 f in
  let x14 := Znth 6 f in
  let x12 := Znth 5 f in
  let x10 := Znth 4 f in
  let x8 := Znth 3 f in
  let x6 := Znth 2 f in
  let x4 := Znth 1 f in
  let x2 := Znth 0 f in
  let x19 := (Int64.mul (u64 x2) (u64 x2)) in
  let x20 := (Int64.mul (u64 (Int.mul (Int.repr 2) x2)) (u64 x4)) in
  let x21 := (Int64.mul (Int64.repr 2) (Int64.add (Int64.mul (u64 x4) (u64 x4)) (Int64.mul (u64 x2) (u64 x6)))) in
  let x22 := (Int64.mul (Int64.repr 2) (Int64.add (Int64.mul (u64 x4) (u64 x6)) (Int64.mul (u64 x2) (u64 x8)))) in
  let x23 := (Int64.add (Int64.add (Int64.mul (u64 x6) (u64 x6)) (Int64.mul (u64 (Int.mul (Int.repr 4) x4)) (u64 x8))) (Int64.mul (u64 (Int.mul (Int.repr 2) x2)) (u64 x10))) in
  let x24 := (Int64.mul (Int64.repr 2) (Int64.add (Int64.add (Int64.mul (u64 x6) (u64 x8)) (Int64.mul (u64 x4) (u64 x10))) (Int64.mul (u64 x2) (u64 x12)))) in
  let x25 := (Int64.mul (Int64.repr 2) (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x8) (u64 x8)) (Int64.mul (u64 x6) (u64 x10))) (Int64.mul (u64 x2) (u64 x14))) (Int64.mul (u64 (Int.mul (Int.repr 2) x4)) (u64 x12)))) in
  let x26 := (Int64.mul (Int64.repr 2) (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x8) (u64 x10)) (Int64.mul (u64 x6) (u64 x12))) (Int64.mul (u64 x4) (u64 x14))) (Int64.mul (u64 x2) (u64 x16)))) in
  let x27 := (Int64.add (Int64.mul (u64 x10) (u64 x10)) (Int64.mul (Int64.repr 2) (Int64.add (Int64.add (Int64.mul (u64 x6) (u64 x14)) (Int64.mul (u64 x2) (u64 x18))) (Int64.mul (Int64.repr 2) (Int64.add (Int64.mul (u64 x4) (u64 x16)) (Int64.mul (u64 x8) (u64 x12))))))) in
  let x28 := (Int64.mul (Int64.repr 2) (Int64.add (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x10) (u64 x12)) (Int64.mul (u64 x8) (u64 x14))) (Int64.mul (u64 x6) (u64 x16))) (Int64.mul (u64 x4) (u64 x18))) (Int64.mul (u64 x2) (u64 x17)))) in
  let x29 := (Int64.mul (Int64.repr 2) (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x12) (u64 x12)) (Int64.mul (u64 x10) (u64 x14))) (Int64.mul (u64 x6) (u64 x18))) (Int64.mul (Int64.repr 2) (Int64.add (Int64.mul (u64 x8) (u64 x16)) (Int64.mul (u64 x4) (u64 x17)))))) in
  let x30 := (Int64.mul (Int64.repr 2) (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x12) (u64 x14)) (Int64.mul (u64 x10) (u64 x16))) (Int64.mul (u64 x8) (u64 x18))) (Int64.mul (u64 x6) (u64 x17)))) in
  let x31 := (Int64.add (Int64.mul (u64 x14) (u64 x14)) (Int64.mul (Int64.repr 2) (Int64.add (Int64.mul (u64 x10) (u64 x18)) (Int64.mul (Int64.repr 2) (Int64.add (Int64.mul (u64 x12) (u64 x16)) (Int64.mul (u64 x8) (u64 x17))))))) in
  let x32 := (Int64.mul (Int64.repr 2) (Int64.add (Int64.add (Int64.mul (u64 x14) (u64 x16)) (Int64.mul (u64 x12) (u64 x18))) (Int64.mul (u64 x10) (u64 x17)))) in
  let x33 := (Int64.mul (Int64.repr 2) (Int64.add (Int64.add (Int64.mul (u64 x16) (u64 x16)) (Int64.mul (u64 x14) (u64 x18))) (Int64.mul (u64 (Int.mul (Int.repr 2) x12)) (u64 x17)))) in
  let x34 := (Int64.mul (Int64.repr 2) (Int64.add (Int64.mul (u64 x16) (u64 x18)) (Int64.mul (u64 x14) (u64 x17)))) in
  let x35 := (Int64.add (Int64.mul (u64 x18) (u64 x18)) (Int64.mul (u64 (Int.mul (Int.repr 4) x16)) (u64 x17))) in
  let x36 := (Int64.mul (u64 (Int.mul (Int.repr 2) x18)) (u64 x17)) in
  let x37 := (Int64.mul (u64 (Int.mul (Int.repr 2) x17)) (u64 x17)) in
  let x38 := (Int64.add x27 (Int64.shl x37 (Int64.repr 4))) in
  let x39 := (Int64.add x38 (Int64.shl x37 (Int64.repr 1))) in
  let x40 := (Int64.add x39 x37) in
  let x41 := (Int64.add x26 (Int64.shl x36 (Int64.repr 4))) in
  let x42 := (Int64.add x41 (Int64.shl x36 (Int64.repr 1))) in
  let x43 := (Int64.add x42 x36) in
  let x44 := (Int64.add x25 (Int64.shl x35 (Int64.repr 4))) in
  let x45 := (Int64.add x44 (Int64.shl x35 (Int64.repr 1))) in
  let x46 := (Int64.add x45 x35) in
  let x47 := (Int64.add x24 (Int64.shl x34 (Int64.repr 4))) in
  let x48 := (Int64.add x47 (Int64.shl x34 (Int64.repr 1))) in
  let x49 := (Int64.add x48 x34) in
  let x50 := (Int64.add x23 (Int64.shl x33 (Int64.repr 4))) in
  let x51 := (Int64.add x50 (Int64.shl x33 (Int64.repr 1))) in
  let x52 := (Int64.add x51 x33) in
  let x53 := (Int64.add x22 (Int64.shl x32 (Int64.repr 4))) in
  let x54 := (Int64.add x53 (Int64.shl x32 (Int64.repr 1))) in
  let x55 := (Int64.add x54 x32) in
  let x56 := (Int64.add x21 (Int64.shl x31 (Int64.repr 4))) in
  let x57 := (Int64.add x56 (Int64.shl x31 (Int64.repr 1))) in
  let x58 := (Int64.add x57 x31) in
  let x59 := (Int64.add x20 (Int64.shl x30 (Int64.repr 4))) in
  let x60 := (Int64.add x59 (Int64.shl x30 (Int64.repr 1))) in
  let x61 := (Int64.add x60 x30) in
  let x62 := (Int64.add x19 (Int64.shl x29 (Int64.repr 4))) in
  let x63 := (Int64.add x62 (Int64.shl x29 (Int64.repr 1))) in
  let x64 := (Int64.add x63 x29) in
  let x65 := (Int64.shru x64 (Int64.repr 26)) in
  let x66 := (Int.and (lo x64) (Int.repr 67108863)) in
  let x67 := (Int64.add x65 x61) in
  let x68 := (Int64.shru x67 (Int64.repr 25)) in
  let x69 := (Int.and (lo x67) (Int.repr 33554431)) in
  let x70 := (Int64.add x68 x58) in
  let x71 := (Int64.shru x70 (Int64.repr 26)) in
  let x72 := (Int.and (lo x70) (Int.repr 67108863)) in
  let x73 := (Int64.add x71 x55) in
  let x74 := (Int64.shru x73 (Int64.repr 25)) in
  let x75 := (Int.and (lo x73) (Int.repr 33554431)) in
  let x76 := (Int64.add x74 x52) in
  let x77 := (Int64.shru x76 (Int64.repr 26)) in
  let x78 := (Int.and (lo x76) (Int.repr 67108863)) in
  let x79 := (Int64.add x77 x49) in
  let x80 := (Int64.shru x79 (Int64.repr 25)) in
  let x81 := (Int.and (lo x79) (Int.repr 33554431)) in
  let x82 := (Int64.add x80 x46) in
  let x83 := (Int64.shru x82 (Int64.repr 26)) in
  let x84 := (Int.and (lo x82) (Int.repr 67108863)) in
  let x85 := (Int64.add x83 x43) in
  let x86 := (Int64.shru x85 (Int64.repr 25)) in
  let x87 := (Int.and (lo x85) (Int.repr 33554431)) in
  let x88 := (Int64.add x86 x40) in
  let x89 := (Int64.shru x88 (Int64.repr 26)) in
  let x90 := (Int.and (lo x88) (Int.repr 67108863)) in
  let x91 := (Int64.add x89 x28) in
  let x92 := (Int64.shru x91 (Int64.repr 25)) in
  let x93 := (Int.and (lo x91) (Int.repr 33554431)) in
  let x94 := (Int64.add (u64 x66) (Int64.mul (Int64.repr 19) x92)) in
  let x95 := (lo (Int64.shru x94 (Int64.repr 26))) in
  let x96 := (Int.and (lo x94) (Int.repr 67108863)) in
  let x97 := (Int.add x95 x69) in
  let x98 := (Int.shru x97 (Int.repr 25)) in
  let x99 := (Int.and x97 (Int.repr 33554431)) in
  [x96; x99; (Int.add x98 x72); x75; x78; x81; x84; x87; x90; x93].

(* fe_mul_121666_impl (in2 = 121666, 0, ..., 0) *)
Definition fe_mul121666_m (f: list int) : list int :=
  let x20 := Znth 9 f in
  let x21 := Znth 8 f in
  let x19 := Znth 7 f in
  let x17 := Znth 6 f in
  let x15 := Znth 5 f in
  let x13 := Znth 4 f in
  let x11 := Znth 3 f in
  let x9 := Znth 2 f in
  let x7 := Znth 1 f in
  let x5 := Znth 0 f in
  let x38 := Int.repr 0 in
  let x39 := Int.repr 0 in
  let x37 := Int.repr 0 in
  let x35 := Int.repr 0 in
  let x33 := Int.repr 0 in
  let x31 := Int.repr 0 in
  let x29 := Int.repr 0 in
  let x27 := Int.repr 0 in
  let x25 := Int.repr 0 in
  let x23 := Int.repr 121666 in
  let x40 := (Int64.mul (u64 x23) (u64 x5)) in
  let x41 := (Int64.add (Int64.mul (u64 x23) (u64 x7)) (Int64.mul (u64 x25) (u64 x5))) in
  let x42 := (Int64.add (Int64.add (Int64.mul (u64 (Int.mul (Int.repr 2) x25)) (u64 x7)) (Int64.mul (u64 x23) (u64 x9))) (Int64.mul (u64 x27) (u64 x5))) in
  let x43 := (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x25) (u64 x9)) (Int64.mul (u64 x27) (u64 x7))) (Int64.mul (u64 x23) (u64 x11))) (Int64.mul (u64 x29) (u64 x5))) in
  let x44 := (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x27) (u64 x9)) (Int64.mul (Int64.repr 2) (Int64.add (Int64.mul (u64 x25) (u64 x11)) (Int64.mul (u64 x29) (u64 x7))))) (Int64.mul (u64 x23) (u64 x13))) (Int64.mul (u64 x31) (u64 x5))) in
  let x45 := (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x27) (u64 x11)) (Int64.mul (u64 x29) (u64 x9))) (Int64.mul (u64 x25) (u64 x13))) (Int64.mul (u64 x31) (u64 x7))) (Int64.mul (u64 x23) (u64 x15))) (Int64.mul (u64 x33) (u64 x5))) in
  let x46 := (Int64.add (Int64.add (Int64.add (Int64.add (Int64.mul (Int64.repr 2) (Int64.add (Int64.add (Int64.mul (u64 x29) (u64 x11)) (Int64.mul (u64 x25) (u64 x15))) (Int64.mul (u64 x33) (u64 x7)))) (Int64.mul (u64 x27) (u64 x13))) (Int64.mul (u64 x31) (u64 x9))) (Int64.mul (u64 x23) (u64 x17))) (Int64.mul (u64 x35) (u64 x5))) in
  let x47 := (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x29) (u64 x13)) (Int64.mul (u64 x31) (u64 x11))) (Int64.mul (u64 x27) (u64 x15))) (Int64.mul (u64 x33) (u64 x9))) (Int64.mul (u64 x25) (u64 x17))) (Int64.mul (u64 x35) (u64 x7))) (Int64.mul (u64 x23) (u64 x19))) (Int64.mul (u64 x37) (u64 x5))) in
  let x48 := (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x31) (u64 x13)) (Int64.mul (Int64.repr 2) (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x29) (u64 x15)) (Int64.mul (u64 x33) (u64 x11))) (Int64.mul (u64 x25) (u64 x19))) (Int64.mul (u64 x37) (u64 x7))))) (Int64.mul (u64 x27) (u64 x17))) (Int64.mul (u64 x35) (u64 x9))) (Int64.mul (u64 x23) (u64 x21))) (Int64.mul (u64 x39) (u64 x5))) in
  let x49 := (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x31) (u64 x15)) (Int64.mul (u64 x33) (u64 x13))) (Int64.mul (u64 x29) (u64 x17))) (Int64.mul (u64 x35) (u64 x11))) (Int64.mul (u64 x27) (u64 x19))) (Int64.mul (u64 x37) (u64 x9))) (Int64.mul (u64 x25) (u64 x21))) (Int64.mul (u64 x39) (u64 x7))) (Int64.mul (u64 x23) (u64 x20))) (Int64.mul (u64 x38) (u64 x5))) in
  let x50 := (Int64.add (Int64.add (Int64.add (Int64.add (Int64.mul (Int64.repr 2) (Int64.add (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x33) (u64 x15)) (Int64.mul (u64 x29) (u64 x19))) (Int64.mul (u64 x37) (u64 x11))) (Int64.mul (u64 x25) (u64 x20))) (Int64.mul (u64 x38) (u64 x7)))) (Int64.mul (u64 x31) (u64 x17))) (Int64.mul (u64 x35) (u64 x13))) (Int64.mul (u64 x27) (u64 x21))) (Int64.mul (u64 x39) (u64 x9))) in
  let x51 := (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x33) (u64 x17)) (Int64.mul (u64 x35) (u64 x15))) (Int64.mul (u64 x31) (u64 x19))) (Int64.mul (u64 x37) (u64 x13))) (Int64.mul (u64 x29) (u64 x21))) (Int64.mul (u64 x39) (u64 x11))) (Int64.mul (u64 x27) (u64 x20))) (Int64.mul (u64 x38) (u64 x9))) in
  let x52 := (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x35) (u64 x17)) (Int64.mul (Int64.repr 2) (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x33) (u64 x19)) (Int64.mul (u64 x37) (u64 x15))) (Int64.mul (u64 x29) (u64 x20))) (Int64.mul (u64 x38) (u64 x11))))) (Int64.mul (u64 x31) (u64 x21))) (Int64.mul (u64 x39) (u64 x13))) in
  let x53 := (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x35) (u64 x19)) (Int64.mul (u64 x37) (u64 x17))) (Int64.mul (u64 x33) (u64 x21))) (Int64.mul (u64 x39) (u64 x15))) (Int64.mul (u64 x31) (u64 x20))) (Int64.mul (u64 x38) (u64 x13))) in
  let x54 := (Int64.add (Int64.add (Int64.mul (Int64.repr 2) (Int64.add (Int64.add (Int64.mul (u64 x37) (u64 x19)) (Int64.mul (u64 x33) (u64 x20))) (Int64.mul (u64 x38) (u64 x15)))) (Int64.mul (u64 x35) (u64 x21))) (Int64.mul (u64 x39) (u64 x17))) in
  let x55 := (Int64.add (Int64.add (Int64.add (Int64.mul (u64 x37) (u64 x21)) (Int64.mul (u64 x39) (u64 x19))) (Int64.mul (u64 x35) (u64 x20))) (Int64.mul (u64 x38) (u64 x17))) in
  let x56 := (Int64.add (Int64.mul (u64 x39) (u64 x21)) (Int64.mul (Int64.repr 2) (Int64.add (Int64.mul (u64 x37) (u64 x20)) (Int64.mul (u64 x38) (u64 x19))))) in
  let x57 := (Int64.add (Int64.mul (u64 x39) (u64 x20)) (Int64.mul (u64 x38) (u64 x21))) in
  let x58 := (Int64.mul (u64 (Int.mul (Int.repr 2) x38)) (u64 x20)) in
  let x59 := (Int64.add x48 (Int64.shl x58 (Int64.repr 4))) in
  let x60 := (Int64.add x59 (Int64.shl x58 (Int64.repr 1))) in
  let x61 := (Int64.add x60 x58) in
  let x62 := (Int64.add x47 (Int64.shl x57 (Int64.repr 4))) in
  let x63 := (Int64.add x62 (Int64.shl x57 (Int64.repr 1))) in
  let x64 := (Int64.add x63 x57) in
  let x65 := (Int64.add x46 (Int64.shl x56 (Int64.repr 4))) in
  let x66 := (Int64.add x65 (Int64.shl x56 (Int64.repr 1))) in
  let x67 := (Int64.add x66 x56) in
  let x68 := (Int64.add x45 (Int64.shl x55 (Int64.repr 4))) in
  let x69 := (Int64.add x68 (Int64.shl x55 (Int64.repr 1))) in
  let x70 := (Int64.add x69 x55) in
  let x71 := (Int64.add x44 (Int64.shl x54 (Int64.repr 4))) in
  let x72 := (Int64.add x71 (Int64.shl x54 (Int64.repr 1))) in
  let x73 := (Int64.add x72 x54) in
  let x74 := (Int64.add x43 (Int64.shl x53 (Int64.repr 4))) in
  let x75 := (Int64.add x74 (Int64.shl x53 (Int64.repr 1))) in
  let x76 := (Int64.add x75 x53) in
  let x77 := (Int64.add x42 (Int64.shl x52 (Int64.repr 4))) in
  let x78 := (Int64.add x77 (Int64.shl x52 (Int64.repr 1))) in
  let x79 := (Int64.add x78 x52) in
  let x80 := (Int64.add x41 (Int64.shl x51 (Int64.repr 4))) in
  let x81 := (Int64.add x80 (Int64.shl x51 (Int64.repr 1))) in
  let x82 := (Int64.add x81 x51) in
  let x83 := (Int64.add x40 (Int64.shl x50 (Int64.repr 4))) in
  let x84 := (Int64.add x83 (Int64.shl x50 (Int64.repr 1))) in
  let x85 := (Int64.add x84 x50) in
  let x86 := (Int64.shru x85 (Int64.repr 26)) in
  let x87 := (Int.and (lo x85) (Int.repr 67108863)) in
  let x88 := (Int64.add x86 x82) in
  let x89 := (Int64.shru x88 (Int64.repr 25)) in
  let x90 := (Int.and (lo x88) (Int.repr 33554431)) in
  let x91 := (Int64.add x89 x79) in
  let x92 := (Int64.shru x91 (Int64.repr 26)) in
  let x93 := (Int.and (lo x91) (Int.repr 67108863)) in
  let x94 := (Int64.add x92 x76) in
  let x95 := (Int64.shru x94 (Int64.repr 25)) in
  let x96 := (Int.and (lo x94) (Int.repr 33554431)) in
  let x97 := (Int64.add x95 x73) in
  let x98 := (Int64.shru x97 (Int64.repr 26)) in
  let x99 := (Int.and (lo x97) (Int.repr 67108863)) in
  let x100 := (Int64.add x98 x70) in
  let x101 := (Int64.shru x100 (Int64.repr 25)) in
  let x102 := (Int.and (lo x100) (Int.repr 33554431)) in
  let x103 := (Int64.add x101 x67) in
  let x104 := (Int64.shru x103 (Int64.repr 26)) in
  let x105 := (Int.and (lo x103) (Int.repr 67108863)) in
  let x106 := (Int64.add x104 x64) in
  let x107 := (Int64.shru x106 (Int64.repr 25)) in
  let x108 := (Int.and (lo x106) (Int.repr 33554431)) in
  let x109 := (Int64.add x107 x61) in
  let x110 := (Int64.shru x109 (Int64.repr 26)) in
  let x111 := (Int.and (lo x109) (Int.repr 67108863)) in
  let x112 := (Int64.add x110 x49) in
  let x113 := (Int64.shru x112 (Int64.repr 25)) in
  let x114 := (Int.and (lo x112) (Int.repr 33554431)) in
  let x115 := (Int64.add (u64 x87) (Int64.mul (Int64.repr 19) x113)) in
  let x116 := (lo (Int64.shru x115 (Int64.repr 26))) in
  let x117 := (Int.and (lo x115) (Int.repr 67108863)) in
  let x118 := (Int.add x116 x90) in
  let x119 := (Int.shru x118 (Int.repr 25)) in
  let x120 := (Int.and x118 (Int.repr 33554431)) in
  [x117; x120; (Int.add x119 x93); x96; x99; x102; x105; x108; x111; x114].

(* fe_cswap(f, g, b): b := 0 - b; x := (f[i] ^ g[i]) & b; f[i] ^= x; g[i] ^= x *)
Definition cswap_x (f g: list int) (m: int) (i: Z) : int := Int.and (Int.xor (Znth i f) (Znth i g)) m.
Definition fe_cswap_m (f g: list int) (b: int) : list int * list int :=
  let m := Int.sub Int.zero b in
  (map (fun i => Int.xor (Znth i f) (cswap_x f g m i)) (upto 10),
   map (fun i => Int.xor (Znth i g) (cswap_x f g m i)) (upto 10)).

(* n more squarings: the loops `for (i = 1; i < n + 1; ++i) fe_sq_tt(&t, &t);` *)
Definition fe_sqn_m (n: nat) (f: list int) : list int := Nat.iter n fe_sqr_m f.

(* fe_loose_invert: z^(p-2), the C sequence of squarings and multiplications *)
Definition fe_loose_invert_m (z: list int) : list int :=
  let t0 := fe_sqr_m z in
  let t1 := fe_sqr_m t0 in
  let t1 := fe_sqn_m 1 t1 in
  let t1 := fe_mul_m z t1 in
  let t0 := fe_mul_m t0 t1 in
  let t2 := fe_sqr_m t0 in
  let t1 := fe_mul_m t1 t2 in
  let t2 := fe_sqr_m t1 in
  let t2 := fe_sqn_m 4 t2 in
  let t1 := fe_mul_m t2 t1 in
  let t2 := fe_sqr_m t1 in
  let t2 := fe_sqn_m 9 t2 in
  let t2 := fe_mul_m t2 t1 in
  let t3 := fe_sqr_m t2 in
  let t3 := fe_sqn_m 19 t3 in
  let t2 := fe_mul_m t3 t2 in
  let t2 := fe_sqr_m t2 in
  let t2 := fe_sqn_m 9 t2 in
  let t1 := fe_mul_m t2 t1 in
  let t2 := fe_sqr_m t1 in
  let t2 := fe_sqn_m 49 t2 in
  let t2 := fe_mul_m t2 t1 in
  let t3 := fe_sqr_m t2 in
  let t3 := fe_sqn_m 99 t3 in
  let t2 := fe_mul_m t3 t2 in
  let t2 := fe_sqr_m t2 in
  let t2 := fe_sqn_m 49 t2 in
  let t1 := fe_mul_m t2 t1 in
  let t1 := fe_sqr_m t1 in
  let t1 := fe_sqn_m 4 t1 in
  fe_mul_m t1 t0.

(* fe_invert: fe_copy_lt then fe_loose_invert *)
Definition fe_invert_m (z: list int) : list int := fe_loose_invert_m z.

(* ------------------------------------------------------------------ *)
(* the Montgomery ladder of curve25519_generic                         *)
(* ------------------------------------------------------------------ *)

(* the loop state before the test: x2, z2, x3, z3, swap *)
Record ladder_state := mk_ls { ls_x2: list int; ls_z2: list int; ls_x3: list int; ls_z3: list int;
                               ls_swap: int }.

(* unsigned b = 1 & (e[pos / 8] >> (pos & 7)); (int arithmetic, e[.] promoted to int) *)
Definition ladder_bit (e: list byte) (pos: Z) : int :=
  Int.and Int.one (Int.shr (Int.repr (Byte.unsigned (Znth (pos / 8) e))) (Int.and (Int.repr pos) (Int.repr 7))).

(* one iteration of the loop body at position pos *)
Definition ladder_step (e: list byte) (x1: list int) (pos: Z) (st: ladder_state) : ladder_state :=
  let b := ladder_bit e pos in
  let swap := Int.xor (ls_swap st) b in
  let xs := fe_cswap_m (ls_x2 st) (ls_x3 st) swap in
  let zs := fe_cswap_m (ls_z2 st) (ls_z3 st) swap in
  let x2 := fst xs in let x3 := snd xs in let z2 := fst zs in let z3 := snd zs in
  let swap := b in
  let tmp0l := fe_sub_m x3 z3 in
  let tmp1l := fe_sub_m x2 z2 in
  let x2l := fe_add_m x2 z2 in
  let z2l := fe_add_m x3 z3 in
  let z3 := fe_mul_m tmp0l x2l in
  let z2 := fe_mul_m z2l tmp1l in
  let tmp0 := fe_sqr_m tmp1l in
  let tmp1 := fe_sqr_m x2l in
  let x3l := fe_add_m z3 z2 in
  let z2l := fe_sub_m z3 z2 in
  let x2 := fe_mul_m tmp1 tmp0 in
  let tmp1l := fe_sub_m tmp1 tmp0 in
  let z2 := fe_sqr_m z2l in
  let z3 := fe_mul121666_m tmp1l in
  let x3 := fe_sqr_m x3l in
  let tmp0l := fe_add_m tmp0 z3 in
  let z3 := fe_mul_m x1 z2 in
  let z2 := fe_mul_m tmp1l tmp0l in
  mk_ls x2 z2 x3 z3 swap.

(* the state after k iterations (positions 254, 253, ..., 255 - k) *)
Fixpoint ladder_steps (e: list byte) (x1: list int) (k: nat) (st: ladder_state) : ladder_state :=
  match k with
  | O => st
  | S k' => ladder_step e x1 (254 - Z.of_nat k') (ladder_steps e x1 k' st)
  end.

Definition ladder_init (x1: list int) : ladder_state := mk_ls fe1_m fe0_m x1 fe1_m Int.zero.

(* curve25519_generic(out, scalar, point) *)
Definition x25519_m (scalar point: list byte) : list byte :=
  let e := clamp scalar in
  let x1 := fe_frombytes_m point in
  let st := ladder_steps e x1 255 (ladder_init x1) in
  let x2 := fst (fe_cswap_m (ls_x2 st) (ls_x3 st) (ls_swap st)) in
  let z2 := fst (fe_cswap_m (ls_z2 st) (ls_z3 st) (ls_swap st)) in
  let z2 := fe_invert_m z2 in
  let x2 := fe_mul_m x2 z2 in
  fe_tobytes_m x2.

Lemma fe_tobytes_m_length : forall f, Zlength (fe_tobytes_m f) = 32.
Proof. intros. reflexivity. Qed.

Lemma x25519_m_length : forall s p, Zlength (x25519_m s p) = 32.
Proof.
  intros. apply fe_tobytes_m_length.
Qed.

(* RFC 7748 5.2, first test vector: a sanity check of the transliteration.  Checked when the model was written:
   Eval vm_compute in (list_eq_dec Byte.eq_dec (x25519_m rfc7748_scalar rfc7748_point) rfc7748_out) = left _ *)
Definition hexbytes (l: list Z) : list byte := map Byte.repr l.
Definition rfc7748_scalar := hexbytes
  [0xa5;0x46;0xe3;0x6b;0xf0;0x52;0x7c;0x9d;0x3b;0x16;0x15;0x4b;0x82;0x46;0x5e;0xdd;
   0x62;0x14;0x4c;0x0a;0xc1;0xfc;0x5a;0x18;0x50;0x6a;0x22;0x44;0xba;0x44;0x9a;0xc4].
Definition rfc7748_point := hexbytes
  [0xe6;0xdb;0x68;0x67;0x58;0x30;0x30;0xdb;0x35;0x94;0xc1;0xa4;0x24;0xb1;0x5f;0x7c;
   0x72;0x66;0x24;0xec;0x26;0xb3;0x35;0x3b;0x10;0xa9;0x03;0xa6;0xd0;0xab;0x1c;0x4c].
Definition rfc7748_out := hexbytes
  [0xc3;0xda;0x55;0x37;0x9d;0xe9;0xc6;0x90;0x8e;0x94;0xea;0x4d;0xf2;0x8d;0x08;0x4f;
   0x32;0xec;0xcf;0x03;0x49;0x1c;0x71;0xf7;0x54;0xb4;0x07;0x55;0x77;0xa2;0x85;0x52].
