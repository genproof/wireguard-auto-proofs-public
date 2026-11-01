(* The Coq model of BLAKE2s (RFC 7693), shaped after the kernel's lib/crypto/blake2s.c.

   Owner: law prim_blake2s (src/proof/blake2s/).  Shared by every law: the protocol laws only use
   `blake2s key outlen msg` (the digest) through the specifications of src/proof/blake2s/spec.v.

   - words are CompCert `int`s, bytes `byte`s, buffers `list byte`;
   - b2s_G / b2s_round / b2s_compress follow the kernel's order of operations exactly
     (`a += b + m[..]` is `a + (b + m)`);
   - the byte counter t is a Z (>= 0): the context stores Int.repr t and Int.repr (t / 2^32), i.e.
     t mod 2^64 in two words, as the kernel does;
   - the stream: the key padded to one block (if any key) followed by the message; every block but
     the last is compressed with the count of bytes so far, the last one (zero padded, possibly
     empty) with the total and the final flag.  `blake2s key outlen msg` is the digest. *)
Require Import VST.floyd.proofauto.
Require Export WgNoise.proof.blake2s.spec_shared.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Constants                                                               *)
(* ---------------------------------------------------------------------- *)

Definition b2s_IV : list int := map Int.repr
  [1779033703; 3144134277; 1013904242; 2773480762;
   1359893119; 2600822924; 528734635; 1541459225].

Definition b2s_sigma : list (list Z) :=
  [ [ 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15 ];
    [ 14; 10; 4; 8; 9; 15; 13; 6; 1; 12; 0; 2; 11; 7; 5; 3 ];
    [ 11; 8; 12; 0; 5; 2; 15; 13; 10; 14; 3; 6; 7; 1; 9; 4 ];
    [ 7; 9; 3; 1; 13; 12; 11; 14; 2; 6; 5; 10; 4; 0; 15; 8 ];
    [ 9; 0; 5; 7; 2; 4; 10; 15; 14; 1; 11; 12; 6; 8; 3; 13 ];
    [ 2; 12; 6; 10; 0; 11; 8; 3; 4; 13; 7; 5; 15; 14; 1; 9 ];
    [ 12; 5; 1; 15; 14; 13; 4; 10; 0; 7; 6; 3; 9; 2; 8; 11 ];
    [ 13; 11; 7; 14; 12; 1; 3; 9; 5; 0; 15; 4; 8; 6; 2; 10 ];
    [ 6; 15; 14; 9; 11; 3; 0; 8; 12; 2; 13; 7; 1; 4; 10; 5 ];
    [ 10; 2; 8; 4; 7; 6; 1; 5; 15; 11; 9; 14; 3; 12; 13; 0 ] ].

(* ---------------------------------------------------------------------- *)
(* The compression function                                                *)
(* ---------------------------------------------------------------------- *)

(* G on the 16-word working vector v, as the kernel's macro G (sequential updates). *)
Definition b2s_G (v: list int) (a b c d: Z) (x y: int) : list int :=
  let v := upd_Znth a v (Int.add (Znth a v) (Int.add (Znth b v) x)) in
  let v := upd_Znth d v (Int.ror (Int.xor (Znth d v) (Znth a v)) (Int.repr 16)) in
  let v := upd_Znth c v (Int.add (Znth c v) (Znth d v)) in
  let v := upd_Znth b v (Int.ror (Int.xor (Znth b v) (Znth c v)) (Int.repr 12)) in
  let v := upd_Znth a v (Int.add (Znth a v) (Int.add (Znth b v) y)) in
  let v := upd_Znth d v (Int.ror (Int.xor (Znth d v) (Znth a v)) (Int.repr 8)) in
  let v := upd_Znth c v (Int.add (Znth c v) (Znth d v)) in
  upd_Znth b v (Int.ror (Int.xor (Znth b v) (Znth c v)) (Int.repr 7)).

(* one round with the permutation s (a row of b2s_sigma) of the message words m *)
Definition b2s_round (m: list int) (v: list int) (s: list Z) : list int :=
  let x i := Znth (Znth i s) m in
  let v := b2s_G v 0 4 8 12 (x 0) (x 1) in
  let v := b2s_G v 1 5 9 13 (x 2) (x 3) in
  let v := b2s_G v 2 6 10 14 (x 4) (x 5) in
  let v := b2s_G v 3 7 11 15 (x 6) (x 7) in
  let v := b2s_G v 0 5 10 15 (x 8) (x 9) in
  let v := b2s_G v 1 6 11 12 (x 10) (x 11) in
  let v := b2s_G v 2 7 8 13 (x 12) (x 13) in
  b2s_G v 3 4 9 14 (x 14) (x 15).

(* the first r rounds *)
Definition b2s_rounds (m: list int) (v: list int) (r: Z) : list int :=
  fold_left (b2s_round m) (sublist 0 r b2s_sigma) v.

(* the initial working vector *)
Definition b2s_v0 (h: list int) (t0 t1 f0 f1: int) : list int :=
  h ++ [Znth 0 b2s_IV; Znth 1 b2s_IV; Znth 2 b2s_IV; Znth 3 b2s_IV;
        Int.xor (Znth 4 b2s_IV) t0; Int.xor (Znth 5 b2s_IV) t1;
        Int.xor (Znth 6 b2s_IV) f0; Int.xor (Znth 7 b2s_IV) f1].

(* the feed-forward: h[i] ^= v[i] ^ v[i + 8] *)
Definition b2s_feed (h v: list int) : list int :=
  map (fun i => Int.xor (Znth i h) (Int.xor (Znth i v) (Znth (i + 8) v))) (upto 8).

(* F(h, m, t, f): h 8 words, m 16 words, (t0, t1) the counter words, (f0, f1) the flags *)
Definition b2s_compress (h m: list int) (t0 t1 f0 f1: int) : list int :=
  b2s_feed h (b2s_rounds m (b2s_v0 h t0 t1 f0 f1) 10).

(* the i-th little-endian word of a byte buffer (le32_at: spec_shared.v, as get_unaligned_le32) *)
Definition b2s_word (bs: list byte) (i: Z) : int := le32_at bs (4 * i).

(* the 16 message words of a 64-byte block *)
Definition b2s_words (blk: list byte) : list int := map (b2s_word blk) (upto 16).

(* the counter words of t *)
Definition b2s_t0 (t: Z) : int := Int.repr t.
Definition b2s_t1 (t: Z) : int := Int.repr (t / Int.modulus).

(* compress one 64-byte block with counter t and final flag word f0 (f1 is always 0) *)
Definition b2s_compress_block (h: list int) (blk: list byte) (t: Z) (f0: int) : list int :=
  b2s_compress h (b2s_words blk) (b2s_t0 t) (b2s_t1 t) f0 Int.zero.

(* blake2s_compress_generic(ctx, data, n, inc): n blocks of data, the counter advanced by inc before
   each one; f0 is the context's flag word.  Result: the new h (the counter becomes t + n * inc). *)
Fixpoint b2s_compress_n (n: nat) (h: list int) (t: Z) (f0: int) (inc: Z) (data: list byte)
  : list int :=
  match n with
  | O => h
  | S n' => b2s_compress_n n' (b2s_compress_block h (sublist 0 64 data) (t + inc) f0)
                           (t + inc) f0 inc (sublist 64 (Zlength data) data)
  end.

(* the non-final blocks of a stream (a multiple of 64 bytes), counter starting at t *)
Definition b2s_blocks (h: list int) (t: Z) (data: list byte) : list int :=
  b2s_compress_n (Z.to_nat (Zlength data / 64)) h t Int.zero 64 data.

(* ---------------------------------------------------------------------- *)
(* The hash                                                                *)
(* ---------------------------------------------------------------------- *)

(* h0: IV with the parameter block (digest length, key length, fanout 1, depth 1) *)
Definition b2s_h0 (keylen outlen: Z) : list int :=
  upd_Znth 0 b2s_IV (Int.xor (Znth 0 b2s_IV) (Int.repr (16842752 + keylen * 256 + outlen))).

(* the key padded to a block, if any *)
Definition b2s_keyblock (key: list byte) : list byte :=
  if Zlength key =? 0 then [] else key ++ Zrepeat Byte.zero (64 - Zlength key).

(* the bytes hashed: key block ++ message *)
Definition b2s_stream (key msg: list byte) : list byte := b2s_keyblock key ++ msg.

(* number of blocks of the stream compressed as non-final: all but the last (nonempty) block *)
Definition b2s_nfull (s: list byte) : Z :=
  if Zlength s =? 0 then 0 else (Zlength s - 1) / 64.

(* the digest bytes: byte i of the little-endian words h *)
Definition b2s_out (outlen: Z) (h: list int) : list byte :=
  map (fun i => Byte.repr (Int.unsigned (Int.shru (Znth (i / 4) h) (Int.repr (8 * (i mod 4))))))
      (upto (Z.to_nat outlen)).

(* h after the non-final blocks of stream s *)
Definition b2s_h_nonfinal (keylen outlen: Z) (s: list byte) : list int :=
  b2s_blocks (b2s_h0 keylen outlen) 0 (sublist 0 (64 * b2s_nfull s) s).

(* the last block (unpadded: 0..64 bytes) *)
Definition b2s_lastblock (s: list byte) : list byte :=
  sublist (64 * b2s_nfull s) (Zlength s) s.

Definition b2s_digest_stream (keylen outlen: Z) (s: list byte) : list byte :=
  let last := b2s_lastblock s in
  b2s_out outlen
    (b2s_compress_block (b2s_h_nonfinal keylen outlen s)
       (last ++ Zrepeat Byte.zero (64 - Zlength last)) (Zlength s) Int.mone).

(* BLAKE2s-outlen(key, msg): 1 <= outlen <= 32, 0 <= |key| <= 32 *)
Definition blake2s (key: list byte) (outlen: Z) (msg: list byte) : list byte :=
  b2s_digest_stream (Zlength key) outlen (b2s_stream key msg).

(* ---------------------------------------------------------------------- *)
(* Tests (RFC 7693 Appendix B: BLAKE2s-256("abc"))                          *)
(* ---------------------------------------------------------------------- *)

Definition b2s_hexbytes (l: list Z) : list byte := map Byte.repr l.

Lemma b2s_test_abc :
  map Byte.unsigned (blake2s [] 32 (b2s_hexbytes [97; 98; 99])) =
  [80; 140; 94; 140; 50; 124; 20; 226; 225; 167; 43; 163; 78; 235; 69; 47;
                55; 69; 139; 32; 158; 214; 58; 41; 77; 153; 155; 76; 134; 103; 89; 130].
Proof. vm_compute. reflexivity. Qed.


Lemma b2s_test_keyed_multi :
  map Byte.unsigned (blake2s (b2s_hexbytes [0; 1; 2; 3; 4; 5; 6]) 16 (b2s_hexbytes [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39; 40; 41; 42; 43; 44; 45; 46; 47; 48; 49; 50; 51; 52; 53; 54; 55; 56; 57; 58; 59; 60; 61; 62; 63; 64; 65; 66; 67; 68; 69; 70; 71; 72; 73; 74; 75; 76; 77; 78; 79; 80; 81; 82; 83; 84; 85; 86; 87; 88; 89; 90; 91; 92; 93; 94; 95; 96; 97; 98; 99; 100; 101; 102; 103; 104; 105; 106; 107; 108; 109; 110; 111; 112; 113; 114; 115; 116; 117; 118; 119; 120; 121; 122; 123; 124; 125; 126; 127; 128; 129])) =
  [1; 86; 230; 254; 174; 44; 87; 162; 37; 200; 26; 209; 177; 187; 217; 89].
Proof. vm_compute. reflexivity. Qed.

Lemma b2s_test_empty :
  map Byte.unsigned (blake2s (b2s_hexbytes []) 32 (b2s_hexbytes [])) =
  [105; 33; 122; 48; 121; 144; 128; 148; 225; 17; 33; 208; 66; 53; 74; 124; 31; 85; 182; 72; 44; 161; 165; 30; 27; 37; 13; 253; 30; 208; 238; 249].
Proof. vm_compute. reflexivity. Qed.

Lemma b2s_test_keyed_empty :
  map Byte.unsigned (blake2s (b2s_hexbytes [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]) 32 (b2s_hexbytes [])) =
  [72; 168; 153; 125; 164; 7; 135; 107; 61; 121; 192; 217; 35; 37; 173; 59; 137; 203; 183; 84; 216; 106; 183; 26; 238; 4; 122; 211; 69; 253; 44; 73].
Proof. vm_compute. reflexivity. Qed.

Lemma b2s_test_block :
  map Byte.unsigned (blake2s (b2s_hexbytes [0; 1; 2]) 20 (b2s_hexbytes [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39; 40; 41; 42; 43; 44; 45; 46; 47; 48; 49; 50; 51; 52; 53; 54; 55; 56; 57; 58; 59; 60; 61; 62; 63])) =
  [166; 34; 239; 76; 93; 219; 81; 201; 195; 123; 238; 11; 128; 236; 117; 165; 150; 244; 103; 51].
Proof. vm_compute. reflexivity. Qed.

Lemma b2s_test_128 :
  map Byte.unsigned (blake2s (b2s_hexbytes []) 32 (b2s_hexbytes [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39; 40; 41; 42; 43; 44; 45; 46; 47; 48; 49; 50; 51; 52; 53; 54; 55; 56; 57; 58; 59; 60; 61; 62; 63; 64; 65; 66; 67; 68; 69; 70; 71; 72; 73; 74; 75; 76; 77; 78; 79; 80; 81; 82; 83; 84; 85; 86; 87; 88; 89; 90; 91; 92; 93; 94; 95; 96; 97; 98; 99; 100; 101; 102; 103; 104; 105; 106; 107; 108; 109; 110; 111; 112; 113; 114; 115; 116; 117; 118; 119; 120; 121; 122; 123; 124; 125; 126; 127])) =
  [31; 168; 119; 222; 103; 37; 157; 25; 134; 58; 42; 52; 188; 198; 150; 42; 43; 37; 252; 191; 92; 190; 205; 126; 222; 143; 31; 163; 102; 136; 167; 150].
Proof. vm_compute. reflexivity. Qed.
