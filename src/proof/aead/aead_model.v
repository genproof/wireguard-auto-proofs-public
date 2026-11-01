(* The functional model of the AEAD piece: ChaCha20 / HChaCha20 over 32-bit words
   (RFC 8439 2.3, the XChaCha draft), Poly1305 as the polynomial over Z mod 2^130 - 5 (RFC 8439 2.5), and
   the ChaCha20-Poly1305 / XChaCha20-Poly1305 constructions (RFC 8439 2.8) with the kernel's 64-bit nonce.

   Plain Coq (no separation logic).  The specifications (aead_spec.v) and the harness pieces of the laws
   prim_aead_u32 and prim_poly1305_bounded use these definitions. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.blake2s.spec_shared.   (* le32_at *)

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* bytes and words                                                         *)
(* ---------------------------------------------------------------------- *)

(* a word as 4 little-endian bytes (put_unaligned_le32) *)
Definition le32_bytes (w: int) : list byte :=
  [Byte.repr (Int.unsigned w); Byte.repr (Z.shiftr (Int.unsigned w) 8);
   Byte.repr (Z.shiftr (Int.unsigned w) 16); Byte.repr (Z.shiftr (Int.unsigned w) 24)].

(* words as bytes *)
Definition words_bytes (ws: list int) : list byte := concat (map le32_bytes ws).

(* the n little-endian bytes of z (mod 256^n) *)
Fixpoint le_bytes (n: nat) (z: Z) : list byte :=
  match n with O => [] | S k => Byte.repr z :: le_bytes k (z / 256) end.

(* a 64-bit value as 8 little-endian bytes (put_unaligned_le64) *)
Definition le64_bytes (z: Z) : list byte := le_bytes 8 z.

(* the little-endian number of a byte string *)
Fixpoint le_Z (bs: list byte) : Z :=
  match bs with [] => 0 | b :: t => Byte.unsigned b + 256 * le_Z t end.

(* the n little-endian words at the start of bs (chacha_load_key: n = 8) *)
Definition le32_words (n: nat) (bs: list byte) : list int :=
  map (fun i => le32_at bs (4 * i)) (map Z.of_nat (seq 0 n)).

(* byte-wise XOR, truncated to the shorter list *)
Definition xor_bytes (a b: list byte) : list byte :=
  map (fun xy => Byte.xor (fst xy) (snd xy)) (combine a b).

(* word-wise sum *)
Definition add_words (a b: list int) : list int :=
  map (fun xy => Int.add (fst xy) (snd xy)) (combine a b).

(* ---------------------------------------------------------------------- *)
(* ChaCha20                                                                *)
(* ---------------------------------------------------------------------- *)

(* the quarter round on words a b c d of the state (RFC 8439 2.2) *)
Definition chacha_qround (x: list int) (a b c d: Z) : list int :=
  let x := upd_Znth a x (Int.add (Znth a x) (Znth b x)) in
  let x := upd_Znth d x (Int.rol (Int.xor (Znth d x) (Znth a x)) (Int.repr 16)) in
  let x := upd_Znth c x (Int.add (Znth c x) (Znth d x)) in
  let x := upd_Znth b x (Int.rol (Int.xor (Znth b x) (Znth c x)) (Int.repr 12)) in
  let x := upd_Znth a x (Int.add (Znth a x) (Znth b x)) in
  let x := upd_Znth d x (Int.rol (Int.xor (Znth d x) (Znth a x)) (Int.repr 8)) in
  let x := upd_Znth c x (Int.add (Znth c x) (Znth d x)) in
  upd_Znth b x (Int.rol (Int.xor (Znth b x) (Znth c x)) (Int.repr 7)).

(* a column round and a diagonal round *)
Definition chacha_dround (x: list int) : list int :=
  let x := chacha_qround x 0 4 8 12 in
  let x := chacha_qround x 1 5 9 13 in
  let x := chacha_qround x 2 6 10 14 in
  let x := chacha_qround x 3 7 11 15 in
  let x := chacha_qround x 0 5 10 15 in
  let x := chacha_qround x 1 6 11 12 in
  let x := chacha_qround x 2 7 8 13 in
  chacha_qround x 3 4 9 14.

(* n double rounds (ChaCha20: 10) *)
Fixpoint chacha_rounds (n: nat) (x: list int) : list int :=
  match n with O => x | S k => chacha_rounds k (chacha_dround x) end.

(* the ChaCha block function: 64 bytes of keystream from the 16-word state *)
Definition chacha_block_words (n: nat) (st: list int) : list int := add_words (chacha_rounds n st) st.
Definition chacha_block_bytes (n: nat) (st: list int) : list byte := words_bytes (chacha_block_words n st).

(* the block counter (word 12) incremented by k *)
Definition chacha_advance (st: list int) (k: Z) : list int :=
  upd_Znth 12 st (Int.add (Znth 12 st) (Int.repr k)).

(* the keystream of nb blocks from st *)
Fixpoint chacha_stream (n: nat) (st: list int) (nb: nat) : list byte :=
  match nb with O => [] | S k => chacha_block_bytes n st ++ chacha_stream n (chacha_advance st 1) k end.

(* the number of blocks for len bytes *)
Definition chacha_nblocks (len: Z) : Z := (len + 63) / 64.

(* chacha_crypt: src XOR the keystream; the state then advances by chacha_nblocks |src| blocks *)
Definition chacha_xor (n: nat) (st: list int) (src: list byte) : list byte :=
  xor_bytes src (chacha_stream n st (Z.to_nat (chacha_nblocks (Zlength src)))).

(* HChaCha: the rounds without the final addition, words 0..3 and 12..15 *)
Definition hchacha_words (n: nat) (st: list int) : list int :=
  let x := chacha_rounds n st in sublist 0 4 x ++ sublist 12 16 x.

(* "expand 32-byte k" *)
Definition chacha_consts : list int :=
  [Int.repr 1634760805; Int.repr 857760878; Int.repr 2036477234; Int.repr 1797285236].

(* chacha_init(state, key words, iv): constants, key, the four iv words *)
Definition chacha_init_st (k: list int) (iv: list byte) : list int :=
  chacha_consts ++ k ++ [le32_at iv 0; le32_at iv 4; le32_at iv 8; le32_at iv 12].

(* ---------------------------------------------------------------------- *)
(* Poly1305                                                                *)
(* ---------------------------------------------------------------------- *)

Definition p1305_p : Z := 2 ^ 130 - 5.

(* r = le(key[0..16)) clamped, s = le(key[16..32)) *)
Definition p1305_r (key: list byte) : Z :=
  Z.land (le_Z (sublist 0 16 key)) 21267647620597763993911028882763415551.  (* 0x0ffffffc0ffffffc0ffffffc0fffffff *)
Definition p1305_s (key: list byte) : Z := le_Z (sublist 16 32 key).

(* one block of 1..16 bytes: acc := (acc + le(blk || 0x01)) * r mod p *)
Definition p1305_step (r: Z) (acc: Z) (blk: list byte) : Z :=
  (acc + le_Z blk + 2 ^ (8 * Zlength blk)) * r mod p1305_p.

(* the message cut into blocks of 16 bytes (the last one 1..16 bytes) *)
Definition p1305_blocks (msg: list byte) : list (list byte) :=
  map (fun i => sublist (16 * i) (16 * i + 16) msg) (map Z.of_nat (seq 0 (Z.to_nat ((Zlength msg + 15) / 16)))).

Definition p1305_acc (r: Z) (acc: Z) (msg: list byte) : Z := fold_left (p1305_step r) (p1305_blocks msg) acc.

(* the tag: (acc + s) mod 2^128, 16 bytes little-endian *)
Definition poly1305_tag (key: list byte) (msg: list byte) : list byte :=
  le_bytes 16 ((p1305_acc (p1305_r key) 0 msg + p1305_s key) mod 2 ^ 128).

(* the core (poly1305_core_blocks): whole 16-byte blocks, with 2^128 added iff hibit = 1 *)
Definition p1305_core_step (r: Z) (hibit: Z) (acc: Z) (blk: list byte) : Z :=
  (acc + le_Z blk + hibit * 2 ^ 128) * r mod p1305_p.

Definition p1305_core_blocks (r: Z) (hibit: Z) (acc: Z) (bs: list byte) : Z :=
  fold_left (p1305_core_step r hibit)
    (map (fun i => sublist (16 * i) (16 * i + 16) bs) (map Z.of_nat (seq 0 (Z.to_nat (Zlength bs / 16)))))
    acc.

(* ---------------------------------------------------------------------- *)
(* ChaCha20-Poly1305 (RFC 8439 2.8) and XChaCha20-Poly1305                  *)
(* ---------------------------------------------------------------------- *)

Definition pad16 (l: list byte) : list byte := Zrepeat Byte.zero ((16 - Zlength l mod 16) mod 16).

(* the data authenticated by Poly1305 *)
Definition aead_mac_data (ad ct: list byte) : list byte :=
  ad ++ pad16 ad ++ ct ++ pad16 ct ++ le64_bytes (Zlength ad) ++ le64_bytes (Zlength ct).

(* the one-time Poly1305 key: the first 32 bytes of block 0 *)
Definition aead_otk (st: list int) : list byte := sublist 0 32 (chacha_block_bytes 10 st).

(* from the initial ChaCha20 state (block counter 0) *)
Definition aead_enc_st (st: list int) (ad m: list byte) : list byte :=
  let ct := chacha_xor 10 (chacha_advance st 1) m in
  ct ++ poly1305_tag (aead_otk st) (aead_mac_data ad ct).

Definition aead_dec_st (st: list int) (ad c: list byte) : option (list byte) :=
  if Z_lt_dec (Zlength c) 16 then None
  else
    let ct := sublist 0 (Zlength c - 16) c in
    if list_eq_dec Byte.eq_dec (poly1305_tag (aead_otk st) (aead_mac_data ad ct))
         (sublist (Zlength c - 16) (Zlength c) c)
    then Some (chacha_xor 10 (chacha_advance st 1) ct)
    else None.

(* the kernel's iv: 64 zero bits (block counter and the first nonce word), then the 64-bit nonce *)
Definition aead_iv (nonce: Z) : list byte := Zrepeat Byte.zero 8 ++ le64_bytes nonce.

Definition aead_st (key: list byte) (nonce: Z) : list int := chacha_init_st (le32_words 8 key) (aead_iv nonce).

Definition aead_enc (key: list byte) (nonce: Z) (ad m: list byte) : list byte := aead_enc_st (aead_st key nonce) ad m.
Definition aead_dec (key: list byte) (nonce: Z) (ad c: list byte) : option (list byte) :=
  aead_dec_st (aead_st key nonce) ad c.

(* XChaCha: subkey = HChaCha20(key, nonce[0..16)), iv = 0^8 || nonce[16..24) *)
Definition xaead_subkey (key nonce: list byte) : list int :=
  hchacha_words 10 (chacha_init_st (le32_words 8 key) (sublist 0 16 nonce)).

Definition xaead_st (key nonce: list byte) : list int :=
  chacha_init_st (xaead_subkey key nonce) (Zrepeat Byte.zero 8 ++ sublist 16 24 nonce).

Definition xaead_enc (key nonce: list byte) (ad m: list byte) : list byte := aead_enc_st (xaead_st key nonce) ad m.
Definition xaead_dec (key nonce: list byte) (ad c: list byte) : option (list byte) :=
  aead_dec_st (xaead_st key nonce) ad c.
