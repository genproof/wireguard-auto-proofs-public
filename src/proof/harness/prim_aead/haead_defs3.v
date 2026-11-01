(* law prim_aead: the plain-Coq definitions of the harness piece beyond hrp1305_math3.v. *)
Require Import VST.floyd.proofauto.
Require Export WgNoise.proof.aead.aead_model.
Require Export WgNoise.proof.harness.hrp1305_math3.
Require Export WgNoise.proof.prims.prim_api.

Local Open Scope Z_scope.

(* rp_padded(p, in, len): the whole 16-byte blocks of buf, then the rest (if any) zero padded to 16 bytes:
     while (len - pos >= 16) { rp_block(p, in + pos); pos += 16; }
     if (len - pos > 0) { bytes_set(b, 0, 16); bytes_copy(b, in + pos, len - pos); rp_block(p, b); } *)
Definition haead_padded (r h: list int) (buf: list byte) : list int :=
  let nb := Zlength buf / 16 in
  let h1 := hrp_loop (fun h k => hrp_block r h (sublist (16 * k) (16 * k + 16) buf)) nb h in
  if Z.eq_dec (Zlength buf - 16 * nb) 0 then h1
  else hrp_block r h1 (sublist (16 * nb) (Zlength buf) buf ++ Zrepeat Byte.zero (16 - (Zlength buf - 16 * nb))).

(* the Poly1305 state of ref_aead_tag after its last block, from the 64-byte block 0 `blk` *)
Definition haead_tag_h (blk ad ct: list byte) : list int :=
  let r := hrp_init_r blk in
  hrp_block r (haead_padded r (haead_padded r hrp_zero17 ad) ct)
    (le64_bytes (Zlength ad) ++ le64_bytes (Zlength ct)).

(* bytes l stored at offset i of the buffer contents (le32_store, le64_store) *)
Definition haead_splice (i: Z) (l: list byte) (contents: list val) : list val :=
  sublist 0 i contents ++ map Vubyte l ++ sublist (i + Zlength l) (Zlength contents) contents.

(* ---------------------------------------------------------------------- *)
(* hypotheses of the body lemmas: the
   facts of hrp1305_math3.v, the model facts of haead_model3.v and prim_api's aead_props (proved by
   aead_models_props3.v); haead_piece3.v discharges them. *)
(* ---------------------------------------------------------------------- *)

(* the statements of hrp1305_math3.v *)
Definition haead_hrp_facts : Prop :=
  (forall h c, Zlength h = 17 -> Zlength (hrp_add h c) = 17) /\
  (forall key, Zlength key >= 16 -> Zlength (hrp_init_r key) = 17) /\
  (forall r h c, Zlength h = 17 -> Zlength (hrp_mul r h c) = 17) /\
  (forall h sk, Zlength h = 17 -> Zlength (hrp_final_h h sk) = 17) /\
  (forall h sk, Zlength h = 17 -> Zlength (hrp_final_out h sk) = 16) /\
  (hrp_inv hrp_zero17 /\ hrp_val hrp_zero17 = 0) /\
  (forall key, 16 <= Zlength key ->
     Zlength (hrp_init_r key) = 17 /\ Forall (fun w => Int.unsigned w <= 255) (hrp_init_r key) /\
     hrp_val (hrp_init_r key) = p1305_r key) /\
  (forall m, Zlength m = 16 -> hrp_cblock (hrp_block_c m) /\ hrp_val (hrp_block_c m) = le_Z m + 2 ^ 128) /\
  (forall key h c, 16 <= Zlength key -> hrp_inv h -> hrp_cblock c ->
     hrp_inv (hrp_mul (hrp_init_r key) h c) /\
     hrp_val (hrp_mul (hrp_init_r key) h c) mod p1305_p = (hrp_val h + hrp_val c) * p1305_r key mod p1305_p) /\
  (forall h sk, hrp_inv h -> Zlength sk = 16 ->
     hrp_final_out h sk = le_bytes 16 ((hrp_val h mod p1305_p + le_Z sk) mod 2 ^ 128)).

(* the statements of haead_model3.v (see there) *)
Definition haead_facts : Prop :=
  (forall key n ctr, Zlength key = 32 -> 0 <= n <= Int64.max_unsigned ->
     chacha_consts ++ le32_words 8 key ++ [ctr; Int.zero; Int.repr n; Int.repr (Z.shiftr n 32)] =
     chacha_advance (aead_st key n) (Int.unsigned ctr)) /\
  (forall st m, Zlength st = 16 -> Zlength (chacha_xor 10 st m) = Zlength m) /\
  (forall st m b, Zlength st = 16 -> 0 <= b -> 64 * b < Zlength m ->
     sublist (64 * b) (Z.min (64 * b + 64) (Zlength m)) (chacha_xor 10 st m) =
     xor_bytes (sublist (64 * b) (Z.min (64 * b + 64) (Zlength m)) m)
       (chacha_block_bytes 10 (chacha_advance st b))) /\
  (forall r h buf, Zlength h = 17 -> Zlength (haead_padded r h buf) = 17) /\
  (forall blk ad ct, 32 <= Zlength blk ->
     hrp_final_out (haead_tag_h blk ad ct) (hrp_init_s blk) = poly1305_tag (sublist 0 32 blk) (aead_mac_data ad ct)) /\
  (forall bs, Zlength bs = 8 -> 0 <= le_Z bs <= Int64.max_unsigned) /\
  (forall key nonce, Zlength key = 32 -> Zlength nonce = 24 ->
     aead_st (words_bytes (hchacha_words 10 (chacha_init_st (le32_words 8 key) (sublist 0 16 nonce))))
       (le_Z (sublist 16 24 nonce)) = xaead_st key nonce).

(* the hypothesis of every body lemma of the harness piece *)
Definition haead_hyps : Prop :=
  haead_hrp_facts /\ haead_facts /\ aead_props aead_enc aead_dec /\ xaead_props xaead_enc xaead_dec.
