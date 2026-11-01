(* Body proof(s) of the BLAKE2s piece: see blake2s_piece.v and b2s_prog.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.b2s_prog3.
Require WgNoise.blake2s.code.

#[local] Existing Instance Blake2s.CS.

(* ---------- ror32 ---------- *)

Lemma b2s_small_and31 (x: int) : Int.unsigned (Int.and x (Int.repr 31)) = Int.unsigned x mod 32.
Proof.
  replace (Int.repr 31) with (Int.sub (Int.repr 32) Int.one) by reflexivity.
  rewrite <- (Int.modu_and x (Int.repr 32) (Int.repr 5)) by reflexivity.
  unfold Int.modu. change (Int.unsigned (Int.repr 32)) with 32.
  pose proof (Z.mod_pos_bound (Int.unsigned x) 32 ltac:(lia)).
  rewrite Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma b2s_small_ror_mod (w s: int) : Int.ror w s = Int.ror w (Int.and s (Int.repr 31)).
Proof.
  unfold Int.ror. rewrite b2s_small_and31. change Int.zwordsize with 32.
  rewrite Zmod_mod. reflexivity.
Qed.

Lemma b2s_small_ror32_eq (w s: int) :
  Int.or (Int.shru w (Int.and s (Int.repr 31))) (Int.shl w (Int.and (Int.neg s) (Int.repr 31))) =
  Int.ror w s.
Proof.
  rewrite (b2s_small_ror_mod w s).
  assert (Hn: Int.unsigned (Int.and (Int.neg s) (Int.repr 31)) = (- Int.unsigned s) mod 32). {
    rewrite b2s_small_and31. unfold Int.neg. rewrite Int.unsigned_repr_eq.
    rewrite <- Znumtheory.Zmod_div_mod; [reflexivity | lia | rep_lia | ].
    exists (Int.modulus / 32). reflexivity. }
  pose proof (b2s_small_and31 s) as Ha.
  destruct (Z.eq_dec (Int.unsigned s mod 32) 0) as [H0|H0].
  - assert (E1: Int.and s (Int.repr 31) = Int.zero).
    { apply Int.same_if_eq. unfold Int.eq. rewrite Ha, H0. reflexivity. }
    assert (E2: Int.and (Int.neg s) (Int.repr 31) = Int.zero).
    { apply Int.same_if_eq. unfold Int.eq. rewrite Hn, Z_mod_zero_opp_full by assumption. reflexivity. }
    rewrite E1, E2, Int.shru_zero, Int.shl_zero, Int.or_idem.
    unfold Int.ror. change (Int.unsigned Int.zero mod Int.zwordsize) with 0.
    rewrite Z.shiftr_0_r, Z.sub_0_r.
    rewrite Z.lor_comm.
    apply Int.same_bits_eq; intros i Hi. rewrite Int.testbit_repr by auto.
    rewrite Z.lor_spec, Z.shiftl_spec_low by lia. reflexivity.
  - rewrite Int.or_commut.
    rewrite (Int.or_ror w (Int.and (Int.neg s) (Int.repr 31)) (Int.and s (Int.repr 31))); auto.
    + unfold Int.ltu. rewrite Hn. change (Int.unsigned Int.iwordsize) with 32.
      pose proof (Z.mod_pos_bound (- Int.unsigned s) 32 ltac:(lia)). destruct zlt; auto; lia.
    + unfold Int.ltu. rewrite Ha. change (Int.unsigned Int.iwordsize) with 32.
      pose proof (Z.mod_pos_bound (Int.unsigned s) 32 ltac:(lia)). destruct zlt; auto; lia.
    + apply Int.same_if_eq. unfold Int.eq, Int.add. rewrite Hn, Ha.
      rewrite Z_mod_nz_opp_full by assumption.
      change (Int.unsigned Int.iwordsize) with 32.
      replace (32 - Int.unsigned s mod 32 + Int.unsigned s mod 32) with 32 by lia.
      reflexivity.
Qed.

Lemma b2s_small_body_ror32 :
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog3 WgNoise.blake2s.code.f_ror32 ror32_spec.
Proof.
  start_function.
  forward.
  - entailer!. rewrite !b2s_small_and31. change (Int.unsigned Int.iwordsize) with 32.
    pose proof (Z.mod_pos_bound (Int.unsigned s) 32 ltac:(lia)).
    pose proof (Z.mod_pos_bound (Int.unsigned (Int.neg s)) 32 ltac:(lia)). lia.
  - entailer!. rewrite b2s_small_ror32_eq. reflexivity.
Qed.

(* ---------- blake2s_increment_counter ---------- *)

Lemma b2s_small_carry (t inc: Z) :
  0 <= t -> 0 <= inc <= Int.max_unsigned ->
  Int.add (b2s_t1 t) (Int.repr (Z.b2z (Int.ltu (Int.add (b2s_t0 t) (Int.repr inc)) (Int.repr inc)))) =
  b2s_t1 (t + inc).
Proof.
  intros Ht Hi. unfold b2s_t0, b2s_t1. rewrite add_repr.
  unfold Int.ltu. rewrite add_repr. rewrite (Int.unsigned_repr inc) by rep_lia. rewrite Int.unsigned_repr_eq.
  f_equal.
  pose proof (Z.div_mod t Int.modulus ltac:(rep_lia)) as Ed.
  pose proof (Z.mod_pos_bound t Int.modulus ltac:(rep_lia)) as Br.
  set (q := t / Int.modulus) in *. set (r := t mod Int.modulus) in *.
  replace (t + inc) with ((r + inc) + q * Int.modulus) by lia.
  rewrite Z.div_add by rep_lia. rewrite Z_mod_plus_full.
  assert (Int.modulus = Int.max_unsigned + 1) by reflexivity.
  destruct (zlt (r + inc) Int.modulus).
  - rewrite Z.div_small by lia. rewrite Z.mod_small by lia.
    destruct (zlt (r + inc) inc); [lia|]. simpl. lia.
  - assert (E: (r + inc) / Int.modulus = 1).
    { symmetry. apply Z.div_unique with (r + inc - Int.modulus); lia. }
    assert (E': (r + inc) mod Int.modulus = r + inc - Int.modulus).
    { symmetry. apply Z.mod_unique with 1; lia. }
    rewrite E, E'. destruct (zlt (r + inc - Int.modulus) inc); [|lia]. simpl. lia.
Qed.

Lemma b2s_small_body_increment_counter :
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog3 WgNoise.blake2s.code.f_blake2s_increment_counter
    blake2s_increment_counter_spec.
Proof.
  start_function.
  forward. forward. forward. forward. forward.
  rewrite b2s_small_carry by auto.
  replace (Int.add (b2s_t0 t) (Int.repr inc)) with (b2s_t0 (t + inc))
    by (unfold b2s_t0; rewrite add_repr; reflexivity).
  entailer!.
Qed.

Lemma b2s_small_body_set_lastblock :
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog3 WgNoise.blake2s.code.f_blake2s_set_lastblock
    blake2s_set_lastblock_spec.
Proof.
  start_function.
  forward.
  entailer!.
Qed.

(* ---------- get_unaligned_le32 ---------- *)

Lemma b2s_small_is_int_Vubyte (b: byte) : is_int I8 Unsigned (Vubyte b).
Proof.
  simpl. unfold Vubyte. simpl. rewrite Int.unsigned_repr; pose proof (Byte.unsigned_range_2 b); rep_lia.
Qed.

Lemma b2s_small_body_get_unaligned_le32 :
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog3 WgNoise.blake2s.code.f_get_unaligned_le32
    (@get_unaligned_le32_spec Blake2s.CS).
Proof.
  start_function.
  assert_PROP (field_compatible (tarray tuchar (Zlength bs)) [] p) by entailer!.
  rewrite (split2_data_at_Tarray_tuchar sh (Zlength bs) i) by (rewrite ?Zlength_map; lia).
  change (Tarray tuchar (Zlength bs) noattr) with (tarray tuchar (Zlength bs)).
  rewrite arr_field_address0 by (auto; lia). simpl sizeof. rewrite Z.mul_1_l.
  rewrite !sublist_map. Intros.
  forward.
  forward; [entailer!; try rewrite Znth_map by list_solve; apply b2s_small_is_int_Vubyte|].
  forward; [entailer!; try rewrite Znth_map by list_solve; apply b2s_small_is_int_Vubyte|].
  forward; [entailer!; try rewrite Znth_map by list_solve; apply b2s_small_is_int_Vubyte|].
  forward; [entailer!; try rewrite Znth_map by list_solve; apply b2s_small_is_int_Vubyte|].
  rewrite !Znth_map by list_solve. rewrite !Znth_sublist by list_solve.
  forward.
  apply andp_right.
  - apply prop_right. unfold le32_at, le32_of, Vubyte. simpl. rewrite !(Z.add_comm _ i). reflexivity.
  - rewrite (split2_data_at_Tarray_tuchar sh (Zlength bs) i) by list_solve.
    change (Tarray tuchar (Zlength bs) noattr) with (tarray tuchar (Zlength bs)).
    rewrite arr_field_address0 by (auto; lia). simpl sizeof. rewrite Z.mul_1_l, !sublist_map. cancel.
Qed.

Lemma b2s_small_body_memzero_explicit :
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog3 WgNoise.blake2s.code.f_memzero_explicit
    (@memzero_explicit_spec Blake2s.CS).
Proof.
  start_function.
  forward_call (sh, p, 0, n).
  forward.
Qed.

(* the small functions of lib/crypto/blake2s.c and the shared inlines (blake2s.c's copies) *)
Lemma b2s_small_bodies :
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog3 WgNoise.blake2s.code.f_ror32 ror32_spec /\
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog3 WgNoise.blake2s.code.f_blake2s_increment_counter
    blake2s_increment_counter_spec /\
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog3 WgNoise.blake2s.code.f_blake2s_set_lastblock
    blake2s_set_lastblock_spec /\
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog3 WgNoise.blake2s.code.f_get_unaligned_le32
    (@get_unaligned_le32_spec Blake2s.CS) /\
  semax_body (QPvarspecs Blake2s.qp) b2s_Gprog3 WgNoise.blake2s.code.f_memzero_explicit
    (@memzero_explicit_spec Blake2s.CS).
Proof.
  split; [|split; [|split; [|split]]].
  - apply b2s_small_body_ror32.
  - apply b2s_small_body_increment_counter.
  - apply b2s_small_body_set_lastblock.
  - apply b2s_small_body_get_unaligned_le32.
  - apply b2s_small_body_memzero_explicit.
Qed.
