(* hc_pieces3, group loops: common.h bodies, proved once at a small compspecs with the callee context
   of hc3_ctx.v.  One lemma per function (per law where the Clight
   reads a renamed constant). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.blake2s.b2s_spec3.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common.hc3_ctx.
Require WgNoise.harness.x_handshake.code WgNoise.harness.x_cookie_reply.code WgNoise.harness.x_consume_response_any.code
        WgNoise.harness.x_keypairs.code WgNoise.harness.x_create_any.code WgNoise.harness.x_replay.code
        WgNoise.harness.x_cookie_mac.code WgNoise.harness.x_consume_initiation_any.code.
Require WgNoise.contracts.x_cookie_reply.

Module FH := WgNoise.harness.x_handshake.code.
Module FK := WgNoise.harness.x_cookie_reply.code.
Module FR := WgNoise.harness.x_consume_response_any.code.

(* byte arrays across compspecs (copied from libc_bytes, not loaded here) *)
Lemma hc3b_loops_field_compatible_cs {cs1 cs2: compspecs}: forall n p,
  @field_compatible cs1 (tarray tuchar n) nil p <-> @field_compatible cs2 (tarray tuchar n) nil p.
Proof.
  assert (A: forall (ce: composite_env) n z, align_compatible_rec ce (tarray tuchar n) z).
  { intros. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  intros. unfold field_compatible, size_compatible, align_compatible.
  destruct p; simpl; try tauto.
  pose proof (A (@cenv_cs cs1) n (Ptrofs.unsigned i)).
  pose proof (A (@cenv_cs cs2) n (Ptrofs.unsigned i)).
  tauto.
Qed.

Lemma hc3b_loops_data_at_cs {cs1 cs2: compspecs}: forall sh n (v: list val) p,
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  intros. unfold data_at, field_at.
  f_equal. f_equal. apply prop_ext. apply hc3b_loops_field_compatible_cs.
Qed.

Lemma hc3b_loops_data_at__cs {cs1 cs2: compspecs}: forall sh n p,
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof.
  intros. unfold data_at_, field_at_. apply hc3b_loops_data_at_cs.
Qed.

Lemma hc3b_loops_hbytes sh A p :
  hbytes sh A p = @data_at CSk sh (tarray tuchar (Zlength A)) (bytes A) p.
Proof. unfold hbytes. apply hc3b_loops_data_at_cs. Qed.

Lemma hc3b_loops_hout sh n p : hout sh n p = @data_at_ CSk sh (tarray tuchar n) p.
Proof. unfold hout. apply hc3b_loops_data_at__cs. Qed.

Lemma hc3b_loops_upd_prefix (A: list byte) i n : 0 <= i < n -> Zlength A = n ->
  upd_Znth i (bytes (sublist 0 i A) ++ Zrepeat Vundef (n - i)) (Vubyte (Znth i A)) =
  bytes (sublist 0 (i + 1) A) ++ Zrepeat Vundef (n - (i + 1)).
Proof. intros. unfold bytes. list_solve. Qed.

Lemma hc3b_loops_Znth_bytes (A: list byte) i : 0 <= i < Zlength A -> Znth i (bytes A) = Vubyte (Znth i A).
Proof. intros. unfold bytes. rewrite Znth_map by lia. reflexivity. Qed.

Lemma hc3b_loops_prefix_step (A B: list byte) i : 0 <= i < Zlength A -> Zlength A = Zlength B ->
  sublist 0 i A = sublist 0 i B -> Byte.unsigned (Znth i A) = Byte.unsigned (Znth i B) ->
  sublist 0 (i + 1) A = sublist 0 (i + 1) B.
Proof.
  intros. rewrite !(sublist_split 0 i (i + 1)) by lia. rewrite !sublist_len_1 by lia.
  rewrite H1, <- (Byte.repr_unsigned (Znth i A)), H2, Byte.repr_unsigned. reflexivity.
Qed.

Lemma hc3b_loops_eqb_false (A B: list byte) i : 0 <= i < Zlength A ->
  Byte.unsigned (Znth i A) <> Byte.unsigned (Znth i B) -> bytes_eqb A B = false.
Proof. intros. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec A B); [subst; congruence | reflexivity]. Qed.

Lemma hc3b_loops_eqb_true (A B: list byte) : Zlength A = Zlength B ->
  sublist 0 (Zlength A) A = sublist 0 (Zlength A) B -> bytes_eqb A B = true.
Proof.
  intros. rewrite sublist_same in H0 by lia. rewrite sublist_same in H0 by lia. subst.
  unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec B B); congruence.
Qed.

Lemma hc3b_loops_vubyte (x: int) :
  Vint (Int.zero_ext 8 (Int.zero_ext 8 x)) = Vubyte (Byte.repr (Int.unsigned x)).
Proof.
  rewrite Int.zero_ext_idem by lia. unfold Vubyte. f_equal.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 x)), Int.zero_ext_mod; [ rewrite Byte.unsigned_repr_eq; reflexivity | ]; rep_lia.
Qed.

Lemma hc3b_loops_le32_bytes (v: int) : bytes (le32 v) =
  [Vint (Int.zero_ext 8 (Int.zero_ext 8 v));
   Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.shru v (Int.repr 8))));
   Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.shru v (Int.repr 16))));
   Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.shru v (Int.repr 24))))].
Proof.
  assert (D: forall k, 0 <= k -> Int.unsigned (Int.repr (Int.unsigned v / two_p k)) = Int.unsigned v / two_p k).
  { intros. apply Int.unsigned_repr. pose proof (Int.unsigned_range_2 v).
    assert (0 < two_p k) by (pose proof (two_p_gt_ZERO k H); lia).
    split. apply Z.div_pos; lia.
    apply Z.le_trans with (Int.unsigned v); [apply Z.div_le_upper_bound; nia | lia]. }
  rewrite !hc3b_loops_vubyte, !Int.shru_div_two_p, !(Int.unsigned_repr 8), !(Int.unsigned_repr 16),
    !(Int.unsigned_repr 24) by rep_lia.
  rewrite !D by lia. unfold le32, bytes. cbn [map].
  change (2 ^ (8 * 0)) with 1. rewrite Z.div_1_r. reflexivity.
Qed.

(* a pointwise fact about bytes, checked on the 256 values *)
Lemma hc3b_loops_byte_all (f g: byte -> int) :
  forallb (fun z => Int.eq (f (Byte.repr z)) (g (Byte.repr z))) (map Z.of_nat (seq 0 256)) = true ->
  forall b, f b = g b.
Proof.
  intros H b. rewrite forallb_forall in H. rewrite <- (Byte.repr_unsigned b).
  pose proof (Byte.unsigned_range b). change Byte.modulus with 256 in *.
  assert (I: In (Byte.unsigned b) (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat (Byte.unsigned b)). split; [rewrite Z2Nat.id; lia |].
    apply in_seq. lia. }
  specialize (H _ I). generalize (Int.eq_spec (f (Byte.repr (Byte.unsigned b))) (g (Byte.repr (Byte.unsigned b)))).
  rewrite H. auto.
Qed.

Lemma hc3b_loops_clamp0 (b: byte) :
  Vint (Int.zero_ext 8 (Int.repr (Z.land (Byte.unsigned b) 248))) = Vubyte (Byte.and b (Byte.repr 248)).
Proof.
  unfold Vubyte. f_equal.
  apply (hc3b_loops_byte_all (fun b => Int.zero_ext 8 (Int.repr (Z.land (Byte.unsigned b) 248)))
    (fun b => Int.repr (Byte.unsigned (Byte.and b (Byte.repr 248))))).
  vm_compute. reflexivity.
Qed.

Lemma hc3b_loops_clamp31 (b: byte) :
  Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.repr (Z.lor (Z.land (Byte.unsigned b) 127) 64)))) =
  Vubyte (Byte.or (Byte.and b (Byte.repr 127)) (Byte.repr 64)).
Proof.
  unfold Vubyte. f_equal.
  apply (hc3b_loops_byte_all (fun b => Int.zero_ext 8 (Int.zero_ext 8 (Int.repr (Z.lor (Z.land (Byte.unsigned b) 127) 64))))
    (fun b => Int.repr (Byte.unsigned (Byte.or (Byte.and b (Byte.repr 127)) (Byte.repr 64))))).
  vm_compute. reflexivity.
Qed.

Lemma hc3b_loops_ts_newer_app (P T L: list byte) : ts_newer (P ++ T) (P ++ L) = ts_newer T L.
Proof. induction P; simpl; auto. rewrite Byte.eq_true. auto. Qed.

Lemma hc3b_loops_ts_newer_refl (T: list byte) : ts_newer T T = false.
Proof. induction T; simpl; auto. rewrite Byte.eq_true. auto. Qed.

Lemma hc3b_loops_ts_newer_at (A B: list byte) i : 0 <= i < Zlength A -> Zlength A = Zlength B ->
  sublist 0 i A = sublist 0 i B -> Byte.unsigned (Znth i A) <> Byte.unsigned (Znth i B) ->
  ts_newer A B = Z.gtb (Byte.unsigned (Znth i A)) (Byte.unsigned (Znth i B)).
Proof.
  intros. assert (SA: A = sublist 0 i A ++ Znth i A :: sublist (i + 1) (Zlength A) A).
  { change (Znth i A :: ?x) with ([Znth i A] ++ x). rewrite <- sublist_len_1 by lia.
    rewrite <- !sublist_split; try lia. now rewrite sublist_same by lia. }
  assert (SB: B = sublist 0 i B ++ Znth i B :: sublist (i + 1) (Zlength B) B).
  { change (Znth i B :: ?x) with ([Znth i B] ++ x). rewrite <- sublist_len_1 by lia.
    rewrite <- !sublist_split; try lia. now rewrite sublist_same by lia. }
  rewrite SA at 1. rewrite SB at 1. rewrite H1, hc3b_loops_ts_newer_app. simpl.
  rewrite Byte.eq_false; auto. congruence.
Qed.

Lemma hc3b_loops_byte_div (z a b c: Z) : 0 <= z -> 0 <= b -> 0 <= c -> c + 8 <= 32 -> a = b + c ->
  Byte.repr (Int.unsigned (Int.repr (z / 2 ^ a))) = Byte.repr (Int.unsigned (Int.repr (z / 2 ^ b)) / 2 ^ c).
Proof.
  intros. subst a. apply Byte.same_bits_eq. intros n Hn.
  rewrite !Byte.testbit_repr by lia. change Byte.zwordsize with 8 in Hn. rewrite !Int.unsigned_repr_eq. change Int.modulus with (2 ^ 32).
  rewrite <- !Z.shiftr_div_pow2 by lia. rewrite Z.mod_pow2_bits_low by lia.
  rewrite !Z.shiftr_spec by lia. rewrite Z.mod_pow2_bits_low by lia.
  rewrite Z.shiftr_spec by lia. f_equal. lia.
Qed.

Lemma hc3b_loops_be64_byte (S: int64) i : 0 <= i < 8 ->
  Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.repr (Int64.Z_mod_modulus (Z.shiftr (Int64.unsigned S)
    (Int64.Z_mod_modulus (Int.unsigned (Int.sub (Int.repr 56) (Int.mul (Int.repr 8) (Int.repr i)))))))))) =
  Vubyte (Znth i (be64 S)).
Proof.
  intros. pose proof (Int64.unsigned_range S) as R.
  assert (E: Int.unsigned (Int.sub (Int.repr 56) (Int.mul (Int.repr 8) (Int.repr i))) = 56 - 8 * i).
  { unfold Int.sub, Int.mul.
    rewrite (Int.unsigned_repr 8), (Int.unsigned_repr i), (Int.unsigned_repr 56), (Int.unsigned_repr (8 * i)),
      Int.unsigned_repr by rep_lia. reflexivity. }
  rewrite E, (Int64.Z_mod_modulus_eq (56 - 8 * i)), (Z.mod_small (56 - 8 * i)) by (change Int64.modulus with (2 ^ 64); lia).
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite Int64.Z_mod_modulus_eq, Z.mod_small.
  2: { split. apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia].
       apply Z.le_lt_trans with (Int64.unsigned S); [apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|] | lia].
       assert (1 <= 2 ^ (56 - 8 * i)) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia). nia. }
  rewrite hc3b_loops_vubyte. f_equal.
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) as C by lia.
  unfold be64, be32. destruct S as [u U]. simpl Int64.unsigned in *.
  destruct C as [C|[C|[C|[C|[C|[C|[C|C]]]]]]]; subst i; unfold Znth; cbn -[Z.div Z.pow Int.unsigned Int.repr Byte.repr];
  first [ apply (hc3b_loops_byte_div u _ 32); lia
        | rewrite <- (Z.div_1_r u) at 2; apply (hc3b_loops_byte_div u _ 0); lia ].
Qed.

Lemma hc3b_loops_be32_byte (N: int) i : 0 <= i < 4 ->
  Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.shru N (Int.sub (Int.repr 24) (Int.mul (Int.repr 8) (Int.repr i)))))) =
  Vubyte (Znth i (be32 N)).
Proof.
  intros. pose proof (Int.unsigned_range_2 N) as R.
  assert (E: Int.sub (Int.repr 24) (Int.mul (Int.repr 8) (Int.repr i)) = Int.repr (24 - 8 * i)).
  { unfold Int.sub, Int.mul.
    rewrite (Int.unsigned_repr 8), (Int.unsigned_repr i), (Int.unsigned_repr 24), (Int.unsigned_repr (8 * i))
      by rep_lia. reflexivity. }
  rewrite E, Int.shru_div_two_p, (Int.unsigned_repr (24 - 8 * i)) by rep_lia. rewrite two_p_equiv.
  assert (1 <= 2 ^ (24 - 8 * i)) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia).
  rewrite hc3b_loops_vubyte, Int.unsigned_repr.
  2: { split. apply Z.div_pos; lia. apply Z.le_trans with (Int.unsigned N); [apply Z.div_le_upper_bound; nia | lia]. }
  f_equal.
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) as C by lia.
  unfold be32. destruct C as [C|[C|[C|C]]]; subst i; unfold Znth; cbn -[Z.div Z.pow Int.unsigned Int.repr Byte.repr];
  reflexivity.
Qed.

(* every lemma takes all the section variables and hypotheses (a stable signature for the assembly) *)
#[local] Set Default Proof Using "All".

Section Bodies.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Hypothesis X25519: x25519_props x25519.
Hypothesis AEAD: aead_props aead_enc aead_dec.
Hypothesis XAEAD: xaead_props xaead_enc xaead_dec.

#[local] Existing Instance CSk.

Lemma hc3_body_bytes_eq :
  @semax_body [] (hc3_G_none) CSk FH.f_bytes_eq (bytes_eq_spec).
Proof.
start_function.
rewrite !hc3b_loops_hbytes.
forward_for_simple_bound (Zlength A) (EX i:Z, PROP (sublist 0 i A = sublist 0 i B)
  LOCAL (temp FH._a a; temp FH._b b; temp FH._n (Vlong (Int64.repr (Zlength A))))
  SEP (data_at sha (tarray tuchar (Zlength A)) (bytes A) a;
       data_at shb (tarray tuchar (Zlength B)) (bytes B) b))%assert.
- entailer!.
- cbv beta. Intros. forward.
  { rewrite hc3b_loops_Znth_bytes by lia. entailer!. simpl. rewrite ?Int.unsigned_repr by rep_lia. rep_lia. }
  rewrite hc3b_loops_Znth_bytes by lia.
  forward.
  { rewrite hc3b_loops_Znth_bytes by lia. entailer!. simpl. rewrite ?Int.unsigned_repr by rep_lia. rep_lia. }
  rewrite hc3b_loops_Znth_bytes by lia.
  forward_if.
  + forward.
    rewrite (hc3b_loops_eqb_false A B i) by auto. entailer!. rewrite !hc3b_loops_hbytes. cancel.
  + forward.
    entailer!. apply hc3b_loops_prefix_step; auto.
- forward.
  rewrite hc3b_loops_eqb_true by auto. entailer!. rewrite !hc3b_loops_hbytes. cancel.
Qed.

Lemma hc3_body_bytes_zero :
  @semax_body [] (hc3_G_none) CSk FH.f_bytes_zero (bytes_zero_spec).
Proof.
start_function.
rewrite !hc3b_loops_hbytes.
assert (LZ: Zlength (zeros (Zlength A)) = Zlength A) by (unfold zeros; rewrite Zlength_Zrepeat; rep_lia).
assert (ZZ: forall i, 0 <= i < Zlength A -> Byte.unsigned (Znth i (zeros (Zlength A))) = 0)
  by (intros; unfold zeros; rewrite Znth_Zrepeat by lia; reflexivity).
forward_for_simple_bound (Zlength A) (EX i:Z, PROP (sublist 0 i A = sublist 0 i (zeros (Zlength A)))
  LOCAL (temp FH._a a; temp FH._n (Vlong (Int64.repr (Zlength A))))
  SEP (data_at sha (tarray tuchar (Zlength A)) (bytes A) a))%assert.
- entailer!.
- cbv beta. Intros. forward.
  { rewrite hc3b_loops_Znth_bytes by lia. entailer!. simpl. rewrite ?Int.unsigned_repr by rep_lia. rep_lia. }
  rewrite hc3b_loops_Znth_bytes by lia.
  forward_if.
  + forward.
    unfold is_zero. rewrite (hc3b_loops_eqb_false A _ i) by (auto; rewrite ZZ by lia; auto).
    entailer!. rewrite !hc3b_loops_hbytes. cancel.
  + forward.
    entailer!. apply hc3b_loops_prefix_step; auto. rewrite ZZ by lia. auto.
- forward.
  unfold is_zero. rewrite hc3b_loops_eqb_true by auto. entailer!. rewrite !hc3b_loops_hbytes. cancel.
Qed.

Lemma hc3_body_bytes_copy :
  @semax_body [] (hc3_G_none) CSk FH.f_bytes_copy (bytes_copy_spec).
Proof.
start_function.
rewrite hc3b_loops_hout, !hc3b_loops_hbytes.
forward_for_simple_bound (Zlength A) (EX i:Z, PROP () LOCAL (temp FH._d d; temp FH._s s;
  temp FH._n (Vlong (Int64.repr (Zlength A))))
  SEP (data_at shd (tarray tuchar (Zlength A)) (bytes (sublist 0 i A) ++ Zrepeat Vundef (Zlength A - i)) d;
       data_at shs (tarray tuchar (Zlength A)) (bytes A) s))%assert.
- rewrite sublist_nil, Z.sub_0_r; simpl app; entailer!.
- forward.
  { rewrite hc3b_loops_Znth_bytes by lia. entailer!. simpl. rewrite ?Int.unsigned_repr by rep_lia. rep_lia. }
  rewrite hc3b_loops_Znth_bytes by lia.
  forward.
  entailer!.
  rewrite hc3b_loops_upd_prefix by lia. apply derives_refl.
- rewrite sublist_same, Z.sub_diag, Zrepeat_0, app_nil_r by lia.
  entailer!. rewrite !hc3b_loops_hbytes. cancel.
Qed.

Lemma hc3_body_bytes_set :
  @semax_body [] (hc3_G_none) CSk FH.f_bytes_set (bytes_set_spec).
Proof.
start_function.
rewrite hc3b_loops_hout.
assert (LR: Zlength (Zrepeat v n) = n) by (rewrite Zlength_Zrepeat; lia).
forward_for_simple_bound n (EX i:Z, PROP () LOCAL (temp FH._d d; temp FH._v (Vubyte v);
  temp FH._n (Vlong (Int64.repr n)))
  SEP (data_at shd (tarray tuchar n) (bytes (sublist 0 i (Zrepeat v n)) ++ Zrepeat Vundef (n - i)) d))%assert.
- rewrite sublist_nil, Z.sub_0_r; simpl app; entailer!.
- forward.
  entailer!.
  replace (Vint (Int.repr (Byte.unsigned v))) with (Vubyte (Znth i (Zrepeat v n)))
    by (rewrite Znth_Zrepeat by lia; reflexivity).
  rewrite hc3b_loops_upd_prefix by lia. apply derives_refl.
- rewrite sublist_same, Z.sub_diag, Zrepeat_0, app_nil_r by lia.
  entailer!. rewrite hc3b_loops_hbytes, LR. cancel.
Qed.

Lemma hc3_body_le32_store :
  @semax_body [] (hc3_G_none) CSk FH.f_le32_store (le32_store_spec).
Proof.
start_function.
rewrite hc3b_loops_hout.
forward. forward. forward. forward.
entailer!.
rewrite hc3b_loops_hbytes, hc3b_loops_le32_bytes. apply derives_refl.
Qed.

Lemma hc3_body_m_clamp :
  @semax_body [] (hc3_G_none) CSk FH.f_m_clamp (m_clamp_spec).
Proof.
start_function.
rewrite hc3b_loops_hbytes.
forward.
{ rewrite hc3b_loops_Znth_bytes by lia. entailer!. simpl. rewrite ?Int.unsigned_repr by rep_lia. rep_lia. }
rewrite hc3b_loops_Znth_bytes by lia.
forward.
forward.
{ rewrite Znth_upd_Znth_diff, hc3b_loops_Znth_bytes by lia.
  entailer!. simpl. rewrite ?Int.unsigned_repr by rep_lia. rep_lia. }
rewrite Znth_upd_Znth_diff, hc3b_loops_Znth_bytes by lia.
forward.
entailer!.
rewrite hc3b_loops_clamp0, hc3b_loops_clamp31, hc3b_loops_hbytes.
unfold clamp, bytes. rewrite !upd_Znth_map, !upd_Znth_Zlength by list_solve. apply derives_refl.
Qed.

Lemma hc3_body_m_tai64n :
  @semax_body [] (hc3_G_none) CSk FH.f_m_tai64n (m_tai64n_spec).
Proof.
start_function.
rewrite hc3b_loops_hout.
forward. forward.
change (Int64.sub (Int64.repr (Int.signed (Int.repr 16777216))) (Int64.repr (Int.signed (Int.repr 1))))
  with (Int64.repr 16777215).
set (N := Int.repr (Int64.unsigned (Int64.and nsec (Int64.not (Int64.repr 16777215))))).
forward_for_simple_bound 8 (EX i:Z, PROP () LOCAL (temp FH._out o; temp FH._n (Vint N);
  temp FH._s (Vlong (Int64.add (Int64.repr 4611686018427387914) sec)))
  SEP (data_at sh (tarray tuchar 12)
     (bytes (sublist 0 i (be64 (Int64.add (Int64.repr 4611686018427387914) sec))) ++ Zrepeat Vundef (12 - i)) o))%assert.
- rewrite sublist_nil, Z.sub_0_r; simpl app; entailer!.
- forward.
  { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
  replace (Int64.Z_mod_modulus (4611686018427387914 + Int64.unsigned sec))
    with (Int64.unsigned (Int64.add (Int64.repr 4611686018427387914) sec)) by reflexivity.
  rewrite (hc3b_loops_be64_byte (Int64.add (Int64.repr 4611686018427387914) sec) i) by lia.
  entailer!.
  assert (Zlength (be64 (Int64.add (Int64.repr 4611686018427387914) sec)) = 8) by reflexivity.
  unfold bytes. replace (Zrepeat Vundef (12 - i)) with (Zrepeat Vundef (8 - i) ++ Zrepeat Vundef 4) by list_solve.
  rewrite app_assoc, upd_Znth_app1 by list_solve. fold bytes. rewrite hc3b_loops_upd_prefix by lia.
  replace (Zrepeat Vundef (12 - (i + 1))) with (Zrepeat Vundef (8 - (i + 1)) ++ Zrepeat Vundef 4) by list_solve.
  rewrite app_assoc. apply derives_refl.
- rewrite sublist_same by reflexivity. change (12 - 8) with 4.
  forward_for_simple_bound 4 (EX i:Z, PROP () LOCAL (temp FH._out o; temp FH._n (Vint N))
  SEP (data_at sh (tarray tuchar 12)
     (bytes (be64 (Int64.add (Int64.repr 4611686018427387914) sec) ++ sublist 0 i (be32 N)) ++
      Zrepeat Vundef (4 - i)) o))%assert.
  + rewrite sublist_nil, app_nil_r. entailer!.
  + forward.
    { entailer!. all: try (change (Int.unsigned Int.iwordsize) with 32; lia). }
    rewrite hc3b_loops_be32_byte by lia.
    entailer!.
    assert (Zlength (be64 (Int64.add (Int64.repr 4611686018427387914) sec)) = 8) by reflexivity.
    assert (Zlength (be32 N) = 4) by reflexivity.
    unfold bytes. rewrite !map_app, <- !app_assoc, upd_Znth_app2 by list_solve.
    replace (8 + i - Zlength (map Vubyte (be64 (Int64.add (Int64.repr 4611686018427387914) sec)))) with i by list_solve.
    fold bytes. rewrite hc3b_loops_upd_prefix by lia. unfold bytes. apply derives_refl.
  + rewrite sublist_same, Z.sub_diag, Zrepeat_0, app_nil_r by reflexivity.
    entailer!. rewrite hc3b_loops_hbytes. apply derives_refl.
Qed.

Lemma hc3_body_m_ts_newer :
  @semax_body [] (hc3_G_none) CSk FH.f_m_ts_newer (m_ts_newer_spec).
Proof.
start_function.
rewrite !hc3b_loops_hbytes.
forward_for_simple_bound 12 (EX i:Z, PROP (sublist 0 i TS = sublist 0 i L)
  LOCAL (temp FH._t t; temp FH._latest l)
  SEP (data_at sh1 (tarray tuchar (Zlength TS)) (bytes TS) t;
       data_at sh2 (tarray tuchar (Zlength L)) (bytes L) l))%assert.
- entailer!.
- cbv beta. Intros. forward.
  { rewrite hc3b_loops_Znth_bytes by lia. entailer!. all: rep_lia. }
  rewrite hc3b_loops_Znth_bytes by lia.
  forward.
  { rewrite hc3b_loops_Znth_bytes by lia. entailer!. all: rep_lia. }
  rewrite hc3b_loops_Znth_bytes by lia.
  forward_if.
  + forward. forward. forward.
    rewrite (hc3b_loops_ts_newer_at TS L i) by first [assumption | lia].
    entailer!.
    { unfold Vubyte. simpl. unfold Int.lt. rewrite !Int.signed_repr by rep_lia.
      destruct (zlt _ _), (Z.gtb_spec (Byte.unsigned (Znth i TS)) (Byte.unsigned (Znth i L))); try lia; reflexivity. }
    rewrite !hc3b_loops_hbytes. cancel.
  + forward.
    entailer!. apply hc3b_loops_prefix_step; auto; lia.
- forward.
  rewrite !sublist_same in H1 by lia. subst L. rewrite hc3b_loops_ts_newer_refl.
  entailer!. rewrite !hc3b_loops_hbytes. cancel.
Qed.

(* the group *)
Theorem hc3_bodies_loops :
  (@semax_body [] (hc3_G_none) CSk FH.f_bytes_eq (bytes_eq_spec)) /\
  (@semax_body [] (hc3_G_none) CSk FH.f_bytes_zero (bytes_zero_spec)) /\
  (@semax_body [] (hc3_G_none) CSk FH.f_bytes_copy (bytes_copy_spec)) /\
  (@semax_body [] (hc3_G_none) CSk FH.f_bytes_set (bytes_set_spec)) /\
  (@semax_body [] (hc3_G_none) CSk FH.f_le32_store (le32_store_spec)) /\
  (@semax_body [] (hc3_G_none) CSk FH.f_m_clamp (m_clamp_spec)) /\
  (@semax_body [] (hc3_G_none) CSk FH.f_m_tai64n (m_tai64n_spec)) /\
  (@semax_body [] (hc3_G_none) CSk FH.f_m_ts_newer (m_ts_newer_spec)).
Proof.
  split; [apply hc3_body_bytes_eq|]. split; [apply hc3_body_bytes_zero|].
  split; [apply hc3_body_bytes_copy|]. split; [apply hc3_body_bytes_set|].
  split; [apply hc3_body_le32_store|]. split; [apply hc3_body_m_clamp|].
  split; [apply hc3_body_m_tai64n | apply hc3_body_m_ts_newer].
Qed.

End Bodies.
