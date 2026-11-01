(* body proof of poly1305_core_setkey and poly1305_core_emit (donna32), against aead_spec3.aead_G3. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.chacha.code WgNoise.chacha_block.code WgNoise.poly1305.code WgNoise.poly1305_donna32.code
        WgNoise.chacha20poly1305.code WgNoise.shim.code.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.common.wg3_iface.
Require Import WgNoise.proof.aead.aead_spec3.
Require Import WgNoise.proof.aead.aead_cce.
Require Import WgNoise.proof.aead.aead_bytes.
Require Import WgNoise.proof.aead.aead_model.
Require Import WgNoise.proof.aead.aead_donna_emit3_reduce.
Require Import WgNoise.proof.aead.aead_donna_emit3_keymath.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* the nonce addition: four 32-bit words with 64-bit carries               *)
(* ---------------------------------------------------------------------- *)

Lemma emit3_u64_add x y :
  Int64.unsigned x + Int64.unsigned y <= Int64.max_unsigned ->
  Int64.unsigned (Int64.add x y) = Int64.unsigned x + Int64.unsigned y.
Proof.
  intros. unfold Int64.add. apply Int64.unsigned_repr.
  pose proof (Int64.unsigned_range x); pose proof (Int64.unsigned_range y). lia.
Qed.

Lemma emit3_u64_shru32 x :
  Int64.unsigned (Int64.shru x (Int64.repr (Int.unsigned (Int.repr 32)))) = Int64.unsigned x / 2 ^ 32.
Proof.
  rewrite Int64.shru_div_two_p. change (Int.unsigned (Int.repr 32)) with 32.
  change (two_p (Int64.unsigned (Int64.repr 32))) with (2 ^ 32).
  apply Int64.unsigned_repr. pose proof (Int64.unsigned_range x).
  split. apply Z.div_pos; lia. apply Z.le_trans with (Int64.unsigned x). apply Z.div_le_upper_bound; lia. rep_lia.
Qed.

Lemma emit3_u64_of_u32 (u: int) : Int64.unsigned (Int64.repr (Int.unsigned u)) = Int.unsigned u.
Proof. apply Int64.unsigned_repr. pose proof (Int.unsigned_range u). rep_lia. Qed.

(* one step of the carry chain: u + v + c with c <= 1 *)
Lemma emit3_carry_step (u v: int) f f' :
  Int64.unsigned f < 2 ^ 33 ->
  f' = Int64.add (Int64.add (Int64.repr (Int.unsigned u)) (Int64.repr (Int.unsigned v)))
         (Int64.shru f (Int64.repr (Int.unsigned (Int.repr 32)))) ->
  Int64.unsigned f' = Int.unsigned u + Int.unsigned v + Int64.unsigned f / 2 ^ 32 /\ Int64.unsigned f' < 2 ^ 33.
Proof.
  intros Hf ->.
  pose proof (Int.unsigned_range u); pose proof (Int.unsigned_range v).
  pose proof (Int64.unsigned_range f).
  assert (0 <= Int64.unsigned f / 2 ^ 32 <= 1).
  { split. apply Z.div_pos; lia. cut (Int64.unsigned f / 2 ^ 32 < 2). lia. apply Z.div_lt_upper_bound; lia. }
  change Int.modulus with (2 ^ 32) in *.
  rewrite emit3_u64_add; rewrite ?emit3_u64_add, ?emit3_u64_of_u32, ?emit3_u64_shru32.
  all: rewrite ?emit3_u64_of_u32; rep_lia.
Qed.

Lemma emit3_nonce_ok (u0 u1 u2 u3 v0 v1 v2 v3: int) f f0 f1 f2 :
  f = Int64.add (Int64.repr (Int.unsigned u0)) (Int64.repr (Int.unsigned v0)) ->
  f0 = Int64.add (Int64.add (Int64.repr (Int.unsigned u1)) (Int64.repr (Int.unsigned v1)))
         (Int64.shru f (Int64.repr (Int.unsigned (Int.repr 32)))) ->
  f1 = Int64.add (Int64.add (Int64.repr (Int.unsigned u2)) (Int64.repr (Int.unsigned v2)))
         (Int64.shru f0 (Int64.repr (Int.unsigned (Int.repr 32)))) ->
  f2 = Int64.add (Int64.add (Int64.repr (Int.unsigned u3)) (Int64.repr (Int.unsigned v3)))
         (Int64.shru f1 (Int64.repr (Int.unsigned (Int.repr 32)))) ->
  words_Z [Int.repr (Int64.unsigned f); Int.repr (Int64.unsigned f0); Int.repr (Int64.unsigned f1);
           Int.repr (Int64.unsigned f2)] =
  (words_Z [u0; u1; u2; u3] + words_Z [v0; v1; v2; v3]) mod 2 ^ 128.
Proof.
  intros Ef Ef0 Ef1 Ef2.
  pose proof (Int.unsigned_range u0); pose proof (Int.unsigned_range v0).
  change Int.modulus with (2 ^ 32) in *.
  assert (HF: Int64.unsigned f = Int.unsigned u0 + Int.unsigned v0 /\ Int64.unsigned f < 2 ^ 33).
  { subst f. rewrite emit3_u64_add; rewrite !emit3_u64_of_u32; rep_lia. }
  destruct HF as [HF HFb].
  destruct (emit3_carry_step _ _ _ _ HFb Ef0) as [HF0 HF0b].
  destruct (emit3_carry_step _ _ _ _ HF0b Ef1) as [HF1 HF1b].
  destruct (emit3_carry_step _ _ _ _ HF1b Ef2) as [HF2 HF2b].
  clear Ef Ef0 Ef1 Ef2.
  simpl words_Z. rewrite !Int.unsigned_repr_eq. change Int.modulus with (2 ^ 32).
  remember (Int64.unsigned f) as F. remember (Int64.unsigned f0) as F0.
  remember (Int64.unsigned f1) as F1. remember (Int64.unsigned f2) as F2.
  apply Z.mod_unique with (F2 / 2 ^ 32).
  - left. pose proof (Z.mod_pos_bound F (2 ^ 32)); pose proof (Z.mod_pos_bound F0 (2 ^ 32));
    pose proof (Z.mod_pos_bound F1 (2 ^ 32)); pose proof (Z.mod_pos_bound F2 (2 ^ 32)). lia.
  - pose proof (Z.div_mod F (2 ^ 32)); pose proof (Z.div_mod F0 (2 ^ 32));
    pose proof (Z.div_mod F1 (2 ^ 32)); pose proof (Z.div_mod F2 (2 ^ 32)). lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* little-endian words as bytes                                            *)
(* ---------------------------------------------------------------------- *)

Lemma emit3_le_bytes_S n z : le_bytes (S n) z = Byte.repr z :: le_bytes n (z / 256).
Proof. reflexivity. Qed.

Lemma emit3_le_bytes_add n z k : le_bytes n (z + 256 ^ Z.of_nat n * k) = le_bytes n z.
Proof.
  revert z k; induction n as [|n IH]; intros z k; [reflexivity|].
  rewrite !emit3_le_bytes_S, Nat2Z.inj_succ, Z.pow_succ_r by lia.
  replace (z + 256 * 256 ^ Z.of_nat n * k) with (z + (256 ^ Z.of_nat n * k) * 256) by ring.
  rewrite Z.div_add by lia. rewrite IH. f_equal.
  apply Byte.eqm_samerepr. exists (256 ^ Z.of_nat n * k). change Byte.modulus with 256. ring.
Qed.

Lemma emit3_le_bytes_app n m z :
  le_bytes (n + m) z = le_bytes n z ++ le_bytes m (z / 256 ^ Z.of_nat n).
Proof.
  revert z; induction n as [|n IH]; intros z.
  - change (256 ^ Z.of_nat 0) with 1. rewrite Z.div_1_r. reflexivity.
  - change (S n + m)%nat with (S (n + m)). rewrite !emit3_le_bytes_S, IH, <- app_comm_cons.
    rewrite Zdiv_Zdiv by lia. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity.
Qed.

Lemma emit3_le32_bytes (w: int) : le32_bytes w = le_bytes 4 (Int.unsigned w).
Proof.
  unfold le32_bytes. rewrite !emit3_le_bytes_S. rewrite !Z.shiftr_div_pow2 by lia. rewrite !Zdiv_Zdiv by lia. reflexivity.
Qed.

Lemma emit3_words_bytes (ws: list int) : words_bytes ws = le_bytes (4 * length ws) (words_Z ws).
Proof.
  induction ws as [|w ws IH]; [reflexivity|].
  unfold words_bytes in *.
  change (concat (map le32_bytes (w :: ws))) with (le32_bytes w ++ concat (map le32_bytes ws)).
  change (words_Z (w :: ws)) with (Int.unsigned w + 2 ^ 32 * words_Z ws).
  replace (4 * length (w :: ws))%nat with (4 + 4 * length ws)%nat by (simpl; lia).
  rewrite emit3_le_bytes_app, emit3_le32_bytes, IH. f_equal.
  - change (2 ^ 32) with (256 ^ Z.of_nat 4). rewrite emit3_le_bytes_add. reflexivity.
  - f_equal. change (256 ^ Z.of_nat 4) with (2 ^ 32).
    rewrite (Z.mul_comm (2 ^ 32)), Z.div_add by lia. rewrite Z.div_small by apply Int.unsigned_range. lia.
Qed.

Lemma emit3_mask_shift :
  Int64.loword (Int64.sub (Int64.mul (Ptrofs.to_int64 (Ptrofs.repr (@sizeof Poly1305Donna32.CS tuint)))
                                     (Int64.repr (Int.signed (Int.repr 8))))
                          (Int64.repr (Int.signed (Int.repr 1)))) = Int.repr 31.
Proof. reflexivity. Qed.

(* the output buffer after a put_unaligned_le32 at offset i: the bytes so far, then undefined *)
Lemma emit3_put_norm sh (bs: list byte) (x: int) i p :
  Zlength bs = i -> 0 <= i -> i + 4 <= 16 ->
  @data_at ChachaBlock.CS sh (tarray tuchar (Zlength (map Vubyte bs ++ Zrepeat Vundef (16 - i))))
    (sublist 0 i (map Vubyte bs ++ Zrepeat Vundef (16 - i)) ++ map Vubyte (le32_bytes x) ++
     sublist (i + 4) (Zlength (map Vubyte bs ++ Zrepeat Vundef (16 - i))) (map Vubyte bs ++ Zrepeat Vundef (16 - i))) p =
  @data_at ChachaBlock.CS sh (tarray tuchar (Zlength (map Vubyte (bs ++ le32_bytes x) ++ Zrepeat Vundef (16 - (i + 4)))))
    (map Vubyte (bs ++ le32_bytes x) ++ Zrepeat Vundef (16 - (i + 4))) p.
Proof.
  intros. assert (Zlength (le32_bytes x) = 4) by reflexivity.
  assert (E1: Zlength (map Vubyte bs ++ Zrepeat Vundef (16 - i)) = 16) by list_solve.
  assert (E2: Zlength (map Vubyte (bs ++ le32_bytes x) ++ Zrepeat Vundef (16 - (i + 4))) = 16) by list_solve.
  rewrite E1, E2. apply (f_equal (fun l => @data_at ChachaBlock.CS sh (tarray tuchar 16) l p)).
  list_solve.
Qed.

Lemma emit3_hval_eq sh (h: list Z) p :
  @data_at Poly1305.CS sh t_p1305_state (p1305_h_val h) p =
  @data_at Poly1305Donna32.CS sh t_p1305_state (@inl (list val) (list val) (map Vint (map Int.repr h))) p.
Proof. change_compspecs Poly1305Donna32.CS. reflexivity. Qed.

Ltac emit3_abbrev :=
  lazymatch goal with
  | |- semax _ (PROPx _ (LOCALx (temp _ (Vint ?e) :: _) _)) _ _ =>
      tryif is_var e then idtac else (let x := fresh "w" in let E := fresh "E" x in remember e as x eqn:E)
  | |- semax _ (PROPx _ (LOCALx (temp _ (Vlong ?e) :: _) _)) _ _ =>
      tryif is_var e then idtac else (let x := fresh "f" in let E := fresh "E" x in remember e as x eqn:E)
  | _ => idtac
  end.

#[local] Existing Instance Poly1305Donna32.CS.

Lemma aead3_donna_emit_body :
  @semax_body (QPvarspecs Poly1305Donna32.qp) (aead_imports3 Poly1305Donna32.CS ++ aead_G3) Poly1305Donna32.CS
    WgNoise.poly1305_donna32.code.f_poly1305_core_emit poly1305_core_emit_spec.
Proof.
  start_function.
  destruct H as [Hlen Hb].
  rewrite emit3_hval_eq.
  destruct h as [|a0 [|a1 [|a2 [|a3 [|a4 [|]]]]]]; try list_solve. clear Hlen.
  destruct s as [|n0 [|n1 [|n2 [|n3 [|]]]]]; try list_solve. clear H0.
  simpl in Hb. unfold Znth in Hb; simpl in Hb.
  simpl map.
  forward.
  do 5 forward.
  unfold Znth; simpl.
  do 44 (forward; emit3_abbrev).
  forward_if (EX x0: int, EX x1: int, EX x2: int, EX x3: int,
    PROP (words_Z [x0; x1; x2; x3] = (words_Z [w39; w40; w41; w42] + words_Z [n0; n1; n2; n3]) mod 2 ^ 128)
    LOCAL (temp WgNoise.poly1305_donna32.code._h0 (Vint x0); temp WgNoise.poly1305_donna32.code._h1 (Vint x1);
           temp WgNoise.poly1305_donna32.code._h2 (Vint x2); temp WgNoise.poly1305_donna32.code._h3 (Vint x3);
           temp WgNoise.poly1305_donna32.code._mac dst)
    SEP (data_at hsh t_p1305_state
          (@inl (list val) (list val) [Vint (Int.repr a0); Vint (Int.repr a1); Vint (Int.repr a2); Vint (Int.repr a3); Vint (Int.repr a4)]) hp;
         data_at nsh (tarray tuint 4) [Vint n0; Vint n1; Vint n2; Vint n3] np;
         data_at_ dsh (tarray tuchar 16) dst))%assert.
  { do 4 (forward; unfold Znth; simpl; forward; emit3_abbrev; forward; emit3_abbrev).
    pose proof (emit3_nonce_ok _ _ _ _ _ _ _ _ _ _ _ _ Ef Ef0 Ef1 Ef2) as HN.
    subst w43 w44 w45. revert HN.
    repeat match goal with Hx: ?x = _ |- _ => is_var x; clear Hx end. intros HN.
    Exists (Int.repr (Int64.unsigned f)) (Int.repr (Int64.unsigned f0)) (Int.repr (Int64.unsigned f1))
      (Int.repr (Int64.unsigned f2)).
    entailer!. }
  { assert_PROP (isptr np) by entailer!. subst np. contradiction. }
  Intros x0 x1 x2 x3.
  rewrite emit3_mask_shift in Ew27.
  destruct Hb as (Hb0 & Hb1 & Hb2 & Hb3 & Hb4).
  pose proof (emit3_reduce_ok a0 a1 a2 a3 a4 w w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
    w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42
    Hb0 Hb1 Hb2 Hb3 Hb4 Ew Ew0 Ew1 Ew2 Ew3 Ew4 Ew5 Ew6 Ew7 Ew8 Ew9 Ew10 Ew11 Ew12 Ew13 Ew14 Ew15 Ew16 Ew17
    Ew18 Ew19 Ew20 Ew21 Ew22 Ew23 Ew24 Ew25 Ew26 Ew27 Ew28 Ew29 Ew30 Ew31 Ew32 Ew33 Ew34 Ew35 Ew36 Ew37 Ew38
    Ew39 Ew40 Ew41 Ew42) as HR.
  rewrite HR, Zplus_mod_idemp_l in H.
  clear - SH SH0 SH1 H.
  rewrite (@aead_data_at__tuchar_cs Poly1305Donna32.CS ChachaBlock.CS).
  change (@data_at_ ChachaBlock.CS dsh (tarray tuchar 16) dst)
    with (@data_at ChachaBlock.CS dsh (tarray tuchar 16) (Zrepeat Vundef 16) dst).
  assert_PROP (isptr dst)
    by (entailer!; match goal with Hf: field_compatible _ _ dst |- _ => destruct Hf; auto end).
  change (@data_at ChachaBlock.CS dsh (tarray tuchar 16) (Zrepeat Vundef 16) dst) with
    (@data_at ChachaBlock.CS dsh (tarray tuchar (Zlength (map Vubyte [] ++ Zrepeat Vundef (16 - 0))))
       (map Vubyte [] ++ Zrepeat Vundef (16 - 0)) dst).
  forward_call (x0, dsh, dst, 0, map Vubyte [] ++ Zrepeat Vundef (16 - 0)).
  { unfold le32_bytes; list_solve. }
  rewrite emit3_put_norm by (try reflexivity; lia).
  forward_call (x1, dsh, dst, 4, map Vubyte ([] ++ le32_bytes x0) ++ Zrepeat Vundef (16 - (0 + 4))).
  { unfold le32_bytes; list_solve. }
  rewrite emit3_put_norm by (try reflexivity; lia).
  forward_call (x2, dsh, dst, 8, map Vubyte (([] ++ le32_bytes x0) ++ le32_bytes x1) ++ Zrepeat Vundef (16 - (4 + 4))).
  { unfold le32_bytes; list_solve. }
  rewrite emit3_put_norm by (try reflexivity; lia).
  forward_call (x3, dsh, dst, 12,
    map Vubyte ((([] ++ le32_bytes x0) ++ le32_bytes x1) ++ le32_bytes x2) ++ Zrepeat Vundef (16 - (8 + 4))).
  { unfold le32_bytes; list_solve. }
  rewrite emit3_put_norm by (try reflexivity; lia).
  change (Zrepeat Vundef (16 - (8 + 4 + 4))) with (@nil val). rewrite app_nil_r.
  match goal with |- context [tarray tuchar (Zlength ?l)] =>
    replace (Zlength l) with 16 by (unfold le32_bytes; list_solve) end.
  assert (EB: ((([] ++ le32_bytes x0) ++ le32_bytes x1) ++ le32_bytes x2) ++ le32_bytes x3 =
              le_bytes 16 ((p1305_limbs_val [a0; a1; a2; a3; a4] mod p1305_p + words_Z [n0; n1; n2; n3]) mod 2 ^ 128)).
  { rewrite <- H. change 16%nat with (4 * length [x0; x1; x2; x3])%nat. rewrite <- emit3_words_bytes.
    reflexivity. }
  rewrite EB. clear EB H.
  rewrite (@aead_data_at_tuchar_cs ChachaBlock.CS Poly1305Donna32.CS).
  rewrite emit3_hval_eq.
  entailer!.
  Unshelve. all: exact 0.
Qed.

Lemma key3_kval_eq sh r p :
  @data_at Poly1305.CS sh t_p1305_core_key (p1305_key_val r) p =
  @data_at Poly1305Donna32.CS sh t_p1305_core_key
    (@inl (list val) (list val) (map Vint (map Int.repr (p1305_r_limbs r))),
     @inl (list val) (list val) (map (fun z => Vint (Int.repr (5 * z))) (sublist 1 5 (p1305_r_limbs r)) ++ [Vundef])) p.
Proof. change_compspecs Poly1305Donna32.CS. reflexivity. Qed.

Lemma aead3_donna_setkey_body :
  @semax_body (QPvarspecs Poly1305Donna32.qp) (aead_imports3 Poly1305Donna32.CS ++ aead_G3) Poly1305Donna32.CS
    WgNoise.poly1305_donna32.code.f_poly1305_core_setkey poly1305_core_setkey_spec.
Proof.
  start_function.
  assert_PROP (isptr raw) by entailer!.
  forward_call (rsh, raw, 0, rk).
  forward.
  forward_call (rsh, raw, 3, rk).
  forward.
  forward_call (rsh, raw, 6, rk).
  forward.
  forward_call (rsh, raw, 9, rk).
  forward.
  forward_call (rsh, raw, 12, rk).
  forward.
  rewrite (key3_r0 rk H), (key3_r1 rk H), (key3_r2 rk H), (key3_r3 rk H), (key3_r4 rk H).
  set (r0 := Int.repr (p1305_r rk mod 2 ^ 26)).
  set (r1 := Int.repr (p1305_r rk / 2 ^ 26 mod 2 ^ 26)).
  set (r2 := Int.repr (p1305_r rk / 2 ^ 52 mod 2 ^ 26)).
  set (r3 := Int.repr (p1305_r rk / 2 ^ 78 mod 2 ^ 26)).
  set (r4 := Int.repr (p1305_r rk / 2 ^ 104)).
  simpl default_val. simpl upd_Znth.
  do 8 forward.
  rewrite key3_kval_eq. unfold p1305_r_limbs.
  subst r0 r1 r2 r3 r4.
  set (z0 := p1305_r rk mod 2 ^ 26). set (z1 := p1305_r rk / 2 ^ 26 mod 2 ^ 26).
  set (z2 := p1305_r rk / 2 ^ 52 mod 2 ^ 26). set (z3 := p1305_r rk / 2 ^ 78 mod 2 ^ 26).
  set (z4 := p1305_r rk / 2 ^ 104). clearbody z0 z1 z2 z3 z4.
  rewrite !key3_mul5.
  entailer!.
Qed.

Theorem aead_donna_emit_bodies3 :
  @semax_body (QPvarspecs Poly1305Donna32.qp) (aead_imports3 Poly1305Donna32.CS ++ aead_G3) Poly1305Donna32.CS
    WgNoise.poly1305_donna32.code.f_poly1305_core_setkey poly1305_core_setkey_spec /\
  @semax_body (QPvarspecs Poly1305Donna32.qp) (aead_imports3 Poly1305Donna32.CS ++ aead_G3) Poly1305Donna32.CS
    WgNoise.poly1305_donna32.code.f_poly1305_core_emit poly1305_core_emit_spec.
Proof.
  split; [apply aead3_donna_setkey_body | apply aead3_donna_emit_body].
Qed.
